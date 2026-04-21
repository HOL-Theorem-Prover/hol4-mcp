(* tactic_prefix.sml - GOALFRAG-based proof navigation

   Every tactic step uses ef() (expand_frag), giving 1:1 mapping between
   TacticParse.linearize fragments and executable steps. FOpen/FFMid/FFClose
   fragments are natively steppable via ef(open/close). No heuristics needed
   — structural boundaries ARE step boundaries.

   SML emits raw fragment data (type + text). Python wraps with
   ef(goalFrag.expand(<text>)) or ef(goalFrag.<text>).
   This avoids text-level rewriting of e() output which breaks on multiline.

   Usage:
     goalfrag_step_plan_json "rpt strip_tac >> simp[] >> fs[]";
     => {"ok":[{"end":9,"type":"expand","text":"rpt strip_tac"}, ...]}

     goalfrag_prefix_commands_json "strip_tac >- (simp[])" 15;
     => {"ok":[{"type":"expand","text":"strip_tac"},{"type":"open","text":"open_then1"}]}
*)

(* Load dependencies *)
load "TacticParse";
load "HOLSourceParser";
load "smlExecute";
load "markerLib";

(* Parse a tactic string to a tac_expr.
   TacticParse.parseTacticBlock now expects HOLSourceAST.exp (not string).
   We use HOLSourceParser.parseSML to parse the string to a DecExp exp,
   then pass the exp to parseTacticBlock. When parseSML produces no
   declaration (empty/comment-only input), we use ExpEmpty which
   parseTacticBlock maps to RepairEmpty -> Then[] (ALL_TAC). *)
fun parseTacticBlockFromString s =
  let
    val fed = ref false
    fun read _ = if !fed then "" else (fed := true; s)
    val result = HOLSourceParser.parseSML "" read
      (fn _ => fn _ => fn _ => ()) (* ignore parse warnings *)
      HOLSourceParser.initialScope
    val dec = #parseDec result ()
  in
    case dec of
      SOME (HOLSourceAST.DecExp e) => TacticParse.parseTacticBlock e
    | NONE => TacticParse.parseTacticBlock (HOLSourceAST.ExpEmpty 0)
    | _ => raise Fail ("parseTacticBlockFromString: expected expression in tactic string: " ^
                       String.substring (s, 0, Int.min (String.size s, 40)))
  end

(* JSON helpers *)
fun json_escape_char c =
  case c of
    #"\"" => "\\\""
  | #"\\" => "\\\\"
  | #"\n" => "\\n"
  | #"\r" => "\\r"
  | #"\t" => "\\t"
  | _ => if Char.ord c < 32
         then "\\u" ^ StringCvt.padLeft #"0" 4 (Int.fmt StringCvt.HEX (Char.ord c))
         else String.str c

fun json_escape_string s =
  String.concat (map json_escape_char (String.explode s))

fun json_string s = "\"" ^ json_escape_string s ^ "\""
fun json_int n = Int.toString n
fun json_ok payload = "{\"ok\":" ^ payload ^ "}"
fun json_err msg = "{\"err\":" ^ json_string msg ^ "}"

fun json_string_array strs =
  "[" ^ String.concatWith "," (map json_string strs) ^ "]"

(* goals_json for getting proof state *)
fun goal_to_json (asms, concl) =
  "{\"asms\":" ^ json_string_array (map term_to_string asms) ^
  ",\"goal\":" ^ json_string (term_to_string concl) ^ "}"

fun goals_to_json_array goals =
  "[" ^ String.concatWith "," (map goal_to_json goals) ^ "]"

fun goals_json () =
  let val goals = top_goals()
  in print (json_ok (goals_to_json_array goals) ^ "\n") end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* =============================================================================
 * GOALFRAG step plan: Map linearize fragments 1:1 to ef() commands
 *
 * Unlike the old step_plan (which threw away structural fragments and
 * re-derived them via ~400 lines of heuristics), goalfrag_step_plan uses
 * EVERY fragment from linearize as a step. FOpen/FFMid/FFClose are natively
 * executable via ef(open_paren/close_paren/etc).
 * ============================================================================= *)

(* Flatten nested fragments from linearize into a flat step sequence.
   FBracket(FOpenThen1, [inner], FClose, expr) -> FOpenThen1, inner..., FClose
   FMBracket(FOpenNullOk, mid, FClose, [arm1,arm2], expr)
     -> FOpenNullOk, arm1, FMid, arm2, FClose
   FGroup(span, [inner]) -> inner (unwrapped)

   Returns fragments in FORWARD execution order. *)
fun flatten_frags frags =
  let
    fun go [] acc = rev acc
      | go (TacticParse.FFOpen opn :: rest) acc = go rest (TacticParse.FFOpen opn :: acc)
      | go (TacticParse.FFMid mid :: rest) acc = go rest (TacticParse.FFMid mid :: acc)
      | go (TacticParse.FFClose cls :: rest) acc = go rest (TacticParse.FFClose cls :: acc)
      | go (TacticParse.FAtom a :: rest) acc = go rest (TacticParse.FAtom a :: acc)
      | go (TacticParse.FGroup (_, inner) :: rest) acc =
          go rest (rev (flatten_frags inner) @ acc)
      | go (TacticParse.FBracket (opn, inner, cls, _) :: rest) acc =
          (* open -> inner body -> close *)
          let val flat = TacticParse.FFOpen opn :: flatten_frags inner @ [TacticParse.FFClose cls]
          in go rest (rev flat @ acc) end
      | go (TacticParse.FMBracket (opn, mid, cls, [], _) :: rest) acc =
          (* degenerate: open -> close *)
          go rest (TacticParse.FFClose cls :: TacticParse.FFOpen opn :: acc)
      | go (TacticParse.FMBracket (opn, mid, cls, arms, _) :: rest) acc =
          (* open -> arm1 -> mid -> arm2 -> mid -> ... -> armN -> close *)
          let
            fun interleave [] _ = []
              | interleave [a] _ = flatten_frags a
              | interleave (a::as') mid =
                  flatten_frags a @ [TacticParse.FFMid mid] @ interleave as' mid
            val flat = TacticParse.FFOpen opn :: interleave arms mid @ [TacticParse.FFClose cls]
          in go rest (rev flat @ acc) end
  in
    go frags []
  end

(* Map a tac_frag_open to the goalFrag open function name *)
fun openFragName TacticParse.FOpen = "open_paren"
  | openFragName TacticParse.FOpenThen1 = "open_then1"
  | openFragName TacticParse.FOpenFirst = "open_first"
  | openFragName TacticParse.FOpenRepeat = "open_repeat"
  | openFragName TacticParse.FOpenTacsToLT = "open_tacs_to_lt"
  | openFragName TacticParse.FOpenNullOk = "open_null_ok"
  | openFragName (TacticParse.FOpenNthGoal (i, _)) = "open_nth_goal " ^ Int.toString i
  | openFragName TacticParse.FOpenLastGoal = "open_last_goal"
  | openFragName TacticParse.FOpenHeadGoal = "open_head_goal"
  | openFragName (TacticParse.FOpenSplit (i, _)) = "open_split_lt " ^ Int.toString i
  | openFragName TacticParse.FOpenSelect = "open_select_lt"
  | openFragName TacticParse.FOpenFirstLT = "open_first_lt"

(* Map a tac_frag_mid to the goalFrag next function name *)
fun midFragName TacticParse.FNextFirst = "next_first"
  | midFragName TacticParse.FNextTacsToLT = "next_tacs_to_lt"
  | midFragName TacticParse.FNextSplit = "next_split_lt"
  | midFragName TacticParse.FNextSelect = "next_select_lt"

(* Map a tac_frag_close to the goalFrag close function name *)
fun closeFragName TacticParse.FClose = "close_paren"
  | closeFragName TacticParse.FCloseFirst = "close_first"
  | closeFragName TacticParse.FCloseRepeat = "close_repeat"
  | closeFragName TacticParse.FCloseFirstLT = "close_first_lt"

(* Alternative span extraction for FAtom types where topSpan returns NONE.
   Subgoal, LSelectGoal, LSelectGoals store span in constructor args. *)
fun altSpan (TacticParse.Subgoal (s, e)) = SOME (s, e)
  | altSpan (TacticParse.LSelectGoal p) = SOME p
  | altSpan (TacticParse.LSelectGoals p) = SOME p
  | altSpan _ = NONE

(* Extract fragment type: "expand", "open", "mid", or "close" *)
fun frag_type (TacticParse.FAtom _) = "expand"
  | frag_type (TacticParse.FFOpen _) = "open"
  | frag_type (TacticParse.FFMid _) = "mid"
  | frag_type (TacticParse.FFClose _) = "close"
  | frag_type _ = ""

(* Extract raw text from a fragment (no ef() wrapping).
   FAtom -> tactic text from proofBody substring.
   FFOpen/FFMid/FFClose -> goalFrag function name (e.g. "open_then1").
   Returns "" for span-less atoms. *)
fun frag_text proofBody (TacticParse.FAtom a) =
      (case (TacticParse.topSpan a, altSpan a) of
         (SOME (start, endPos), _) =>
           String.substring(proofBody, start, endPos - start)
       | (NONE, SOME (start, endPos)) =>
           String.substring(proofBody, start, endPos - start)
       | (NONE, NONE) => "")
  | frag_text _ (TacticParse.FFOpen opn) = openFragName opn
  | frag_text _ (TacticParse.FFMid mid) = midFragName mid
  | frag_text _ (TacticParse.FFClose cls) = closeFragName cls


(* Get the end offset for an FAtom fragment *)
fun fragEnd (TacticParse.FAtom a) =
      (case (TacticParse.topSpan a, altSpan a) of
         (SOME (_, r), _) => r
       | (NONE, SOME (_, r)) => r
       | _ => 0)
  | fragEnd _ = 0  (* structural frag -- caller assigns position *)

(* Re-expand ThenLT atoms that linearize left atomic inside >> chains.
   linearize's `asTac` skips bracketing when `one=true` (inside Then list),
   collapsing >- into a single FAtom(ThenLT _). We detect these and
   re-linearize the ThenLT AST directly at the top level so it gets proper
   open/close decomposition.
   The AST already has correct spans from the original parse, no offset shift.

   IMPORTANT: ThenLT(Subgoal _, _) — i.e., `by`/`sg` — is NOT re-expanded.
   `Subgoal \`Q\`` is a goal specification, not a standalone tactic;
   `expand(Subgoal \`Q\`)` fails. Only the full `\`Q\` by tac` expression
   is valid as a single expand step. For `by` inside >> chains, the atomic
   FAtom is kept and text-based inside_by detection is used instead. *)
fun reexpand_thenlt_frags frags =
  let
    (* Detect FAtom(ThenLT _) or FAtom(Group(_, _, ThenLT _)) — ThenLT that
       linearize left atomic inside a >> chain. *)
    fun isThenLTatom (TacticParse.FAtom (TacticParse.ThenLT _)) = true
      | isThenLTatom (TacticParse.FAtom (TacticParse.Group (_, _, TacticParse.ThenLT _))) = true
      | isThenLTatom _ = false
    (* But skip Subgoal-based ThenLT (by/sg) — the Subgoal base cannot be
       expanded as a standalone tactic. *)
    fun isSubgoalThenLT (TacticParse.ThenLT (TacticParse.Subgoal _, _)) = true
      | isSubgoalThenLT (TacticParse.Group (_, _, TacticParse.ThenLT (TacticParse.Subgoal _, _))) = true
      | isSubgoalThenLT _ = false
    fun shouldReexpand (TacticParse.FAtom e) = isThenLTatom (TacticParse.FAtom e)
                                              andalso not (isSubgoalThenLT e)
      | shouldReexpand _ = false
    (* Extract the ThenLT from FAtom, unwrapping Group if present *)
    fun getThenLT (TacticParse.FAtom (TacticParse.ThenLT (base, arms))) =
          TacticParse.ThenLT (base, arms)
      | getThenLT (TacticParse.FAtom (TacticParse.Group (_, _, TacticParse.ThenLT (base, arms)))) =
          TacticParse.ThenLT (base, arms)
      | getThenLT _ = raise Match
    fun reexpand f =
          let
            val expr = getThenLT f
            fun isAtom e = Option.isSome (TacticParse.topSpan e)
            val subFrags = TacticParse.linearize isAtom expr
          in flatten_frags subFrags end
      | reexpand frag = [frag]
    fun go [] acc = rev acc
      | go (f :: rest) acc =
          if shouldReexpand f
          then go rest (rev (reexpand f) @ acc)
          else go rest (f :: acc)
  in go frags [] end

(* goalfrag_step_plan: Generate fragment steps from linearize fragments.
   Returns (end_offset, type, text) triples for every navigable position.
   Every fragment boundary is a step boundary -- no heuristics needed. *)
fun goalfrag_step_plan proofBody =
  let
    val tree = parseTacticBlockFromString proofBody
    fun isAtom e = Option.isSome (TacticParse.topSpan e)
    val rawFrags = TacticParse.linearize isAtom tree
    val reexpanded = reexpand_thenlt_frags rawFrags
    val flatFrags = flatten_frags reexpanded

    (* Assign end offsets: walk the flat list, tracking the last FAtom end.
       Structural frags (FOpen/FFMid/FFClose) get the end of the PREVIOUS atom.
       This means navigating to a structural frag shows the state after executing
       it, and the position aligns with the most recent tactic text.
       NOTE: reexpanded frags from ThenLT have spans from the original parse
       (not offset-shifted), so fragEnd returns correct positions. *)
    fun assignEnds [] _ acc = rev acc
      | assignEnds (f :: rest) lastAtomEnd acc =
          let
            val t = frag_type f
            val x = frag_text proofBody f
            val (endPos, newLast) = case f of
                TacticParse.FAtom _ =>
                  (let val e = fragEnd f in (e, e) end)
              | _ => (lastAtomEnd, lastAtomEnd)
          in
            if String.size x > 0
            then assignEnds rest newLast ((endPos, t, x) :: acc)
            else assignEnds rest lastAtomEnd acc
          end
  in
    assignEnds flatFrags 0 []
  end

fun goalfrag_step_plan_json proofBody =
  let
    val steps = goalfrag_step_plan proofBody
    fun stepToJson (endOff, t, x) =
      "{\"end\":" ^ json_int endOff ^ ",\"type\":" ^ json_string t ^ ",\"text\":" ^ json_string x ^ "}"
    val stepsJson = "[" ^ String.concatWith "," (map stepToJson steps) ^ "]"
  in
    print (json_ok stepsJson ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* goalfrag_prefix_commands: Generate fragment list to replay up to an offset.
   Returns (type, text) pairs. Python wraps with ef(goalFrag.*()).
   For positions at fragment boundaries, collect complete fragments.
   For positions inside an FAtom span, use sliceTacticBlock to extract
   the sliced tactic text directly from spans. *)
fun goalfrag_prefix_commands proofBody endOffset =
  let
    val tree = parseTacticBlockFromString proofBody
    val fullEnd = String.size proofBody
    val defaultSpan = (0, fullEnd)
    fun isAtom e = Option.isSome (TacticParse.topSpan e)
    val rawFrags = TacticParse.linearize isAtom tree
    val reexpanded = reexpand_thenlt_frags rawFrags
    val flatFrags = flatten_frags reexpanded

    (* Find the FAtom whose span contains endOffset *)
    fun findPartialAtom [] = NONE
      | findPartialAtom (TacticParse.FAtom a :: rest) =
          (case TacticParse.topSpan a of
             SOME (start, endP) =>
               if endOffset > start andalso endOffset < endP
               then SOME (start, endP)  (* inside this atom *)
               else findPartialAtom rest
           | NONE => findPartialAtom rest)
      | findPartialAtom (_ :: rest) = findPartialAtom rest

    (* Collect (type, text) for all complete fragments up to endOffset *)
    fun collectFrags [] _ acc = rev acc
      | collectFrags (TacticParse.FAtom a :: rest) lastEnd acc =
          (case TacticParse.topSpan a of
             SOME (_, endP) =>
               if endP <= endOffset
               then
                 let val t = frag_type (TacticParse.FAtom a)
                     val x = frag_text proofBody (TacticParse.FAtom a)
                 in collectFrags rest endP
                    (if String.size x > 0 then (t, x) :: acc else acc) end
               else rev acc  (* past the target -- done *)
           | NONE => collectFrags rest lastEnd acc)
      | collectFrags (f :: rest) lastEnd acc =
          if lastEnd <= endOffset
          then
            let val t = frag_type f
                val x = frag_text proofBody f
            in collectFrags rest lastEnd
               (if String.size x > 0 then (t, x) :: acc else acc) end
          else rev acc

    val partialAtom = findPartialAtom flatFrags
  in
    case partialAtom of
      SOME (start, endP) =>
        (* Inside an FAtom: use sliceTacticBlock to get valid fragments up to
           endOffset. Walk the slice fragments and emit (type, text) pairs.
           Uses frag_type/frag_text to emit (type, text) pairs. *)
        let
          val sliceFrags = TacticParse.sliceTacticBlock 0 endOffset false defaultSpan tree
          (* Flatten the list-of-groups into individual fragments *)
          fun extractFrags [] acc = rev acc
            | extractFrags (group :: rest) acc =
                let fun walk [] acc = acc
                      | walk (f :: fs) acc =
                          let val t = frag_type f
                              val x = frag_text proofBody f
                          in if String.size x > 0
                             then walk fs ((t, x) :: acc)
                             else walk fs acc
                          end
                in extractFrags rest (walk group acc) end
        in
          extractFrags sliceFrags []
        end
    | NONE =>
      (* At a fragment boundary: collect all complete frags up to endOffset *)
      collectFrags flatFrags 0 []
  end

fun goalfrag_prefix_commands_json proofBody endOffset =
  let
    val frags = goalfrag_prefix_commands proofBody endOffset
    fun fragToJson (t, x) =
      "{\"type\":" ^ json_string t ^ ",\"text\":" ^ json_string x ^ "}"
    val fragsJson = "[" ^ String.concatWith "," (map fragToJson frags) ^ "]"
  in
    print (json_ok fragsJson ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* backup_n - undo N ef()/e() calls via History.undo *)
fun backup_n 0 = ()
  | backup_n n = (proofManagerLib.b(); backup_n (n - 1));

(* =============================================================================
 * Proof Timing
 * ============================================================================= *)

(* timed_step_json: Execute command, return timing with goal counts *)
fun timed_step_json cmd =
  let
    val goals_before = length (top_goals()) handle _ => 0
    val start_real = Timer.startRealTimer()
    val start_cpu = Timer.startCPUTimer()
    val ok = smlExecute.quse_string cmd
    val _ = if not ok then raise Fail ("Tactic execution failed: " ^ cmd) else ()
    val real_ms = Time.toMilliseconds (Timer.checkRealTimer start_real)
    val cpu = Timer.checkCPUTimer start_cpu
    val usr_ms = Time.toMilliseconds (#usr cpu)
    val sys_ms = Time.toMilliseconds (#sys cpu)
    val goals_after = length (top_goals()) handle _ => 0
  in
    print (json_ok (
      "{\"real_ms\":" ^ LargeInt.toString real_ms ^
      ",\"usr_ms\":" ^ LargeInt.toString usr_ms ^
      ",\"sys_ms\":" ^ LargeInt.toString sys_ms ^
      ",\"goals_before\":" ^ Int.toString goals_before ^
      ",\"goals_after\":" ^ Int.toString goals_after ^ "}") ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* Core verification - goal must already be set on proof manager.
   Runs tactics with per-tactic timing, optionally stores theorem.
   Checks oracle tags on stored theorems for cheat detection. *)
fun verify_core name tactics store timeout_sec =
  let
    fun run_one cmd =
      let
        val goals_before = length (top_goals()) handle _ => 0
        val start = Timer.startRealTimer()
        val ok = smlTimeout.timeout timeout_sec (fn () => smlExecute.quse_string cmd) ()
        val real_ms = Time.toMilliseconds (Timer.checkRealTimer start)
        val goals_after = length (top_goals()) handle _ => 0
      in
        if ok then
          (SOME ("{\"real_ms\":" ^ LargeInt.toString real_ms ^
                 ",\"goals_before\":" ^ Int.toString goals_before ^
                 ",\"goals_after\":" ^ Int.toString goals_after ^ "}"), true)
        else
          (SOME ("{\"err\":" ^ json_string ("Tactic execution failed: " ^ cmd) ^
                 ",\"real_ms\":" ^ LargeInt.toString real_ms ^
                 ",\"goals_before\":" ^ Int.toString goals_before ^
                 ",\"goals_after\":" ^ Int.toString goals_after ^ "}"), false)
      end
      handle smlTimeout.FunctionTimeout =>
        let
          val timeout_ms = Real.round (timeout_sec * 1000.0)
          val goals_now = length (top_goals()) handle _ => 0
        in
        (SOME ("{\"err\":\"TIMEOUT after " ^ Real.fmt (StringCvt.FIX (SOME 1)) timeout_sec ^ "s\"" ^
               ",\"real_ms\":" ^ Int.toString timeout_ms ^
               ",\"goals_before\":" ^ Int.toString goals_now ^
               ",\"goals_after\":" ^ Int.toString goals_now ^ "}"), false)
        end
      | e =>
        let val goals_now = length (top_goals()) handle _ => 0 in
        (SOME ("{\"err\":" ^ json_string (exnMessage e) ^
               ",\"goals_before\":" ^ Int.toString goals_now ^
               ",\"goals_after\":" ^ Int.toString goals_now ^ "}"), false)
        end

    fun run_all [] acc = rev acc
      | run_all (cmd::rest) acc =
          case run_one cmd of
            (SOME entry, true) => run_all rest (entry::acc)
          | (SOME entry, false) => rev (entry::acc)
          | (NONE, _) => rev acc

    val trace_entries = run_all tactics []
    val goals_remaining = length (top_goals()) handle _ => 0
    val proof_ok = goals_remaining = 0

    val stored = proof_ok andalso store
    val _ = if stored
            then (smlExecute.quse_string ("val " ^ name ^ " = save_thm(\"" ^ name ^ "\", top_thm());"); ())
            else (drop_all (); ())

    val oracles =
      if stored then
        Lib.set_diff (fst (Tag.dest_tag (Thm.tag (DB.fetch "-" name)))) ["DISK_THM"]
        handle _ => []
      else []

    val oracles_json = "[" ^ String.concatWith "," (map json_string oracles) ^ "]"
    val trace_json = "[" ^ String.concatWith "," trace_entries ^ "]"
  in
    print (json_ok (
      "{\"stored\":" ^ (if stored then "true" else "false") ^
      ",\"name\":" ^ json_string name ^
      ",\"oracles\":" ^ oracles_json ^
      ",\"trace\":" ^ trace_json ^ "}") ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* verify_theorem_json: Execute entire proof with timing, optionally store.
   Uses GOALFRAG (gf) so that ef() commands from goalfrag_step_plan work. *)
fun verify_theorem_json goal name tactics store timeout_sec =
  let
    val _ = drop_all ()
    val _ = smlExecute.quse_string ("gf `" ^ goal ^ "`;")
  in
    verify_core name tactics store timeout_sec
  end;

(* =============================================================================
 * Definition Termination Goal Extraction
 * ============================================================================= *)

val _ = load "Defn" handle _ => ();

exception MCP_TC_Rollback;

fun extract_tc_goal_json body_str =
  let
    val result = ref ""
    fun inner () =
      let
        val d = Defn.Hol_defn "mcp_tc_extract" [QUOTE body_str]
        val _ = Defn.tgoal d
        val (_, t) = hd (top_goals())
        val _ = result := term_to_string t
        val _ = ((drop_all(); ()) handle _ => ())
      in
        raise MCP_TC_Rollback
      end
    val _ = (
      Parse.try_grammar_extension
        (fn () => Theory.try_theory_extension inner ()) ()
    ) handle MCP_TC_Rollback => ()
  in
    print (json_ok (json_string (!result)) ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* =============================================================================
 * Resume Goal Extraction
 * ============================================================================= *)

fun resume_goal_terms suspension_name label_name =
  let
    val th = case boolLib.find_suspension suspension_name of
                 SOME th => th
               | NONE => raise Fail ("No suspension found: " ^ suspension_name)
    val goal_term = markerLib.extract_suspended_goal th label_name
  in
    markerLib.resumption_to_goal goal_term
  end

fun extract_resume_goal_json suspension_name label_name =
  let
    val (asms, concl) = resume_goal_terms suspension_name label_name
    fun typed_term_to_string t =
      Lib.with_flag (Globals.show_types, true) term_to_string t
    val json = "{\"asms\":" ^ json_string_array (map typed_term_to_string asms) ^
               ",\"goal\":" ^ json_string (typed_term_to_string concl) ^ "}"
  in
    print (json_ok json ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* Verify a Resume block. Uses GOALFRAG (set_goalfrag) for ef() compatibility. *)
fun verify_resume_json suspension_name label_name name tactics store timeout_sec =
  let
    val _ = drop_all ()
    val (asms, concl) = resume_goal_terms suspension_name label_name
    val _ = proofManagerLib.set_goalfrag (asms, concl)
  in
    verify_core name tactics store timeout_sec
  end
  handle e => print (json_err (exnMessage e) ^ "\n");
