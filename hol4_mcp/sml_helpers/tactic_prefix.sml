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
*)

(* Load dependencies *)
load "TacticParse";
load "HOLSourceParser";
load "smlExecute";
load "markerLib";
load "Q";

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

(* Extract fragment type: "expand", "open", "mid", "close", or "select" *)
fun frag_type (TacticParse.FAtom (TacticParse.LSelectGoal _)) = "select"
  | frag_type (TacticParse.FAtom (TacticParse.LSelectGoals _)) = "selects"
  | frag_type (TacticParse.FAtom _) = "expand"
  | frag_type (TacticParse.FFOpen _) = "open"
  | frag_type (TacticParse.FFMid _) = "mid"
  | frag_type (TacticParse.FFClose _) = "close"
  | frag_type _ = ""

(* Extract raw text from a fragment (no ef() wrapping).
   FAtom -> tactic text from proofBody substring.
   Subgoal atoms get "sg " prefix so `Q` becomes `sg `Q`` — a valid tactic.
   FFOpen/FFMid/FFClose -> goalFrag function name (e.g. "open_then1").
   Returns "" for span-less atoms. *)
fun frag_text proofBody (TacticParse.FAtom a) =
      let val raw = (case (TacticParse.topSpan a, altSpan a) of
                       (SOME (start, endPos), _) =>
                         String.substring(proofBody, start, endPos - start)
                     | (NONE, SOME (start, endPos)) =>
                         String.substring(proofBody, start, endPos - start)
                     | (NONE, NONE) => "")
      in case a of
           TacticParse.Subgoal _ =>
             (* Subgoal from `by`: if text is a term quotation `...`, prefix with sg
                so it becomes a valid tactic. If already a tactic name, keep as-is. *)
             if String.size raw > 0 andalso String.sub(raw, 0) = #"`"
             then "sg " ^ raw else raw
         | _ => raw
      end
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

(* Re-expand Group atoms that linearize left atomic inside brackets.
   linearize's `asTac` skips bracketing when `one=true` (inside ThenLT/First/etc
   bracket), collapsing compound expressions (Then, ThenLT, First, etc.) into
   single FAtom(Group(_, _, _)). After flatten_frags unwraps the outer bracket,
   these Group atoms appear as flat FAtom steps with undecomposed content.
   We detect them and re-linearize the Group's inner AST so it gets proper
   step decomposition.
   The AST already has correct spans from the original parse, no offset shift.
   Must run AFTER flatten_frags so Group atoms are at the top level (not inside
   FGroup/FBracket containers where they're invisible to the scan).
   Recursively re-expands: subFrags from re-linearization may themselves contain
   Group atoms (e.g., nested >- inside >> inside >-).
   Subgoal atoms (\`Q`) get "sg " prefix in frag_text so they become valid tactics
   (sg \`Q`) that goalFrag.expand can execute. *)
fun reexpand_group_atoms frags =
  let
    (* Only re-expand Group atoms containing compound expressions (Then, ThenLT, etc.)
       that produce useful navigable sub-steps. Single-step wrappers like Repeat,
       Try, LNullOk etc. should stay atomic — their open/close structure adds
       navigation overhead without useful intermediate goal states. *)
    fun isComposable (TacticParse.Then _) = true
      | isComposable (TacticParse.ThenLT _) = true
      | isComposable (TacticParse.LThen1 _) = true
      | isComposable (TacticParse.LThenLT _) = true
      | isComposable (TacticParse.Group _) = true  (* peels outer wrapper; inner expr is checked by recursion *)
      | isComposable _ = false
    fun isGroupAtom (TacticParse.FAtom (TacticParse.Group (_, _, e))) =
          isComposable e
      | isGroupAtom _ = false
    fun getGroupExpr (TacticParse.FAtom (TacticParse.Group (_, _, e))) = e
      | getGroupExpr _ = raise Match
    fun reexpand f =
          let
            val expr = getGroupExpr f
            fun isAtom e = Option.isSome (TacticParse.topSpan e)
            val subFrags = TacticParse.linearize isAtom expr
          in reexpand_group_atoms (flatten_frags subFrags) end
      | reexpand frag = [frag]
    fun go [] acc = rev acc
      | go (f :: rest) acc =
          if isGroupAtom f
          then go rest (rev (reexpand f) @ acc)
          else go rest (f :: acc)
  in go frags [] end

(* merge_select_steps: Post-process step list to merge LSelectGoal/LSelectGroups
   "select"/"selects" steps with their following bracket into a single "expand_list"
   step. >~[`Foo`] >- simp[] is NOT decomposable into individual ef() steps
   because SELECT_GOAL_LT is a list_tactic, not a tactic. It must be executed
   via goalFrag.expand_list as a single combined step.
   Pattern: select/selects, [open_then1|open_first] expand close -> expand_list
   For the combined text: Q.SELECT_GOAL_LT pat >- tac  (or Q.SELECT_GOALS_LT) *)
fun isSelectKind "select" = true
  | isSelectKind "selects" = true
  | isSelectKind _ = false

fun merge_select_steps [] acc = rev acc
  | merge_select_steps ((endP, kind, patText) :: rest) acc =
      if isSelectKind kind then
        let
          (* Collect consecutive select steps (for >~ >>~ patterns) *)
          fun collectSelects ([]: (int * string * string) list) sels =
                (rev sels, [])
            | collectSelects ((ep, k, t) :: rest') sels =
                if isSelectKind k then collectSelects rest' (t :: sels)
                else (rev sels, (ep, k, t) :: rest')
          val (sels, afterSels) = collectSelects rest [patText]
          (* Build the SELECT_GOAL_LT/SELECT_GOALS_LT prefix *)
          fun mkSelectPrefix [] = ""  (* shouldn't happen *)
            | mkSelectPrefix [p] = "Q.SELECT_GOAL_LT " ^ p
            | mkSelectPrefix (p :: ps) = "Q.SELECT_GOAL_LT " ^ p ^ " >>~ Q.SELECT_GOALS_LT " ^
                String.concatWith " >>~ Q.SELECT_GOALS_LT " ps
          val selectPrefix = mkSelectPrefix sels
          (* Try to consume the following bracket: open expand close *)
          fun tryConsumeBracket [] = NONE
            | tryConsumeBracket ((_, "open", "open_then1") ::
                                (tacEnd, "expand", tacText) ::
                                (_, "close", _) :: rest') =
                SOME (selectPrefix ^ " >- " ^ tacText, tacEnd, rest')
            | tryConsumeBracket ((_, "open", "open_first") ::
                                (tacEnd, "expand", tacText) ::
                                (_, "close", _) :: rest') =
                SOME (selectPrefix ^ " >- " ^ tacText, tacEnd, rest')
            | tryConsumeBracket _ = NONE
        in
          case tryConsumeBracket afterSels of
            SOME (combinedText, tacEnd, rest') =>
              merge_select_steps rest' ((tacEnd, "expand_list", combinedText) :: acc)
          | NONE =>
              (* No following bracket — skip the invalid select step entirely *)
              merge_select_steps afterSels acc
        end
      else
        merge_select_steps rest ((endP, kind, patText) :: acc)

(* goalfrag_step_plan: Generate fragment steps from linearize fragments.
   Returns (end_offset, type, text) triples for every navigable position.
   Every fragment boundary is a step boundary -- no heuristics needed.
   LSelectGoal/LSelectGroups fragments are merged with their following
   bracket into a single expand_list step (SELECT_GOAL_LT requires
   goalFrag.expand_list, not goalFrag.expand). *)
fun goalfrag_step_plan proofBody =
  let
    val tree = parseTacticBlockFromString proofBody
    fun isAtom e = Option.isSome (TacticParse.topSpan e)
    val rawFrags = TacticParse.linearize isAtom tree
    val flatFrags = flatten_frags rawFrags
    val reexpanded = reexpand_group_atoms flatFrags

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
    val rawSteps = assignEnds reexpanded 0 []
  in
    merge_select_steps rawSteps []
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
