(* tactic_prefix.sml - GOALFRAG-based proof navigation

   Every tactic step uses ef() (expand_frag), giving 1:1 mapping between
   TacticParse.linearize fragments and executable steps. FOpen/FFMid/FFClose
   fragments are natively steppable via ef(open/close). No heuristics needed
   — structural boundaries ARE step boundaries.

   Usage:
     goalfrag_step_plan_json "rpt strip_tac >> simp[] >> fs[]";
     => {"ok":[{"end":9,"cmd":"ef(goalFrag.expand(rpt strip_tac));"}, ...]}

     goalfrag_prefix_commands_json "strip_tac >- (simp[])" 15;
     => {"ok":"ef(goalFrag.expand(strip_tac));\nef(goalFrag.open_then1);\n"}
*)

(* Load dependencies *)
load "TacticParse";
load "smlExecute";
load "markerLib";

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

(* Map a single flat fragment to an ef() command string.
   FAtom -> ef(goalFrag.expand(text)) where text comes from proofBody substring.
   FFOpen/FFMid/FFClose -> ef(goalFrag.<function>). *)
fun frag_to_cmd proofBody (TacticParse.FAtom a) =
      (case (TacticParse.topSpan a, altSpan a) of
         (SOME (start, endPos), _) =>
           let val text = String.substring(proofBody, start, endPos - start)
           in "ef(goalFrag.expand(" ^ text ^ "));"
           end
       | (NONE, SOME (start, endPos)) =>
           let val text = String.substring(proofBody, start, endPos - start)
           in "ef(goalFrag.expand(" ^ text ^ "));"
           end
       | (NONE, NONE) => "")  (* truly span-less atom = skip *)
  | frag_to_cmd _ (TacticParse.FFOpen opn) =
      "ef(goalFrag." ^ openFragName opn ^ ");"
  | frag_to_cmd _ (TacticParse.FFMid mid) =
      "ef(goalFrag." ^ midFragName mid ^ ");"
  | frag_to_cmd _ (TacticParse.FFClose cls) =
      "ef(goalFrag." ^ closeFragName cls ^ ");"

(* Get the end offset for an FAtom fragment *)
fun fragEnd (TacticParse.FAtom a) =
      (case (TacticParse.topSpan a, altSpan a) of
         (SOME (_, r), _) => r
       | (NONE, SOME (_, r)) => r
       | _ => 0)
  | fragEnd _ = 0  (* structural frag -- caller assigns position *)

(* goalfrag_step_plan: Generate ef() step commands from linearize fragments.
   Returns (end_offset, cmd) pairs for every navigable position.
   Every fragment boundary is a step boundary -- no heuristics needed. *)
fun goalfrag_step_plan proofBody =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    fun isAtom e = Option.isSome (TacticParse.topSpan e)
    val rawFrags = TacticParse.linearize isAtom tree
    val flatFrags = flatten_frags rawFrags

    (* Assign end offsets: walk the flat list, tracking the last FAtom end.
       Structural frags (FOpen/FFMid/FFClose) get the end of the PREVIOUS atom.
       This means navigating to a structural frag shows the state after executing
       it, and the position aligns with the most recent tactic text. *)
    fun assignEnds [] _ acc = rev acc
      | assignEnds (f :: rest) lastAtomEnd acc =
          let
            val cmd = frag_to_cmd proofBody f
            val (endPos, newLast) = case f of
                TacticParse.FAtom _ =>
                  (let val e = fragEnd f in (e, e) end)
              | _ => (lastAtomEnd, lastAtomEnd)
          in
            if String.size cmd > 0
            then assignEnds rest newLast ((endPos, cmd) :: acc)
            else assignEnds rest lastAtomEnd acc
          end
  in
    assignEnds flatFrags 0 []
  end

fun goalfrag_step_plan_json proofBody =
  let
    val steps = goalfrag_step_plan proofBody
    fun stepToJson (endOff, cmd) =
      "{\"end\":" ^ json_int endOff ^ ",\"cmd\":" ^ json_string cmd ^ "}"
    val stepsJson = "[" ^ String.concatWith "," (map stepToJson steps) ^ "]"
  in
    print (json_ok stepsJson ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* goalfrag_prefix_commands: Generate ef() commands to replay up to an offset.
   For positions at fragment boundaries, use the flat fragment list.
   For positions inside an FAtom span, use sliceTacticBlock to generate
   a single ef(expand(<prefix>)) command. *)
fun goalfrag_prefix_commands proofBody endOffset =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    val fullEnd = String.size proofBody
    val defaultSpan = (0, fullEnd)
    fun isAtom e = Option.isSome (TacticParse.topSpan e)
    val rawFrags = TacticParse.linearize isAtom tree
    val flatFrags = flatten_frags rawFrags

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

    (* Collect ef() commands for all complete fragments up to endOffset *)
    fun collectCmds [] _ acc = rev acc
      | collectCmds (TacticParse.FAtom a :: rest) lastEnd acc =
          (case TacticParse.topSpan a of
             SOME (_, endP) =>
               if endP <= endOffset
               then
                 let val cmd = frag_to_cmd proofBody (TacticParse.FAtom a)
                 in collectCmds rest endP (if String.size cmd > 0 then cmd :: acc else acc) end
               else rev acc  (* past the target -- done *)
           | NONE => collectCmds rest lastEnd acc)
      | collectCmds (f :: rest) lastEnd acc =
          if lastEnd <= endOffset
          then
            let val cmd = frag_to_cmd proofBody f
            in collectCmds rest lastEnd (if String.size cmd > 0 then cmd :: acc else acc) end
          else rev acc

    val partialAtom = findPartialAtom flatFrags
  in
    case partialAtom of
      SOME (start, endP) =>
        (* Inside an FAtom: use sliceTacticBlock for the prefix,
           then rewrite e() -> ef(goalFrag.expand()). *)
        let
          val sliceFrags = TacticParse.sliceTacticBlock 0 endOffset false defaultSpan tree
          val eCmd = TacticParse.printFragsAsE proofBody sliceFrags
          fun rewriteEtoEf s =
            if String.isPrefix "e(" s then
              "ef(goalFrag.expand(" ^ String.extract(s, 2, NONE)
            else if String.isPrefix "eall(" s then
              "ef(goalFrag.expand(" ^ String.extract(s, 5, NONE)
            else s
        in
          String.concat (map rewriteEtoEf (String.tokens (fn c => c = #"\n") eCmd))
        end
    | NONE =>
      (* At a fragment boundary: collect ef() commands for all complete frags *)
      let val cmds = collectCmds flatFrags 0 [] in
        String.concatWith "\n" cmds ^ "\n"
      end
  end

fun goalfrag_prefix_commands_json proofBody endOffset =
  print (json_ok (json_string (goalfrag_prefix_commands proofBody endOffset)) ^ "\n")
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
