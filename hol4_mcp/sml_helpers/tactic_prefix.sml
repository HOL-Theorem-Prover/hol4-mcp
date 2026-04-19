(* tactic_prefix.sml - Use HOL's TacticParse for exact tactic replay

   This uses HOL's own sliceTacticBlock to extract syntactically valid
   tactic prefixes, guaranteeing 100% match with holmake semantics.

   Usage:
     prefix_commands_json "rpt strip_tac >> simp[] >> fs[]" 20;
     => {"ok":"e(rpt strip_tac\n  >> simp[]);\n"}

     step_positions_json "rpt strip_tac >> simp[] >> fs[]";
     => {"ok":[13,23,31]}
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

(* Get e() commands to replay tactics up to a given offset in the proof body.
   Uses HOL's sliceTacticBlock for exact semantics. *)
fun prefix_commands proofBody endOffset =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    val defaultSpan = (0, String.size proofBody)
    (* sliceTacticBlock start stop sliceClose defaultSpan tree *)
    val frags = TacticParse.sliceTacticBlock 0 endOffset false defaultSpan tree
    val cmds = TacticParse.printFragsAsE proofBody frags
  in
    cmds
  end

fun prefix_commands_json proofBody endOffset =
  print (json_ok (json_string (prefix_commands proofBody endOffset)) ^ "\n")
  handle e => print (json_err (exnMessage e) ^ "\n");

(* Get all tactic steps with their end positions.
   Each step is a natural "stopping point" in the proof.
   Returns: [{"cmd":"e(tac);","end":offset}, ...] *)
fun tactic_steps proofBody =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    val defaultSpan = (0, String.size proofBody)

    (* Helper to check if a tac_expr is "atomic" for linearization purposes *)
    fun isAtom e = case TacticParse.topSpan e of
        NONE => false
      | SOME (l, r) => true  (* Has a span = treat as atom *)

    (* Linearize the entire proof to get all fragments *)
    val allFrags = TacticParse.linearize isAtom tree

    (* Compute span bounds from nested Opaque nodes for composite structures *)
    fun computeSpan e =
      let
        fun go (TacticParse.Opaque (_, (l, r))) (minL, maxR) = (Int.min(l, minL), Int.max(r, maxR))
          | go (TacticParse.Then ls) acc = foldl (fn (x, a) => go x a) acc ls
          | go (TacticParse.ThenLT (e, ls)) acc = foldl (fn (x, a) => go x a) (go e acc) ls
          | go (TacticParse.First ls) acc = foldl (fn (x, a) => go x a) acc ls
          | go (TacticParse.Try e) acc = go e acc
          | go (TacticParse.Repeat e) acc = go e acc
          | go (TacticParse.Group (_, _, e)) acc = go e acc
          | go (TacticParse.RepairGroup (_, _, e, _)) acc = go e acc
          | go (TacticParse.LThenLT ls) acc = foldl (fn (x, a) => go x a) acc ls
          | go (TacticParse.LThen (e, ls)) acc = foldl (fn (x, a) => go x a) (go e acc) ls
          | go (TacticParse.LThen1 e) acc = go e acc
          | go (TacticParse.LTacsToLT e) acc = go e acc
          | go (TacticParse.LNullOk e) acc = go e acc
          | go (TacticParse.LFirstLT e) acc = go e acc
          | go (TacticParse.LAllGoals e) acc = go e acc
          | go (TacticParse.LNthGoal (e, _)) acc = go e acc
          | go (TacticParse.LLastGoal e) acc = go e acc
          | go (TacticParse.LHeadGoal e) acc = go e acc
          | go (TacticParse.LSplit (sp, e1, e2)) acc = go e1 (go e2 acc)
          | go (TacticParse.LSelectThen (e1, e2)) acc = go e1 (go e2 acc)
          | go TacticParse.LReverse acc = acc
          | go _ acc = acc
        val (minL, maxR) = go e (String.size proofBody, 0)
      in
        if maxR > 0 then SOME (minL, maxR) else NONE
      end

    (* Extract spans from fragments to find step boundaries *)
    fun fragSpan (TacticParse.FAtom a) = 
          (case TacticParse.topSpan a of
             SOME sp => SOME sp
           | NONE => computeSpan a)
      | fragSpan (TacticParse.FGroup (p, _)) = SOME p
      | fragSpan _ = NONE

    (* Collect end positions of each top-level step *)
    fun collectEnds [] acc = rev acc
      | collectEnds (f::fs) acc =
          case fragSpan f of
            SOME (_, endPos) => collectEnds fs (endPos :: acc)
          | NONE => collectEnds fs acc

    val endPositions = collectEnds allFrags []

    (* For each end position, generate the e() command to reach that state *)
    fun makeStep endPos =
      let
        val frags = TacticParse.sliceTacticBlock 0 endPos false defaultSpan tree
        val cmd = TacticParse.printFragsAsE proofBody frags
      in
        (cmd, endPos)
      end
  in
    map makeStep endPositions
  end

fun step_to_json (cmd, endPos) =
  "{\"cmd\":" ^ json_string cmd ^ ",\"end\":" ^ json_int endPos ^ "}"

fun tactic_steps_json proofBody =
  let
    val steps = tactic_steps proofBody
    val jsonSteps = "[" ^ String.concatWith "," (map step_to_json steps) ^ "]"
  in
    print (json_ok jsonSteps ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* Simpler API: just get step count and end positions *)
fun step_positions proofBody =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    fun isAtom e = Option.isSome (TacticParse.topSpan e)
    val allFrags = TacticParse.linearize isAtom tree

    fun fragSpan (TacticParse.FAtom a) = TacticParse.topSpan a
      | fragSpan (TacticParse.FGroup (p, _)) = SOME p
      | fragSpan _ = NONE

    fun collectEnds [] acc = rev acc
      | collectEnds (f::fs) acc =
          case fragSpan f of
            SOME (_, endPos) => collectEnds fs (endPos :: acc)
          | NONE => collectEnds fs acc

    val basePositions = collectEnds allFrags []

    (* Find internal boundaries of `by` clauses (ThenLT(Subgoal, [LThen1])).
       The Subgoal end position enables find_failing_substep to bisect
       between sg selection and the by tactic. sliceTacticBlock handles
       the correct prefix generation at these boundaries. *)
    fun findByBoundaries (TacticParse.ThenLT (TacticParse.Subgoal (_, sgEnd), _)) acc =
          sgEnd :: acc
      | findByBoundaries (TacticParse.Then es) acc =
          foldl (fn (e, a) => findByBoundaries e a) acc es
      | findByBoundaries (TacticParse.ThenLT (e, arms)) acc =
          foldl (fn (e, a) => findByBoundaries e a)
            (findByBoundaries e acc) arms
      | findByBoundaries (TacticParse.Group (_, _, e)) acc = findByBoundaries e acc
      | findByBoundaries (TacticParse.LThen1 e) acc = findByBoundaries e acc
      | findByBoundaries _ acc = acc

    val byPositions = findByBoundaries tree []

    (* Merge, sort, deduplicate *)
    val allPositions = Portable.int_sort (basePositions @ byPositions)
    fun dedup [] = []
      | dedup [x] = [x]
      | dedup (x :: y :: rest) = if x = y then dedup (y :: rest) else x :: dedup (y :: rest)
  in
    dedup allPositions
  end

fun step_positions_json proofBody =
  let
    val positions = step_positions proofBody
    val jsonArr = "[" ^ String.concatWith "," (map json_int positions) ^ "]"
  in
    print (json_ok jsonArr ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* Generate e() commands for full proof using sliceTacticBlock.
   Each step becomes a separate e() call, enabling backup_n. *)
fun step_commands proofBody =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    val defaultSpan = (0, String.size proofBody)
    (* Full slice from 0 to end, sliceClose=false *)
    val frags = TacticParse.sliceTacticBlock 0 (String.size proofBody) false defaultSpan tree
    val cmds = TacticParse.printFragsAsE proofBody frags
  in
    cmds
  end

fun step_commands_json proofBody =
  print (json_ok (json_string (step_commands proofBody)) ^ "\n")
  handle e => print (json_err (exnMessage e) ^ "\n");

(* backup_n - undo N e() calls in the goaltree *)
fun backup_n 0 = ()
  | backup_n n = (proofManagerLib.b(); backup_n (n - 1));

(* Generate e() commands for a slice of the proof body.
   Used after backup_n to execute just the remaining portion.
   startOffset/endOffset are character positions in proofBody.
   When slicing inside >-, generates HEADGOAL automatically. *)
fun partial_step_commands proofBody startOffset endOffset =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    val defaultSpan = (0, String.size proofBody)
    (* sliceClose=false to avoid FFClose tokens unlinearize can't handle *)
    val frags = TacticParse.sliceTacticBlock startOffset endOffset false defaultSpan tree
    val cmds = TacticParse.printFragsAsE proofBody frags
  in
    cmds
  end

fun partial_step_commands_json proofBody startOffset endOffset =
  print (json_ok (json_string (partial_step_commands proofBody startOffset endOffset)) ^ "\n")
  handle e => print (json_err (exnMessage e) ^ "\n");

(* step_plan: Get step boundaries aligned with executable commands.
   Returns (end_offset, command) pairs for O(1) tactic navigation.
   
   Design:
   - >> chains: decompose into individual e()/eall() commands (multiple backup points)
   - >- chains: treat as ATOMIC (one backup point, no internal navigation)
   
   This is correct because:
   - >> is sequential: each tactic runs on results of previous, intermediate states exist
   - >- is parallel routing: branches are concurrent, not sequential steps
   
   Implementation note:
   For `a >> b >> c >- d >- e` (AST: ThenLT(ThenLT(Then([a,b,c]), [d]), [e])):
   - We extract the base Then([a,b,c]) and linearize THAT
   - The >- suffix becomes ONE final step: eall(ALL_TAC >- d >- e)
   This avoids the problem where making ThenLT atomic makes everything one step. *)

(* Compute overall span of a tac_expr by finding min/max from nested Opaque nodes.
   Returns NONE if no spans found (shouldn't happen for valid parsed tactics). *)
fun computeSpan e =
  let
    fun merge NONE s = s
      | merge s NONE = s
      | merge (SOME (l1, r1)) (SOME (l2, r2)) = SOME (Int.min(l1, l2), Int.max(r1, r2))
    
    fun go (TacticParse.Opaque (_, sp)) = SOME sp
      | go (TacticParse.LOpaque (_, sp)) = SOME sp
      | go (TacticParse.OOpaque (_, sp)) = SOME sp
      | go (TacticParse.LSelectGoal sp) = SOME sp
      | go (TacticParse.LSelectGoals sp) = SOME sp
      | go (TacticParse.List (sp, es)) = foldl (fn (e, acc) => merge (go e) acc) (SOME sp) es
      | go (TacticParse.Group (_, sp, e)) = merge (SOME sp) (go e)
      | go (TacticParse.RepairEmpty (_, sp, _)) = SOME sp
      | go (TacticParse.RepairGroup (sp, _, e, _)) = merge (SOME sp) (go e)
      | go (TacticParse.Then es) = foldl (fn (e, acc) => merge (go e) acc) NONE es
      | go (TacticParse.ThenLT (e, es)) = foldl (fn (e, acc) => merge (go e) acc) (go e) es
      | go (TacticParse.LThenLT es) = foldl (fn (e, acc) => merge (go e) acc) NONE es
      | go (TacticParse.First es) = foldl (fn (e, acc) => merge (go e) acc) NONE es
      | go (TacticParse.LFirst es) = foldl (fn (e, acc) => merge (go e) acc) NONE es
      | go (TacticParse.Try e) = go e
      | go (TacticParse.LTry e) = go e
      | go (TacticParse.Repeat e) = go e
      | go (TacticParse.LRepeat e) = go e
      | go (TacticParse.MapEvery (sp, es)) = foldl (fn (e, acc) => merge (go e) acc) (SOME sp) es
      | go (TacticParse.MapFirst (sp, es)) = foldl (fn (e, acc) => merge (go e) acc) (SOME sp) es
      | go (TacticParse.Rename sp) = SOME sp
      | go (TacticParse.Subgoal sp) = SOME sp
      | go (TacticParse.LThen (e, es)) = foldl (fn (e, acc) => merge (go e) acc) (go e) es
      | go (TacticParse.LThen1 e) = go e
      | go (TacticParse.LTacsToLT e) = go e
      | go (TacticParse.LNullOk e) = go e
      | go (TacticParse.LFirstLT e) = go e
      | go (TacticParse.LAllGoals e) = go e
      | go (TacticParse.LNthGoal (e, sp)) = merge (go e) (SOME sp)
      | go (TacticParse.LLastGoal e) = go e
      | go (TacticParse.LHeadGoal e) = go e
      | go (TacticParse.LSplit (sp, e1, e2)) = merge (SOME sp) (merge (go e1) (go e2))
      | go TacticParse.LReverse = NONE
      | go (TacticParse.LSelectThen (e1, e2)) = merge (go e1) (go e2)
  in
    go e
  end

(* Extract the innermost base from nested ThenLT structures.
   For ThenLT(ThenLT(Then([a,b,c]), [d]), [e]) returns Then([a,b,c]).
   Also returns the position just before the first arm (to find >- suffix). *)
fun extractThenLTBaseAndFirstArm (TacticParse.ThenLT (e, arms)) = 
      let 
        val (base, _) = extractThenLTBaseAndFirstArm e
        (* Find the start of the first arm at this level *)
        val armStart = case arms of
            [] => NONE
          | (firstArm::_) => 
              case computeSpan firstArm of
                SOME (start, _) => SOME start
              | NONE => NONE
      in
        (base, armStart)
      end
  | extractThenLTBaseAndFirstArm (TacticParse.Group (_, _, e)) = extractThenLTBaseAndFirstArm e
  | extractThenLTBaseAndFirstArm e = (e, NONE)

(* Simple base extraction for backward compatibility *)
fun extractThenLTBase e = #1 (extractThenLTBaseAndFirstArm e)

(* Find the start of the first >- arm in a ThenLT chain.
   Scans back to find the >- operator position. *)
fun findFirstArmStart (TacticParse.ThenLT (e, arms)) =
      let
        val innerArmStart = findFirstArmStart e
      in
        case innerArmStart of
          SOME _ => innerArmStart  (* Inner ThenLT has first arm *)
        | NONE => 
            (* This is the innermost ThenLT, get arm start from here *)
            case arms of
              [] => NONE
            | (firstArm::_) => 
                case computeSpan firstArm of
                  SOME (start, _) => SOME start
                | NONE => NONE
      end
  | findFirstArmStart (TacticParse.Group (_, _, e)) = findFirstArmStart e
  | findFirstArmStart _ = NONE

(* Find the position of ThenLT operator before a given position in the text.
   Handles: >- >| >>> >~ >>~ >>~- THEN1 THENL THEN_LT *)
fun findThenLTOperator proofBody armStart =
  let
    val len = String.size proofBody
    fun charAt i = if i >= 0 andalso i < len then String.sub(proofBody, i) else #" "
    
    (* Check for 2-char operators: >- >| >~ *)
    fun is2CharOp pos =
      let val c1 = charAt pos val c2 = charAt (pos + 1)
      in c1 = #">" andalso (c2 = #"-" orelse c2 = #"|" orelse c2 = #"~")
      end
    
    (* Check for 3-char operators: >>> >>~ *)
    fun is3CharOp pos =
      let val c1 = charAt pos val c2 = charAt (pos + 1) val c3 = charAt (pos + 2)
      in c1 = #">" andalso c2 = #">" andalso (c3 = #">" orelse c3 = #"~")
      end
    
    (* Check for 4-char operator: >>~- *)
    fun is4CharOp pos =
      let val c1 = charAt pos val c2 = charAt (pos + 1) 
          val c3 = charAt (pos + 2) val c4 = charAt (pos + 3)
      in c1 = #">" andalso c2 = #">" andalso c3 = #"~" andalso c4 = #"-"
      end
    
    fun scanBack pos =
      if pos < 2 then 0
      else if is4CharOp (pos - 4) then pos - 4
      else if is3CharOp (pos - 3) then pos - 3
      else if is2CharOp (pos - 2) then pos - 2
      else scanBack (pos - 1)
  in
    scanBack armStart
  end

(* Check if an expression has ThenLT at top level (unwrapping Groups) *)
fun hasThenLTAtTop (TacticParse.ThenLT _) = true
  | hasThenLTAtTop (TacticParse.Group (_, _, e)) = hasThenLTAtTop e
  | hasThenLTAtTop _ = false

(* Check if a tac_expr contains any goal-routing structure anywhere in the tree.
   Goal-routing = ThenLT, Subgoal, LSelectGoal, LSelectGoals, LSelectThen,
   LSplit, LReverse, LNthGoal, LLastGoal, LHeadGoal, LNullOk, etc.
   These create or route between subgoals, making fine-grained stepping
   impossible without restructuring the proof (e.g., via suspend/Resume). *)
fun hasGoalRouting (TacticParse.ThenLT _) = true
  | hasGoalRouting (TacticParse.Subgoal _) = true
  | hasGoalRouting (TacticParse.LSelectGoal _) = true
  | hasGoalRouting (TacticParse.LSelectGoals _) = true
  | hasGoalRouting (TacticParse.LSelectThen _) = true
  | hasGoalRouting (TacticParse.LSplit _) = true
  | hasGoalRouting TacticParse.LReverse = true
  | hasGoalRouting (TacticParse.LNthGoal _) = true
  | hasGoalRouting (TacticParse.LLastGoal _) = true
  | hasGoalRouting (TacticParse.LHeadGoal _) = true
  | hasGoalRouting (TacticParse.LNullOk _) = true
  | hasGoalRouting (TacticParse.LThen1 _) = true
  | hasGoalRouting (TacticParse.LThenLT _) = true
  | hasGoalRouting (TacticParse.LThen _) = true
  | hasGoalRouting (TacticParse.Then es) = List.exists hasGoalRouting es
  | hasGoalRouting (TacticParse.First es) = List.exists hasGoalRouting es
  | hasGoalRouting (TacticParse.LFirst es) = List.exists hasGoalRouting es
  | hasGoalRouting (TacticParse.Group (_, _, e)) = hasGoalRouting e
  | hasGoalRouting (TacticParse.RepairGroup (_, _, e, _)) = hasGoalRouting e
  | hasGoalRouting (TacticParse.Try e) = hasGoalRouting e
  | hasGoalRouting (TacticParse.LTry e) = hasGoalRouting e
  | hasGoalRouting (TacticParse.Repeat e) = hasGoalRouting e
  | hasGoalRouting (TacticParse.LRepeat e) = hasGoalRouting e
  | hasGoalRouting (TacticParse.LTacsToLT _) = true
  | hasGoalRouting (TacticParse.LAllGoals e) = hasGoalRouting e
  | hasGoalRouting (TacticParse.LFirstLT _) = true
  | hasGoalRouting _ = false

(* Check if a list_tac_expr is LThen1 (>- arm, decomposable) *)
fun isLThen1Arm (TacticParse.LThen1 _) = true
  | isLThen1Arm _ = false

(* Check if all arms in nested ThenLT chain are LThen1.
   If ANY arm is not LThen1 (e.g., >| produces LNullOk), the entire
   suffix must stay atomic because >| arms can produce subgoals. *)
fun allArmsDecomposable (TacticParse.ThenLT (e, arms)) =
      List.all isLThen1Arm arms andalso allArmsDecomposable e
  | allArmsDecomposable (TacticParse.Group (_, _, e)) = allArmsDecomposable e
  | allArmsDecomposable _ = true

(* Collect inner tac_exprs from LThen1 arms in nested ThenLT chain.
   Returns innermost arms first (matches evaluation order). *)
fun collectLThen1Inners (TacticParse.ThenLT (e, arms)) =
      collectLThen1Inners e @
      List.mapPartial (fn (TacticParse.LThen1 inner) => SOME inner | _ => NONE) arms
  | collectLThen1Inners (TacticParse.Group (_, _, e)) = collectLThen1Inners e
  | collectLThen1Inners _ = []

fun step_plan proofBody =
  let
    val tree = TacticParse.parseTacticBlock proofBody
    val defaultSpan = (0, String.size proofBody)
    val fullEnd = String.size proofBody

    (* Standard isAtom for Then chains - NO special ThenLT handling *)
    fun isAtom e = Option.isSome (TacticParse.topSpan e)

    (* Convert e() to eall() for subsequent steps *)
    fun eToEall cmd =
      if String.isPrefix "e(" cmd then
        "eall(" ^ String.extract(cmd, 2, NONE)
      else cmd

    (* Extract spans from fragments *)
    fun fragSpan (TacticParse.FAtom a) = 
          (case TacticParse.topSpan a of
             SOME sp => SOME sp
           | NONE => computeSpan a)
      | fragSpan (TacticParse.FGroup (p, _)) = SOME p
      | fragSpan _ = NONE

    (* Collect end positions and AST exprs from fragments *)
    fun collectEndExprs [] acc = rev acc
      | collectEndExprs (f::fs) acc =
          case f of
            TacticParse.FAtom a =>
              (case (case TacticParse.topSpan a of SOME sp => SOME sp | NONE => computeSpan a) of
                 SOME (_, endPos) => collectEndExprs fs ((endPos, SOME a) :: acc)
               | NONE => collectEndExprs fs acc)
          | TacticParse.FGroup (p, _) =>
              collectEndExprs fs ((#2 p, NONE) :: acc)
          | _ => collectEndExprs fs acc

    (* Generate steps from fragments, end positions and AST exprs.
       Returns (endOff, cmd, goalRouting) triples. *)
    fun makeSteps baseTree [] _ _ acc = rev acc
      | makeSteps baseTree ((endPos, exprOpt)::rest) prevEnd isFirst acc =
          let
            val frags = TacticParse.sliceTacticBlock prevEnd endPos false defaultSpan baseTree
            val rawCmd = TacticParse.printFragsAsE proofBody frags
            val cmd = if isFirst then rawCmd else eToEall rawCmd
            val gr = case exprOpt of
                       SOME e => hasGoalRouting e
                     | NONE => false
            val step = if String.size cmd > 0 then [(endPos, cmd, gr)] else []
          in
            makeSteps baseTree rest endPos false (step @ acc)
          end

  in
    if hasThenLTAtTop tree then
      (* Top-level ThenLT: decompose >> base chain, then handle arms.
         
         If all arms are LThen1 (>-), decompose each into e(arm_text).
         Each >- arm solves exactly one goal (THEN1 semantics), so
         sequential e(arm_k) is equivalent to the parallel >- chain.
         
         If any arm is NOT LThen1 (e.g., >| produces LNullOk), keep
         entire suffix atomic as elt(ALL_LT ...) because >| arms can
         produce subgoals that corrupt sequential execution.
         
         Refs: goalStack.sml expandf/expand_listf, Tactical.sml THEN1/ALL_LT *)
      let
        val base = extractThenLTBase tree
        val baseFrags = TacticParse.linearize isAtom base
        val baseEndExprs = collectEndExprs baseFrags []
        val baseSteps = makeSteps base baseEndExprs 0 true []
        
        val suffixSteps =
          if allArmsDecomposable tree then
            (* All arms are LThen1: decompose into individual e() steps.
               Each arm may itself contain goal-routing (e.g., nested by). *)
            let
              val innerExprs = collectLThen1Inners tree
              fun armToStep expr =
                case computeSpan expr of
                  SOME (start, endPos) =>
                    let val text = String.substring(proofBody, start, endPos - start)
                    in SOME (endPos, "e(" ^ text ^ ");\n", hasGoalRouting expr)
                    end
                | NONE => NONE
            in
              List.mapPartial armToStep innerExprs
            end
          else
            (* Has >| or other non-LThen1 arm: keep suffix atomic.
               Find operator position by scanning forward from base span end,
               skipping whitespace and ')' (grouped bases like "(a >> b) >-"). *)
            let
              val baseSpanOpt = computeSpan base
            in
              case baseSpanOpt of
                SOME (_, baseEnd) =>
                  let
                    fun skipWsAndClose i =
                      if i >= fullEnd then i
                      else let val c = String.sub(proofBody, i)
                      in if Char.isSpace c orelse c = #")" then skipWsAndClose (i + 1) else i
                      end
                    val opStart = skipWsAndClose baseEnd
                    val suffixText = String.substring(proofBody, opStart, fullEnd - opStart)
                    (* `by` is sugar for `sg >- tac`. Replace "by" with ">-". *)
                    val isByOp = String.size suffixText >= 2 andalso
                      String.substring(suffixText, 0, 2) = "by" andalso
                      (String.size suffixText = 2 orelse
                       not (Char.isAlphaNum (String.sub(suffixText, 2))))
                    val suffix =
                      if isByOp
                      then ">- " ^ String.extract(suffixText, 2, NONE)
                      else suffixText
                    val cmd = "elt(ALL_LT " ^ suffix ^ ");\n"
                  in
                    [(fullEnd, cmd, true)]  (* elt = always goal-routing *)
                  end
              | NONE =>
                  let
                    val _ = TextIO.output(TextIO.stdErr,
                      "step_plan: WARNING: ThenLT with no arm spans, falling back to atomic\n")
                    val frags = TacticParse.sliceTacticBlock 0 fullEnd false defaultSpan tree
                    val cmd = TacticParse.printFragsAsE proofBody frags
                  in
                    [(fullEnd, cmd, true)]  (* fallback for ThenLT = goal-routing *)
                  end
            end
      in
        baseSteps @ suffixSteps
      end
    else
      (* No ThenLT at top: normal linearization *)
      let
        val allFrags = TacticParse.linearize isAtom tree
        val endExprs = collectEndExprs allFrags []
      in
        makeSteps tree endExprs 0 true []
      end
  end

fun step_plan_json proofBody =
  let
    val steps = step_plan proofBody

    (* No synthetic fallback here.
       If there are no executable steps (e.g., empty body/comments-only),
       return []. Parse errors still surface via {"err":...} through handler. *)
    fun stepToJson (endOff, cmd, gr) =
      "{\"end\":" ^ json_int endOff ^ ",\"cmd\":" ^ json_string cmd ^
      (if gr then ",\"gr\":true" else "") ^ "}"
    val stepsJson = "[" ^ String.concatWith "," (map stepToJson steps) ^ "]"
  in
    print (json_ok stepsJson ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* =============================================================================
 * Proof Timing
 * =============================================================================
 * Execute a tactic command and return timing as JSON. Stateless.
 *)

(* timed_step_json: Execute command, return timing with goal counts.
   Output: {"ok":{"real_ms":N,"usr_ms":N,"sys_ms":N,"goals_before":N,"goals_after":N}} *)
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
   Args: goal (string), name (string), tactics (string list), store (bool), timeout_sec (real)
   Output: {"ok":{"stored":true/false,"name":"...",
            "trace":[{"real_ms":N,"goals_before":N,"goals_after":N}, ...]}}
   Does: drop_all -> g goal -> run tactics with timing -> save_thm if OK and store=true *)
fun verify_theorem_json goal name tactics store timeout_sec =
  let
    val _ = drop_all ()
    val _ = smlExecute.quse_string ("g `" ^ goal ^ "`;")
  in
    verify_core name tactics store timeout_sec
  end;

(* =============================================================================
 * Definition Termination Goal Extraction
 * =============================================================================
 * Extract the termination conditions (TC) goal from a recursive definition
 * body WITHOUT permanently modifying the theory.
 *
 * Used for Definition ... Termination ... End blocks where we need to
 * recreate the termination proof goal for interactive state inspection.
 *
 * Approach: temporarily create the defn via Hol_defn inside nested
 * try_grammar_extension + try_theory_extension, extract the TC goal
 * string, then roll back all theory and grammar changes.
 *
 * MUST be called BEFORE the Definition block is processed (so the
 * function constant doesn't exist yet). If the constant already exists,
 * try_theory_extension rollback won't properly undo the replacement
 * (KernelSig.insert retires the old constant silently).
 *)

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
 * =============================================================================
 * Extract the goal for a Resume block from the suspension DB.
 * Returns: {"ok":{"asms":[...], "goal":"..."}} or {"err":"..."}
 *)

(* Look up (asms, concl) for a Resume block directly from the suspension DB.
   Shared by display (extract_resume_goal_json) and verification
   (verify_resume_json) so both use the same live term — no print/reparse
   round-trip (which is lossy, e.g. "case SOME (a,b) => body" with unused
   a,b collapses to "SOME v => body" on printing). *)
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
    (* show_types on for display so users see accurate types; this string is
       display-only and is NOT used to rebuild the goal for verification. *)
    fun typed_term_to_string t =
      Lib.with_flag (Globals.show_types, true) term_to_string t
    val json = "{\"asms\":" ^ json_string_array (map typed_term_to_string asms) ^
               ",\"goal\":" ^ json_string (typed_term_to_string concl) ^ "}"
  in
    print (json_ok json ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* Verify a Resume block. Re-extracts the suspended goal at verify time and
   calls proofManagerLib.set_goal with the live term, avoiding any
   pretty-print/reparse round-trip. *)
fun verify_resume_json suspension_name label_name name tactics store timeout_sec =
  let
    val _ = drop_all ()
    val (asms, concl) = resume_goal_terms suspension_name label_name
    val _ = proofManagerLib.set_goal (asms, concl)
  in
    verify_core name tactics store timeout_sec
  end
  handle e => print (json_err (exnMessage e) ^ "\n");