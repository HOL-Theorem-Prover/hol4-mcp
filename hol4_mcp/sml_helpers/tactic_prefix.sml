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
    (* A tactic body is ONE declaration. A stray delimiter ends the expression
       early and leaves the REST of the body as further declarations, which the
       caller never sees: the step plan silently loses every tactic after it.
       A second declaration is therefore always a broken body. *)
    val nextDec = (SOME (#parseDec result ()))
                  handle Interrupt => raise Interrupt | _ => NONE
    val () =
      case nextDec of
        SOME (SOME _) =>
          raise Fail "parseTacticBlockFromString: trailing text after the \
                     \tactic expression (surplus or missing delimiter?)"
      | _ => ()
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

(* HOL's goal printer warns when a goal carries two variables of the same name
   and different types (goalStack.check_vars), but that printer never runs here:
   goals are rendered with term_to_string, which shows no types at all, so the
   colliding variables reach the caller indistinguishable. Report them. *)
fun same_name_clashes (asms, concl) =
  let
    val vs = List.foldl (fn (t, acc) => acc @ free_vars t) [] (concl :: asms)
    fun add (v, acc) = if List.exists (fn u => aconv u v) acc then acc else acc @ [v]
    val uniq = List.foldl add [] vs
    fun nameOf v = #1 (dest_var v)
    fun typeOf v = #2 (dest_var v)
    fun clashes v =
      List.exists (fn u => nameOf u = nameOf v
                           andalso Type.compare (typeOf u, typeOf v) <> EQUAL)
                  uniq
    val bad = List.filter clashes uniq
    fun descr v = nameOf v ^ " : " ^ Parse.type_to_string (typeOf v)
  in
    if null bad then []
    else ["WARNING: goal contains variables of same name but different types: " ^
          String.concatWith ", " (map descr bad)]
  end

fun goals_json () =
  let
    val goals = top_goals()
    val warns = List.concat (map same_name_clashes goals)
    val body = "\"ok\":" ^ goals_to_json_array goals
  in
    print ("{" ^ body ^
           (if null warns then ""
            else ",\"warnings\":" ^ json_string_array warns) ^ "}\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* db_search_json: first-class DB search for the hol_search MCP tool.
   query   - substring match on theorem name (DB.find), "" to skip
   pattern - term pattern for DB.match (Parse.Term), "" to skip
   thy     - restrict results to one theory, "" for all
   limit   - max results in output (total match count still reported) *)
fun db_search_json query pattern thy limit =
  let
    fun key ((t, n), _) = t ^ "$" ^ n
    val found =
      case (query, pattern) of
        ("", "") => raise Fail "db_search_json: need a query or a pattern"
      | (q, "") => DB.find q
      | ("", p) => DB.match (if thy = "" then [] else [thy])
                            (Parse.Term [QUOTE p])
      | (q, p) =>
          let
            val keys = HOLset.addList (HOLset.empty String.compare,
                                       map key (DB.find q))
            val bypat = DB.match (if thy = "" then [] else [thy])
                                 (Parse.Term [QUOTE p])
          in
            List.filter (fn d => HOLset.member (keys, key d)) bypat
          end
    val found = if thy = "" then found
                else List.filter (fn ((t, _), _) => t = thy) found
    val total = length found
    val shown = if total > limit andalso limit >= 0
                then List.take (found, limit) else found
    fun entry ((t, n), (th, _, _)) =
      "{\"theory\":" ^ json_string t ^
      ",\"name\":" ^ json_string n ^
      ",\"statement\":" ^ json_string (term_to_string (concl th)) ^ "}"
  in
    print (json_ok ("{\"total\":" ^ json_int total ^
                    ",\"results\":[" ^
                    String.concatWith "," (map entry shown) ^ "]}") ^ "\n")
  end
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
   FBracket(FOpenThen1 _, [inner], FClose, expr) -> FOpenThen1 _, inner..., FClose
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
  | openFragName (TacticParse.FOpenThen1 _) = "open_then1"
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

(* Extract fragment type: "expand", "open", "mid", "close", "select", or
   "open_by"/"open_suffices_by" (merged away by merge_by_steps) *)
fun frag_type (TacticParse.FAtom (TacticParse.LSelectGoal _)) = "select"
  | frag_type (TacticParse.FAtom (TacticParse.LSelectGoals _)) = "selects"
  | frag_type (TacticParse.FAtom (TacticParse.OOpaque _)) = "expand"
  | frag_type (TacticParse.FAtom (TacticParse.List _)) = "expand"
  | frag_type (TacticParse.FAtom a) =
      (* list_tactic atoms (e.g. THEN_LT Q.SELECT_GOALS_LT_THEN ...) need expand_list *)
      if TacticParse.isTac a then "expand" else "expand_list"
  | frag_type (TacticParse.FFOpen (TacticParse.FOpenBy _)) = "open_by"
  | frag_type (TacticParse.FFOpen (TacticParse.FOpenSufficesBy _)) = "open_suffices_by"
  | frag_type (TacticParse.FFOpen _) = "open"
  | frag_type (TacticParse.FFMid _) = "mid"
  | frag_type (TacticParse.FFClose _) = "close"
  | frag_type _ = ""

(* Unwrap Group/RepairGroup wrappers to reach the underlying atom kind. *)
fun unwrapAtom (TacticParse.Group (_, _, e)) = unwrapAtom e
  | unwrapAtom (TacticParse.RepairGroup (_, _, e, _)) = unwrapAtom e
  | unwrapAtom e = e

(* Term-quotation openers: ASCII backtick, and the UTF-8 bytes of ‘ and “. *)
val quoteOpeners = ["`", "\226\128\152", "\226\128\156"]

fun startsWithQuote t = List.exists (fn q => String.isPrefix q t) quoteOpeners

(* Does the atom's own span cover a complete tactic, or only an operand?
   TacticParse's `group tac a b` records exactly that in Group's first field:
     `Q` by tac      -> bare Subgoal, span = the quotation          (operand)
     sg `Q`          -> Group(true, whole call, Subgoal _)          (tactic)
     >>~- ([p], t)   -> Group(false, p, Rename p)                   (operand)
     rename [p]      -> Group(true, whole call, Rename p)           (tactic)
   An operand span must be realized as a tactic before goalFrag.expand (a
   tactic -> _) receives it. Both Subgoal and Rename have topSpan = NONE, so
   both forms are wrapped and the flag — not the span's first character — is
   the discriminator. *)
fun spanIsTactic (TacticParse.Group (b, _, _)) = b
  | spanIsTactic (TacticParse.RepairGroup _) = true
  | spanIsTactic _ = false

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
      in case unwrapAtom a of
           (* `Q` by tac spans only the quotation; realize it as the tactic
              HOL4 equates that form with. `by`'s left operand is not always a
              quotation (tac1 by tac2), and those spans are already tactics. *)
           TacticParse.Subgoal _ =>
             if startsWithQuote raw then "sg " ^ raw else raw
           (* `Q` suffices_by tac elaborates to ThenLT (Subgoal Q, [LReverse])
              under a Group whose span is likewise only the quotation, so it
              reaches here as a ThenLT rather than a bare Subgoal. Use the
              native suffices_by operand: reversed sg strips Q into the
              assumptions, whereas SUFF_TAC presents Q ==> G to the closer. *)
         | TacticParse.ThenLT (TacticParse.Subgoal _, [TacticParse.LReverse]) =>
             if startsWithQuote raw then "Q_TAC SUFF_TAC " ^ raw else raw
           (* An operand span carries only the pattern of `>>~- ([pat], tac)`,
              applied as the SELECT tactic between open_select_lt and
              next_select_lt; realize it the way TacticParse does. *)
         | TacticParse.Rename _ =>
             if spanIsTactic a then raw else "Q.RENAME_TAC " ^ raw
         | _ => raw
      end
  | frag_text proofBody (TacticParse.FFOpen (TacticParse.FOpenBy ((s, e), _))) =
      String.substring(proofBody, s, e - s)
  | frag_text proofBody (TacticParse.FFOpen (TacticParse.FOpenSufficesBy ((s, e), _))) =
      String.substring(proofBody, s, e - s)
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
(* Flat mode: re-expand parenthesised groups even when they contain a
   goal-positional LT operator. Sound only where the group is applied to
   exactly ONE goal; the caller (hol_cursor's inside-group navigation)
   checks that at each such group's entry before replaying past it. *)
val reexpand_positional_groups = ref false

fun reexpand_group_atoms frags = reexpand_group_atoms_in false frags

(* `arm`: the first fragment is the arm of a `>-` / THEN1, so it receives
   exactly one goal. A group with a goal-positional operator anywhere in its
   body is re-expanded only there (or in flat mode): applied by THEN, or at
   the proof start, it runs once per goal it receives, which a flat replay
   cannot express. Mirrors `_is_then_group` in hol_cursor.py. *)
and reexpand_group_atoms_in arm frags =
  let
    (* Only re-expand Group atoms containing compound expressions (Then, ThenLT, etc.)
       that produce useful navigable sub-steps. Single-step wrappers like Repeat,
       Try, LNullOk etc. should stay atomic — their open/close structure adds
       navigation overhead without useful intermediate goal states.
       ThenLT whose list-tactic argument contains LReverse / LTacsToLT / other
       structural-only LT-elements MUST stay opaque — re-expanding produces
       FAtoms (LReverse, etc.) that have no span, get empty text from
       frag_text, and are silently dropped by assignEnds, which would lose
       e.g. the `reverse` in `reverse TOP_CASE_TAC`. *)
    fun ltElemIsStructuralOnly TacticParse.LReverse = true
      | ltElemIsStructuralOnly _ = false
    fun lsHasStructuralOnly ls = List.exists ltElemIsStructuralOnly ls
    (* Goal-position-sensitive LT operators. When present in a Group's body,
       the Group must NOT be re-expanded — re-expansion produces flat
       fragments matching the un-parenthesised semantics (e.g. open_then1
       focuses goal 1 GLOBALLY). HOL4 source semantics for the parenthesised
       form distributes the whole tactic per source goal under outer THEN,
       running the LT op once per source. The two diverge in multi-goal
       contexts. Keep Group opaque so goalFrag.expand runs the whole tactic
       atomically per source goal — matches Holmake. *)
    (* An expression is goal-positional if it contains, at any depth, an
       operator that picks goals by position or pattern: `>-`, `>|`,
       `>>>` with NTH_GOAL/LASTGOAL/HEADGOAL/FIRST_LT, a split, or a
       goal selection. The same test serves an LT element and a Group
       body: `>|` parses as `ThenLT(_, [LNullOk (LTacsToLT _)])`, and a
       positional operator under TRY, REPEAT, FIRST, MAP_EVERY or `by`
       still runs once per goal the enclosing tactic is applied to. *)
    fun exprHasGoalPositional e =
          case e of
            TacticParse.LThen1 _ => true
          | TacticParse.LFirst _ => true
          | TacticParse.LTacsToLT _ => true
          | TacticParse.LSplit _ => true
          | TacticParse.LNthGoal _ => true
          | TacticParse.LLastGoal _ => true
          | TacticParse.LHeadGoal _ => true
          | TacticParse.LSelectThen _ => true
          | TacticParse.LSelectGoal _ => true
          | TacticParse.LSelectGoals _ => true
          | TacticParse.Then es => lsHasGoalPositional es
          | TacticParse.ThenLT (e, ls) =>
              exprHasGoalPositional e orelse lsHasGoalPositional ls
          | TacticParse.LThen (e, ls) =>
              exprHasGoalPositional e orelse lsHasGoalPositional ls
          | TacticParse.LThenLT ls => lsHasGoalPositional ls
          | TacticParse.First es => lsHasGoalPositional es
          | TacticParse.FirstProve es => lsHasGoalPositional es
          | TacticParse.MapEvery (_, es) => lsHasGoalPositional es
          | TacticParse.MapFirst (_, es) => lsHasGoalPositional es
          | TacticParse.List (_, es) => lsHasGoalPositional es
          | TacticParse.Try e => exprHasGoalPositional e
          | TacticParse.Repeat e => exprHasGoalPositional e
          | TacticParse.By (_, _, e) => exprHasGoalPositional e
          | TacticParse.SufficesBy (_, _, e) => exprHasGoalPositional e
          | TacticParse.LAllGoals e => exprHasGoalPositional e
          | TacticParse.LRepeat e => exprHasGoalPositional e
          | TacticParse.LTry e => exprHasGoalPositional e
          | TacticParse.LNullOk e => exprHasGoalPositional e
          | TacticParse.LFirstLT e => exprHasGoalPositional e
          | TacticParse.Group (_, _, e) => exprHasGoalPositional e
          | TacticParse.RepairGroup (_, _, e, _) => exprHasGoalPositional e
          | _ => false
    and lsHasGoalPositional ls = List.exists exprHasGoalPositional ls
    fun isComposable (TacticParse.Then _) = true
      | isComposable (TacticParse.ThenLT (_, ls)) =
          not (lsHasStructuralOnly ls) andalso
          (!reexpand_positional_groups orelse not (lsHasGoalPositional ls))
      | isComposable (TacticParse.LThen1 _) = true
      | isComposable (TacticParse.LThenLT ls) =
          not (lsHasStructuralOnly ls) andalso
          (!reexpand_positional_groups orelse not (lsHasGoalPositional ls))
      | isComposable (TacticParse.Group _) = true  (* peels outer wrapper; inner expr is checked by recursion *)
      | isComposable _ = false
    fun isGroupAtom (TacticParse.FAtom (TacticParse.Group (_, _, e))) =
          isComposable e
      | isGroupAtom _ = false
    fun getGroupExpr (TacticParse.FAtom (TacticParse.Group (_, _, e))) = e
      | getGroupExpr _ = raise Match
    fun getGroupSpan (TacticParse.FAtom (TacticParse.Group (_, span, _))) = SOME span
      | getGroupSpan _ = NONE
    fun spanString (s, e) = Int.toString s ^ ".." ^ Int.toString e
    fun warn_nested_goal_positional spanOpt =
      let val loc = case spanOpt of SOME sp => " at span " ^ spanString sp
                                  | NONE => ""
      in
        (* Emit a structured WARNING line on stdout. Hol_send captures
           stdout. The step-plan JSON parser only consumes lines starting
           with `{"ok":...}`; warning lines are visible to humans inspecting
           the raw output. *)
        print ("{\"warning\":\"reexpanded Group" ^ loc ^
               " contains nested >- / >| / etc. inside a sub-expression; " ^
               "if this Group runs in a per-goal context (e.g. inside a " ^
               "\\\\ chain), the inner LT operator may execute GLOBALLY " ^
               "rather than per-source-goal, diverging from Holmake — " ^
               "parenthesise the inner LT subexpression itself.\"}\n")
      end
    fun reexpand inArm f =
          let
            val expr = getGroupExpr f
            val _ = if exprHasGoalPositional expr
                    then warn_nested_goal_positional (getGroupSpan f)
                    else ()
            fun isAtom e = Option.isSome (TacticParse.topSpan e)
            val subFrags = TacticParse.linearize isAtom expr
          in reexpand_group_atoms_in inArm (flatten_frags subFrags) end
    fun opensArm (TacticParse.FFOpen (TacticParse.FOpenThen1 _)) = true
      | opensArm _ = false
    fun reexpandable inArm f =
          isGroupAtom f andalso
          (inArm orelse !reexpand_positional_groups orelse
           not (exprHasGoalPositional (getGroupExpr f)))
    fun go [] _ acc = rev acc
      | go (f :: rest) inArm acc =
          if reexpandable inArm f
          then go rest false (rev (reexpand inArm f) @ acc)
          else go rest (opensArm f) (f :: acc)
  in go frags arm [] end

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
            | mkSelectPrefix [p] =
                (if kind = "selects" then "Q.SELECT_GOALS_LT " else "Q.SELECT_GOAL_LT ") ^ p
            | mkSelectPrefix (p :: ps) = "Q.SELECT_GOAL_LT " ^ p ^ " >>~ Q.SELECT_GOALS_LT " ^
                String.concatWith " >>~ Q.SELECT_GOALS_LT " ps
          val selectPrefix = mkSelectPrefix sels
          (* Try to consume the following bracket: open (expand|nested)+ close.
             The body may be a single expand, a compound of expands joined by
             >>, or contain NESTED >- / parens. parseBody recursively
             reconstructs the body text, parenthesising nested >- groups so
             the precedence ((tac >- body) vs surrounding >>) is preserved.
             Bails on unsupported open kinds (>|, >~ inside, etc). *)
          fun isOpenArm "open_then1" = true
            | isOpenArm "open_first" = true
            | isOpenArm _ = false
          (* parseBody: walk steps until matching close at depth 0, returning
             (combined-text, close-end-offset, remaining-steps). On nested
             open_then1, the previous atom in acc is wrapped:
                 last  +  open_then1  +  innerBody  +  close
                  -> "(" ^ last ^ " >- (" ^ innerBody ^ "))"
             so subsequent >> joins don't accidentally bind to the THEN1. *)
          fun parseBody [] _ = NONE  (* unbalanced *)
            | parseBody ((closeEnd, "close", _) :: rest) acc =
                (case rev acc of
                   [] => NONE
                 | xs => SOME (String.concatWith " >> " xs, closeEnd, rest))
            | parseBody ((_, "open", "open_then1") :: rest) acc =
                (case parseBody rest [] of
                   NONE => NONE
                 | SOME (innerText, _, rest') =>
                     (case acc of
                        [] => NONE  (* >- with no preceding atom *)
                      | last :: restAcc =>
                          parseBody rest'
                            (("(" ^ last ^ " >- (" ^ innerText ^ "))") :: restAcc)))
            | parseBody ((_, "open", "open_paren") :: rest) acc =
                (case parseBody rest [] of
                   NONE => NONE
                 | SOME (innerText, _, rest') =>
                     parseBody rest' (("(" ^ innerText ^ ")") :: acc))
            | parseBody ((_, "open", _) :: _) _ = NONE  (* other opens: bail *)
            | parseBody ((_, "mid", _) :: _) _ = NONE   (* >| / next_select: bail *)
            | parseBody ((_, "expand", t) :: rest) acc =
                parseBody rest (t :: acc)
            | parseBody ((_, "expand_list", t) :: rest) acc =
                parseBody rest (("(" ^ t ^ ")") :: acc)
            | parseBody _ _ = NONE
          (* Wrap final body for the >- arm of the SELECT_GOAL_LT.
             Single-token body: no extra parens (matches old behaviour).
             Multi-token body: parenthesise so >- binds the whole chain. *)
          fun finishArm bodyText closeEnd rest' =
                let
                  (* Detect "single token" by absence of a top-level >> *)
                  val needsParens = String.isSubstring " >> " bodyText
                  val wrapped = if needsParens
                                then "(" ^ bodyText ^ ")"
                                else bodyText
                in
                  SOME (selectPrefix ^ " >- " ^ wrapped, closeEnd, rest')
                end
          fun tryConsumeBracket [] = NONE
            | tryConsumeBracket ((_, "open", openName) :: rest') =
                if isOpenArm openName then
                  (case parseBody rest' [] of
                     NONE => NONE
                   | SOME (bodyText, closeEnd, rest'') =>
                       finishArm bodyText closeEnd rest'')
                else NONE
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

(* merge_by_steps: Post-process step list to merge a Subgoal atom (`P`) and
   its following >- bracket back into a single atomic `P` by tac step.

   WHY: `P` by tac is parsed by HOL4 as a single tactic equivalent to
   `subgoal P >- tac`. When applied via THEN-distribution (\\ / >>) over a
   multi-goal stack, HOL4 runs this tactic atomically per goal: each goal
   independently gets P proven (by tac) and added as a hypothesis. Per goal:
   1 in, 1 out.

   The naive decomposition `expand (sg P), open_then1, expand tac, close_paren`
   does NOT match this semantics. `expand (sg P)` distributes per-goal
   (correctly producing 2N goals: [P_1, cont_1, ..., P_N, cont_N]), but
   `open_then1` is a goalstate-level fragment tactic that always focuses on
   the FIRST top-level goal. So only P_1 gets discharged; P_2..P_N remain
   open as subgoals. Subsequent tactics applied via THEN do not generally
   close those — they were meant to operate on the cont_i, not on the P_i.

   This is exactly the bug that occurs when proofs use the common idiom

       Cases_on `q` \\ ... \\ `tttt = ttt` by tac \\ fs[option_le_max]

   after a multi-goal split. In real HOL4 (Holmake), the proof passes; in
   the MCP's decomposed replay, N-1 sg-subgoals remain unproven and the
   theorem looks INCOMPLETE.

   Fix: detect the [Subgoal `P`, open_then1, expand+, close_paren] sequence
   and merge it into a single atomic step `P by tac` (or `P by (t1 >> t2)`
   for a compound body). The merged step is run via goalFrag.expand and
   distributes correctly per-goal — matching Holmake.

   Bails (no merge) on nested open/mid inside the body — those would need
   full source reconstruction to preserve. The unmerged case keeps the old
   behaviour, which is correct in single-goal contexts (top-level `P` by tac
   without an upstream multi-goal-producing tactic in the same THEN chain). *)
fun isSubgoalText t =
      String.isPrefix "sg " t andalso
      startsWithQuote (String.extract (t, 3, NONE))

fun stripSgPrefix t = String.substring (t, 3, String.size t - 3)

fun merge_by_steps [] acc = rev acc
  | merge_by_steps ((endP, "expand", subgoalText) :: rest) acc =
      if isSubgoalText subgoalText then
        let
          val patText = stripSgPrefix subgoalText
          (* Walk a single >- arm: expand+, close. Bail on nested opens. *)
          fun walkArm [] _ _ = NONE
            | walkArm ((closeEnd, "close", _) :: rest') texts _ =
                (case rev texts of
                   [] => NONE
                 | [single] => SOME (patText ^ " by " ^ single, closeEnd, rest')
                 | many => SOME (patText ^ " by (" ^
                                 String.concatWith " >> " many ^ ")",
                                 closeEnd, rest'))
            | walkArm ((endP', "expand", t) :: rest') texts _ =
                walkArm rest' (t :: texts) endP'
            | walkArm _ _ _ = NONE
          fun tryConsume ((_, "open", "open_then1") :: rest') =
                walkArm rest' [] 0
            | tryConsume _ = NONE
        in
          case tryConsume rest of
            SOME (combinedText, closeEnd, rest') =>
              merge_by_steps rest' ((closeEnd, "expand", combinedText) :: acc)
          | NONE =>
              merge_by_steps rest ((endP, "expand", subgoalText) :: acc)
        end
      else
        merge_by_steps rest ((endP, "expand", subgoalText) :: acc)
  | merge_by_steps ((endP, kind, q) :: rest) acc =
      if kind = "open_by" orelse kind = "open_suffices_by" then
        (* Newer TacticParse linearizes `q by tac` as [open_by q, body, close].
           Merge into one atomic step as above; if the body is not a flat
           arm, open it natively with open_then1_with, as HOL's LSP does. *)
        let
          val (conn, byA) = if kind = "open_by"
                            then (" by ", "BasicProvers.byA")
                            else (" suffices_by ", "BasicProvers.suffices_byA")
          fun walkArm [] _ = NONE
            | walkArm ((closeEnd, "close", _) :: rest') texts =
                (case rev texts of
                   [] => NONE
                 | [single] => SOME (q ^ conn ^ single, closeEnd, rest')
                 | many => SOME (q ^ conn ^ "(" ^
                                 String.concatWith " >> " many ^ ")",
                                 closeEnd, rest'))
            | walkArm ((_, "expand", t) :: rest') texts =
                walkArm rest' (t :: texts)
            | walkArm _ _ = NONE
          (* `tac1 by tac2` with a tactic on the left means tac1 >- tac2 *)
          val isQuote = startsWithQuote q
        in
          if not isQuote then
            merge_by_steps rest ((endP, "open", "open_then1") ::
                                 (endP, "expand", q) :: acc)
          else if kind = "open_suffices_by" then
            (* step through it, realizing the operand as frag_text does for
               the older ThenLT (Subgoal, [LReverse]) form *)
            merge_by_steps rest ((endP, "open", "open_then1") ::
                                 (endP, "expand", "Q_TAC SUFF_TAC " ^ q) :: acc)
          else
          case walkArm rest [] of
            SOME (combinedText, closeEnd, rest') =>
              merge_by_steps rest' ((closeEnd, "expand", combinedText) :: acc)
          | NONE =>
              merge_by_steps rest
                ((endP, "open", "open_then1_with (" ^ byA ^ " (" ^ q ^
                                ", Tactical.ALL_TAC)) (Context.snapshot())") :: acc)
        end
      else
        merge_by_steps rest ((endP, kind, q) :: acc)

(* goalfrag_step_plan: Generate fragment steps from linearize fragments.
   Returns (end_offset, type, text) triples for every navigable position.
   Every fragment boundary is a step boundary -- no heuristics needed.
   LSelectGoal/LSelectGroups fragments are merged with their following
   bracket into a single expand_list step (SELECT_GOAL_LT requires
   goalFrag.expand_list, not goalFrag.expand).
   Subgoal atoms (`P`) are merged with their following >- arm into a single
   atomic `P` by tac step (preserves HOL4's per-goal distribution semantics
   when the by-pattern is in a THEN-distributed chain after a multi-goal-
   producing tactic — see merge_by_steps). *)
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
              | TacticParse.FFOpen (TacticParse.FOpenBy ((_, e), _)) => (e, e)
              | TacticParse.FFOpen (TacticParse.FOpenSufficesBy ((_, e), _)) => (e, e)
              | _ => (lastAtomEnd, lastAtomEnd)
          in
            if String.size x > 0
            then assignEnds rest newLast ((endPos, t, x) :: acc)
            else assignEnds rest lastAtomEnd acc
          end
    val rawSteps = assignEnds reexpanded 0 []
    val afterSelect = merge_select_steps rawSteps []
  in
    merge_by_steps afterSelect []
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

(* Same plan with parenthesised goal-positional groups re-expanded (see
   reexpand_positional_groups). *)
fun goalfrag_step_plan_json_flat proofBody =
  (reexpand_positional_groups := true;
   goalfrag_step_plan_json proofBody;
   reexpand_positional_groups := false)
  handle e => (reexpand_positional_groups := false;
               print (json_err (exnMessage e) ^ "\n"));

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

(* The theorem the last successful verify_core proved, kept whether or not it
   was stored, so the cursor can bind it with the file's own header. *)
val hol4mcp_checked_thm : thm option ref = ref NONE;

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

    (* Read oracle tags from the proved theorem directly (top_thm()) BEFORE
       drop_all discards it, so cheat-dependency detection works whether or not
       we store. Previously oracles were read via DB.fetch only when stored, so
       store=false checks (single hol_check_proof) never reported a dependency
       on an auto-cheated lemma. *)
    val oracles =
      if proof_ok then
        Lib.set_diff (fst (Tag.dest_tag (Thm.tag (top_thm())))) ["DISK_THM"]
        handle _ => []
      else []

    val _ = hol4mcp_checked_thm :=
              (if proof_ok then (SOME (top_thm ()) handle _ => NONE) else NONE)
    val stored = proof_ok andalso store
    val _ = if stored
            then (smlExecute.quse_string ("val " ^ name ^ " = save_thm(\"" ^ name ^ "\", top_thm());"); ())
            else (drop_all (); ())

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

(* The body arrives as the quotation HOL's own filter would compile, so its
   ANTIQUOTE frags name SML values of the session. Each extracted termination
   goal is kept as a term, by the Definition's name, and the goal is set from
   it. The printed form goes back too, as the fallback: with every variable
   and numeral typed, an unannotated `-` or `<` cannot resolve to another
   overload when it is reparsed (int, once integerTheory is open). *)
val mcp_tc_goals : (string * term) list ref = ref [];

fun extract_tc_goal_json_named name (q : term frag list) =
  let
    val result = ref ""
    fun inner () =
      let
        val d = Defn.Hol_defn "mcp_tc_extract" q
        val _ = Defn.tgoal d
        val (_, t) = hd (top_goals())
        val _ = mcp_tc_goals :=
                  (name, t) :: List.filter (fn (n, _) => n <> name) (!mcp_tc_goals)
        (* The printed form is the fallback when the term outlives a
           constant the rollback below retires: no elision, every type. *)
        val _ = result :=
                  Lib.with_flag (Globals.max_print_depth, ~1)
                    (Lib.with_flag (Globals.show_types, true) term_to_string) t
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

fun extract_tc_goal_json_q q = extract_tc_goal_json_named "" q;

fun extract_tc_goal_json body_str = extract_tc_goal_json_q [QUOTE body_str];

(* Set the goal from the term extract_tc_goal_json_named kept for `name`.
   Refused when that term mentions a constant the extraction's rollback
   retired (nested recursion through an auxiliary): the caller then parses
   the printed form in the current context instead. *)
fun set_tc_goalfrag_json name =
  (case List.find (fn (n, _) => n = name) (!mcp_tc_goals) of
     NONE => print (json_err ("no termination goal extracted for " ^ name) ^ "\n")
   | SOME (_, t) =>
       if Term.uptodate_term t then
         (drop_all ();
          proofManagerLib.set_goalfrag ([], t);
          print (json_ok "true" ^ "\n"))
       else print (json_err "termination goal mentions a retired constant" ^ "\n"))
  handle e => print (json_err (exnMessage e) ^ "\n");

(* =============================================================================
 * Resume Goal Extraction
 * ============================================================================= *)

fun resume_goal_terms suspension_name label_name =
  let
    val (parent_thy, th) =
        case markerLib.lookup_suspension suspension_name of
            SOME pair => pair
          | NONE => raise Fail ("No suspension found: " ^ suspension_name)
    val sths = markerLib.lookup_resumption
                 {parent_thy = parent_thy,
                  parent_name = suspension_name,
                  label = label_name}
  in
    markerLib.resumption_to_goal
      (markerLib.extract_suspended_goal (th::sths) label_name)
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

(* Verify a Resume block. Uses GOALFRAG (set_goalfrag) for ef() compatibility
   with the step-plan / navigation machinery.

   IMPORTANT: this path does NOT record resumption deltas for any sub-suspends
   issued inside the Resume body — only markerLib.resume records them.  Use
   verify_resume_json for one-shot verification (hol_check_proof, where
   per-tactic timing matters); use run_resume_canonical_json below for file
   replay (where sub-suspensions must register for downstream Resume blocks
   to look them up — symptom: "No such label" when navigating into a deeper
   Resume body). *)
fun verify_resume_json suspension_name label_name name tactics store timeout_sec =
  let
    val _ = drop_all ()
    val (asms, concl) = resume_goal_terms suspension_name label_name
    val _ = proofManagerLib.set_goalfrag (asms, concl)
  in
    verify_core name tactics store timeout_sec
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* Set up a Resume goal on the proof manager directly from the suspension
   store. Used by hol_state_at navigation: avoids a term->string->term
   round-trip via term_to_string + Parse.Term, which can rename bound
   variables under a clashing parse context. The terms here come straight
   from markerLib.lookup_suspension / extract_suspended_goal — identical
   to what Holmake's Resume processing uses.  Uses set_goalfrag for ef()
   compatibility with the rest of the navigation machinery. *)
fun set_resume_goalfrag_json suspension_name label_name =
  let
    val _ = drop_all ()
    val (asms, concl) = resume_goal_terms suspension_name label_name
    val _ = proofManagerLib.set_goalfrag (asms, concl)
  in
    print (json_ok "true" ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* Run a Resume block canonically via markerLib.resume.  This is the same
   code path Holmake executes when it processes `Resume thm[label]: tacs QED`
   in a script file: it runs the combined tactic via prove_goal (NOT the
   proof manager) and records resumption deltas for EACH suspendlabel
   hypothesis remaining in the proven theorem — including sub-suspends
   issued inside the Resume body's tactics.

   This is the only path that preserves the sub-suspension lifecycle.  Use
   it for file replay where downstream Resume blocks may need to look up
   sub-suspensions produced by this body.  Per-tactic timing trace is NOT
   available — the tactics combine into a single call.

   tactics: list of SML tactic strings, combined left-associatively with
   THEN.  An empty list runs the identity tactic (ALL_TAC) — closes nothing,
   so used only when the Resume body is itself empty. *)
(* Captures oracle tags of the most recently run Resume theorem (set inside
   the quse_string'd command, read back after), so cheat-dependency detection
   works for store=false single checks too. *)
val hol4mcp_resume_oracles = ref ([]: string list)

fun run_resume_canonical_json suspension_name label_name name tactics store timeout_sec =
  let
    val _ = drop_all ()
    val combined =
        case tactics of
            [] => "ALL_TAC"
          | _ => "(" ^ String.concatWith ") \\\\ (" tactics ^ ")"
    val save_decl =
        if store then
          "val _ = save_thm(\"" ^ String.toString name ^ "\", hol4mcp_resume_thm) "
        else ""
    val () = hol4mcp_resume_oracles := []
    val cmd =
        "let val hol4mcp_tac = (" ^ combined ^ ") " ^
        "    val hol4mcp_resume_thm = markerLib.resume " ^
        "{suspension_name = \"" ^ String.toString suspension_name ^
        "\", label_name = \"" ^ String.toString label_name ^ "\"} hol4mcp_tac (Context.snapshot()) " ^
        save_decl ^
        "    val () = hol4mcp_resume_oracles := ((Lib.set_diff (fst (Tag.dest_tag (Thm.tag hol4mcp_resume_thm))) [\"DISK_THM\"]) handle _ => []) " ^
        "in () end"
    val start = Timer.startRealTimer ()
    val ok = smlTimeout.timeout timeout_sec
               (fn () => smlExecute.quse_string cmd) ()
    val real_ms = Time.toMilliseconds (Timer.checkRealTimer start)
    (* Read oracle tags captured inside the command (works whether or not we
       store; DB.fetch only works post-save). *)
    val oracles = if ok then !hol4mcp_resume_oracles else []
    val oracles_json = "[" ^ String.concatWith "," (map json_string oracles) ^ "]"
    val trace_json =
      "[{\"real_ms\":" ^ LargeInt.toString real_ms ^
      ",\"goals_before\":0,\"goals_after\":" ^ (if ok then "0" else "1") ^
      (if ok then "" else ",\"err\":\"markerLib.resume failed\"") ^ "}]"
  in
    print (json_ok (
      "{\"stored\":" ^ (if ok andalso store then "true" else "false") ^
      ",\"name\":" ^ json_string name ^
      ",\"oracles\":" ^ oracles_json ^
      ",\"trace\":" ^ trace_json ^ "}") ^ "\n")
  end
  handle e => print (json_err (exnMessage e) ^ "\n");

(* ----------------------------------------------------------------------
   e-mode safety.

   hol_state_at navigates with a GOALFRAG (needed for ef()/open/close
   fine-grained stepping). But on a GOALFRAG, proofManagerLib.e/expand apply a
   tactic to ALL goals in the current Base (THEN / `>>` semantics), whereas on
   a GOALSTACK they apply to the FIRST goal only (classic HOL `e`). So manually
   driving a navigated proof with `e` silently misfires per-goal (`>-`/THEN1)
   tactics across sibling goals (typically Lib.assert: predicate not true).

   Fix: a `safe_e` driver that, on a GOALFRAG, applies the tactic to the FIRST
   goal only (via enth/NTH_GOAL goal 1) — matching classic first-goal `e`. NO
   goalstate conversion: the proof stays a GOALFRAG and all other goals stay
   exactly in place. On a GOALSTACK (or no live proof) behaviour is the stock
   proofManagerLib.e.

   We install safe_e two ways so BOTH common driving forms are covered:
     (1) shadow the structure `proofManagerLib` (re-export everything, override
         only e/expand) so QUALIFIED `proofManagerLib.e`/`.expand` are safe;
     (2) shadow the top-level `e`/`expand`.
   The navigation machinery uses proofManagerLib.expand_frag / ef / expand_list
   (all re-exported unchanged), never .e/.expand, so it is untouched.
   Low-level escape hatches (Manager.expand, goalFrag.expand, eall/eta) are NOT
   guarded — they are explicit/low-level, not the silent footgun. *)
local
  val orig_e    = proofManagerLib.e
  val orig_enth = proofManagerLib.enth
  val orig_p    = proofManagerLib.p
in
  fun safe_e tac =
    let
      val on_frag =
        (case orig_p () of Manager.PF (Manager.GOALFRAG _, _) => true | _ => false)
        handle _ => false
    in
      if on_frag then orig_enth tac 1 else orig_e tac
    end
end

structure proofManagerLib =
struct
  open proofManagerLib
  val e = safe_e
  val expand = safe_e
end

val e = safe_e
val expand = safe_e

(* =============================================================================
 * In-memory rewind points (the cursor's context checkpoints)
 *
 * A point is the Context and the loaded-module set before a stretch of file
 * content runs. Context.restore rewinds the kernel signatures, theorem DB,
 * simpsets, grammars and proof manager, but not the SML namespace: so before
 * each chunk the cursor records the bindings the chunk's names have
 * (mcp_capture), and a rewind puts them back. A module loaded since a point
 * cannot be taken back (loading seals a theory), so such a rewind is refused
 * and the caller falls back to a SaveState checkpoint.
 * ============================================================================= *)

val mcp_points : (int * Context.t * (unit -> unit) * int) list ref = ref [];
val mcp_captures :
      (int * (string * PolyML.NameSpace.Values.value option) list) list ref = ref [];

(* Take point `id`, keeping only the newest `keep` points and the captures
   a rewind to one of them needs. Prints the oldest point kept. *)
fun mcp_point id keep =
  let
    val all = (id, Context.snapshot (), Meta.snapshotLoaded (),
               length (Meta.loaded ())) :: !mcp_points
    val kept = List.take (all, Int.min (length all, Int.max (keep, 1)))
    val oldest = #1 (List.last kept)
  in
    mcp_points := kept;
    mcp_captures := List.filter (fn (i, _) => i >= oldest) (!mcp_captures);
    print (json_ok (Int.toString oldest) ^ "\n")
  end;

(* `id`: the newest point before the chunk about to run. *)
fun mcp_capture id names =
  mcp_captures :=
    (id, map (fn n => (n, #lookupVal PolyML.globalNameSpace n)) names) :: !mcp_captures;

(* Rewind to point `id`. Prints the names a chunk after the point bound that
   had no binding before it, for the caller to shadow; or an error, having
   changed nothing. *)
fun mcp_rewind_json id =
  (case List.find (fn (i, _, _, _) => i = id) (!mcp_points) of
     NONE => print (json_err ("no rewind point " ^ Int.toString id) ^ "\n")
   | SOME (_, ctx, restore_loaded, nloaded) =>
       if length (Meta.loaded ()) > nloaded then
         print (json_err "a module was loaded since the rewind point" ^ "\n")
       else
         let
           val (undo, keep) = List.partition (fn (i, _) => i >= id) (!mcp_captures)
           (* oldest capture first: a name's value before its earliest rebinding *)
           fun before ([], seen) = seen
             | before ((_, names) :: rest, seen) =
                 before (rest, List.foldl (fn ((n, v), acc) =>
                   if List.exists (fn (m, _) => m = n) acc then acc else (n, v) :: acc)
                   seen names)
           val values = before (rev undo, [])
           val unbound = List.mapPartial (fn (n, NONE) => SOME n | _ => NONE) values
         in
           (* The restores can fail; the namespace changes only after them. *)
           Context.restore ctx;
           restore_loaded ();
           List.app (fn (n, SOME v) => #enterVal PolyML.globalNameSpace (n, v)
                      | _ => ()) values;
           mcp_points := List.filter (fn (i, _, _, _) => i <= id) (!mcp_points);
           mcp_captures := keep;
           print (json_ok (json_string_array unbound) ^ "\n")
         end)
  handle e => print (json_err (exnMessage e) ^ "\n");
