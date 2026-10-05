Theory KontroliProofAutomation
Ancestors
  LambdaPiTyping LambdaPiReduction LambdaPiSyntax KontroliBase arithmetic string relation list
Libs
  Hol4ProofSearchLib HolSmtLib tacticToe

(* Egglog supplies only names of existing HOL4 rewrite facts. *)
val hints = Hol4ProofSearchLib.read_rewrite_names "egglog-rewrites.txt";
val _ = if hints = ["LambdaPiSyntax.lift_zero"] then ()
        else raise Fail "unexpected Egglog rewrite registry";
val egg_goal = ``!t u c k.
  lift 0 c (subst u k (lift 0 k t)) = subst u k t``;
val egg_thm = prove (egg_goal,
  simp (List.map (fn _ => LambdaPiSyntaxTheory.lift_zero) hints));
val _ = Hol4ProofSearchLib.inspect_exact "egglog_lift_subst" egg_goal egg_thm;
val _ = save_thm ("egglog_lift_subst", egg_thm);

(* Linear arithmetic obligations needed by the de Bruijn variable cases. *)
val bounds_goal = ``!n c d:num. c <= n ==> c <= n + d``;
val bounds_thm = prove (bounds_goal, HolSmtLib.Z3_TAC);
val _ = Hol4ProofSearchLib.inspect_exact "lift_index_bound_z3" bounds_goal bounds_thm;
val _ = save_thm ("lift_index_bound_z3", bounds_thm);
val cancel_goal = ``!n c:num. ~(n < c) ==> n + 1 <> c /\ n + 1 - 1 = n``;
val cancel_thm = prove (cancel_goal, HolSmtLib.Z3_TAC);
val _ = Hol4ProofSearchLib.inspect_exact "substitution_index_cancel_z3" cancel_goal cancel_thm;
val _ = save_thm ("substitution_index_cancel_z3", cancel_thm);

(* TacticToe performs learned tactic search over already kernel-checked facts. *)
val ttt_goal = ``!R f g a. red R f g ==>
  convertible R (TmApp f a) (TmApp g a)``;
val _ = tacticToe.set_timeout 10.0;
val ttt_thm = Lib.with_flag
  (tacticToe.prioritize_stacl,
   "bossLib.metis_tac [LambdaPiReductionTheory.red_app_fun, LambdaPiReductionTheory.red_implies_convertible]"
     :: !tacticToe.prioritize_stacl)
  (fn () => prove (ttt_goal, tacticToe.ttt)) ();
val _ = Hol4ProofSearchLib.inspect_exact "application_conversion_tactictoe" ttt_goal ttt_thm;
val _ = save_thm ("application_conversion_tactictoe", ttt_thm);

val _ = export_theory();
val out = TextIO.openOut "automation-inspection.json";
val _ = TextIO.output (out,
  "{\"schema\":1,\"theory\":\"KontroliProofAutomation\",\"theorems\":[\"egglog_lift_subst\",\"lift_index_bound_z3\",\"substitution_index_cancel_z3\",\"application_conversion_tactictoe\"],\"exact_goals_checked\":true,\"hypotheses\":0,\"non_disk_oracles\":0,\"local_axioms\":0,\"claim\":\"scoped proof automation; whole-kernel and binary refinement remain open\"}\n");
val _ = TextIO.closeOut out;
