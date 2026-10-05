Theory KontroliProofAutomation
Ancestors
  LambdaPiBinderAlgebra LambdaPiTyping LambdaPiReduction LambdaPiSyntax KontroliBase arithmetic string relation list rich_list
Libs
  Hol4ProofSearchLib HolSmtLib tacticToe

(* Egglog supplies only names of existing HOL4 rewrite facts. *)
val hints = Hol4ProofSearchLib.read_rewrite_names "egglog-rewrites.txt";
val _ = if hints = ["LambdaPiSyntax.lift_zero", "LambdaPiBinderAlgebra.subst0_lift1"] then ()
        else raise Fail "unexpected Egglog rewrite registry";
val egg_goal = ``!t u a c.
  subst0 u (lift 1 0 (subst0 a (lift 1 0 (lift 0 c t)))) = t``;
val (egg_engine, egg_thm) = Hol4ProofSearchLib.prove_with_search
  {name = "egglog_lift_subst", goal = egg_goal, egglog_rewrites = hints};
val _ = if egg_engine = "egglog-replay" then ()
        else raise Fail "binder candidate did not replay its named HOL4 rewrites";
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
val commute_bounds_goal = ``!n base amount c:num.
  base + amount <= c /\ n = c - amount ==>
  n + amount = c /\ base <= c - amount``;
val commute_bounds_thm = prove (commute_bounds_goal, HolSmtLib.Z3_TAC);
val _ = Hol4ProofSearchLib.inspect_exact "substitution_lift_bounds_z3"
  commute_bounds_goal commute_bounds_thm;
val _ = save_thm ("substitution_lift_bounds_z3", commute_bounds_thm);

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

(* Inspect the repaired metatheory facts, including every closure premise. *)
val binder_goals = [
  ("lift_compose", ``!t d1 d2 c.
    lift d1 c (lift d2 c t) = lift (d2 + d1) c t``),
  ("subst_lift_commute", ``!t u base amount c.
    base + amount <= c ==>
    subst u c (lift amount base t) = lift amount base (subst u (c - amount) t)``),
  ("subst_subst_ge", ``!t a u k c. k <= c ==>
    subst u c (subst a k t) =
    subst (subst u (c - k) a) k (subst u (c + 1) t)``),
  ("red_subst_from_rewrite_closed", ``!R t v.
    rewrite_substitution_closed R /\ red R t v ==>
    !u c. red R (subst u c t) (subst u c v)``),
  ("convertible_subst_from_rewrite_closed", ``!R t v u c.
    rewrite_substitution_closed R /\ convertible R t v ==>
    convertible R (subst u c t) (subst u c v)``)
];
val _ = List.app (fn (name, goal) => Hol4ProofSearchLib.inspect_exact
  ("LambdaPiBinderAlgebra." ^ name) goal (DB.fetch "LambdaPiBinderAlgebra" name))
  binder_goals;

val _ = export_theory();
val out = TextIO.openOut "automation-inspection.json";
val _ = TextIO.output (out,
  "{\"schema\":1,\"theory\":\"KontroliProofAutomation\",\"theorems\":[\"egglog_lift_subst\",\"lift_index_bound_z3\",\"substitution_index_cancel_z3\",\"substitution_lift_bounds_z3\",\"application_conversion_tactictoe\"],\"metatheory_theorems\":[\"lift_compose\",\"subst_lift_commute\",\"subst_subst_ge\",\"red_subst_from_rewrite_closed\",\"convertible_subst_from_rewrite_closed\"],\"exact_goals_checked\":true,\"hypotheses\":0,\"non_disk_oracles\":0,\"local_axioms\":0,\"claim\":\"scoped proof automation and binder algebra; whole-kernel and binary refinement remain open\"}\n");
val _ = TextIO.closeOut out;
