Theory LambdaPiBinderAlgebra
Ancestors
  LambdaPiTyping LambdaPiReduction LambdaPiSyntax KontroliBase arithmetic string relation list rich_list
Libs
  boolSimps numLib

(* Two lifts at the same cutoff compose additively.  This is the standard
   de Bruijn algebra used by Kontroli's shift implementation. *)
Theorem lift_compose:
  !t d1 d2 c.
    lift d1 c (lift d2 c t) = lift (d2 + d1) c t
Proof
  Induct >> simp[ADD_ASSOC]
  >- (rpt gen_tac >> Cases_on `n < c` >> simp[] >> numLib.ARITH_TAC)
QED

(* Nipkow-style cancellation: inserting a fresh slot and substituting at the
   same cutoff restores the original term. *)
Theorem subst_lift_cancel:
  !t u c.
    subst u c (lift 1 c t) = t
Proof
  Induct >> simp[]
  >- (rpt gen_tac >> Cases_on `n < c` >> simp[] >> numLib.ARITH_TAC)
QED

Theorem subst0_lift1[simp]:
  !t u.
    subst0 u (lift 1 0 t) = t
Proof
  simp[subst0_def, subst_lift_cancel]
QED

(* Reverse-index local-context facts matching LCtx::get_type. *)
Theorem ctx_type_extend_zero:
  !G A.
    ctx_type (G ++ [A]) 0 (lift 1 0 A)
Proof
  simp[ctx_type_def, rich_listTheory.EL_LENGTH_APPEND_0]
QED

Theorem ctx_type_empty:
  !n A. ~ctx_type [] n A
Proof
  simp[ctx_type_def]
QED

Theorem ctx_type_in_bounds:
  !G n A. ctx_type G n A ==> n < LENGTH G
Proof
  simp[ctx_type_def]
QED

Theorem ctx_type_functional:
  !G n A B.
    ctx_type G n A /\ ctx_type G n B ==> A = B
Proof
  simp[ctx_type_def]
QED

(* A concrete lambda-Pi-modulo rewrite relation is closed under capture-
   avoiding substitution because rules are applied by instantiation.  Keep
   this obligation explicit until the Kontroli rule-instantiation relation is
   connected to the executable matcher. *)
Definition rewrite_substitution_closed_def:
  rewrite_substitution_closed R <=>
    !t v u c.
      R t v ==> R (subst u c t) (subst u c v)
End

(* This stronger closure property includes beta and compatible reduction.  It
   is exactly what the typing substitution proof needs in its conversion case. *)
Definition red_substitution_closed_def:
  red_substitution_closed R <=>
    !t v u c.
      red R t v ==> red R (subst u c t) (subst u c v)
End

(* General lift fusion.  The second insertion starts inside the prefix
   inserted by the first lift. *)
Theorem lift_fusion:
  !t base gap extra prefix.
    gap <= prefix ==>
    lift extra (base + gap) (lift prefix base t) =
    lift (prefix + extra) base t
Proof
  Induct >> simp[ADD_ASSOC, ADD_COMM, ADD_LEFT_COMM]
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `n < base` >> simp[] >> numLib.ARITH_TAC)
QED

Theorem lift_prefix_fusion:
  !t extra base prefix.
    base <= prefix ==>
    lift extra base (lift prefix 0 t) =
    lift (prefix + extra) 0 t
Proof
  metis_tac[lift_fusion, ADD_CLAUSES]
QED

(* Moving an outer substitution through a prefix lift. *)
Theorem subst_lift_commute:
  !t u base amount c.
    base + amount <= c ==>
    subst u c (lift amount base t) =
    lift amount base (subst u (c - amount) t)
Proof
  Induct >> simp[ADD_ASSOC, ADD_COMM, ADD_LEFT_COMM]
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `n < base` >> simp[] >- numLib.ARITH_TAC >>
      Cases_on `n < c - amount` >> simp[] >- numLib.ARITH_TAC >>
      Cases_on `n = c - amount` >> simp[] >-
        (`base <= c - amount` by numLib.ARITH_TAC >>
         simp[lift_prefix_fusion] >> numLib.ARITH_TAC) >>
      simp[] >> numLib.ARITH_TAC)
QED

(* Substituting below a fully lifted prefix simply removes one of the
   inserted slots.  This is the exceptional variable case of substitution
   composition. *)
Theorem subst_lift_prefix_drop:
  !t a k c.
    k <= c ==>
    subst a k (lift (c + 1) 0 t) = lift c 0 t
Proof
  rpt gen_tac >> strip_tac >>
  `lift (c + 1) 0 t = lift 1 k (lift c 0 t)` by
    metis_tac[lift_prefix_fusion, ADD_COMM] >>
  simp[subst_lift_cancel]
QED

(* Composition law needed to push an outer substitution through beta
   substitution.  The eliminated variable k precedes the variable c being
   substituted by u. *)
Theorem subst_subst_ge:
  !t a u k c.
    k <= c ==>
    subst u c (subst a k t) =
    subst (subst u (c - k) a) k (subst u (c + 1) t)
Proof
  Induct >> simp[ADD_ASSOC, ADD_COMM, ADD_LEFT_COMM]
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `n < k` >> simp[] >- numLib.ARITH_TAC >>
      Cases_on `n = k` >> simp[subst_lift_commute] >- numLib.ARITH_TAC >>
      Cases_on `n < c + 1` >> simp[] >- numLib.ARITH_TAC >>
      Cases_on `n = c + 1` >> simp[subst_lift_prefix_drop] >>
      numLib.ARITH_TAC)
QED

Theorem subst_subst0:
  !t a u c.
    subst u c (subst0 a t) =
    subst0 (subst u c a) (subst u (c + 1) t)
Proof
  simp[subst0_def, subst_subst_ge]
QED

(* User-rule closure is sufficient for the compatible beta+rewrite relation:
   beta is handled by subst_subst0 and every constructor case follows from
   the inductive hypotheses. *)
Theorem red_subst_from_rewrite_closed:
  !R t v.
    rewrite_substitution_closed R /\ red R t v ==>
    !u c. red R (subst u c t) (subst u c v)
Proof
  ho_match_mp_tac red_ind >>
  rw[rewrite_substitution_closed_def] >>
  simp[subst_subst0] >>
  metis_tac[red_rules]
QED

Theorem rewrite_substitution_closed_implies_red:
  !R. rewrite_substitution_closed R ==> red_substitution_closed R
Proof
  simp[red_substitution_closed_def] >>
  metis_tac[red_subst_from_rewrite_closed]
QED

Theorem convertible_subst_closed:
  !R.
    red_substitution_closed R ==>
    !t v. convertible R t v ==>
      !u c. convertible R (subst u c t) (subst u c v)
Proof
  rw[red_substitution_closed_def, convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS]
QED

Theorem convertible_subst_from_rewrite_closed:
  !R t v u c.
    rewrite_substitution_closed R /\ convertible R t v ==>
    convertible R (subst u c t) (subst u c v)
Proof
  metis_tac[rewrite_substitution_closed_implies_red, convertible_subst_closed]
QED

val _ = export_theory();
