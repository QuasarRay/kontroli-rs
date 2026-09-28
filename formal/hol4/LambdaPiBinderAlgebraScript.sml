Theory LambdaPiBinderAlgebra
Ancestors
  LambdaPiTyping rich_list
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

val _ = export_theory();
