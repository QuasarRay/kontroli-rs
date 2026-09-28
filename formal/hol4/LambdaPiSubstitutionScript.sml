Theory LambdaPiSubstitution
Ancestors
  LambdaPiTyping LambdaPiBinderAlgebra
Libs
  boolSimps

(* Eliminate one binder that sits before a suffix H.  The i-th stored type in
   H was written with i preceding suffix binders in scope, so the eliminated
   variable occurs at cutoff i. *)
Definition subst_ctx_from_def:
  (subst_ctx_from u k [] = []) /\
  (subst_ctx_from u k (A::H) =
    subst u k A :: subst_ctx_from u (SUC k) H)
End

Definition subst_ctx_def:
  subst_ctx u H = subst_ctx_from u 0 H
End

Theorem subst_ctx_from_length[simp]:
  !u k H. LENGTH (subst_ctx_from u k H) = LENGTH H
Proof
  rpt gen_tac >> Induct_on `H` >> simp[subst_ctx_from_def]
QED

Theorem subst_ctx_length[simp]:
  !u H. LENGTH (subst_ctx u H) = LENGTH H
Proof
  simp[subst_ctx_def]
QED

Theorem subst_ctx_from_snoc:
  !H u k A.
    subst_ctx_from u k (H ++ [A]) =
    subst_ctx_from u k H ++ [subst u (k + LENGTH H) A]
Proof
  Induct >>
  simp[subst_ctx_from_def, ADD_CLAUSES, ADD_ASSOC]
QED

Theorem subst_ctx_snoc:
  !H u A.
    subst_ctx u (H ++ [A]) =
    subst_ctx u H ++ [subst u (LENGTH H) A]
Proof
  simp[subst_ctx_def, subst_ctx_from_snoc]
QED

(* Context shape used by the generalized substitution theorem. *)
Definition subst_context_def:
  subst_context G u H = G ++ subst_ctx u H
End

Theorem subst_context_empty[simp]:
  !G u. subst_context G u [] = G
Proof
  simp[subst_context_def, subst_ctx_def, subst_ctx_from_def]
QED

Theorem subst_context_snoc:
  !G u H A.
    subst_context G u (H ++ [A]) =
    subst_context G u H ++ [subst u (LENGTH H) A]
Proof
  simp[subst_context_def, subst_ctx_snoc]
QED

val _ = export_theory();
