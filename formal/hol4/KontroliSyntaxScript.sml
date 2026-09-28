open HolKernel boolLib bossLib;
open arithmeticTheory KontroliBaseTheory;

val _ = new_theory "KontroliSyntax";

(* Declarative syntax for the supported λΠ-calculus-modulo kernel fragment.
   Constants are abstracted as natural-number identifiers; correspondence to
   Kontroli's interned Symbol representation is proved in a later layer. *)
Datatype:
  term =
      TmKind
    | TmType
    | TmConst num
    | TmVar num
    | TmApp term term
    | TmLam term term
    | TmPi term term
End

Definition lift_def:
  (lift d c TmKind = TmKind) /\
  (lift d c TmType = TmType) /\
  (lift d c (TmConst s) = TmConst s) /\
  (lift d c (TmVar k) =
     if k < c then TmVar k else TmVar (k + d)) /\
  (lift d c (TmApp f x) = TmApp (lift d c f) (lift d c x)) /\
  (lift d c (TmLam a b) =
     TmLam (lift d c a) (lift d (c + 1) b)) /\
  (lift d c (TmPi a b) =
     TmPi (lift d c a) (lift d (c + 1) b))
End

Definition subst_def:
  (subst c u TmKind = TmKind) /\
  (subst c u TmType = TmType) /\
  (subst c u (TmConst s) = TmConst s) /\
  (subst c u (TmVar k) =
     if k < c then TmVar k
     else if k = c then u
     else TmVar (k - 1)) /\
  (subst c u (TmApp f x) = TmApp (subst c u f) (subst c u x)) /\
  (subst c u (TmLam a b) =
     TmLam (subst c u a) (subst (c + 1) (lift 1 0 u) b)) /\
  (subst c u (TmPi a b) =
     TmPi (subst c u a) (subst (c + 1) (lift 1 0 u) b))
End

Definition closed_at_def:
  (closed_at n TmKind <=> T) /\
  (closed_at n TmType <=> T) /\
  (closed_at n (TmConst s) <=> T) /\
  (closed_at n (TmVar k) <=> k < n) /\
  (closed_at n (TmApp f x) <=>
     closed_at n f /\ closed_at n x) /\
  (closed_at n (TmLam a b) <=>
     closed_at n a /\ closed_at (n + 1) b) /\
  (closed_at n (TmPi a b) <=>
     closed_at n a /\ closed_at (n + 1) b)
End

Definition closed_def:
  closed t <=> closed_at 0 t
End

Theorem lift_zero[simp]:
  !c t. lift 0 c t = t
Proof
  Induct_on `t` >> simp [lift_def]
QED

Theorem lift_closed_at:
  !t n d. closed_at n t ==> lift d n t = t
Proof
  Induct_on `t` >> simp [closed_at_def, lift_def]
QED

Theorem closed_has_no_free_var:
  !k. ~closed (TmVar k)
Proof
  simp [closed_def, closed_at_def]
QED

Theorem subst_closed_at_below:
  !t n u. closed_at n t ==> subst n u t = t
Proof
  Induct_on `t` >> simp [closed_at_def, subst_def, lift_closed_at]
QED

val _ = export_theory();
