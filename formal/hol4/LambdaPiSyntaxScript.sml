Theory LambdaPiSyntax
Ancestors
  KontroliBase arithmetic string
Libs
  boolSimps

Datatype:
  term =
    TmKind
  | TmType
  | TmConst string
  | TmVar num
  | TmApp term term
  | TmLam term term
  | TmLamU term
  | TmPi term term
End

(* De Bruijn lifting. This matches the index discipline used by
   kontroli/src/kernel/subst.rs: domains are outside the binder and bodies
   increment the cutoff. *)
Definition lift_def[simp]:
  (lift d c TmKind = TmKind) /\
  (lift d c TmType = TmType) /\
  (lift d c (TmConst s) = TmConst s) /\
  (lift d c (TmVar n) =
    if n < c then TmVar n else TmVar (n + d)) /\
  (lift d c (TmApp f a) = TmApp (lift d c f) (lift d c a)) /\
  (lift d c (TmLam A b) = TmLam (lift d c A) (lift d (c + 1) b)) /\
  (lift d c (TmLamU b) = TmLamU (lift d (c + 1) b)) /\
  (lift d c (TmPi A B) = TmPi (lift d c A) (lift d (c + 1) B))
End

(* Capture-avoiding substitution for the variable at cutoff c. *)
Definition subst_def[simp]:
  (subst u c TmKind = TmKind) /\
  (subst u c TmType = TmType) /\
  (subst u c (TmConst s) = TmConst s) /\
  (subst u c (TmVar n) =
    if n < c then TmVar n
    else if n = c then lift c 0 u
    else TmVar (n - 1)) /\
  (subst u c (TmApp f a) = TmApp (subst u c f) (subst u c a)) /\
  (subst u c (TmLam A b) = TmLam (subst u c A) (subst u (c + 1) b)) /\
  (subst u c (TmLamU b) = TmLamU (subst u (c + 1) b)) /\
  (subst u c (TmPi A B) = TmPi (subst u c A) (subst u (c + 1) B))
End

Definition subst0_def:
  subst0 u t = subst u 0 t
End

Theorem lift_zero[simp]:
  !t c. lift 0 c t = t
Proof
  Induct >> simp[]
QED

Theorem lift_var_below[simp]:
  !d c n. n < c ==> lift d c (TmVar n) = TmVar n
Proof
  simp[]
QED

Theorem lift_var_at_or_above[simp]:
  !d c n. c <= n ==> lift d c (TmVar n) = TmVar (n + d)
Proof
  simp[] >> metis_tac[NOT_LESS]
QED

Theorem subst_var_same[simp]:
  !u c. subst u c (TmVar c) = lift c 0 u
Proof
  simp[]
QED

Theorem subst_var_below[simp]:
  !u c n. n < c ==> subst u c (TmVar n) = TmVar n
Proof
  simp[]
QED

Theorem subst_var_above[simp]:
  !u c n. c < n ==> subst u c (TmVar n) = TmVar (n - 1)
Proof
  simp[] >> metis_tac[LESS_ANTISYM, LESS_REFL]
QED

Theorem subst0_var0[simp]:
  !u. subst0 u (TmVar 0) = u
Proof
  simp[subst0_def]
QED
