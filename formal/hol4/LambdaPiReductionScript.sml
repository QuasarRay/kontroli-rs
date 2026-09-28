Theory LambdaPiReduction
Ancestors
  LambdaPiSyntax relation
Libs
  boolSimps

(* R is the user-supplied rewrite relation. The compatible closure below adds
   beta reduction and closure under all λΠ term constructors. *)
Inductive red:
[~beta:]
  red R (TmApp (TmLam A b) u) (subst0 u b)
[~beta_unannotated:]
  red R (TmApp (TmLamU b) u) (subst0 u b)
[~user:]
  R t u ==> red R t u
[~app_fun:]
  red R f f' ==> red R (TmApp f a) (TmApp f' a)
[~app_arg:]
  red R a a' ==> red R (TmApp f a) (TmApp f a')
[~lam_type:]
  red R A A' ==> red R (TmLam A b) (TmLam A' b)
[~lam_body:]
  red R b b' ==> red R (TmLam A b) (TmLam A b')
[~lamU_body:]
  red R b b' ==> red R (TmLamU b) (TmLamU b')
[~pi_domain:]
  red R A A' ==> red R (TmPi A B) (TmPi A' B)
[~pi_codomain:]
  red R B B' ==> red R (TmPi A B) (TmPi A B')
End

Definition reduces_def:
  reduces R t u <=> RTC (red R) t u
End

Definition joinable_def:
  joinable R t u <=>
    ?v. reduces R t v /\ reduces R u v
End

Definition confluent_def:
  confluent R <=>
    !x y z. reduces R x y /\ reduces R x z ==>
      ?u. reduces R y u /\ reduces R z u
End

Theorem red_contains_user:
  !R t u. R t u ==> red R t u
Proof
  metis_tac[red_rules]
QED

Theorem beta_is_red:
  !R A b u. red R (TmApp (TmLam A b) u) (subst0 u b)
Proof
  metis_tac[red_rules]
QED

Theorem beta_unannotated_is_red:
  !R b u. red R (TmApp (TmLamU b) u) (subst0 u b)
Proof
  metis_tac[red_rules]
QED

Theorem reduces_refl[simp]:
  !R t. reduces R t t
Proof
  simp[reduces_def, RTC_REFL]
QED

Theorem reduces_step:
  !R t u. red R t u ==> reduces R t u
Proof
  simp[reduces_def] >> metis_tac[RTC_SUBSET]
QED

Theorem reduces_trans:
  !R x y z. reduces R x y /\ reduces R y z ==> reduces R x z
Proof
  simp[reduces_def] >> metis_tac[RTC_TRANS]
QED

Theorem joinable_refl[simp]:
  !R t. joinable R t t
Proof
  simp[joinable_def]
QED

Theorem joinable_sym:
  !R x y. joinable R x y ==> joinable R y x
Proof
  simp[joinable_def] >> metis_tac[]
QED

(* Confluence is exactly what is needed to make common-reduct
   convertibility transitive. No termination assumption is hidden here. *)
Theorem joinable_trans_confluent:
  !R. confluent R ==>
    !x y z. joinable R x y /\ joinable R y z ==> joinable R x z
Proof
  rw[confluent_def, joinable_def] >>
  rename [`reduces R x a`, `reduces R y a`,
          `reduces R y b`, `reduces R z b`] >>
  `?c. reduces R a c /\ reduces R b c` by metis_tac[] >>
  qexists_tac `c` >>
  metis_tac[reduces_trans]
QED

Theorem joinable_equivalence_under_confluence:
  !R. confluent R ==>
    (!x. joinable R x x) /\
    (!x y. joinable R x y ==> joinable R y x) /\
    (!x y z. joinable R x y /\ joinable R y z ==> joinable R x z)
Proof
  metis_tac[joinable_refl, joinable_sym, joinable_trans_confluent]
QED
