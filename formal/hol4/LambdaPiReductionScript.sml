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


(* Declarative conversion of the lambda-Pi calculus modulo is the least
   equivalence relation containing beta + user reduction.  It does not require
   confluence.  Common-reduct joinability remains below as the executable /
   confluent characterization. *)
Definition convertible_def:
  convertible R t u <=> EQC (red R) t u
End

Theorem red_implies_convertible:
  !R t u. red R t u ==> convertible R t u
Proof
  simp[convertible_def] >> metis_tac[EQC_R]
QED

Theorem convertible_refl[simp]:
  !R t. convertible R t t
Proof
  simp[convertible_def, EQC_REFL]
QED

Theorem convertible_sym:
  !R t u. convertible R t u ==> convertible R u t
Proof
  simp[convertible_def] >> metis_tac[EQC_SYM]
QED

Theorem convertible_trans:
  !R t u v.
    convertible R t u /\ convertible R u v ==>
    convertible R t v
Proof
  simp[convertible_def] >> metis_tac[EQC_TRANS]
QED

Theorem reduces_implies_convertible:
  !R t u. reduces R t u ==> convertible R t u
Proof
  simp[reduces_def, convertible_def] >> metis_tac[RTC_EQC]
QED

Theorem joinable_implies_convertible:
  !R t u. joinable R t u ==> convertible R t u
Proof
  simp[joinable_def] >>
  metis_tac[reduces_implies_convertible, convertible_sym, convertible_trans]
QED

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


Theorem red_implies_joinable:
  !R t u. red R t u ==> joinable R t u
Proof
  rw[joinable_def] >>
  qexists_tac `u` >>
  metis_tac[reduces_step, reduces_refl]
QED

Theorem convertible_implies_joinable_confluent:
  !R. confluent R ==>
    !t u. convertible R t u ==> joinable R t u
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[red_implies_joinable, joinable_refl, joinable_sym,
            joinable_trans_confluent]
QED

Theorem convertible_iff_joinable_confluent:
  !R. confluent R ==>
    !t u. convertible R t u <=> joinable R t u
Proof
  metis_tac[joinable_implies_convertible,
            convertible_implies_joinable_confluent]
QED

Theorem joinable_equivalence_under_confluence:
  !R. confluent R ==>
    (!x. joinable R x x) /\
    (!x y. joinable R x y ==> joinable R y x) /\
    (!x y z. joinable R x y /\ joinable R y z ==> joinable R x z)
Proof
  metis_tac[joinable_refl, joinable_sym, joinable_trans_confluent]
QED
