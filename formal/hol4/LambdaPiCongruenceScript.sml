Theory LambdaPiCongruence
Ancestors
  LambdaPiRegularity
Libs
  boolSimps numLib

Theorem convertible_app_fun:
  !R f g.
    convertible R f g ==>
    !a. convertible R (TmApp f a) (TmApp g a)
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS, red_rules]
QED

Theorem convertible_app_arg:
  !R a b.
    convertible R a b ==>
    !f. convertible R (TmApp f a) (TmApp f b)
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS, red_rules]
QED

Theorem convertible_lam_type:
  !R A A'.
    convertible R A A' ==>
    !b. convertible R (TmLam A b) (TmLam A' b)
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS, red_rules]
QED

Theorem convertible_lam_body:
  !R b b'.
    convertible R b b' ==>
    !A. convertible R (TmLam A b) (TmLam A b')
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS, red_rules]
QED

Theorem convertible_lamU_body:
  !R b b'.
    convertible R b b' ==>
    convertible R (TmLamU b) (TmLamU b')
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS, red_rules]
QED

Theorem convertible_pi_domain:
  !R A A'.
    convertible R A A' ==>
    !B. convertible R (TmPi A B) (TmPi A' B)
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS, red_rules]
QED

Theorem convertible_pi_codomain:
  !R B B'.
    convertible R B B' ==>
    !A. convertible R (TmPi A B) (TmPi A B')
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS, red_rules]
QED

Theorem convertible_app:
  !R f f' a a'.
    convertible R f f' /\ convertible R a a' ==>
    convertible R (TmApp f a) (TmApp f' a')
Proof
  metis_tac[convertible_app_fun, convertible_app_arg, convertible_trans]
QED

Theorem convertible_lam:
  !R A A' b b'.
    convertible R A A' /\ convertible R b b' ==>
    convertible R (TmLam A b) (TmLam A' b')
Proof
  metis_tac[convertible_lam_type, convertible_lam_body, convertible_trans]
QED

Theorem convertible_pi:
  !R A A' B B'.
    convertible R A A' /\ convertible R B B' ==>
    convertible R (TmPi A B) (TmPi A' B')
Proof
  metis_tac[convertible_pi_domain, convertible_pi_codomain, convertible_trans]
QED

(* Changing only the term substituted for a de Bruijn variable preserves
   conversion of the resulting term. *)
Theorem subst_argument_convertible:
  !t R u v c.
    rewrite_lift_closed R /\
    convertible R u v ==>
    convertible R (subst u c t) (subst v c t)
Proof
  Induct
  >- simp[]
  >- simp[]
  >- simp[]
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `n < c`
      >- simp[] >>
      Cases_on `n = c`
      >- (simp[] >>
          metis_tac[convertible_lift_from_rewrite_closed]) >>
      simp[])
  >- (rpt strip_tac >>
      simp[] >>
      metis_tac[convertible_app])
  >- (rpt strip_tac >>
      simp[] >>
      metis_tac[convertible_lam])
  >- (rpt strip_tac >>
      simp[] >>
      metis_tac[convertible_lamU_body])
  >- (rpt strip_tac >>
      simp[] >>
      metis_tac[convertible_pi])
QED

Theorem application_result_has_sort:
  !Sigma R G f a A B.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    rewrite_substitution_closed R /\
    wf_context Sigma R G /\
    has_type Sigma R G f (TmPi A B) /\
    has_type Sigma R G a A ==>
    ?s. is_sort s /\ has_type Sigma R G (subst0 a B) s
Proof
  rpt strip_tac >>
  `TmPi A B = TmKind \/
    ?s. is_sort s /\ has_type Sigma R G (TmPi A B) s` by
    metis_tac[typing_regularity] >>
  `TmPi A B <> TmKind` by simp[] >>
  metis_tac[application_result_typeable]
QED

val _ = export_theory();
