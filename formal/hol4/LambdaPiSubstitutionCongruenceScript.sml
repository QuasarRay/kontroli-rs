Theory LambdaPiSubstitutionCongruence
Ancestors
  LambdaPiRegularity
Libs
  boolSimps

Theorem convertible_app_fun_congr:
  !R f f' a.
    convertible R f f' ==>
    convertible R (TmApp f a) (TmApp f' a)
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[red_rules, EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS]
QED

Theorem convertible_app_arg_congr:
  !R f a a'.
    convertible R a a' ==>
    convertible R (TmApp f a) (TmApp f a')
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[red_rules, EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS]
QED

Theorem convertible_lam_type_congr:
  !R A A' b.
    convertible R A A' ==>
    convertible R (TmLam A b) (TmLam A' b)
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[red_rules, EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS]
QED

Theorem convertible_lam_body_congr:
  !R A b b'.
    convertible R b b' ==>
    convertible R (TmLam A b) (TmLam A b')
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[red_rules, EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS]
QED

Theorem convertible_lamU_body_congr:
  !R b b'.
    convertible R b b' ==>
    convertible R (TmLamU b) (TmLamU b')
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[red_rules, EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS]
QED

Theorem convertible_pi_domain_congr:
  !R A A' B.
    convertible R A A' ==>
    convertible R (TmPi A B) (TmPi A' B)
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[red_rules, EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS]
QED

Theorem convertible_pi_codomain_congr:
  !R A B B'.
    convertible R B B' ==>
    convertible R (TmPi A B) (TmPi A B')
Proof
  rw[convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[red_rules, EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS]
QED

(* Dual to convertible_subst_from_rewrite_closed: here the body is fixed and
   the replacement term varies.  The variable-at-cutoff case needs lift
   closure; all constructor cases follow from conversion congruence. *)
Theorem convertible_subst_argument:
  !R.
    rewrite_lift_closed R ==>
    !a a'. convertible R a a' ==>
      !t c. convertible R (subst a c t) (subst a' c t)
Proof
  gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  Induct >> simp[]
  >- (rpt gen_tac >>
      Cases_on `n < c` >> simp[] >>
      Cases_on `n = c` >> simp[] >>
      metis_tac[
        convertible_refl,
        convertible_lift_from_rewrite_closed
      ])
  >- metis_tac[
        convertible_app_fun_congr,
        convertible_app_arg_congr,
        convertible_trans
      ]
  >- metis_tac[
        convertible_lam_type_congr,
        convertible_lam_body_congr,
        convertible_trans
      ]
  >- metis_tac[convertible_lamU_body_congr]
  >- metis_tac[
        convertible_pi_domain_congr,
        convertible_pi_codomain_congr,
        convertible_trans
      ]
QED

Theorem convertible_subst0_argument:
  !R a a' t.
    rewrite_lift_closed R /\
    convertible R a a' ==>
    convertible R (subst0 a t) (subst0 a' t)
Proof
  simp[subst0_def] >>
  metis_tac[convertible_subst_argument]
QED

val _ = export_theory();
