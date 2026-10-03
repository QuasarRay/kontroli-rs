Theory LambdaPiSubjectReductionComplete
Ancestors
  LambdaPiBetaApplication
Libs
  boolSimps

Theorem product_domain_preserves_type:
  !Sigma R G A A' B s.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    has_type Sigma R G A TmType /\
    has_type Sigma R G A' TmType /\
    has_type Sigma R (G ++ [A]) B s /\
    is_sort s /\
    red R A A' ==>
    has_type Sigma R G (TmPi A' B) s
Proof
  rpt strip_tac >>
  `convertible R A A'` by metis_tac[red_implies_convertible] >>
  `has_type Sigma R (G ++ [A']) B s` by
    metis_tac[has_type_context_conversion, APPEND_NIL] >>
  metis_tac[has_type_rules]
QED

Theorem lambda_domain_preserves_type:
  !Sigma R G A A' B b s.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    has_type Sigma R G A TmType /\
    has_type Sigma R G A' TmType /\
    has_type Sigma R (G ++ [A]) B s /\
    is_sort s /\
    has_type Sigma R (G ++ [A]) b B /\
    red R A A' ==>
    has_type Sigma R G (TmLam A' b) (TmPi A B)
Proof
  rpt strip_tac >>
  `convertible R A A'` by metis_tac[red_implies_convertible] >>
  `has_type Sigma R (G ++ [A']) B s` by
    metis_tac[has_type_context_conversion, APPEND_NIL] >>
  `has_type Sigma R (G ++ [A']) b B` by
    metis_tac[has_type_context_conversion, APPEND_NIL] >>
  `has_type Sigma R G (TmLam A' b) (TmPi A' B)` by
    metis_tac[has_type_rules] >>
  `has_type Sigma R G (TmPi A B) s` by
    metis_tac[has_type_rules] >>
  `red R (TmPi A B) (TmPi A' B)` by
    metis_tac[red_rules] >>
  `convertible R (TmPi A' B) (TmPi A B)` by
    metis_tac[red_implies_convertible, convertible_sym] >>
  metis_tac[has_type_rules]
QED

Theorem subject_reduction_core:
  !Sigma R G t T.
    has_type Sigma R G t T ==>
    !u.
      signature_wf Sigma R /\
      rewrite_lift_closed R /\
      rewrite_substitution_closed R /\
      rewrite_preserves_typing Sigma R /\
      product_compatible R /\
      wf_context Sigma R G /\
      red R t u ==>
      has_type Sigma R G u T
Proof
  ho_match_mp_tac has_type_ind
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[user_rewrite_subject_reduction])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[user_rewrite_subject_reduction])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[user_rewrite_subject_reduction])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        user_rewrite_subject_reduction,
        product_domain_preserves_type,
        wf_context_extend,
        has_type_rules
      ])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        user_rewrite_subject_reduction,
        lambda_domain_preserves_type,
        wf_context_extend,
        has_type_rules
      ])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        user_rewrite_subject_reduction,
        wf_context_extend,
        has_type_rules
      ])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        user_rewrite_subject_reduction,
        beta_annotated_preserves_type,
        beta_unannotated_preserves_type,
        application_argument_preserves_type,
        has_type_rules
      ])
  >- (rpt strip_tac >>
      metis_tac[has_type_rules])
QED

Theorem subject_reduction_from_metatheory:
  !Sigma R.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    rewrite_substitution_closed R /\
    rewrite_preserves_typing Sigma R /\
    product_compatible R ==>
    subject_reduction Sigma R
Proof
  rw[subject_reduction_def] >>
  metis_tac[subject_reduction_core]
QED

Theorem subject_reduction_from_confluence:
  !Sigma R.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    rewrite_substitution_closed R /\
    rewrite_preserves_typing Sigma R /\
    pi_root_free R /\
    confluent R ==>
    subject_reduction Sigma R
Proof
  metis_tac[
    subject_reduction_from_metatheory,
    confluent_pi_root_free_product_compatible
  ]
QED

val _ = export_theory();
