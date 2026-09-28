Theory LambdaPiSubjectReductionFinal
Ancestors
  LambdaPiStructuralReduction
Libs
  boolSimps

Theorem has_type_red_preserved:
  !Sigma R G t A.
    has_type Sigma R G t A ==>
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    rewrite_substitution_closed R /\
    rewrite_preserves_typing Sigma R /\
    product_compatible R /\
    wf_context Sigma R G ==>
    !u. red R t u ==> has_type Sigma R G u A
Proof
  ho_match_mp_tac has_type_ind
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        has_type_rules,
        user_rewrite_subject_reduction
      ])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        has_type_rules,
        user_rewrite_subject_reduction
      ])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        has_type_rules,
        user_rewrite_subject_reduction
      ])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        has_type_rules,
        wf_context_extend,
        product_domain_preserves_type,
        product_codomain_preserves_type,
        user_rewrite_subject_reduction
      ])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        has_type_rules,
        wf_context_extend,
        lambda_domain_preserves_type,
        lambda_body_preserves_type,
        user_rewrite_subject_reduction
      ])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        has_type_rules,
        wf_context_extend,
        lambdaU_body_preserves_type,
        user_rewrite_subject_reduction
      ])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        has_type_rules,
        beta_annotated_preserves_type,
        beta_unannotated_preserves_type,
        application_function_preserves_type,
        application_argument_preserves_type,
        user_rewrite_subject_reduction
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
  metis_tac[has_type_red_preserved]
QED

val _ = export_theory();
