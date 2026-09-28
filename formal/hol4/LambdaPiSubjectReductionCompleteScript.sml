Theory LambdaPiSubjectReductionComplete
Ancestors
  LambdaPiSubstitutionCongruence
  LambdaPiContextConversion
  LambdaPiGeneration
  LambdaPiRegularity
  LambdaPiTypingSubstitution
  LambdaPiSubjectReduction
Libs
  boolSimps

Theorem product_compatible_elim:
  !R A B A' B'.
    product_compatible R /\
    convertible R (TmPi A B) (TmPi A' B') ==>
    convertible R A A' /\ convertible R B B'
Proof
  simp[product_compatible_def] >> metis_tac[]
QED

Theorem function_product_typeable:
  !Sigma R G f A B.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    rewrite_substitution_closed R /\
    wf_context Sigma R G /\
    has_type Sigma R G f (TmPi A B) ==>
    ?s. is_sort s /\ has_type Sigma R G (TmPi A B) s
Proof
  rpt strip_tac >>
  `TmPi A B <> TmKind` by simp[] >>
  metis_tac[typing_regularity]
QED

Theorem application_result_typeable_from_function:
  !Sigma R G f a A B.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    rewrite_substitution_closed R /\
    wf_context Sigma R G /\
    has_type Sigma R G f (TmPi A B) /\
    has_type Sigma R G a A ==>
    ?s. is_sort s /\ has_type Sigma R G (subst0 a B) s
Proof
  metis_tac[
    function_product_typeable,
    application_result_typeable
  ]
QED

Theorem beta_annotated_subject_reduction:
  !Sigma R G D b a A B.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    rewrite_substitution_closed R /\
    product_compatible R /\
    wf_context Sigma R G /\
    has_type Sigma R G (TmLam D b) (TmPi A B) /\
    has_type Sigma R G a A ==>
    has_type Sigma R G (subst0 a b) (subst0 a B)
Proof
  rpt strip_tac >>
  `?C s.
      is_sort s /\
      has_type Sigma R G D TmType /\
      has_type Sigma R (G ++ [D]) C s /\
      has_type Sigma R (G ++ [D]) b C /\
      convertible R (TmPi D C) (TmPi A B)` by
    metis_tac[lambda_generation] >>
  qpat_x_assum `?C s. _` strip_assume_tac >>
  `convertible R D A /\ convertible R C B` by
    metis_tac[product_compatible_elim] >>
  `has_type Sigma R G a D` by
    metis_tac[
      has_type_rules,
      convertible_sym
    ] >>
  `has_type Sigma R G (subst0 a b) (subst0 a C)` by (
    `has_type Sigma R (subst_context G a [])
       (subst a 0 b) (subst a 0 C)` by
      metis_tac[has_type_substitution] >>
    fs[subst_context_empty, subst0_def]
  ) >>
  `?sT. is_sort sT /\
      has_type Sigma R G (subst0 a B) sT` by
    metis_tac[application_result_typeable_from_function] >>
  `convertible R (subst0 a C) (subst0 a B)` by
    metis_tac[convertible_subst_from_rewrite_closed] >>
  metis_tac[has_type_rules]
QED

Theorem beta_unannotated_subject_reduction:
  !Sigma R G b a A B.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    rewrite_substitution_closed R /\
    product_compatible R /\
    wf_context Sigma R G /\
    has_type Sigma R G (TmLamU b) (TmPi A B) /\
    has_type Sigma R G a A ==>
    has_type Sigma R G (subst0 a b) (subst0 a B)
Proof
  rpt strip_tac >>
  `?D C s.
      is_sort s /\
      has_type Sigma R G D TmType /\
      has_type Sigma R (G ++ [D]) C s /\
      has_type Sigma R (G ++ [D]) b C /\
      convertible R (TmPi D C) (TmPi A B)` by
    metis_tac[lambda_unannotated_generation] >>
  qpat_x_assum `?D C s. _` strip_assume_tac >>
  `convertible R D A /\ convertible R C B` by
    metis_tac[product_compatible_elim] >>
  `has_type Sigma R G a D` by
    metis_tac[
      has_type_rules,
      convertible_sym
    ] >>
  `has_type Sigma R G (subst0 a b) (subst0 a C)` by (
    `has_type Sigma R (subst_context G a [])
       (subst a 0 b) (subst a 0 C)` by
      metis_tac[has_type_substitution] >>
    fs[subst_context_empty, subst0_def]
  ) >>
  `?sT. is_sort sT /\
      has_type Sigma R G (subst0 a B) sT` by
    metis_tac[application_result_typeable_from_function] >>
  `convertible R (subst0 a C) (subst0 a B)` by
    metis_tac[convertible_subst_from_rewrite_closed] >>
  metis_tac[has_type_rules]
QED

(* Subject reduction is proved by induction over the typing derivation rather
   than the reduction derivation.  This keeps the conversion typing rule as the
   outermost case and avoids introducing a hidden typeability premise for the
   final type. *)
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
        has_type_context_conversion,
        red_implies_convertible,
        user_rewrite_subject_reduction
      ])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        has_type_rules,
        wf_context_extend,
        has_type_context_conversion,
        red_rules,
        red_implies_convertible,
        convertible_sym,
        user_rewrite_subject_reduction
      ])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        has_type_rules,
        wf_context_extend,
        user_rewrite_subject_reduction
      ])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        has_type_rules,
        beta_annotated_subject_reduction,
        beta_unannotated_subject_reduction,
        application_result_typeable_from_function,
        convertible_subst0_argument,
        red_implies_convertible,
        user_rewrite_subject_reduction
      ])
  >- (rpt strip_tac >>
      fs[Once red_cases] >>
      metis_tac[
        has_type_rules,
        user_rewrite_subject_reduction
      ])
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
