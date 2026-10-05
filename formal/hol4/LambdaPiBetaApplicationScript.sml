Theory LambdaPiBetaApplication
Ancestors
  LambdaPiCongruence LambdaPiRegularity LambdaPiContextWellformed LambdaPiGeneration LambdaPiContextConversion LambdaPiTypingSubstitution LambdaPiSubstLookup LambdaPiWeakening LambdaPiContextInsertion LambdaPiScoping LambdaPiBinderAlgebra LambdaPiTyping LambdaPiReduction LambdaPiSyntax KontroliBase arithmetic string relation list rich_list LambdaPiSubstitution LambdaPiSubjectReduction LambdaPiMetatheory
Libs
  boolSimps

Theorem beta_annotated_preserves_type:
  !Sigma R G A0 b a A B.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    rewrite_substitution_closed R /\
    product_compatible R /\
    wf_context Sigma R G /\
    has_type Sigma R G (TmLam A0 b) (TmPi A B) /\
    has_type Sigma R G a A ==>
    has_type Sigma R G (subst0 a b) (subst0 a B)
Proof
  rpt strip_tac >>
  `?B0 s.
      is_sort s /\
      has_type Sigma R G A0 TmType /\
      has_type Sigma R (G ++ [A0]) B0 s /\
      has_type Sigma R (G ++ [A0]) b B0 /\
      convertible R (TmPi A0 B0) (TmPi A B)` by
    metis_tac[lambda_generation] >>
  qpat_x_assum `?B0 s. _` strip_assume_tac >>
  `convertible R A0 A /\ convertible R B0 B` by
    metis_tac[product_compatible_def] >>
  `has_type Sigma R G a A0` by
    metis_tac[has_type_rules, convertible_sym] >>
  `typing_substitution Sigma R` by
    metis_tac[typing_substitution_from_closure] >>
  `has_type Sigma R G (subst0 a b) (subst0 a B0)` by
    metis_tac[beta_body_preserves_type_from_substitution] >>
  `convertible R (subst0 a B0) (subst0 a B)` by
    metis_tac[convertible_subst_from_rewrite_closed, subst0_def] >>
  `?q. is_sort q /\ has_type Sigma R G (subst0 a B) q` by
    metis_tac[application_result_has_sort] >>
  metis_tac[has_type_rules]
QED

Theorem beta_unannotated_preserves_type:
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
  `?A0 B0 s.
      is_sort s /\
      has_type Sigma R G A0 TmType /\
      has_type Sigma R (G ++ [A0]) B0 s /\
      has_type Sigma R (G ++ [A0]) b B0 /\
      convertible R (TmPi A0 B0) (TmPi A B)` by
    metis_tac[lambda_unannotated_generation] >>
  qpat_x_assum `?A0 B0 s. _` strip_assume_tac >>
  `convertible R A0 A /\ convertible R B0 B` by
    metis_tac[product_compatible_def] >>
  `has_type Sigma R G a A0` by
    metis_tac[has_type_rules, convertible_sym] >>
  `typing_substitution Sigma R` by
    metis_tac[typing_substitution_from_closure] >>
  `has_type Sigma R G (subst0 a b) (subst0 a B0)` by
    metis_tac[beta_body_preserves_type_from_substitution] >>
  `convertible R (subst0 a B0) (subst0 a B)` by
    metis_tac[convertible_subst_from_rewrite_closed, subst0_def] >>
  `?q. is_sort q /\ has_type Sigma R G (subst0 a B) q` by
    metis_tac[application_result_has_sort] >>
  metis_tac[has_type_rules]
QED

Theorem application_argument_preserves_type:
  !Sigma R G f a a' A B.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    rewrite_substitution_closed R /\
    wf_context Sigma R G /\
    has_type Sigma R G f (TmPi A B) /\
    has_type Sigma R G a A /\
    has_type Sigma R G a' A /\
    red R a a' ==>
    has_type Sigma R G (TmApp f a') (subst0 a B)
Proof
  rpt strip_tac >>
  `has_type Sigma R G (TmApp f a') (subst0 a' B)` by
    metis_tac[has_type_rules] >>
  `convertible R a' a` by
    metis_tac[red_implies_convertible, convertible_sym] >>
  `convertible R (subst0 a' B) (subst0 a B)` by
    metis_tac[subst_argument_convertible, subst0_def] >>
  `?s. is_sort s /\ has_type Sigma R G (subst0 a B) s` by
    metis_tac[application_result_has_sort] >>
  metis_tac[has_type_rules]
QED

val _ = export_theory();
