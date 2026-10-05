Theory LambdaPiStructuralReduction
Ancestors
  LambdaPiBetaApplication LambdaPiCongruence LambdaPiRegularity LambdaPiContextWellformed LambdaPiGeneration LambdaPiContextConversion LambdaPiTypingSubstitution LambdaPiSubstLookup LambdaPiWeakening LambdaPiContextInsertion LambdaPiScoping LambdaPiBinderAlgebra LambdaPiTyping LambdaPiReduction LambdaPiSyntax KontroliBase arithmetic string relation list rich_list LambdaPiSubstitution LambdaPiSubjectReduction LambdaPiMetatheory
Libs
  boolSimps

Theorem product_domain_preserves_type:
  !Sigma R G A A' B s.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    has_type Sigma R G A TmType /\
    has_type Sigma R G A' TmType /\
    red R A A' /\
    has_type Sigma R (G ++ [A]) B s /\
    is_sort s ==>
    has_type Sigma R G (TmPi A' B) s
Proof
  rpt strip_tac >>
  `convertible R A A'` by
    metis_tac[red_implies_convertible] >>
  `has_type Sigma R (G ++ [A']) B s` by
    metis_tac[
      has_type_context_conversion,
      APPEND_NIL
    ] >>
  metis_tac[has_type_rules]
QED

Theorem product_codomain_preserves_type:
  !Sigma R G A B' s.
    has_type Sigma R G A TmType /\
    has_type Sigma R (G ++ [A]) B' s /\
    is_sort s ==>
    has_type Sigma R G (TmPi A B') s
Proof
  metis_tac[has_type_rules]
QED

Theorem lambda_domain_preserves_type:
  !Sigma R G A A' B b s.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    has_type Sigma R G A TmType /\
    has_type Sigma R G A' TmType /\
    red R A A' /\
    has_type Sigma R (G ++ [A]) B s /\
    is_sort s /\
    has_type Sigma R (G ++ [A]) b B ==>
    has_type Sigma R G (TmLam A' b) (TmPi A B)
Proof
  rpt strip_tac >>
  `convertible R A A'` by
    metis_tac[red_implies_convertible] >>
  `has_type Sigma R (G ++ [A']) B s` by
    metis_tac[
      has_type_context_conversion,
      APPEND_NIL
    ] >>
  `has_type Sigma R (G ++ [A']) b B` by
    metis_tac[
      has_type_context_conversion,
      APPEND_NIL
    ] >>
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

Theorem lambda_body_preserves_type:
  !Sigma R G A B b' s.
    has_type Sigma R G A TmType /\
    has_type Sigma R (G ++ [A]) B s /\
    is_sort s /\
    has_type Sigma R (G ++ [A]) b' B ==>
    has_type Sigma R G (TmLam A b') (TmPi A B)
Proof
  metis_tac[has_type_rules]
QED

Theorem lambdaU_body_preserves_type:
  !Sigma R G A B b' s.
    has_type Sigma R G A TmType /\
    has_type Sigma R (G ++ [A]) B s /\
    is_sort s /\
    has_type Sigma R (G ++ [A]) b' B ==>
    has_type Sigma R G (TmLamU b') (TmPi A B)
Proof
  metis_tac[has_type_rules]
QED

Theorem application_function_preserves_type:
  !Sigma R G f' a A B.
    has_type Sigma R G f' (TmPi A B) /\
    has_type Sigma R G a A ==>
    has_type Sigma R G (TmApp f' a) (subst0 a B)
Proof
  metis_tac[has_type_rules]
QED

val _ = export_theory();
