Theory LambdaPiRegularity
Ancestors
  LambdaPiContextWellformed LambdaPiGeneration LambdaPiContextConversion LambdaPiTypingSubstitution LambdaPiSubstLookup LambdaPiWeakening LambdaPiContextInsertion LambdaPiScoping LambdaPiBinderAlgebra LambdaPiTyping LambdaPiReduction LambdaPiSyntax KontroliBase arithmetic string relation list rich_list LambdaPiSubstitution LambdaPiSubjectReduction LambdaPiMetatheory
Libs
  boolSimps numLib

Theorem signature_type_in_context:
  !Sigma R G c A.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    Sigma c A ==>
    ?s. is_sort s /\ has_type Sigma R G A s
Proof
  rw[signature_wf_def] >>
  first_x_assum drule >>
  strip_tac >>
  qexists_tac `s` >>
  conj_tac
  >- assumption >>
  `has_type Sigma R ([] ++ G)
      (lift (LENGTH G) 0 A)
      (lift (LENGTH G) 0 s)` by
    metis_tac[has_type_append_suffix] >>
  `lift (LENGTH G) 0 A = A` by
    metis_tac[signature_decl_lift_at_identity] >>
  `lift (LENGTH G) 0 s = s` by
    metis_tac[lift_sort_identity] >>
  fs[]
QED

Theorem application_result_typeable:
  !Sigma R G f a A B.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    rewrite_substitution_closed R /\
    has_type Sigma R G f (TmPi A B) /\
    has_type Sigma R G a A /\
    (?s. is_sort s /\ has_type Sigma R G (TmPi A B) s) ==>
    ?s. is_sort s /\ has_type Sigma R G (subst0 a B) s
Proof
  rpt strip_tac >>
  qpat_x_assum `?s. _` strip_assume_tac >>
  `?s0.
      is_sort s0 /\
      has_type Sigma R G A TmType /\
      has_type Sigma R (G ++ [A]) B s0 /\
      convertible R s0 s` by
    metis_tac[product_generation] >>
  qpat_x_assum `?s0. _` strip_assume_tac >>
  qexists_tac `s0` >>
  conj_tac
  >- assumption >>
  `has_type Sigma R (subst_context G a [])
      (subst a 0 B)
      (subst a 0 s0)` by
    metis_tac[has_type_substitution] >>
  fs[subst_context_empty, subst0_def]
QED

(* Type regularity: every type produced in a well-formed context is either
   Kind or is itself classified by one of the two sorts. *)
Theorem typing_regularity:
  !Sigma R G t A.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    rewrite_substitution_closed R /\
    wf_context Sigma R G /\
    has_type Sigma R G t A ==>
    A = TmKind \/
    ?s. is_sort s /\ has_type Sigma R G A s
Proof
  ho_match_mp_tac has_type_ind
  >- (rpt strip_tac >> simp[])
  >- (rpt strip_tac >>
      right >>
      metis_tac[signature_type_in_context])
  >- (rpt strip_tac >>
      right >>
      qexists_tac `TmType` >>
      simp[] >>
      metis_tac[ctx_type_well_typed])
  >- (rpt strip_tac >>
      fs[is_sort_def] >>
      metis_tac[has_type_rules])
  >- (rpt strip_tac >>
      right >>
      metis_tac[has_type_rules])
  >- (rpt strip_tac >>
      right >>
      metis_tac[has_type_rules])
  >- (rpt strip_tac >>
      right >>
      metis_tac[application_result_typeable])
  >- (rpt strip_tac >>
      right >>
      metis_tac[])
QED

val _ = export_theory();
