Theory LambdaPiContextWellformed
Ancestors
  LambdaPiGeneration LambdaPiContextConversion LambdaPiTypingSubstitution LambdaPiSubstLookup LambdaPiWeakening LambdaPiContextInsertion LambdaPiScoping LambdaPiBinderAlgebra LambdaPiTyping LambdaPiReduction LambdaPiSyntax KontroliBase arithmetic string relation list rich_list LambdaPiSubstitution LambdaPiSubjectReduction LambdaPiMetatheory
Libs
  boolSimps numLib

Theorem ctx_type_snoc_zero_inv:
  !G B A.
    ctx_type (G ++ [B]) 0 A ==>
    A = lift 1 0 B
Proof
  rw[ctx_type_def] >>
  simp[rich_listTheory.EL_LENGTH_APPEND_0]
QED

Theorem ctx_type_snoc_suc_inv:
  !G B n A.
    ctx_type (G ++ [B]) (SUC n) A ==>
    ?A0.
      ctx_type G n A0 /\
      A = lift 1 0 A0
Proof
  rw[ctx_type_def] >>
  `n < LENGTH G` by numLib.ARITH_TAC >>
  qpat_x_assum `A = _` SUBST1_TAC >>
  qexists_tac `lift (SUC n) 0 (EL (LENGTH G - SUC n) G)` >>
  conj_tac
  >- simp[ctx_type_def] >>
  `LENGTH (G ++ [B]) - SUC (SUC n) =
    LENGTH G - SUC n` by
    (simp[] >> numLib.ARITH_TAC) >>
  pop_assum SUBST1_TAC >>
  `LENGTH G - SUC n < LENGTH G` by numLib.ARITH_TAC >>
  simp[rich_listTheory.EL_APPEND1, lift_compose, ADD1]
QED

(* In a well-formed local context every reverse-index lookup returns a type
   that is itself classified by Type in the full context. *)
Theorem ctx_type_well_typed:
  !n Sigma R G A.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    wf_context Sigma R G /\
    ctx_type G n A ==>
    has_type Sigma R G A TmType
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `G` using SNOC_CASES
      >- fs[ctx_type_empty]
      >- (fs[GSYM SNOC_APPEND] >>
          metis_tac[
            ctx_type_snoc_zero_inv,
            wf_context_snoc_inv,
            has_type_append_suffix
          ]))
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `G` using SNOC_CASES
      >- fs[ctx_type_empty]
      >- (fs[GSYM SNOC_APPEND] >>
          metis_tac[
            ctx_type_snoc_suc_inv,
            wf_context_snoc_inv,
            has_type_append_suffix
          ]))
QED

val _ = export_theory();
