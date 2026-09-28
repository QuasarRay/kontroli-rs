Theory LambdaPiContextConversion
Ancestors
  LambdaPiTypingSubstitution
Libs
  boolSimps numLib

Theorem ctx_type_replace_suffix:
  !G A A' H n T.
    n < LENGTH H /\
    ctx_type (G ++ [A] ++ H) n T ==>
    ctx_type (G ++ [A'] ++ H) n T
Proof
  rw[ctx_type_def] >>
  conj_tac
  >- simp[] >>
  qpat_x_assum `T = _` SUBST1_TAC >>
  qabbrev_tac `i = LENGTH H - SUC n` >>
  `i < LENGTH H` by
    (qunabbrev_tac `i` >> numLib.ARITH_TAC) >>
  `LENGTH (G ++ [A] ++ H) - SUC n =
    LENGTH (G ++ [A]) + i` by
    (qunabbrev_tac `i` >> simp[] >> numLib.ARITH_TAC) >>
  `LENGTH (G ++ [A'] ++ H) - SUC n =
    LENGTH (G ++ [A']) + i` by
    (qunabbrev_tac `i` >> simp[] >> numLib.ARITH_TAC) >>
  asm_simp_tac bool_ss [el_append_offset]
QED

Theorem ctx_type_replace_prefix:
  !G A A' H n T.
    LENGTH H < n /\
    ctx_type (G ++ [A] ++ H) n T ==>
    ctx_type (G ++ [A'] ++ H) n T
Proof
  rw[ctx_type_def] >>
  conj_tac
  >- simp[] >>
  qpat_x_assum `T = _` SUBST1_TAC >>
  qabbrev_tac `m = n - SUC (LENGTH H)` >>
  `m < LENGTH G` by
    (qunabbrev_tac `m` >> fs[] >> numLib.ARITH_TAC) >>
  `LENGTH (G ++ [A] ++ H) - SUC n =
    LENGTH G - SUC m` by
    (qunabbrev_tac `m` >> simp[] >> numLib.ARITH_TAC) >>
  `LENGTH (G ++ [A'] ++ H) - SUC n =
    LENGTH G - SUC m` by
    (qunabbrev_tac `m` >> simp[] >> numLib.ARITH_TAC) >>
  `LENGTH G - SUC m < LENGTH G` by numLib.ARITH_TAC >>
  asm_simp_tac bool_ss [rich_listTheory.EL_APPEND1]
QED

Theorem ctx_type_replacement_binder:
  !G A H.
    ctx_type (G ++ [A] ++ H) (LENGTH H)
      (lift (SUC (LENGTH H)) 0 A)
Proof
  rw[ctx_type_def] >>
  conj_tac
  >- simp[] >>
  `LENGTH (G ++ [A] ++ H) - SUC (LENGTH H) = LENGTH G` by
    (simp[] >> numLib.ARITH_TAC) >>
  pop_assum SUBST1_TAC >>
  `LENGTH G < LENGTH (G ++ [A])` by simp[] >>
  simp[rich_listTheory.EL_APPEND1, rich_listTheory.EL_LENGTH_APPEND_0]
QED

Theorem variable_typing_context_conversion:
  !Sigma R G H A A' n T.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    has_type Sigma R G A TmType /\
    has_type Sigma R G A' TmType /\
    convertible R A A' /\
    ctx_type (G ++ [A] ++ H) n T ==>
    has_type Sigma R (G ++ [A'] ++ H) (TmVar n) T
Proof
  rpt strip_tac >>
  Cases_on `n < LENGTH H`
  >- metis_tac[ctx_type_replace_suffix, has_type_rules] >>
  Cases_on `n = LENGTH H`
  >- (
    `T = lift (SUC (LENGTH H)) 0 A` by
      metis_tac[ctx_type_eliminated_binder] >>
    `ctx_type (G ++ [A'] ++ H) (LENGTH H)
       (lift (SUC (LENGTH H)) 0 A')` by
      metis_tac[ctx_type_replacement_binder] >>
    `has_type Sigma R (G ++ [A'] ++ H)
       (TmVar (LENGTH H))
       (lift (SUC (LENGTH H)) 0 A')` by
      metis_tac[has_type_rules] >>
    `has_type Sigma R (G ++ [A'] ++ H)
       (lift (SUC (LENGTH H)) 0 A) TmType` by (
      `LENGTH ([A'] ++ H) = SUC (LENGTH H)` by simp[] >>
      metis_tac[has_type_append_suffix, APPEND_ASSOC]) >>
    `convertible R
       (lift (SUC (LENGTH H)) 0 A')
       (lift (SUC (LENGTH H)) 0 A)` by
      metis_tac[
        convertible_sym,
        convertible_lift_from_rewrite_closed
      ] >>
    metis_tac[has_type_rules]
  ) >>
  `LENGTH H < n` by numLib.ARITH_TAC >>
  metis_tac[ctx_type_replace_prefix, has_type_rules]
QED

Theorem has_type_context_conversion:
  !Sigma R C t T.
    has_type Sigma R C t T ==>
    !G H A A'.
      C = G ++ [A] ++ H /\
      signature_wf Sigma R /\
      rewrite_lift_closed R /\
      has_type Sigma R G A TmType /\
      has_type Sigma R G A' TmType /\
      convertible R A A' ==>
      has_type Sigma R (G ++ [A'] ++ H) t T
Proof
  ho_match_mp_tac has_type_ind >>
  rpt strip_tac >>
  fs[APPEND_ASSOC] >>
  metis_tac[
    has_type_rules,
    variable_typing_context_conversion,
    APPEND_ASSOC
  ]
QED

Theorem wf_context_context_conversion:
  !Sigma R G H A A'.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    wf_context Sigma R (G ++ [A] ++ H) /\
    has_type Sigma R G A TmType /\
    has_type Sigma R G A' TmType /\
    convertible R A A' ==>
    wf_context Sigma R (G ++ [A'] ++ H)
Proof
  rpt gen_tac >>
  Induct_on `H` using SNOC_INDUCT
  >- (simp[] >>
      metis_tac[wf_context_prefix, wf_context_rules])
  >- (rpt strip_tac >>
      fs[SNOC_APPEND, APPEND_ASSOC] >>
      metis_tac[
        wf_context_snoc_inv,
        has_type_context_conversion,
        wf_context_rules,
        APPEND_ASSOC
      ])
QED

val _ = export_theory();
