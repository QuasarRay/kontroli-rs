Theory LambdaPiSubstLookup
Ancestors
  LambdaPiWeakening LambdaPiSubstitution
Libs
  boolSimps numLib

Theorem subst_ctx_from_el:
  !H u k i.
    i < LENGTH H ==>
    EL i (subst_ctx_from u k H) =
      subst u (k + i) (EL i H)
Proof
  Induct >>
  simp[subst_ctx_from_def] >>
  rpt gen_tac >>
  Cases_on `i` >>
  simp[ADD_CLAUSES, ADD_ASSOC]
QED

Theorem subst_ctx_el:
  !H u i.
    i < LENGTH H ==>
    EL i (subst_ctx u H) = subst u i (EL i H)
Proof
  simp[subst_ctx_def, subst_ctx_from_el]
QED

(* Variables naming a binder in the suffix retain their de Bruijn index.
   Their stored declaration is substituted at exactly its depth in H. *)
Theorem ctx_type_subst_suffix:
  !G A H u n T.
    n < LENGTH H /\
    ctx_type (G ++ [A] ++ H) n T ==>
    ctx_type (subst_context G u H) n
      (subst u (LENGTH H) T)
Proof
  rw[ctx_type_def, subst_context_def] >>
  conj_tac
  >- simp[] >>
  qpat_x_assum `T = _` SUBST1_TAC >>
  qabbrev_tac `i = LENGTH H - SUC n` >>
  `i < LENGTH H` by
    (qunabbrev_tac `i` >> numLib.ARITH_TAC) >>
  `SUC n <= LENGTH H` by numLib.ARITH_TAC >>
  `LENGTH (G ++ [A] ++ H) - SUC n =
    LENGTH (G ++ [A]) + i` by
    (qunabbrev_tac `i` >> simp[] >> numLib.ARITH_TAC) >>
  `LENGTH (G ++ subst_ctx u H) - SUC n =
    LENGTH G + i` by
    (qunabbrev_tac `i` >> simp[] >> numLib.ARITH_TAC) >>
  asm_simp_tac bool_ss
    [el_append_offset, subst_ctx_el, subst_lift_commute] >>
  qunabbrev_tac `i` >>
  numLib.ARITH_TAC
QED

(* The variable exactly at the suffix boundary names the binder being
   eliminated. *)
Theorem ctx_type_eliminated_binder:
  !G A H T.
    ctx_type (G ++ [A] ++ H) (LENGTH H) T ==>
    T = lift (SUC (LENGTH H)) 0 A
Proof
  rw[ctx_type_def] >>
  qpat_x_assum `T = _` SUBST1_TAC >>
  `LENGTH (G ++ [A] ++ H) - SUC (LENGTH H) = LENGTH G` by
    (simp[] >> numLib.ARITH_TAC) >>
  pop_assum SUBST1_TAC >>
  `LENGTH G < LENGTH (G ++ [A])` by simp[] >>
  simp[rich_listTheory.EL_APPEND1, rich_listTheory.EL_LENGTH_APPEND_0]
QED

(* Variables older than the eliminated binder move down by one.  Their type
   loses exactly the lift introduced by that binder. *)
Theorem ctx_type_subst_prefix:
  !G A H u n T.
    LENGTH H < n /\
    ctx_type (G ++ [A] ++ H) n T ==>
    ctx_type (subst_context G u H) (n - 1)
      (subst u (LENGTH H) T)
Proof
  rw[ctx_type_def, subst_context_def] >>
  conj_tac
  >- (simp[] >> numLib.ARITH_TAC) >>
  qpat_x_assum `T = _` SUBST1_TAC >>
  qabbrev_tac `m = n - SUC (LENGTH H)` >>
  `m < LENGTH G` by
    (qunabbrev_tac `m` >> fs[] >> numLib.ARITH_TAC) >>
  `LENGTH (G ++ [A] ++ H) - SUC n =
    LENGTH G - SUC m` by
    (qunabbrev_tac `m` >> simp[] >> numLib.ARITH_TAC) >>
  `LENGTH (G ++ subst_ctx u H) - SUC (n - 1) =
    LENGTH G - SUC m` by
    (qunabbrev_tac `m` >> simp[] >> numLib.ARITH_TAC) >>
  `LENGTH G - SUC m < LENGTH G` by numLib.ARITH_TAC >>
  `LENGTH H <= n` by numLib.ARITH_TAC >>
  asm_simp_tac bool_ss
    [rich_listTheory.EL_APPEND1, subst_lift_prefix_drop] >>
  numLib.ARITH_TAC
QED

Theorem eliminated_variable_substitution:
  !Sigma R G H A u T.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    has_type Sigma R G u A /\
    ctx_type (G ++ [A] ++ H) (LENGTH H) T ==>
    has_type Sigma R (subst_context G u H)
      (subst u (LENGTH H) (TmVar (LENGTH H)))
      (subst u (LENGTH H) T)
Proof
  rpt strip_tac >>
  `T = lift (SUC (LENGTH H)) 0 A` by
    metis_tac[ctx_type_eliminated_binder] >>
  pop_assum SUBST1_TAC >>
  fs[subst_context_def, subst_lift_prefix_drop] >>
  metis_tac[has_type_append_suffix]
QED

Theorem variable_typing_substitution:
  !Sigma R G H A u n T.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    has_type Sigma R G u A /\
    ctx_type (G ++ [A] ++ H) n T ==>
    has_type Sigma R (subst_context G u H)
      (subst u (LENGTH H) (TmVar n))
      (subst u (LENGTH H) T)
Proof
  rpt strip_tac >>
  Cases_on `n < LENGTH H`
  >- (simp[] >>
      metis_tac[ctx_type_subst_suffix, has_type_rules]) >>
  Cases_on `n = LENGTH H`
  >- metis_tac[eliminated_variable_substitution] >>
  `LENGTH H < n` by numLib.ARITH_TAC >>
  simp[] >>
  metis_tac[ctx_type_subst_prefix, has_type_rules]
QED

val _ = export_theory();
