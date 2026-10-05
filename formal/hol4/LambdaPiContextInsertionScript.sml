Theory LambdaPiContextInsertion
Ancestors
  LambdaPiScoping LambdaPiBinderAlgebra LambdaPiTyping LambdaPiReduction LambdaPiSyntax KontroliBase arithmetic string relation list rich_list
Libs
  boolSimps numLib

(* Insert d new de Bruijn slots before a suffix.  The i-th suffix declaration
   was written with i earlier suffix declarations already in scope, so its
   cutoff is k+i. *)
Definition lift_ctx_from_def:
  (lift_ctx_from d k [] = []) /\
  (lift_ctx_from d k (A::H) =
    lift d k A :: lift_ctx_from d (SUC k) H)
End

Definition lift_ctx_def:
  lift_ctx d H = lift_ctx_from d 0 H
End

Theorem lift_ctx_from_length[simp]:
  !d k H. LENGTH (lift_ctx_from d k H) = LENGTH H
Proof
  rpt gen_tac >> Induct_on `H` >> simp[lift_ctx_from_def]
QED

Theorem lift_ctx_length[simp]:
  !d H. LENGTH (lift_ctx d H) = LENGTH H
Proof
  simp[lift_ctx_def]
QED

Theorem lift_ctx_from_el:
  !H d k i.
    i < LENGTH H ==>
    EL i (lift_ctx_from d k H) = lift d (k + i) (EL i H)
Proof
  Induct >>
  simp[lift_ctx_from_def] >>
  rpt gen_tac >>
  Cases_on `i` >>
  simp[ADD_CLAUSES, ADD_ASSOC]
QED

Theorem lift_ctx_from_snoc:
  !H d k A.
    lift_ctx_from d k (H ++ [A]) =
    lift_ctx_from d k H ++ [lift d (k + LENGTH H) A]
Proof
  Induct >>
  simp[lift_ctx_from_def, ADD_CLAUSES, ADD_ASSOC]
QED

Theorem lift_ctx_snoc:
  !H d A.
    lift_ctx d (H ++ [A]) =
    lift_ctx d H ++ [lift d (LENGTH H) A]
Proof
  simp[lift_ctx_def, lift_ctx_from_snoc]
QED

(* Insert one binder B between prefix G and suffix H.  Existing suffix
   declaration types are lifted at successively deeper cutoffs. *)
Definition insert_context_def:
  insert_context G B H = G ++ [B] ++ lift_ctx 1 H
End

Theorem insert_context_length[simp]:
  !G B H.
    LENGTH (insert_context G B H) = SUC (LENGTH G + LENGTH H)
Proof
  simp[insert_context_def]
QED

Theorem insert_context_empty_suffix[simp]:
  !G B. insert_context G B [] = G ++ [B]
Proof
  simp[insert_context_def, lift_ctx_def, lift_ctx_from_def]
QED

Theorem insert_context_snoc:
  !G B H A.
    insert_context G B (H ++ [A]) =
    insert_context G B H ++ [lift 1 (LENGTH H) A]
Proof
  simp[insert_context_def, lift_ctx_snoc, APPEND_ASSOC]
QED

(* Variable indices below the insertion point name suffix binders and stay
   unchanged; variables at/above it name the prefix and move by one. *)
Definition insert_index_def:
  insert_index h n = if n < h then n else SUC n
End

Theorem insert_index_bound:
  !g h n.
    n < g + h ==>
    insert_index h n < SUC (g + h)
Proof
  rw[insert_index_def] >>
  numLib.ARITH_TAC
QED

Theorem insert_index_below[simp]:
  !h n. n < h ==> insert_index h n = n
Proof
  simp[insert_index_def]
QED

Theorem insert_index_at_or_above[simp]:
  !h n. h <= n ==> insert_index h n = SUC n
Proof
  simp[insert_index_def] >> metis_tac[NOT_LESS]
QED

(* Prefix lifting commutes with a later lift whose cutoff is measured in the
   unprefixed term. *)
Theorem lift_prefix_commute:
  !t p d c.
    lift p 0 (lift d c t) =
    lift d (c + p) (lift p 0 t)
Proof
  Induct >>
  simp[ADD_ASSOC, ADD_COMM, ADD_LEFT_COMM]
  >- (rpt gen_tac >> Cases_on `n < c` >> simp[] >> numLib.ARITH_TAC)
QED

Theorem el_append_offset:
  !G H i.
    i < LENGTH H ==>
    EL (LENGTH G + i) (G ++ H) = EL i H
Proof
  simp[rich_listTheory.EL_APPEND2]
QED

(* A variable naming one of the newer suffix binders keeps its index when B is
   inserted below the suffix.  Its type receives one lift at the full suffix
   boundary. *)
Theorem ctx_type_insert_suffix:
  !G B H n A.
    n < LENGTH H /\
    ctx_type (G ++ H) n A ==>
    ctx_type (insert_context G B H) n (lift 1 (LENGTH H) A)
Proof
  rw[ctx_type_def, insert_context_def] >>
  conj_tac
  >- simp[] >>
  qpat_x_assum `A = _` SUBST1_TAC >>
  qabbrev_tac `i = LENGTH H - SUC n` >>
  `i < LENGTH H` by
    (qunabbrev_tac `i` >> numLib.ARITH_TAC) >>
  `LENGTH (G ++ H) - SUC n = LENGTH G + i` by
    (qunabbrev_tac `i` >> simp[] >> numLib.ARITH_TAC) >>
  `LENGTH (G ++ [B] ++ lift_ctx 1 H) - SUC n =
    LENGTH (G ++ [B]) + i` by
    (qunabbrev_tac `i` >> simp[] >> numLib.ARITH_TAC) >>
  asm_simp_tac bool_ss
    [el_append_offset, lift_ctx_def, lift_ctx_from_el,
     lift_prefix_commute] >>
  qunabbrev_tac `i` >>
  numLib.ARITH_TAC
QED

(* A variable naming the older prefix moves by one because the inserted binder
   is newer than that prefix but older than every suffix declaration. *)
Theorem ctx_type_insert_prefix:
  !G B H n A.
    LENGTH H <= n /\
    ctx_type (G ++ H) n A ==>
    ctx_type (insert_context G B H) (SUC n)
      (lift 1 (LENGTH H) A)
Proof
  rw[ctx_type_def, insert_context_def] >>
  conj_tac
  >- simp[] >>
  qpat_x_assum `A = _` SUBST1_TAC >>
  qabbrev_tac `m = n - LENGTH H` >>
  `m < LENGTH G` by
    (qunabbrev_tac `m` >> fs[] >> numLib.ARITH_TAC) >>
  `LENGTH (G ++ H) - SUC n = LENGTH G - SUC m` by
    (qunabbrev_tac `m` >> simp[] >> numLib.ARITH_TAC) >>
  `LENGTH (G ++ [B] ++ lift_ctx 1 H) - SUC (SUC n) =
    LENGTH G - SUC m` by
    (qunabbrev_tac `m` >> simp[] >> numLib.ARITH_TAC) >>
  `LENGTH G - SUC m < LENGTH G` by numLib.ARITH_TAC >>
  asm_simp_tac bool_ss
    [rich_listTheory.EL_APPEND1, lift_fusion] >>
  numLib.ARITH_TAC
QED

Theorem ctx_type_insert:
  !G B H n A.
    ctx_type (G ++ H) n A ==>
    ctx_type (insert_context G B H)
      (insert_index (LENGTH H) n)
      (lift 1 (LENGTH H) A)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `n < LENGTH H`
  >- metis_tac[ctx_type_insert_suffix, insert_index_below] >>
  `LENGTH H <= n` by metis_tac[NOT_LESS] >>
  metis_tac[ctx_type_insert_prefix, insert_index_at_or_above]
QED

val _ = export_theory();
