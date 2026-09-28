Theory LambdaPiContextInsertion
Ancestors
  LambdaPiScoping
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

val _ = export_theory();
