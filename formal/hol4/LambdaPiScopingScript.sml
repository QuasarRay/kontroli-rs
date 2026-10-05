Theory LambdaPiScoping
Ancestors
  LambdaPiBinderAlgebra LambdaPiTyping LambdaPiReduction LambdaPiSyntax KontroliBase arithmetic string relation list rich_list
Libs
  boolSimps numLib

(* Syntactic well-scoping for de Bruijn terms. *)
Definition scoped_def[simp]:
  (scoped k TmKind <=> T) /\
  (scoped k TmType <=> T) /\
  (scoped k (TmConst c) <=> T) /\
  (scoped k (TmVar n) <=> n < k) /\
  (scoped k (TmApp f a) <=> scoped k f /\ scoped k a) /\
  (scoped k (TmLam A b) <=> scoped k A /\ scoped (SUC k) b) /\
  (scoped k (TmLamU b) <=> scoped (SUC k) b) /\
  (scoped k (TmPi A B) <=> scoped k A /\ scoped (SUC k) B)
End

Theorem scoped_mono:
  !t n m.
    scoped n t /\ n <= m ==> scoped m t
Proof
  Induct >> simp[] >> rpt strip_tac >> metis_tac[LESS_EQ_TRANS]
QED

(* A term accepted by the declarative typing rules cannot contain a dangling
   de Bruijn index.  This statement is intentionally about the term, not yet
   its inferred type. *)
Theorem has_type_term_scoped:
  !Sigma R G t A.
    has_type Sigma R G t A ==> scoped (LENGTH G) t
Proof
  ho_match_mp_tac has_type_ind >>
  simp[ctx_type_def] >>
  metis_tac[]
QED

Theorem scoped_lift_identity:
  !t k d.
    scoped k t ==> lift d k t = t
Proof
  Induct >> simp[]
QED

Theorem closed_lift_identity:
  !t d.
    scoped 0 t ==> lift d 0 t = t
Proof
  metis_tac[scoped_lift_identity]
QED

(* A well-formed signature assigns closed types to constants because each
   declaration type is itself typable in the empty context. *)
Theorem signature_decl_scoped:
  !Sigma R c A.
    signature_wf Sigma R /\ Sigma c A ==> scoped 0 A
Proof
  rw[signature_wf_def] >>
  first_x_assum drule >>
  strip_tac >>
  metis_tac[has_type_term_scoped, LENGTH]
QED

Theorem signature_decl_lift_identity:
  !Sigma R c A d.
    signature_wf Sigma R /\ Sigma c A ==> lift d 0 A = A
Proof
  metis_tac[signature_decl_scoped, closed_lift_identity]
QED

(* Appending h newer binders shifts an old reverse de Bruijn index by h and
   lifts its stored type by the same amount.  This is the exact arithmetic
   shape used by LCtx::get_type. *)
Theorem ctx_type_append_suffix:
  !G H n A.
    ctx_type G n A ==>
    ctx_type (G ++ H) (n + LENGTH H) (lift (LENGTH H) 0 A)
Proof
  rw[ctx_type_def] >>
  conj_tac
  >- simp[] >>
  qpat_x_assum `A = _` SUBST1_TAC >>
  `LENGTH (G ++ H) - SUC (n + LENGTH H) = LENGTH G - SUC n`
    by (simp[] >> numLib.ARITH_TAC) >>
  pop_assum SUBST1_TAC >>
  `LENGTH G - SUC n < LENGTH G` by numLib.ARITH_TAC >>
  simp[rich_listTheory.EL_APPEND1, lift_compose] >>
  numLib.ARITH_TAC
QED

Theorem ctx_type_append_one:
  !G B n A.
    ctx_type G n A ==>
    ctx_type (G ++ [B]) (SUC n) (lift 1 0 A)
Proof
  rpt strip_tac >>
  drule ctx_type_append_suffix >>
  simp[ADD1]
QED

val _ = export_theory();
