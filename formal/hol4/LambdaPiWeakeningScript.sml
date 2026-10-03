Theory LambdaPiWeakening
Ancestors
  LambdaPiContextInsertion
Libs
  boolSimps numLib

(* Lifting commutes with beta substitution when the beta binder is accounted
   for by incrementing the cutoff in the body. *)
Theorem lift_subst0_commute:
  !t a d c.
    lift d c (subst0 a t) =
    subst0 (lift d c a) (lift d (SUC c) t)
Proof
  Induct >>
  simp[subst0_def] >>
  rpt gen_tac >>
  Cases_on `n` >>
  simp[] >>
  Cases_on `n' < c` >>
  simp[] >>
  numLib.ARITH_TAC
QED

Definition rewrite_lift_closed_def:
  rewrite_lift_closed R <=>
    !t v d c.
      R t v ==> R (lift d c t) (lift d c v)
End

Definition red_lift_closed_def:
  red_lift_closed R <=>
    !t v d c.
      red R t v ==> red R (lift d c t) (lift d c v)
End

Theorem red_lift_from_rewrite_closed:
  !R t v.
    rewrite_lift_closed R /\ red R t v ==>
    !d c. red R (lift d c t) (lift d c v)
Proof
  ho_match_mp_tac red_ind >>
  rw[rewrite_lift_closed_def] >>
  simp[lift_subst0_commute] >>
  metis_tac[red_rules]
QED

Theorem rewrite_lift_closed_implies_red:
  !R. rewrite_lift_closed R ==> red_lift_closed R
Proof
  simp[red_lift_closed_def] >>
  metis_tac[red_lift_from_rewrite_closed]
QED

Theorem convertible_lift_closed:
  !R.
    red_lift_closed R ==>
    !t v. convertible R t v ==>
      !d c. convertible R (lift d c t) (lift d c v)
Proof
  rw[red_lift_closed_def, convertible_def] >>
  ho_match_mp_tac EQC_INDUCTION >>
  metis_tac[EQC_R, EQC_REFL, EQC_SYM, EQC_TRANS]
QED

Theorem convertible_lift_from_rewrite_closed:
  !R t v d c.
    rewrite_lift_closed R /\ convertible R t v ==>
    convertible R (lift d c t) (lift d c v)
Proof
  metis_tac[rewrite_lift_closed_implies_red, convertible_lift_closed]
QED


Theorem signature_decl_lift_at_identity:
  !Sigma R c A d k.
    signature_wf Sigma R /\ Sigma c A ==>
    lift d k A = A
Proof
  rpt strip_tac >>
  `scoped 0 A` by metis_tac[signature_decl_scoped] >>
  `0 <= k` by numLib.ARITH_TAC >>
  `scoped k A` by metis_tac[scoped_mono] >>
  metis_tac[scoped_lift_identity]
QED

Theorem lift_var_insert_index[simp]:
  !h n.
    lift 1 h (TmVar n) = TmVar (insert_index h n)
Proof
  rpt gen_tac >>
  Cases_on `n < h` >>
  simp[insert_index_def, ADD1]
QED

Theorem lift_sort_identity[simp]:
  !s d c.
    is_sort s ==> lift d c s = s
Proof
  rpt strip_tac >>
  fs[is_sort_def]
QED

(* Raw declarative weakening: insert one binder between a prefix G and suffix H.
   The inserted declaration need not itself be used by the old derivation; the
   well-formed-context layer will separately require that B is a valid type. *)
Theorem has_type_insert:
  !Sigma R C t A.
    has_type Sigma R C t A ==>
    !G B H.
      C = G ++ H /\
      signature_wf Sigma R /\
      rewrite_lift_closed R ==>
      has_type Sigma R (insert_context G B H)
        (lift 1 (LENGTH H) t)
        (lift 1 (LENGTH H) A)
Proof
  ho_match_mp_tac has_type_ind >>
  rpt strip_tac >>
  fs[insert_context_snoc, lift_subst0_commute, APPEND_ASSOC] >>
  metis_tac[
    has_type_rules,
    ctx_type_insert,
    signature_decl_lift_at_identity,
    convertible_lift_from_rewrite_closed,
    APPEND_ASSOC
  ]
QED

Theorem declarative_weakening:
  !Sigma R G H B t A.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    has_type Sigma R (G ++ H) t A ==>
    has_type Sigma R (insert_context G B H)
      (lift 1 (LENGTH H) t)
      (lift 1 (LENGTH H) A)
Proof
  metis_tac[has_type_insert]
QED


Theorem wf_context_snoc_inv:
  !Sigma R G A.
    wf_context Sigma R (G ++ [A]) ==>
    wf_context Sigma R G /\
    has_type Sigma R G A TmType
Proof
  rpt gen_tac >>
  rw[Once wf_context_cases] >>
  fs[GSYM SNOC_APPEND, SNOC_11]
QED

Theorem wf_context_prefix:
  !Sigma R G H.
    wf_context Sigma R (G ++ H) ==>
    wf_context Sigma R G
Proof
  rpt gen_tac >>
  Induct_on `H` using SNOC_INDUCT
  >- simp[]
  >- (rpt strip_tac >>
      fs[SNOC_APPEND, APPEND_ASSOC] >>
      metis_tac[wf_context_snoc_inv])
QED

Theorem wf_context_insert:
  !Sigma R G H B.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    wf_context Sigma R (G ++ H) /\
    has_type Sigma R G B TmType ==>
    wf_context Sigma R (insert_context G B H)
Proof
  rpt gen_tac >>
  Induct_on `H` using SNOC_INDUCT
  >- (simp[insert_context_empty_suffix] >>
      metis_tac[wf_context_rules])
  >- (rpt strip_tac >>
      fs[SNOC_APPEND, APPEND_ASSOC, insert_context_snoc] >>
      metis_tac[
        wf_context_snoc_inv,
        declarative_weakening,
        wf_context_rules
      ])
QED


Theorem has_type_append_suffix:
  !Sigma R G H t A.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    has_type Sigma R G t A ==>
    has_type Sigma R (G ++ H)
      (lift (LENGTH H) 0 t)
      (lift (LENGTH H) 0 A)
Proof
  rpt gen_tac >>
  Induct_on `H` using SNOC_INDUCT
  >- simp[]
  >- (rpt strip_tac >>
      fs[SNOC_APPEND, APPEND_ASSOC, lift_compose, ADD1] >>
      metis_tac[has_type_insert])
QED

val _ = export_theory();
