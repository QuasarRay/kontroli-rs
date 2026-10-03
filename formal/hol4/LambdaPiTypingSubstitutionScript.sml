Theory LambdaPiTypingSubstitution
Ancestors
  LambdaPiSubstLookup LambdaPiSubjectReduction
Libs
  boolSimps numLib

Theorem scoped_subst_identity:
  !t k u.
    scoped k t ==> subst u k t = t
Proof
  Induct >>
  simp[]
QED

Theorem signature_decl_subst_at_identity:
  !Sigma R c A u k.
    signature_wf Sigma R /\ Sigma c A ==>
    subst u k A = A
Proof
  rpt strip_tac >>
  `scoped 0 A` by metis_tac[signature_decl_scoped] >>
  `0 <= k` by numLib.ARITH_TAC >>
  `scoped k A` by metis_tac[scoped_mono] >>
  metis_tac[scoped_subst_identity]
QED

Theorem subst_sort_identity[simp]:
  !s u k.
    is_sort s ==> subst u k s = s
Proof
  rpt strip_tac >>
  fs[is_sort_def]
QED

(* Generalized typing substitution.  C is split at the eliminated binder into
   G ++ [A] ++ H.  The theorem is intentionally conditional on the two closure
   properties of the concrete rewrite relation used by the executable checker. *)
Theorem has_type_substitution:
  !Sigma R C t T.
    has_type Sigma R C t T ==>
    !G H A u.
      C = G ++ [A] ++ H /\
      signature_wf Sigma R /\
      rewrite_lift_closed R /\
      rewrite_substitution_closed R /\
      has_type Sigma R G u A ==>
      has_type Sigma R (subst_context G u H)
        (subst u (LENGTH H) t)
        (subst u (LENGTH H) T)
Proof
  ho_match_mp_tac has_type_ind >>
  rpt strip_tac >>
  fs[
    subst_context_snoc,
    subst_subst0,
    APPEND_ASSOC
  ] >>
  metis_tac[
    has_type_rules,
    variable_typing_substitution,
    signature_decl_subst_at_identity,
    convertible_subst_from_rewrite_closed,
    APPEND_ASSOC
  ]
QED

Theorem typing_substitution_from_closure:
  !Sigma R.
    signature_wf Sigma R /\
    rewrite_lift_closed R /\
    rewrite_substitution_closed R ==>
    typing_substitution Sigma R
Proof
  rw[typing_substitution_def] >>
  metis_tac[has_type_substitution]
QED

val _ = export_theory();
