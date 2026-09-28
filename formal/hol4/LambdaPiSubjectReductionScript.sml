Theory LambdaPiSubjectReduction
Ancestors
  LambdaPiSubstitution LambdaPiMetatheory
Libs
  boolSimps

Definition subject_reduction_def:
  subject_reduction Sigma R <=>
    !G t u A.
      wf_context Sigma R G /\
      has_type Sigma R G t A /\
      red R t u ==>
      has_type Sigma R G u A
End

(* Generalized substitution across an arbitrary suffix H.  The eliminated
   binder has de Bruijn index LENGTH H; subst_context removes it while
   substituting through every stored suffix type. *)
Definition typing_substitution_def:
  typing_substitution Sigma R <=>
    !G H A u t T.
      wf_context Sigma R G /\
      has_type Sigma R G A TmType /\
      has_type Sigma R G u A /\
      wf_context Sigma R (G ++ [A] ++ H) /\
      has_type Sigma R (G ++ [A] ++ H) t T ==>
      has_type Sigma R (subst_context G u H)
        (subst u (LENGTH H) t)
        (subst u (LENGTH H) T)
End

Theorem user_rewrite_subject_reduction:
  !Sigma R G t u A.
    rewrite_preserves_typing Sigma R /\
    R t u /\
    has_type Sigma R G t A ==>
    has_type Sigma R G u A
Proof
  metis_tac[user_rewrite_preserves_type_when_certified]
QED

Theorem wf_context_extend:
  !Sigma R G A.
    wf_context Sigma R G /\
    has_type Sigma R G A TmType ==>
    wf_context Sigma R (G ++ [A])
Proof
  metis_tac[wf_context_rules]
QED

(* This is the central beta case once generalized substitution has been
   established independently. *)
Theorem beta_body_preserves_type_from_substitution:
  !Sigma R G A u b B.
    typing_substitution Sigma R /\
    wf_context Sigma R G /\
    has_type Sigma R G A TmType /\
    has_type Sigma R G u A /\
    has_type Sigma R (G ++ [A]) b B ==>
    has_type Sigma R G (subst0 u b) (subst0 u B)
Proof
  rw[typing_substitution_def] >>
  first_x_assum
    (qspec_then `G`
      (qspec_then `[]`
        (qspec_then `A`
          (qspec_then `u`
            (qspec_then `b`
              (qspec_then `B` mp_tac)))))) >>
  simp[subst0_def, wf_context_extend]
QED

(* The remaining proof of subject_reduction consists of:
   1. proving typing_substitution;
   2. context conversion under convertible binder types;
   3. typing inversion/generation under product_compatible;
   4. induction over the red derivation using those lemmas.
   These are deliberately separate HOL theorems, not trusted assumptions. *)

val _ = export_theory();
