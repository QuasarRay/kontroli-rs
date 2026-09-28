Theory LambdaPiGeneration
Ancestors
  LambdaPiContextConversion
Libs
  boolSimps

Theorem application_generation:
  !Sigma R G t T.
    has_type Sigma R G t T ==>
    !f a.
      t = TmApp f a ==>
      ?A B.
        has_type Sigma R G f (TmPi A B) /\
        has_type Sigma R G a A /\
        convertible R (subst0 a B) T
Proof
  ho_match_mp_tac has_type_ind >>
  simp[] >>
  metis_tac[convertible_refl, convertible_trans]
QED

Theorem lambda_generation:
  !Sigma R G t T.
    has_type Sigma R G t T ==>
    !A b.
      t = TmLam A b ==>
      ?B s.
        is_sort s /\
        has_type Sigma R G A TmType /\
        has_type Sigma R (G ++ [A]) B s /\
        has_type Sigma R (G ++ [A]) b B /\
        convertible R (TmPi A B) T
Proof
  ho_match_mp_tac has_type_ind >>
  simp[] >>
  metis_tac[convertible_refl, convertible_trans]
QED

Theorem lambda_unannotated_generation:
  !Sigma R G t T.
    has_type Sigma R G t T ==>
    !b.
      t = TmLamU b ==>
      ?A B s.
        is_sort s /\
        has_type Sigma R G A TmType /\
        has_type Sigma R (G ++ [A]) B s /\
        has_type Sigma R (G ++ [A]) b B /\
        convertible R (TmPi A B) T
Proof
  ho_match_mp_tac has_type_ind >>
  simp[] >>
  metis_tac[convertible_refl, convertible_trans]
QED

Theorem product_generation:
  !Sigma R G t T.
    has_type Sigma R G t T ==>
    !A B.
      t = TmPi A B ==>
      ?s.
        is_sort s /\
        has_type Sigma R G A TmType /\
        has_type Sigma R (G ++ [A]) B s /\
        convertible R s T
Proof
  ho_match_mp_tac has_type_ind >>
  simp[] >>
  metis_tac[convertible_refl, convertible_trans]
QED

val _ = export_theory();
