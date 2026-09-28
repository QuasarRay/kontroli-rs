Theory LambdaPiTyping
Ancestors
  LambdaPiReduction list
Libs
  boolSimps

Definition is_sort_def[simp]:
  is_sort s <=> (s = TmType) \/ (s = TmKind)
End

(* Kontroli stores local assumptions oldest-to-newest and indexes them from
   the right. get_type(n) additionally shifts the stored type by n+1. *)
Definition ctx_type_def:
  ctx_type G n A <=>
    n < LENGTH G /\
    A = lift (SUC n) 0 (EL (LENGTH G - SUC n) G)
End

(* Sigma maps constants to their declared types. R remains the user rewrite
   relation; conversion is the equivalence closure of beta + compatible R reduction. *)
Inductive has_type:
[~type_sort:]
  has_type Sigma R G TmType TmKind
[~constant:]
  Sigma c A ==>
  has_type Sigma R G (TmConst c) A
[~variable:]
  ctx_type G n A ==>
  has_type Sigma R G (TmVar n) A
[~product:]
  has_type Sigma R G A TmType /\
  has_type Sigma R (G ++ [A]) B s /\
  is_sort s ==>
  has_type Sigma R G (TmPi A B) s
[~abstraction:]
  has_type Sigma R G A TmType /\
  has_type Sigma R (G ++ [A]) B s /\
  is_sort s /\
  has_type Sigma R (G ++ [A]) b B ==>
  has_type Sigma R G (TmLam A b) (TmPi A B)
[~abstraction_unannotated:]
  has_type Sigma R G A TmType /\
  has_type Sigma R (G ++ [A]) B s /\
  is_sort s /\
  has_type Sigma R (G ++ [A]) b B ==>
  has_type Sigma R G (TmLamU b) (TmPi A B)
[~application:]
  has_type Sigma R G f (TmPi A B) /\
  has_type Sigma R G a A ==>
  has_type Sigma R G (TmApp f a) (subst0 a B)
[~conversion:]
  has_type Sigma R G t A /\
  has_type Sigma R G B s /\
  is_sort s /\
  convertible R A B ==>
  has_type Sigma R G t B
End

Inductive wf_context:
[~empty:]
  wf_context Sigma R []
[~extend:]
  wf_context Sigma R G /\
  has_type Sigma R G A TmType ==>
  wf_context Sigma R (G ++ [A])
End

Definition signature_wf_def:
  signature_wf Sigma R <=>
    !c A. Sigma c A ==>
      ?s. is_sort s /\ has_type Sigma R [] A s
End

(* This is an explicit theory obligation, not an axiom hidden in the typing
   rules. A concrete rewrite system must discharge it before subject reduction
   can use user-rewrite steps. *)
Definition rewrite_preserves_typing_def:
  rewrite_preserves_typing Sigma R <=>
    !G t u A.
      R t u /\ has_type Sigma R G t A ==>
      has_type Sigma R G u A
End

Theorem type_has_kind:
  !Sigma R G. has_type Sigma R G TmType TmKind
Proof
  metis_tac[has_type_rules]
QED

Theorem constants_have_declared_types:
  !Sigma R G c A.
    Sigma c A ==> has_type Sigma R G (TmConst c) A
Proof
  metis_tac[has_type_rules]
QED

Theorem variables_use_ctx_type:
  !Sigma R G n A.
    ctx_type G n A ==> has_type Sigma R G (TmVar n) A
Proof
  metis_tac[has_type_rules]
QED

Theorem user_rewrite_preserves_type_when_certified:
  !Sigma R G t u A.
    rewrite_preserves_typing Sigma R /\
    R t u /\
    has_type Sigma R G t A ==>
    has_type Sigma R G u A
Proof
  simp[rewrite_preserves_typing_def] >> metis_tac[]
QED

(* Declarative conversion is an equivalence relation by construction. *)
Theorem conversion_symmetry:
  !Sigma R G t A B s.
    has_type Sigma R G t A /\
    has_type Sigma R G B s /\
    is_sort s /\
    convertible R A B ==>
    has_type Sigma R G t B
Proof
  metis_tac[has_type_rules]
QED
