Theory KontroliSurface
Ancestors
  LambdaPiTyping

(* Surface terms model the user/kernel LTerm shape. Kind is internal to STerm,
   so it is intentionally absent here. Lambda annotations are optional exactly
   as in Comb::Abst(_, Option<Tm>, _). *)
Datatype:
  surface_term =
    STmType
  | STmConst string
  | STmVar num
  | STmApp surface_term surface_term
  | STmLam (surface_term option) surface_term
  | STmPi surface_term surface_term
End

(* Elaboration forgets the surface-only optionality. An unannotated lambda may
   elaborate with any core domain; the expected Pi type supplied by checking
   will determine which such elaboration is typable. *)
Inductive elaborates:
[~type:]
  elaborates STmType TmType
[~const:]
  elaborates (STmConst c) (TmConst c)
[~var:]
  elaborates (STmVar n) (TmVar n)
[~app:]
  elaborates f f' /\ elaborates a a' ==>
  elaborates (STmApp f a) (TmApp f' a')
[~lam_annotated:]
  elaborates A A' /\ elaborates b b' ==>
  elaborates (STmLam (SOME A) b) (TmLam A' b')
[~lam_unannotated:]
  elaborates b b' ==>
  elaborates (STmLam NONE b) (TmLam A b')
[~pi:]
  elaborates A A' /\ elaborates B B' ==>
  elaborates (STmPi A B) (TmPi A' B')
End

Theorem annotated_lambda_elaborates:
  !A A' b b'.
    elaborates A A' /\ elaborates b b' ==>
    elaborates (STmLam (SOME A) b) (TmLam A' b')
Proof
  metis_tac[elaborates_rules]
QED

Theorem unannotated_lambda_elaborates_with_expected_domain:
  !A b b'.
    elaborates b b' ==>
    elaborates (STmLam NONE b) (TmLam A b')
Proof
  metis_tac[elaborates_rules]
QED

val _ = export_theory();
