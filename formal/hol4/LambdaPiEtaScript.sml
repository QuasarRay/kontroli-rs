Theory LambdaPiEta
Ancestors
  LambdaPiMetatheory LambdaPiTyping LambdaPiReduction LambdaPiSyntax KontroliBase arithmetic string relation list
Libs
  boolSimps

(* Declarative eta contraction.  The lifted occurrence ensures that the bound
   variable introduced by the lambda is not free in the contracted term. *)
Definition eta_expand_def:
  eta_expand t = TmLamU (TmApp (lift 1 0 t) (TmVar 0))
End

Inductive eta_red:
[~unannotated:]
  eta_red (TmLamU (TmApp (lift 1 0 f) (TmVar 0))) f
[~annotated:]
  eta_red (TmLam A (TmApp (lift 1 0 f) (TmVar 0))) f
[~app_fun:]
  eta_red f f' ==> eta_red (TmApp f a) (TmApp f' a)
[~app_arg:]
  eta_red a a' ==> eta_red (TmApp f a) (TmApp f a')
[~lam_type:]
  eta_red A A' ==> eta_red (TmLam A b) (TmLam A' b)
[~lam_body:]
  eta_red b b' ==> eta_red (TmLam A b) (TmLam A b')
[~lamU_body:]
  eta_red b b' ==> eta_red (TmLamU b) (TmLamU b')
[~pi_domain:]
  eta_red A A' ==> eta_red (TmPi A B) (TmPi A' B)
[~pi_codomain:]
  eta_red B B' ==> eta_red (TmPi A B) (TmPi A B')
End

(* Kontroli exposes eta as a runtime boolean.  Keeping it explicit prevents
   proofs for the default mode from silently claiming coverage of --eta. *)
Definition mode_red_def:
  mode_red eta R t u <=>
    red R t u \/ (eta /\ eta_red t u)
End


Definition mode_convertible_def:
  mode_convertible eta R t u <=>
    EQC (\x y. mode_red eta R x y) t u
End

Definition mode_reduces_def:
  mode_reduces eta R t u <=>
    RTC (\x y. mode_red eta R x y) t u
End

Definition mode_joinable_def:
  mode_joinable eta R t u <=>
    ?v. mode_reduces eta R t v /\ mode_reduces eta R u v
End

Theorem eta_expand_contracts:
  !t. eta_red (eta_expand t) t
Proof
  simp[eta_expand_def] >> metis_tac[eta_red_rules]
QED

Theorem mode_red_no_eta[simp]:
  !R t u. mode_red F R t u <=> red R t u
Proof
  simp[mode_red_def]
QED

Theorem mode_convertible_no_eta[simp]:
  !R t u. mode_convertible F R t u <=> convertible R t u
Proof
  simp[mode_convertible_def, convertible_def, mode_red_def]
QED

Theorem mode_reduces_no_eta[simp]:
  !R t u. mode_reduces F R t u <=> reduces R t u
Proof
  simp[mode_reduces_def, reduces_def, mode_red_def]
QED

Theorem mode_joinable_no_eta[simp]:
  !R t u. mode_joinable F R t u <=> joinable R t u
Proof
  simp[mode_joinable_def, joinable_def]
QED

Theorem default_mode_is_base_calculus:
  !R t u.
    mode_convertible F R t u <=> convertible R t u
Proof
  simp[]
QED

val _ = export_theory();
