Theory LambdaPiMetatheory
Ancestors
  LambdaPiTyping
Libs
  boolSimps

(* Kontroli's accepted rewrite rules are headed by constants. Hence a user
   rewrite never rewrites a product constructor at the root. This predicate
   isolates exactly the structural fact used below. *)
Definition pi_root_free_def:
  pi_root_free R <=>
    !A B u. ~R (TmPi A B) u
End

(* Product compatibility / Pi-injectivity for the declarative conversion. *)
Definition product_compatible_def:
  product_compatible R <=>
    !A1 B1 A2 B2.
      joinable R (TmPi A1 B1) (TmPi A2 B2) ==>
      joinable R A1 A2 /\ joinable R B1 B2
End

Theorem red_pi_inv:
  !R A B t.
    pi_root_free R /\ red R (TmPi A B) t ==>
    (?A'. t = TmPi A' B /\ red R A A') \/
    (?B'. t = TmPi A B' /\ red R B B')
Proof
  rw[Once red_cases] >>
  fs[pi_root_free_def] >>
  metis_tac[]
QED

(* A multi-step reduction starting at a product stays a product, with the
   domain and codomain reducing independently. *)
Theorem rtc_red_pi_inv:
  !R. pi_root_free R ==>
    !x y. RTC (red R) x y ==>
      !A B. x = TmPi A B ==>
        ?A' B'.
          y = TmPi A' B' /\
          RTC (red R) A A' /\
          RTC (red R) B B'
Proof
  gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      rpt gen_tac >> strip_tac >>
      metis_tac[red_pi_inv, RTC_RULES_RIGHT1])
QED

Theorem reduces_pi_inv:
  !R A B t.
    pi_root_free R /\ reduces R (TmPi A B) t ==>
    ?A' B'.
      t = TmPi A' B' /\
      reduces R A A' /\
      reduces R B B'
Proof
  rw[reduces_def] >>
  metis_tac[rtc_red_pi_inv]
QED

Theorem pi_root_free_product_compatible:
  !R. pi_root_free R ==> product_compatible R
Proof
  rw[product_compatible_def, joinable_def] >>
  drule_all reduces_pi_inv >>
  drule_all reduces_pi_inv >>
  metis_tac[]
QED

(* With confluence, the already-proved transitivity of joinability and
   Pi-injectivity give the conversion properties used by the typing
   metatheory.  Confluence is not hidden in product compatibility itself. *)
Theorem confluent_conversion_and_product_compatibility:
  !R. pi_root_free R /\ confluent R ==>
    product_compatible R /\
    (!x y z. joinable R x y /\ joinable R y z ==> joinable R x z)
Proof
  metis_tac[pi_root_free_product_compatible, joinable_trans_confluent]
QED

val _ = export_theory();
