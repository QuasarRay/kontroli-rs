Theory LambdaPiMetatheory
Ancestors
  LambdaPiTyping LambdaPiReduction LambdaPiSyntax KontroliBase arithmetic string relation list
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
      convertible R (TmPi A1 B1) (TmPi A2 B2) ==>
      convertible R A1 A2 /\ convertible R B1 B2
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

Theorem pi_root_free_joinable_products:
  !R A1 B1 A2 B2.
    pi_root_free R /\
    joinable R (TmPi A1 B1) (TmPi A2 B2) ==>
    joinable R A1 A2 /\ joinable R B1 B2
Proof
  rw[joinable_def] >>
  drule_all reduces_pi_inv >>
  drule_all reduces_pi_inv >>
  metis_tac[]
QED

(* Root-freeness alone is not enough for EQC conversion: an inverse rewrite
   can enter a product from a non-product.  Confluence turns EQC conversion
   into common-reduct joinability, after which the structural inversion proof
   applies. *)
Theorem confluent_pi_root_free_product_compatible:
  !R. pi_root_free R /\ confluent R ==> product_compatible R
Proof
  rw[product_compatible_def] >>
  `joinable R (TmPi A1 B1) (TmPi A2 B2)` by
    metis_tac[convertible_implies_joinable_confluent] >>
  `joinable R A1 A2 /\ joinable R B1 B2` by
    metis_tac[pi_root_free_joinable_products] >>
  metis_tac[joinable_implies_convertible]
QED

Theorem confluent_conversion_and_product_compatibility:
  !R. pi_root_free R /\ confluent R ==>
    product_compatible R /\
    (!x y z. convertible R x y /\ convertible R y z ==> convertible R x z)
Proof
  metis_tac[confluent_pi_root_free_product_compatible, convertible_trans]
QED


(* Per-rule formulation of the rewrite-safety obligation used by the
   subject-reduction theorem.  This mirrors the standard metatheory:
   a rewrite rule must preserve every type it can have in the final theory. *)
Definition rule_well_typed_def:
  rule_well_typed Sigma R l r <=>
    !G A. has_type Sigma R G l A ==> has_type Sigma R G r A
End

Theorem rewrite_preserves_typing_iff_rules_well_typed:
  !Sigma R.
    rewrite_preserves_typing Sigma R <=>
    !l r. R l r ==> rule_well_typed Sigma R l r
Proof
  simp[rewrite_preserves_typing_def, rule_well_typed_def] >>
  metis_tac[]
QED

Definition relation_extends_def:
  relation_extends R R' <=> !t u. R t u ==> R' t u
End

(* Saillard's "permanently well-typed" condition: once a rule is accepted in
   a prefix theory, it remains well-typed in every product-compatible
   extension.  This is the property the executable rewrite-rule checker must
   ultimately refine for checked rules. *)
Definition permanently_well_typed_rule_def:
  permanently_well_typed_rule Sigma R l r <=>
    !R'.
      relation_extends R R' /\ product_compatible R' ==>
      rule_well_typed Sigma R' l r
End

Theorem permanent_rule_safe_in_extension:
  !Sigma R l r R'.
    permanently_well_typed_rule Sigma R l r /\
    relation_extends R R' /\
    product_compatible R' ==>
    rule_well_typed Sigma R' l r
Proof
  simp[permanently_well_typed_rule_def] >> metis_tac[]
QED

Theorem final_relation_safe_from_per_rule_obligation:
  !Sigma R.
    (!l r. R l r ==> rule_well_typed Sigma R l r) ==>
    rewrite_preserves_typing Sigma R
Proof
  metis_tac[rewrite_preserves_typing_iff_rules_well_typed]
QED

val _ = export_theory();
