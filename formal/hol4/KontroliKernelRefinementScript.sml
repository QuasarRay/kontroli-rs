Theory KontroliKernelRefinement
Ancestors
  LambdaPiSubjectReductionFinal
Libs
  boolSimps

Definition infer_refines_def:
  infer_refines Sigma R infer <=>
    !G t A.
      wf_context Sigma R G /\
      infer G t = SOME A ==>
      has_type Sigma R G t A
End

Definition check_refines_def:
  check_refines Sigma R check <=>
    !G t A.
      wf_context Sigma R G /\
      check G t A ==>
      has_type Sigma R G t A
End

Definition conversion_refines_def:
  conversion_refines R conv <=>
    !t u. conv t u ==> convertible R t u
End

Definition whnf_refines_def:
  whnf_refines R whnf <=>
    !t. convertible R t (whnf t)
End

Definition rule_admission_refines_def:
  rule_admission_refines Sigma R admitted <=>
    !l r. admitted l r ==> rule_well_typed Sigma R l r
End

Definition admission_generates_def:
  admission_generates R admitted <=>
    !l r. R l r <=> admitted l r
End

Definition verified_execution_mode_def:
  verified_execution_mode eta check_enabled <=>
    ~eta /\ check_enabled
End

Definition kernel_refinement_contract_def:
  kernel_refinement_contract
    Sigma R infer check conv whnf admitted eta check_enabled <=>
      signature_wf Sigma R /\
      rewrite_lift_closed R /\
      rewrite_substitution_closed R /\
      product_compatible R /\
      infer_refines Sigma R infer /\
      check_refines Sigma R check /\
      conversion_refines R conv /\
      whnf_refines R whnf /\
      rule_admission_refines Sigma R admitted /\
      admission_generates R admitted /\
      verified_execution_mode eta check_enabled
End

Theorem admitted_relation_preserves_typing:
  !Sigma R admitted.
    rule_admission_refines Sigma R admitted /\
    admission_generates R admitted ==>
    rewrite_preserves_typing Sigma R
Proof
  rw[
    rule_admission_refines_def,
    admission_generates_def,
    rewrite_preserves_typing_iff_rules_well_typed
  ] >>
  metis_tac[]
QED

Theorem kernel_contract_implies_subject_reduction:
  !Sigma R infer check conv whnf admitted eta check_enabled.
    kernel_refinement_contract
      Sigma R infer check conv whnf admitted eta check_enabled ==>
    subject_reduction Sigma R
Proof
  rw[kernel_refinement_contract_def] >>
  `rewrite_preserves_typing Sigma R` by
    metis_tac[admitted_relation_preserves_typing] >>
  metis_tac[subject_reduction_from_metatheory]
QED

Theorem accepted_check_has_declarative_type:
  !Sigma R infer check conv whnf admitted eta check_enabled G t A.
    kernel_refinement_contract
      Sigma R infer check conv whnf admitted eta check_enabled /\
    wf_context Sigma R G /\
    check G t A ==>
    has_type Sigma R G t A
Proof
  simp[kernel_refinement_contract_def, check_refines_def] >>
  metis_tac[]
QED

Theorem accepted_check_preserved_by_one_step_reduction:
  !Sigma R infer check conv whnf admitted eta check_enabled G t u A.
    kernel_refinement_contract
      Sigma R infer check conv whnf admitted eta check_enabled /\
    wf_context Sigma R G /\
    check G t A /\
    red R t u ==>
    has_type Sigma R G u A
Proof
  rpt strip_tac >>
  `has_type Sigma R G t A` by
    metis_tac[accepted_check_has_declarative_type] >>
  `subject_reduction Sigma R` by
    metis_tac[kernel_contract_implies_subject_reduction] >>
  fs[subject_reduction_def] >>
  metis_tac[]
QED

val _ = export_theory();
