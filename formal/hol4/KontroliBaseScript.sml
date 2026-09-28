open HolKernel boolLib bossLib;

val _ = new_theory "KontroliBase";

Datatype:
  ksort = KType | KKind
End

Theorem KType_neq_KKind:
  KType <> KKind
Proof
  simp[]
QED

Theorem ksort_cases:
  !s. s = KType \/ s = KKind
Proof
  Cases >> simp[]
QED

val _ = export_theory();
