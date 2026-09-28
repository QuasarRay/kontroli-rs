# Kontroli implementation-refinement contract

This layer is the boundary between the machine-checked λΠ-calculus-modulo
metatheory and the Rust implementation.

It deliberately does **not** assert that the Rust kernel already satisfies the
contract. Aeneas-generated HOL4 definitions must discharge each executable
obligation.

## Contract obligations

| Rust implementation | HOL4 obligation | Status |
|---|---|---|
| `STerm::infer` / `SComb::infer` | `infer_refines` | pending Aeneas refinement |
| `STerm::check` | `check_refines` | pending Aeneas refinement |
| `STerm::convertible` + `convertible::{step,step1,step2}` | `conversion_refines` | pending |
| `STerm::whnf` / abstract machine | `whnf_refines` | pending; external models may be needed |
| `kernel::rewrite` + checked rule admission | `rule_admission_refines` | pending executable correspondence |
| admitted rules ↔ formal relation `R` | `admission_generates` | pending |
| `kernel/subst.rs` | lift/substitution closure + function correspondence | sliced Aeneas checkpoint |
| normal CLI mode | `verified_execution_mode` | requires `eta=false`, checking enabled |

## Explicit environment premise

The executable checker validates rule typing but does not establish
confluence/product compatibility for arbitrary user rewrite systems.
Consequently `product_compatible R` remains an explicit contract premise.

A theory can discharge it independently, for example through a verified
confluence/product-compatibility certificate. It must not be inferred merely
from successful parsing or rule typechecking.

## Composition theorem

Once Aeneas-extracted executable functions satisfy the contract,
`kernel_contract_implies_subject_reduction` composes implementation refinement
with the declarative HOL4 metatheory.

`accepted_check_has_declarative_type` connects executable checking to the
declarative typing judgment. `accepted_check_preserved_by_one_step_reduction`
then combines executable acceptance with subject reduction.

The trusted acceptance boundary remains direct HOL4 kernel replay. Aegis,
hol4-mcp, TacticToe, Aeneas, SMT, and proof agents are orchestration or
translation tools; none may turn an unproved refinement obligation into a
theorem.
