# Eta-mode semantics

Kontroli's `GCtx::eta` is false by default and is enabled by the CLI
`--eta` option. The executable convertibility checker eta-expands the
non-lambda side while comparing a lambda with a non-lambda.

This checkpoint keeps eta separate from the base λΠ-modulo metatheory:

- `red R` remains beta + user rewriting and compatible closure.
- `eta_red` is a declarative eta-contraction relation, closed under term
  constructors.
- `mode_red eta R`, `mode_reduces`, and `mode_joinable` expose the runtime
  mode as an explicit semantic parameter.
- HOL4 proves that `eta = false` collapses exactly to the existing base
  calculus.

The `eta = true` implementation-refinement theorem is intentionally separate:
it must show that Kontroli's recursive eta-expansion comparison is equivalent
to the declarative eta semantics on well-typed terms. No proof for the default
mode is allowed to silently claim that stronger result.
