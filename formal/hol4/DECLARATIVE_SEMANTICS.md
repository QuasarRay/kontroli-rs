# Declarative semantic migration

This checkpoint removes the accidental confluence assumption from the typing
specification.

- Typing conversion now uses `convertible R = EQC (red R)`.
- Product compatibility is stated over `convertible`, as in the λΠ-modulo
  metatheory.
- The old root-free Π inversion result is retained only for `joinable`.
- HOL4 derives product compatibility from root-freeness **and confluence** by
  using the proved equivalence between declarative conversion and common-reduct
  joinability under confluence.
- Optional eta mode now exposes `mode_convertible`; the default
  `eta = false` theorem reduces exactly to base `convertible`.

This separation is required before subject reduction: subject reduction should
depend on product compatibility and rewrite-rule well-typedness, not on an
unadvertised global confluence assumption.
