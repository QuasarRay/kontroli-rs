# Aeneas → HOL4 extraction qualification

This directory records the implementation-refinement boundary.

The declarative HOL4 theories under `formal/hol4` are the specification side.
Aeneas/Charon is used to translate the actual safe Rust implementation into HOL4
functions. Translation success alone is **not** a correctness theorem: the
generated functions still need correspondence proofs against
`LambdaPiTypingTheory`, `LambdaPiReductionTheory`, and the metatheory built on
top of them.

The pinned Aeneas release is stored in `formal/hol4/toolchain.json`.
`scripts/qualify_aeneas_hol4.sh`:

1. downloads and hashes the pinned Aeneas/Charon release;
2. extracts the `kontroli` library with Charon's `aeneas` preset;
3. asks Aeneas to emit the HOL4 backend;
4. records all diagnostics under `.aegis/aeneas`.

A failed qualification is intentionally useful evidence. In particular, the
WHNF evaluator uses `Rc<RefCell<_>>` and `lazy_st::Thunk`. If those external
types/functions are not modeled by Aeneas, the failure identifies the exact
model/adaptation boundary rather than silently replacing the Rust code by a
hand-written function.

The first implementation proofs should target the smallest directly translated
pieces (`subst.rs`, term constructors, and local-context/index logic) before the
lazy WHNF engine.
