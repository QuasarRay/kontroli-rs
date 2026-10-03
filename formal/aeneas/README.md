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


## Generated HOL4 interface manifest

Each successful extraction scope now emits `symbols.json` beside the generated
HOL4 files. The manifest records:

- generated `new_theory` names;
- `*_def` definition identifiers;
- opaque/external constants declared by the backend;
- the subset of definitions whose names contain `_fwd`.

The manifest is deterministic and is discovery metadata only. It is used by
later refinement proofs to bind theorem scripts to the exact Aeneas output
instead of guessing Rust-to-HOL4 names. It is **not** itself verification
evidence.
