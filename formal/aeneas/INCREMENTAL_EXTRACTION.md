# Incremental Aeneas extraction

Aeneas/Charon qualification now emits two independent evidence scopes:

1. **full** — the entire `kontroli` crate;
2. **subst-slice** — the call graph rooted at `crate::kernel::subst`.

Both use an explicit `--dest-file` and separate HOL4 output directories.
The substitution slice is the required checkpoint for this PR so that
refinement can begin on de Bruijn shift/substitution even if the lazy WHNF
engine or third-party containers prevent whole-crate translation.

This is not a relaxation of the final claim. Before a whole-kernel refinement
theorem is accepted, the full extraction must either succeed or every opaque
boundary must have an explicit HOL4 contract proved against the Rust-facing
API. Opaque/excluded code is never silently treated as verified.
