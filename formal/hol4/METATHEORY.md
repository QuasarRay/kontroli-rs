# Product compatibility checkpoint

The published λΠ-calculus-modulo metatheory uses two central conditions for
subject reduction:

1. product compatibility (Π-injectivity), and
2. well-typed rewrite rules.

This theory discharges the first condition for the structural rewrite fragment
implemented by Kontroli. The executable checker only accepts rewrite patterns
headed by a symbol; therefore a user rewrite does not rewrite a `TmPi`
constructor at its root. `pi_root_free` states that fact independently of the
Rust representation.

`pi_root_free_product_compatible` then proves that if two Π-types have a
common β+rewrite reduct, their respective domains and codomains also have common
reducts.

This is not yet the whole subject-reduction theorem. The next metatheory layer
must prove typing substitution and show that every rewrite rule admitted by
Kontroli satisfies the explicit `rewrite_preserves_typing` obligation.
