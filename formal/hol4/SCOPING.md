# Scoping and context algebra

This checkpoint isolates the structural facts needed before weakening and
generalized typing substitution:

- a declaratively typed term is well-scoped at the length of its local context;
- lifting at the boundary of a well-scoped term is an identity;
- signature declaration types are closed when the signature is well-formed;
- appending newer binders shifts an old reverse de Bruijn index and its type in
  the same way as Kontroli's `LCtx::get_type`.

The next layer can use these facts to state weakening as insertion into a
context prefix/suffix split, rather than the unsoundly simpler "append one
binder everywhere" formulation.
