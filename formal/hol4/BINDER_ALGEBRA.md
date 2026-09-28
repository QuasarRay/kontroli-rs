# Binder/context algebra checkpoint

This layer proves the de Bruijn identities needed before attempting the
typing-substitution lemma:

- same-cutoff lifting composes additively;
- substitution cancels a one-step lift at the same cutoff;
- in particular, `subst0 u (lift 1 0 t) = t`;
- reverse-index local-context lookup agrees with Kontroli's
  `LCtx::get_type` for the newest binder and is functional/in-bounds.

The next layer generalizes context substitution under nested binders.  User
rewrite steps additionally require the explicit
`rewrite_substitution_closed` obligation; it is not assumed by these
theorems.
