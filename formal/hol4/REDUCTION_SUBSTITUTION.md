# Reduction closure under substitution

This layer proves the de Bruijn composition law required to substitute through
beta reduction.

The dependency chain is:

`rewrite_substitution_closed R`
→ `red_substitution_closed R`
→ substitution preserves `convertible R`.

The beta cases are discharged by `subst_subst0`; compatible-constructor cases
follow by the inductive hypotheses.  No confluence assumption is used.

The remaining implementation obligation is to show that the relation generated
by accepted Kontroli rewrite rules is substitution-closed.  That proof belongs
to the rule-instantiation/matcher refinement layer.
