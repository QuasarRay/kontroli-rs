# Declarative typing correspondence

The HOL4 relation `has_type Sigma R G t A` is the specification target for
`kontroli/src/kernel/infer_check.rs`.

| Rust behavior | HOL4 rule/definition |
|---|---|
| `Type -> Kind` | `type_sort` |
| constant lookup in `GCtx` | `constant` / `Sigma` |
| reverse de Bruijn lookup + `shift(n+1)` | `ctx_type` / `variable` |
| product domain must have type `Type` | `product` first premise |
| product codomain has sort Type or Kind | `product` second/third premise |
| annotated abstraction | `abstraction` |
| dependent application + codomain substitution | `application` |
| WHNF/convertibility fallback | `conversion` using `joinable` |

The specification intentionally does not declare arbitrary user rewrite rules
type preserving. `rewrite_preserves_typing Sigma R` is an explicit obligation.
The implementation's rule-introduction path must eventually be proved to
establish this obligation for every accepted rule.

This file is a correspondence index, not a proof.
