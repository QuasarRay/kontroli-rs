# Declarative conversion

The λΠ-calculus modulo conversion judgment is represented by

```
convertible R t u <=> EQC (red R) t u
```

where `red R` is the compatible one-step closure of beta reduction and the
user rewrite relation. This is the equivalence closure required by the
declarative calculus and does **not** assume confluence.

`joinable R t u` remains in the development because Kontroli's executable
convertibility procedure reduces terms to weak-head form and searches for a
common reduct structurally. HOL4 proves the unconditional direction

```
joinable R t u ==> convertible R t u
```

The converse is a Church–Rosser/confluence result and must only be used under
the corresponding rewrite-system hypothesis.

Later typing and product-compatibility theories must use `convertible`, not
`joinable`, as their declarative conversion relation.
