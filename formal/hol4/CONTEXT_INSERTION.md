# Context insertion

Weakening in a de Bruijn context is not "append one binder and lift
everything". Under a binder, the new declaration is inserted before an
existing suffix.

This theory therefore defines:

- `lift_ctx_from`: lift each stored suffix declaration at the cutoff matching
  the declarations already in scope;
- `insert_context G B H`: insert binder `B` between prefix `G` and suffix
  `H`;
- `insert_index`: keep variables naming suffix binders unchanged and shift
  variables naming the older prefix by one.

The next checkpoint relates `ctx_type (G ++ H)` to
`ctx_type (insert_context G B H)`, then lifts the result from lookup algebra
to declarative typing.
