# Kontroli HOL4 verification workspace

Primary objective: establish a machine-checked specification and metatheory for
Kontroli's supported fragment of the λΠ-calculus modulo rewriting, then prove the
safe Rust kernel refines that specification.

Authority order for semantic work:
1. the published λΠ-calculus-modulo typing/rewrite metatheory;
2. the Dedukti standard and documented checker semantics;
3. Kontroli's published paper and the exact Rust source being refined.

Do not invent stronger assumptions to make a proof pass. Record assumptions such
as confluence, well-typed rewrite rules, termination/normalisation, eta mode, or
the exclusion of higher-order rewrite rules explicitly.

The initial implementation proof boundary is kontroli/src/kernel plus the data
structures it consumes. kocheck's parallel orchestration is a later layer.

HOL4's kernel/Holmake is the acceptance boundary. hol4-mcp, TacticToe, Aegis,
SMT/ATP tools, and agents are proof-search/orchestration aids only. Never report a
theorem as established unless the committed HOL4 theory builds without cheats or
oracle-only acceptance.

Use the Aegis HOL4 control plane pinned in formal/hol4/toolchain.json. Preserve
progress as small stacked pull requests. Each PR must have a single bounded proof
objective and must retain the exact parent branch.
