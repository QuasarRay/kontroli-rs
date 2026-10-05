# LPCM proof automation

The first objective is to make the existing HOL4 theories replay. Afterwards,
the Rust implementation must be connected to those theories. The final objective
is a theorem about the exact machine code. Each step needs its own proof.

`run_proof_automation.py` currently checks four scoped lemmas. It does not certify
the whole metatheory, Kontroli's Rust implementation, or its executable.

1. The native Rust Egglog engine proposes existing HOL4 rewrite names.
2. HOL4 replays those named rewrites for a lifting/substitution identity.
3. `HolSmtLib.Z3_TAC` reconstructs two de Bruijn index arithmetic proofs.
4. TacticToe proves application convertibility using checked reduction facts.
5. The reused HOL proof inspector checks each exact conclusion, hypotheses,
   oracle tags and local axioms. Direct Holmake exports the resulting theory.

The latest checked run loaded 1,948 recorded tactic calls from MetaRocq's
manifest-managed persistent TacticToe cache. Search remains untrusted.

## Reuse

`reuse.json` identifies the existing HOL bridge, HOL proof inspector, native
Egglog revision and MetaRocq/Aegis process and MCP adapters. Their code is read
from the pinned Git objects and materialized in ignored local build directories.
It is not copied into a second framework.

Two small compatibility adaptations are recorded by before/after hashes:
seed the Egglog goal terms before saturation, and qualify `Term.term`/`Thm.thm`
in the inherited library signature. Neither adaptation changes a HOL theorem.

```sh
export HOLDIR=/path/to/built/pinned/HOL
export HOL4_Z3_EXECUTABLE=/path/to/z3
# Put the pinned hol4-mcp executable on PATH.
python3 scripts/run_proof_automation.py \
  --hol-tools /path/to/QuasarRay-HOL \
  --metarocq /path/to/pinned/MetaRocq-rs \
  --egglog-source /path/to/pinned/egglog \
  --egglog /path/to/egglog/target/release/egglog \
  --rustc /path/to/rustc
```

All execution is local after these tools are installed. Every run uses a fresh
build directory and a unique evidence directory. Failed runs retain diagnostics.
An earlier JSON receipt cannot bypass kernel replay. The proof workflows are
manual while this incremental stack is being repaired.

## Remaining proof boundaries

The declarative metatheory still fails beyond the successfully replayed syntax,
reduction and typing layers. The existing implementation-refinement contract
has open substitution, admission, WHNF, conversion and infer/check obligations.
Its product-compatibility premise must also be discharged for a concrete rewrite
system; ordinary rule typechecking does not establish it.

The rust-analyzer fork's Charon adapter was inspected. It delegates to a specific
Charon revision rather than independently defining Rust semantics. Its pinned
Aeneas/Charon pair differs from Kontroli's existing release, so combining their
outputs requires an explicit compatibility check.

For the binary boundary, seL4's relevant idea is translation validation: relate
the actual compiler output to the already verified source semantics. The exact
ELF bytes, ABI, runtime, allocator, dependency behavior and instruction semantics
must be included in that relation. A successful Rust build or an ELF digest
cannot discharge it. See the [seL4 proof assumptions](https://sel4.systems/Verification/assumptions.html).

The requested ISO architecture description remains conditional on completing
the source and machine-code proofs. This checkpoint does not claim that condition
has been met.
