# HOL4 verification

This directory is the machine-checked specification and proof workspace for
Kontroli.

The first stack establishes the toolchain and a minimal HOL4 theory. Subsequent
stacks add syntax/substitution, reduction/conversion, declarative typing,
metatheory, then executable-kernel refinement.

## Local use

Requirements are pinned in `toolchain.json`.

```sh
export HOLDIR=/path/to/pinned/HOL
export HOL4_TACTICTOE_CACHE="$PWD/.aegis/tactictoe-cache"
cd formal/hol4
"$HOLDIR/bin/Holmake" --qof
```

For interactive agents, install the pinned `hol4-mcp` revision and use the
repository `.mcp.json`. MCP proof navigation is not proof evidence.

CI additionally imports the pinned Aegis HOL4 adapter and persists TacticToe's
manifest-validated cache between runs.
