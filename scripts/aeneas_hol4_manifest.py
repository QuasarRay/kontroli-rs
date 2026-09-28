#!/usr/bin/env python3
"""Extract a deterministic interface manifest from Aeneas-generated HOL4."""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

THEORY = re.compile(r'new_theory\s+"([^"]+)"')
DEF = re.compile(r'\bval\s+([A-Za-z0-9_]+_def)\s*=')
CONST = re.compile(r'new_constant\s*\(\s*"([^"]+)"')


def main() -> int:
    if len(sys.argv) != 3:
        raise SystemExit("usage: aeneas_hol4_manifest.py GENERATED_DIR OUTPUT_JSON")
    generated = Path(sys.argv[1]).resolve()
    output = Path(sys.argv[2]).resolve()
    if not generated.is_dir():
        raise SystemExit(f"generated HOL4 directory not found: {generated}")

    files = []
    theories: set[str] = set()
    definitions: set[str] = set()
    constants: set[str] = set()

    for path in sorted(generated.rglob("*.sml")):
        text = path.read_text(encoding="utf-8", errors="strict")
        rel = str(path.relative_to(generated))
        files.append(rel)
        theories.update(THEORY.findall(text))
        definitions.update(DEF.findall(text))
        constants.update(CONST.findall(text))

    data = {
        "schema": 1,
        "generator": "scripts/aeneas_hol4_manifest.py",
        "claim": "generated-code interface discovery only; not refinement evidence",
        "files": files,
        "theories": sorted(theories),
        "definitions": sorted(definitions),
        "constants": sorted(constants),
        "forward_definitions": sorted(
            d for d in definitions if "_fwd" in d
        ),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print(json.dumps(data, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
