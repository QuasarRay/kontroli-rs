#!/usr/bin/env python3
"""Make inherited HOL4 ML theorem names available explicitly and deterministically."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1] / "formal/hol4"
PATTERN = re.compile(r"(?m)^Ancestors\n((?:[ \t]+[A-Za-z0-9_ \t]+\n)+)")

def main():
    files = {p.name.removesuffix("Script.sml"): p for p in ROOT.glob("*Script.sml")}
    sources = {name: p.read_text() for name, p in files.items()}
    parents = {name: (PATTERN.search(s).group(1).split() if PATTERN.search(s) else [])
               for name, s in sources.items()}
    def closure(name, active=()):
        if name in active:
            raise ValueError("cyclic theory dependencies: " + " -> ".join((*active, name)))
        result = []
        for parent in parents.get(name, []):
            for item in [parent, *closure(parent, (*active, name))]:
                if item not in result:
                    result.append(item)
        return result
    for name, path in sorted(files.items()):
        if parents[name]:
            expanded = PATTERN.sub(lambda _: "Ancestors\n  " + " ".join(closure(name)) + "\n", sources[name], count=1)
            if expanded != sources[name]:
                path.write_text(expanded)
                print(path.name)

if __name__ == "__main__":
    main()
