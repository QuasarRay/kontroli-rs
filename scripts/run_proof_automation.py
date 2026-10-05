#!/usr/bin/env python3
"""Run native Rust Egglog hints, HOL4/Z3 reconstruction and TacticToe replay.

Reuse the existing HOL bridge and MetaRocq/Aegis process and HOL adapters.
Each run freezes its inputs, uses an isolated build, and preserves diagnostics.
This command certifies only the four explicitly stated automation lemmas.
"""
from pathlib import Path
from dataclasses import asdict
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from uuid import uuid4

ROOT = Path(__file__).resolve().parents[1]
BRIDGE = "tools/cakeml-hol4/egglog-bridge/src/main.rs"
LIBRARY = "tools/cakeml-hol4/formal/Hol4ProofSearchLib"

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])

def pinned(repo, revision):
    if git(repo, "rev-parse", "HEAD").decode().strip() != revision:
        raise ValueError(f"wrong checkout revision: {repo}")
    if git(repo, "diff", "HEAD", "--"):
        raise ValueError(f"tracked source is modified: {repo}")

def seed_bridge(source):
    # The inherited bridge runs rewrites before check inserts the goal terms.
    # Materialize both sides before saturation. Search still supplies names only.
    before = 'program.push_str("(run 20)\\n(check (= ");'
    after = '''program.push_str("(let $lhs ");
        program.push_str(&lhs);
        program.push_str(")\\n(let $rhs ");
        program.push_str(&rhs);
        program.push_str(")\\n(run 20)\\n(check (= ");'''
    if source.count(before) != 1:
        raise ValueError("inherited Egglog bridge changed; re-audit its seed boundary")
    return source.replace(before, after)

def lazy_search(source):
    # SML list arguments are eager. The inherited library otherwise searches
    # with SMT and TacticToe even after its named-rewrite proof succeeded.
    before = '''  | first_success (NONE :: rest) = first_success rest
  | first_success (SOME x :: _) = x;'''
    after = '''  | first_success (attempt :: rest) =
      (case attempt () of NONE => first_success rest | SOME x => x);'''
    if source.count(before) != 1:
        raise ValueError("inherited search dispatcher changed; re-audit lazy fallback")
    source = source.replace(before, after)
    for engine in ("egglog-replay", "z3-replay", "tactictoe-replay"):
        before = 'attempt "' + engine + '"'
        if source.count(before) != 1:
            raise ValueError("inherited proof-search strategies changed")
        source = source.replace(before, 'fn () => ' + before)
    return source

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--hol-tools", type=Path, required=True)
    parser.add_argument("--metarocq", type=Path, required=True)
    parser.add_argument("--egglog-source", type=Path, required=True)
    parser.add_argument("--egglog", type=Path, required=True)
    parser.add_argument("--rustc", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=60)
    args = parser.parse_args()
    lock = json.loads((ROOT / "formal/automation/reuse.json").read_text())
    pinned(args.metarocq, lock["metarocq_commit"])
    pinned(args.egglog_source, lock["egglog_commit"])
    sys.path.insert(0, str(args.metarocq / ".agents/infra"))
    from agentinfra.process import run_process
    from agentinfra.hol4 import identity, hol4_home, environment, mcp_smoke
    if git(hol4_home(), "rev-parse", "HEAD").decode().strip() != lock["hol4_commit"]:
        raise ValueError("HOL4 pin differs from the Kontroli automation lock")
    refs = {s: git(args.hol_tools, "show", lock["hol_tools_commit"] + ":" + s)
            for s in (BRIDGE, LIBRARY + ".sml", LIBRARY + ".sig")}
    scripts = sorted((ROOT / "formal/hol4").glob("*Script.sml")) + sorted(
        (ROOT / "formal/automation/hol4").glob("*Script.sml"))
    paths = scripts + [
        ROOT / "formal/automation/reuse.json",
        ROOT / "formal/automation/binder-rewrites.tsv", Path(__file__)]
    inputs = {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in paths}
    tools = {"hol4": identity(require_mcp=True),
             "egglog": sha(args.egglog.read_bytes()), "rustc": sha(args.rustc.read_bytes()),
             "reused_sources": {p: sha(data) for p, data in refs.items()}}
    fingerprint = sha(json.dumps({"inputs": inputs, "tools": tools}, sort_keys=True).encode())
    evidence_root = ROOT / "formal/automation/evidence"
    evidence_root.mkdir(parents=True, exist_ok=True)
    for old in sorted(evidence_root.glob("*/result.json")):
        previous = json.loads(old.read_text())
        if previous.get("fingerprint") == fingerprint and previous.get("status") == "SCOPED_KERNEL_CHECKED":
            # A JSON receipt is not a theorem. Preserve the checkpoint reference,
            # but replay the small kernel proof before returning success.
            previous_run = str(old.relative_to(ROOT))
            break
    else:
        previous_run = None
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid4().hex[:8]
    out = evidence_root / run_id
    out.mkdir()
    stage = ROOT / ".aegis/proof-automation" / run_id
    stage.mkdir(parents=True)
    packet = {"schema": 1, "status": "FAILED", "fingerprint": fingerprint,
              "inputs": inputs, "tools": tools, "steps": {},
              "claim": "scoped automation and binder algebra; whole metatheory, Rust refinement and binary refinement remain open"}
    packet["previous_checked_checkpoint"] = previous_run
    env = {**environment(ROOT), "PATH": os.environ["PATH"]}
    if os.environ.get("LD_LIBRARY_PATH"):
        env["LD_LIBRARY_PATH"] = os.environ["LD_LIBRARY_PATH"]
    def execute(name, argv, cwd=stage):
        result = run_process([str(a) for a in argv], cwd=cwd,
                             timeout=args.timeout, env=env, capture_limit=2_000_000)
        packet["steps"][name] = {k: v for k, v in asdict(result).items()
                                 if k not in ("stdout", "stderr")}
        packet["steps"][name]["log"] = name + ".log"
        (out / (name + ".log")).write_text(result.stdout + result.stderr)
        if result.returncode or result.timed_out or result.stdout_truncated or result.stderr_truncated:
            raise RuntimeError(f"{name} failed; see preserved diagnostics")
        return result
    try:
        for path in scripts:
            shutil.copyfile(path, stage / path.name)
        for path, data in refs.items():
            if path != BRIDGE:
                if path.endswith(".sml"):
                    original = data
                    data = lazy_search(data.decode()).encode()
                    packet["search_adaptation"] = {
                        "original_sha256": sha(original), "lazy_sha256": sha(data),
                        "reason": "run fallback proof search only after the earlier strategy fails"}
                if path.endswith(".sig"):
                    original = data
                    data = re.sub(r"\bterm\b", "Term.term", data.decode())
                    data = re.sub(r"\bthm\b", "Thm.thm", data).encode()
                    packet["signature_adaptation"] = {
                        "original_sha256": sha(original), "qualified_sha256": sha(data),
                        "reason": "qualify kernel types in the inherited standalone signature"}
                (stage / Path(path).name).write_bytes(data)
        adapted = seed_bridge(refs[BRIDGE].decode())
        (stage / "bridge.rs").write_text(adapted)
        packet["bridge_adaptation"] = {"original_sha256": sha(refs[BRIDGE]),
                                      "seeded_sha256": sha(adapted.encode())}
        execute("bridge-build", [args.rustc, "--edition=2024", stage / "bridge.rs", "-o", stage / "bridge"])
        execute("egglog", [stage / "bridge", "--egglog", args.egglog,
            "--rules", ROOT / "formal/automation/binder-rewrites.tsv",
            "--lhs", '(App (App (Const "subst0") (Var "u")) (App (Const "lift1") (App (App (Const "subst0") (Var "a")) (App (Const "lift1") (App (Const "lift0") (Var "t"))))))',
            "--rhs", '(Var "t")', "--out", stage / "egglog-rewrites.txt",
            "--receipt", out / "egglog-receipt.json"])
        (stage / "Holmakefile").write_text("INCLUDES = $(HOLDIR)/src/integer $(HOLDIR)/src/HolSmt $(HOLDIR)/src/tactictoe/src\n")
        execute("hol4", [hol4_home() / "bin/Holmake", "--qof", "--no-cache", "-j1", "KontroliProofAutomationTheory.uo"])
        inspection = json.loads((stage / "automation-inspection.json").read_text())
        expected = ["egglog_lift_subst", "lift_index_bound_z3", "substitution_index_cancel_z3", "substitution_lift_bounds_z3", "application_conversion_tactictoe"]
        metatheory = ["lift_compose", "subst_lift_commute", "subst_subst_ge", "red_subst_from_rewrite_closed", "convertible_subst_from_rewrite_closed"]
        if inspection.get("theorems") != expected or inspection.get("metatheory_theorems") != metatheory or inspection.get("exact_goals_checked") is not True or any(
            inspection.get(k) != 0 for k in ("hypotheses", "non_disk_oracles", "local_axioms")):
            raise ValueError("unexpected HOL4 theorem inspection")
        packet["inspection"] = inspection
        (out / "inspection.json").write_text(json.dumps(inspection, indent=2) + "\n")
        packet["exports"] = {p.name: sha(p.read_bytes()) for theory in
                             ("KontroliBase", "LambdaPiSyntax", "LambdaPiReduction", "LambdaPiTyping", "LambdaPiBinderAlgebra", "KontroliProofAutomation")
                             for p in (stage / ".hol/objs").glob(theory + "Theory.*")}
        packet["mcp"] = mcp_smoke(ROOT, timeout=30)
        if inputs != {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in paths} or tools["hol4"] != identity(require_mcp=True):
            raise ValueError("proof inputs or kernel tools changed during replay")
        if tools["egglog"] != sha(args.egglog.read_bytes()) or tools["rustc"] != sha(args.rustc.read_bytes()):
            raise ValueError("search tools changed during replay")
        packet["status"] = "SCOPED_KERNEL_CHECKED"
    except Exception as exc:
        packet["reason"] = str(exc)
    finally:
        (out / "result.json").write_text(json.dumps(packet, indent=2) + "\n")
    print(json.dumps({"status": packet["status"], "evidence": str(out.relative_to(ROOT)), "reason": packet.get("reason")}))
    return 0 if packet["status"] == "SCOPED_KERNEL_CHECKED" else 1

if __name__ == "__main__":
    raise SystemExit(main())
