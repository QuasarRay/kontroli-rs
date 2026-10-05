#!/usr/bin/env bash
set -uo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
runs="$root/.aegis/aeneas"
cache="$root/.aegis/aeneas-cache"
mkdir -p "$runs" "$cache"
evidence="$(mktemp -d "$runs/$(date -u +%Y%m%dT%H%M%SZ)-XXXXXX")"
bundle="${AENEAS_BUNDLE:-$cache/aeneas.tar.gz}"
tool="$evidence/tool"
scope="${AENEAS_SCOPE:-all}"
sysroot="${AENEAS_SYSROOT:-default}"
step_timeout="${AENEAS_STEP_TIMEOUT:-120}"
case "$scope" in all|subst-slice|full) ;; *) echo "Unknown extraction scope: $scope" >&2; exit 2;; esac
mkdir -p "$evidence" "$tool" "$cache"

readarray -t cfg < <(python3 - "$root/formal/hol4/toolchain.json" <<'PY'
import json, sys
j=json.load(open(sys.argv[1]))
a=j["aeneas_release"]
print(a["url"])
print(a["sha256"])
print(a["tag"])
PY
)
url="${cfg[0]}"
expected="${cfg[1]}"
tag="${cfg[2]}"

install_tool() {
  echo "Aeneas release: $tag"
  echo "Asset: $url"
  if [[ ! -f "$bundle" ]]; then
    curl -L --fail --retry 1 --max-time "$step_timeout" "$url" -o "$bundle.part" || return
    mv "$bundle.part" "$bundle" || return
  fi
  actual="$(sha256sum "$bundle" | awk '{print $1}')"
  echo "sha256: $actual"
  if [[ "$actual" != "$expected" ]]; then
    echo "Aeneas archive digest mismatch" >&2
    return 90
  fi
  tar --no-same-owner -xzf "$bundle" -C "$tool" || return
  "$tool/aeneas" -version || return
  "$tool/charon" version || return
  "$tool/charon" toolchain-version || return
  local toolchain_path
  toolchain_path="$("$tool/charon" toolchain-path)" || return
  "$toolchain_path/bin/rustc" --version --verbose >"$evidence/rustc-version.log" || return
}
install_status=0
install_tool >"$evidence/install.log" 2>&1 || install_status=$?

python3 - "$root" "$evidence/source-inputs.json" <<'PY'
import hashlib, json, pathlib, subprocess, sys
root, out = map(pathlib.Path, sys.argv[1:])
paths = subprocess.check_output([
    "git", "ls-files", "--", "*.rs", "Cargo.lock", "Cargo.toml", "*/Cargo.toml",
    "formal/hol4/toolchain.json", "scripts/qualify_aeneas_hol4.sh",
    "scripts/aeneas_hol4_manifest.py"], cwd=root).decode().splitlines()
data = {p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in paths}
out.write_text(json.dumps(data, indent=2) + "\n")
PY

run_scope() {
  local scope="$1"
  local start_from="$2"
  local out="$evidence/$scope"
  local llbc="$out/kontroli.llbc"
  local generated="$out/hol4-generated"
  local charon_status=125
  local aeneas_status=125

  mkdir -p "$out" "$generated"

  if [[ $install_status -ne 0 ]]; then
    printf 'Skipped: tool installation failed (%s)\n' "$install_status" >"$out/charon.log"
    printf 'Skipped: tool installation failed\n' >"$out/aeneas.log"
  else
    local -a charon_args=(cargo --preset=aeneas "--sysroot=$sysroot" "--dest-file=$llbc")
    if [[ -n "${AENEAS_MONOMORPHIZE_MUT:-}" ]]; then
      charon_args+=("--monomorphize-mut=$AENEAS_MONOMORPHIZE_MUT")
    fi
    if [[ -n "$start_from" ]]; then
      charon_args+=("--start-from=$start_from")
    fi
    (
      cd "$root/kontroli"
      RUSTUP_TOOLCHAIN="${AENEAS_RUST_TOOLCHAIN:-nightly-2026-09-17}" \
        timeout --kill-after=5 "$step_timeout" "$tool/charon" "${charon_args[@]}" -- --locked
    ) >"$out/charon.log" 2>&1
    charon_status=$?

    if [[ $charon_status -eq 0 && -s "$llbc" ]]; then
      timeout --kill-after=5 "$step_timeout" "$tool/aeneas" -backend hol4 \
        -sequential -no-progress-bar -warnings-as-errors "$llbc" -dest "$generated" \
        >"$out/aeneas.log" 2>&1
      aeneas_status=$?
      if [[ $aeneas_status -eq 0 ]]; then
        python3 "$root/scripts/aeneas_hol4_manifest.py" \
          "$generated" "$out/symbols.json" >"$out/manifest.log" 2>&1
      else
        printf 'Skipped: Aeneas HOL4 extraction failed\n' >"$out/manifest.log"
      fi
    else
      printf 'Charon failed or emitted no LLBC (status=%s)\n' "$charon_status" >"$out/aeneas.log"
    fi
  fi

python3 - "$out/result.json" "$scope" "$start_from" "$install_status" "$charon_status" "$aeneas_status" <<'PY'
import hashlib, json, os, pathlib, sys
out, scope, start_from, install, charon, aeneas = sys.argv[1:]
p = pathlib.Path(out)
data = {
  "schema": 1,
  "scope": scope,
  "start_from": start_from or None,
  "claim": "Aeneas/Charon extraction qualification only; success does not prove refinement",
  "install_status": int(install),
  "charon_status": int(charon),
  "aeneas_hol4_status": int(aeneas),
  "llbc_exists": (p.parent / "kontroli.llbc").is_file(),
  "llbc_sha256": hashlib.sha256((p.parent / "kontroli.llbc").read_bytes()).hexdigest() if (p.parent / "kontroli.llbc").is_file() else None,
  "mutable_reference_monomorphization": os.environ.get("AENEAS_MONOMORPHIZE_MUT"),
  "generated_files": sorted(
      str(x.relative_to(p.parent))
      for x in (p.parent / "hol4-generated").glob("**/*")
      if x.is_file()
  ),
  "symbol_manifest": "symbols.json" if (p.parent / "symbols.json").is_file() else None,
}
p.write_text(json.dumps(data, indent=2) + "\n")
print(json.dumps(data, indent=2))
PY

  [[ $install_status -eq 0 && $charon_status -eq 0 && $aeneas_status -eq 0 ]]
}

full_status=125
slice_status=125
if [[ "$scope" != full ]]; then
  slice_status=0
  run_scope subst-slice "crate::kernel::subst" || slice_status=$?
fi
# The whole crate contains this slice. Avoid another known-blocked extraction
# unless the caller explicitly requests the full diagnostic run.
if [[ "$scope" == full || ( "$scope" == all && $slice_status -eq 0 ) ]]; then
  full_status=0
  run_scope full "" || full_status=$?
fi

python3 - "$root" "$evidence/result.json" "$install_status" "$full_status" "$slice_status" "$scope" "$sysroot" "$expected" <<'PY'
import hashlib, json, pathlib, sys
root, out, install, full, sliced, scope, sysroot, archive_sha = sys.argv[1:]
root, out = pathlib.Path(root), pathlib.Path(out)
inputs = json.loads((out.parent / "source-inputs.json").read_text())
unchanged = all((root / p).is_file() and hashlib.sha256((root / p).read_bytes()).hexdigest() == digest
                for p, digest in inputs.items())
data = {
  "schema": 3,
  "claim": "Extraction qualification, not an implementation correctness proof",
  "install_status": int(install),
  "full_crate_qualified": int(full) == 0,
  "subst_slice_qualified": int(sliced) == 0,
  "required_checkpoint": "full" if scope == "full" else "subst-slice",
  "scope": scope,
  "sysroot": sysroot,
  "archive_sha256": archive_sha,
  "tool_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in (out.parent / "tool").iterdir() if p.is_file()},
  "inputs_unchanged": unchanged,
  "skip_reason": "full extraction skipped after failed prerequisite slice" if scope == "all" and int(sliced) != 0 else None,
}
out.write_text(json.dumps(data, indent=2) + "\n")
print(json.dumps(data, indent=2))
if not unchanged:
    raise SystemExit("source inputs changed during extraction")
PY
input_status=$?

# Incremental policy: the substitution slice is the required checkpoint for
# this PR. Full-crate qualification remains recorded and becomes mandatory in
# the later whole-kernel refinement layer.
required_status="$slice_status"
if [[ "$scope" == full ]]; then required_status="$full_status"; fi
if [[ $install_status -ne 0 || $required_status -ne 0 || $input_status -ne 0 ]]; then
  exit 1
fi
