#!/usr/bin/env bash
set -uo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
evidence="$root/.aegis/aeneas"
bundle="$evidence/aeneas.tar.gz"
tool="$evidence/tool"
mkdir -p "$evidence" "$tool"

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

install_status=0
{
  echo "Aeneas release: $tag"
  echo "Asset: $url"
  curl -L --fail --retry 3 "$url" -o "$bundle"
  actual="$(sha256sum "$bundle" | awk '{print $1}')"
  echo "sha256: $actual"
  if [[ "$actual" != "$expected" ]]; then
    echo "Aeneas archive digest mismatch" >&2
    exit 90
  fi
  rm -rf "$tool"
  mkdir -p "$tool"
  tar -xzf "$bundle" -C "$tool"
  "$tool/aeneas" -version
  "$tool/charon" --version || true
} >"$evidence/install.log" 2>&1 || install_status=$?

run_scope() {
  local scope="$1"
  local start_from="$2"
  local out="$evidence/$scope"
  local llbc="$out/kontroli.llbc"
  local generated="$out/hol4-generated"
  local charon_status=125
  local aeneas_status=125

  rm -rf "$out"
  mkdir -p "$out" "$generated"

  if [[ $install_status -ne 0 ]]; then
    printf 'Skipped: tool installation failed (%s)\n' "$install_status" >"$out/charon.log"
    printf 'Skipped: tool installation failed\n' >"$out/aeneas.log"
  else
    local -a charon_args=(cargo --preset=aeneas "--dest-file=$llbc")
    if [[ -n "$start_from" ]]; then
      charon_args+=("--start-from=$start_from")
    fi
    (
      cd "$root/kontroli"
      RUSTUP_TOOLCHAIN="${AENEAS_RUST_TOOLCHAIN:-nightly-2026-09-17}" \
        "$tool/charon" "${charon_args[@]}"
    ) >"$out/charon.log" 2>&1
    charon_status=$?

    if [[ $charon_status -eq 0 && -s "$llbc" ]]; then
      "$tool/aeneas" -backend hol4 "$llbc" -dest "$generated" \
        >"$out/aeneas.log" 2>&1
      aeneas_status=$?
    else
      printf 'Charon failed or emitted no LLBC (status=%s)\n' "$charon_status" >"$out/aeneas.log"
    fi
  fi

  python3 - "$out/result.json" "$scope" "$start_from" "$install_status" "$charon_status" "$aeneas_status" <<'PY'
import json, pathlib, sys
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
  "generated_files": sorted(
      str(x.relative_to(p.parent))
      for x in (p.parent / "hol4-generated").glob("**/*")
      if x.is_file()
  ),
}
p.write_text(json.dumps(data, indent=2) + "\n")
print(json.dumps(data, indent=2))
PY

  [[ $install_status -eq 0 && $charon_status -eq 0 && $aeneas_status -eq 0 ]]
}

full_status=0
run_scope full "" || full_status=$?

slice_status=0
run_scope subst-slice "crate::kernel::subst" || slice_status=$?

python3 - "$evidence/result.json" "$install_status" "$full_status" "$slice_status" <<'PY'
import json, pathlib, sys
out, install, full, sliced = sys.argv[1:]
data = {
  "schema": 2,
  "claim": "Extraction qualification, not an implementation correctness proof",
  "install_status": int(install),
  "full_crate_qualified": int(full) == 0,
  "subst_slice_qualified": int(sliced) == 0,
  "required_checkpoint": "subst-slice",
}
pathlib.Path(out).write_text(json.dumps(data, indent=2) + "\n")
print(json.dumps(data, indent=2))
PY

# Incremental policy: the substitution slice is the required checkpoint for
# this PR. Full-crate qualification remains recorded and becomes mandatory in
# the later whole-kernel refinement layer.
if [[ $install_status -ne 0 || $slice_status -ne 0 ]]; then
  exit 1
fi
