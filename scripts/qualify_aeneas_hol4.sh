#!/usr/bin/env bash
set -uo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
evidence="$root/.aegis/aeneas"
bundle="$evidence/aeneas.tar.gz"
tool="$evidence/tool"
generated="$evidence/hol4-generated"
mkdir -p "$evidence" "$tool" "$generated"

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

status=0
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
  tar -xzf "$bundle" -C "$tool"
  "$tool/aeneas" -version
  "$tool/charon" --version || true
} >"$evidence/install.log" 2>&1 || status=$?

charon_status=125
aeneas_status=125
llbc=""
if [[ $status -eq 0 ]]; then
  (
    cd "$root/kontroli"
    RUSTUP_TOOLCHAIN="${AENEAS_RUST_TOOLCHAIN:-nightly-2026-09-17}"       "$tool/charon" cargo --preset=aeneas
  ) >"$evidence/charon.log" 2>&1
  charon_status=$?
  llbc="$(find "$root/kontroli" -maxdepth 1 -name '*.llbc' -print -quit)"
  if [[ $charon_status -eq 0 && -n "$llbc" ]]; then
    (
      cd "$generated"
      "$tool/aeneas" -backend hol4 "$llbc"
    ) >"$evidence/aeneas.log" 2>&1
    aeneas_status=$?
  else
    printf 'Charon failed or emitted no LLBC (status=%s)\n' "$charon_status" >"$evidence/aeneas.log"
  fi
else
  printf 'Aeneas bundle installation failed (status=%s)\n' "$status" >"$evidence/charon.log"
  printf 'Skipped because installation failed\n' >"$evidence/aeneas.log"
fi

python3 - "$evidence/result.json" "$status" "$charon_status" "$aeneas_status" "$llbc" <<'PY'
import json, pathlib, sys
out, install, charon, aeneas, llbc = sys.argv[1:]
data = {
  "schema": 1,
  "claim": "Aeneas/Charon extraction qualification only; success does not prove refinement",
  "install_status": int(install),
  "charon_status": int(charon),
  "aeneas_hol4_status": int(aeneas),
  "llbc": llbc or None,
  "generated_files": sorted(
      str(p.relative_to(pathlib.Path(out).parent))
      for p in (pathlib.Path(out).parent / "hol4-generated").glob("**/*")
      if p.is_file()
  ),
}
pathlib.Path(out).write_text(json.dumps(data, indent=2) + "\n")
print(json.dumps(data, indent=2))
PY

if [[ $status -ne 0 || $charon_status -ne 0 || $aeneas_status -ne 0 ]]; then
  exit 1
fi
