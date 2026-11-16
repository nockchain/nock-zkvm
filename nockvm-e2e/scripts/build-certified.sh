#!/usr/bin/env bash
# build-certified.sh <outdir> — build the certified verifier `nockvm-e2e-verify-cert` from THIS tree and collect what a reviewer needs to
# audit and reproduce it: the binary, the Lean-emitted C of every module in its closure (.lake/build/ir/**), the toolchain versions, and sha256s.
#   CLEAN=1       first delete the exe's own build products (binary and the ir/olean/ilean/trace/hash files of NockvmE2E.Exec.Cert*,
#                 NockvmE2E.Exec.VerifyCertMain) so that those modules are really re-elaborated and re-emitted; the dependency closure is
#                 rebuilt only if stale (a whole-closure clean build is hours; set CLEAN=all to `rm -rf .lake/build` too).
#   SKIP_BUILD=1  do not call lake (collect from the existing build; used when a queue already built the target).
#   LAKE=<cmd>    the lake command (default: lake).
# Run it twice into two output dirs and `diff <dir1>/SHA256SUMS <dir2>/SHA256SUMS`: the shas of the emitted C and of the binary must match.
set -euo pipefail
OUT=${1:?usage: build-certified.sh <outdir>}
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)     # the nockvm-e2e package root
cd "$HERE"
LAKE=${LAKE:-lake}
EXE=nockvm-e2e-verify-cert
mkdir -p "$OUT/ir" "$OUT/bin"
if [ "${CLEAN:-}" = all ]; then rm -rf .lake/build; fi
if [ "${CLEAN:-}" = 1 ]; then
  rm -f .lake/build/bin/$EXE .lake/build/bin/$EXE.*
  for f in .lake/build/ir/NockvmE2E/Exec/Cert* .lake/build/ir/NockvmE2E/Exec/VerifyCertMain* \
           .lake/build/lib/lean/NockvmE2E/Exec/Cert* .lake/build/lib/lean/NockvmE2E/Exec/VerifyCertMain*; do
    [ -e "$f" ] && rm -rf "$f"
  done
fi
[ "${SKIP_BUILD:-}" = 1 ] || $LAKE build $EXE
{ echo "lean: $(lean --version 2>&1 | head -1)"; echo "lake: $($LAKE --version 2>&1 | head -1)"; echo "cc: $(cc --version 2>&1 | head -1)"
  echo "tree: $(git rev-parse HEAD 2>/dev/null || echo unknown)"; echo "uname: $(uname -srm)"; } > "$OUT/VERSIONS.txt"
cp .lake/build/bin/$EXE "$OUT/bin/$EXE"
# the emitted C of the exe's own modules and of its whole import closure's ir tree
( cd .lake/build/ir && find . -name '*.c' -print0 | sort -z | xargs -0 -I{} cp --parents {} "$OUT/ir/" )
( cd "$OUT" && find bin ir -type f -print0 | sort -z | xargs -0 sha256sum > SHA256SUMS )
echo "wrote $OUT: $(grep -c . "$OUT/SHA256SUMS") files; binary sha256:"; grep " bin/$EXE\$" "$OUT/SHA256SUMS"
cat "$OUT/VERSIONS.txt"
