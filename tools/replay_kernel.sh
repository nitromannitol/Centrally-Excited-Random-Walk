#!/bin/bash
# Replay in the Lean kernel every declaration of every module of the library CERW, and of every
# module of the dependency LatticeProb that CERW imports, so that no declaration added with
# kernel checking disabled survives. Mathlib and the core library are imported, not replayed.
# The replay must also reject tools/fixtures/KernelBypass.lean. Run after `lake build`.
set -euo pipefail
cd "$(dirname "$0")/.."
out=$(lake env lean --run tools/ReplayKernel.lean CERW LatticeProb)
echo "$out"
n=$( { echo CERW.lean; find CERW -name "*.lean"; } | wc -l)
grep -qx "$n modules of CERW" <<<"$out" || { echo "expected $n modules of CERW"; exit 1; }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
lake env lean -o "$tmp/KernelBypass.olean" tools/fixtures/KernelBypass.lean
if lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run tools/ReplayKernel.lean KernelBypass' \
    "$tmp" >"$tmp/log" 2>&1; then
  echo "the kernel replay accepted tools/fixtures/KernelBypass.lean"; exit 1
fi
grep -q "declaration type mismatch, 'KernelBypass.falseProof'" "$tmp/log" \
  || { cat "$tmp/log"; echo "the kernel replay failed on the fixture for another reason"; exit 1; }
echo "the kernel replay rejects tools/fixtures/KernelBypass.lean"
