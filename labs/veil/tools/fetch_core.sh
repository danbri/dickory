#!/bin/sh
# Fetch the factoidal-core files this lab compiles, at the pinned commit, into artifacts/.
set -eu
cd "$(dirname "$0")/.."
ref=$(cat tools/core-ref.txt)
dir=artifacts/factoidal-core
if [ ! -d "$dir/.git" ]; then
  git init -q "$dir"
  git -C "$dir" remote add origin https://github.com/danbri/factoidal-core.git
  git -C "$dir" sparse-checkout set --no-cone /formal/lean4/L4Factoidal/CL/ \
    /formal/lean4/L4Factoidal/Syntax/Lexing.lean /formal/lean4/L4Factoidal/Encoding/Hex.lean
fi
git -C "$dir" fetch -q --depth 1 --filter=blob:none origin "$ref"
git -C "$dir" checkout -q --detach FETCH_HEAD
test "$(git -C "$dir" rev-parse HEAD)" = "$ref"
echo "factoidal-core $ref in $dir"
