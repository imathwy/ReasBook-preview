#!/usr/bin/env bash

# Build the main Lean project. Set BUILD_DOCS=0 to skip doc-gen4.
set -euo pipefail

LAKE_BIN="${LAKE_BIN:-$HOME/.elan/bin/lake}"
BUILD_DOCS="${BUILD_DOCS:-1}"

cd ReasBook
"$LAKE_BIN" exe cache get || true
if [ "$BUILD_DOCS" = "1" ]; then
  "$LAKE_BIN" -R -Kenv=dev build ReasBook:docs
fi
"$LAKE_BIN" build
