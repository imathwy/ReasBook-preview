#!/usr/bin/env bash

# Build the Verso web project after sections/routes generation.
set -euo pipefail

LAKE_BIN="${LAKE_BIN:-$HOME/.elan/bin/lake}"

echo "[build_reasbook_web] generating sections/routes"
cd ReasBookWeb
python3 scripts/gen_sections.py

echo "[build_reasbook_web] running cache get (if available)"
if "$LAKE_BIN" exe cache get; then
  echo "[build_reasbook_web] cache get completed"
else
  echo "[build_reasbook_web] cache executable not available in this project; continuing without cache get"
fi

echo "[build_reasbook_web] building Verso site"
"$LAKE_BIN" exe reasbook-site
