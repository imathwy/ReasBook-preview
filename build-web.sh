#!/usr/bin/env bash

# Build Verso site and place API docs at _site/docs.
set -euo pipefail

LAKE_BIN="${LAKE_BIN:-$HOME/.elan/bin/lake}"

./build.sh

cd ReasBookWeb
python3 scripts/gen_sections.py
"$LAKE_BIN" exe reasbook-site

mkdir -p _site/docs
cp -r ../ReasBook/.lake/build/doc/. _site/docs/
find _site/docs -name "*.trace" -delete || true
find _site/docs -name "*.hash" -delete || true
