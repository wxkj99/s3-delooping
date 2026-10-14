#!/usr/bin/env bash
set -euo pipefail
HERE="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
BUILD="${PAPER_BUILD_DIR:-$HERE/.build}"
mkdir -p "$BUILD"; cd "$HERE"
for i in 1 2 3; do
  timeout 240s pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory="$BUILD" main.tex >"$BUILD/build-$i.log" 2>&1 || { tail -50 "$BUILD/build-$i.log"; exit 1; }
done
if grep -Eq 'Overfull|Missing character:|There were undefined references|Citation .* undefined|Reference .* undefined|Token not allowed in a PDF string|multiply defined' "$BUILD/main.log"; then
  grep -nE 'Overfull|Missing character:|undefined|Token not allowed|multiply defined' "$BUILD/main.log"
  echo 'Resolve layout and reference warnings before publishing the PDF.' >&2
  exit 1
fi
cp "$BUILD/main.pdf" "$HERE/../s3-delooping-paper.pdf"
