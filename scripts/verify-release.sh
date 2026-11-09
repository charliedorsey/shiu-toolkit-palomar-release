#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_release_sources.py
lake exe cache get
lake build ShiuToolkit Challenge Solution
for file in examples/*.lean; do
  lake env lean "$file"
done
printf '%s\n' 'LOCAL_LEAN_AND_8_CONSUMER_CHECKS_PASS'
printf '%s\n' 'The independent Comparator requires a trusted Linux runner with Bubblewrap and the required external kernel binaries.'
printf '%s\n' 'Run bash scripts/verify-comparator.sh there; do not infer its PASS from this script.'
