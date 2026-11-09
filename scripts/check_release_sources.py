#!/usr/bin/env python3
"""Source-only public package audit; works without private engineering ledgers."""
from pathlib import Path
import re
import sys
ROOT=Path(__file__).resolve().parents[1]
items=[
    *sorted((ROOT/'src').rglob('*.lean')),
    *sorted((ROOT/'examples').glob('*.lean')),
    *sorted((ROOT/'ChallengeDefs').glob('*.lean')),
    ROOT/'Challenge.lean', ROOT/'Solution.lean',
]
if len(items)!=175:raise SystemExit(f'Expected 175 Lean source files; got {len(items)}')
for p in items:
    if not p.is_file() or p.is_symlink() or not p.read_text().startswith('module\n'):
        raise SystemExit('Invalid module file '+str(p))
    if p != ROOT/'Challenge.lean' and re.search(r'(?m)^\s*sorry\s*(?:$|--)',p.read_text()):
        raise SystemExit('Proof placeholder in proved module: '+str(p))
challenge=(ROOT/'Challenge.lean').read_text()
if len(re.findall(r'(?m)^\s*sorry\s*(?:$|--)',challenge))!=3:
    raise SystemExit('Expected exactly three challenge contract placeholders')
for file in ['LICENSE','NOTICE','CITATION.cff','formalization.yaml','README.md',
             'RELEASE_PROVENANCE.md','comparator.json','lakefile.toml',
             'lake-manifest.json','lean-toolchain','Solution.lean']:
    if not (ROOT/file).is_file():raise SystemExit('Missing release file '+file)
if not (ROOT/'scripts/check_canonical_challenge.py').is_file():
    raise SystemExit('Missing canonical Challenge source fidelity audit')
print('PUBLIC_SOURCE_STRUCTURE_PASS',len(items),'module-format files, 3 deliberate Challenge holes')
