#!/usr/bin/env bash
set -euo pipefail
# Run only on trusted, isolated Linux with bubblewrap. This does NOT publish.
cd "$(dirname "$0")/.."
for tool in bwrap lake lean python3; do
  command -v "$tool" >/dev/null || { echo "missing required $tool" >&2; exit 2; }
done
prefix="$(lean --print-prefix)"
for tool in leanexport leanchecker nanoda_bin con-ron; do
  test -x "$prefix/bin/$tool" || { echo "toolchain lacks $tool" >&2; exit 2; }
done
cfg="$(mktemp ${TMPDIR:-/tmp}/shiu-palomar-comparator.XXXXXX)"
trap 'rm -f "$cfg"' EXIT
python3 - "$cfg" "$prefix" <<'PY'
import json, pathlib, sys
dst,prefix=sys.argv[1:]
cfg=json.loads(pathlib.Path('comparator.json').read_text())
assert 'external_kernels' not in cfg
cfg.pop('enable_nanoda',None)
cfg['external_kernels']={
  'nanoda':[prefix+'/bin/nanoda_bin'],
  'con-ron':[prefix+'/bin/con-ron']
}
pathlib.Path(dst).write_text(json.dumps(cfg,indent=2)+'\n')
PY
lake comparator --config "$cfg"
