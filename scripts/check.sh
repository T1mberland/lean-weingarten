#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

lake build Weingarten Weingarten.Examples Weingarten.AxiomAudit
python3 - <<'PY'
from pathlib import Path
import re
import subprocess

# The current source has no nested block comments; strip comments before scanning.
paths = [Path('Weingarten.lean'), *Path('Weingarten').glob('*.lean')]
for path in paths:
    source = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
    source = re.sub(r'--[^\n]*', '', source)
    if re.search(r'\b(sorry|admit|axiom)\b', source):
        raise SystemExit(f'Unproved declaration or placeholder in {path}')

result = subprocess.run(
    ['lake', 'env', 'lean', 'Weingarten/AxiomAudit.lean'],
    check=True, text=True, capture_output=True)
print(result.stdout, end='')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', result.stdout)
if len(reports) != 14:
    raise SystemExit(f'Expected 14 axiom reports; found {len(reports)}')
for report in reports:
    unexpected = {a.strip() for a in report.split(',') if a.strip()} - allowed
    if unexpected:
        raise SystemExit(f'Unexpected axioms: {unexpected}')
print('All principal results use only the standard Lean logical foundations.')
PY
