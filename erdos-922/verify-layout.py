"""Read-only checks for a staged portable package; never runs Lean or Lake."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--dependencies', action='store_true')
args = parser.parse_args()
lock = json.loads((ROOT / 'source-lock.json').read_text(encoding='utf-8'))
manifest_bytes = (ROOT / 'lake-manifest.json').read_bytes()
assert hashlib.sha256(manifest_bytes).hexdigest() == lock['lake_manifest_sha256'], 'Manifest changed'
manifest = json.loads(manifest_bytes)
assert (ROOT / 'lean-toolchain').read_text().strip() == lock['lean_toolchain']
records = lock['proof_modules'] + [lock['audit']]
names = {x['module'] for x in records}
expected = {x['path'] for x in records}
actual = {p.relative_to(ROOT).as_posix() for folder in ('src', 'audit')
          for p in (ROOT / folder).rglob('*.lean')}
assert actual == expected, ('Staged source paths differ', sorted(expected - actual), sorted(actual - expected))
graph = {}
for rec in records:
    data = (ROOT / rec['path']).read_bytes()
    assert len(data) == rec['bytes'], rec['path']
    assert hashlib.sha256(data).hexdigest() == rec['sha256'], rec['path']
    imports = []
    for line in data.decode('utf-8-sig').splitlines():
        if line.startswith('import '):
            imports.extend(line[7:].split('--', 1)[0].split())
    assert imports == rec['imports'], ('Imports changed', rec['path'])
    assert all(n in names or n.startswith('Mathlib.') for n in imports), rec['path']
    graph[rec['module']] = [n for n in imports if n in names]
seen, active = set(), set()
def visit(name):
    assert name not in active, ('Import cycle', name)
    if name in seen:
        return
    active.add(name)
    for dep in graph[name]:
        visit(dep)
    active.remove(name)
    seen.add(name)
visit('E922ProjectRebuildAudit')
assert seen == names, ('Unused source outside endpoint audit closure', sorted(names - seen))
assert all(re.fullmatch(r'[0-9a-f]{40}', p['rev']) and p['type'] == 'git'
           for p in manifest['packages']), 'Unpinned dependency'
if args.dependencies:
    for pkg in manifest['packages']:
        checkout = ROOT / manifest['packagesDir'] / pkg['name']
        rev = subprocess.run(['git', '--no-optional-locks', '-C', str(checkout), 'rev-parse', 'HEAD'],
                             check=True, capture_output=True, text=True).stdout.strip()
        assert rev == pkg['rev'], ('Dependency revision mismatch', pkg['name'])
        dirty = subprocess.run(['git', '--no-optional-locks', '-C', str(checkout),
                                'status', '--porcelain', '--untracked-files=no'],
                               check=True, capture_output=True, text=True).stdout.strip()
        assert not dirty, ('Tracked dependency modifications', pkg['name'], dirty)
print('PASS: 29 unchanged proof modules + unchanged 24-name audit; complete local closure; exact manifest.')
if args.dependencies:
    print('PASS: all 9 dependency HEADs pinned and no tracked dependency modifications.')
print('Static checks only: no Lean/Lake execution, theorem validation or sandbox certification.')
