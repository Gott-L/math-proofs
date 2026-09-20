"""Build all five modules and record the separate named-axiom audit.

After preparing dependencies, run: python verify.py --label my-check
This uses the installed Lean toolchain and available dependency artifacts;
it does not independently rebuild or certify Lean or all of Mathlib.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--lake', default='lake')
parser.add_argument('--label', required=True)
args = parser.parse_args()
if not re.fullmatch(r'[A-Za-z0-9-]+', args.label):
    raise SystemExit('The label must contain only letters, digits and hyphens.')
out = ROOT / 'verification' / args.label
out.mkdir(parents=True, exist_ok=False)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

files = sorted(ROOT.glob('*.lean')) + [ROOT / name for name in
    ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain')]
sources = {p.name: dict(bytes=p.stat().st_size, sha256=digest(p)) for p in files}
env = os.environ.copy()
env.pop('LEAN_PATH', None)
env.pop('LEAN_SRC_PATH', None)
lake = Path(args.lake)
if lake.is_absolute():
    env['PATH'] = str(lake.parent) + os.pathsep + env.get('PATH', '')
manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))
dependencies = []
for item in manifest['packages']:
    path = ROOT / '.lake/packages' / item['name']
    head = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    if head != item['rev']:
        raise SystemExit(f'Package {item["name"]} differs from the manifest pin.')
    dirty = subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], text=True)
    if dirty:
        raise SystemExit(f'Package {item["name"]} has tracked changes.')
    dependencies.append(dict(name=item['name'], revision=head, tracked_source_clean=True))
version = subprocess.check_output([args.lake, '--version'], cwd=ROOT, env=env, text=True).strip()
records = []
audit = None

def save():
    unchanged = all(digest(ROOT / k) == v['sha256'] for k, v in sources.items())
    (out / 'result.json').write_text(json.dumps(dict(
        source_and_config=sources, source_and_config_unchanged=unchanged,
        lake_version=version, dependencies=dependencies, records=records,
        axiom_audit=audit,
        dependency_trust='Pinned cached dependency artifacts reused; missing or stale dependencies rebuilt by Lake. Not a clean rebuild or independent verification of Lean/Mathlib.'
    ), indent=2) + '\n', encoding='utf-8')
    return unchanged

for name, command in [
    ('build', [args.lake, 'build']),
    ('axioms', [args.lake, 'env', 'lean', '-DwarningAsError=true', 'Audit.lean']),
]:
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    t0 = time.monotonic()
    stdout = out / (name + '-stdout.txt')
    stderr = out / (name + '-stderr.txt')
    print(f'Starting {name}: {command}', flush=True)
    with stdout.open('wb') as out_handle, stderr.open('wb') as err_handle:
        p = subprocess.run(command, cwd=ROOT, env=env, stdout=out_handle, stderr=err_handle)
    records.append(dict(name=name, started_utc=start, command=command,
        cwd=str(ROOT), exit_code=p.returncode, elapsed_seconds=time.monotonic() - t0,
        stdout_bytes=stdout.stat().st_size, stderr_bytes=stderr.stat().st_size,
        stdout_sha256=digest(stdout), stderr_sha256=digest(stderr)))
    if name == 'axioms' and p.returncode == 0:
        text = stdout.read_text(encoding='utf-8')
        expected = re.findall(r'^#print axioms (\S+)\s*$', (ROOT / 'Audit.lean').read_text(encoding='utf-8'), re.M)
        found = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text))
        no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", text)
        for name_no_axioms in no_axioms:
            found[name_no_axioms] = ''
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        names_match = set(found) == set(expected) and len(expected) == len(set(expected))
        lists = {k: [a.strip() for a in v.split(',') if a.strip()] for k, v in found.items()}
        standard_only = all(set(v) <= allowed for v in lists.values())
        audit = dict(expected_declarations=expected, reported_axioms=lists,
                     declaration_names_match=names_match, standard_axioms_only=standard_only)
        print(text, end='', flush=True)
    unchanged = save()
    print(f'{name}: exit {p.returncode}; {records[-1]["elapsed_seconds"]:.3f}s', flush=True)
    if p.returncode:
        raise SystemExit(p.returncode)
    if not unchanged:
        raise SystemExit('Source or configuration changed during verification.')
    if name == 'axioms' and not (audit['declaration_names_match'] and audit['standard_axioms_only']):
        raise SystemExit('Named-axiom audit failed.')
print('Whole project build and separate named-axiom audit passed.', flush=True)
