"""Build the pinned project and record its actual named-axiom audit.

Run after preparing the dependencies: python verify.py --label my-check
This checks the project; it does not rebuild or independently verify Mathlib.
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

sources = {p.name: digest(p) for p in ROOT.glob('*.lean')}
env = os.environ.copy()
env.pop('LEAN_PATH', None)
env.pop('LEAN_SRC_PATH', None)
lake = Path(args.lake)
if lake.is_absolute():
    env['PATH'] = str(lake.parent) + os.pathsep + env.get('PATH', '')
records = []
for name, command in [
    ('build', [args.lake, 'build']),
    ('axioms', [args.lake, 'env', 'lean', '-DwarningAsError=true', 'Audit.lean']),
]:
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    t0 = time.monotonic()
    p = subprocess.run(command, cwd=ROOT, env=env, capture_output=True)
    elapsed = time.monotonic() - t0
    (out / (name + '-stdout.txt')).write_bytes(p.stdout)
    (out / (name + '-stderr.txt')).write_bytes(p.stderr)
    record = dict(name=name, started_utc=start, command=command,
                  exit_code=p.returncode, elapsed_seconds=elapsed,
                  stdout_sha256=hashlib.sha256(p.stdout).hexdigest(),
                  stderr_sha256=hashlib.sha256(p.stderr).hexdigest())
    records.append(record)
    print(p.stdout.decode('utf-8', errors='replace'), end='', flush=True)
    print(p.stderr.decode('utf-8', errors='replace'), end='', flush=True)
    (out / 'result.json').write_text(json.dumps(dict(
        source_sha256=sources, records=records,
        source_unchanged=all(digest(ROOT / k) == v for k, v in sources.items()),
        dependency_trust='Uses the pinned available Mathlib build; not a fresh dependency build.'
    ), indent=2) + '\n', encoding='utf-8')
    if p.returncode:
        raise SystemExit(p.returncode)
if not all(digest(ROOT / k) == v for k, v in sources.items()):
    raise SystemExit('Source changed during verification.')
print('Build and axiom audit completed successfully.', flush=True)
