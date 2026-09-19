"""Separate internal E336 replay, using only the existing pinned dependency cache."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def without_comments_strings(text):
    output = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                output.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif in_string:
            if text[i] == '\\':
                i += 2
            elif text[i] == '"':
                in_string = False
                i += 1
            else:
                output.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            while i < len(text) and text[i] != '\n':
                i += 1
        elif text[i] == '"':
            in_string = True
            i += 1
        else:
            output.append(text[i])
            i += 1
    assert depth == 0 and not in_string
    return ''.join(output)


parser = argparse.ArgumentParser()
parser.add_argument('--lean', default='lean')
parser.add_argument('--resume', help='Reuse successful unchanged proof compilation; rerun review sources only')
args = parser.parse_args()
project = Path(__file__).resolve().parent
public = project / 'review-a'
lean_path = Path(shutil.which(args.lean) or args.lean).resolve()
lake_path = lean_path.with_name('lake.exe' if os.name == 'nt' else 'lake')
assert lean_path.is_file() and lake_path.is_file()
environment = os.environ.copy()
environment['PATH'] = str(lean_path.parent) + os.pathsep + environment.get('PATH', '')
environment['MATHLIB_NO_CACHE_ON_UPDATE'] = '1'

manifest_file = project / 'lake-manifest.json'
manifest = json.loads(manifest_file.read_text(encoding='utf-8'))
assert len(manifest['packages']) == 9
package_checks = {}
for package in manifest['packages']:
    package_dir = project / '.lake/packages' / package['name']
    def git(*arguments):
        return subprocess.run(['git', *arguments], cwd=package_dir, check=True,
                              capture_output=True, text=True, encoding='utf-8').stdout.strip()
    actual = git('rev-parse', 'HEAD')
    tracked = git('status', '--porcelain', '--untracked-files=no')
    assert actual == package['rev'], package['name']
    assert not tracked, package['name']
    package_checks[package['name']] = {
        'expected_revision': package['rev'], 'actual_revision': actual,
        'git_tree_sha1': git('rev-parse', 'HEAD^{tree}'),
        'tracked_sources_clean': True,
        'config_file': package['configFile'],
        'config_sha256': sha256(package_dir / package['configFile']),
    }

env_query = subprocess.run(
    [str(lake_path), 'env', sys.executable, '-c', 'import os;print(os.environ["LEAN_PATH"])'],
    cwd=project, env=environment, capture_output=True, text=True, encoding='utf-8', check=True)
dependencies = [str((project / value).resolve())
                for value in env_query.stdout.strip().split(os.pathsep)
                if '.lake/packages' in value.replace('\\', '/')]
assert len(dependencies) == 9
review = Path(args.resume).resolve() if args.resume else Path(
    tempfile.mkdtemp(prefix='review-a-fresh-', dir=project))
previous = json.loads((review / 'receipt.json').read_text(encoding='utf-8')) if args.resume else None
environment['LEAN_PATH'] = os.pathsep.join([str(review)] + dependencies)
environment.pop('LEAN_SRC_PATH', None)
sources = ['E336Defs.lean', 'E336Padding.lean', 'E336Necessity.lean',
           'E336Differences.lean', 'E336Criterion.lean']
source_hashes = {}
declarations = []
declaration_pattern = r'(?m)^(?:noncomputable )?(?:def|theorem|lemma|structure|abbrev)\s+([\w.]+)'
for name in sources:
    data = (project / name).read_bytes()
    source_hashes[name] = hashlib.sha256(data).hexdigest()
    (review / name).write_bytes(data)
    clean = without_comments_strings(data.decode('utf-8'))
    assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', clean), name
    assert 'skipKernelTC' not in clean
    declarations.extend('E336.' + match for match in re.findall(declaration_pattern, clean))
assert len(declarations) == len(set(declarations)) == 34
audit_data = (public / 'Audit.lean').read_bytes()
(review / 'Audit.lean').write_bytes(audit_data)
review_names = ['E336InternalReview.' + name for name in
               re.findall(declaration_pattern, without_comments_strings(audit_data.decode('utf-8')))]
assert len(review_names) == 12
names = declarations + review_names
axiom_source = 'import Audit\n\n' + '\n'.join('#print axioms ' + name for name in names) + '\n'
for destination in [public, review]:
    (destination / 'AxiomAudit.lean').write_text(axiom_source, encoding='utf-8')

if previous:
    assert previous['source_sha256'] == source_hashes
    assert [entry['source'] for entry in previous['commands'][:len(sources)]] == sources
    assert all(entry['exit_code'] == 0 for entry in previous['commands'][:len(sources)])
    assert all((review / (Path(name).stem + '.olean')).is_file() for name in sources)
commands = previous['commands'][:len(sources)] if previous else []
compiled = True
for source in ([] if previous else sources) + ['Audit.lean', 'AxiomAudit.lean']:
    arguments = ['-s', '65536', '-DwarningAsError=true', '-o', Path(source).stem + '.olean', source]
    start = time.monotonic()
    result = subprocess.run([str(lean_path), *arguments], cwd=review, env=environment,
                            capture_output=True, text=True, encoding='utf-8')
    commands.append({'source': source, 'arguments': arguments, 'exit_code': result.returncode,
                     'elapsed_seconds': round(time.monotonic()-start, 3),
                     'stdout': result.stdout, 'stderr': result.stderr})
    (review / 'compile-checkpoint.json').write_text(json.dumps({
        'source_sha256': source_hashes, 'commands': commands,
    }, indent=2), encoding='utf-8')
    print(source, 'exit', result.returncode, flush=True)
    if result.returncode:
        print(result.stdout, result.stderr, flush=True)
        compiled = False
        break

unchanged = all(sha256(project / source) == digest for source, digest in source_hashes.items())
axioms = {}
if compiled:
    output = commands[-1]['stdout']
    for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        axioms[name] = [value.strip() for value in values.split(',') if value.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        axioms[name] = []
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
axioms_ok = set(axioms) == set(names) and all(set(values) <= allowed for values in axioms.values())
version = subprocess.run([str(lean_path), '--version'], capture_output=True,
                         text=True, encoding='utf-8', check=True).stdout.strip()
assert '4.19.0' in version
receipt = {
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'success': compiled and unchanged and axioms_ok,
    'review_kind': 'Internal same-team AI semantic review and separate fresh local-module replay',
    'reviewer_role': 'Authored E336Defs, E336Padding and E336Necessity; did not author '
                    'E336Differences or E336Criterion. Not external human review.',
    'lean_version': version, 'lean_executable_sha256': sha256(lean_path),
    'manifest_sha256': sha256(manifest_file),
    'toolchain_file_sha256': sha256(project / 'lean-toolchain'),
    'checked_dependency_revisions': {name: info['actual_revision'] for name, info in package_checks.items()},
    'dependency_checks': package_checks,
    'source_sha256': source_hashes,
    'sources_unchanged_after_review': unchanged,
    'audit_source_sha256': {name: sha256(public / name) for name in ['Audit.lean', 'AxiomAudit.lean']},
    'import_isolation': {
        'fresh_local_olean_directory': True, 'excluded_project_build_path': True,
        'dependency_library_paths_count': len(dependencies),
        'dependency_caches_reused_not_rebuilt': True,
        'core_toolchain_and_dependency_oleans_remain_trusted': True,
    },
    'proof_declarations_audited': declarations,
    'typed_review_checks': review_names,
    'axiom_results': axioms,
    'axiom_allowlist': sorted(allowed),
    'all_axiom_audits_passed': axioms_ok,
    'commands': commands,
}
(review / 'receipt.json').write_text(json.dumps(receipt, indent=2), encoding='utf-8')
if receipt['success']:
    (public / 'receipt.json').write_text(json.dumps(receipt, indent=2), encoding='utf-8')
print('RECEIPT', review / 'receipt.json', flush=True)
print('SUCCESS', receipt['success'], 'PROOF_AUDITS', len(declarations),
      'REVIEW_CHECKS', len(review_names), flush=True)
raise SystemExit(0 if receipt['success'] else 1)
