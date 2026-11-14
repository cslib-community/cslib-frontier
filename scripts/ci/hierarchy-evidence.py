"""Disposable hosted comparison for #4073. DO NOT MERGE. No local execution."""
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import time
import tomllib
from hierarchy_evidence_support import (attribute_matrix_complete, instrument, registration_counts,
                                        restore_snapshot, scoped_control_passed)

VARIANTS = {
    'before': '39b11c9de',
    '5494': '55c7e0dabb4fab4ecf9deb9373d502ba4dfb231f',
    '5498': 'b50dee8e88b6b0d6154654d2e30e918d3a1acefd',
    '5510': '28c3dffb82a3102754689396c2b7609036ba60aa',
}
ROOT = 'CslibFrontier/Computability/Complexity/Classes/Hierarchy/'
CLIENTS = ['NondeterministicTime', 'NondeterministicExponentialTime']
MODULES = ['LazyDiagonalBounds', 'LazyDiagonalVerifier', *CLIENTS]
OUT = Path(os.environ['RUNNER_TEMP']) / 'hierarchy-evidence'
OUT.mkdir(parents=True, exist_ok=True)

def run(args, **kw):
    print('+', ' '.join(map(str, args)), flush=True)
    return subprocess.run(args, check=True, **kw)

def flatten(table, prefix=''):
    for name, value in table.items():
        key = f'{prefix}.{name}' if prefix else name
        if isinstance(value, dict):
            yield from flatten(value, key)
        else:
            yield key, value

# Only disposable hosted checkout changes; no worktrees/shared object manipulation.
resolved = {k: subprocess.check_output(['git', 'rev-parse', v], text=True).strip()
            for k, v in VARIANTS.items()}
for config in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
    contents = [subprocess.check_output(['git', 'show', f'{sha}:{config}']) for sha in resolved.values()]
    assert all(c == contents[0] for c in contents), config
metadata = dict(commits=resolved, warmups=1, repetitions=5,
                cpu=Path('/proc/cpuinfo').read_text(),
                limits='900s each. Whole-module startup/import/elaboration/output wall time; setup and prerequisite builds excluded. No heartbeat overrides. Per-revision warm imports; reverse variant order each repetition. Raw expression serialization is conservative, not definitional equality. Exported kind/body checks expose preservation. Scoped fun_prop registry probes and negative controls run separately after timing; not a generic attribute audit.')
(OUT / 'metadata.json').write_text(json.dumps(metadata, indent=2))
setups = {}
flags = []
# Prepare every variant once before timing. Preserve independent outputs by copying
# the built root library; dependency packages stay fixed throughout the experiment.
for label, sha in resolved.items():
    run(['git', 'restore', '--source', sha, '--', 'CslibFrontier', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'])
    run(['scripts/cache/ensure.sh'])
    dest = OUT / label
    dest.mkdir()
    modules = [ROOT + n + '.lean' for n in MODULES if Path(ROOT + n + '.lean').exists()]
    run(['lake', 'build', '--wfail', '--iofail', *[p[:-5].replace('/', '.') for p in modules]])
    if label == 'before':
        control = 'HierarchyAttributeControl'
        run(['lake', 'env', 'lean', '-o', f'.lake/build/lib/lean/{control}.olean',
             'scripts/ci/HierarchyAttributeControl.lean'])
        result = run(['lake', 'env', 'lean', '--run', 'scripts/ci/HierarchyDeclarations.lean',
                      control], capture_output=True, text=True)
        (OUT / 'expose-controls.jsonl').write_text(result.stdout)
        controls = {r['name']: r for line in result.stdout.splitlines()
                    for r in [json.loads(line)]}
        assert controls['hierarchyExposedControl']['kind'] == 'def'
        assert controls['hierarchyExposedControl']['exposedBody']
        assert controls['hierarchyHiddenControl']['kind'] != 'def'
        assert not controls['hierarchyHiddenControl']['exposedBody']
    for name in CLIENTS:
        p = ROOT + name + '.lean'
        result = run(['lake', 'setup-file', p], capture_output=True, text=True)
        json.loads(result.stdout)
        setup = dest / (name + '.setup.json')
        setup.write_text(result.stdout)
        (dest / (name + '.setup.stderr')).write_text(result.stderr)
        setups[label, name] = setup
    attrs = {}
    for p in modules:
        source = Path(p).read_bytes()
        instrument(source.decode())  # Reject any attribute outside the audited family.
        (dest / Path(p).name).write_bytes(source)
        attrs[p] = [line.strip() for line in source.decode().splitlines()
                    if '@[' in line or line.lstrip().startswith('attribute ')]
    (dest / 'attribute-syntax.json').write_text(json.dumps(attrs, indent=2))
    with (dest / 'declarations.jsonl').open('w') as out:
        run(['lake', 'env', 'lean', '--run', 'scripts/ci/HierarchyDeclarations.lean',
             *[p[:-5].replace('/', '.') for p in modules]], stdout=out)
    # Reflinks when supported; otherwise independent copies on this runner only.
    snapshot = dest / 'lib' / Path(ROOT)
    snapshot.mkdir(parents=True)
    for module in MODULES:
        for output in (Path('.lake/build/lib/lean') / ROOT).glob(module + '.*'):
            if output.is_file():
                run(['cp', '-a', '--reflink=auto', str(output), str(snapshot / output.name)])
    flags = [f'-D{k}={str(v).lower()}' for k, v in flatten(tomllib.loads(Path('lakefile.toml').read_text())['leanOptions'])]

# Exact strings intentionally retain binders, universe names and all resource expressions.
# A mismatch is a finding requiring review, never normalized away silently.
def declarations(label):
    return {r['name']: r for line in (OUT / label / 'declarations.jsonl').read_text().splitlines()
            if line.strip() for r in [json.loads(line)]}
base = declarations('before')
assert len(base) == 19, 'Unexpected baseline export inventory; inspect declarations'
comparison = {}
for label in list(resolved)[1:]:
    after = declarations(label)
    comparison[label] = dict(existing=len(base), missing=sorted(base.keys() - after.keys()),
                            changed=[n for n in base.keys() & after.keys() if base[n] != after[n]],
                            added=sorted(after.keys() - base.keys()))
(OUT / 'preservation.json').write_text(json.dumps(comparison, indent=2))
rows = []
for rep in range(6):
    labels = list(resolved)
    if rep % 2:
        labels.reverse()
    for label in labels:
        sha = resolved[label]
        run(['git', 'restore', '--source', sha, '--', 'CslibFrontier'])
        # Setup JSON names root outputs here; restore that variant's compiled imports.
        restore_snapshot(OUT / label / 'lib', '.lake/build/lib/lean')
        for name in CLIENTS:
            p = ROOT + name + '.lean'
            dest = OUT / f'{name}-{label}-{rep}'
            dest.mkdir()
            cmd = ['lake', 'env', 'lean', '--setup', str(setups[label, name]), *flags,
                   '-o', str(dest / 'result.olean'), '-i', str(dest / 'result.ilean'), p]
            start = time.perf_counter()
            with (dest / 'lean.log').open('w') as log:
                result = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, timeout=900)
            row = dict(module=name, variant=label, sha=sha, repetition=rep, warmup=rep == 0,
                       seconds=time.perf_counter()-start, returncode=result.returncode,
                       source_sha256=hashlib.sha256(Path(p).read_bytes()).hexdigest(), command=cmd)
            rows.append(row)
            (OUT / 'timings.json').write_text(json.dumps(rows, indent=2))
            print(json.dumps(row), flush=True)
            if result.returncode:
                raise SystemExit(result.returncode)
summary = []
for name in CLIENTS:
    for label in resolved:
        xs = [r['seconds'] for r in rows if r['module'] == name and r['variant'] == label and not r['warmup']]
        summary.append(dict(module=name, variant=label, samples=xs, median=statistics.median(xs), minimum=min(xs), maximum=max(xs)))
(OUT / 'summary.json').write_text(json.dumps(summary, indent=2))
# Check the actual scoped registry during separate, untimed re-elaborations.
# Negative controls remove only the local attribute, retaining the same probe/proof.
attribute_results = []
for label, sha in resolved.items():
    run(['git', 'restore', '--source', sha, '--', 'CslibFrontier'])
    restore_snapshot(OUT / label / 'lib', '.lake/build/lib/lean')
    for name in CLIENTS:
        path = Path(ROOT + name + '.lean')
        original = path.read_text()
        for negative in [False, True]:
            source, count = instrument(original, negative=negative)
            assert count == (1 if name == 'NondeterministicTime' else 2)
            path.write_text(source)
            tag = f'{name}-{label}-attribute-{"negative" if negative else "positive"}'
            dest = OUT / tag
            dest.mkdir()
            (dest / path.name).write_text(source)
            cmd = ['lake', 'env', 'lean', '--setup', str(setups[label, name]), *flags, str(path)]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=900)
            log = result.stdout + result.stderr
            (dest / 'lean.log').write_text(log)
            passed = scoped_control_passed(result.returncode, log, count, negative)
            attribute_results.append(dict(variant=label, module=name, negative=negative,
                                          scopes=count, passed=passed, command=cmd,
                                          returncode=result.returncode, counts=registration_counts(log)))
            (OUT / 'compiled-attributes.json').write_text(json.dumps(attribute_results, indent=2))
            if not passed:
                raise SystemExit(f'Attribute control failed: {tag}; inspect lean.log')
        path.write_text(original)
assert attribute_matrix_complete(attribute_results, resolved, dict(zip(CLIENTS, [1, 2])))
# Library snapshots are not evidence and are too large for an artifact. Keep all actual
# measured outputs, declarations, sources, setup files and commands instead.
import shutil
for label in resolved:
    shutil.rmtree(OUT / label / 'lib')
if any(v['missing'] or v['changed'] for v in comparison.values()):
    raise SystemExit('Compiled preservation mismatches; inspect preservation.json')
