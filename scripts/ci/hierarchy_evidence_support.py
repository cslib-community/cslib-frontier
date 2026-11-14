"""Fail-closed controls for disposable hierarchy evidence; no Lean invocation here."""
from pathlib import Path
import re
import shutil

LOCAL = "attribute [local fun_prop] ComputableInPolyTime.fst' ComputableInPolyTime.snd' in"
# Disposable declarations live in the source namespace, before its first LOCAL.
# Mathlib FunProp/Theorems.lean appends (rather than deduplicates) both entry kinds.
HELPER = """
meta initialize hierarchyEvidence5530Baseline : IO.Ref (Array Nat) ← IO.mkRef #[]

private meta def hierarchyEvidence5530Counts : Lean.MetaM (Array Nat) := do
  let mut counts := #[]
  for n in [``ComputableInPolyTime.fst', ``ComputableInPolyTime.snd'] do
    let count ← match (← Mathlib.Meta.FunProp.getTheoremFromConst n) with
      | .lam t => do
        let ts ← Mathlib.Meta.FunProp.getLambdaTheorems t.funPropName t.thmArgs.type
        pure (ts.filter (· == t)).size
      | .function t => do
        let ts ← Mathlib.Meta.FunProp.getTheoremsForFunction t.funOrigin.name t.funPropName
        pure (ts.filter (· == t)).size
      | _ => throwError "HIERARCHY_UNSUPPORTED_ATTRIBUTE_KIND"
    counts := counts.push count
  return counts

"""
BASELINE = """run_cmd Lean.Elab.Command.liftTermElabM do
  let counts ← hierarchyEvidence5530Counts
  hierarchyEvidence5530Baseline.set counts
  IO.println s!"HIERARCHY_ATTRIBUTE_COUNTS {scope} baseline {counts[0]!} {counts[1]!}"

"""
PROBE = """
  run_tac
    let baseline ← hierarchyEvidence5530Baseline.get
    let counts ← hierarchyEvidence5530Counts
    IO.println s!"HIERARCHY_ATTRIBUTE_COUNTS {scope} inside {counts[0]!} {counts[1]!}"
    unless baseline.size == 2 && counts == baseline.map (· + 1) do
      throwError "HIERARCHY_ATTRIBUTE_MISSING"
    Lean.logInfo "HIERARCHY_ATTRIBUTE_PRESENT"
"""


def instrument(source, negative=False):
    # Reject attributes outside the explicitly inspected contract instead of silently
    # calling a partial scan exhaustive. These sources have no attribute-like comments.
    attrs = [line.strip() for line in source.splitlines()
             if '@[' in line or line.lstrip().startswith('attribute ')]
    assert all(a in ('@[expose] public section', LOCAL) for a in attrs), attrs
    count = attrs.count(LOCAL)
    pattern = re.escape(LOCAL) + r'(.*?private theorem\s+\w+.*?:= by)'
    scope = 0

    def replace(m):
        nonlocal scope
        scope += 1
        # Replace only the scope placeholder: Lean's interpolation braces stay literal.
        baseline = BASELINE.replace('{scope}', str(scope))
        probe = PROBE.replace('{scope}', str(scope))
        return (HELPER if scope == 1 else '') + baseline + ('' if negative else LOCAL) + m[1] + probe

    result, changed = re.subn(pattern, replace, source, flags=re.S)
    assert changed == count, (changed, count)
    return result, count


def restore_snapshot(source, destination):
    # Lake's artifact cache supplies read-only files. Unlink destinations before copying;
    # never chmod a cache inode, and never write through a cache hard link/symlink.
    source, destination = Path(source), Path(destination)
    for src in source.rglob('*'):
        if src.is_file():
            dst = destination / src.relative_to(source)
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.unlink(missing_ok=True)
            shutil.copyfile(src, dst)


def attribute_control_passed(returncode, log, count, negative=False):
    """Count emitted messages, excluding source echoes in unrelated diagnostics."""
    if negative:
        missing = re.findall(
            r"^.+:\d+:\d+: error: HIERARCHY_ATTRIBUTE_MISSING$", log, flags=re.M)
        return returncode != 0 and len(missing) == count
    present = sum(line.strip() == "HIERARCHY_ATTRIBUTE_PRESENT" for line in log.splitlines())
    return returncode == 0 and present == count


def registration_counts(log):
    """Only standalone raw records count; diagnostic source echoes are excluded."""
    return [dict(scope=int(scope), phase=phase, counts=[int(a), int(b)])
            for scope, phase, a, b in re.findall(
                r"^HIERARCHY_ATTRIBUTE_COUNTS (\d+) (baseline|inside) (\d+) (\d+)$",
                log, flags=re.M)]


def scoped_control_passed(returncode, log, count, negative=False):
    if not attribute_control_passed(returncode, log, count, negative):
        return False
    records = registration_counts(log)
    if [(r['scope'], r['phase']) for r in records] != [
            (scope, phase) for scope in range(1, count + 1) for phase in ('baseline', 'inside')]:
        return False
    for baseline, inside in zip(records[::2], records[1::2]):
        # Omitting only LOCAL must leave both counts unchanged, not merely fail
        # some unrelated assertion or yield an arbitrary non-unit delta.
        delta = 0 if negative else 1
        if inside['counts'] != [n + delta for n in baseline['counts']]:
            return False
    return True


def attribute_matrix_complete(records, variants, modules):
    expected = {(v, m, n): scopes for v in variants for m, scopes in modules.items()
                for n in (False, True)}
    actual = {(r['variant'], r['module'], r['negative']): r['scopes'] for r in records}
    return (len(records) == len(expected) and actual == expected
            and all(r['passed'] for r in records))
