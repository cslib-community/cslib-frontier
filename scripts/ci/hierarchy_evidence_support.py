"""Fail-closed controls for disposable hierarchy evidence; no Lean invocation here."""
from pathlib import Path
import re
import shutil

LOCAL = "attribute [local fun_prop] ComputableInPolyTime.fst' ComputableInPolyTime.snd' in"
PROBE = '''
  run_tac
    for n in [``ComputableInPolyTime.fst', ``ComputableInPolyTime.snd'] do
      let found ← match (← Mathlib.Meta.FunProp.getTheoremFromConst n) with
        | .lam t => do
          let ts ← Mathlib.Meta.FunProp.getLambdaTheorems t.funPropName t.thmArgs.type
          pure (ts.contains t)
        | .function t => do
          let ts ← Mathlib.Meta.FunProp.getTheoremsForFunction t.funOrigin.name t.funPropName
          pure (ts.contains t)
        | _ => throwError "HIERARCHY_UNSUPPORTED_ATTRIBUTE_KIND"
      unless found do throwError "HIERARCHY_ATTRIBUTE_MISSING"
    Lean.logInfo "HIERARCHY_ATTRIBUTE_PRESENT"
'''


def instrument(source, negative=False):
    # Reject attributes outside the explicitly inspected contract instead of silently
    # calling a partial scan exhaustive. These sources have no attribute-like comments.
    attrs = [line.strip() for line in source.splitlines()
             if '@[' in line or line.lstrip().startswith('attribute ')]
    assert all(a in ('@[expose] public section', LOCAL) for a in attrs), attrs
    count = attrs.count(LOCAL)
    pattern = re.escape(LOCAL) + r'(.*?private theorem\s+\w+.*?:= by)'
    result, changed = re.subn(pattern, lambda m: ('' if negative else LOCAL) + m[1] + PROBE,
                             source, flags=re.S)
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
