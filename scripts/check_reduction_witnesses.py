#!/usr/bin/env python3
"""Point a reviewer at explicit security reductions that have no efficiency certificate (#5293).

Usage: python3 scripts/check_reduction_witnesses.py [--base REF | --all | --report]
           [--list [PREFIX]] [--advisory] [--update-baseline] [--no-build-check]
           [--baseline FILE]

This is an advisory search for the rule "Security theorems" in AGENTS.md: each reduction is an
explicit program with an efficiency witness proved from the adversary's certificate, an `isPPT_…`
or `isOraclePPT_…` lemma or the model's certificate. On a pull request it prints what it finds in
the changed modules and does not fail. `scripts/check_security_premises.py` finds a theorem that
assumes the reduction's efficiency; this scan finds a reduction that has no certificate at all.
A hardness assumption stated for a fixed efficient adversary class cannot be applied to such a
reduction, because Lean asks for the certificate there, so an uncertified reduction is a place to
look and not by itself a defect.

`scripts/SecurityPremises.lean --reductions` reads the built `.olean` files of the library, with
CSLib's as context, so it sees elaborated statements. A *reduction* is a definition under
`CslibFrontier/Crypto` or in the namespace `Cslib.Crypto` that finally yields a program (a
`ProbComp`, `OracleComp` or `PMF`, or a structure of these such as an adversary) and that a
public theorem uses on the bounding side of an advantage bound, applied to a program variable
that the bounded side mentions: `B` in `Adv(scheme, A) ≤ Adv(problem, B A)`, or in
`Adv(scheme, A) = Adv(problem, B A)`. An *efficiency witness* is a theorem, private ones
included, that concludes an efficiency certificate mentioning the reduction: a predicate named
`IsPPT…`, `IsOraclePPT…`, `IsTidyOraclePPT…`, `ComputableIn…`, `ComputableTidilyIn…`,
`IsPolyTime…`, `IsEfficient…` or `Efficient…`. A query bound is not one. A reduction is also
certified when it is an `abbrev` of certified reductions, or when a certified definition applies
it (the word-level program that runs it). The Lean file's docstring gives the exact rules and the
known gaps.

`scripts/reduction_witnesses_baseline.json` records the uncertified reductions that are known,
one per line, as `{reduction: {"module": source path, "kind": "gap" | "via_certified_program" |
"exempt", "why": note}}`. A `gap` is a reduction without a witness; its `why` names the issue
that tracks it. An `exempt` entry needs none, and its `why` says which case it is: the bound is
information-theoretic (it holds for unbounded adversaries and no computational theorem applies an
assumption to the reduction), or the definition is not a reduction, such as a scheme or protocol
built from a component, which the checker cannot tell apart. An entry is a note that the item is
known, so that the report does not repeat it. It is not a clearance, the number of entries of a
kind does not measure progress, and moving an entry from one kind to another proves nothing.

A `via_certified_program` entry records a typed reduction, often a per-instance step, that a
certified program runs. Between `kind` and `why` it names four declarations: `"program"` X, the
certified program; `"certificate"` Y, X's efficiency witness; `"equality"` E, a theorem stating that
X's law or evaluation equals the reduction's; and `"headline"` H, the asymptotic theorem that
applies the hardness assumption to X. X, Y and H must be public. E may be private, named without its
private prefix. The entry records the file that holds E, so that a reviewer can open it:
`"equality_module"`, written after `equality`, when E is not in the entry's `module`; a private E is
looked up in that file first, so a declaration of the same name elsewhere is not taken for it.
`scripts/SecurityPremises.lean --reductions` verifies that all four exist in the compiled modules;
that X is a definition that yields a program; that Y is a theorem whose conclusion is an efficiency
certificate, as recognized above, that mentions X; that E is a theorem whose conclusion, after its
`∀`s and premises, is an equation `a = b`, not of propositions, with X in one side and the reduction
in the other, such as an equality of `PMF`s or `eval`s or `Game.advantage … = …`; and that H is a
theorem other than Y and E whose conclusion makes a negligibility or advantage claim (directly or
through the notions it states) and whose statement mentions X or Y or, failing that, whose proof
term does (together with the auxiliary proofs Lean generates under H's name). This checker then
compares E's module with the recorded file. The conditions under which E holds (its hypotheses, and
the arguments and branches at which it is stated) are for the reviewer to read: the entry's `why`
states them by hand, and the pass does not check them. E's conclusion must be an equation: a bound
(`≤`, `<`) or a simulation predicate does not link X to the reduction, and such a step stays a
`gap`, as do an equation that covers only one world (the ideal experiment, say) and a reduction
whose program no headline consumes yet. `--report` prints, for each entry, whether H mentions X or Y
in its statement or only in its proof. A missing, renamed, misplaced or private-where-public
declaration fails the check. An entry is enforced in the modules of its reduction and of the four
declarations, and in every module while one of them is missing, since the change that renamed or
deleted it can be in any module. The status supplements review and does not replace it: the pass
checks names and the shape of statements, not that Y assumes only the adversary's certificate, that
E holds at the arguments where H uses X, or that H is the headline the reduction's result needs. The
entry names the declarations so that a reviewer can open them.

An entry for a generic reduction whose equality holds only at the instance that the headline uses
adds `"scope": "instance"` and `"consumers"`, after `headline`: an object from each *referrer* of
the reduction outside its module to its tag. The baseline is keyed on the reduction, so without the
pinned list a later theorem that applied an assumption through the reduction at another instance
would pass unseen. A referrer is a public declaration that names the reduction in its statement or
proof, directly, through the declarations Lean generates under a name, or through private
declarations; only the reduction's module and the modules that import it, directly or through other
modules, are read. The tags are `headline`, a theorem on the headline's proof path (the headline
itself, or a constant of the library that its statement and proof use, transitively); `concrete`, a
theorem elsewhere, an exact bound that applies no assumption; and `reduction`, a definition that
uses the reduction. The Lean pass fails when the pinned consumers differ from the referrers, so a
new one must be classified, or the entry made a `gap`; when a tag does not hold; and when a
referring theorem other than the headline, in the reduction's module or outside it, is not
*concrete*: a premise (instance arguments included) is headed by a named assumption, or a premise or
the conclusion makes a negligibility claim, directly or through Prop-valued definitions unfolded at
most five times, an alias for the whole statement included. This checker fails when a definition
among the referrers, tagged or in the reduction's module, has no efficiency witness of its own and
no baseline entry: a `gap` or `exempt` entry, which it keeps even when no theorem states a bound
with the definition, or when the definition is a reduction certified only through another definition
(`tracked_definitions`). Being mentioned in a certified definition's body, which certifies a
reduction, does not count as a witness here. A definition with a witness of its own needs no entry,
and an entry for it is stale. So the baseline accounts for every definition that uses the reduction;
that does not establish that every headline downstream of such a definition has its own certificate
or via entry. The referrers' modules join the modules where the entry is enforced. The pass finds a
referrer by name, and a public declaration stops the search, so it does not see a theorem that
reaches the reduction only through another public declaration (a theorem that consumes the headline,
or one about a definition that wraps the reduction), nor a premise that assumes a bound without
`Negligible` or a named assumption, and it does not judge whether a `headline` consumer uses the
reduction at the instance that the equality covers; review does. `--update-baseline` also adds `gap`
entries for the unrecorded uncertified definitions and keeps the recorded ones. The summary prints
the gap, via, instance-scoped via and exempt counts separately.

The modules that a change touches are those it adds, modifies or deletes, against the merge base
of `--base` (default `origin/main`) and the working tree, as `scripts/check_changed_files.py`
computes them. A reduction belongs to the module that defines it and to the modules of the
theorems that state bounds with it. A change that adds or modifies the checker or the baseline
covers every module.

Pull requests run `--base REF --advisory`. It prints the differences from the baseline in the
touched modules (an uncertified reduction without an entry, an entry that no longer matches an
uncertified reduction, an entry without a `why`, a `via_certified_program` entry that the Lean
pass does not verify), emits a GitHub `::notice` when running in Actions, and succeeds. So where
the paragraphs above say that the pass or this checker fails, it reports a difference, which
fails only under the enforcement below. A difference is a prompt for the reviewer to look, not a
failure. The scan still fails when it cannot run or the baseline is malformed, because that is a
broken tool and not a finding. `--report` prints every difference in every module and always
succeeds; merge groups and pushes to `main` run it.

Without `--advisory`, `--base` and `--all` enforce, which CI no longer does and which remains for
local use: a difference in a touched module (`--all`: in any module) fails, and differences in
other modules are printed but do not fail, since a change can cause them without touching those
modules, for example by deleting a witness.

`--list [PREFIX]` ignores the baseline and prints every reduction defined in the modules under
the path PREFIX with its certificate. `--update-baseline` adds `gap` entries with an empty `why`
for the unrecorded uncertified reductions of the touched modules and removes their stale entries;
fill in each `why`, which the checker's unit tests require of the committed baseline. It never
writes a `via_certified_program` entry.

This is a post-build check: it needs the outputs of `lake build CslibFrontier`, and refuses stale
ones unless `--no-build-check` is given.

The scan supplements review: a clean run is not evidence that a reduction is efficient in the
sense its theorem needs. A witness is recognized by the constants its conclusion mentions, so
the check does not judge whether the witness assumes only the adversary's certificate, covers the
oracles the reduction simulates, or is the one the asymptotic theorem uses. It does not see a
reduction written inline in a bound, a bound without an advantage-named constant, a simulator or
extractor on the bounded side or outside any advantage bound, an attack, or an uncertified setup
sampler or scheme algorithm.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_encoding_readability as cer  # noqa: E402
import check_hardness_assumptions as cha  # noqa: E402
import check_security_premises as csp  # noqa: E402
import lean_outputs as lo  # noqa: E402

BASELINE = ROOT / "scripts/reduction_witnesses_baseline.json"
# A change to the checker or its baseline covers every module, so that its own CI run shows
# whether the whole library still matches.
CHECKER_FILES = frozenset({csp.TOOL, "scripts/check_reduction_witnesses.py",
                           "scripts/reduction_witnesses_baseline.json"})
UPDATE = "python3 scripts/check_reduction_witnesses.py --update-baseline"
RULE = "AGENTS.md, Security theorems"
KINDS = ("gap", "via_certified_program", "exempt")
VIA = "via_certified_program"
# The declarations that a `via_certified_program` entry names.
VIA_FIELDS = ("program", "certificate", "equality", "headline")
# The file that holds the equality, when it is not the entry's `module`.
EQUALITY_MODULE = "equality_module"
# An entry whose equality holds only at the headline's instance: `"scope": "instance"`, with the
# reduction's consumers outside its module pinned by name, each with one of `TAGS`.
SCOPE, INSTANCE, CONSUMERS = "scope", "instance", "consumers"
TAGS = ("headline", "concrete", "reduction")
# The fields of an entry of each kind, in the order they are written; `EQUALITY_MODULE` is
# optional, and so are `SCOPE` and `CONSUMERS`, which come together.
FIELDS = {"gap": ("module", "kind", "why"), "exempt": ("module", "kind", "why"),
          VIA: ("module", "kind", "program", "certificate", "equality", EQUALITY_MODULE,
                "headline", SCOPE, CONSUMERS, "why")}
OPTIONAL = frozenset({EQUALITY_MODULE, SCOPE, CONSUMERS})


@dataclass(frozen=True)
class Reduction:
    """A reduction: its name, defining module path and line, the theorems that state an advantage
    bound with it and their module paths, and its certificate: `direct`, `abbrev` or `wrapper`
    with the certifying declarations, or the empty string when it has none."""
    name: str
    path: str
    line: int
    theorems: tuple[str, ...]
    stated_in: tuple[str, ...]
    certificate: str
    certified_by: tuple[str, ...]

    def paths(self) -> set[str]:
        return {self.path, *self.stated_in}


@dataclass(frozen=True)
class ViaCheck:
    """The Lean pass's verdict on a `via_certified_program` entry: its problems, where the
    headline mentions the program or its certificate (`statement`, `proof`, or the empty string),
    the paths of the modules of the declarations it found (for an entry scoped to one instance,
    those of the reduction's referrers too), the path of the equality's module (or the empty
    string), and the names it did not find. For an entry scoped to one instance, also the
    reduction's referrers outside its module, the uncertified definitions among all its referrers
    with their paths, and the certified ones."""
    problems: tuple[str, ...]
    headline_at: str
    paths: tuple[str, ...]
    equality_path: str
    missing: tuple[str, ...]
    referrers: tuple[str, ...] = ()
    definitions: tuple[tuple[str, str], ...] = ()
    certified_definitions: tuple[str, ...] = ()


def parse(output: str) -> tuple[dict[str, Reduction], dict]:
    """The reductions and the summary line of `scripts/SecurityPremises.lean --reductions`."""
    reductions, summary = {}, {}
    for line in output.splitlines():
        row = json.loads(line)
        if "v" in row:
            continue
        if "n" not in row:
            summary = row
            continue
        reductions[row["n"]] = Reduction(
            row["n"], csp.module_path(row["m"]), row["l"], tuple(row["t"]),
            tuple(csp.module_path(m) for m in row["tm"]), row["k"], tuple(row["w"]))
    return reductions, summary


def parse_checks(output: str) -> dict[str, ViaCheck]:
    """The verdicts of `scripts/SecurityPremises.lean --reductions` on `via_certified_program`
    entries, by reduction."""
    checks = {}
    for line in output.splitlines():
        row = json.loads(line)
        if "v" in row:
            checks[row["v"]] = ViaCheck(tuple(row["p"]), row["at"],
                                        tuple(csp.module_path(m) for m in row["vm"]),
                                        csp.module_path(row["em"]) if row["em"] else "",
                                        tuple(row["missing"]), tuple(row.get("refs", ())),
                                        tuple((d["n"], csp.module_path(d["m"]))
                                              for d in row.get("defs", ())),
                                        tuple(row.get("cdefs", ())))
    return checks


def module_name(path: str) -> str:
    """The module of a source path: `CslibFrontier.A.B` for `CslibFrontier/A/B.lean`."""
    return path.removesuffix(".lean").replace("/", ".")


def via_requests(baseline: dict[str, dict]) -> list[str]:
    """The reader's input lines that ask it to verify the `via_certified_program` entries: the
    reduction and its module, the program, the certificate, the equality and its module, and the
    headline; for an entry scoped to one instance, then `instance` and each pinned consumer as
    `tag:name`."""
    return ["\t".join(["via", name, module_name(entry["module"]), entry["program"],
                       entry["certificate"], entry["equality"],
                       module_name(entry.get(EQUALITY_MODULE, entry["module"])), entry["headline"],
                       *([INSTANCE, *(f"{tag}:{consumer}" for consumer, tag
                                      in sorted(entry[CONSUMERS].items()))]
                         if SCOPE in entry else [])])
            for name, entry in sorted(baseline.items()) if entry["kind"] == VIA]


def scan(root: Path, build_dir: Path, upstream: Path, baseline: dict[str, dict] | None = None
         ) -> tuple[dict[str, Reduction], dict[str, ViaCheck]]:
    """Run the Lean reader over every library module, with CSLib as context, and have it verify
    the `via_certified_program` entries of `baseline`."""
    lines = (cha.context_modules(upstream) + csp.library_modules(root)
             + via_requests(baseline or {}))
    out = subprocess.run(["lake", "env", "lean", "--run", csp.TOOL, str(build_dir),
                          "--reductions"], cwd=root, input="\n".join(lines) + "\n",
                         capture_output=True, text=True)
    if out.returncode:
        sys.exit(f"{csp.TOOL} failed:\n{out.stderr or out.stdout}")
    reductions, summary = parse(out.stdout)
    if summary.get("missing"):
        sys.exit(f"build outputs are missing for {len(summary['missing'])} module(s), e.g. "
                 f"{summary['missing'][0]}; run `lake build CslibFrontier` first")
    return reductions, parse_checks(out.stdout)


def uncertified(reductions: dict[str, Reduction]) -> dict[str, Reduction]:
    return {name: r for name, r in reductions.items() if not r.certificate}


def valid_entry(value: object) -> bool:
    """Whether a baseline value has the fields of its kind, the optional ones aside, as strings,
    a `via_certified_program` entry names its four declarations, and an entry scoped to one
    instance has `"scope": "instance"` with its consumers, an object from names to `TAGS`."""
    if not isinstance(value, dict) or value.get("kind") not in KINDS:
        return False
    fields = set(FIELDS[value["kind"]])
    consumers = value.get(CONSUMERS, {})
    return (fields - OPTIONAL <= set(value) <= fields
            and (SCOPE in value) == (CONSUMERS in value)
            and all(isinstance(v, str) for f, v in value.items() if f != CONSUMERS)
            and all(value[f].strip() for f in (*VIA_FIELDS, EQUALITY_MODULE) if f in value)
            and value.get(SCOPE, INSTANCE) == INSTANCE
            and isinstance(consumers, dict)
            and all(isinstance(n, str) and n.strip() and t in TAGS for n, t in consumers.items()))


def load_baseline(path: Path) -> dict[str, dict]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not (isinstance(data, dict) and all(valid_entry(v) for v in data.values())):
        sys.exit(f"{path}: expected a JSON object from reduction names to "
                 '{"module": path, "kind": "gap" or "exempt", "why": justification} or '
                 f'{{"module": path, "kind": "{VIA}", "program": declaration, '
                 '"certificate": declaration, "equality": declaration, '
                 f'optionally "{EQUALITY_MODULE}": path, "headline": declaration, '
                 f'optionally "{SCOPE}": "{INSTANCE}" and "{CONSUMERS}": {{declaration: '
                 f'{" or ".join(repr(t) for t in TAGS)}}}, "why": justification}}')
    return data


def baseline_text(entries: dict[str, dict]) -> str:
    """One entry per line, grouped by module, so concurrent edits rarely touch the same lines."""
    order = sorted(entries, key=lambda n: (entries[n]["module"], n))
    def value(entry: dict, f: str) -> object:
        return dict(sorted(entry[f].items())) if f == CONSUMERS else entry[f]
    lines = [f" {json.dumps(n, ensure_ascii=False)}: "
             + json.dumps({f: value(entries[n], f) for f in FIELDS[entries[n]["kind"]]
                           if f in entries[n]}, ensure_ascii=False)
             for n in order]
    return "{\n" + ",\n".join(lines) + ("\n" if lines else "") + "}\n"


def tracked_definitions(checks: dict[str, ViaCheck]) -> dict[str, str]:
    """The definitions without a witness of their own that use a reduction of an instance-scoped
    entry, with their paths. Each needs a baseline entry of its own, which stands even when no
    theorem states an advantage bound with the definition, or when the definition is a reduction
    certified only through another definition."""
    return {name: path for check in checks.values() for name, path in check.definitions}


@dataclass(frozen=True)
class Problems:
    """Differences from the baseline: unrecorded uncertified reductions, entries that no longer
    match as `(reduction, entry, reason)`, entries without a justification, and
    `via_certified_program` entries that the Lean pass does not verify as `(reduction, entry,
    reasons)`."""
    new: list[Reduction]
    stale: list[tuple[str, dict, str]]
    unjustified: list[str]
    invalid: list[tuple[str, dict, str]] = field(default_factory=list)

    def __bool__(self) -> bool:
        return bool(self.new or self.stale or self.unjustified or self.invalid)


def compare(reductions: dict[str, Reduction], baseline: dict[str, dict],
            paths: set[str] | None, checks: dict[str, ViaCheck] | None = None) -> Problems:
    """The differences in the modules `paths` (every module when `None`), with the Lean pass's
    verdicts `checks` on the `via_certified_program` entries."""
    def scoped(*candidates: str) -> bool:
        return paths is None or bool(paths.intersection(candidates))
    checks = checks or {}
    tracked = tracked_definitions(checks)
    certified_definitions = {d for check in checks.values() for d in check.certified_definitions}
    new, stale, unjustified, invalid = [], [], [], []
    for name, r in sorted(uncertified(reductions).items(),
                          key=lambda i: (i[1].path, i[1].line, i[0])):
        if scoped(*r.paths()) and name not in baseline:
            new.append(r)
    for name, entry in sorted(baseline.items(), key=lambda i: (i[1]["module"], i[0])):
        r = reductions.get(name)
        via = entry["kind"] == VIA
        check = checks.get(name) if via else None
        # A declaration the pass cannot find may have been renamed or deleted in any module.
        everywhere = via and (check is None or bool(check.missing))
        if not (everywhere or scoped(entry["module"], entry.get(EQUALITY_MODULE, ""),
                                     *(r.paths() if r else ()),
                                     *(check.paths if check else ()))):
            continue
        if r is None:
            if name in certified_definitions:
                stale.append((name, entry, "has an efficiency witness of its own, as a definition "
                                           "that uses an instance-scoped reduction; it needs no "
                                           "entry"))
            elif name not in tracked:
                stale.append((name, entry, "no theorem states an advantage bound with it"))
            elif tracked[name] != entry["module"]:
                stale.append((name, entry, f"now defined in {tracked[name]}"))
        elif r.certificate and name not in tracked:
            # A reduction certified only through another definition (`wrapper`, `abbrev`) keeps
            # its entry while an instance-scoped entry needs it.
            stale.append((name, entry, f"certified ({r.certificate}: {', '.join(r.certified_by)})"))
        elif r.path != entry["module"]:
            stale.append((name, entry, f"now defined in {r.path}"))
        if not entry["why"].strip():
            unjustified.append(name)
        if via and check is None:
            invalid.append((name, entry, "the Lean pass did not verify it"))
        elif check is not None:
            reasons = list(check.problems)
            recorded = entry.get(EQUALITY_MODULE, entry["module"])
            if check.equality_path and check.equality_path != recorded:
                reasons.append(f"equality `{entry['equality']}` is in {check.equality_path}, not "
                               f"{recorded}; record its file as `{EQUALITY_MODULE}`, or omit "
                               "that field when it is the entry's `module`")
            # A definition that uses the reduction is recorded unless it has a witness of its own,
            # so that the baseline accounts for every definition that runs it.
            reasons += [f"`{d}` is a definition that uses `{name}` without an efficiency witness "
                        "of its own but has no baseline entry; record it (a `gap` or `exempt` "
                        "entry), or make this entry a `gap`"
                        for d, _ in check.definitions if d not in baseline]
            if reasons:
                invalid.append((name, entry, "; ".join(reasons)))
    return Problems(new, stale, unjustified, invalid)


def outside(everywhere: Problems, here: Problems) -> Problems:
    """The differences of `everywhere` that are not in `here`."""
    return Problems([p for p in everywhere.new if p not in here.new],
                    [p for p in everywhere.stale if p not in here.stale],
                    [p for p in everywhere.unjustified if p not in here.unjustified],
                    [p for p in everywhere.invalid if p not in here.invalid])


def checker_changed(root: Path, ref: str) -> bool:
    """Whether the change adds or modifies the checker or its baseline."""
    added, modified = cer.ccf.changed_files(root, ref)
    return bool(CHECKER_FILES.intersection(added + modified))


def describe(r: Reduction) -> list[str]:
    shown = ", ".join(f"`{t}`" for t in r.theorems[:3])
    more = f" and {len(r.theorems) - 3} more" if len(r.theorems) > 3 else ""
    return [f"  {r.path}:{r.line}: {r.name}", f"    bound stated by {shown}{more}"]


def report(problems: Problems, advisory: bool = False) -> str:
    """The differences as text: as failures to fix, or with `advisory` as prompts for a reviewer."""
    out = []
    if problems.new:
        out += ["Explicit reductions without an efficiency witness, which the baseline does not "
                f"record ({RULE}). Each is a prompt to look, not a failure: check whether an "
                "asymptotic theorem applies a hardness assumption through the reduction, which "
                "needs a certificate for it or for a program that runs it (`isPPT_…`, "
                "`isOraclePPT_…`). An information-theoretic bound, or a definition that is not a "
                f"reduction, needs none. `{UPDATE}` records an item as known." if advisory else
                "Explicit reductions without an efficiency witness. Each reduction needs a "
                f"certificate proved from the adversary's ({RULE}): prove `isPPT_…` or "
                "`isOraclePPT_…` for it (as `isPPT_elGamalMsgToDDHDistinguisher` does), or for the "
                "word-level program that runs it, and apply the hardness assumption through that "
                "lemma. If the bound is information-theoretic, or the definition is not a "
                "reduction (a scheme or protocol built from a component), add a baseline entry "
                f"with `\"kind\": \"exempt\"` and a justification (`{UPDATE}`, then fill in "
                "`why`).", ""]
        for r in problems.new:
            out += describe(r)
    if problems.stale:
        out += ([""] if out else []) + [
            f"Baseline entries that no longer match an uncertified reduction (`{UPDATE}` drops "
            "them):" if advisory else
            "Baseline entries that no longer match an uncertified reduction; remove or update "
            f"them in the same change (`{UPDATE}`):"]
        out += [f"  {entry['module']}: {name} ({reason})" for name, entry, reason in problems.stale]
    if problems.unjustified:
        out += ([""] if out else []) + ["Baseline entries without a justification (`why`):"]
        out += [f"  {name}" for name in problems.unjustified]
    if problems.invalid:
        out += ([""] if out else []) + [
            f"`{VIA}` entries that the Lean pass does not verify:" if advisory else
            f"`{VIA}` entries that the Lean pass does not verify. Fix the entry, or make it a "
            "`gap` until the certified program, its certificate, an equation between the "
            "program's law and the reduction's, and a headline that consumes the program all "
            "exist:"]
        out += [f"  {entry['module']}: {name}: {reasons}"
                for name, entry, reasons in problems.invalid]
    return "\n".join(out)


def via_listing(baseline: dict[str, dict], checks: dict[str, ViaCheck]) -> str:
    """For each `via_certified_program` entry, where its headline mentions the program or the
    certificate."""
    out = []
    for name, entry in sorted(baseline.items(), key=lambda i: (i[1]["module"], i[0])):
        if entry["kind"] != VIA:
            continue
        check = checks.get(name)
        where = (f"in its {check.headline_at}" if check and check.headline_at
                 else "nowhere the pass could verify")
        scope = ""
        if SCOPE in entry:
            tags = Counter(entry[CONSUMERS].values())
            scope = (f"; scoped to one instance, with {len(entry[CONSUMERS])} pinned consumer(s) ("
                     + ", ".join(f"{tags[t]} {t}" for t in TAGS) + ")")
        out.append(f"  {entry['module']}: {name}: headline `{entry['headline']}` uses the program "
                   f"{where}{scope}")
    return "\n".join([f"`{VIA}` entries:", *out] if out else [])


def listing(reductions: dict[str, Reduction], prefix: str) -> str:
    chosen = sorted((r for r in reductions.values() if r.path.startswith(prefix)),
                    key=lambda r: (r.path, r.line, r.name))
    out = []
    for r in chosen:
        out += describe(r)
        out.append(f"    certified {r.certificate}: {', '.join(r.certified_by[:3])}"
                   if r.certificate else "    no efficiency witness")
    return "\n".join(out + [f"{len(chosen)} reduction(s), "
                            f"{len(uncertified({r.name: r for r in chosen}))} without an "
                            "efficiency witness"])


def update(reductions: dict[str, Reduction], baseline: dict[str, dict], paths: set[str] | None,
           tracked: dict[str, str] | None = None) -> dict[str, dict]:
    """The baseline with the entries of the modules `paths` (all when `None`) matching the
    uncertified reductions and the `tracked` definitions (`tracked_definitions`): existing entries
    are kept with their kinds, declarations and justifications, new entries are gaps with an empty
    justification."""
    def scoped(*candidates: str) -> bool:
        return paths is None or bool(paths.intersection(candidates))
    unrecorded = uncertified(reductions)
    tracked = {name: path for name, path in (tracked or {}).items() if name not in unrecorded}
    updated = {}
    for name, entry in baseline.items():
        r = reductions.get(name)
        if not scoped(entry["module"], *(r.paths() if r else ()), tracked.get(name, "")):
            updated[name] = entry
    for name, path in tracked.items():
        if scoped(path):
            old = baseline.get(name)
            updated[name] = ({**old, "module": path} if old
                             else {"module": path, "kind": "gap", "why": ""})
    for name, r in uncertified(reductions).items():
        if scoped(*r.paths()):
            old = baseline.get(name)
            updated[name] = ({**old, "module": r.path} if old
                             else {"module": r.path, "kind": "gap", "why": ""})
    return updated


def status(reductions: dict[str, Reduction], baseline: dict[str, dict], scope_text: str) -> str:
    kinds = Counter(entry["kind"] for entry in baseline.values())
    scoped = sum(entry["kind"] == VIA and SCOPE in entry for entry in baseline.values())
    return (f"{len(reductions)} reduction(s), {len(uncertified(reductions))} without an efficiency "
            f"witness; {len(baseline)} baseline entries ({kinds['gap']} gap(s), "
            f"{kinds[VIA] - scoped} via certified program, {scoped} instance-scoped via, "
            f"{kinds['exempt']} exempt), checking {scope_text}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument("--base", default="origin/main",
                       help="check the modules changed since the merge base with this revision "
                            "(default origin/main)")
    scope.add_argument("--all", action="store_true", help="check every module")
    scope.add_argument("--report", action="store_true",
                       help="report every difference from the baseline and succeed")
    scope.add_argument("--list", nargs="?", const="", metavar="PREFIX",
                       help="ignore the baseline and list every reduction defined in the modules "
                            "under the path PREFIX with its certificate; always succeeds")
    parser.add_argument("--advisory", action="store_true",
                        help="print the differences in the checked modules as prompts for a "
                             "reviewer and succeed, instead of failing on them; pull requests "
                             "run `--base REF --advisory`")
    parser.add_argument("--update-baseline", action="store_true",
                        help="record the uncertified reductions of the checked modules")
    parser.add_argument("--no-build-check", action="store_true",
                        help="do not check that the build outputs are current")
    parser.add_argument("--baseline", type=Path, default=BASELINE)
    args = parser.parse_args(argv)
    if (args.report or args.advisory or args.list is not None) and args.update_baseline:
        parser.error("--report, --advisory and --list do not combine with --update-baseline")
    if not args.no_build_check and not lo.lake_outputs_current(("CslibFrontier",)):
        sys.exit("build outputs are missing or stale; run `lake build CslibFrontier` "
                 "(or pass --no-build-check)")
    baseline = (load_baseline(args.baseline)
                if args.list is None and args.baseline.exists() else {})
    reductions, checks = scan(ROOT, lo.DEFAULT_BUILD_DIR, cha.UPSTREAM_BUILD, baseline)
    if args.list is not None:
        print(listing(reductions, args.list))
        return 0
    whole = args.all or args.report
    if not whole and checker_changed(ROOT, args.base):
        whole = True
        print("This change edits the reduction-witness checker or its baseline, so every module "
              f"is {'reported' if args.advisory else 'enforced'}.")
    paths = None if whole else cer.touched_modules(ROOT, args.base)
    scope_text = "every module" if whole else f"{len(paths)} changed module(s)"
    if args.update_baseline:
        updated = update(reductions, baseline, paths, tracked_definitions(checks))
        args.baseline.write_text(baseline_text(updated), encoding="utf-8")
        empty = sorted(n for n, e in updated.items() if not e["why"].strip())
        print(f"Wrote {args.baseline} for {scope_text}."
              + (f" Fill in `why` for: {', '.join(empty)}." if empty else ""))
        return 0
    problems = compare(reductions, baseline, paths, checks)
    summary = status(reductions, baseline, scope_text)
    if args.report:
        if problems:
            print(report(problems, advisory=True) + "\n")
        vias = via_listing(baseline, checks)
        if vias:
            print(vias + "\n")
        print(f"{summary}; report only, nothing is enforced.")
        return 0
    elsewhere = (outside(compare(reductions, baseline, None, checks), problems)
                 if paths is not None else None)
    if args.advisory:
        if problems:
            print(report(problems, advisory=True) + "\n")
            if os.environ.get("GITHUB_ACTIONS") == "true":
                count = (len(problems.new) + len(problems.stale) + len(problems.unjustified)
                         + len(problems.invalid))
                print(f"::notice title=Reduction witnesses (advisory)::{count} difference(s) "
                      "from the baseline in the modules this change touches, for the reviewer "
                      "to open; see the step log. Nothing is enforced.")
        more = (len(elsewhere.new) + len(elsewhere.stale) + len(elsewhere.unjustified)
                + len(elsewhere.invalid) if elsewhere else 0)
        print(f"{summary}; advisory, nothing is enforced."
              + (f" {more} more difference(s) in modules this change does not touch; `--report` "
                 "lists them." if more else ""))
        return 0
    if elsewhere:
        print("Not enforced: differences from the baseline in modules this change does not touch. "
              "They fail the next change to those modules. A change can cause them without "
              "touching those modules, for example by deleting a witness; if this one did, fix "
              "them here.\n\n" + report(elsewhere) + "\n")
        if os.environ.get("GITHUB_ACTIONS") == "true":
            count = (len(elsewhere.new) + len(elsewhere.stale) + len(elsewhere.unjustified)
                     + len(elsewhere.invalid))
            print(f"::notice title=Reduction witnesses::{count} difference(s) from the baseline in "
                  "modules this change does not touch; see the step log.")
    if problems:
        print(report(problems), file=sys.stderr)
        return 1
    print(f"{summary}; every uncertified reduction is recorded.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
