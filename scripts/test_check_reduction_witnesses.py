"""Unit tests for scripts/check_reduction_witnesses.py, on synthetic reader output and, when Lean
is available, on a compiled module (`CompiledFixtureTests`) read by
`scripts/SecurityPremises.lean --reductions`."""

from __future__ import annotations

import contextlib
import io
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_reduction_witnesses as c  # noqa: E402

CERTIFIED = "Cslib.Crypto.ElGamal.toDDHDistinguisher"
UNCERTIFIED = "Cslib.Crypto.Schnorr.forkingReduction"
EXEMPT = "Cslib.Crypto.Signature.toScheme"
ELGAMAL_PATH = "CslibFrontier/Crypto/ElGamal.lean"
SCHNORR_PATH = "CslibFrontier/Crypto/Schnorr.lean"
SIGNATURE_PATH = "CslibFrontier/Crypto/Signature.lean"
CLIENT_PATH = "CslibFrontier/Crypto/SchnorrClient.lean"


def row(name: str, module: str, line: int, theorems: list[str], stated_in: list[str],
        certificate: str = "", certified_by: list[str] | None = None) -> str:
    """A line of the reader's output."""
    return json.dumps({"n": name, "m": module, "l": line, "t": theorems, "tm": stated_in,
                       "k": certificate, "w": certified_by or []})


OUTPUT = "\n".join([
    row(CERTIFIED, "CslibFrontier.Crypto.ElGamal", 10, ["Cslib.Crypto.ElGamal.advantage_le"],
        ["CslibFrontier.Crypto.ElGamal"], "direct", ["Cslib.Crypto.ElGamal.isPPT_toDDH"]),
    row(UNCERTIFIED, "CslibFrontier.Crypto.Schnorr", 20,
        ["Cslib.Crypto.Schnorr.succProbability_le", "Cslib.Crypto.SchnorrClient.bound"],
        ["CslibFrontier.Crypto.Schnorr", "CslibFrontier.Crypto.SchnorrClient"]),
    row(EXEMPT, "CslibFrontier.Crypto.Signature", 30, ["Cslib.Crypto.Signature.advantage_eq"],
        ["CslibFrontier.Crypto.Signature"]),
    json.dumps({"theorems": 4, "modules": 4, "missing": []}),
])


def entry(path: str, kind: str = "gap", why: str = "tracked in #5293 section 2") -> dict:
    return {"module": path, "kind": kind, "why": why}


BASELINE = {UNCERTIFIED: entry(SCHNORR_PATH),
            EXEMPT: entry(SIGNATURE_PATH, "exempt", "not a reduction: a typed scheme")}

# A typed reduction that a certified program runs, and the modules of the declarations it names.
VIA_REDUCTION = "Cslib.Crypto.Garbling.stepReduction"
GARBLING_PATH = "CslibFrontier/Crypto/Garbling.lean"
WORD_PATH = "CslibFrontier/Crypto/GarblingWord.lean"
VIA_ENTRY = {"module": GARBLING_PATH, "kind": c.VIA,
             "program": "Cslib.Crypto.GarblingWord.wordReduction",
             "certificate": "Cslib.Crypto.GarblingWord.isOraclePPT_wordReduction",
             "equality": "Cslib.Crypto.GarblingWord.eval_run_wordReduction",
             "equality_module": WORD_PATH,
             "headline": "Cslib.Crypto.GarblingWord.prvSim",
             "why": "per-instance step that the certified word reduction runs on every label "
                    "table"}


WORD_MODULE = "CslibFrontier.Crypto.GarblingWord"
# The same entry scoped to one instance, with the reduction's consumers outside its module pinned.
WRAPPER = "Cslib.Crypto.GarblingWord.wrappedStep"
SCOPED_ENTRY = {**{key: value for key, value in VIA_ENTRY.items() if key != "why"},
                "scope": "instance",
                "consumers": {"Cslib.Crypto.GarblingWord.prvSim": "headline",
                              "Cslib.Crypto.Garbling.otherInstance_le": "concrete",
                              WRAPPER: "reduction"},
                "why": "generic step whose equality holds only at the word instance"}


def check_row(problems: list[str] | None = None, missing: list[str] | None = None,
              equality_module: str = "CslibFrontier.Crypto.GarblingWord",
              definitions: list[tuple[str, str]] | None = None,
              certified: list[str] | None = None) -> str:
    """A line of the reader's output for the request of `VIA_ENTRY`, with the uncertified
    definitions among the reduction's referrers as `(name, module)` and the certified ones."""
    return json.dumps({"v": VIA_REDUCTION, "p": problems or [], "at": "" if problems else "proof",
                       "vm": ["CslibFrontier.Crypto.Garbling", "CslibFrontier.Crypto.GarblingWord"],
                       "em": equality_module, "missing": missing or [], "refs": [],
                       "defs": [{"n": n, "m": m} for n, m in definitions or []],
                       "cdefs": certified or []})


VIA_OUTPUT = "\n".join([
    row(VIA_REDUCTION, "CslibFrontier.Crypto.Garbling", 40,
        ["Cslib.Crypto.Garbling.advantage_le_sum"], ["CslibFrontier.Crypto.Garbling"]),
    check_row(), OUTPUT])


class ParseTests(unittest.TestCase):
    def test_rows_and_summary(self) -> None:
        reductions, summary = c.parse(OUTPUT)
        self.assertEqual(summary["theorems"], 4)
        self.assertEqual(reductions[CERTIFIED].path, ELGAMAL_PATH)
        self.assertEqual(reductions[CERTIFIED].certificate, "direct")
        self.assertEqual(reductions[UNCERTIFIED].line, 20)
        self.assertEqual(reductions[UNCERTIFIED].paths(), {SCHNORR_PATH, CLIENT_PATH})
        self.assertEqual(set(c.uncertified(reductions)), {UNCERTIFIED, EXEMPT})


class CompareTests(unittest.TestCase):
    def setUp(self) -> None:
        self.reductions, _ = c.parse(OUTPUT)

    def test_certified_and_recorded_reductions_pass(self) -> None:
        self.assertFalse(c.compare(self.reductions, BASELINE, None))

    def test_an_uncertified_reduction_fails_only_in_scope(self) -> None:
        problems = c.compare(self.reductions, {EXEMPT: BASELINE[EXEMPT]}, None)
        self.assertEqual([r.name for r in problems.new], [UNCERTIFIED])
        self.assertFalse(c.compare(self.reductions, {EXEMPT: BASELINE[EXEMPT]}, {ELGAMAL_PATH}))

    def test_a_reduction_belongs_to_the_modules_that_state_its_bounds(self) -> None:
        # A change to a client that states a bound with the reduction enforces it too.
        problems = c.compare(self.reductions, {EXEMPT: BASELINE[EXEMPT]}, {CLIENT_PATH})
        self.assertEqual([r.name for r in problems.new], [UNCERTIFIED])

    def test_an_exempt_reduction_needs_its_entry(self) -> None:
        problems = c.compare(self.reductions, {UNCERTIFIED: BASELINE[UNCERTIFIED]}, None)
        self.assertEqual([r.name for r in problems.new], [EXEMPT])

    def test_stale_entries_fail_in_their_module(self) -> None:
        # A reduction that gained its witness, and one that no theorem bounds any more.
        baseline = {**BASELINE, CERTIFIED: entry(ELGAMAL_PATH),
                    "Cslib.Crypto.Gone.reduction": entry("CslibFrontier/Crypto/Gone.lean")}
        stale = c.compare(self.reductions, baseline, None).stale
        self.assertEqual([(name, reason) for name, _, reason in stale], [
            (CERTIFIED, "certified (direct: Cslib.Crypto.ElGamal.isPPT_toDDH)"),
            ("Cslib.Crypto.Gone.reduction", "no theorem states an advantage bound with it")])
        self.assertFalse(c.compare(self.reductions, baseline, {SCHNORR_PATH}))
        self.assertEqual(len(c.compare(self.reductions, baseline, {ELGAMAL_PATH}).stale), 1)

    def test_moved_reduction_needs_its_entry_updated(self) -> None:
        baseline = {**BASELINE, UNCERTIFIED: entry("CslibFrontier/Crypto/Old.lean")}
        problems = c.compare(self.reductions, baseline, {SCHNORR_PATH})
        self.assertEqual([(name, reason) for name, _, reason in problems.stale],
                         [(UNCERTIFIED, f"now defined in {SCHNORR_PATH}")])

    def test_entries_need_a_justification(self) -> None:
        baseline = {**BASELINE, UNCERTIFIED: entry(SCHNORR_PATH, why="  ")}
        self.assertEqual(c.compare(self.reductions, baseline, None).unjustified, [UNCERTIFIED])


class ViaTests(unittest.TestCase):
    """`via_certified_program` entries, on synthetic verdicts of the Lean pass."""

    def setUp(self) -> None:
        self.reductions, _ = c.parse(VIA_OUTPUT)
        self.baseline = {**BASELINE, VIA_REDUCTION: VIA_ENTRY}

    def checks(self, *problems: str, missing: list[str] | None = None) -> dict[str, c.ViaCheck]:
        return c.parse_checks(check_row(list(problems), missing))

    def test_parse_reads_verdicts_apart_from_reductions(self) -> None:
        self.assertEqual(c.parse_checks(VIA_OUTPUT), {VIA_REDUCTION: c.ViaCheck(
            (), "proof", (GARBLING_PATH, WORD_PATH), WORD_PATH, ())})
        self.assertEqual(set(c.uncertified(self.reductions)), {UNCERTIFIED, EXEMPT, VIA_REDUCTION})

    def test_requests_name_the_declarations_and_where_to_find_private_ones(self) -> None:
        self.assertEqual(c.via_requests(self.baseline), ["\t".join([
            "via", VIA_REDUCTION, "CslibFrontier.Crypto.Garbling", VIA_ENTRY["program"],
            VIA_ENTRY["certificate"], VIA_ENTRY["equality"], "CslibFrontier.Crypto.GarblingWord",
            VIA_ENTRY["headline"]])])
        # Without `equality_module`, a private equality is looked up in the entry's module.
        unrecorded = {key: value for key, value in VIA_ENTRY.items() if key != "equality_module"}
        self.assertIn(f"{VIA_ENTRY['equality']}\tCslibFrontier.Crypto.Garbling\t"
                      f"{VIA_ENTRY['headline']}", c.via_requests({VIA_REDUCTION: unrecorded})[0])
        self.assertEqual(c.via_requests(BASELINE), [])

    def test_a_verified_entry_passes(self) -> None:
        self.assertFalse(c.compare(self.reductions, self.baseline, None, self.checks()))

    def test_the_entry_records_the_file_of_the_equality(self) -> None:
        # Without `equality_module`, the equality must be in the entry's `module`.
        unrecorded = {key: value for key, value in VIA_ENTRY.items() if key != "equality_module"}
        for value, equality_module in ((unrecorded, "CslibFrontier.Crypto.GarblingWord"),
                                       (VIA_ENTRY, "CslibFrontier.Crypto.Other")):
            checks = c.parse_checks(check_row(equality_module=equality_module))
            invalid = c.compare(self.reductions, {**BASELINE, VIA_REDUCTION: value}, None,
                                checks).invalid
            self.assertEqual(len(invalid), 1)
            self.assertIn(f"equality `{VIA_ENTRY['equality']}` is in "
                          f"{equality_module.replace('.', '/')}.lean, not ", invalid[0][2])
        checks = c.parse_checks(check_row(equality_module="CslibFrontier.Crypto.Garbling"))
        self.assertFalse(c.compare(self.reductions, {**BASELINE, VIA_REDUCTION: unrecorded}, None,
                                   checks))

    def test_a_renamed_declaration_fails_in_every_module(self) -> None:
        checks = self.checks("equality `Cslib.Crypto.GarblingWord.eval_run_wordReduction` does "
                             "not exist", missing=[VIA_ENTRY["equality"]])
        for paths in (None, {SIGNATURE_PATH}):
            invalid = c.compare(self.reductions, self.baseline, paths, checks).invalid
            self.assertEqual([(name, reason) for name, _, reason in invalid], [
                (VIA_REDUCTION, "equality `Cslib.Crypto.GarblingWord.eval_run_wordReduction` "
                                "does not exist")])

    def test_an_inequality_or_an_unrelated_headline_fails(self) -> None:
        for problem in ("equality `E` is not an equation (its conclusion is headed by "
                        "`LE.le`); a step linked by a bound or a simulation stays a `gap`",
                        "headline `H` mentions neither `X` nor `Y` in its statement or proof"):
            problems = c.compare(self.reductions, self.baseline, None, self.checks(problem))
            self.assertEqual([reason for _, _, reason in problems.invalid], [problem])

    def test_a_failing_entry_is_enforced_in_the_modules_of_its_declarations(self) -> None:
        checks = self.checks("headline `H` mentions neither `X` nor `Y` in its statement or proof")
        for paths in ({GARBLING_PATH}, {WORD_PATH}):
            self.assertTrue(c.compare(self.reductions, self.baseline, paths, checks).invalid)
        self.assertFalse(c.compare(self.reductions, self.baseline, {SIGNATURE_PATH}, checks))
        everywhere = c.compare(self.reductions, self.baseline, None, checks)
        here = c.compare(self.reductions, self.baseline, {SIGNATURE_PATH}, checks)
        self.assertEqual(len(c.outside(everywhere, here).invalid), 1)

    def test_an_entry_the_pass_did_not_verify_fails(self) -> None:
        invalid = c.compare(self.reductions, self.baseline, {SIGNATURE_PATH}).invalid
        self.assertEqual([(name, reason) for name, _, reason in invalid],
                         [(VIA_REDUCTION, "the Lean pass did not verify it")])

    def test_an_instance_scoped_request_pins_the_consumers(self) -> None:
        request = c.via_requests({VIA_REDUCTION: SCOPED_ENTRY})[0].split("\t")
        self.assertEqual(request[8:], ["instance",
                                       "concrete:Cslib.Crypto.Garbling.otherInstance_le",
                                       "headline:Cslib.Crypto.GarblingWord.prvSim",
                                       f"reduction:{WRAPPER}"])
        # A full entry sends no scope.
        self.assertEqual(len(c.via_requests(self.baseline)[0].split("\t")), 8)

    def test_parse_reads_the_referrers_and_definitions(self) -> None:
        row = json.loads(check_row(definitions=[(WRAPPER, WORD_MODULE)], certified=[CERTIFIED]))
        row["refs"] = ["Cslib.Crypto.GarblingWord.prvSim"]
        check = c.parse_checks(json.dumps(row))[VIA_REDUCTION]
        self.assertEqual((check.referrers, check.definitions, check.certified_definitions),
                         (("Cslib.Crypto.GarblingWord.prvSim",), ((WRAPPER, WORD_PATH),),
                          (CERTIFIED,)))
        # Output without these fields, as for a full entry, reads as empty.
        legacy = {key: value for key, value in row.items() if key not in ("refs", "defs", "cdefs")}
        self.assertEqual(c.parse_checks(json.dumps(legacy))[VIA_REDUCTION].definitions, ())

    def test_an_uncertified_definition_that_uses_the_reduction_needs_an_entry(self) -> None:
        # The wrapper is no reduction: no theorem states an advantage bound with it.
        self.assertNotIn(WRAPPER, self.reductions)
        checks = c.parse_checks(check_row(definitions=[(WRAPPER, WORD_MODULE)]))
        baseline = {**BASELINE, VIA_REDUCTION: SCOPED_ENTRY}
        problems = c.compare(self.reductions, baseline, None, checks)
        self.assertEqual([(name, reason) for name, _, reason in problems.invalid], [
            (VIA_REDUCTION, f"`{WRAPPER}` is a definition that uses `{VIA_REDUCTION}` without an "
                            "efficiency witness of its own but has no baseline entry; record it (a "
                            "`gap` or `exempt` entry), or make this entry a `gap`")])
        # Recorded, as a `gap` or an `exempt` entry, it passes completely: the entry is not stale
        # although no theorem states a bound with the wrapper.
        for kind in ("gap", "exempt"):
            recorded = {**baseline, WRAPPER: entry(WORD_PATH, kind)}
            self.assertFalse(c.compare(self.reductions, recorded, None, checks), kind)
        # The same entry is stale once nothing needs it, or when the wrapper has moved.
        recorded = {**baseline, WRAPPER: entry(WORD_PATH)}
        self.assertEqual([(name, reason) for name, _, reason in
                          c.compare(self.reductions, recorded, None, {}).stale],
                         [(WRAPPER, "no theorem states an advantage bound with it")])
        moved = {**baseline, WRAPPER: entry(GARBLING_PATH)}
        self.assertEqual([(name, reason) for name, _, reason in
                          c.compare(self.reductions, moved, None, checks).stale],
                         [(WRAPPER, f"now defined in {WORD_PATH}")])

    def test_an_uncertified_reduction_that_uses_the_reduction_keeps_its_entry(self) -> None:
        checks = c.parse_checks(check_row(definitions=[(UNCERTIFIED,
                                                        "CslibFrontier.Crypto.Schnorr")]))
        self.assertFalse(c.compare(self.reductions, {**BASELINE, VIA_REDUCTION: SCOPED_ENTRY}, None,
                                   checks))

    def test_a_certified_definition_that_uses_the_reduction_needs_no_entry(self) -> None:
        # A certified wrapper has its own efficiency witness; an entry for it would be stale.
        checks = c.parse_checks(check_row(certified=[WRAPPER]))
        baseline = {**BASELINE, VIA_REDUCTION: SCOPED_ENTRY}
        self.assertFalse(c.compare(self.reductions, baseline, None, checks))
        stale = c.compare(self.reductions, {**baseline, WRAPPER: entry(WORD_PATH)}, None,
                          checks).stale
        self.assertEqual([(name, reason) for name, _, reason in stale], [
            (WRAPPER, "has an efficiency witness of its own, as a definition that uses an "
                      "instance-scoped reduction; it needs no entry")])

    def test_a_reduction_certified_only_through_another_definition_keeps_its_entry(self) -> None:
        # Mentioned in a certified program's body but without a witness of its own, it is still
        # tracked, so its entry stands; with a witness of its own, the entry is stale.
        wrapped = c.Reduction(WRAPPER, WORD_PATH, 50, ("Cslib.Crypto.GarblingWord.bound",),
                              (WORD_PATH,), "wrapper", ("Cslib.Crypto.GarblingWord.program",))
        reductions = {**self.reductions, WRAPPER: wrapped}
        baseline = {**BASELINE, VIA_REDUCTION: SCOPED_ENTRY, WRAPPER: entry(WORD_PATH)}
        tracked = c.parse_checks(check_row(definitions=[(WRAPPER, WORD_MODULE)]))
        self.assertFalse(c.compare(reductions, baseline, None, tracked))
        self.assertEqual(c.update(reductions, baseline, None, c.tracked_definitions(tracked))
                         [WRAPPER], entry(WORD_PATH))
        stale = c.compare(reductions, baseline, None, {}).stale
        self.assertEqual([name for name, _, _ in stale], [WRAPPER])

    def test_update_records_the_tracked_definitions(self) -> None:
        checks = c.parse_checks(check_row(definitions=[(WRAPPER, WORD_MODULE)]))
        baseline = {**BASELINE, VIA_REDUCTION: SCOPED_ENTRY}
        tracked = c.tracked_definitions(checks)
        added = c.update(self.reductions, baseline, None, tracked)
        self.assertEqual(added[WRAPPER], entry(WORD_PATH, "gap", ""))
        kept = c.update(self.reductions, {**baseline, WRAPPER: entry(WORD_PATH, "exempt")}, None,
                        tracked)
        self.assertEqual(kept[WRAPPER], entry(WORD_PATH, "exempt"))
        # Without an instance-scoped entry that needs it, the entry is dropped.
        self.assertNotIn(WRAPPER, c.update(self.reductions, kept, None, {}))

    def test_an_entry_stays_stale_once_the_reduction_is_certified(self) -> None:
        reductions, _ = c.parse(OUTPUT)
        baseline = {**BASELINE, CERTIFIED: {**VIA_ENTRY, "module": ELGAMAL_PATH}}
        checks = {CERTIFIED: c.ViaCheck((), "proof", (ELGAMAL_PATH,), WORD_PATH, ())}
        stale = c.compare(reductions, baseline, None, checks).stale
        self.assertEqual([name for name, _, _ in stale], [CERTIFIED])


class BaselineTests(unittest.TestCase):
    def test_text_round_trips_one_entry_per_line(self) -> None:
        text = c.baseline_text(BASELINE)
        self.assertEqual(json.loads(text), BASELINE)
        self.assertEqual(len(text.splitlines()), len(BASELINE) + 2)
        self.assertEqual(c.baseline_text({}), "{\n}\n")

    def test_via_entries_keep_their_field_order(self) -> None:
        text = c.baseline_text({**BASELINE, VIA_REDUCTION: VIA_ENTRY})
        self.assertEqual(json.loads(text)[VIA_REDUCTION], VIA_ENTRY)
        self.assertEqual(len(text.splitlines()), len(BASELINE) + 3)
        line = next(line for line in text.splitlines() if VIA_REDUCTION in line)
        self.assertEqual(list(json.loads(line.split(": ", 1)[1].rstrip(","))),
                         ["module", "kind", "program", "certificate", "equality",
                          "equality_module", "headline", "why"])

    def test_scoped_entries_keep_their_field_order_and_sort_consumers(self) -> None:
        shuffled = {**SCOPED_ENTRY, "consumers": dict(reversed(SCOPED_ENTRY["consumers"].items()))}
        text = c.baseline_text({**BASELINE, VIA_REDUCTION: shuffled})
        self.assertEqual(json.loads(text)[VIA_REDUCTION], SCOPED_ENTRY)
        line = next(line for line in text.splitlines() if VIA_REDUCTION in line)
        value = json.loads(line.split(": ", 1)[1].rstrip(","))
        self.assertEqual(list(value), ["module", "kind", "program", "certificate", "equality",
                                       "equality_module", "headline", "scope", "consumers", "why"])
        self.assertEqual(list(value["consumers"]), sorted(SCOPED_ENTRY["consumers"]))

    def test_a_scope_needs_its_consumers_and_known_tags(self) -> None:
        unscoped = {key: value for key, value in SCOPED_ENTRY.items() if key != "scope"}
        bad = (unscoped,
               {key: value for key, value in SCOPED_ENTRY.items() if key != "consumers"},
               {**SCOPED_ENTRY, "scope": "global"},
               {**SCOPED_ENTRY, "consumers": [WRAPPER]},
               {**SCOPED_ENTRY, "consumers": {WRAPPER: "exact"}},
               {**SCOPED_ENTRY, "consumers": {" ": "concrete"}},
               {**entry(SCHNORR_PATH), "scope": "instance", "consumers": {}})
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "baseline.json"
            for value in bad:
                path.write_text(json.dumps({UNCERTIFIED: value}))
                with self.assertRaises(SystemExit, msg=value):
                    c.load_baseline(path)
            for value in (SCOPED_ENTRY, {**SCOPED_ENTRY, "consumers": {}}):
                path.write_text(json.dumps({UNCERTIFIED: value}))
                self.assertEqual(c.load_baseline(path), {UNCERTIFIED: value})

    def test_kind_is_gap_via_certified_program_or_exempt(self) -> None:
        bad = (entry(SCHNORR_PATH, "later"),
               {key: value for key, value in VIA_ENTRY.items() if key != "headline"},
               {**VIA_ENTRY, "program": " "},
               {**VIA_ENTRY, "equality_module": ""},
               {**entry(SCHNORR_PATH), "program": VIA_ENTRY["program"]},
               {**entry(SCHNORR_PATH), "equality_module": WORD_PATH})
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "baseline.json"
            for value in bad:
                path.write_text(json.dumps({UNCERTIFIED: value}))
                with self.assertRaises(SystemExit, msg=value):
                    c.load_baseline(path)
            unrecorded = {key: value for key, value in VIA_ENTRY.items()
                          if key != "equality_module"}
            for value in (VIA_ENTRY, unrecorded):
                path.write_text(json.dumps({UNCERTIFIED: value}))
                self.assertEqual(c.load_baseline(path), {UNCERTIFIED: value})

    def test_update_keeps_justifications_and_drops_stale_entries(self) -> None:
        reductions, _ = c.parse(OUTPUT)
        baseline = {EXEMPT: BASELINE[EXEMPT], CERTIFIED: entry(ELGAMAL_PATH),
                    "Cslib.Crypto.Gone.reduction": entry("CslibFrontier/Crypto/Gone.lean")}
        updated = c.update(reductions, baseline, None)
        self.assertEqual(updated, {EXEMPT: BASELINE[EXEMPT],
                                   UNCERTIFIED: entry(SCHNORR_PATH, "gap", "")})
        # Outside the changed modules, entries stay as they are.
        self.assertEqual(c.update(reductions, baseline, {SCHNORR_PATH}),
                         {**baseline, UNCERTIFIED: entry(SCHNORR_PATH, "gap", "")})

    def test_update_keeps_via_entries(self) -> None:
        reductions, _ = c.parse(VIA_OUTPUT)
        baseline = {**BASELINE, VIA_REDUCTION: {**VIA_ENTRY, "module": "CslibFrontier/Old.lean"}}
        self.assertEqual(c.update(reductions, baseline, None),
                         {**BASELINE, VIA_REDUCTION: VIA_ENTRY})


class CheckerChangedTests(unittest.TestCase):
    def test_only_the_checker_and_its_baseline_count(self) -> None:
        for changed, expected in ((["scripts/reduction_witnesses_baseline.json"], True),
                                  (["scripts/SecurityPremises.lean"], True),
                                  (["scripts/check_reduction_witnesses.py"], True),
                                  (["scripts/security_premises_baseline.json"], False),
                                  (["CslibFrontier/Crypto/Schnorr.lean", "AGENTS.md"], False)):
            with mock.patch.object(c.cer.ccf, "changed_files", return_value=(changed, [])):
                self.assertEqual(c.checker_changed(c.ROOT, "origin/main"), expected, changed)


class MainTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.baseline = pathlib.Path(tmp.name) / "baseline.json"
        reductions, _ = c.parse(OUTPUT)
        for patcher in (mock.patch.object(c, "scan", return_value=(reductions, {})),
                        mock.patch.object(c.cer, "touched_modules", return_value={SCHNORR_PATH}),
                        mock.patch.object(c, "checker_changed", return_value=False)):
            patcher.start()
            self.addCleanup(patcher.stop)

    def run_main(self, baseline: dict | None, *args: str) -> tuple[int, str, str]:
        if baseline is not None:
            self.baseline.write_text(c.baseline_text(baseline))
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = c.main(["--no-build-check", "--baseline", str(self.baseline), *args])
        return code, out.getvalue(), err.getvalue()

    def test_pull_request_that_adds_an_uncertified_reduction_fails(self) -> None:
        code, _, err = self.run_main({EXEMPT: BASELINE[EXEMPT]})
        self.assertEqual(code, 1)
        self.assertIn(f"{SCHNORR_PATH}:20: {UNCERTIFIED}", err)
        self.assertIn("bound stated by `Cslib.Crypto.Schnorr.succProbability_le`", err)
        self.assertIn("isPPT_", err)
        self.assertNotIn(EXEMPT, err)
        self.assertNotIn(CERTIFIED, err)

    def test_pull_request_mode_passes_with_the_baseline(self) -> None:
        code, out, err = self.run_main(BASELINE)
        self.assertEqual((code, err), (0, ""))
        self.assertIn("3 reduction(s), 2 without an efficiency witness; 2 baseline entries "
                      "(1 gap(s), 0 via certified program, 0 instance-scoped via, 1 exempt), "
                      "checking 1 changed module(s)", out)

    def test_main_counts_and_checks_via_entries(self) -> None:
        reductions, _ = c.parse(VIA_OUTPUT)
        baseline = {**BASELINE, VIA_REDUCTION: VIA_ENTRY}
        with mock.patch.object(c, "scan", return_value=(reductions, c.parse_checks(VIA_OUTPUT))):
            code, out, err = self.run_main(baseline, "--all")
        self.assertEqual((code, err), (0, ""))
        self.assertIn("3 baseline entries (1 gap(s), 1 via certified program, 0 instance-scoped "
                      "via, 1 exempt)", out)
        problem = "headline `H` mentions neither `X` nor `Y` in its statement or proof"
        with mock.patch.object(c, "scan", return_value=(reductions,
                                                        c.parse_checks(check_row([problem])))):
            code, _, err = self.run_main(baseline, "--all")
        self.assertEqual(code, 1)
        self.assertIn(f"{GARBLING_PATH}: {VIA_REDUCTION}: {problem}", err)

    def test_instance_scoped_entries_are_counted_apart(self) -> None:
        reductions, _ = c.parse(VIA_OUTPUT)
        baseline = {**BASELINE, VIA_REDUCTION: SCOPED_ENTRY}
        with mock.patch.object(c, "scan", return_value=(reductions, c.parse_checks(VIA_OUTPUT))):
            code, out, err = self.run_main(baseline, "--all")
            self.assertEqual((code, err), (0, ""))
            self.assertIn("3 baseline entries (1 gap(s), 0 via certified program, 1 "
                          "instance-scoped via, 1 exempt)", out)
            out = self.run_main(baseline, "--report")[1]
        self.assertIn(f"{GARBLING_PATH}: {VIA_REDUCTION}: headline `{VIA_ENTRY['headline']}` uses "
                      "the program in its proof; scoped to one instance, with 3 pinned "
                      "consumer(s) (1 headline, 1 concrete, 1 reduction)", out)

    def test_report_prints_where_the_headline_uses_the_program(self) -> None:
        reductions, _ = c.parse(VIA_OUTPUT)
        baseline = {**BASELINE, VIA_REDUCTION: VIA_ENTRY}
        with mock.patch.object(c, "scan", return_value=(reductions, c.parse_checks(VIA_OUTPUT))):
            code, out, _ = self.run_main(baseline, "--report")
        self.assertEqual(code, 0)
        self.assertIn(f"{GARBLING_PATH}: {VIA_REDUCTION}: headline `{VIA_ENTRY['headline']}` uses "
                      "the program in its proof", out)

    def test_pull_request_mode_reports_untouched_modules(self) -> None:
        code, out, err = self.run_main({UNCERTIFIED: BASELINE[UNCERTIFIED]})
        self.assertEqual(code, 0)
        self.assertIn("Not enforced", out)
        self.assertIn(f"{SIGNATURE_PATH}:30: {EXEMPT}", out)
        self.assertEqual(err, "")
        with mock.patch.dict(c.os.environ, {"GITHUB_ACTIONS": "true"}):
            out = self.run_main(None)[1]
        self.assertIn("::notice title=Reduction witnesses::1 difference(s)", out)

    def test_a_stale_entry_fails_the_change_that_certifies_the_reduction(self) -> None:
        with mock.patch.object(c.cer, "touched_modules", return_value={ELGAMAL_PATH}):
            code, _, err = self.run_main({**BASELINE, CERTIFIED: entry(ELGAMAL_PATH)})
        self.assertEqual(code, 1)
        self.assertIn(f"{ELGAMAL_PATH}: {CERTIFIED} (certified (direct:", err)

    def test_a_change_to_the_checker_enforces_every_module(self) -> None:
        with mock.patch.object(c, "checker_changed", return_value=True):
            code, out, err = self.run_main({UNCERTIFIED: BASELINE[UNCERTIFIED]})
        self.assertEqual(code, 1)
        self.assertIn("every module is enforced", out)
        self.assertIn(f"{SIGNATURE_PATH}:30: {EXEMPT}", err)

    def test_report_mode_succeeds(self) -> None:
        code, out, _ = self.run_main({}, "--report")
        self.assertEqual(code, 0)
        self.assertIn(UNCERTIFIED, out)
        self.assertIn(EXEMPT, out)
        self.assertIn("report only", out)

    def test_list_shows_certificates(self) -> None:
        code, out, _ = self.run_main(None, "--list", "CslibFrontier/Crypto/")
        self.assertEqual(code, 0)
        self.assertIn("certified direct: Cslib.Crypto.ElGamal.isPPT_toDDH", out)
        self.assertIn("3 reduction(s), 2 without an efficiency witness", out)

    def test_update_then_justify(self) -> None:
        self.assertEqual(self.run_main({}, "--update-baseline")[0], 0)
        written = json.loads(self.baseline.read_text())
        self.assertEqual(written, {UNCERTIFIED: entry(SCHNORR_PATH, "gap", "")})
        code, _, err = self.run_main(None)
        self.assertEqual(code, 1)
        self.assertIn("without a justification", err)
        written[UNCERTIFIED]["why"] = "tracked in #5293 section 2"
        self.assertEqual(self.run_main(written)[0], 0)


# A compiled module for `CompiledFixtureTests`, under `CslibFrontier/Crypto` so that it is scanned.
FIXTURE = """module
public import Init
public section

/-- Stands in for Mathlib's `PMF`: a distribution by name. -/
structure PMF (α : Type) where
  weight : α → Nat

/-- Stands in for `PFunctor.FreeM`, which `ProbComp` and `OracleComp` unfold to. -/
structure PFunctor.FreeM (α : Type) where
  run : Nat → α

namespace Cslib.Crypto.Fixture

abbrev ProbComp := PFunctor.FreeM
/-- An adversary given as a function into a computation. -/
abbrev Adversary := Nat → ProbComp Bool
/-- An adversary given as a structure of programs. -/
structure TwoStage where
  choose : Nat → ProbComp Nat
  guess : Nat → ProbComp Bool
/-- A scheme: a structure of programs too. -/
structure Scheme where
  keyGen : Nat → ProbComp Nat
/-- A group: not a program. -/
structure Group where
  order : Nat

def IsPPT (_A : Adversary) : Prop := True
def TwoStage.IsPPT (_A : TwoStage) : Prop := True
def IsPPTOn (_f : Nat → Nat → ProbComp Bool) : Prop := True
def IsQueryBounded (_A : Adversary) (_q : Nat) : Prop := True

def advantage (_G : Group) (_A : Adversary) (n : Nat) : Nat := n
def schemeAdvantage (_S : Scheme) (_A : Adversary) (n : Nat) : Nat := n
def twoStageAdvantage (_A : TwoStage) (n : Nat) : Nat := n
def lawAdvantage (_X : PMF Nat) (_A : Adversary) (n : Nat) : Nat := n
def forgeExperiment (_A : Adversary) (n : Nat) : Nat := n

variable (G : Group) (S : Scheme) (A : Adversary) (n : Nat)

/-! Certified reductions. -/

def certified (A : Adversary) : Adversary := A
theorem isPPT_certified {A : Adversary} (_h : IsPPT A) : IsPPT (certified A) := trivial
theorem certified_le : schemeAdvantage S A n ≤ advantage G (certified A) n := Nat.le_refl _

def privatelyCertified (A : Adversary) : Adversary := A
private theorem isPPT_privatelyCertified : IsPPT (privatelyCertified A) := trivial
theorem privatelyCertified_le : schemeAdvantage S A n ≤ advantage G (privatelyCertified A) n :=
  Nat.le_refl _

def certifiedTwoStage (A : Adversary) : TwoStage := ⟨fun _ => ⟨fun k => k⟩, A⟩
theorem isPPT_certifiedTwoStage (_h : IsPPT A) : (certifiedTwoStage A).IsPPT := trivial
theorem certifiedTwoStage_le :
    schemeAdvantage S A n ≤ twoStageAdvantage (certifiedTwoStage A) n := Nat.le_refl _

/-- An abbreviation of certified reductions is certified. -/
abbrev abbreviated (A : Adversary) : Adversary := certified (privatelyCertified A)
theorem abbreviated_le : schemeAdvantage S A n ≤ advantage G (abbreviated A) n := Nat.le_refl _

/-- A reduction that a certified word-level program runs is certified. -/
def wrapped (A : Adversary) : Adversary := A
def wrappedWords (A : Adversary) (n k : Nat) : ProbComp Bool := wrapped A (n + k)
theorem isPPTOn_wrappedWords (_h : IsPPT A) : IsPPTOn (wrappedWords A) := trivial
theorem wrapped_le : schemeAdvantage S A n ≤ advantage G (wrapped A) n := Nat.le_refl _

/-! Reductions without an efficiency witness. -/

def uncertified (A : Adversary) : Adversary := A
theorem uncertified_le : schemeAdvantage S A n ≤ advantage G (uncertified A) n + 1 :=
  Nat.le_succ _

/-- A query bound is not an efficiency witness. -/
def queryBounded (A : Adversary) : Adversary := A
theorem isQueryBounded_queryBounded : IsQueryBounded (queryBounded A) 3 := trivial
theorem queryBounded_le : schemeAdvantage S A n ≤ advantage G (queryBounded A) n := Nat.le_refl _

def equated (A : Adversary) : Adversary := A
theorem equated_eq : schemeAdvantage S A n = advantage G (equated A) n :=
  Nat.le_antisymm (Nat.le_refl _) (Nat.le_refl _)

def reversed (A : Adversary) : Adversary := A
theorem reversed_ge : advantage G (reversed A) n ≥ schemeAdvantage S A n := Nat.le_refl _

def indexed (A : Adversary) (_i : Nat) : Adversary := A
theorem indexed_le : ∃ i, schemeAdvantage S A n ≤ advantage G (indexed A i) n :=
  ⟨0, Nat.le_refl _⟩

def uncertifiedTwoStage (A : Adversary) : TwoStage := ⟨fun _ => ⟨fun k => k⟩, A⟩
theorem uncertifiedTwoStage_le :
    schemeAdvantage S A n ≤ twoStageAdvantage (uncertifiedTwoStage A) n := Nat.le_refl _

/-- An abbreviation of an uncertified reduction is not certified. -/
abbrev abbreviatedUncertified (A : Adversary) : Adversary := certified (uncertified A)
theorem abbreviatedUncertified_le :
    schemeAdvantage S A n ≤ advantage G (abbreviatedUncertified A) n := Nat.le_refl _

/-- Reported, though not a reduction: a scheme built from the scheme, on the bounding side only.
The baseline exempts such a definition. -/
def typedScheme (S : Scheme) : Scheme := S
theorem typedScheme_eq :
    schemeAdvantage S A n = schemeAdvantage (typedScheme S) (certified A) n :=
  Nat.le_antisymm (Nat.le_refl _) (Nat.le_refl _)

/-! Not reductions. -/

/-- A scheme on both sides. -/
def derivedScheme (S : Scheme) : Scheme := S
theorem derivedScheme_le :
    schemeAdvantage (derivedScheme S) A n ≤ schemeAdvantage (derivedScheme S) (certified A) n :=
  Nat.le_refl _

/-- A law of a component that is not a program. -/
def keyLaw (_G : Group) (_n : Nat) : PMF Nat := ⟨fun _ => 0⟩
theorem keyLaw_le : schemeAdvantage S A n ≤ lawAdvantage (keyLaw G n) (certified A) n :=
  Nat.le_refl _

/-- A number. -/
def loss (_A : Adversary) : Nat := 0
theorem loss_le : schemeAdvantage S A n ≤ advantage G (certified A) n + loss A := Nat.le_refl _

/-- An attack: the bounded side mentions no program variable. -/
def attack (_S : Scheme) : Adversary := fun _ => ⟨fun _ => true⟩
theorem attack_le : n ≤ schemeAdvantage S (attack S) n := Nat.le_refl _

/-- A simulator on the bounded side (a known gap). -/
def simulator (A : Adversary) : Adversary := A
theorem simulator_le : schemeAdvantage S (simulator A) n ≤ advantage G (certified A) n :=
  Nat.le_refl _

/-- A bound without an advantage-named constant (a known gap). -/
def unnamedBound (A : Adversary) : Adversary := A
theorem unnamedBound_le : forgeExperiment A n ≤ forgeExperiment (unnamedBound A) n :=
  Nat.le_refl _

/-- A reduction written inline (a known gap). -/
theorem inline_le : schemeAdvantage S A n ≤ advantage G (fun k => A (k + 1)) n := Nat.le_refl _

/-- A bound stated only by a private theorem. -/
def privatelyStated (A : Adversary) : Adversary := A
private theorem privatelyStated_le :
    schemeAdvantage S A n ≤ advantage G (privatelyStated A) n := Nat.le_refl _

/-! A typed reduction that a certified program runs (`via_certified_program` requests). -/

/-- Stands in for `Negligible`, which the reader recognizes by its name. -/
def Negligible (_f : Nat → Nat) : Prop := True
/-- A security notion that unfolds to a negligibility claim. -/
def Secure (A : Adversary) : Prop := ∀ G : Group, Negligible fun n => advantage G A n

/-- The typed step: uncertified. -/
@[expose] def typedStep (A : Adversary) : Adversary := A
theorem typedStep_le : schemeAdvantage S A n ≤ advantage G (typedStep A) n := Nat.le_refl _

/-- The certified program, whose body does not mention the step (else it would be a wrapper). -/
@[expose] def stepProgram (A : Adversary) : Adversary := fun k => A k
theorem isPPT_stepProgram (_h : IsPPT A) : IsPPT (stepProgram A) := trivial
theorem eval_stepProgram : stepProgram A = typedStep A := rfl
private theorem eval_stepProgram_private : typedStep A = stepProgram A := rfl
/-- A bound, not an equation. -/
theorem stepProgram_le : advantage G (stepProgram A) n ≤ advantage G (typedStep A) n :=
  Nat.le_refl _
/-- An equation that does not mention the step. -/
theorem stepProgram_eq_self : stepProgram A = fun k => A k := rfl
/-- A private program and a private certificate, which an entry may not name. -/
private def privateProgram (A : Adversary) : Adversary := fun k => A k
private theorem isPPT_stepProgram_private (_h : IsPPT A) : IsPPT (stepProgram A) := trivial

/-- A headline that applies the certificate in its proof only. -/
theorem stepHeadline (h : IsPPT A) : Negligible fun n => schemeAdvantage S A n :=
  (fun _ => trivial) (isPPT_stepProgram A h)
/-- A headline that mentions the program in its statement. -/
theorem stepStatement (_h : IsPPT A) : Negligible fun n => advantage G (stepProgram A) n := trivial
/-- A headline whose notion unfolds to a negligibility claim. -/
theorem stepNotion (_h : IsPPT A) : Secure (stepProgram A) := fun _ => trivial
/-- A negligibility claim that mentions neither the program nor its certificate. -/
theorem unrelatedHeadline : Negligible fun n => schemeAdvantage S A n := trivial
/-- A theorem that uses the certificate but makes no security claim. -/
theorem atomlessHeadline (h : IsPPT A) : 0 ≤ n := (fun _ => Nat.zero_le n) (isPPT_stepProgram A h)
/-- A private headline. -/
private theorem privateHeadline (h : IsPPT A) : Negligible fun n => schemeAdvantage S A n :=
  (fun _ => trivial) (isPPT_stepProgram A h)

/-- A second typed step, whose consumers in `FixtureConsumers` are not concrete. -/
@[expose] def otherStep (A : Adversary) : Adversary := A
theorem eval_otherStep : stepProgram A = otherStep A := rfl
/-- A theorem of the step's own module whose conclusion is a negligibility claim. -/
theorem otherStep_secure (h : IsPPT A) : Secure (otherStep (stepProgram A)) := stepNotion A h

end Cslib.Crypto.Fixture
"""

PREFIX = "Cslib.Crypto.Fixture."
FIXTURE_MODULE = "CslibFrontier.Crypto.Fixture"
FIXTURE_PATH = "CslibFrontier/Crypto/Fixture.lean"

# A second module with a private declaration of the same name as the fixture's private equality.
OTHER_MODULE = "CslibFrontier.Crypto.FixtureOther"
FIXTURE_OTHER = """module
public import Init
public section

namespace Cslib.Crypto.Fixture

private theorem eval_stepProgram_private : (1 : Nat) = 1 := rfl

end Cslib.Crypto.Fixture
"""

# A third module with a public declaration of the same name as the fixture's private equality.
PUBLIC_MODULE = "CslibFrontier.Crypto.FixturePublic"
FIXTURE_PUBLIC = """module
public import Init
public section

namespace Cslib.Crypto.Fixture

theorem eval_stepProgram_private : (1 : Nat) = 1 := rfl

end Cslib.Crypto.Fixture
"""

# A fourth module, which imports the fixture: consumers of its typed steps outside their module.
CONSUMERS_MODULE = "CslibFrontier.Crypto.FixtureConsumers"
CONSUMERS_PATH = "CslibFrontier/Crypto/FixtureConsumers.lean"
FIXTURE_CONSUMERS = """module
public import CslibFrontier.Crypto.Fixture
public section

namespace Cslib.Crypto.Fixture

variable (G : Group) (S : Scheme) (A : Adversary) (n : Nat)

/-! Consumers of `typedStep`, for requests scoped to one instance. -/

/-- On the headline's proof path: a bound through the typed step. -/
theorem pathBound : schemeAdvantage S A n ≤ advantage G (typedStep A) n := typedStep_le G S A n
/-- The headline: it applies the certificate and uses `pathBound`, under a negligibility
premise. -/
theorem scopedHeadline (h : IsPPT A) (_hn : Negligible fun n => advantage G A n) :
    Negligible fun n => schemeAdvantage S A n :=
  (fun _ _ => stepHeadline S A h) (isPPT_stepProgram A h) (pathBound G S A 0)
/-- An exact bound at another instance, off the headline's proof path. -/
theorem concreteBound :
    schemeAdvantage S (typedStep A) n ≤ advantage G (typedStep (typedStep A)) n :=
  typedStep_le G S (typedStep A) n
/-- Mentions the typed step only through a private definition. -/
private def privateWrap (A : Adversary) : Adversary := typedStep A
theorem throughPrivate (A : Adversary) : n ≤ n :=
  (fun (_ : Adversary) => Nat.le_refl n) (privateWrap A)
/-- A definition that wraps the typed step. -/
def wrappedStep (A : Adversary) : Adversary := typedStep A

/-! Consumers of `otherStep` that are not concrete. -/

/-- An assumption. -/
def Hard (G : Group) : Prop := ∀ A : Adversary, IsPPT A → Negligible fun n => advantage G A n
/-- A defined predicate that wraps the assumption. -/
def Wrapped (G : Group) : Prop := Hard G
/-- On the headline's proof path, but resting on the wrapped assumption. -/
theorem wrappedOther (_h : Wrapped G) : otherStep A = A := rfl
/-- The headline for `otherStep`. -/
theorem otherHeadline (h : IsPPT A) (hw : Wrapped G) : Negligible fun n => schemeAdvantage S A n :=
  (fun _ _ => stepHeadline S A h) (isPPT_stepProgram A h) (wrappedOther G A hw)
/-- A definition that wraps `otherStep`. -/
def otherWrapper (A : Adversary) : Adversary := otherStep A
/-- A certified definition that wraps `otherStep`, and its certificate. -/
def certifiedOther (A : Adversary) : Adversary := certified (otherStep A)
theorem isPPT_certifiedOther (h : IsPPT A) : IsPPT (certifiedOther A) :=
  isPPT_certified (A := otherStep A) h
/-- A generic wrapper of `otherStep`, which a certified definition runs but which has no witness of
its own. -/
def genericOther (A : Adversary) : Adversary := otherStep A
def certifiedGeneric (A : Adversary) : Adversary := certified (genericOther A)
theorem isPPT_certifiedGeneric (h : IsPPT A) : IsPPT (certifiedGeneric A) :=
  isPPT_certified (A := genericOther A) h
/-- A class that packages the assumption. -/
class WrappedClass (G : Group) : Prop where
  hard : Hard G
/-- Rests on the assumption through an instance argument. -/
theorem classOther [WrappedClass G] : otherStep A = A := rfl
/-- An ordinary instance argument is not an assumption. -/
theorem plainInstance [Nonempty Adversary] : otherStep A = A := rfl
/-- An alias for a whole statement, whose premise is the wrapped assumption. A module's public
statement cannot name a private alias, so this one is public, which makes it a definition that uses
`otherStep` too. -/
def WrappedType (G : Group) (A : Adversary) : Prop := Wrapped G → otherStep A = A
/-- Rests on the assumption through the alias of its statement. -/
theorem aliasOther : WrappedType G A := fun _ => rfl

end Cslib.Crypto.Fixture
"""

# `via_certified_program` requests for the fixture, all for the reduction `typedStep`: a valid
# request, and the changes each label makes to it. Names are without `PREFIX`.
VALID_REQUEST = {"program": "stepProgram", "certificate": "isPPT_stepProgram",
                 "equality": "eval_stepProgram", "equality_module": FIXTURE_MODULE,
                 "headline": "stepHeadline"}
VIA_REQUESTS = {
    "valid": {},
    "statement": {"headline": "stepStatement"},
    "notion": {"headline": "stepNotion"},
    "private": {"equality": "eval_stepProgram_private"},
    "private elsewhere": {"equality": "eval_stepProgram_private", "equality_module": OTHER_MODULE},
    "public elsewhere": {"equality": "eval_stepProgram_private", "equality_module": PUBLIC_MODULE},
    "bogus private": {"equality": "eval_stepProgram_privat"},
    "private program": {"program": "privateProgram"},
    "private certificate": {"certificate": "isPPT_stepProgram_private"},
    "private headline": {"headline": "privateHeadline"},
    "renamed": {"program": "stepProgramRenamed"},
    "inequality": {"equality": "stepProgram_le"},
    "one side": {"equality": "stepProgram_eq_self"},
    "headline is the certificate": {"headline": "isPPT_stepProgram"},
    "headline is the equality": {"headline": "eval_stepProgram"},
    "no security claim": {"headline": "atomlessHeadline"},
    "unrelated": {"headline": "unrelatedHeadline"},
    "not a certificate": {"certificate": "eval_stepProgram"},
}


# Requests scoped to one instance: the consumers of `typedStep` outside its module, with the
# headline `scopedHeadline`, and the changes each label makes to them; and a request for
# `otherStep`, whose referring theorems are not concrete.
SCOPED_VALID = {"pathBound": "headline", "scopedHeadline": "headline",
                "concreteBound": "concrete", "throughPrivate": "concrete",
                "wrappedStep": "reduction"}
SCOPED_REQUESTS = {
    "scoped": {},
    "unpinned": {"concreteBound": None},
    "pinned in its module": {"typedStep_le": "concrete"},
    "missing consumer": {"goneConsumer": "concrete"},
    "off the path": {"concreteBound": "headline"},
    "headline as concrete": {"scopedHeadline": "concrete"},
    "definition as theorem": {"wrappedStep": "concrete"},
    "theorem as reduction": {"pathBound": "reduction"},
}
NOT_CONCRETE = {"otherHeadline": "headline", "wrappedOther": "headline",
                "otherWrapper": "reduction", "certifiedOther": "reduction",
                "isPPT_certifiedOther": "concrete", "classOther": "concrete",
                "plainInstance": "concrete", "aliasOther": "concrete",
                "WrappedType": "reduction", "genericOther": "reduction"}


def via_request(changes: dict[str, str], consumers: dict[str, str] | None = None,
                reduction: str = "typedStep") -> str:
    """The reader's input line for the valid request with `changes`, scoped to one instance with
    the pinned `consumers` when they are given."""
    r = {**VALID_REQUEST, **changes}
    scope = ([] if consumers is None else
             ["instance", *(f"{tag}:{PREFIX}{name}" for name, tag in sorted(consumers.items()))])
    return "\t".join(["via", PREFIX + reduction, FIXTURE_MODULE, PREFIX + r["program"],
                      PREFIX + r["certificate"], PREFIX + r["equality"], r["equality_module"],
                      PREFIX + r["headline"], *scope])


def scoped_requests() -> dict[str, str]:
    """The reader's input lines for the requests scoped to one instance, by label."""
    out = {}
    for label, changes in SCOPED_REQUESTS.items():
        consumers = {name: tag for name, tag in {**SCOPED_VALID, **changes}.items() if tag}
        out[label] = via_request({"headline": "scopedHeadline"}, consumers)
    out["not concrete"] = via_request({"equality": "eval_otherStep", "headline": "otherHeadline"},
                                      NOT_CONCRETE, "otherStep")
    return out


@unittest.skipUnless(shutil.which("lake") and (c.ROOT / ".lake/packages").is_dir(),
                     "needs Lean and the repository's packages (CI runs this after the build)")
class CompiledFixtureTests(unittest.TestCase):
    """What `scripts/SecurityPremises.lean --reductions` reports for a compiled module."""

    @classmethod
    def setUpClass(cls) -> None:
        tmp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(tmp.cleanup)
        root = pathlib.Path(tmp.name)
        # The fixture's own build directory comes first, so that `FixtureConsumers` finds the
        # fixture rather than the library's `CslibFrontier`.
        lean = ["lake", "env", "sh", "-c", 'LEAN_PATH="$0:$LEAN_PATH" exec lean "$@"',
                str(root / "build")]
        modules = ((FIXTURE_MODULE, FIXTURE), (OTHER_MODULE, FIXTURE_OTHER),
                   (PUBLIC_MODULE, FIXTURE_PUBLIC), (CONSUMERS_MODULE, FIXTURE_CONSUMERS))
        for module, text in modules:
            source = root / "src" / c.csp.module_path(module)
            olean = (root / "build" / c.csp.module_path(module)).with_suffix(".olean")
            source.parent.mkdir(parents=True, exist_ok=True)
            olean.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(text)
            subprocess.run([*lean, f"--root={root / 'src'}", "-o", str(olean), str(source)],
                           cwd=c.ROOT, check=True, capture_output=True)
        scoped = scoped_requests()
        requests = [via_request(changes) for changes in VIA_REQUESTS.values()] + list(
            scoped.values())
        out = subprocess.run(["lake", "env", "lean", "--run", c.csp.TOOL, str(root / "build"),
                              "--reductions"], cwd=c.ROOT,
                             input="\n".join([*(module for module, _ in modules),
                                              *requests]) + "\n",
                             capture_output=True, text=True, check=True).stdout
        reductions, cls.summary = c.parse(out)
        cls.reductions = {name.removeprefix(PREFIX): r for name, r in reductions.items()}
        # One verdict per request, in order; most share a reduction, so `parse_checks` would
        # keep only the last.
        verdicts = [next(iter(c.parse_checks(line).values())) for line in out.splitlines()
                    if '"v"' in line]
        cls.verdicts = dict(zip([*VIA_REQUESTS, *scoped], verdicts, strict=True))

    def certificate(self, name: str) -> tuple[str, tuple[str, ...]]:
        r = self.reductions[name]
        return r.certificate, tuple(w.removeprefix(PREFIX) for w in r.certified_by)

    def test_certified_reductions(self) -> None:
        self.assertEqual(self.certificate("certified"), ("direct", ("isPPT_certified",)))
        self.assertEqual(self.reductions["certified"].path, "CslibFrontier/Crypto/Fixture.lean")
        self.assertIn(PREFIX + "certified_le", self.reductions["certified"].theorems)
        # A private witness counts, and so does a certificate of a structure of programs.
        self.assertEqual(self.certificate("privatelyCertified"),
                         ("direct", ("isPPT_privatelyCertified",)))
        self.assertEqual(self.certificate("certifiedTwoStage"),
                         ("direct", ("isPPT_certifiedTwoStage",)))

    def test_abbreviations_and_wrappers_carry_certificates(self) -> None:
        self.assertEqual(self.certificate("abbreviated"),
                         ("abbrev", ("certified", "privatelyCertified")))
        self.assertEqual(self.certificate("wrapped"), ("wrapper", ("wrappedWords",)))
        self.assertEqual(self.certificate("abbreviatedUncertified"), ("", ()))

    def test_uncertified_reductions(self) -> None:
        for name in ("uncertified", "queryBounded", "equated", "reversed", "indexed",
                     "uncertifiedTwoStage", "abbreviatedUncertified"):
            self.assertEqual(self.certificate(name), ("", ()), name)

    def test_a_scheme_on_the_bounding_side_only_is_reported(self) -> None:
        # A known false positive, which the baseline exempts.
        self.assertEqual(self.certificate("typedScheme"), ("", ()))

    def test_schemes_laws_numbers_and_attacks_are_not_reductions(self) -> None:
        for name in ("derivedScheme", "keyLaw", "loss", "attack", "privatelyStated"):
            self.assertNotIn(name, self.reductions)

    def test_known_limitations(self) -> None:
        # Review covers these cases (the reader's docstring, "Known gaps of this mode").
        for name in ("simulator", "unnamedBound"):
            self.assertNotIn(name, self.reductions)
        self.assertNotIn(PREFIX + "inline_le",
                         [t for r in self.reductions.values() for t in r.theorems])

    def test_exactly_the_expected_reductions(self) -> None:
        self.assertEqual(len(self.reductions), 14)
        self.assertEqual(len(c.uncertified(self.reductions)), 9)
        self.assertEqual(self.summary["missing"], [])

    def test_a_valid_via_request_passes(self) -> None:
        self.assertEqual(self.certificate("typedStep"), ("", ()))
        self.assertEqual(self.verdicts["valid"],
                         c.ViaCheck((), "proof", (FIXTURE_PATH,), FIXTURE_PATH, ()))
        # A headline may mention the program in its statement, and state a notion that unfolds
        # to a negligibility claim.
        for label in ("statement", "notion"):
            self.assertEqual(self.verdicts[label].problems, (), label)
            self.assertEqual(self.verdicts[label].headline_at, "statement", label)

    def test_a_private_equality_resolves_in_its_recorded_module(self) -> None:
        # Another module has a private declaration of the same name, and a third a public one;
        # the entry's recorded module decides.
        self.assertEqual(self.verdicts["private"],
                         c.ViaCheck((), "proof", (FIXTURE_PATH,), FIXTURE_PATH, ()))
        for label, module in (("private elsewhere", OTHER_MODULE),
                              ("public elsewhere", PUBLIC_MODULE)):
            elsewhere = self.verdicts[label]
            self.assertEqual(elsewhere.equality_path, c.csp.module_path(module), label)
            self.assertEqual(len(elsewhere.problems), 1, label)
            self.assertIn(f"equality `{PREFIX}eval_stepProgram_private` does not equate",
                          elsewhere.problems[0], label)
        bogus = self.verdicts["bogus private"]
        self.assertEqual(bogus.problems, (f"equality `{PREFIX}eval_stepProgram_privat` does not "
                                          "exist, publicly or as a private declaration of "
                                          f"{FIXTURE_MODULE}",))
        self.assertEqual((bogus.missing, bogus.equality_path),
                         ((PREFIX + "eval_stepProgram_privat",), ""))

    def test_the_program_certificate_and_headline_must_be_public(self) -> None:
        for label, role, name in (("private program", "program", "privateProgram"),
                                  ("private certificate", "certificate",
                                   "isPPT_stepProgram_private"),
                                  ("private headline", "headline", "privateHeadline")):
            verdict = self.verdicts[label]
            self.assertEqual(verdict.problems, (f"{role} `{PREFIX}{name}` is private; the "
                                                "program, its certificate and the headline must "
                                                "be public",), label)
            self.assertEqual(verdict.missing, (PREFIX + name,), label)

    def test_invalid_via_requests_fail(self) -> None:
        expected = {
            "renamed": f"program `{PREFIX}stepProgramRenamed` does not exist",
            "inequality": f"equality `{PREFIX}stepProgram_le` is not an equation (its conclusion "
                          "is headed by `LE.le`)",
            "one side": f"equality `{PREFIX}stepProgram_eq_self` does not equate a term that "
                        f"mentions `{PREFIX}stepProgram` with one that mentions "
                        f"`{PREFIX}typedStep`",
            "headline is the certificate": f"headline `{PREFIX}isPPT_stepProgram` is the "
                                           "certificate",
            "headline is the equality": f"headline `{PREFIX}eval_stepProgram` is the equality",
            "no security claim": f"headline `{PREFIX}atomlessHeadline` does not conclude a "
                                 "negligibility or advantage claim",
            "unrelated": f"headline `{PREFIX}unrelatedHeadline` mentions neither "
                         f"`{PREFIX}stepProgram` nor `{PREFIX}isPPT_stepProgram`",
            "not a certificate": f"certificate `{PREFIX}eval_stepProgram` does not conclude an "
                                 "efficiency certificate",
        }
        for label, problem in expected.items():
            problems = self.verdicts[label].problems
            self.assertEqual(len(problems), 1, (label, problems))
            self.assertIn(problem, problems[0], label)
        self.assertEqual(self.verdicts["renamed"].missing, (PREFIX + "stepProgramRenamed",))

    def test_a_scoped_request_pins_exactly_the_referrers(self) -> None:
        # The referrers outside the step's module: directly, through a private definition, and a
        # definition that wraps the step; not the theorems of the step's own module.
        verdict = self.verdicts["scoped"]
        self.assertEqual(verdict.problems, ())
        self.assertEqual(set(verdict.referrers), {PREFIX + name for name in SCOPED_VALID})
        self.assertEqual(verdict.headline_at, "proof")
        self.assertEqual(set(verdict.paths), {FIXTURE_PATH, CONSUMERS_PATH})

    def test_scoped_requests_fail_on_a_new_referrer_or_a_wrong_tag(self) -> None:
        step, headline = f"`{PREFIX}typedStep`", f"`{PREFIX}scopedHeadline`"
        expected = {
            # The regression: a pinned list that misses a referrer fails.
            "unpinned": f"`{PREFIX}concreteBound` refers to {step} outside its module but is not "
                        "a pinned consumer",
            "pinned in its module": f"consumer `{PREFIX}typedStep_le` does not refer to {step} "
                                    "outside",
            "missing consumer": f"consumer `{PREFIX}goneConsumer` does not exist",
            "off the path": f"consumer `{PREFIX}concreteBound` is tagged `headline` but is not on "
                            f"the proof path of {headline}",
            "headline as concrete": f"consumer {headline} is the headline but is tagged "
                                    "`concrete`",
            "definition as theorem": f"consumer `{PREFIX}wrappedStep` is tagged `concrete` but is "
                                     "not a theorem",
            "theorem as reduction": f"consumer `{PREFIX}pathBound` is tagged `reduction` but is "
                                    "not a definition",
        }
        for label, problem in expected.items():
            problems = self.verdicts[label].problems
            self.assertEqual(len(problems), 1, (label, problems))
            self.assertIn(problem, problems[0], label)
        self.assertEqual(self.verdicts["missing consumer"].missing, (PREFIX + "goneConsumer",))

    def test_every_other_referring_theorem_must_be_concrete(self) -> None:
        # The assumption is seen however it is packaged: a defined predicate that wraps it, a
        # class instance argument, an alias for the whole statement, and a conclusion that unfolds
        # to a negligibility claim in the step's own module. The headline is not held to this,
        # and an ordinary instance argument or an efficiency premise is no assumption.
        verdict = self.verdicts["not concrete"]
        step = f"`{PREFIX}otherStep`"
        expected = [
            f"`{PREFIX}aliasOther` refers to {step} and is not concrete (a premise rests on the "
            f"named assumption `{PREFIX}Wrapped`",
            f"`{PREFIX}classOther` refers to {step} and is not concrete (a premise rests on the "
            f"named assumption `{PREFIX}WrappedClass`",
            f"`{PREFIX}otherStep_secure` refers to {step} in its module and is not concrete (its "
            "conclusion makes a negligibility claim)",
            f"`{PREFIX}wrappedOther` refers to {step} and is not concrete (a premise rests on the "
            f"named assumption `{PREFIX}Wrapped`",
        ]
        self.assertEqual(len(verdict.problems), len(expected), verdict.problems)
        for problem in expected:
            self.assertTrue(any(problem in p for p in verdict.problems), problem)

    def test_definitions_that_use_the_step_are_reported_with_their_certification(self) -> None:
        # A wrapper without a witness of its own needs a baseline entry, even when a certified
        # definition runs it (`genericOther`); one with a witness of its own needs none.
        verdict = self.verdicts["not concrete"]
        self.assertEqual(verdict.definitions, ((PREFIX + "WrappedType", CONSUMERS_PATH),
                                               (PREFIX + "genericOther", CONSUMERS_PATH),
                                               (PREFIX + "otherWrapper", CONSUMERS_PATH)))
        self.assertEqual(verdict.certified_definitions, (PREFIX + "certifiedOther",))
        self.assertEqual(self.verdicts["scoped"].definitions,
                         ((PREFIX + "wrappedStep", CONSUMERS_PATH),))


class CommittedFilesTests(unittest.TestCase):
    """These run on every event, merge groups included, so they check only the baseline file
    itself. Whether its entries match the library (a moved or deleted module, say) is the pull
    request check's job, which merge groups only report."""

    def test_baseline_is_canonical_and_justified(self) -> None:
        baseline = c.load_baseline(c.BASELINE)
        self.assertEqual(c.BASELINE.read_text(encoding="utf-8"), c.baseline_text(baseline))
        for name, value in baseline.items():
            self.assertTrue(value["why"].strip(), name)
            self.assertIn(value["kind"], c.KINDS, name)


if __name__ == "__main__":
    unittest.main()
