"""`scripts/full_check.py` mirrors CI's source and Lean jobs, and its runner reports each step.

The parity test reads `.github/workflows/lean_action_ci.yml` as text (CI's Python has no YAML
library) and fails closed. Every named `source-checks` and `lean-checks` step must be mirrored by
`full_check.STEPS`, run by `scripts/check.sh` before the cache bootstrap (`PREFLIGHT`), or listed in
`CI_ONLY`. The `run` script of a mirrored or preflight step may contain only its local commands, in
order, and the lines in `PLUMBING` (`set -e` and the computation of `BASE`), which the local run
replaces by the merge base of `--base`; any other line is reported. So is a step key the local run
does not reproduce (anything outside `MIRRORED_KEYS`, such as `shell`, `continue-on-error` or
`timeout-minutes`), a working directory or literal environment that differs from CI's, an
environment value taken from GitHub context other than `CONTEXT_ENV`, a job-level `defaults` or
literal `env`, and mirrored steps out of order within either CI job. A step's `if:` condition is
not compared: the local run always runs a mirrored step, which is the stricter direction for steps
that CI runs only on some events. `ParityProblemTests` mutates the workflow to check that each kind
of drift is reported. Separate aggregator tests require both jobs to succeed and check that its
publication output is forwarded from `lean-checks`.
"""

import importlib.util
import io
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("full_check", Path(__file__).with_name("full_check.py"))
full = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = full
SPEC.loader.exec_module(full)
REPO = Path(__file__).resolve().parent.parent
WORKFLOW = REPO / ".github/workflows/lean_action_ci.yml"
EXECUTION_JOBS = ("source-checks", "lean-checks")
ADVISORY_JOBS = ("pr-notices",)
CHECKED_JOBS = EXECUTION_JOBS + ADVISORY_JOBS
AGGREGATOR_JOB = "ci-checks"
SOURCE_CHECK_NAMES = frozenset({
    "Test Python tooling",
    "Operator manual links and excerpts",
    "Source hygiene",
    "Forbid TimeM",
    "Encoding readability ratchet (changed modules)",
    "Encoding readability report",
    "Projection chain ratchet (changed modules)",
    "Projection chain report",
    "Documentation pins",
})
PR_NOTICE_NAMES = frozenset({
    "Repeated-proof-block notice (advisory)",
    "High-fan-in module impact (advisory)",
    "PR description names (advisory)",
})
# The only `run` lines of a mirrored step that the local run does not repeat: they compute CI's
# base commit, which `full_check.py` passes as `BASE` instead.
PLUMBING = frozenset({
    "set -e",
    "BASE=",
    'if [ "$GITHUB_EVENT_NAME" = pull_request ]; then',
    "BASE=$(git cat-file -p HEAD | sed -n 's/^parent //p' | head -n 1)",
    "fi",
    "BASE=${BASE:-$RECORDED_BASE}",
    'git fetch --no-tags --depth=1 origin "$BASE"',
})
# Step keys the local run accounts for: `if` is deliberately not reproduced (see above), and `id`
# only names the step for later steps.
MIRRORED_KEYS = frozenset({"name", "run", "working-directory", "env", "if", "id"})
# Environment a mirrored step may take from GitHub context: CI's base commit, replaced by `BASE`.
CONTEXT_ENV = frozenset({"RECORDED_BASE"})
STEP_KEY = re.compile(r"      (- |  )([A-Za-z-]+):(?: (.*))?$")  # a step key, indented 8


def unquote(value: str) -> str:
    value = value.strip()
    if len(value) > 1 and value[0] == value[-1] and value[0] in "'\"":
        return value[1:-1]
    return value


def job_lines(text: str, job: str) -> list[str]:
    """The lines of `job`, from its key to the next job."""
    lines = text.splitlines()
    start = lines.index(f"  {job}:")
    end = next((i for i in range(start + 1, len(lines))
                if re.match(r"  \S", lines[i])), len(lines))
    return lines[start:end]


def job_steps(text: str, job: str) -> list[dict]:
    """The steps of `job`, each a dict of its top-level keys (`with` and `env` as raw lines).

    Handles the forms this workflow uses: plain or quoted scalars and `|`/`>` block scalars. A line
    that is neither a step key nor indented deeper than one (inside a block scalar) raises
    `ValueError`, so a misindented key cannot be absorbed into the previous step."""
    lines = job_lines(text, job)
    steps: list[dict] = []
    folded: set[tuple[int, str]] = set()  # (step index, key) of `>` block scalars
    current: dict | None = None
    key = None
    for line in lines[lines.index("    steps:") + 1:]:
        if not line.strip() or line.lstrip().startswith("#"):
            if key and current is not None and isinstance(current.get(key), list):
                current[key].append("")
            continue
        match = STEP_KEY.match(line)
        if match:
            if match[1] == "- ":
                current = {}
                steps.append(current)
            key, value = match[2], (match[3] or "")
            current[key] = [] if value.strip() in ("|", "|-", ">", ">-", "") else unquote(value)
            if value.strip().startswith(">"):
                folded.add((len(steps) - 1, key))
            continue
        if (current is None or key is None or not isinstance(current.get(key), list)
                or len(line) - len(line.lstrip()) <= 8):
            raise ValueError(f"unparsed workflow line: {line!r}")
        current[key].append(line.strip())
    for index, step in enumerate(steps):
        for name, value in step.items():
            if isinstance(value, list) and name != "env":
                step[name] = (" " if (index, name) in folded else "\n").join(value).strip()
    return steps


def script_lines(run: str) -> tuple[str, ...]:
    """The lines of a `run` script other than blank lines and `PLUMBING`."""
    return tuple(line.strip() for line in run.splitlines()
                 if line.strip() and line.strip() not in PLUMBING)


def literal_env(lines: list[str]) -> dict[str, str]:
    env = {}
    for line in lines:
        name, _, value = line.partition(":")
        if line and "${{" not in value:
            env[name.strip()] = unquote(value)
    return env


def header_problems(lines: list[str], job: str) -> list[str]:
    """Job-level settings that would change how CI runs the mirrored steps."""
    problems, section = [], None
    for line in lines[1:lines.index("    steps:")]:
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if re.match(r"    \S", line):
            section = line.strip().split(":", 1)[0]
            if section == "defaults":
                problems.append(f"{job} sets job-level `defaults`, which the local run does not "
                                "reproduce")
        elif section == "env" and "${{" not in line:
            problems.append(f"{job} sets job-level `env` {line.strip()!r}, which the local run "
                            "does not reproduce")
    return problems


def parity_problems(text: str) -> list[str]:
    """Each way the source, Lean and advisory jobs of workflow `text` differ from the local check."""
    problems = []
    steps_by_job = {job: job_steps(text, job) for job in CHECKED_JOBS}
    for job in EXECUTION_JOBS:
        problems.extend(header_problems(job_lines(text, job), job))
    steps = [step for job in CHECKED_JOBS for step in steps_by_job[job]]
    for step in steps:
        if "name" not in step and "run" in step:
            problems.append(f"an unnamed `run` step ({step['run'].splitlines()[0]!r}) cannot be "
                            "classified; name it")
    named_steps = [step for step in steps if "name" in step]
    named = {step["name"]: step for step in named_steps}
    if len(named) != len(named_steps):
        problems.append("checked CI jobs have two steps with the same name")
    mirrored = {step.name: step for step in full.STEPS}
    homes = (mirrored, full.PREFLIGHT, full.CI_ONLY)
    for name in named:
        if sum(name in home for home in homes) != 1:
            problems.append(f"{name}: add the step to exactly one of full_check.STEPS or "
                            "full_check.PREFLIGHT, or record why it stays in CI in "
                            "full_check.CI_ONLY")
    for name in sorted(set().union(*homes) - set(named)):
        problems.append(f"{name}: listed in full_check, but CI no longer has this step in a "
                        "checked job")
    local = [(step.name, step.commands, step.cwd, step.env) for step in full.STEPS]
    local += [(name, (command,), None, {}) for name, command in full.PREFLIGHT.items()]
    for name, commands, cwd, env in local:
        ci = named.get(name)
        if ci is None:
            continue
        extra = sorted(set(ci) - MIRRORED_KEYS)
        if extra:
            hint = "; advisory steps stay CI-only" if "continue-on-error" in extra else ""
            problems.append(f"{name}: sets {', '.join(extra)}, which the local run does not "
                            f"reproduce{hint}")
        lines = script_lines(ci.get("run", ""))
        if lines != commands:
            unknown = [line for line in lines if line not in commands]
            note = f"; neither PLUMBING nor local commands: {unknown}" if unknown else ""
            problems.append(f"{name}: CI runs {lines}, the local run {commands}{note}")
        if cwd != ci.get("working-directory"):
            problems.append(f"{name}: working-directory {ci.get('working-directory')!r} in CI, "
                            f"{cwd!r} locally")
        if env != literal_env(ci.get("env", [])):
            problems.append(f"{name}: literal env {literal_env(ci.get('env', []))} in CI, "
                            f"{env} locally")
        for line in ci.get("env", []):
            variable, _, value = line.partition(":")
            if "${{" in value and variable.strip() not in CONTEXT_ENV:
                problems.append(f"{name}: env {variable.strip()} comes from GitHub context, "
                                "which the local run does not reproduce")
    for job, job_entries in steps_by_job.items():
        order = [step["name"] for step in job_entries
                 if step.get("name") in mirrored]
        expected = [step.name for step in full.STEPS if step.name in order]
        if order != expected:
            problems.append(f"mirrored steps run in {job} in the order {order}, "
                            f"in full_check.STEPS in the order {expected}")
    return problems


class WorkflowParityTests(unittest.TestCase):
    def setUp(self):
        self.text = WORKFLOW.read_text()
        self.named_by_job = {
            job: [step for step in job_steps(self.text, job) if "name" in step]
            for job in CHECKED_JOBS
        }
        self.named = [step for job in CHECKED_JOBS for step in self.named_by_job[job]]

    def test_parser_reads_the_steps_it_compares(self):
        # A parser that silently lost steps would make the parity test vacuous.
        names = [step["name"] for step in self.named]
        source_names = [step["name"] for step in self.named_by_job["source-checks"]]
        notice_names = [step["name"] for step in self.named_by_job["pr-notices"]]
        lean_names = [step["name"] for step in self.named_by_job["lean-checks"]]
        self.assertEqual(set(source_names), SOURCE_CHECK_NAMES)
        self.assertEqual(set(notice_names), PR_NOTICE_NAMES)
        self.assertIn("Tidy statement ratchet", names)
        self.assertIn("lake build", lean_names)
        self.assertGreater(len(names), 25)
        handoff = next(step for step in self.named if step["name"] == "Test Lake build handoff reuse")
        local = next(step for step in full.STEPS if step.name == handoff["name"])
        self.assertEqual(script_lines(handoff["run"]), local.commands)  # a folded `>-` scalar

    def test_full_check_mirrors_ci(self):
        problems = parity_problems(self.text)
        self.assertEqual(problems, [], "\n".join(problems))

    def test_preflight_steps_run_in_check_sh_with_ci_commands(self):
        lines = [line.strip() for line in (REPO / "scripts/check.sh").read_text().splitlines()
                 if not line.lstrip().startswith("#")]
        for name, command in full.PREFLIGHT.items():
            with self.subTest(step=name):
                self.assertTrue(any(line.endswith(f" {command}") for line in lines), command)

    def test_post_build_audits_follow_the_build(self):
        names = [step.name for step in full.STEPS]
        for audit in ("Tidy statement ratchet", "Result registry references", "Changed-file lints"):
            self.assertGreater(names.index(audit), names.index("lake build"))

    def test_pr_and_full_lint_steps_are_complementary(self):
        lean = {step["name"]: step for step in self.named_by_job["lean-checks"]}
        self.assertEqual(lean["lake lint (affected modules)"]["if"], "github.event_name == 'pull_request'")
        self.assertEqual(lean["lake lint"]["if"], "github.event_name != 'pull_request'")
        self.assertIn("python3 -B scripts/quick_check.py --lint-only --base \"$BASE\"",
                      lean["lake lint (affected modules)"]["run"])
        self.assertEqual(lean["lake lint"]["run"], "lake lint")

    def test_fused_build_tooling_gates_and_push_only_advisory_reports(self):
        select_header = "\n".join(job_lines(self.text, "select-checks"))
        self.assertIn("tooling: ${{ steps.select.outputs.tooling }}", select_header)
        source_header = "\n".join(
            job_lines(self.text, "source-checks")[
                :job_lines(self.text, "source-checks").index("    steps:")])
        self.assertNotIn("needs:", source_header)
        lean = {step["name"]: step for step in self.named_by_job["lean-checks"]}
        self.assertIn("CslibFrontierTests", lean["lake build"]["run"])
        self.assertNotIn("lake test", lean)
        for name in (
            "Test Lake build handoff reuse",
            "Test real Lake interrupt cleanup",
            "Test real Lake cache publication staging",
            "Test post-build Python tooling",
            "Test import generation with custom source directories",
        ):
            with self.subTest(step=name):
                self.assertEqual(lean[name]["if"],
                                 "needs.select-checks.outputs.tooling == 'true'")
        for name in ("Security premise report", "Reduction witness report"):
            with self.subTest(report=name):
                self.assertEqual(lean[name]["if"], "github.event_name == 'push'")

    def test_merge_groups_build_the_same_targets_with_fail_fast(self):
        # The merge-group build must check exactly what the mirrored build checks; it may only
        # stop scheduling after the first failure. Exactly one of the two runs for every event.
        lean = {step["name"]: step for step in self.named_by_job["lean-checks"]}
        full_build = lean["lake build"]
        fail_fast = lean["lake build (merge group, fail fast)"]
        self.assertEqual((full_build["id"], fail_fast["id"]), ("build", "build-fail-fast"))
        self.assertEqual(full_build["if"], "github.event_name != 'merge_group'")
        self.assertEqual(fail_fast["if"], "github.event_name == 'merge_group'")
        self.assertEqual(set(fail_fast), {"name", "id", "if", "run"})
        words = full_build["run"].split()
        self.assertEqual(words[:2], ["lake", "build"])
        self.assertEqual([word for word in fail_fast["run"].split() if word != "--fail-fast"],
                         words)
        self.assertEqual(fail_fast["run"].split().count("--fail-fast"), 1)
        steps = job_steps(self.text, "lean-checks")
        names = [step.get("name") for step in steps]
        self.assertEqual(names.index("lake build (merge group, fail fast)"),
                         names.index("lake build") + 1)
        # A later step that needs a successful build must either run only on pushes or accept
        # the fail-fast build too; otherwise it would silently stop running in merge groups.
        gated = [step for step in steps
                 if "steps.build.outcome == 'success'" in step.get("if", "")]
        self.assertGreaterEqual(len(gated), 2)
        for step in gated:
            with self.subTest(step=step.get("name")):
                condition = step["if"]
                if "github.event_name == 'push'" not in condition:
                    self.assertIn("steps.build-fail-fast.outcome == 'success'", condition)

    def test_local_steps_are_not_ci_steps(self):
        # A local step must neither pass for a mirror of a CI step nor hide one from the parity check.
        ci = {step["name"] for step in self.named}
        others = {step.name for step in full.STEPS} | set(full.PREFLIGHT) | set(full.CI_ONLY)
        for step in full.LOCAL_STEPS:
            with self.subTest(step=step.name):
                self.assertNotIn(step.name, ci | others)


class AncestorHandoffFailurePolicyTests(unittest.TestCase):
    """Only the ancestor handoff's exit status 125 (unconfirmed process shutdown) stops the job.

    The step is optional (`continue-on-error`), which alone would also hide that status from the
    Git, cache and build steps after it. The step's own script and the guard's are run here with
    a stand-in for the handoff command; the guard's condition is compared as text."""

    RESTORE, GUARD = ("Restore nearest ancestor merge-group build outputs",
                      "Stop after an unconfirmed ancestor-handoff shutdown")
    CONDITION = "steps.ancestor-handoff.outputs.exit-status == '125'"

    def setUp(self):
        self.steps = job_steps(WORKFLOW.read_text(), "lean-checks")
        self.index = next(i for i, step in enumerate(self.steps)
                          if step.get("name") == self.RESTORE)
        self.restore, self.guard = self.steps[self.index], self.steps[self.index + 1]

    def run_script(self, script, status):
        """Run a step's script as Actions does, with `python3` exiting with `status`."""
        with tempfile.TemporaryDirectory(prefix="handoff-policy-") as temporary:
            stub = Path(temporary, "python3")
            stub.write_text(f"#!/bin/sh\necho \"$@\" > '{temporary}/arguments'\nexit {status}\n")
            stub.chmod(0o755)
            output = Path(temporary, "output")
            output.touch()
            result = subprocess.run(
                ["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", script],
                env={**os.environ, "PATH": f"{temporary}{os.pathsep}{os.environ['PATH']}",
                     "GITHUB_OUTPUT": str(output)}, capture_output=True, text=True)
            arguments = Path(temporary, "arguments")
            return (result, dict(line.split("=", 1) for line in output.read_text().splitlines()),
                    arguments.read_text().strip() if arguments.exists() else None)

    def test_optional_step_records_the_handoff_exit_status(self):
        self.assertEqual(self.restore.get("id"), "ancestor-handoff")
        self.assertEqual(self.restore.get("continue-on-error"), "true")
        self.assertEqual(self.restore.get("timeout-minutes"), "10")
        for status in (0, 1, 124, 125):
            with self.subTest(status=status):
                result, outputs, arguments = self.run_script(self.restore["run"], status)
                self.assertEqual(arguments, "-B scripts/cache_handoff.py restore --ancestor")
                self.assertEqual(result.returncode, status)
                self.assertEqual(outputs, {"exit-status": str(status)})
                # Only an unconfirmed shutdown satisfies the guard; a miss (0) and any other
                # failure of the optional step leave the job running.
                self.assertEqual(f"steps.ancestor-handoff.outputs.exit-status == '{status}'"
                                 == self.CONDITION, status == 125)

    def test_guard_fails_the_job_before_any_other_step(self):
        self.assertEqual(self.guard.get("name"), self.GUARD)
        self.assertEqual(set(self.guard), {"name", "if", "run"})  # not optional, not bounded away
        self.assertEqual(self.guard["if"], self.CONDITION)
        result, outputs, arguments = self.run_script(self.guard["run"], 0)
        self.assertEqual((result.returncode, outputs, arguments), (125, {}, None))
        self.assertIn("::error title=Unconfirmed cache process shutdown::", result.stdout)
        names = [step.get("name") for step in self.steps]
        for later in ("Restore build outputs from the remote cache",
                      "Restore validated merge-group build outputs", "lake build"):
            self.assertGreater(names.index(later), self.index + 1)

    def test_pr_handoff_is_an_optional_reader_before_the_remote_cache(self):
        names = [step.get("name") for step in self.steps]
        index = names.index("Restore PR base merge-group build outputs")
        self.assertLess(self.index + 1, index)
        self.assertLess(index, names.index("Restore build outputs from the remote cache"))
        step = self.steps[index]
        self.assertEqual(step["run"], "python3 -B scripts/cache_handoff.py restore --pr-base")
        self.assertEqual(step["continue-on-error"], "true")
        self.assertIn("github.event_name == 'pull_request' && github.base_ref == 'main'", step["if"])
        self.assertIn("vars.DISABLE_PR_BUILD_HANDOFF", step["if"])
        self.assertIn("RESTORED_LAKE_KEY: ${{ steps.lake-cache.outputs.cache-matched-key }}", step["env"])
        for name in ("Stage merge-group build outputs", "Upload merge-group build outputs"):
            self.assertIn("github.event_name == 'merge_group' &&", self.steps[names.index(name)]["if"])

    def test_no_later_step_runs_after_the_guard_fails(self):
        # A failed step skips every later step whose condition has no status function. Those that
        # have one must require a completed build or explicitly exclude the guard failure. The
        # guard only fires in merge groups, which run the fail-fast build step.
        for build_id in ("build", "build-fail-fast"):
            build = next(step for step in self.steps if step.get("id") == build_id)
            self.assertGreater(self.steps.index(build), self.index + 1)
            self.assertNotRegex(build.get("if", ""), r"always\(\)|cancelled\(\)|failure\(\)")
        for step in self.steps[self.index + 2:]:
            condition = step.get("if", "")
            if re.search(r"always\(\)|cancelled\(\)|failure\(\)", condition):
                with self.subTest(step=step.get("name")):
                    if "steps.ancestor-handoff.outputs.exit-status != '125'" not in condition:
                        self.assertIn("steps.build.outcome == 'success'", condition)

    def test_handoff_cli_reserves_125_for_unconfirmed_shutdown(self):
        sys.path.insert(0, str(REPO / "scripts"))
        import cache_handoff
        self.addCleanup(sys.path.remove, str(REPO / "scripts"))
        for error, status in ((cache_handoff.UnsafeShutdown("unconfirmed"), 125),
                              (cache_handoff.Rejected("no handoff"), 0),
                              (subprocess.TimeoutExpired("gh", 60), 0), (OSError("transport"), 0)):
            with self.subTest(error=error), \
                    patch("sys.argv", ["cache_handoff.py", "restore", "--ancestor"]), \
                    patch.object(cache_handoff, "restore_ancestor", side_effect=error), \
                    patch("sys.stdout", io.StringIO()), patch("sys.stderr", io.StringIO()):
                self.assertEqual(cache_handoff.main(), status)


class AggregatorTests(unittest.TestCase):
    def setUp(self):
        self.text = WORKFLOW.read_text()
        self.lines = job_lines(self.text, AGGREGATOR_JOB)
        self.steps = job_steps(self.text, AGGREGATOR_JOB)

    def test_required_context_depends_on_both_jobs_and_forwards_lean_publication(self):
        header = "\n".join(self.lines[:self.lines.index("    steps:")])
        self.assertIn("needs: [select-checks, source-checks, lean-checks]", header)
        self.assertIn("if: always()", header)
        self.assertIn("publication: ${{ needs.lean-checks.outputs.publication }}", header)
        self.assertNotIn("steps.upload-publication.outputs", header)
        self.assertEqual([step.get("name") for step in self.steps],
                         ["Require source and Lean validation"])
        env = self.steps[0]["env"]
        self.assertIn("SOURCE_RESULT: ${{ needs.source-checks.result }}", env)
        self.assertIn("LEAN_RESULT: ${{ needs.lean-checks.result }}", env)

    def test_execution_jobs_can_start_in_parallel(self):
        for job in EXECUTION_JOBS:
            with self.subTest(job=job):
                lines = job_lines(self.text, job)
                header = "\n".join(lines[:lines.index("    steps:")])
                self.assertNotIn("needs: source-checks", header)
                self.assertNotIn("needs: lean-checks", header)

    def test_gate_accepts_only_the_selected_lean_result(self):
        env = self.steps[0]["env"]
        self.assertIn("SELECTION_RESULT: ${{ needs.select-checks.result }}", env)
        self.assertIn("EXPECTED_LEAN: ${{ github.event_name == 'pull_request' && "
                      "needs.select-checks.outputs.lean == 'false' && 'skipped' || 'success' }}", env)
        script = self.steps[0]["run"]
        for expected in ("success", "skipped"):
            for selection, source, lean in (
                ("success", "success", "success"), ("success", "success", "skipped"),
                ("failure", "success", expected), ("success", "failure", expected),
                ("success", "success", "failure"), ("success", "success", "cancelled")
            ):
                with self.subTest(expected=expected, selection=selection, source=source, lean=lean):
                    result = subprocess.run(["bash", "-e", "-c", script], env={
                        **os.environ, "SELECTION_RESULT": selection, "SOURCE_RESULT": source,
                        "EXPECTED_LEAN": expected, "LEAN_RESULT": lean})
                    self.assertEqual(result.returncode == 0,
                                     selection == source == "success" and lean == expected)


class HandoffOrderingTests(unittest.TestCase):
    """Every unit-replacing build handoff precedes remote-cache top-up, and exact hits skip it."""

    def test_all_handoffs_precede_remote_cache_and_exact_hits_skip_redundant_top_up(self):
        steps = job_steps(WORKFLOW.read_text(), "lean-checks")
        names = [step.get("name") for step in steps]
        remote_idx = names.index("Restore build outputs from the remote cache")
        for handoff_name in (
            "Restore nearest ancestor merge-group build outputs",
            "Restore PR base merge-group build outputs",
            "Restore validated merge-group build outputs",
        ):
            with self.subTest(handoff=handoff_name):
                self.assertLess(names.index(handoff_name), remote_idx)
        pr_step = steps[names.index("Restore PR base merge-group build outputs")]
        main_step = steps[names.index("Restore validated merge-group build outputs")]
        remote_step = steps[remote_idx]
        self.assertEqual(pr_step.get("id"), "pr-handoff")
        self.assertEqual(main_step.get("id"), "main-handoff")
        self.assertIn("steps.pr-handoff.outputs.restored != 'true'", remote_step["if"])
        self.assertIn("steps.main-handoff.outputs.restored != 'true'", remote_step["if"])
        self.assertNotIn("steps.ancestor-handoff", remote_step["if"])


TIDY = "          python3 -B scripts/check_tidy_surface.py\n"
REGISTRY = ('      - name: "Result registry references"\n'
            "        run: python3 -B scripts/results_registry.py --compiled\n")


class ParityProblemTests(unittest.TestCase):
    """Negative controls: each edit makes CI do something the local run would not."""

    def report(self, *edits: tuple[str, str]) -> list[str]:
        text = WORKFLOW.read_text()
        for old, new in edits:
            self.assertEqual(text.count(old), 1, old)
            text = text.replace(old, new)
        return parity_problems(text)

    def assertReported(self, problems: list[str], *fragments: str):
        self.assertTrue(any(all(f in p for f in fragments) for p in problems),
                        f"no problem mentions {fragments}: {problems}")

    def test_extra_lines_in_a_mirrored_script(self):
        for line in ("bash scripts/ci/extra_gate.sh", "cd scripts", "export TIDY_STRICT=1",
                     "python3 -B scripts/extra_gate.py", "if true; then"):
            with self.subTest(line=line):
                problems = self.report((TIDY, f"          {line}\n{TIDY}"))
                self.assertReported(problems, "Tidy statement ratchet", line)

    def test_changed_arguments(self):
        problems = self.report((REGISTRY, REGISTRY.replace("--compiled", "--compiled --strict")))
        self.assertReported(problems, "Result registry references", "--strict")

    def test_step_settings_the_local_run_does_not_reproduce(self):
        for setting, fragment in (("working-directory: scripts", "working-directory"),
                                  ("env:\n          STRICT: \"1\"", "literal env"),
                                  ("env:\n          TOKEN: ${{ secrets.TOKEN }}", "GitHub context"),
                                  ("shell: sh {0}", "shell"),
                                  ("continue-on-error: true", "advisory"),
                                  ("timeout-minutes: 5", "timeout-minutes")):
            with self.subTest(setting=setting):
                problems = self.report((REGISTRY, f"{REGISTRY}        {setting}\n"))
                self.assertReported(problems, "Result registry references", fragment)

    def test_mirrored_step_becomes_an_action(self):
        problems = self.report((REGISTRY, '      - name: "Result registry references"\n'
                                          "        uses: ./.github/actions/registry\n"))
        self.assertReported(problems, "Result registry references", "uses")

    def test_unclassified_unnamed_removed_and_reordered_steps(self):
        new = '      - name: "New gate"\n        run: python3 -B scripts/new_gate.py\n'
        self.assertReported(self.report((REGISTRY, new + REGISTRY)), "New gate", "CI_ONLY")
        unnamed = "      - run: python3 -B scripts/new_gate.py\n"
        self.assertReported(self.report((REGISTRY, unnamed + REGISTRY)), "unnamed")
        self.assertReported(self.report((REGISTRY, "")), "Result registry references",
                            "no longer")
        tidy = '      - name: "Tidy statement ratchet"\n'
        self.assertReported(self.report((REGISTRY, ""), (tidy, REGISTRY + tidy)), "order")

    def test_preflight_drift(self):
        command = "python3 -B scripts/check_operator_manual.py"
        problems = self.report((f"run: {command}\n", f"run: {command} --strict\n"))
        self.assertReported(problems, "Operator manual links and excerpts", "--strict")

    def test_job_level_settings(self):
        anchor = "  lean-checks:\n"
        defaults = "    defaults:\n      run:\n        shell: sh\n"
        env = "    env:\n      STRICT: \"1\"\n"
        self.assertReported(self.report((anchor, anchor + defaults)), "defaults")
        self.assertReported(self.report((anchor, anchor + env)), "STRICT")

    def test_misindented_key_is_not_absorbed(self):
        with self.assertRaisesRegex(ValueError, "unparsed workflow line"):
            self.report((REGISTRY, REGISTRY.replace("      - name", "      -   name")))


class RunnerTests(unittest.TestCase):
    def run_steps(self, steps, base="example-base"):
        out = io.StringIO()
        with tempfile.TemporaryDirectory() as temp, \
             patch.object(full.tempfile, "tempdir", temp):
            root = Path(temp) / "checkout"
            (root / "sub").mkdir(parents=True)
            status = full.run_steps(steps, base, root=root, out=out)
            leftover = sorted(p.name for p in Path(temp).glob("cslib-frontier-check.*"))
        return status, out.getvalue(), leftover

    def test_every_step_runs_and_failures_are_reported_with_logs(self):
        steps = (
            full.Step("first", ('test "$BASE" = example-base', "echo first-output")),
            full.Step("second", ("echo second-log", "false", "echo unreachable")),
            full.Step("third", ('test "$(basename "$PWD")" = sub', 'test "$FLAG" = on'),
                      cwd="sub", env={"FLAG": "on"}),
        )
        status, out, leftover = self.run_steps(steps)
        self.assertEqual(status, 1)
        self.assertIn("ok    first\n", out)
        self.assertNotIn("first-output", out)
        self.assertIn("FAIL  second\nsecond-log\n", out)
        self.assertNotIn("unreachable", out)  # `bash -e`, as GitHub runs a step
        self.assertIn("ok    third\n", out)
        self.assertIn("Full logs: ", out)
        self.assertEqual(len(leftover), 1)

    def test_success_removes_the_logs(self):
        status, out, leftover = self.run_steps((full.Step("only", ("true",)),))
        self.assertEqual((status, out, leftover), (0, "ok    only\n", []))

    def test_main_passes_the_base_to_the_steps(self):
        with patch.object(full.check_vm_map_count, "preflight", return_value=0), \
             patch.object(full, "run_steps", return_value=0) as run:
            self.assertEqual(full.main(["--base", "abc123"]), 0)
            self.assertEqual(run.call_args.args, (full.STEPS + full.LOCAL_STEPS, "abc123"))
            full.main([])
            self.assertEqual(run.call_args.args, (full.STEPS + full.LOCAL_STEPS, "origin/main"))

    def test_main_stops_when_vm_map_count_preflight_fails(self):
        with patch.object(full.check_vm_map_count, "preflight", return_value=1), \
             patch.object(full, "run_steps", return_value=0) as run:
            self.assertEqual(full.main([]), 1)
            run.assert_not_called()
            self.assertEqual(full.main(["--skip-map-count-check"]), 0)
            run.assert_called_once()


class AdvisoryNoticeTests(unittest.TestCase):
    """Advisory notices run early on pull requests and never block `ci-checks`."""

    def setUp(self):
        self.text = WORKFLOW.read_text()

    def test_pr_notices_job_is_independent_nonblocking_and_pull_request_only(self):
        lines = job_lines(self.text, "pr-notices")
        header = "\n".join(lines[:lines.index("    steps:")])
        self.assertIn("if: github.event_name == 'pull_request'", header)
        self.assertNotIn("needs:", header)
        self.assertIn("contents: read", header)
        aggregator = "\n".join(job_lines(self.text, AGGREGATOR_JOB))
        self.assertNotIn("pr-notices", aggregator)
        steps = {s["name"]: s for s in job_steps(self.text, "pr-notices") if "name" in s}
        self.assertEqual(set(steps), PR_NOTICE_NAMES)
        for name, step in steps.items():
            with self.subTest(step=name):
                self.assertEqual(step.get("continue-on-error"), "true")
                self.assertIn("timeout-minutes", step)
        self.assertIn("--fetch-deps", steps["PR description names (advisory)"]["run"])

    def test_parallel_definition_notices_run_right_after_lint_and_upload_early_summary(self):
        lean_steps = job_steps(self.text, "lean-checks")
        names = [s.get("name") for s in lean_steps]
        parallel_idx = names.index("Parallel-definition and duplicate-statement notices (advisory)")
        upload_idx = names.index("Upload early Lean advisory notices")
        self.assertGreater(parallel_idx, names.index("lake lint"))
        self.assertEqual(upload_idx, parallel_idx + 1)
        self.assertLess(upload_idx, names.index("Tidy statement ratchet"))
        self.assertLess(upload_idx, names.index("Changed-file lints"))
        parallel_step = lean_steps[parallel_idx]
        upload_step = lean_steps[upload_idx]
        self.assertEqual(parallel_step.get("if"), "github.event_name == 'pull_request'")
        self.assertEqual(parallel_step.get("continue-on-error"), "true")
        self.assertIn("lean-advisory-notices.md", parallel_step["run"])
        self.assertIn("--summary-file", parallel_step["run"])
        self.assertNotIn("| tee", parallel_step["run"])
        self.assertEqual(upload_step.get("if"), "github.event_name == 'pull_request'")
        self.assertEqual(upload_step.get("continue-on-error"), "true")

    def test_parallel_definition_step_excludes_workflow_commands_and_marks_failures_incomplete(self):
        lean_steps = job_steps(self.text, "lean-checks")
        script = next(s["run"] for s in lean_steps
                      if s.get("name") == "Parallel-definition and duplicate-statement notices (advisory)")
        with tempfile.TemporaryDirectory(prefix="advisory-step-") as tmp:
            tmp_path = Path(tmp)
            env_git = {**os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
                       "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"}
            origin = tmp_path / "origin.git"
            subprocess.run(["git", "init", "--bare", "-q", str(origin)], check=True, env=env_git)
            work = tmp_path / "work"
            work.mkdir()
            subprocess.run(["git", "init", "-q"], cwd=work, check=True, env=env_git)
            subprocess.run(["git", "remote", "add", "origin", str(origin)], cwd=work, check=True)
            (work / "README").write_text("base\n")
            subprocess.run(["git", "add", "README"], cwd=work, check=True)
            subprocess.run(["git", "-c", "commit.gpgsign=false", "commit", "-qm", "base"],
                           cwd=work, check=True, env=env_git)
            base_sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=work, text=True).strip()
            subprocess.run(["git", "push", "-q", "origin", "HEAD:refs/heads/main"], cwd=work, check=True)
            (work / "scripts").mkdir()

            def run_step(stub_body: str, recorded_base: str = base_sha) -> tuple[int, str, str, str]:
                (work / "scripts/parallel_defs.py").write_text(stub_body, encoding="utf-8")
                runner_temp = tmp_path / "runner_temp"
                shutil.rmtree(runner_temp, ignore_errors=True)
                runner_temp.mkdir()
                step_summary = tmp_path / "step_summary.md"
                step_summary.write_text("", encoding="utf-8")
                res = subprocess.run(
                    ["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c", script],
                    cwd=work,
                    env={**os.environ, "RUNNER_TEMP": str(runner_temp),
                         "GITHUB_STEP_SUMMARY": str(step_summary),
                         "RECORDED_BASE": recorded_base},
                    capture_output=True, text=True,
                )
                artifact_md = (runner_temp / "lean-advisory-notices.md").read_text(encoding="utf-8")
                return res.returncode, res.stdout, artifact_md, step_summary.read_text(encoding="utf-8")

            # 1. Findings emit `::notice` to stdout while artifact & summary get pure Markdown.
            clean_stub = (
                "import os, pathlib, sys\n"
                "args = sys.argv[1:]\n"
                "sf = pathlib.Path(args[args.index('--summary-file') + 1])\n"
                "kind = 'Duplicate-statement' if '--theorems' in args else 'Parallel-definition'\n"
                "md = f'### {kind} notice (advisory)\\n\\n1 candidate.\\n'\n"
                "print(md, end='')\n"
                "sf.open('a').write(md)\n"
                "open(os.environ['GITHUB_STEP_SUMMARY'], 'a').write(md)\n"
                "print(f'::notice title=Possible {kind.lower()}::candidate')\n"
            )
            rc, stdout, artifact_md, summary_md = run_step(clean_stub)
            self.assertEqual(rc, 0)
            self.assertIn("::notice title=Possible parallel-definition::", stdout)
            self.assertIn("### Parallel-definition notice (advisory)", artifact_md)
            self.assertIn("### Duplicate-statement notice (advisory)", artifact_md)
            self.assertNotIn("::notice", artifact_md)
            self.assertEqual(artifact_md, summary_md)

            # 2. If the first scanner crashes non-zero, status is preserved (not masked), the
            #    second scanner still runs, and incomplete coverage is explicit in the artifact.
            crash_stub = (
                "import os, pathlib, sys\n"
                "args = sys.argv[1:]\n"
                "if '--theorems' not in args:\n"
                "    sys.exit(2)\n"
                "sf = pathlib.Path(args[args.index('--summary-file') + 1])\n"
                "md = '### Duplicate-statement notice (advisory)\\n\\nClean.\\n'\n"
                "sf.open('a').write(md)\n"
                "open(os.environ['GITHUB_STEP_SUMMARY'], 'a').write(md)\n"
            )
            rc, _, artifact_md, summary_md = run_step(crash_stub)
            self.assertEqual(rc, 2)
            self.assertIn("**Incomplete advisory check:** `parallel_defs.py` exited with status 2.",
                          artifact_md)
            self.assertIn("### Duplicate-statement notice (advisory)", artifact_md)
            self.assertIn("**Incomplete advisory check:**", summary_md)

            # 3. If `git fetch` of the base commit fails, status is non-zero and artifact records it.
            subprocess.run(["git", "commit", "--allow-empty", "-qm", "second"],
                           cwd=work, check=True, env=env_git)
            # Shallow graft or unfetchable Recorded Base: force fetch failure via missing SHA.
            subprocess.run(["git", "remote", "set-url", "origin", str(tmp_path / "missing.git")],
                           cwd=work, check=True)
            rc, _, artifact_md, summary_md = run_step(clean_stub)
            self.assertNotEqual(rc, 0)
            self.assertIn("**Incomplete advisory check:** `git fetch` of comparison base",
                          artifact_md)
            self.assertIn("neither duplication scan ran", summary_md)


if __name__ == "__main__":
    unittest.main()
