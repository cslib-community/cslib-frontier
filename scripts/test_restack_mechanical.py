"""Temporary-repository tests for scripts/restack_mechanical.py: a local bare repository stands in
for GitHub, `gh` is stubbed, and the real resolvers and `scripts/check_restack.py` run from the
fixture's `main`."""

from __future__ import annotations

import contextlib
import io
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import restack_mechanical  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]

GIT_ENV = {
    "GIT_AUTHOR_NAME": "Test",
    "GIT_AUTHOR_EMAIL": "test@example.com",
    "GIT_COMMITTER_NAME": "Test",
    "GIT_COMMITTER_EMAIL": "test@example.com",
    "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_CONFIG_NOSYSTEM": "1",
}

LAKEFILE = 'name = "fixture"\n\n[[lean_lib]]\nname = "CslibFrontier"\n'
PREAMBLE = "module  -- shake: keep-all --deprecated_module: ignore\n\n"
ATTRIBUTES = ("CslibFrontier.lean merge=leanagg\nreferences.bib merge=bibkeys\n"
              "manual/sources.md merge=sourcesmd\n")
LIB = "namespace Foo\ndef x := 1\nend Foo\n\nnamespace Bar\ndef y := 2\nend Bar\n"
# What the run uses from the fixture's `main`: the check, the resolvers and the modules that they
# import.
SCRIPTS = ("check_restack.py", "resolve_bib_conflict.py", "resolve_aggregate_conflict.py",
           "aggregate_order.py", "resolve_sources_conflict.py", "sources_format.py",
           "check_hygiene.py", "proof_lengths.py", "upstream.py")
# `manual/sources.md` before its conversion to one sentence per line.
SOURCES = '# Sources\n\n<a id="alpha"></a>\n## alpha\n\nAlpha one. Alpha two. Alpha three.\n'

def aggregate(*names: str) -> str:
    """`CslibFrontier.lean` importing `CslibFrontier.<name>` for each name, in the order given; as
    in `test_check_restack.py`, the fixture names' alphabetical order is `mk_all`'s hash order."""
    return PREAMBLE + "".join(f"public import CslibFrontier.{name}\n" for name in names)


def modules(*names: str) -> dict[str, str]:
    return {f"CslibFrontier/{name}.lean": f"theorem {name.lower()}_holds : True := trivial\n"
            for name in names}


def entry(key: str, title: str = "T") -> str:
    return f"@article{{{key},\n  author = {{A}},\n  title  = {{{title}}}\n}}"


def bib(*entries: str) -> str:
    return "\n\n".join(entries) + "\n"


@unittest.skipUnless(shutil.which("git"), "git is required")
class RestackMechanicalTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.tmp = pathlib.Path(tmp.name)
        environment = mock.patch.dict(os.environ, GIT_ENV)
        environment.start()
        self.addCleanup(environment.stop)
        self.origin = self.tmp / "origin.git"
        self.root = self.tmp / "clone"
        subprocess.run(["git", "init", "-q", "--bare", "-b", "main", str(self.origin)], check=True)
        self.root.mkdir()
        self.git("init", "-q", "-b", "main")
        self.git("remote", "add", "origin", str(self.origin))
        scripts = {f"scripts/{name}": (ROOT / "scripts" / name).read_text() for name in SCRIPTS}
        self.commit("base", {"lakefile.toml": LAKEFILE, ".gitattributes": ATTRIBUTES,
                             ".gitignore": ".lake/\n",
                             "CslibFrontier.lean": aggregate("Ant", "Cap", "Emu"),
                             **modules("Ant", "Cap", "Emu"), "Lib.lean": LIB,
                             "references.bib": bib(entry("a"), entry("c"), entry("e")), **scripts})
        self.git("push", "-q", "origin", "main")

    def git(self, *args: str, root: pathlib.Path | None = None) -> str:
        return subprocess.run(["git", "-C", str(root or self.root), *args], capture_output=True,
                              text=True, check=True).stdout.strip()

    def commit(self, message: str, files: dict[str, str | None]) -> str:
        for name, content in files.items():
            path = self.root / name
            if content is None:
                path.unlink()
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD")

    def feature(self, files: dict[str, str | None] | None = None) -> str:
        """Push a PR branch (number 7) adding `CslibFrontier.Bee`; returns its head."""
        self.git("checkout", "-q", "-b", "feature", "main")
        head = self.commit("feature", files or {
            "CslibFrontier.lean": aggregate("Ant", "Bee", "Cap", "Emu"), **modules("Bee")})
        self.publish(head)
        return head

    def publish(self, head: str) -> None:
        self.git("push", "-q", "-f", "origin", f"{head}:refs/heads/feature",
                 f"{head}:refs/pull/7/head")

    def on_main(self, files: dict[str, str | None]) -> str:
        self.git("checkout", "-q", "main")
        head = self.commit("main moves", files)
        self.git("push", "-q", "origin", "main")
        return head

    def remote(self, ref: str = "refs/heads/feature") -> str:
        return self.git("rev-parse", ref, root=self.origin)

    def run_script(self, approved: str, *extra: str, head: str | None = None) -> tuple[int, str]:
        info = {"number": 7, "state": "OPEN", "baseRefName": "main", "headRefName": "feature",
                "headRefOid": head or self.remote(), "isCrossRepository": False}
        output = io.StringIO()
        with mock.patch.object(restack_mechanical, "pr_info", return_value=info), \
                contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            code = restack_mechanical.main(["7", "--approved-head", approved,
                                            "--repo", str(self.root), *extra])
        return code, output.getvalue()

    def state(self) -> tuple[str, ...]:
        """Everything a run must leave alone: refs, worktrees, HEAD and status of the checkout,
        and the remote's refs."""
        return (self.git("for-each-ref"), self.git("worktree", "list", "--porcelain"),
                self.git("rev-parse", "HEAD"), self.git("status", "--porcelain", "--ignored"),
                self.git("for-each-ref", root=self.origin))

    def aggregate_conflict(self) -> str:
        approved = self.feature()
        self.on_main({"CslibFrontier.lean": aggregate("Ant", "Bees", "Cap", "Emu"),
                      **modules("Bees")})
        return approved

    def assert_restacked(self, old: str, code: int, out: str) -> str:
        self.assertEqual(code, 0, out)
        new = self.remote()
        self.assertNotEqual(new, old)
        self.assertEqual(self.git("rev-parse", f"{new}^1", f"{new}^2").split(),
                         [old, self.remote("refs/heads/main")])
        verdict = "Restack check: identical to the approved change"
        self.assertIn(f"restack_mechanical: approval pre-check: {verdict}", out)
        self.assertEqual(sum(line.startswith(verdict) for line in out.splitlines()), 1, out)
        self.assertIn(f"python3 scripts/queue_pr.py 7 {new}", out)
        self.assertEqual(self.git("worktree", "list").count("\n"), 0, "a worktree was left behind")
        return new

    # Mechanical restacks.

    def test_aggregate_conflict_is_merged_regenerated_and_pushed(self) -> None:
        approved = self.aggregate_conflict()
        before = self.git("status", "--porcelain", "--ignored"), self.git("rev-parse", "HEAD")
        code, out = self.run_script(approved, "--push")
        new = self.assert_restacked(approved, code, out)
        self.assertIn("in: CslibFrontier.lean", out)
        self.assertEqual(self.git("show", f"{new}:CslibFrontier.lean"),
                         aggregate("Ant", "Bee", "Bees", "Cap", "Emu").rstrip("\n"))
        self.assertEqual((self.git("status", "--porcelain", "--ignored"),
                          self.git("rev-parse", "HEAD")), before)

    def alphabetical_rollout_base(self) -> None:
        """Set `main` to a pre-#8486 commit without `aggregate_order.py` and with `A`, `C`, `D`, `E`
        in alphabetical order (`mk_all` hash order is `A`, `D`, `C`, `E`)."""
        self.on_main({"scripts/aggregate_order.py": None,
                      "CslibFrontier/Ant.lean": None, "CslibFrontier/Cap.lean": None,
                      "CslibFrontier/Emu.lean": None, **modules("A", "C", "D", "E"),
                      "CslibFrontier.lean": aggregate("A", "C", "D", "E")})

    def rollout_hash_order_on_main(self) -> None:
        self.on_main({"scripts/aggregate_order.py":
                      (ROOT / "scripts" / "aggregate_order.py").read_text(),
                      "CslibFrontier.lean": aggregate("A", "D", "C", "E")})

    def test_alphabetical_pr_adding_module_is_restacked_across_hash_rollout(self) -> None:
        self.alphabetical_rollout_base()
        approved = self.feature({"CslibFrontier.lean": aggregate("A", "B", "C", "D", "E"),
                                 **modules("B")})
        self.rollout_hash_order_on_main()
        code, out = self.run_script(approved, "--push")
        new = self.assert_restacked(approved, code, out)
        self.assertIn("in: CslibFrontier.lean", out)
        self.assertEqual(self.git("show", f"{new}:CslibFrontier.lean"),
                         aggregate("A", "D", "C", "B", "E").rstrip("\n"))

    def test_alphabetical_pr_without_aggregate_change_crosses_hash_rollout(self) -> None:
        self.alphabetical_rollout_base()
        approved = self.feature({"Lib.lean": LIB.replace("y := 2", "y := 3")})
        self.rollout_hash_order_on_main()
        code, out = self.run_script(approved, "--push", "--allow-clean")
        new = self.assert_restacked(approved, code, out)
        self.assertEqual(self.git("show", f"{new}:CslibFrontier.lean"),
                         aggregate("A", "D", "C", "E").rstrip("\n"))

    def test_bibliography_conflict_is_merged_by_key_and_pushed(self) -> None:
        approved = self.feature({"references.bib": bib(entry("a"), entry("b"), entry("c"),
                                                       entry("e"))})
        resolver = "scripts/resolve_bib_conflict.py"
        code = (self.root / resolver).read_text()
        main_guard = 'if __name__ == "__main__":'
        self.assertIn(main_guard, code)
        code = code.replace(main_guard, "if pathlib.Path.cwd().resolve() != "
                            "pathlib.Path(__file__).resolve().parents[1]:\n"
                            "    raise SystemExit('resolver invoked outside its checkout')\n\n"
                            + main_guard)
        self.on_main({"references.bib": bib(entry("a"), entry("bb"), entry("c"), entry("e")),
                      resolver: code})
        code, out = self.run_script(approved, "--push")
        new = self.assert_restacked(approved, code, out)
        self.assertIn("in: references.bib", out)
        self.assertEqual(self.git("show", f"{new}:references.bib") + "\n",
                         bib(entry("a"), entry("b"), entry("bb"), entry("c"), entry("e")))

    def test_sources_conflict_with_the_conversion_is_merged_by_sentence(self) -> None:
        self.on_main({"manual/sources.md": SOURCES})
        approved = self.feature({"manual/sources.md": SOURCES.replace(
            "Alpha two.", "Alpha two. Added by the PR.")})
        self.on_main({"manual/sources.md": SOURCES.replace(". A", ".\nA")})
        code, out = self.run_script(approved, "--push")
        new = self.assert_restacked(approved, code, out)
        self.assertIn("in: manual/sources.md", out)
        self.assertEqual(self.git("show", f"{new}:manual/sources.md") + "\n", SOURCES.replace(
            "Alpha two. Alpha three.", "Alpha two.\nAdded by the PR.\nAlpha three.").replace(
            "Alpha one. ", "Alpha one.\n"))

    def test_dry_run_changes_nothing_but_origin_main(self) -> None:
        approved = self.aggregate_conflict()
        fetch_head = self.root / ".git" / "FETCH_HEAD"
        self.assertFalse(fetch_head.exists())
        before = self.state()
        code, out = self.run_script(approved)
        self.assertEqual(code, 0, out)
        self.assertIn("dry run: nothing pushed", out)
        self.assertIn("Restack check: identical to the approved change", out)
        self.assertIn("python3 scripts/queue_pr.py 7 ", out)
        fetched = f"{self.remote('refs/heads/main')} commit\trefs/remotes/origin/main"
        after = self.state()

        def without_fetch(state: tuple[str, ...]) -> tuple[object, ...]:
            return ([line for line in state[0].splitlines() if line != fetched], *state[1:])

        self.assertEqual(without_fetch(after), without_fetch(before))
        refs = after[0]
        self.assertIn(fetched, refs)
        self.assertFalse(fetch_head.exists())

    def test_already_up_to_date_and_clean_merges_are_left_alone(self) -> None:
        approved = self.feature()
        code, out = self.run_script(approved, "--push")
        self.assertEqual((code, self.remote()), (0, approved), out)
        self.assertIn("already contains origin/main", out)
        self.assertNotRegex(out, r"(?m)^Restack check:")
        self.on_main({"Other.lean": "def o := 0\n"})
        code, out = self.run_script(approved, "--push")
        self.assertEqual((code, self.remote()), (0, approved), out)
        self.assertIn("without conflicts", out)
        code, out = self.run_script(approved, "--push", "--allow-clean")
        self.assert_restacked(approved, code, out)

    # Refusals.

    def test_conflict_in_another_path_is_refused(self) -> None:
        approved = self.feature({"CslibFrontier.lean": aggregate("Ant", "Bee", "Cap", "Emu"),
                                 **modules("Bee"), "Lib.lean": LIB.replace("y := 2", "y := 3")})
        self.on_main({"CslibFrontier.lean": aggregate("Ant", "Bees", "Cap", "Emu"),
                      **modules("Bees"), "Lib.lean": LIB.replace("y := 2", "y := 4")})
        self.git("fetch", "-q", "origin")
        before = self.state()
        code, out = self.run_script(approved, "--push")
        self.assertEqual(code, 1, out)
        self.assertIn("outside generated files: Lib.lean", out)
        self.assertEqual(self.state(), before)

    def test_bibliography_entry_changed_on_both_sides_is_refused(self) -> None:
        approved = self.feature({"references.bib": bib(entry("a"), entry("c", "X"), entry("e"))})
        self.on_main({"references.bib": bib(entry("a"), entry("c", "Y"), entry("e"))})
        self.git("fetch", "-q", "origin")
        before = self.state()
        code, out = self.run_script(approved, "--push")
        self.assertEqual(code, 1, out)
        self.assertIn("left conflicts in references.bib", out)
        self.assertEqual(self.state(), before)

    def test_sentence_changed_on_both_sides_is_refused(self) -> None:
        self.on_main({"manual/sources.md": SOURCES.replace(". A", ".\nA")})
        approved = self.feature({"manual/sources.md": SOURCES.replace(". A", ".\nA").replace(
            "Alpha two.", "Alpha 2.")})
        self.on_main({"manual/sources.md": SOURCES.replace(". A", ".\nA").replace(
            "Alpha two.", "Alpha II.")})
        code, out = self.run_script(approved, "--push")
        self.assertEqual(code, 1, out)
        self.assertIn("left conflicts in manual/sources.md", out)

    def test_branch_moved_during_the_restack_is_not_overwritten(self) -> None:
        approved = self.aggregate_conflict()
        self.git("checkout", "-q", "feature")
        pushed = self.commit("a teammate's push", {"Notes.lean": "-- notes\n"})
        original = restack_mechanical.merge

        def merge_then_push(*args: object) -> str:
            new = original(*args)
            self.git("push", "-q", "origin", f"{pushed}:refs/heads/feature")
            return new

        with mock.patch.object(restack_mechanical, "merge", merge_then_push):
            code, out = self.run_script(approved, "--push")
        self.assertEqual(code, 1, out)
        self.assertIn(f"now points at {pushed[:12]}", out)
        self.assertEqual(self.remote(), pushed)

    def test_head_other_than_the_one_github_reports_is_refused(self) -> None:
        approved = self.aggregate_conflict()
        code, out = self.run_script(approved, "--push", head=self.remote("refs/heads/main"))
        self.assertEqual((code, self.remote()), (1, approved), out)
        self.assertIn("the PR moved during the run", out)

    def test_unapproved_head_is_refused_before_any_merge(self) -> None:
        approved = self.aggregate_conflict()
        self.git("checkout", "-q", "feature")
        changed = self.commit("pushed after the approval", {"Lib.lean": LIB + "-- more\n"})
        self.publish(changed)
        with mock.patch.object(restack_mechanical, "merge") as merge:
            code, out = self.run_script(approved, "--push")
        merge.assert_not_called()
        self.assertEqual((code, self.remote()), (1, changed), out)
        self.assertIn("Restack check: differs from the approved change", out)
        self.assertIn("is not the approved change", out)

    def test_failed_final_check_is_not_pushed(self) -> None:
        approved = self.aggregate_conflict()
        with mock.patch.object(restack_mechanical, "run_check", side_effect=[0, 1]):
            code, out = self.run_script(approved, "--push")
        self.assertEqual((code, self.remote()), (1, approved), out)
        self.assertIn("check_restack.py did not pass, so nothing is pushed", out)

    def test_locally_configured_drivers_are_not_used(self) -> None:
        # `true` would report every merge clean and keep the PR's side.
        self.git("config", "merge.bibkeys.driver", "true")
        self.git("config", "merge.leanagg.driver", "true")
        approved = self.feature({"references.bib": bib(entry("a"), entry("b"), entry("c"),
                                                       entry("e"))})
        self.on_main({"references.bib": bib(entry("a"), entry("bb"), entry("c"), entry("e"))})
        code, out = self.run_script(approved, "--push")
        new = self.assert_restacked(approved, code, out)
        self.assertIn("in: references.bib", out)
        self.assertEqual(self.git("show", f"{new}:references.bib") + "\n",
                         bib(entry("a"), entry("b"), entry("bb"), entry("c"), entry("e")))


if __name__ == "__main__":
    unittest.main()
