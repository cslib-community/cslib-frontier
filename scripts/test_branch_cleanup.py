"""Tests for branch categorization, protection and guarded deletion, without the network."""

from __future__ import annotations

import contextlib
from datetime import timedelta
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import branch_cleanup as bc  # noqa: E402
from test_gh_records import REPO, T0, fake_github, stamp  # noqa: E402

NOW = T0 + timedelta(days=30)
AGE = timedelta(days=14)


def sha(n: int) -> str:
    return f"{n:040x}"


def branch(name: str, n: int, protected: bool = False) -> dict:
    return {"name": name, "commit": {"sha": sha(n)}, "protected": protected}


def pull(number: int, head: str, n: int, *, state: str = "closed", base: str = "main",
         closed: float | None = None, merged: bool = False, repo: str = REPO) -> dict:
    closed_at = stamp(closed) if closed is not None else None
    return {"number": number, "state": state, "base": {"ref": base},
            "head": {"ref": head, "sha": sha(n), "repo": {"full_name": repo}},
            "closed_at": closed_at, "merged_at": closed_at if merged else None}


def days_before_now(days: float) -> float:
    """Hours after T0 that are `days` before NOW."""
    return 24 * (30 - days)


BRANCHES = [
    branch("main", 1),
    branch("gh-readonly-queue/main/pr-4-abc", 2),
    branch("feat/open", 3),
    branch("feat/base", 4),
    branch("feat/stacked", 5),
    branch("feat/merged", 6),
    branch("feat/merged-pushed", 7),
    branch("feat/merged-late", 8),
    branch("feat/closed-old", 9),
    branch("feat/closed-new", 10),
    branch("feat/reused", 11),
    branch("fork-name", 12),
    branch("scratch-old", 13),
    branch("scratch-new", 14),
    branch("scratch-undated", 15),
    branch("release", 16, protected=True),
]
PULLS = [
    pull(1, "feat/open", 3, state="open"),
    pull(2, "feat/stacked", 5, state="open", base="feat/base"),
    pull(3, "feat/base", 4, closed=days_before_now(20), merged=True),
    pull(4, "feat/merged", 6, closed=days_before_now(1), merged=True),
    pull(5, "feat/merged-pushed", 70, closed=days_before_now(20), merged=True),
    pull(6, "feat/merged-late", 8, closed=days_before_now(20), merged=True),
    pull(7, "feat/closed-old", 9, closed=days_before_now(20)),
    pull(8, "feat/closed-new", 10, closed=days_before_now(3)),
    pull(9, "feat/reused", 11, closed=days_before_now(25), merged=True),
    pull(10, "feat/reused", 11, closed=days_before_now(15)),
    pull(11, "fork-name", 12, closed=days_before_now(20), merged=True, repo="other/r"),
]
DATES = {sha(6): T0, sha(8): T0 + timedelta(days=15), sha(9): T0, sha(12): T0, sha(13): T0,
         sha(14): NOW - timedelta(days=1)}


class CategorizeTests(unittest.TestCase):
    def setUp(self):
        self.records = {r["branch"]: r for r in bc.categorize(BRANCHES, PULLS, REPO, "main", DATES)}

    def summary(self, name: str) -> tuple:
        r = self.records[name]
        return r["category"], r["pr"], bool(r["protected"])

    def test_every_branch_falls_in_one_category(self):
        self.assertEqual({name: self.summary(name)[0] for name in self.records}, {
            "main": "open-base", "gh-readonly-queue/main/pr-4-abc": "nopr",
            "feat/open": "open-head",
            "feat/base": "open-base", "feat/stacked": "open-head", "feat/merged": "merged",
            "feat/merged-pushed": "merged", "feat/merged-late": "merged",
            "feat/closed-old": "closed", "feat/closed-new": "closed", "feat/reused": "closed",
            "fork-name": "nopr", "scratch-old": "nopr", "scratch-new": "nopr",
            "scratch-undated": "nopr", "release": "nopr"})

    def test_protections(self):
        protected = {name for name, r in self.records.items() if r["protected"]}
        self.assertEqual(protected, {
            "main", "gh-readonly-queue/main/pr-4-abc", "feat/open", "feat/base", "feat/stacked",
            "feat/merged-pushed", "feat/merged-late", "release"})
        self.assertEqual(self.records["feat/base"]["protected"], ["base of open PR #2"])
        self.assertEqual(self.records["feat/merged-pushed"]["protected"],
                         ["pushed to after PR #5 closed"])

    def test_fork_pr_bases_and_case_mismatched_repos_are_protected(self):
        branches = [branch("feat/a", 1), branch("fork-target", 2)]
        pulls = [pull(1, "feat/a", 1, state="open", repo="cslib-community/cslib-frontier"),
                 pull(2, "fork-head", 3, state="open", base="fork-target", repo="someone/fork")]
        recs = {r["branch"]: r for r in bc.categorize(
            branches, pulls, "cslib-community/CSLib-frontier", "main", {sha(1): T0, sha(2): T0})}
        self.assertEqual((recs["feat/a"]["category"], recs["feat/a"]["protected"]),
                         ("open-head", ["head of open PR #1"]))
        self.assertEqual((recs["fork-target"]["category"], recs["fork-target"]["protected"]),
                         ("open-base", ["base of open PR #2"]))
        self.assertFalse(bc.eligible(recs["feat/a"], {"nopr"}, NOW, AGE))
        self.assertFalse(bc.eligible(recs["fork-target"], {"nopr"}, NOW, AGE))

    def test_the_most_recently_closed_pr_decides(self):
        self.assertEqual(self.summary("feat/reused"), ("closed", 10, False))
        self.assertEqual(self.records["feat/reused"]["closed_at"], stamp(days_before_now(15)))

    def test_eligibility_by_kind_and_age(self):
        def chosen(*kinds):
            return sorted(n for n, r in self.records.items()
                          if bc.eligible(r, set(kinds), NOW, AGE))
        self.assertEqual(chosen("merged"), ["feat/merged"])
        self.assertEqual(chosen("closed"), ["feat/closed-old", "feat/reused"])
        self.assertEqual(chosen("nopr"), ["fork-name", "scratch-old"])
        self.assertEqual(chosen("merged", "closed", "nopr"),
                         ["feat/closed-old", "feat/merged", "feat/reused", "fork-name",
                          "scratch-old"])

    def test_restore_command_quotes_the_ref(self):
        record = {"branch": "odd name", "sha": sha(1)}
        self.assertEqual(bc.restore_command(REPO, record),
                         f"gh api -X POST repos/{REPO}/git/refs -f 'ref=refs/heads/odd name' "
                         f"-f sha={sha(1)}")


class CommitDateTests(unittest.TestCase):
    def test_local_commits_read_the_object_database_and_skip_missing_commits(self):
        with tempfile.TemporaryDirectory() as directory:
            env = {**os.environ, "GIT_COMMITTER_DATE": "2026-11-01T10:00:00Z",
                   "GIT_AUTHOR_DATE": "2026-11-01T10:00:00Z", "GIT_CONFIG_GLOBAL": os.devnull,
                   "GIT_CONFIG_NOSYSTEM": "1"}

            def git(*args: str) -> str:
                return subprocess.run(["git", "-C", directory, *args], check=True, env=env,
                                      capture_output=True, text=True).stdout.strip()
            git("init", "-q")
            git("-c", "user.name=A. Worker", "-c", "user.email=t@example.com", "commit", "-q",
                "--allow-empty", "-m", "c")
            head = git("rev-parse", "HEAD")
            found = bc.local_commits([head, "f" * 40], Path(directory))
        self.assertEqual(found, {head: (T0 - timedelta(days=19, hours=2), "A. Worker")})

    def test_rest_fills_in_commits_missing_locally(self):
        gh = fake_github({f"repos/{REPO}/commits/{sha(2)}":
                          {"commit": {"committer": {"date": stamp(5)}, "author": {"name": "b"}}}})
        with mock.patch.object(bc, "local_commits", return_value={sha(1): (T0, "a")}):
            found = bc.commit_info(gh, [sha(1), sha(2), sha(3), sha(2)], None, jobs=1)
        self.assertEqual(found, {sha(1): (T0, "a"), sha(2): (T0 + timedelta(hours=5), "b")})
        self.assertEqual(gh.calls, 2)


def notice_comment(body: str, days_ago: float, url: str = "") -> dict:
    return {"created_at": (NOW - timedelta(days=days_ago)).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "body": body, "html_url": url}


class NoticeTests(unittest.TestCase):
    rows = [{"branch": "old/a", "sha": sha(1), "commit_date": "2026-11-01T00:00Z",
             "commit_author": "Pipe | Name"},
            {"branch": "old/b", "sha": sha(2), "commit_date": "2026-11-02T00:00Z",
             "commit_author": None}]

    def test_notice_lists_each_branch_and_ends_with_the_marker(self):
        [body] = bc.notice_bodies(self.rows, REPO, "`coord` (agent)", "14d", "7d")
        self.assertTrue(body.startswith("`coord` (agent)\n\n**No-PR branches to be deleted.**"))
        self.assertIn(f"| `old/a` | 2026-11-01T00:00Z | Pipe \\| Name | `{sha(1)}` |", body)
        self.assertIn(f"| `old/b` | 2026-11-02T00:00Z |  | `{sha(2)}` |", body)
        self.assertTrue(body.endswith(bc.NOTICE_MARKER))
        notices = bc.Notices.read([notice_comment(body, 8)], 7, timedelta(days=7))
        self.assertEqual(notices.listed, {"old/a": [(sha(1), NOW - timedelta(days=8))],
                                          "old/b": [(sha(2), NOW - timedelta(days=8))]})

    def test_long_notices_are_split_into_marked_parts(self):
        with mock.patch.object(bc, "NOTICE_LIMIT", 3100):
            bodies = bc.notice_bodies(self.rows, REPO, "id", "14d", "7d")
        self.assertEqual(len(bodies), 2)
        self.assertIn("(part 2 of 2)", bodies[1])
        self.assertTrue(all(b.endswith(bc.NOTICE_MARKER) for b in bodies))

    def test_deletion_waits_for_an_unanswered_notice_of_the_same_tip(self):
        def row(name: str, n: int) -> str:
            return f"| `{name}` | 2026-11-01T00:00Z | w | `{sha(n)}` |"
        comments = [
            notice_comment("\n".join([row("a", 1), row("b", 2), row("c", 3), row("c-d", 6),
                                       row("q", 7), bc.NOTICE_MARKER]), 8),
            notice_comment("\n".join([row("d", 4), bc.NOTICE_MARKER]), 2),
            notice_comment("Please keep `c`, I still need it.", 1, "https://x/keep"),
            notice_comment(f"> {row('q', 7)}\n> {bc.NOTICE_MARKER}\n\nKeep `q` too!", 1,
                           "https://x/quote"),
            notice_comment(f"Example:\n```\n{row('e', 5)}\n{bc.NOTICE_MARKER}\n```", 9)]
        notices = bc.Notices.read(comments, 7, timedelta(days=7))
        hold = {name: notices.hold({"branch": name, "sha": sha(n)}, NOW)
                for name, n in (("a", 1), ("b", 9), ("c", 3), ("c-d", 6), ("q", 7), ("d", 4),
                                ("e", 5))}
        self.assertEqual(hold, {
            "a": None, "b": "its tip is not the one listed on #7",
            "c": "named in a reply after the notice (https://x/keep)", "c-d": None,
            "q": "named in a reply after the notice (https://x/quote)",
            "d": "noticed 2026-12-18T12:00Z; deletable from 2026-12-25T12:00Z",
            "e": "not listed in a notice on #7"})


def server_error() -> subprocess.CalledProcessError:
    return subprocess.CalledProcessError(1, "gh", stderr="gh: Server Error (HTTP 500)\n")


class DeleteTests(unittest.TestCase):
    def test_deletes_only_unchanged_unused_branches_and_logs_each_outcome(self):
        names = ["gone-ok", "moved", "now-head", "now-base", "main", "vanished", "fails"]
        plan = [{"branch": name, "sha": sha(i), "restore": f"restore {name}", "status": "planned"}
                for i, name in enumerate(names)]
        refs = {f"repos/{REPO}/git/ref/heads/{name}": {"object": {"sha": sha(i)}}
                for i, name in enumerate(names) if name != "vanished"}
        refs[f"repos/{REPO}/git/ref/heads/moved"] = {"object": {"sha": sha(99)}}
        gh = fake_github({
            f"repos/{REPO}/pulls?state=open&per_page=100": [
                pull(20, "now-head", 2, state="open"),
                pull(21, "x", 3, state="open", base="now-base", repo="someone/fork")],
            **refs,
            f"DELETE repos/{REPO}/git/refs/heads/gone-ok": None,
            f"DELETE repos/{REPO}/git/refs/heads/fails": server_error()})
        out = io.StringIO()
        with tempfile.TemporaryDirectory() as directory, \
                mock.patch.object(bc.gr, "utcnow", return_value=NOW):
            path = Path(directory) / "log.json"
            log = {"branches": plan}
            self.assertFalse(bc.delete(gh, plan, log, path, sleep=lambda s: None, out=out))
            logged = json.loads(path.read_text())
        self.assertEqual([e["status"].split(":")[0] for e in logged["branches"]],
                         ["deleted", "kept", "kept", "kept", "kept", "already gone", "failed"])
        self.assertEqual(logged["branches"][1]["status"], f"kept: it moved to {sha(99)}")
        self.assertEqual(logged["branches"][4]["status"], "kept: protected branch")
        self.assertEqual(logged["branches"][0]["deleted_at"], "2026-12-20T12:00Z")
        self.assertEqual(out.getvalue(), f"deleted gone-ok at {sha(0)}; restore: restore gone-ok\n")
        deletes = [endpoint for method, endpoint, _ in gh._run.writes()]
        self.assertEqual(deletes, [f"repos/{REPO}/git/refs/heads/gone-ok",
                                   f"repos/{REPO}/git/refs/heads/fails"])


class CommandLineTests(unittest.TestCase):
    def routes(self) -> dict:
        return {f"repos/{REPO}": {"default_branch": "main"},
                f"repos/{REPO}/branches?per_page=100": BRANCHES,
                f"repos/{REPO}/pulls?state=all&per_page=100": PULLS,
                f"repos/{REPO}/pulls?state=open&per_page=100":
                    [p for p in PULLS if p["state"] == "open"],
                **{f"repos/{REPO}/git/ref/heads/{b['name']}": {"object": b["commit"]}
                   for b in BRANCHES},
                **{f"DELETE repos/{REPO}/git/refs/heads/{b['name']}": None for b in BRANCHES}}

    def run_main(self, argv: list[str], gh) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(bc.gr, "GitHub", return_value=gh), \
                mock.patch.object(bc.gr, "utcnow", return_value=NOW), \
                mock.patch.object(bc, "local_commits",
                                  return_value={k: (v, "w") for k, v in DATES.items()}), \
                mock.patch.object(bc.time, "sleep"), \
                contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = bc.main([*argv, "--repo", REPO])
        return code, out.getvalue(), err.getvalue()

    def test_apply_needs_a_kind_and_ages_are_checked(self):
        for argv in (["--apply"], ["--delete", "merged", "--older-than", "2 weeks"],
                     ["--delete", "everything"], ["--delete", "nopr", "--apply"],
                     ["--notice"], ["--notice", "--identity", "x", "--apply"],
                     ["--notice-wait", "a week"]):
            with self.subTest(argv=argv), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit):
                    bc.main(argv)

    def test_dry_run_lists_the_plan_and_writes_nothing(self):
        gh = fake_github(self.routes())
        code, out, _ = self.run_main(["--delete", "merged", "--delete", "nopr", "--json"], gh)
        self.assertEqual(code, 0)
        report = json.loads(out)
        self.assertEqual([e["branch"] for e in report["plan"]],
                         ["feat/merged", "fork-name", "scratch-old"])
        self.assertEqual(len(report["branches"]), len(BRANCHES))
        self.assertEqual(gh._run.writes(), [])

    def test_notice_mode_writes_the_comments_and_posts_nothing(self):
        gh = fake_github(self.routes())
        with tempfile.TemporaryDirectory() as directory:
            code, out, _ = self.run_main(["--notice", "--identity", "`coord` (agent)",
                                          "--notice-dir", directory, "--notice-issue", "7"], gh)
            body = (Path(directory) / "notice-1.md").read_text()
        self.assertEqual(code, 0)
        self.assertIn(f"gh issue comment 7 --repo {REPO} --body-file {directory}/notice-1.md",
                      out)
        self.assertEqual([line.split("`")[1] for line in body.splitlines()
                          if line.startswith("| `")], ["fork-name", "scratch-old"])
        self.assertIn(f"| `scratch-old` | 2026-11-20T12:00Z | w | `{sha(13)}` |", body)
        self.assertEqual(gh._run.writes(), [])

    def test_notice_report_prints_markdown_table_to_stdout(self):
        gh = fake_github(self.routes())
        code, out, _ = self.run_main(["--notice-report"], gh)
        self.assertEqual(code, 0)
        self.assertEqual([line.split("`")[1] for line in out.splitlines()
                          if line.startswith("| `")], ["fork-name", "scratch-old"])
        self.assertTrue(out.strip().endswith(bc.NOTICE_MARKER))
        self.assertEqual(gh._run.writes(), [])

    def test_no_pr_deletion_follows_the_notice_issue(self):
        notice = f"| `fork-name` | x | w | `{sha(12)}` |\n{bc.NOTICE_MARKER}"
        gh = fake_github({**self.routes(), f"repos/{REPO}/issues/7/comments?per_page=100":
                          [notice_comment(notice, 8)]})
        code, out, _ = self.run_main(["--delete", "nopr", "--notice-issue", "7", "--json"], gh)
        report = json.loads(out)
        self.assertEqual(code, 0)
        self.assertEqual([e["branch"] for e in report["plan"]], ["fork-name"])
        self.assertEqual([(w["branch"], w["reason"]) for w in report["waiting"]],
                         [("scratch-old", "not listed in a notice on #7")])

    def test_apply_deletes_the_plan_and_keeps_json_output_clean(self):
        gh = fake_github(self.routes())
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "log.json"
            code, out, err = self.run_main(["--delete", "closed", "--apply", "--json",
                                            "--log", str(path)], gh)
            logged = json.loads(path.read_text())
        self.assertEqual(code, 0)
        self.assertEqual([e["status"] for e in json.loads(out)["plan"]], ["deleted", "deleted"])
        self.assertEqual([e["branch"] for e in logged["branches"]],
                         ["feat/closed-old", "feat/reused"])
        self.assertIn(f"restore: gh api -X POST repos/{REPO}/git/refs -f "
                      f"ref=refs/heads/feat/closed-old -f sha={sha(9)}", err)
        self.assertEqual(len(gh._run.writes()), 2)


if __name__ == "__main__":
    unittest.main()
