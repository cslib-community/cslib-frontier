"""Tests for the tender report's classification of open PRs, from fixtures without the network."""

from __future__ import annotations

import contextlib
from datetime import timedelta
import io
import json
from pathlib import Path
import sys
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gh_records as gr  # noqa: E402
import tender_report as tr  # noqa: E402
from test_gh_records import OLD, REPO, T0, fake_github, stamp  # noqa: E402

NOW = T0 + timedelta(hours=24)


def sha(number: int) -> str:
    return format(number, "040x")


def pr(number: int, *, head: str | None = None, base: str = "main", draft: bool = False,
       ref: str | None = None) -> dict:
    return {"number": number, "title": f"PR {number}", "html_url": f"https://x/pull/{number}",
            "draft": draft, "created_at": stamp(-48), "user": {"login": "author"}, "body": "",
            "node_id": f"N{number}",
            "head": {"sha": head or sha(number), "ref": ref or f"feat/{number}",
                     "repo": {"full_name": REPO}},
            "base": {"ref": base}}


def comment(body: str, hours: float, login: str = "SamuelSchlesinger") -> dict:
    return {"event": "commented", "created_at": stamp(hours), "body": body,
            "user": {"login": login}, "html_url": f"https://x/c/{hours}"}


def review(state: str, commit: str, hours: float, body: str = "") -> dict:
    return {"event": "reviewed", "submitted_at": stamp(hours), "state": state, "commit_id": commit,
            "body": body, "user": {"login": "rev"}, "html_url": f"https://x/r/{hours}"}


def approve(number: int, hours: float = 1, extra: str = "", head: str | None = None) -> dict:
    return comment(f"**APPROVE** at `{head or sha(number)}` by `rev-{number}`{extra}", hours)


def runs(conclusion: str | None = "success", status: str = "completed", app: int = 15368) -> dict:
    return {"total_count": 1, "check_runs": [
        {"name": "ci-checks", "status": status, "conclusion": conclusion,
         "started_at": stamp(2), "app": {"id": app}}]}


def routes(pulls: list[dict], timelines: dict[int, list[dict]], checks: dict[int, dict] = {},
           mergeable: dict[int, object] = {}, extra: dict | None = None) -> dict:
    found = {f"repos/{REPO}/pulls?state=open&per_page=100": pulls}
    for number, events in timelines.items():
        found[f"repos/{REPO}/issues/{number}/timeline?per_page=100"] = events
    for number, value in checks.items():
        head = next(p["head"]["sha"] for p in pulls if p["number"] == number)
        found[f"repos/{REPO}/commits/{head}/check-runs?check_name=ci-checks&filter=all"
              "&per_page=100"] = value
    for number, value in mergeable.items():
        found[f"repos/{REPO}/pulls/{number}"] = value
    found.update(extra or {})
    return found


class TenderReportTests(unittest.TestCase):
    def setUp(self):
        held = "HOLD owner=rev until=2026-11-22T00:00Z reason=wait for #9"
        pulls = [pr(n) for n in (1, 2, 3, 4, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17)]
        pulls[3] = pr(4)
        pulls += [pr(5, base="feat/lower"), pr(11, draft=True), pr(13, base="feat/14")]
        timelines = {
            1: [approve(1)],
            2: [approve(2), comment(held, 2)],
            3: [approve(3, extra="\n\nQueueing held until #7 lands.")],
            4: [approve(4, head=OLD)],
            5: [approve(5)],
            6: [approve(6), {"event": "automatic_base_change_succeeded", "created_at": stamp(3)}],
            7: [approve(7)],
            8: [approve(8), {"event": "added_to_merge_queue", "created_at": stamp(2)}],
            9: [comment("HOLD owner=x until=2026-11-20T13:00Z reason=old", 0),
                comment(f"CLAIM review head={sha(9)} by=rev-9 until=2026-11-20T14:00Z", 1)],
            10: [approve(10), comment(f"**REQUEST_CHANGES** at {sha(10)} by `other`", 2)],
            12: [comment(f"Agent review: APPROVED at exact head {sha(12)} (PR #12)", 1)],
            13: [approve(13)],
            14: [],
            15: [review("approved", sha(15), 1, "Looks right.")],
            16: [approve(16)],
            17: [approve(17), comment(
                f"CLAIM review head={sha(17)} by=rev-17 until=2026-11-21T12:30Z", 23.5)],
        }
        self.run_routes = routes(
            pulls, timelines,
            checks={1: runs(), 3: runs(), 7: runs(None, "in_progress"), 12: runs(),
                    15: {"check_runs": runs()["check_runs"] + [
                        {**runs("failure")["check_runs"][0], "started_at": stamp(3)},
                        {**runs("success", app=1)["check_runs"][0], "started_at": stamp(4)}]},
                    16: runs(), 17: runs()},
            mergeable={1: {"mergeable": True}, 3: {"mergeable": True}, 7: {"mergeable": None},
                       12: {"mergeable": True}, 15: {"mergeable": True},
                       16: {"mergeable": False}, 17: {"mergeable": True}},
            extra={f"repos/{REPO}/pulls?state=closed&head=o:feat%2Flower&per_page=100":
                   [{"number": 50, "merged_at": stamp(5)}]})
        self.gh = fake_github(self.run_routes)
        self.report = tr.build_report(self.gh, NOW, sleep=lambda s: None)

    def numbers(self, key: str) -> list[int]:
        return [entry["number"] for entry in self.report[key]]

    def test_ready_rows_carry_the_queue_command(self):
        self.assertEqual(self.numbers("ready"), [1])
        self.assertEqual(self.report["ready"][0]["command"],
                         f"python3 {tr.TRUSTED}/scripts/queue_pr.py 1 {sha(1)} --repo {REPO}")

    def test_free_text_holds_and_other_approvals_need_reading(self):
        self.assertEqual(self.numbers("needs_check"), [3, 12, 17])
        three, twelve, seventeen = self.report["needs_check"]
        self.assertIn("Queueing held until #7 lands.", three["reasons"][0])
        self.assertIn("is not a verdict line", twelve["reasons"][0])
        self.assertEqual(seventeen["reasons"], [
            "[review CLAIM](https://x/c/23.5) by `rev-17` active until 2026-11-21T12:15Z"])

    def test_sequencing_unswept_holds_claims_and_questionable_approvals_need_reading(self):
        cases = {
            21: ([approve(21, hours=1),
                  comment("The queue now has #8474 ahead. I'll verify the delta before queueing.",
                          2, "edemaine")], ""),
            22: ([comment("HOLD owner=maintainer until=2026-11-20T13:00Z reason=needs check", 0.2),
                  approve(22, hours=1)], ""),
            23: ([comment(f"CLAIM review head={sha(23)} by=rev-x until=2026-11-21T12:40Z", 23.5),
                  approve(23, hours=23.6)], ""),
            24: ([comment(f"**REQUEST_CHANGES** at {sha(24)} by rev-b", 0.5),
                  approve(24, hours=1)], ""),
            25: ([comment(f"**APPROVE** at {sha(25)}", 1)], ""),
            26: ([comment(f"**APPROVE** at {sha(26)} by worker-x", 1)],
                 "`worker-x` (Jetski worker agent). This is agent action."),
        }
        pulls = []
        for number, (_, body) in cases.items():
            item = pr(number)
            item["body"] = body
            pulls.append(item)
        gh = fake_github(routes(pulls, {n: ev for n, (ev, _) in cases.items()},
                                checks={n: runs() for n in cases},
                                mergeable={n: {"mergeable": True} for n in cases}))
        report = tr.build_report(gh, NOW, sleep=lambda s: None)
        self.assertEqual(report["ready"], [])
        self.assertEqual([e["number"] for e in report["needs_check"]], sorted(cases))

    def test_blocked_rows_name_their_reasons(self):
        reasons = {e["number"]: e["reasons"] for e in self.report["blocked"]}
        self.assertEqual(sorted(reasons), [2, 7, 13, 15, 16])
        self.assertEqual(reasons[2], ["HOLD by `rev` until 2026-11-22T00:00Z: wait for #9"])
        self.assertEqual(reasons[7], ["required checks pending",
                                      "GitHub has not computed mergeability yet"])
        self.assertEqual(reasons[13], ["stacked on open #14"])
        self.assertEqual(reasons[15], ["required checks failed: ci-checks"])
        self.assertEqual(reasons[16], ["conflicts with `main`"])

    def test_restack_candidates(self):
        rows = {e["number"]: e for e in self.report["restack"]}
        self.assertEqual(sorted(rows), [4, 5, 6])
        self.assertEqual(rows[4]["situation"], "head moved since approval")
        self.assertIn(f"check_restack.py {OLD} {sha(4)}", rows[4]["next"])
        self.assertEqual(rows[5]["situation"], "lower PR #50 merged; approved head unchanged")
        self.assertTrue(
            rows[6]["situation"].startswith("retargeted to `main` at 2026-11-20T15:00Z"))

    def test_expired_holds_and_claims_are_listed(self):
        self.assertEqual(self.report["expired_holds"],
                         [{"number": 9, "owner": "x", "until": "2026-11-20T13:00Z",
                           "reason": "old", "url": "https://x/c/0"}])
        self.assertEqual([(c["number"], c["by"], c["until"]) for c in self.report["stale_claims"]],
                         [(9, "rev-9", "2026-11-20T13:45Z")])

    def test_queued_requested_changes_and_drafts_are_left_out(self):
        listed = {e["number"] for key in ("ready", "needs_check", "blocked", "restack")
                  for e in self.report[key]}
        self.assertFalse(listed & {8, 10, 11, 14})
        self.assertEqual((self.report["scanned"], self.report["drafts_skipped"]), (16, 1))

    def test_render_and_json_entry_point(self):
        text = tr.render(self.report)
        for heading in ("## Ready to queue (1)", "## Needs a human-readable check (3)",
                        "## Restack candidates (3)", "## Expired HOLD lines (1)"):
            self.assertIn(heading, text)
        out = io.StringIO()
        with mock.patch.object(tr.gr, "GitHub", return_value=fake_github(self.run_routes)), \
                mock.patch.object(tr.gr, "utcnow", return_value=NOW), \
                contextlib.redirect_stdout(out):
            self.assertEqual(tr.main(["--json", "--pr", "1", "--pr", "2"]), 0)
        report = json.loads(out.getvalue())
        self.assertEqual(([e["number"] for e in report["ready"]], report["scanned"]), ([1], 2))

    def test_unknown_pr_numbers_are_refused(self):
        with self.assertRaisesRegex(gr.GitHubError, "not open: #99"):
            tr.build_report(fake_github(self.run_routes), NOW, [1, 99])


class CheckStateTests(unittest.TestCase):
    def test_latest_run_from_the_required_app_decides(self):
        run = runs()["check_runs"][0]
        self.assertEqual(tr.ci_state([run]), ("success", []))
        self.assertEqual(tr.ci_state([]), ("pending", []))
        self.assertEqual(tr.ci_state([{**run, "app": {"id": 1}}]), ("pending", []))
        rerun = {**run, "status": "in_progress", "conclusion": None, "started_at": stamp(5)}
        self.assertEqual(tr.ci_state([run, rerun]), ("pending", []))
        failed = {**run, "conclusion": "cancelled", "started_at": stamp(5)}
        self.assertEqual(tr.ci_state([run, failed]), ("failure", ["ci-checks"]))


class ImprovementShareTests(unittest.TestCase):
    def test_counts_improvement_titles_and_flags_large_fleets_below_the_floor(self):
        log = "\n".join(["A\tfeat(X): add a theorem (#1)"] * 8
                        + ["A\trefactor(X)!: share a lemma (#2)", "A\tperf: faster (#3)",
                           "B\tfeat: one (#4)", "B\tstyle(Y): rename (#5)",
                           "C\tfeat(Z): add (#6)"] + ["C\tfeat(Z): more (#7)"] * 9
                        + ["D\trefactoring is not a type (#8)", "malformed line"])
        rows = {r["author"]: r for r in tr.improvement_share(log)}
        self.assertEqual((rows["A"]["merged"], rows["A"]["improvements"], rows["A"]["below"]),
                         (10, 2, False))
        self.assertEqual((rows["B"]["improvements"], rows["B"]["below"]), (1, False))
        self.assertEqual((rows["C"]["merged"], rows["C"]["below"]), (10, True))
        self.assertEqual(rows["D"]["improvements"], 0)
        self.assertNotIn("malformed line", rows)
        self.assertIn("below one in five", tr.render_share(list(rows.values()), "main", 7))


if __name__ == "__main__":
    unittest.main()
