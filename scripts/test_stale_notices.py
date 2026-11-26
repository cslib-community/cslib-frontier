"""Tests for the stale-notice scan and its posting rules, from fixtures without the network."""

from __future__ import annotations

import argparse
import contextlib
from datetime import timedelta
import io
import json
from pathlib import Path
import sys
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import stale_notices as sn  # noqa: E402
from test_gh_records import REPO, T0, fake_github  # noqa: E402
from test_tender_report import comment, pr, review, sha  # noqa: E402

NOW = T0 + timedelta(days=10)


def ago(hours: float) -> float:
    """Hours after T0 that are `hours` before NOW, for the fixture builders."""
    return 240 - hours


def commit(hours: float) -> dict:
    from test_gh_records import stamp
    return {"event": "committed", "sha": "c" * 40, "committer": {"date": stamp(hours)}}


def notice(hours: float, kind: str = "drafts") -> dict:
    return comment(f"`coord` (agent)\n\nPlease update.\n\n<!-- stale-notice:{kind} -->", hours)


def issue(number: int, body: str = "", comments: int = 1) -> dict:
    from test_gh_records import stamp
    return {"number": number, "title": f"Issue {number}", "html_url": f"https://x/issues/{number}",
            "created_at": stamp(0), "user": {"login": "SamuelSchlesinger"}, "body": body,
            "comments": comments}


def args(**overrides) -> argparse.Namespace:
    values = dict(draft_days=7, claim_days=3, changes_hours=48, marker=sn.MARKER, jobs=1,
                  number=None, identity="`coord` (agent)", draft_stalled=False,
                  kinds=list(sn.KINDS), repo=REPO)
    values.update(overrides)
    return argparse.Namespace(**values)


def timeline_routes(timelines: dict[int, list[dict]]) -> dict:
    return {f"repos/{REPO}/issues/{n}/timeline?per_page=100": events
            for n, events in timelines.items()}


AUTHOR = "author"


class ScanTests(unittest.TestCase):
    def setUp(self):
        drafts = {
            1: [commit(0)],
            2: [commit(ago(24))],
            3: [comment(f"**APPROVE** at {sha(3)}", ago(24), AUTHOR), notice(ago(10))],
            4: [notice(ago(30))],
            5: [comment("Still working on it.", ago(48), AUTHOR),
                comment("Ping?", ago(1), "someone")],
            6: [notice(ago(200)), commit(ago(180))],
        }
        changes = {
            10: [comment(f"**REQUEST_CHANGES** at {sha(10)} by `rev`", ago(72))],
            11: [comment(f"**REQUEST_CHANGES** at {sha(11)}", ago(72)), commit(ago(50))],
            12: [comment(f"**REQUEST_CHANGES** at {'b' * 40}", ago(72))],
            13: [comment(f"**REQUEST_CHANGES** at {sha(13)}", ago(72)),
                 comment("Fixing now.", ago(60), AUTHOR)],
            14: [comment(f"**REQUEST_CHANGES** at {sha(14)}", ago(24))],
            15: [review("changes_requested", sha(15), ago(72), "Please split.")],
            16: [comment(f"**REQUEST_CHANGES** at {sha(16)}", ago(72)),
                 comment(f"**APPROVE** at {sha(16)}", ago(70))],
            17: [comment(f"**REQUEST_CHANGES** at {sha(17)}", ago(72)),
                 notice(ago(50), "changes"),
                 comment("> Changes were requested...\n> <!-- stale-notice:changes -->\n\n"
                         "Working on a fix now.", ago(40), AUTHOR)],
        }
        claims = {
            20: [],
            21: [comment("**Claimed** by worker session `abc12345` (Claude Code).", 1),
                 comment("Progress from abc12345: milestone 1 done.", ago(24))],
            22: [comment("Owner: `w-22`", 1),
                 {"event": "cross-referenced", "created_at": "2026-11-21T00:00:00Z",
                  "source": {"issue": {"number": 99, "state": "open", "pull_request": {}}}}],
            23: [comment("Owner: `w-23`", 1), comment("Released: handing this back.", 2)],
            26: [comment("Claimed by chris-ai1.", 1, "chris-ai1"),
                 comment("Update.", ago(24), "chris-ai1")],
            27: [comment("Owner: `w-27`", 1),
                 notice(ago(30), "claims")],
            29: [comment("Owner: `w-29`", 1),
                 notice(ago(80), "claims"),
                 comment("> <!-- stale-notice:claims -->\n\n`w-29` still active.", ago(24))],
        }
        pulls = ([{**pr(n, draft=True), "user": {"login": AUTHOR}} for n in drafts]
                 + [{**pr(n), "user": {"login": AUTHOR},
                     "body": "Uses `<!-- stale-notice:KIND -->` markers."} for n in changes])
        issues = ([issue(20, "Plan.\n\nOwner: `worker-a` (session x)", comments=0)]
                  + [issue(n) for n in (21, 22, 23, 26, 27, 29)]
                  + [issue(24, "Owner: none", comments=0), issue(25, "No claim.", comments=0),
                     issue(28, "Template:\n```\nOwner: `example`\n```", comments=0),
                     {**issue(30), "pull_request": {}}])
        self.routes = {f"repos/{REPO}/pulls?state=open&per_page=100": pulls,
                       f"repos/{REPO}/issues?state=open&per_page=100": issues,
                       **timeline_routes({**drafts, **changes, **claims})}
        self.found = sn.scan(fake_github(self.routes), set(sn.KINDS), NOW, args())

    def kind(self, kind: str) -> dict[int, dict]:
        return {e["number"]: e for e in self.found if e["kind"] == kind}

    def test_drafts_without_author_activity(self):
        drafts = self.kind("drafts")
        self.assertEqual(sorted(drafts), [1, 3, 4, 6])
        self.assertEqual(drafts[1]["activity"], "2026-11-20T12:00Z")
        self.assertTrue(drafts[3]["skip"])
        self.assertEqual((drafts[4]["skip"], drafts[4]["window_passed"]), (True, True))
        self.assertEqual((drafts[6]["skip"], drafts[6]["window_passed"]), (False, False))

    def test_unanswered_change_requests(self):
        changes = self.kind("changes")
        self.assertEqual(sorted(changes), [10, 15])
        self.assertEqual((changes[10]["sha"], changes[10]["node_id"]), (sha(10), "N10"))

    def test_claims_without_claimant_activity(self):
        claims = self.kind("claims")
        self.assertEqual(sorted(claims), [20, 27])
        self.assertTrue(claims[20]["detail"].startswith("`worker-a`: [Owner: `worker-a`"))
        self.assertTrue(claims[27]["window_passed"])


class ApplyTests(unittest.TestCase):
    def entries(self) -> list[dict]:
        base = dict(title="t", url="u", activity="2026-11-20T12:00Z", idle="10d", detail="d",
                    last_notice="", window_passed=False)
        return [{**base, "kind": "drafts", "number": 1, "skip": False},
                {**base, "kind": "drafts", "number": 3, "skip": True},
                {**base, "kind": "changes", "number": 10, "skip": False, "sha": sha(10),
                 "request_url": "r", "node_id": "N10"}]

    def test_posts_identified_marked_notices_and_converts_when_asked(self):
        routes = {f"POST repos/{REPO}/issues/1/comments": {"id": 1},
                  f"POST repos/{REPO}/issues/10/comments": {"id": 2},
                  "graphql": {"data": {}}}
        gh = fake_github(routes)
        entries = self.entries()
        self.assertTrue(sn.apply(gh, entries, args(draft_stalled=True), sleep=lambda s: None))
        self.assertEqual([e["action"] for e in entries],
                         ["posted", "skipped: noticed within 24 hours",
                          "posted; converted to draft"])
        bodies = [json.loads(body)["body"] for method, endpoint, body in gh._run.writes()
                  if endpoint.endswith("/comments")]
        self.assertTrue(all(b.startswith("`coord` (agent)\n\n") for b in bodies))
        self.assertTrue(bodies[0].endswith("<!-- stale-notice:drafts -->"))
        self.assertIn("converted to a draft", bodies[1])
        self.assertNotIn("close", " ".join(e for _, e, _ in gh._run.calls))

    def test_a_failed_write_is_recorded_and_the_rest_continue(self):
        gh = fake_github({f"POST repos/{REPO}/issues/10/comments": {"id": 2}})
        entries = self.entries()
        self.assertFalse(sn.apply(gh, entries, args(), sleep=lambda s: None))
        self.assertTrue(entries[0]["action"].startswith("failed:"))
        self.assertEqual(entries[2]["action"], "posted")

    def test_a_failed_conversion_is_not_announced(self):
        gh = fake_github({f"POST repos/{REPO}/issues/10/comments": {"id": 2}})
        entries = self.entries()[2:]
        self.assertFalse(sn.apply(gh, entries, args(draft_stalled=True), sleep=lambda s: None))
        self.assertTrue(entries[0]["action"].startswith("posted; conversion failed:"))
        [(_, _, body)] = [w for w in gh._run.writes() if w[1].endswith("/comments")]
        self.assertNotIn("draft", json.loads(body)["body"])


class CommandLineTests(unittest.TestCase):
    def test_apply_needs_an_identity_and_kinds_are_checked(self):
        for argv in (["--apply"], ["--only", "drafts,bogus"], ["--draft-stalled"],
                     ["--marker", "a b"]):
            with self.subTest(argv=argv), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit):
                    sn.main(argv)

    def test_dry_run_entry_point_posts_nothing(self):
        events = [comment(f"**REQUEST_CHANGES** at {sha(10)}", ago(72))]
        gh = fake_github({f"repos/{REPO}/pulls?state=open&per_page=100": [pr(10)],
                          **timeline_routes({10: events})})
        out = io.StringIO()
        with mock.patch.object(sn.gr, "GitHub", return_value=gh), \
                mock.patch.object(sn.gr, "utcnow", return_value=NOW), \
                contextlib.redirect_stdout(out):
            self.assertEqual(sn.main(["--only", "changes", "--json"]), 0)
        report = json.loads(out.getvalue())
        self.assertEqual([e["number"] for e in report["items"]], [10])
        self.assertEqual(gh._run.writes(), [])


if __name__ == "__main__":
    unittest.main()
