# Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Christian Reitwiessner
"""Tests for the agent activity page's attribution and count semantics."""

import datetime as dt
import json
import unittest
from unittest.mock import patch

import agent_activity as activity


class Disclosures(unittest.TestCase):
    def test_claims_signatures_and_agent_review_verdicts(self):
        cases = [
            ("Codex session 62875D29 claims the next batch.", ("62875d29", "worker")),
            ("Claimed by a Claude Code worker session (Claude Opus, session 2680eecf).",
             ("2680eecf", "worker")),
            ("Done.\n— Codex worker, session `4625757c`", ("4625757c", "worker")),
            ("Done.\n— `coordinator-codex-example` (agent coordination)",
             ("coordinator-codex-example", "coordinator")),
            ("— codex-example, queue coordinator", ("codex-example", "coordinator")),
            ("AI assistance: written by an AI coding agent acting as coordinator.",
             (None, "coordinator")),
            ("**APPROVE** at `abcd1234` by `reviewer-1-abcd1234`", None),
            ("**APPROVE** at abcd1234 by helper\nIndependent non-author agent review.",
             (None, None)),
            ("<!-- Agent session: fake-session\nAgent role: worker -->", None),
            ("Worker codex-bf12f189 is taking this task.", ("codex-bf12f189", "worker")),
            ("awaiting review at abcdef12 (worker session 2680eecf).", ("2680eecf", "worker")),
            ("I’m taking the author-side restack as coordinator `codex-5b83`.",
             ("codex-5b83", "coordinator")),
            ("Agent session: session-1\nAgent role: coordinator", ("session-1", "coordinator")),
        ]
        for body, expected in cases:
            with self.subTest(body=body):
                self.assertEqual(activity.disclosure(body), expected)

    def test_quoted_mentions_and_conflicting_fields(self):
        self.assertIsNone(activity.disclosure(
            "Please ask Codex session abcd1234 to review.\n"
            "> Agent session: abcdefgh\n```md\nAgent role: worker\n```\n"))
        self.assertEqual(activity.disclosure(
            "Agent session: first-id\nAgent session: second-id\nAgent role: worker"),
            (None, "worker"))


class CountWindows(unittest.TestCase):
    def test_distinct_sessions_with_overlapping_roles_and_logins(self):
        now = dt.datetime(2026, 11, 28, 10, tzinfo=dt.timezone.utc)

        def event(age, number, session, role, account="shared"):
            return {"time": int((now - dt.timedelta(days=age)).timestamp()), "session": session,
                    "role": role, "account": account, "url": f"https://github.com/o/r/pull/{number}"}

        report = activity.summarize([
            event(0, 1, "first-session", "worker"),
            event(1, 2, "first-session", "worker"),
            event(2, 3, "first-session", "coordinator", "other"),
            event(3, 4, "second-session", "worker"),
            event(4, 5, None, "coordinator"),
            event(5, 6, None, None),
            event(7, 7, "older-session", "coordinator"),
            event(30, 8, "outside", "worker"),
            event(-1, 9, "future-session", "worker"),
        ], now)
        week = report["windows"]["7"]
        self.assertEqual((week["sessions"], week["worker"], week["coordinator"], week["both"]),
                         (2, 2, 1, 1))
        self.assertEqual((week["events"], week["without_session"], week["without_role"]),
                         (6, 2, 1))
        self.assertEqual([row["sessions"] for row in week["accounts"]], [2, 1])
        self.assertEqual(report["windows"]["30"]["sessions"], 3)
        self.assertEqual(week["daily"][-1]["sessions"], 1)
        self.assertEqual(len(week["daily"]), 8)
        self.assertEqual(week["daily"][0]["events"], 0)
        self.assertEqual(sum(row["events"] for row in week["daily"]), week["events"])
        self.assertNotIn("first-session", json.dumps(report))

    def test_empty_report_has_both_windows_and_daily_zeroes(self):
        now = dt.datetime(2026, 11, 28, tzinfo=dt.timezone.utc)
        report = activity.summarize([], now)
        self.assertEqual(report["windows"]["7"]["accounts"], [])
        self.assertEqual(len(report["windows"]["30"]["daily"]), 30)
        self.assertTrue(all(row["events"] == 0 for row in report["windows"]["30"]["daily"]))


class Collection(unittest.TestCase):
    def test_filters_out_old_edits_and_uses_review_submission_time(self):
        now = dt.datetime(2026, 11, 28, tzinfo=dt.timezone.utc)
        updated = "2026-11-26T00:00:00Z"
        old_issue = {"body": "Agent session: old-session", "created_at": "2026-01-01T00:00:00Z",
                     "updated_at": updated}
        url = "https://github.com/o/r/pull/1#pullrequestreview-2"
        review = {"body": "Agent session: current-session", "submittedAt": updated,
                  "url": url, "author": {"login": "MixedCase"}}
        prs = [{"number": 1, "updatedAt": updated, "reviews": {"totalCount": 2}},
               {"number": 2, "updatedAt": updated, "reviews": {"totalCount": 0}}]
        with patch.object(activity, "_records", return_value=[old_issue]), \
             patch.object(activity, "_comments", return_value=[]), \
             patch.object(activity, "_reviews", return_value=[review]) as reviews:
            events = activity.fetch("o/r", "test-token", prs, now)
        self.assertEqual(reviews.call_args.args[1], [1])
        self.assertEqual([(event["account"], event["session"], event["url"]) for event in events],
                         [("mixedcase", "current-session", url)])

    def test_comments_resume_with_overlap_at_offset_limit(self):
        start = activity.github_prs.parse_iso("2026-11-18T00:00:00Z")
        end = "2026-11-19T00:00:00Z"
        boundary = {"id": 1, "updated_at": end}
        second = {"id": 2, "updated_at": end}
        with patch.object(activity, "_records",
                          side_effect=[iter([boundary] * 24_000), [boundary, second]]) as pages:
            rows = list(activity._comments("https://api.github.com/repos/o/r/issues", start, "token"))
        self.assertEqual(rows[-2:], [boundary, second])
        self.assertIn("since=2026-11-18T23%3A59%3A59", pages.call_args.args[0])

    def test_reviews_follow_cursor_and_skip_drafts(self):
        def page(cursor, nodes):
            return {"repository": {"p0": {"reviews": {
                "pageInfo": {"hasPreviousPage": bool(cursor), "startCursor": cursor},
                "nodes": nodes,
            }}}}

        newest = {"submittedAt": "2026-11-28T00:00:00Z"}
        earlier = {"submittedAt": "2026-11-27T00:00:00Z"}
        with patch.object(activity.github_prs, "graphql", side_effect=[
            page("previous-page", [newest, {"submittedAt": None}]), page(None, [earlier]),
        ]) as graphql:
            self.assertEqual(list(activity._reviews("o/r", [1], "token")), [newest, earlier])
        self.assertIn('before: "previous-page"', graphql.call_args.args[0])
