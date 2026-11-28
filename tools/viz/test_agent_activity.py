# Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Christian Reitwiessner
"""Tests for the worker activity page's attribution and count semantics."""

import datetime as dt
import unittest
from unittest.mock import patch

import agent_activity as activity


class Disclosures(unittest.TestCase):
    def test_recognizes_public_worker_ids(self):
        cases = [
            ("Worker ID: `Fleet-A`", "fleet-a"),
            ("Worker codex-bf12f189 is taking this task.", "codex-bf12f189"),
            ("Done.\n— Codex worker `codex-5b83-roabp`, agent validation.",
             "codex-5b83-roabp"),
            ("Worker ID: long-lived\nAgent session: one-off", "long-lived"),
            ("Worker ID: long-lived\nWorker ID: LONG-LIVED", "long-lived"),
        ]
        for body, expected in cases:
            with self.subTest(body=body):
                self.assertEqual(activity.worker_id(body), expected)

    def test_excludes_session_ids_aliases_and_ambiguous_worker_ids(self):
        cases = [
            "Codex session 62875d29 claims the next batch.",
            "— Codex worker, session `4625757c`",
            "Agent session: disposable\nAgent role: worker",
            "**APPROVE** at abcd1234 by worker-alias",
            "<!-- Worker ID: hidden-worker -->",
            "> Worker ID: quoted-worker\n```md\nWorker ID: example-worker\n```\n",
            "Worker ID: first-worker\nWorker ID: second-worker",
        ]
        for body in cases:
            with self.subTest(body=body):
                self.assertIsNone(activity.worker_id(body))


class CountWindows(unittest.TestCase):
    def test_deduplicates_worker_ids_across_accounts_and_repeated_activity(self):
        now = dt.datetime(2026, 11, 28, 10, tzinfo=dt.timezone.utc)

        def event(age, number, identifier, account="shared"):
            return {"time": int((now - dt.timedelta(days=age)).timestamp()),
                    "worker_id": identifier, "account": account,
                    "url": f"https://github.com/o/r/pull/{number}"}

        report = activity.summarize([
            event(0, 1, "first-worker"),
            event(1, 2, "first-worker"),
            event(2, 3, "first-worker", "other"),
            event(6.9, 4, "second-worker"),
            event(7, 7, "older-worker"),
            event(30, 8, "outside"),
            event(-1, 9, "future-worker"),
        ], now)
        week = report["windows"]["7"]
        self.assertEqual((week["workers"], week["events"]), (2, 4))
        self.assertEqual([row["workers"] for row in week["accounts"]], [2, 1])
        self.assertEqual(week["accounts"][0]["workers_by_id"][0],
                         {"id": "first-worker", "url": "https://github.com/o/r/pull/1"})
        self.assertEqual(report["windows"]["30"]["workers"], 3)
        self.assertEqual(week["daily"][-1]["workers"], 1)
        self.assertEqual(len(week["daily"]), 8)
        self.assertEqual(week["daily"][0]["workers"], 1)
        self.assertEqual(sum(row["events"] for row in week["daily"]), week["events"])

    def test_empty_report_has_both_windows_and_daily_zeroes(self):
        now = dt.datetime(2026, 11, 28, tzinfo=dt.timezone.utc)
        report = activity.summarize([], now)
        self.assertEqual(report["windows"]["7"]["accounts"], [])
        self.assertEqual(len(report["windows"]["30"]["daily"]), 31)
        self.assertTrue(all(row["events"] == 0 for row in report["windows"]["30"]["daily"]))


class Collection(unittest.TestCase):
    def test_filters_out_old_edits_and_uses_review_submission_time(self):
        now = dt.datetime(2026, 11, 28, tzinfo=dt.timezone.utc)
        updated = "2026-11-26T00:00:00Z"
        old_issue = {"body": "Worker ID: old-worker", "created_at": "2026-01-01T00:00:00Z",
                     "updated_at": updated}
        url = "https://github.com/o/r/pull/1#pullrequestreview-2"
        review = {"body": "Worker ID: current-worker", "submittedAt": updated,
                  "url": url, "author": {"login": "MixedCase"}}
        prs = [{"number": 1, "updatedAt": updated, "reviews": {"totalCount": 2}},
               {"number": 2, "updatedAt": updated, "reviews": {"totalCount": 0}}]
        with patch.object(activity, "_records", return_value=[old_issue]), \
             patch.object(activity, "_comments", return_value=[]), \
             patch.object(activity, "_reviews", return_value=[review]) as reviews:
            events = activity.fetch("o/r", "test-token", prs, now)
        self.assertEqual(reviews.call_args.args[1], [1])
        self.assertEqual([(event["account"], event["worker_id"], event["url"]) for event in events],
                         [("mixedcase", "current-worker", url)])

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
