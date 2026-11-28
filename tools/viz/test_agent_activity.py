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
            ("Worker `codex-bf12f189` is preparing the author-side restack.",
             "codex-bf12f189"),
            ("I’m implementing the Z-table conversion as worker `codex-5b83-boolean`.",
             "codex-5b83-boolean"),
            ("Done.\n— Codex worker `codex-5b83-roabp`, agent validation.",
             "codex-5b83-roabp"),
            ("Worker ID: long-lived\nAgent session: one-off", "long-lived"),
            ("Worker ID: long-lived\nWorker ID: LONG-LIVED", "long-lived"),
        ]
        for body, expected in cases:
            with self.subTest(body=body):
                self.assertEqual(activity.worker_id(body), expected)

    def test_worker_credits_from_public_pull_requests(self):
        # Minimal excerpts from PRs #9038, #9039, #9046, #9047, #9049, #9051–#9053.
        cases = [
            (8, "Implemented by agent worker `{worker}` under coordinator `{coord}`."),
            (7, "Drafted, proved, and locally validated by an AI coding agent "
                "(`{worker}` under coordinator `{coord}`)."),
            (11, "- **Worker:** `{worker}`\nAuthored with AI assistance (`{worker}`)."),
            (10, "*Implemented by AI worker `{worker}` under coordinator `{coord}`.*"),
            (9, "Implemented by agent worker `{worker}` under coordinator `{coord}` (Antigravity)."),
            (12, "Authoring worker: `{worker}` (coordinator: `{coord}`)."),
            (13, "Implemented and locally validated with an Antigravity coding agent "
                 "(`{worker}`) under coordinator `{coord}`."),
            (14, "Implemented by an AI coding agent (`{worker}`) under orchestration."),
        ]
        for number, template in cases:
            identifier = f"worker-{number}-nrtv-b373d02a"
            body = template.format(worker=identifier, coord="coord-nrtv-b373d02a")
            with self.subTest(worker=identifier):
                self.assertEqual(activity.worker_id(body), identifier)
        self.assertEqual(activity.worker_id(
            "Addressed source-check items from `source-checker-9046-b373d02a` at revision "
            "`3d97442668` (by `worker-11-nrtv-b373d02a`):"), "worker-11-nrtv-b373d02a")

    def test_worker_id_after_longer_fence_closer(self):
        self.assertEqual(activity.worker_id(
            "~~~md\nWorker ID: example-worker\n~~~~\nWorker ID: actual-worker"),
            "actual-worker")
        self.assertIsNone(activity.worker_id(
            "~~~~md\n~~~\nWorker ID: example-worker\n~~~~"))

    def test_excludes_session_ids_aliases_and_ambiguous_worker_ids(self):
        cases = [
            "Codex session 62875d29 claims the next batch.",
            "Please assign codex-bf12f189 as worker `codex-bf12f189`.",
            "I’m reviewing the PR from worker `codex-bf12f189`.",
            "— Codex worker, session `4625757c`",
            "Agent session: disposable\nAgent role: worker",
            "**APPROVE** at abcd1234 by worker-alias",
            "Reviewer: `worker-7-nrtv-b373d02a`",
            "Coordinator: `coord-nrtv-b373d02a`",
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
