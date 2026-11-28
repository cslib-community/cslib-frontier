"""Offline tests for the precondition checks in scripts/queue_pr.py."""

from __future__ import annotations

import contextlib
import copy
import importlib.util
import io
import json
import os
import pathlib
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import call, patch

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import queue_pr  # noqa: E402

SHA = "a" * 40
BASE_SHA = "d" * 40
COMMIT_ID = "COMMIT_1"


REAL_FETCH_REVIEW_POSTS = queue_pr.fetch_review_posts


def setUpModule() -> None:
    # `main` reads review records over REST on every run; tests that do not exercise them see a
    # PR without any, and never reach the network. ReviewRecordTests patch their own.
    patcher = patch.object(queue_pr, "fetch_review_posts", return_value=[])
    patcher.start()
    unittest.addModuleCleanup(patcher.stop)


def check_run(name: str = "ci-checks", status: str = "COMPLETED",
              conclusion: str | None = "SUCCESS", started: str = "2026-11-07T10:00:00Z",
              app: int = 15368) -> dict:
    return {"name": name, "status": status, "conclusion": conclusion, "startedAt": started,
            "checkSuite": {"app": {"databaseId": app}}}


def connection(*checks: dict, cursor: str | None = None) -> dict:
    return {"nodes": list(checks), "pageInfo": {"endCursor": cursor,
                                                "hasNextPage": cursor is not None}}


def pr(*checks: dict, committed: str = "2026-11-07T09:00:00Z", retargeted: str | None = None,
       **fields) -> dict:
    commit = {"id": COMMIT_ID, "oid": SHA, "committedDate": committed,
              "statusCheckRollup": {"contexts": connection(*checks)}}
    return {"id": "PR_1", "state": "OPEN", "isDraft": False, "baseRefName": "main",
            "baseRefOid": BASE_SHA, "headRefOid": SHA, "mergeable": "MERGEABLE",
            "mergeQueueEntry": None,
            "timelineItems": {"nodes": [{"createdAt": retargeted}] if retargeted else []},
            "commits": {"nodes": [{"commit": commit}]}, **fields}


def first_page(*checks: dict, cursor: str | None = "page-1", **fields) -> dict:
    result = pr(**fields)
    result["commits"]["nodes"][0]["commit"]["statusCheckRollup"]["contexts"] = connection(
        *checks, cursor=cursor)
    return {"repository": {"pullRequest": result}}


def later_page(*checks: dict, cursor: str | None = None, oid: str = SHA) -> dict:
    return {"node": {"oid": oid, "statusCheckRollup": {
        "contexts": connection(*checks, cursor=cursor)}}}


class AssessTests(unittest.TestCase):
    def test_green_approved_head_is_ready(self) -> None:
        self.assertEqual(queue_pr.assess(pr(check_run(), check_run("HTTP cache origin")), SHA),
                         ("ready", []))

    def test_moved_head_is_refused(self) -> None:
        status, reasons = queue_pr.assess(pr(check_run(), headRefOid="b" * 40), SHA)
        self.assertEqual(status, "refused")
        self.assertIn("not the approved", reasons[0])

    def test_already_queued_is_reported(self) -> None:
        entry = {"position": 2, "state": "AWAITING_CHECKS"}
        self.assertEqual(queue_pr.assess(pr(check_run(), mergeQueueEntry=entry), SHA)[0],
                         "queued")

    def test_draft_stacked_and_conflicting_prs_are_refused(self) -> None:
        status, reasons = queue_pr.assess(
            pr(check_run(), isDraft=True, baseRefName="feat/lower", mergeable="CONFLICTING"), SHA)
        self.assertEqual(status, "refused")
        self.assertEqual(len(reasons), 3)

    def test_failed_required_check_is_refused(self) -> None:
        status, reasons = queue_pr.assess(pr(check_run(conclusion="FAILURE")), SHA)
        self.assertEqual(status, "refused")
        self.assertIn("ci-checks", reasons[0])

    def test_running_or_missing_required_check_is_pending(self) -> None:
        self.assertEqual(queue_pr.assess(pr(check_run(status="IN_PROGRESS", conclusion=None)),
                                         SHA)[0], "pending")
        self.assertEqual(queue_pr.assess(pr(check_run("HTTP cache origin")), SHA)[0], "pending")

    def test_only_the_latest_run_of_a_check_counts(self) -> None:
        cancelled = check_run(conclusion="CANCELLED", started="2026-11-07T09:00:00Z")
        self.assertEqual(queue_pr.assess(pr(cancelled, check_run()), SHA)[0], "ready")
        rerun = check_run(status="IN_PROGRESS", conclusion=None, started="2026-11-07T11:00:00Z")
        self.assertEqual(queue_pr.assess(pr(check_run(), rerun), SHA)[0], "pending")

    def test_unknown_mergeability_is_pending(self) -> None:
        status, reasons = queue_pr.assess(pr(check_run(), mergeable="UNKNOWN"), SHA)
        self.assertEqual(status, "pending")
        self.assertIn("merges cleanly", reasons[0])

    def test_check_from_another_app_does_not_count(self) -> None:
        self.assertEqual(queue_pr.assess(pr(check_run(app=1)), SHA)[0], "pending")

    def test_retargeted_head_must_merge_main_first(self) -> None:
        status, reasons = queue_pr.assess(pr(check_run(), retargeted="2026-11-07T09:30:00Z"), SHA)
        self.assertEqual(status, "refused")
        self.assertIn("base changed", reasons[0])
        already_merged = pr(check_run(), retargeted="2026-11-07T09:30:00Z", baseIsAncestor=True)
        self.assertEqual(queue_pr.assess(already_merged, SHA), ("ready", []))
        later = pr(check_run(), retargeted="2026-11-07T08:00:00Z")
        self.assertEqual(queue_pr.assess(later, SHA)[0], "ready")

    def test_stale_latest_commit_is_refused(self) -> None:
        stale = pr(check_run())
        stale["commits"]["nodes"][0]["commit"]["oid"] = "c" * 40
        self.assertEqual(queue_pr.assess(stale, SHA)[0], "refused")

    def test_closed_pr_is_refused(self) -> None:
        self.assertEqual(queue_pr.assess(pr(check_run(), state="MERGED"), SHA)[0], "refused")


class ArgumentTests(unittest.TestCase):
    def test_abbreviated_sha_and_bad_repo_are_rejected(self) -> None:
        for argv in (["12", "abc1234"], ["12", SHA, "--repo", "cslib-frontier"],
                     ["12", SHA, "--hold-hubs", "--allow-hub"]):
            with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
                queue_pr.main(argv)


class QueueEstimateTests(unittest.TestCase):
    def test_estimate_counts_the_entries_ahead_of_a_new_or_queued_pr(self) -> None:
        self.assertEqual(
            queue_pr.queue_estimate(pr(queueDepth=16), 12),
            "Merge queue: 16 entries ahead of #12; roughly 42 min to land (16 x 14 min / 8 "
            "concurrent group builds, then its own build) if no group build fails.")
        queued = pr(queueDepth=16, mergeQueueEntry={"position": 2, "state": "QUEUED"})
        self.assertIn("1 entry ahead of #12; roughly 16 min", queue_pr.queue_estimate(queued, 12))
        self.assertIn("0 entries ahead of #12; roughly 14 min",
                      queue_pr.queue_estimate(pr(queueDepth=0), 12))
        self.assertIsNone(queue_pr.queue_estimate(pr(), 12))

    def test_fetch_pr_reads_the_queue_depth_only_when_well_formed(self) -> None:
        for queue, depth in (({"entries": {"totalCount": 5}}, 5), (None, None),
                             ({"entries": {"totalCount": True}}, None),
                             ({"entries": {"totalCount": -1}}, None)):
            response = first_page(check_run(), cursor=None)
            response["repository"]["mergeQueue"] = queue
            with self.subTest(queue=queue), \
                 patch.object(queue_pr, "gh_graphql", return_value=response):
                self.assertEqual(queue_pr.fetch_pr("o", "r", 12).get("queueDepth"), depth)

    def test_every_run_prints_the_estimate_first_even_when_refused(self) -> None:
        for fields, status in (({}, 0), ({"isDraft": True}, 1)):
            out = io.StringIO()
            with self.subTest(fields=fields), \
                 patch.object(queue_pr, "fetch_pr",
                              return_value=pr(check_run(), queueDepth=3, **fields)), \
                 patch.object(queue_pr, "check_queue_prefix", return_value=None), \
                 patch.object(queue_pr, "gh_graphql", return_value={
                     "enqueuePullRequest": {"mergeQueueEntry": {"position": 4}}}), \
                 contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
                self.assertEqual(queue_pr.main(["12", SHA]), status, out.getvalue())
                self.assertTrue(out.getvalue().startswith(
                    "Merge queue: 3 entries ahead of #12; roughly 19 min"), out.getvalue())


class PaginationTests(unittest.TestCase):
    def run_main(self, *responses: dict | Exception, wait: str = "0"):
        out = io.StringIO()
        with patch.object(queue_pr, "gh_graphql", side_effect=responses) as graphql, \
             patch.object(queue_pr, "fetch_discussion", return_value=("unchanged",)), \
             patch.object(queue_pr, "check_queue_prefix", return_value=None), \
             patch.object(queue_pr.time, "sleep"), contextlib.redirect_stdout(out), \
             contextlib.redirect_stderr(out):
            status = queue_pr.main(["12", SHA, "--wait", wait])
        return status, out.getvalue(), graphql.call_args_list

    def test_required_attempt_after_first_hundred_can_fail_or_be_pending(self) -> None:
        first = [check_run(), *(check_run(f"other-{i}") for i in range(99))]
        for latest in (check_run(conclusion="FAILURE", started="2026-11-07T11:00:00Z"),
                       check_run(status="IN_PROGRESS", conclusion=None,
                                 started="2026-11-07T11:00:00Z")):
            with self.subTest(latest=latest):
                status, out, calls = self.run_main(first_page(*first), later_page(latest))
                self.assertEqual(status, 1, out)
                self.assertEqual([c.args[0] for c in calls],
                                 [queue_pr.QUERY, queue_pr.CONTEXTS_QUERY])

    def test_required_check_on_third_page_queues_the_exact_head(self) -> None:
        other = [check_run(f"other-{i}") for i in range(100)]
        entry = {"enqueuePullRequest": {"mergeQueueEntry": {"position": 3, "state": "QUEUED"}}}
        status, out, calls = self.run_main(first_page(*other),
                                            later_page(*other, cursor="page-2"),
                                            later_page(check_run()), entry)
        self.assertEqual(status, 0, out)
        self.assertEqual(calls, [
            call(queue_pr.QUERY, owner="cslib-community", name="cslib-frontier", number=12),
            call(queue_pr.CONTEXTS_QUERY, id=COMMIT_ID, after="page-1"),
            call(queue_pr.CONTEXTS_QUERY, id=COMMIT_ID, after="page-2"),
            call(queue_pr.ENQUEUE, id="PR_1", sha=SHA)])

    def test_later_page_still_requires_the_configured_app(self) -> None:
        status, _, calls = self.run_main(first_page(check_run("other")),
                                          later_page(check_run(app=1)))
        self.assertEqual(status, 1)
        self.assertEqual(len(calls), 2)

    def test_later_page_does_not_override_a_newer_first_page_failure(self) -> None:
        status, _, calls = self.run_main(
            first_page(check_run(conclusion="FAILURE", started="2026-11-07T11:00:00Z")),
            later_page(check_run()))
        self.assertEqual(status, 1)
        self.assertEqual(len(calls), 2)

    def test_wrong_or_missing_commit_cannot_supply_a_later_page(self) -> None:
        for page in ({"node": None}, later_page(check_run(), oid="b" * 40)):
            with self.subTest(page=page):
                status, out, calls = self.run_main(first_page(check_run()), page)
                self.assertEqual(status, 2, out)
                self.assertIn("matching commit", out)
                self.assertEqual(len(calls), 2)

    def test_push_during_pagination_cannot_enqueue_a_replacement_head(self) -> None:
        # Page two is still fetched by the immutable old commit ID. A concurrent push makes
        # GitHub reject enqueue's unchanged expectedHeadOid, rather than queueing the new head.
        status, out, calls = self.run_main(first_page(check_run("other")),
                                            later_page(check_run()),
                                            queue_pr.GhError("head changed before enqueue"))
        self.assertEqual(status, 2, out)
        self.assertEqual(calls[1], call(queue_pr.CONTEXTS_QUERY, id=COMMIT_ID, after="page-1"))
        self.assertEqual(calls[2], call(queue_pr.ENQUEUE, id="PR_1", sha=SHA))

    def test_null_rollup_on_first_page_is_pending(self) -> None:
        first = first_page()
        commit = first["repository"]["pullRequest"]["commits"]["nodes"][0]["commit"]
        commit["statusCheckRollup"] = None
        self.assertEqual(self.run_main(first)[0], 1)

    def test_null_or_incomplete_later_page_is_an_error(self) -> None:
        for rollup in (None, {"contexts": None}, {"contexts": {"nodes": []}},
                       {"contexts": {"nodes": [None], "pageInfo": {"hasNextPage": False}}}):
            with self.subTest(rollup=rollup):
                page = {"node": {"oid": SHA, "statusCheckRollup": rollup}}
                status, out, calls = self.run_main(first_page(check_run()),
                                                    page)
                self.assertEqual(status, 2, out)
                self.assertIn("incomplete check-context page", out)
                self.assertEqual(len(calls), 2)

    def test_missing_or_repeated_cursor_stops_without_enqueuing(self) -> None:
        for cursor in (None, ""):
            with self.subTest(cursor=cursor):
                first = first_page(check_run())
                info = first["repository"]["pullRequest"]["commits"]["nodes"][0]["commit"]
                info["statusCheckRollup"]["contexts"]["pageInfo"]["endCursor"] = cursor
                self.assertEqual(self.run_main(first)[0], 2)
        status, out, calls = self.run_main(first_page(check_run()),
                                            later_page(check_run(), cursor="page-1"))
        self.assertEqual(status, 2, out)
        self.assertEqual(len(calls), 2)

    def test_graphql_failure_on_later_page_stops_without_enqueuing(self) -> None:
        status, out, calls = self.run_main(first_page(check_run()), queue_pr.GhError("API error"))
        self.assertEqual(status, 2)
        self.assertIn("API error", out)
        self.assertEqual(len(calls), 2)

    def test_mergeability_retry_fetches_all_pages_again(self) -> None:
        status, out, calls = self.run_main(
            first_page(check_run(), mergeable="UNKNOWN"), later_page(check_run("other")),
            first_page(check_run()),
            later_page(check_run(conclusion="FAILURE", started="2026-11-07T11:00:00Z")))
        self.assertEqual(status, 1, out)
        self.assertEqual([c.args[0] for c in calls],
                         [queue_pr.QUERY, queue_pr.CONTEXTS_QUERY] * 2)

    def test_waiting_for_checks_fetches_fresh_pages(self) -> None:
        entry = {"enqueuePullRequest": {"mergeQueueEntry": {"position": 1, "state": "QUEUED"}}}
        status, out, calls = self.run_main(
            first_page(check_run("other")),
            later_page(check_run(status="IN_PROGRESS", conclusion=None)),
            first_page(check_run("other")), later_page(check_run()), entry, wait="1")
        self.assertEqual(status, 0, out)
        self.assertEqual([c.args[0] for c in calls],
                         [queue_pr.QUERY, queue_pr.CONTEXTS_QUERY] * 2 + [queue_pr.ENQUEUE])


class GraphqlResponseTests(unittest.TestCase):
    def test_invalid_json_null_data_and_graphql_errors_raise_gh_error(self) -> None:
        for output in ("not JSON", "null", '{"data": null}',
                       json.dumps({"data": None, "errors": [{"message": "denied"}]})):
            with self.subTest(output=output), \
                 patch.object(queue_pr.subprocess, "run",
                              return_value=subprocess.CompletedProcess([], 0, output, "")), \
                 self.assertRaises(queue_pr.GhError):
                queue_pr.gh_graphql(queue_pr.QUERY)


def discussion_comment(identity: str = "C1", body: str = "approve", **fields) -> dict:
    return {"id": identity, "body": body, "updatedAt": "2026-11-13T11:16:09Z", **fields}


def discussion_page() -> dict:
    return {"node": {"id": "PR_1", "body": "PR scope", "comments": connection(),
                     "reviews": connection(), "reviewThreads": connection()}}


def discussion_thread(identity: str = "T1", **fields) -> dict:
    return {"id": identity, "isResolved": True, "comments": connection(
        discussion_comment("RC1", state="SUBMITTED")), **fields}


class DiscussionTests(unittest.TestCase):
    def snapshot(self, *pages):
        with patch.object(queue_pr, "gh_graphql", side_effect=pages) as api:
            result = queue_pr.fetch_discussion("PR_1")
        return result, api.call_args_list

    def test_body_comments_reviews_and_inline_changes_are_observable(self) -> None:
        initial = discussion_page()
        node = initial["node"]
        node["comments"] = connection(discussion_comment())
        node["reviews"] = connection(discussion_comment(
            "R1", state="APPROVED", submittedAt="2026-11-13T11:16:09Z"))
        node["reviewThreads"] = connection(discussion_thread())
        baseline, _ = self.snapshot(initial)
        # The old comment is edited without advancing its second-resolution timestamp.
        changes = [lambda p: p.update(body="human review required"),
                   lambda p: p["comments"]["nodes"].append(discussion_comment("C2", "hold")),
                   lambda p: p["comments"]["nodes"][0].update(body="hold"),
                   lambda p: p["comments"]["nodes"].clear(),
                   lambda p: p["reviews"]["nodes"][0].update(body="approval held"),
                   lambda p: p["reviews"]["nodes"][0].update(state="DISMISSED"),
                   lambda p: p["reviews"]["nodes"].append(discussion_comment(
                       "R2", state="CHANGES_REQUESTED", submittedAt="2026-11-13T11:17:49Z")),
                   lambda p: p["reviewThreads"]["nodes"][0].update(isResolved=False),
                   lambda p: p["reviewThreads"]["nodes"][0]["comments"]["nodes"][0].update(
                       body="still broken"),
                   lambda p: p["reviewThreads"]["nodes"][0]["comments"]["nodes"].append(
                       discussion_comment("RC2", "hold", state="SUBMITTED"))]
        for index, change in enumerate(changes):
            with self.subTest(change=index):
                changed = copy.deepcopy(initial)
                change(changed["node"])
                self.assertNotEqual(self.snapshot(changed)[0], baseline)

    def test_order_ci_events_reactions_and_unpublished_drafts_do_not_change_snapshot(self) -> None:
        initial = discussion_page()
        initial["node"]["comments"] = connection(discussion_comment(), discussion_comment("C2"))
        baseline, _ = self.snapshot(initial)
        changed = copy.deepcopy(initial)
        node = changed["node"]
        node.update(updatedAt="later", statusCheckRollup="new CI event")
        node["comments"]["nodes"].reverse()
        node["comments"]["nodes"][0]["reactions"] = ["THUMBS_UP"]
        node["reviews"] = connection(discussion_comment("R1", state="PENDING", submittedAt=None))
        node["reviewThreads"] = connection(discussion_thread(comments=connection(
            discussion_comment("RC1", state="PENDING"))))
        self.assertEqual(self.snapshot(changed)[0], baseline)

    def test_all_three_connections_and_nested_comments_are_paginated_by_owner(self) -> None:
        first = discussion_page()
        first["node"].update(comments=connection(discussion_comment(), cursor="c1"),
                             reviews=connection(cursor="r1"),
                             reviewThreads=connection(cursor="t1"))
        thread = discussion_thread(comments=connection(cursor="rc1"))
        result, calls = self.snapshot(
            first,
            {"node": {"id": "PR_1", "comments": connection(discussion_comment("C2"), cursor="c2")}},
            {"node": {"id": "PR_1", "comments": connection(discussion_comment("C3", "hold"))}},
            {"node": {"id": "PR_1", "reviews": connection(discussion_comment(
                "R1", state="DISMISSED", submittedAt="2026-11-13T11:16:09Z"))}},
            {"node": {"id": "PR_1", "reviewThreads": connection(thread)}},
            {"node": {"id": "T1", "comments": connection(
                discussion_comment("RC1", state="SUBMITTED"))}})
        self.assertEqual(len(result[1]), 3)
        self.assertEqual(result[1][-1][1], "hold")
        self.assertEqual(result[2][0][3], "DISMISSED")
        self.assertEqual(len(result[3][0][2]), 1)
        self.assertEqual([c.kwargs for c in calls], [
            {"id": "PR_1"}, {"id": "PR_1", "after": "c1"},
            {"id": "PR_1", "after": "c2"}, {"id": "PR_1", "after": "r1"},
            {"id": "PR_1", "after": "t1"}, {"id": "T1", "after": "rc1"}])
        self.assertIn("... on PullRequestReviewThread", calls[-1].args[0])

    def test_missing_pr_identity_or_body_is_an_error(self) -> None:
        for node in (None, {}, {"id": "another"}, {"id": "PR_1", "body": None}):
            with self.subTest(node=node), self.assertRaises(queue_pr.GhError):
                self.snapshot({"node": node})

    def test_null_malformed_or_incomplete_connections_are_errors(self) -> None:
        bad = (None, [], "bad", {}, {"nodes": [], "pageInfo": {}},
               {"nodes": [None], "pageInfo": {"hasNextPage": False}})
        for field in ("comments", "reviews", "reviewThreads", "inline"):
            for connection_value in bad:
                with self.subTest(field=field, value=connection_value), \
                     self.assertRaises(queue_pr.GhError):
                    page = discussion_page()
                    if field == "inline":
                        page["node"]["reviewThreads"] = connection(
                            discussion_thread(comments=connection_value))
                    else:
                        page["node"][field] = connection_value
                    self.snapshot(page)

    def test_missing_text_review_time_and_thread_states_are_errors(self) -> None:
        for field, item in (
                ("comments", discussion_comment(body=None)),
                ("comments", discussion_comment(updatedAt=None)),
                ("reviews", discussion_comment("R1", state="APPROVED", submittedAt=None)),
                ("reviews", discussion_comment("R1", state=[])),
                ("reviewThreads", discussion_thread(isResolved=None)),
                ("reviewThreads", discussion_thread(comments=connection(
                    discussion_comment("RC1", state=None))))):
            with self.subTest(field=field, item=item), self.assertRaises(queue_pr.GhError):
                page = discussion_page()
                page["node"][field] = connection(item)
                self.snapshot(page)

    def test_later_pages_require_matching_owner_valid_cursor_and_distinct_ids(self) -> None:
        initial = discussion_page()
        initial["node"]["comments"] = connection(discussion_comment(), cursor="c1")
        for later in ({"node": None}, {"node": {"id": "another"}},
                      {"node": {"id": "PR_1", "comments": connection(discussion_comment())}},
                      {"node": {"id": "PR_1", "comments": connection({"body": "no ID"})}},
                      {"node": {"id": "PR_1", "comments": connection(cursor="c1")}},
                      queue_pr.GhError("API failed")):
            with self.subTest(later=later), self.assertRaises(queue_pr.GhError):
                self.snapshot(copy.deepcopy(initial), later)
        for cursor in (None, ""):
            with self.subTest(cursor=cursor), self.assertRaises(queue_pr.GhError):
                malformed = copy.deepcopy(initial)
                malformed["node"]["comments"]["pageInfo"]["endCursor"] = cursor
                self.snapshot(malformed)


class WaitingDiscussionTests(unittest.TestCase):
    def run_main(self, prs, discussions=("same", "same"), wait="1"):
        out, events = io.StringIO(), []
        def snapshot(_):
            events.append("discussion")
            response = next(snapshots)
            if isinstance(response, Exception):
                raise response
            return response
        snapshots = iter(discussions)
        with patch.object(queue_pr, "fetch_pr", side_effect=prs), \
             patch.object(queue_pr, "fetch_discussion", side_effect=snapshot) as discussion, \
             patch.object(queue_pr, "check_queue_prefix", return_value=None), \
             patch.object(queue_pr.time, "sleep", side_effect=lambda _: events.append("sleep")), \
             patch.object(queue_pr, "gh_graphql", return_value={
                 "enqueuePullRequest": {"mergeQueueEntry": {"position": 1}}}) as api, \
             contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            result = queue_pr.main(["5134", SHA, "--wait", wait])
        return result, out.getvalue(), events, discussion, api

    def test_hold_posted_during_wait_refuses_without_enqueuing(self) -> None:
        pending = pr(check_run(status="IN_PROGRESS", conclusion=None))
        result, out, events, _, api = self.run_main(
            [pending, pr(check_run())], ("source approval", "final material review held"))
        self.assertEqual(result, 1, out)
        self.assertIn("discussion changed", out)
        self.assertIn("reread", out)
        self.assertEqual(events, ["discussion", "sleep", "discussion"])
        api.assert_not_called()

    def test_unchanged_discussion_is_read_only_twice_and_queues_expected_head(self) -> None:
        pending = pr(check_run(status="IN_PROGRESS", conclusion=None))
        result, out, events, _, api = self.run_main([pending, pending, pr(check_run())])
        self.assertEqual(result, 0, out)
        self.assertEqual(events, ["discussion", "sleep", "sleep", "discussion"])
        api.assert_called_once_with(queue_pr.ENQUEUE, id="PR_1", sha=SHA)

    def test_automatic_mergeability_wait_is_guarded_even_without_wait_option(self) -> None:
        result, out, events, _, api = self.run_main(
            [pr(check_run(), mergeable="UNKNOWN"), pr(check_run())],
            ("approved", "hold"), wait="0")
        self.assertEqual(result, 1, out)
        self.assertEqual(events, ["discussion", "sleep", "discussion"])
        api.assert_not_called()

    def test_instant_ready_or_no_sleep_pending_does_not_read_discussion(self) -> None:
        for initial, expected in ((pr(check_run()), 0), (pr(), 1)):
            with self.subTest(expected=expected):
                result, out, events, discussion, _ = self.run_main([initial], wait="0")
                self.assertEqual(result, expected, out)
                self.assertEqual(events, [])
                discussion.assert_not_called()

    def test_already_queued_does_not_read_discussion_or_mutate_even_after_wait(self) -> None:
        queued = pr(check_run(), mergeQueueEntry={"position": 2, "state": "QUEUED"})
        for prs in ([queued], [pr(check_run(), mergeable="UNKNOWN"), queued]):
            with self.subTest(prs=prs):
                result, out, events, _, api = self.run_main(prs, ("baseline",))
                self.assertEqual(result, 0, out)
                self.assertEqual(events.count("discussion"), len(prs) - 1)
                api.assert_not_called()

    def test_incomplete_initial_or_final_snapshot_prevents_enqueue(self) -> None:
        pending = pr(check_run(), mergeable="UNKNOWN")
        for discussions in ((queue_pr.GhError("incomplete discussion"),),
                            ("baseline", queue_pr.GhError("incomplete discussion"))):
            with self.subTest(discussions=discussions):
                result, out, _, _, api = self.run_main([pending, pr(check_run())], discussions)
                self.assertEqual(result, 2, out)
                self.assertIn("incomplete discussion", out)
                api.assert_not_called()

    def test_failed_check_or_changed_head_still_prevents_enqueue(self) -> None:
        pending = pr(check_run(status="IN_PROGRESS", conclusion=None))
        for final in (pr(check_run(conclusion="FAILURE")), pr(check_run(), headRefOid="b" * 40)):
            with self.subTest(final=final):
                result, out, events, _, api = self.run_main([pending, final], ("baseline",))
                self.assertEqual(result, 1, out)
                self.assertEqual(events.count("discussion"), 1)
                api.assert_not_called()


NOW = queue_pr.datetime.datetime(2026, 11, 25, 5, 0, tzinfo=queue_pr.datetime.timezone.utc)
HEAD_TIME = "2026-11-25T03:00:00Z"


def post(body: str, posted: str = "2026-11-25T04:00:00Z", url: str = "c") -> queue_pr.ReviewPost:
    return queue_pr.ReviewPost(url, posted, body)


def approve(posted: str = "2026-11-25T04:00:00Z", sha: str = SHA, by: str = "rev-a",
            url: str = "approve") -> queue_pr.ReviewPost:
    return post(f"**APPROVE** at {sha} by {by} (agent)\n\nLooks right.", posted, url)


class ReviewRecordTests(unittest.TestCase):
    def check(self, *posts: queue_pr.ReviewPost, reviewer: str | None = None):
        return queue_pr.review_record_check(list(posts), SHA, now=NOW, since=HEAD_TIME,
                                            reviewer=reviewer)

    def assertRefused(self, result, *fragments: str) -> None:
        refusals, _ = result
        self.assertTrue(any(all(f in r for f in fragments) for r in refusals),
                        f"no refusal mentions {fragments}: {refusals}")

    def test_no_records_or_a_plain_approval_allow_queueing(self) -> None:
        self.assertEqual(self.check(), ([], []))
        self.assertEqual(self.check(approve()), ([], []))

    def test_hold_in_force_refuses_until_its_owner_releases_it_or_it_expires(self) -> None:
        hold = post("Waiting on the lower PR.\n  **HOLD owner=rev-b until=2026-11-25T08:00Z "
                    "reason=lower PR #10 has not landed", "2026-11-25T03:30:00Z", "hold")
        self.assertRefused(self.check(hold, approve()), "HOLD owner=rev-b", "lower PR #10",
                           "HOLD-RELEASED by=rev-b")
        released = post("HOLD-RELEASED by=rev-b reason=#10 landed", "2026-11-25T04:30:00Z")
        self.assertEqual(self.check(hold, approve(), released)[0], [])
        by_other = post("HOLD-RELEASED by=rev-c reason=impatient", "2026-11-25T04:30:00Z")
        self.assertRefused(self.check(hold, approve(), by_other), "HOLD owner=rev-b")
        earlier_release = post("HOLD-RELEASED by=rev-b reason=old", "2026-11-25T03:00:00Z")
        self.assertRefused(self.check(earlier_release, hold, approve()), "HOLD owner=rev-b")
        expired = post("HOLD owner=rev-b until=2026-11-25T04:59Z reason=x", "2026-11-25T03:30:00Z")
        self.assertEqual(self.check(expired, approve())[0], [])

    def test_a_hold_named_in_the_approval_itself_refuses(self) -> None:
        named = post(f"**APPROVE** at {SHA} by rev-a\n\nHOLD owner=maintainer "
                     "until=2026-11-26T00:00Z reason=migration first", "2026-11-25T04:00:00Z")
        self.assertRefused(self.check(named), "HOLD owner=maintainer", "migration first")
        for by in ("maintainer", "SamuelSchlesinger"):
            self.assertEqual(self.check(named, post(f"HOLD-RELEASED by={by} reason=done",
                                                    "2026-11-25T04:10:00Z"))[0], [])
        self.assertRefused(self.check(named, post("HOLD-RELEASED by=rev-a reason=done",
                                                  "2026-11-25T04:10:00Z")), "owner=maintainer")

    def test_records_in_fenced_code_blocks_are_examples_not_records(self) -> None:
        example = post("Use this form:\n```\nHOLD owner=rev-b until=2026-11-25T08:00Z reason=x\n"
                       f"CLAIM review head={SHA} by=rev-b until=2026-11-25T05:30Z\n```\n"
                       "~~~text\nHOLD owner=rev-c until=2026-11-25T08:00Z reason=y\n~~~\n"
                       "Holding nothing here.", "2026-11-25T04:50:00Z", "example")
        self.assertEqual(self.check(approve(), example),
                         ([], ["example: Holding nothing here."]))
        after = post("```\nnot closed\nHOLD owner=rev-b until=2026-11-25T08:00Z reason=x",
                     "2026-11-25T04:50:00Z")
        self.assertEqual(self.check(approve(), after)[0], [])

    def test_unexpired_claim_of_another_reviewer_without_a_verdict_refuses(self) -> None:
        claim = post(f"CLAIM review head={SHA} by=rev-b until=2026-11-25T05:30Z",
                     "2026-11-25T04:50:00Z", "claim")
        self.assertRefused(self.check(approve(), claim), "`rev-b` claims review",
                           "2026-11-25T05:30Z", "--reviewer")
        self.assertEqual(self.check(approve(), claim, reviewer="rev-b")[0], [])
        refused = self.check(approve(), claim, reviewer="rev-a")
        self.assertRefused(refused, "`rev-b` claims review")
        self.assertNotIn("--reviewer", " ".join(refused[0]))
        other_head = post(f"CLAIM review head={'b' * 40} by=rev-b until=2026-11-25T05:30Z",
                          "2026-11-25T04:50:00Z")
        self.assertEqual(self.check(approve(), other_head)[0], [])
        expired = post(f"CLAIM review head={SHA} by=rev-b until=2026-11-25T04:59Z",
                       "2026-11-25T04:20:00Z")
        self.assertEqual(self.check(approve(), expired)[0], [])

    def test_a_claim_holds_at_most_forty_five_minutes_after_it_was_posted(self) -> None:
        overlong = post(f"**CLAIM review head={SHA} by=rev-b until=2026-11-26T00:00Z**",
                        "2026-11-25T04:10:00Z")
        self.assertEqual(self.check(approve(), overlong)[0], [])
        recent = post(f"**CLAIM review head={SHA} by=rev-b until=2026-11-26T00:00Z**",
                      "2026-11-25T04:30:00Z")
        self.assertRefused(self.check(approve(), recent), "until 2026-11-25T05:15Z")

    def test_the_claimants_verdict_at_the_head_ends_its_claim(self) -> None:
        claim = post(f"CLAIM review head={SHA} by=rev-b until=2026-11-25T05:30Z",
                     "2026-11-25T04:40:00Z")
        for verdict, ends in (
                (approve("2026-11-25T04:50:00Z", by="rev-b"), True),
                (post(f"**APPROVE** at {SHA} by rev-b. This is agent review.",
                      "2026-11-25T04:50:00Z"), True),
                (post(f"**APPROVE** at {SHA} by `rev-b`),", "2026-11-25T04:50:00Z"), True),
                (post(f"**REQUEST_CHANGES** at `{SHA[:12]}` by `rev-b`", "2026-11-25T04:50:00Z"),
                 True),
                (post(f"**APPROVE** at {SHA}\n\n`rev-b` (agent) checked the statement.",
                      "2026-11-25T04:50:00Z"), True),
                (approve("2026-11-25T04:50:00Z", by="rev-c"), False),
                (approve("2026-11-25T04:50:00Z", sha="b" * 40, by="rev-b"), False),
                (approve("2026-11-25T04:30:00Z", by="rev-b"), False)):
            with self.subTest(verdict=verdict.body.splitlines()[0], posted=verdict.posted):
                posts = sorted([claim, verdict], key=lambda p: p.posted)
                claims = [r for r in self.check(*posts)[0] if "claims review" in r]
                self.assertEqual(claims == [], ends, claims)

    def test_request_changes_after_the_newest_approval_at_the_head_refuses(self) -> None:
        changes = post(f"**REQUEST_CHANGES** at `{SHA[:12]}` by `rev-b`\n\nThe name overclaims.",
                       "2026-11-25T04:30:00Z", "changes")
        self.assertRefused(self.check(approve(), changes), "**REQUEST_CHANGES**", "changes")
        self.assertRefused(self.check(changes), "**REQUEST_CHANGES**")
        self.assertEqual(self.check(changes, approve("2026-11-25T04:40:00Z"))[0], [])
        at_old_head = post(f"**REQUEST_CHANGES** at {'b' * 40}", "2026-11-25T04:30:00Z")
        self.assertEqual(self.check(approve(), at_old_head)[0], [])
        not_first_line = post(f"Note\n**REQUEST_CHANGES** at {SHA}", "2026-11-25T04:30:00Z")
        self.assertEqual(self.check(approve(), not_first_line)[0], [])
        short = post("**REQUEST_CHANGES** at aaaaaa", "2026-11-25T04:30:00Z")
        self.assertEqual(self.check(approve(), short)[0], [])

    def test_free_text_holds_since_the_approval_are_advisories_not_refusals(self) -> None:
        before = post("Hold until #10 lands.", "2026-11-25T03:30:00Z", "before")
        malformed = post("HOLD owner=rev-b until=tomorrow reason=x", "2026-11-25T04:10:00Z",
                         "malformed")
        prose = post("The hypotheses hold for every n.", "2026-11-25T04:20:00Z", "prose")
        plural = post("Holds. None remain; the threshold holds.", "2026-11-25T04:25:00Z")
        refusals, advisories = self.check(before, approve(), malformed, prose, plural)
        self.assertEqual(refusals, [])
        self.assertEqual(advisories, ["malformed: HOLD owner=rev-b until=tomorrow reason=x",
                                      "prose: The hypotheses hold for every n."])
        # Without an approval at the head, posts since the head was committed are listed.
        self.assertEqual(self.check(post("hold this", "2026-11-25T02:00:00Z", "old"),
                                    post("hold that", "2026-11-25T03:10:00Z", "new"))[1],
                         ["new: hold that"])
        structured = post("HOLD owner=rev-b until=2026-11-25T04:10Z reason=expired",
                          "2026-11-25T04:05:00Z")
        self.assertEqual(self.check(approve(), structured), ([], []))


class ReviewRecordMainTests(unittest.TestCase):
    def run_main(self, posts, *args: str):
        out = io.StringIO()
        with patch.object(queue_pr, "fetch_pr", return_value=pr(check_run())), \
             patch.object(queue_pr, "fetch_review_posts", side_effect=posts) as read, \
             patch.object(queue_pr, "fetch_discussion") as discussion, \
             patch.object(queue_pr, "check_queue_prefix", return_value=None), \
             patch.object(queue_pr, "gh_graphql", return_value={
                 "enqueuePullRequest": {"mergeQueueEntry": {"position": 1}}}) as api, \
             patch.object(queue_pr, "utc_now", return_value=NOW), \
             contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            result = queue_pr.main(["12", SHA, *args])
        return result, out.getvalue(), read, discussion, api

    def test_instant_ready_run_reads_records_and_refuses_a_hold_without_enqueuing(self) -> None:
        hold = post("HOLD owner=rev-b until=2026-11-25T08:00Z reason=lower PR", url="hold")
        result, out, read, discussion, api = self.run_main([[approve(), hold]])
        self.assertEqual(result, 1, out)
        self.assertIn("#12 not queued: HOLD owner=rev-b", out)
        read.assert_called_once_with("cslib-community", "cslib-frontier", 12)
        discussion.assert_not_called()  # no sleep and no prefix: no discussion snapshot
        api.assert_not_called()

    def test_reviewer_exempts_its_own_claim_and_advisories_do_not_block(self) -> None:
        claim = post(f"CLAIM review head={SHA} by=rev-a until=2026-11-25T05:30Z",
                     "2026-11-25T04:50:00Z")
        note = post("Holding off on a nit; not blocking.", "2026-11-25T04:55:00Z", "nit")
        result, out, _, _, api = self.run_main([[approve(), claim, note]])
        self.assertEqual(result, 1, out)
        self.assertIn("`rev-a` claims review", out)
        api.assert_not_called()
        result, out, _, _, api = self.run_main([[approve(), claim, note]], "--reviewer", "rev-a")
        self.assertEqual(result, 0, out)
        self.assertIn("Advisory:", out)
        self.assertIn("nit: Holding off on a nit; not blocking.", out)
        api.assert_called_once_with(queue_pr.ENQUEUE, id="PR_1", sha=SHA)

    def test_unreadable_records_stop_without_enqueuing(self) -> None:
        result, out, _, _, api = self.run_main(queue_pr.GhError("HTTP 502"))
        self.assertEqual(result, 2, out)
        self.assertIn("queue_pr: HTTP 502", out)
        api.assert_not_called()

    def test_malformed_reviewer_is_rejected(self) -> None:
        with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
            queue_pr.main(["12", SHA, "--reviewer", "two words"])


class FetchReviewPostsTests(unittest.TestCase):
    def test_comments_and_submitted_reviews_are_read_over_rest_oldest_first(self) -> None:
        comments = [{"id": 1, "html_url": "u1", "created_at": "2026-11-25T04:10:00Z",
                     "body": "late"}]
        reviews = [{"id": 2, "html_url": "u2", "submitted_at": "2026-11-25T04:00:00Z",
                    "state": "APPROVED", "body": "early"},
                   {"id": 3, "state": "PENDING", "body": "draft"},
                   {"id": 4, "html_url": "u4", "submitted_at": "2026-11-25T04:20:00Z",
                    "state": "COMMENTED", "body": None}]
        outputs = [json.dumps(comments), json.dumps(reviews[:2]) + json.dumps(reviews[2:])]
        with patch.object(queue_pr.subprocess, "run", side_effect=[
                subprocess.CompletedProcess([], 0, output, "") for output in outputs]) as run:
            posts = REAL_FETCH_REVIEW_POSTS("o", "r", 12)
        self.assertEqual(posts, [queue_pr.ReviewPost("u2", "2026-11-25T04:00:00Z", "early"),
                                 queue_pr.ReviewPost("u1", "2026-11-25T04:10:00Z", "late"),
                                 queue_pr.ReviewPost("u4", "2026-11-25T04:20:00Z", "")])
        self.assertEqual([c.args[0] for c in run.call_args_list], [
            ["gh", "api", "--paginate", "repos/o/r/issues/12/comments?per_page=100"],
            ["gh", "api", "--paginate", "repos/o/r/pulls/12/reviews?per_page=100"]])

    def test_concatenated_pages_from_gh_paginate_are_decoded(self) -> None:
        for stdout, items in (('[{"a": 1}][{"a": 2}]', [{"a": 1}, {"a": 2}]),
                              ('[{"a": 1}]\n[]\n[{"a": 3}]\n', [{"a": 1}, {"a": 3}]),
                              ("[]", [])):
            with self.subTest(stdout=stdout), patch.object(
                    queue_pr.subprocess, "run",
                    return_value=subprocess.CompletedProcess([], 0, stdout, "")):
                self.assertEqual(queue_pr.gh_rest_items("e"), items)

    def test_errors_and_malformed_responses_raise_gh_error(self) -> None:
        for result in (subprocess.CompletedProcess([], 1, "", "unknown flag: --slurp"),
                       subprocess.CompletedProcess([], 0, "not JSON", ""),
                       subprocess.CompletedProcess([], 0, "", ""),
                       subprocess.CompletedProcess([], 0, "[][", ""),
                       subprocess.CompletedProcess([], 0, '{"message": "x"}', ""),
                       subprocess.CompletedProcess([], 0, '[]{"message": "x"}', ""),
                       subprocess.CompletedProcess([], 0, "[1]", ""),
                       subprocess.CompletedProcess([], 0, '[{"created_at": null}]', ""),
                       subprocess.CompletedProcess(
                           [], 0, '[{"created_at": "2026-11-25T04:00Z", "body": ""}]', "")):
            with self.subTest(result=result), \
                 patch.object(queue_pr.subprocess, "run", return_value=result), \
                 self.assertRaises(queue_pr.GhError):
                REAL_FETCH_REVIEW_POSTS("o", "r", 12)


class RetargetAncestorTests(unittest.TestCase):
    def compare_result(self, payload: dict | str, returncode: int = 0) -> subprocess.CompletedProcess:
        text = payload if isinstance(payload, str) else json.dumps(payload)
        return subprocess.CompletedProcess([], returncode, text, "")

    def test_retarget_after_commit_allows_head_already_containing_main(self) -> None:
        entry = {"enqueuePullRequest": {"mergeQueueEntry": {"position": 1, "state": "QUEUED"}}}
        for status in ("ahead", "identical"):
            with self.subTest(status=status):
                page = {"repository": {"pullRequest": pr(
                    check_run(), retargeted="2026-11-07T09:30:00Z")}}
                compare = self.compare_result({
                    "status": status,
                    "behind_by": 0,
                    "merge_base_commit": {"sha": BASE_SHA},
                })
                out = io.StringIO()
                with patch.object(queue_pr, "gh_graphql", side_effect=[page, entry]) as graphql, \
                     patch.object(queue_pr, "check_queue_prefix", return_value=None), \
                     patch.object(queue_pr.subprocess, "run", return_value=compare) as run, \
                     contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
                    rc = queue_pr.main(["7108", SHA])
                self.assertEqual(rc, 0, out.getvalue())
                run.assert_called_once_with(
                    ["gh", "api", f"repos/{queue_pr.REPO}/compare/{BASE_SHA}...{SHA}"],
                    capture_output=True, text=True)
                self.assertEqual(graphql.call_args_list[-1],
                                 call(queue_pr.ENQUEUE, id="PR_1", sha=SHA))

    def test_retarget_after_commit_refuses_when_main_not_ancestor_or_compare_fails(self) -> None:
        cases = (
            self.compare_result({"status": "diverged", "behind_by": 2,
                                 "merge_base_commit": {"sha": "e" * 40}}),
            self.compare_result({"status": "behind", "behind_by": 1,
                                 "merge_base_commit": {"sha": SHA}}),
            self.compare_result({"status": "ahead", "behind_by": 0,
                                 "merge_base_commit": {"sha": "e" * 40}}),
            self.compare_result({"status": "ahead", "behind_by": 1,
                                 "merge_base_commit": {"sha": BASE_SHA}}),
            self.compare_result("not json"),
            self.compare_result({}, returncode=1),
        )
        for compare in cases:
            with self.subTest(compare=compare):
                page = {"repository": {"pullRequest": pr(
                    check_run(), retargeted="2026-11-07T09:30:00Z")}}
                out = io.StringIO()
                with patch.object(queue_pr, "gh_graphql", return_value=page) as graphql, \
                     patch.object(queue_pr.subprocess, "run", return_value=compare), \
                     contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
                    rc = queue_pr.main(["7108", SHA])
                self.assertEqual(rc, 1, out.getvalue())
                self.assertIn("its base changed after the approved head was committed",
                              out.getvalue())
                self.assertEqual(len(graphql.call_args_list), 1)

    def test_compare_is_skipped_when_retarget_did_not_follow_commit(self) -> None:
        for candidate in (
                pr(check_run()),
                pr(check_run(), retargeted="2026-11-07T08:00:00Z"),
                pr(check_run(), retargeted="2026-11-07T09:30:00Z", baseRefName="feat/lower"),
                pr(check_run(), retargeted="2026-11-07T09:30:00Z",
                   mergeQueueEntry={"position": 1, "state": "QUEUED"})):
            with self.subTest(candidate=candidate), \
                 patch.object(queue_pr, "gh_graphql",
                              return_value={"repository": {"pullRequest": candidate}}), \
                 patch.object(queue_pr.subprocess, "run") as run:
                queue_pr.fetch_pr("cslib-community", "cslib-frontier", 12)
                run.assert_not_called()

    def test_retargeted_head_without_rollup_yet_waits_for_checks_when_main_is_ancestor(self) -> None:
        raw = pr(retargeted="2026-11-07T09:30:00Z")
        raw["commits"]["nodes"][0]["commit"]["statusCheckRollup"] = None
        compare = self.compare_result({
            "status": "ahead",
            "behind_by": 0,
            "merge_base_commit": {"sha": BASE_SHA},
        })
        with patch.object(queue_pr, "gh_graphql", return_value={"repository": {"pullRequest": raw}}), \
             patch.object(queue_pr.subprocess, "run", return_value=compare):
            fetched = queue_pr.fetch_pr("cslib-community", "cslib-frontier", 7108)
        self.assertEqual(queue_pr.assess(fetched, SHA),
                         ("pending", ["required checks are still running at the approved head"]))


class QueuePrefixTests(unittest.TestCase):
    OTHER_SHA = "c" * 40

    def test_empty_queue_skips_object_fetch_even_without_local_repo(self) -> None:
        import queue_status

        with tempfile.TemporaryDirectory() as tmp, \
             patch.object(queue_status, "prefix", return_value=(BASE_SHA, [])) as pref, \
             patch.object(queue_status, "fetch_objects") as fetch:
            self.assertIsNone(
                queue_pr.check_queue_prefix("o", "r", 12, SHA, root=pathlib.Path(tmp)))
            pref.assert_called_once_with("o", "r", 12, SHA, graphql=queue_pr.gh_graphql)
            fetch.assert_not_called()

    def test_nonempty_queue_without_repo_or_helper_refuses_instead_of_skipping(self) -> None:
        import queue_status

        with tempfile.TemporaryDirectory() as tmp, \
             patch.object(queue_status, "prefix", return_value=(BASE_SHA, [(10, self.OTHER_SHA)])):
            reason = queue_pr.check_queue_prefix("o", "r", 12, SHA, root=pathlib.Path(tmp))
            self.assertIsNotNone(reason)
            assert reason is not None
            self.assertIn("merge queue has entries ahead (#10)", reason)

        with patch.dict(sys.modules, {"queue_status": None}), \
             patch.object(queue_pr, "snapshot_queue_prefix",
                          return_value=(BASE_SHA, [(10, self.OTHER_SHA)])):
            reason_no_helper = queue_pr.check_queue_prefix("o", "r", 12, SHA)
            self.assertIsNotNone(reason_no_helper)
            assert reason_no_helper is not None
            self.assertIn("merge queue has entries ahead (#10)", reason_no_helper)

    def test_conflicting_queue_prefix_and_bare_git_dir_from_scratch(self) -> None:
        import queue_status

        env = {"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
               "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.test",
               "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.test"}
        with tempfile.TemporaryDirectory() as tmp, patch.dict(os.environ, env):
            base_dir = pathlib.Path(tmp)
            root = base_dir / "work"
            bare = base_dir / "bare.git"
            scratch = base_dir / "scratch"
            root.mkdir()
            scratch.mkdir()

            def git(*args: str) -> str:
                return subprocess.check_output(["git", *args], cwd=root, text=True).strip()

            def commit(path: str, content: str) -> str:
                (root / path).write_text(content)
                git("add", ".")
                git("commit", "-qm", path)
                return git("rev-parse", "HEAD")

            git("init", "-q", "-b", "main")
            base = commit("rows", "old\n")
            non_conflicting = commit("other", "first PR\n")
            git("branch", "non-conflicting")
            git("switch", "-q", "--detach", base)
            conflicting = commit("rows", "queued PR\n")
            git("branch", "conflicting")
            git("switch", "-q", "--detach", base)
            candidate = commit("rows", "candidate PR\n")
            git("branch", "candidate")
            subprocess.run(["git", "clone", "-q", "--bare", str(root), str(bare)], check=True)

            old_cwd = pathlib.Path.cwd()
            try:
                os.chdir(scratch)
                with patch.dict(os.environ, {"GIT_DIR": ".." + os.sep + "bare.git"}), \
                     patch.object(queue_status, "prefix",
                                  return_value=(base, [(10, non_conflicting)])), \
                     patch.object(queue_status, "fetch_objects"):
                    self.assertIsNone(queue_pr.check_queue_prefix("o", "r", 12, candidate))

                with patch.dict(os.environ, {"GIT_DIR": str(bare)}), \
                     patch.object(queue_status, "prefix",
                                  return_value=(base, [(10, non_conflicting), (11, conflicting)])), \
                     patch.object(queue_status, "fetch_objects"):
                    reason = queue_pr.check_queue_prefix("o", "r", 12, candidate)
                    self.assertIsNotNone(reason)
                    assert reason is not None
                    self.assertIn("'rows' first conflicts at #11", reason)
            finally:
                os.chdir(old_cwd)

            ready_pr = pr(check_run(), headRefOid=candidate)
            ready_pr["commits"]["nodes"][0]["commit"]["oid"] = candidate
            out = io.StringIO()
            with patch.object(queue_pr, "fetch_pr", return_value=ready_pr), \
                 patch.object(queue_pr, "check_queue_prefix", return_value=reason), \
                 patch.object(queue_pr, "gh_graphql") as api, \
                 contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
                rc = queue_pr.main(["12", candidate])
            self.assertEqual(rc, 1, out.getvalue())
            self.assertIn("#12 not queued:", out.getvalue())
            api.assert_not_called()

    def test_hold_introduced_during_prefix_replay_stops_enqueue(self) -> None:
        import queue_status

        ready_pr = pr(check_run())
        state = {"discussion": ("before_replay",)}

        def fake_check_prefix(_root: pathlib.Path, _base: str,
                              _entries: list[tuple[int, str]], _sha: str) -> int:
            state["discussion"] = ("hold_comment_added_during_replay",)
            return 0

        out = io.StringIO()
        with patch.object(queue_pr, "fetch_pr", return_value=ready_pr), \
             patch.object(queue_pr, "fetch_discussion",
                          side_effect=lambda _id: state["discussion"]) as disc, \
             patch.object(queue_status, "prefix",
                          return_value=(BASE_SHA, [(10, self.OTHER_SHA)])), \
             patch.object(queue_status, "fetch_objects"), \
             patch.object(queue_status, "check_prefix", side_effect=fake_check_prefix), \
             patch.object(queue_pr, "replay_repository", return_value=queue_pr.ROOT), \
             patch.object(queue_pr, "gh_graphql") as api, \
             contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            rc = queue_pr.main(["12", SHA])
        self.assertEqual(rc, 1, out.getvalue())
        self.assertEqual(disc.call_count, 2)
        self.assertIn("its review discussion changed while waiting", out.getvalue())
        api.assert_not_called()

    def test_changed_queue_prefix_during_replay_stops_enqueue(self) -> None:
        import queue_status

        ready_pr = pr(check_run())
        third_sha = "d" * 40
        prefixes = iter([
            (BASE_SHA, [(10, self.OTHER_SHA)]),
            (BASE_SHA, [(10, self.OTHER_SHA), (11, third_sha)]),
        ])
        out = io.StringIO()
        with patch.object(queue_pr, "fetch_pr", return_value=ready_pr), \
             patch.object(queue_pr, "fetch_discussion", return_value=("unchanged",)), \
             patch.object(queue_status, "prefix", side_effect=lambda *a, **kw: next(prefixes)), \
             patch.object(queue_status, "fetch_objects"), \
             patch.object(queue_status, "check_prefix", return_value=0), \
             patch.object(queue_pr, "replay_repository", return_value=queue_pr.ROOT), \
             patch.object(queue_pr, "gh_graphql") as api, \
             contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            rc = queue_pr.main(["12", SHA])
        self.assertEqual(rc, 1, out.getvalue())
        self.assertIn("the merge queue changed during prefix replay", out.getvalue())
        api.assert_not_called()

    def test_cli_and_separately_loaded_entrypoint_catch_prefix_gh_error(self) -> None:
        import queue_status

        spec = importlib.util.spec_from_file_location("cli_queue_pr", queue_pr.__file__)
        assert spec is not None and spec.loader is not None
        cli_mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cli_mod)
        self.assertIsNot(cli_mod.GhError, queue_pr.GhError)
        ready_pr = pr(check_run())
        out = io.StringIO()
        err = io.StringIO()
        with patch.object(cli_mod, "fetch_pr", return_value=ready_pr), \
             patch.object(queue_status, "prefix",
                          side_effect=queue_pr.GhError("prefix API failed")), \
             patch.object(cli_mod, "gh_graphql") as api, \
             contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = cli_mod.main(["12", SHA])
        self.assertEqual(rc, 2)
        self.assertIn("queue_pr: prefix API failed", err.getvalue())
        api.assert_not_called()

        with tempfile.TemporaryDirectory() as tmp:
            bin_dir = pathlib.Path(tmp)
            calls_log = bin_dir / "calls.log"
            pr_payload = json.dumps({"data": {"repository": {"pullRequest": ready_pr}}})
            fake_gh = bin_dir / "gh"
            fake_gh.write_text(
                f"#!{sys.executable}\n"
                "import pathlib, sys\n"
                f"log = pathlib.Path({str(calls_log)!r})\n"
                "joined = ' '.join(sys.argv[1:])\n"
                "with log.open('a', encoding='utf-8') as fh:\n"
                "    fh.write(joined + '\\n')\n"
                "if 'enqueuePullRequest' in joined:\n"
                "    sys.exit(99)\n"
                "if 'mergeQueue { entries' in joined:\n"
                "    sys.stderr.write('HTTP 502 from GitHub\\n')\n"
                "    sys.exit(1)\n"
                f"sys.stdout.write({pr_payload!r})\n",
                encoding="utf-8",
            )
            fake_gh.chmod(fake_gh.stat().st_mode | stat.S_IXUSR)
            env = {**os.environ, "PATH": f"{bin_dir}{os.pathsep}{os.environ.get('PATH', '')}"}
            proc = subprocess.run(
                [sys.executable, str(pathlib.Path(queue_pr.__file__).resolve()), "12", SHA],
                capture_output=True, text=True, env=env,
            )
            self.assertEqual(proc.returncode, 2, proc.stdout + proc.stderr)
            self.assertIn("queue_pr:", proc.stderr)
            self.assertIn("HTTP 502 from GitHub", proc.stderr)
            self.assertNotIn("enqueuePullRequest", calls_log.read_text(encoding="utf-8"))

    def test_inconsistent_queue_listing_fails_closed_without_enqueuing(self) -> None:
        import queue_status

        ready_pr = pr(check_run())
        out = io.StringIO()
        err = io.StringIO()
        with patch.object(queue_pr, "fetch_pr", return_value=ready_pr), \
             patch.object(queue_status, "prefix", side_effect=ValueError("queue changed")), \
             patch.object(queue_pr, "gh_graphql") as api, \
             contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = queue_pr.main(["12", SHA])
        self.assertEqual(rc, 2, err.getvalue())
        self.assertIn("merge-queue prefix check failed", err.getvalue())
        api.assert_not_called()


class HubImpactQueueTests(unittest.TestCase):
    GIT_ENV = {
        "GIT_CONFIG_GLOBAL": os.devnull,
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_AUTHOR_NAME": "t",
        "GIT_AUTHOR_EMAIL": "t@example.test",
        "GIT_COMMITTER_NAME": "t",
        "GIT_COMMITTER_EMAIL": "t@example.test",
    }

    def _seed_hub_repo(self, base_dir: pathlib.Path) -> tuple[pathlib.Path, dict[str, str]]:
        root = base_dir / "repo"
        (root / "CslibFrontier").mkdir(parents=True)
        (root / "CslibFrontierTests").mkdir(parents=True)

        def git(*args: str) -> str:
            return subprocess.check_output(["git", *args], cwd=root, text=True).strip()

        def write(rel: str, text: str) -> None:
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")

        def commit(msg: str) -> str:
            git("add", "-A")
            git("commit", "-qm", msg)
            return git("rev-parse", "HEAD")

        git("init", "-q", "-b", "main")
        write("CslibFrontier/Hub.lean", "module\npublic def hubVal := 0\n")
        write("CslibFrontier/Mid.lean", "module\npublic import CslibFrontier.Hub\npublic def midVal := 0\n")
        write("CslibFrontier/Leaf1.lean", "module\npublic import CslibFrontier.Mid\ndef l1 := 0\n")
        write("CslibFrontier/Leaf2.lean", "module\npublic import CslibFrontier.Mid\ndef l2 := 0\n")
        write("CslibFrontierTests/Smoke.lean", "module\nimport CslibFrontier.Leaf1\n")
        write("CslibFrontier.lean", "module\npublic import CslibFrontier.Hub\n")
        m0 = commit("m0")

        # Active queue entry #10 touches an unrelated file.
        write("README.md", "queued ahead\n")
        queued_sha = commit("queued-10")
        git("switch", "-q", "--detach", m0)

        # Candidate PR A modifies `CslibFrontier/Hub.lean` (4 transitive importers).
        write("CslibFrontier/Hub.lean", "module\npublic def hubVal := 1\n")
        hub_pr_sha = commit("hub-pr")
        git("switch", "-q", "--detach", m0)

        # Candidate PR B modifies `CslibFrontier/Mid.lean` (3 transitive importers).
        write("CslibFrontier/Mid.lean", "module\npublic import CslibFrontier.Hub\npublic def midVal := 1\n")
        mid_pr_sha = commit("mid-pr")
        git("switch", "-q", "--detach", m0)

        # Candidate PR C only adds a new module and updates root aggregate `CslibFrontier.lean`.
        write("CslibFrontier/BrandNew.lean", "module\ndef brandNew := 0\n")
        write("CslibFrontier.lean", "module\npublic import CslibFrontier.BrandNew\npublic import CslibFrontier.Hub\n")
        new_mod_sha = commit("new-mod-pr")
        git("switch", "-q", "--detach", m0)

        # Advance `main` on `Hub.lean` AFTER `leaf_pr_sha` branched from `m0` to verify 3-dot merge-base diffing.
        write("CslibFrontier/Leaf2.lean", "module\npublic import CslibFrontier.Mid\ndef l2 := 9\n")
        leaf_pr_sha = commit("leaf-pr")
        git("switch", "-q", "main")
        git("reset", "-q", "--hard", m0)
        write("CslibFrontier/Hub.lean", "module\npublic def hubVal := 42\n")
        m1 = commit("main-hub-advance")

        return root, {
            "m0": m0,
            "m1": m1,
            "queued": queued_sha,
            "hub_pr": hub_pr_sha,
            "mid_pr": mid_pr_sha,
            "new_mod": new_mod_sha,
            "leaf_pr": leaf_pr_sha,
        }

    @staticmethod
    def _run_main(root: pathlib.Path, sha: str, base_sha: str, entries: list[tuple[int, str]],
                  extra_args: list[str] = (), threshold: int = 3,
                  high: int = 4) -> tuple[int, str, int]:
        import check_hub_impact
        import queue_status

        enqueue_ok = {"enqueuePullRequest": {"mergeQueueEntry": {"position": 2, "state": "QUEUED"}}}
        candidate_pr = pr(check_run(), baseRefOid=base_sha, headRefOid=sha)
        candidate_pr["commits"]["nodes"][0]["commit"]["oid"] = sha
        out = io.StringIO()
        with patch.object(queue_pr, "ROOT", root), \
             patch.object(queue_pr, "replay_repository", return_value=root), \
             patch.object(queue_pr, "fetch_pr", return_value=candidate_pr), \
             patch.object(queue_pr, "fetch_discussion", return_value=("same",)), \
             patch.object(queue_status, "prefix", return_value=(base_sha, entries)), \
             patch.object(queue_status, "fetch_objects"), \
             patch.object(check_hub_impact, "DEFAULT_THRESHOLD", threshold), \
             patch.object(check_hub_impact, "HIGH_THRESHOLD", high), \
             patch.object(queue_pr, "gh_graphql", return_value=enqueue_ok) as api, \
             contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            rc = queue_pr.main(["12", sha, *extra_args])
        return rc, out.getvalue(), api.call_count

    def test_hub_notice_and_hold_hubs_with_active_queue(self) -> None:
        with tempfile.TemporaryDirectory() as tmp, patch.dict(os.environ, self.GIT_ENV):
            root, shas = self._seed_hub_repo(pathlib.Path(tmp))

            def run_case(*args, **kwargs) -> tuple[int, str, int]:
                return self._run_main(root, *args, **kwargs)

            # 1. >= HIGH_THRESHOLD (4 >= 4): default queues and prints `Warning:`.
            rc, out, calls = run_case(shas["hub_pr"], shas["m0"], [(10, shas["queued"])])
            self.assertEqual(rc, 0, out)
            self.assertEqual(calls, 1)
            self.assertIn("#12 queued at", out)
            self.assertIn("Warning: #12 modifies high-fan-in hub module(s) (`CslibFrontier/Hub.lean` (4 transitive importers))", out)
            self.assertIn("(#10)", out)

            # 2. DEFAULT_THRESHOLD <= count < HIGH_THRESHOLD (3 in [3, 4)): prints `Note:`.
            rc, out, calls = run_case(shas["mid_pr"], shas["m0"], [(10, shas["queued"])])
            self.assertEqual(rc, 0, out)
            self.assertEqual(calls, 1)
            self.assertIn("Note: #12 modifies high-fan-in hub module(s) (`CslibFrontier/Mid.lean` (3 transitive importers))", out)

            # 3. `--hold-hubs` refuses before ENQUEUE when queue has active entries.
            rc, out, calls = run_case(shas["hub_pr"], shas["m0"], [(10, shas["queued"])], ["--hold-hubs"])
            self.assertEqual(rc, 1, out)
            self.assertEqual(calls, 0)
            self.assertIn("#12 not queued: modifies high-fan-in hub module(s)", out)
            self.assertIn("`CslibFrontier/Hub.lean` (4 transitive importers)", out)

            # 4. Empty queue allows `--hold-hubs` to enqueue cleanly without warning.
            rc, out, calls = run_case(shas["hub_pr"], shas["m0"], [], ["--hold-hubs"])
            self.assertEqual(rc, 0, out)
            self.assertEqual(calls, 1)
            self.assertNotIn("modifies high-fan-in hub", out)

            # 5. Adding a brand-new module + root aggregate `CslibFrontier.lean` triggers no hub hit.
            rc, out, calls = run_case(shas["new_mod"], shas["m0"], [(10, shas["queued"])], ["--hold-hubs"], threshold=1)
            self.assertEqual(rc, 0, out)
            self.assertEqual(calls, 1)
            self.assertNotIn("modifies high-fan-in hub", out)

            # 6. Leaf PR branched before `main` edited `Hub.lean` is not blamed for `main`'s hub edit.
            rc, out, calls = run_case(shas["leaf_pr"], shas["m1"], [(10, shas["queued"])], ["--hold-hubs"], threshold=2)
            self.assertEqual(rc, 0, out)
            self.assertEqual(calls, 1)
            self.assertNotIn("Hub.lean", out)

    def test_hub_pacing_refuses_by_queue_depth_and_the_rebuilds_it_adds(self) -> None:
        with tempfile.TemporaryDirectory() as tmp, patch.dict(os.environ, self.GIT_ENV), \
             patch.object(queue_pr, "HUB_PACING_DEPTH", 1):
            root, shas = self._seed_hub_repo(pathlib.Path(tmp))
            # `Hub.lean` rebuilds Hub, Mid, Leaf1, Leaf2 and Smoke; #11 already rebuilds only Leaf2.
            leaf_ahead = [(10, shas["queued"]), (11, shas["leaf_pr"])]
            rc, out, calls = self._run_main(root, shas["hub_pr"], shas["m0"], leaf_ahead)
            self.assertEqual((rc, calls), (1, 0), out)
            self.assertIn("#12 not queued: modifies high-fan-in hub module(s) "
                          "(`CslibFrontier/Hub.lean` (4 transitive importers)) and it adds 4 "
                          "modules to the 1 that the 2 entries ahead already rebuild; a hub PR "
                          "waits while more than 1 entries are ahead", out)
            self.assertIn("--allow-hub", out)

            rc, out, calls = self._run_main(root, shas["hub_pr"], shas["m0"], leaf_ahead,
                                            ["--allow-hub"])
            self.assertEqual((rc, calls), (0, 1), out)
            self.assertIn("Warning: #12 modifies high-fan-in hub module(s)", out)
            self.assertIn("(#10, #11); it adds 4 modules to the 1 that the 2 entries ahead", out)

            # #11 already rebuilds Mid's cone, so the hub PR adds only Hub itself: below threshold.
            mid_ahead = [(10, shas["queued"]), (11, shas["mid_pr"])]
            rc, out, calls = self._run_main(root, shas["hub_pr"], shas["m0"], mid_ahead)
            self.assertEqual((rc, calls), (0, 1), out)
            self.assertIn("it adds 1 module to the 4 that the 2 entries ahead already rebuild", out)

            # At most `HUB_PACING_DEPTH` entries ahead: advisory only.
            rc, out, calls = self._run_main(root, shas["hub_pr"], shas["m0"], leaf_ahead[1:])
            self.assertEqual((rc, calls), (0, 1), out)
            self.assertIn("it adds 4 modules to the 1 that the 1 entries ahead", out)

    def test_bare_repo_without_checkout_skips_advisory_but_fails_closed_for_hold_hubs(self) -> None:
        import queue_status

        with tempfile.TemporaryDirectory() as tmp, patch.dict(os.environ, self.GIT_ENV):
            base_dir = pathlib.Path(tmp)
            root, shas = self._seed_hub_repo(base_dir)
            bare = base_dir / "bare.git"
            scratch = base_dir / "scratch"
            scratch.mkdir()
            subprocess.run(["git", "clone", "-q", "--bare", str(root), str(bare)], check=True)

            notices: list[str] = []
            with patch.dict(os.environ, {"GIT_DIR": str(bare)}), \
                 patch.object(queue_status, "prefix", return_value=(shas["m0"], [(10, shas["queued"])])), \
                 patch.object(queue_status, "fetch_objects"):
                # Explicit `root=scratch` has no `CslibFrontier/` checkout: advisory skips cleanly.
                self.assertIsNone(
                    queue_pr.check_queue_prefix(
                        "o", "r", 12, shas["hub_pr"], root=scratch, on_hub_notice=notices.append,
                    )
                )
                self.assertEqual(notices, [])
                # Hub pacing that cannot check the PR still queues it, with a note saying so.
                with patch.object(queue_pr, "HUB_PACING_DEPTH", 0):
                    for allow_hub in (False, True):
                        notices = []
                        self.assertIsNone(queue_pr.check_queue_prefix(
                            "o", "r", 12, shas["hub_pr"], root=scratch,
                            on_hub_notice=notices.append, allow_hub=allow_hub))
                        if allow_hub:
                            self.assertEqual(notices, [])
                        else:
                            self.assertEqual(len(notices), 1, notices)
                            self.assertTrue(notices[0].startswith(
                                "Note: hub pacing needs a local `CslibFrontier/` checkout"),
                                notices)
                # `--hold-hubs` fails closed when `CslibFrontier/*.lean` changed and cannot be scanned.
                refusal = queue_pr.check_queue_prefix(
                    "o", "r", 12, shas["hub_pr"], root=scratch, hold_hubs=True,
                )
                self.assertIsNotNone(refusal)
                assert refusal is not None
                self.assertIn("--hold-hubs", refusal)

                # Stale checkout missing `Hub.lean` on disk while `base` has it also fails closed.
                (scratch / "CslibFrontier").mkdir()
                stale_refusal = queue_pr.check_queue_prefix(
                    "o", "r", 12, shas["hub_pr"], root=scratch, hold_hubs=True,
                )
                self.assertIsNotNone(stale_refusal)
                assert stale_refusal is not None
                self.assertIn("missing or symlinked locally", stale_refusal)

    def test_opaque_reverse_graph_compatibility_for_pr_7768(self) -> None:
        import check_hub_impact
        import queue_status

        class FakeReverseGraph:
            pass

        sentinel = FakeReverseGraph()
        with tempfile.TemporaryDirectory() as tmp, patch.dict(os.environ, self.GIT_ENV):
            root, shas = self._seed_hub_repo(pathlib.Path(tmp))
            seen: list[tuple[object, str]] = []

            def fake_rebuilt(graph: object, mod: str) -> set[str]:
                seen.append((graph, mod))
                return {f"CslibFrontier.Client{i}" for i in range(650)}

            notices: list[str] = []
            with patch.object(queue_status, "prefix", return_value=(shas["m0"], [(10, shas["queued"])])), \
                 patch.object(queue_status, "fetch_objects"), \
                 patch.object(check_hub_impact, "build_reverse_graph", return_value=(sentinel, 1000)), \
                 patch.object(check_hub_impact, "rebuilt_importers", side_effect=fake_rebuilt):
                rc_reason = queue_pr.check_queue_prefix(
                    "o", "r", 12, shas["hub_pr"], root=root, on_hub_notice=notices.append,
                )
            self.assertIsNone(rc_reason)
            self.assertEqual(seen, [(sentinel, "CslibFrontier.Hub")])
            self.assertEqual(len(notices), 1)
            self.assertIn("650 transitive importers", notices[0])


if __name__ == "__main__":
    unittest.main()
