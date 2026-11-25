"""Tests for the maintenance reports' GitHub client and record parsers, without the network."""

from __future__ import annotations

from datetime import datetime, timedelta, timezone
import json
from pathlib import Path
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gh_records as gr  # noqa: E402

REPO = "o/r"
HEAD = "a" * 40
OLD = "b" * 40
T0 = datetime(2026, 11, 20, 12, 0, tzinfo=timezone.utc)


def stamp(hours: float = 0) -> str:
    return (T0 + timedelta(hours=hours)).strftime("%Y-%m-%dT%H:%M:%SZ")


def not_found(command) -> subprocess.CalledProcessError:
    return subprocess.CalledProcessError(1, command, stderr="gh: Not Found (HTTP 404)\n")


class Page:
    """A page of a listing that links to the next page's URL."""

    def __init__(self, records, after: str):
        self.records, self.after = records, after


class Seq:
    """Successive answers to the same route; the last one repeats."""

    def __init__(self, *values):
        self.values = list(values)

    def next(self):
        return self.values.pop(0) if len(self.values) > 1 else self.values[0]


class FakeRun:
    """Stands in for `subprocess.run` of `gh api`, answering from `routes`.

    A GET route is keyed by its endpoint or page URL, another method by `"METHOD endpoint"`, and
    GraphQL by `"graphql"`. A value may be JSON data, a `Page`, a callable of the request body, an
    exception, or a `Seq` of these.
    GETs are answered with headers, as `gh api --include` prints them. Unknown routes answer 404.
    """

    def __init__(self, routes: dict):
        self.routes = routes
        self.calls: list[tuple[str, str, str | None]] = []

    def __call__(self, command, **kwargs):
        assert command[:2] == ["gh", "api"], command
        args, method, endpoint, include = command[2:], "GET", None, False
        i = 0
        while i < len(args):
            if args[i] in ("-H", "--input", "-f"):
                i += 2
            elif args[i] == "--method":
                method, i = args[i + 1], i + 2
            elif args[i] == "--include":
                include, i = True, i + 1
            else:
                endpoint, i = args[i], i + 1
        body = kwargs.get("input")
        if endpoint == "graphql":
            method, body = "POST", " ".join(a for a in args if a.startswith(("query=", "id=")))
        self.calls.append((method, endpoint, body))
        key = endpoint if method == "GET" or endpoint == "graphql" else f"{method} {endpoint}"
        if key not in self.routes:
            raise not_found(command)
        value = self.routes[key]
        if isinstance(value, Seq):
            value = value.next()
        if isinstance(value, BaseException):
            raise value
        if callable(value):
            value = value(body)
        headers = "HTTP/2.0 200 OK\nX-Ratelimit-Remaining: 4321\r\n"
        if isinstance(value, Page):
            headers += f'Link: <{value.after}>; rel="next", <x>; rel="last"\r\n'
            value = value.records
        out = "" if value is None else json.dumps(value)
        return subprocess.CompletedProcess(command, 0, headers + "\r\n" + out if include else out,
                                           "")

    def writes(self) -> list[tuple[str, str, str | None]]:
        return [call for call in self.calls if call[0] != "GET"]


def fake_github(routes: dict, remaining: int = 5000) -> gr.GitHub:
    routes.setdefault("rate_limit", {"resources": {"core": {"remaining": remaining,
                                                            "reset": 1795584324}}})
    return gr.GitHub(REPO, run=FakeRun(routes), sleep=lambda seconds: None)


def post(body: str, hours: float = 0, *, seq: int = 0, kind: str = "comment", author: str = "x",
         state: str = "", commit: str = "") -> gr.Post:
    return gr.Post(T0 + timedelta(hours=hours), author, body, f"u{seq}", kind, seq, state, commit)


def thread(*bodies: str, start: float = 0) -> list[gr.Post]:
    """Comments one hour apart, after an empty PR body."""
    return [post("", start - 1, seq=0, kind="body")] + [
        post(body, start + i, seq=i + 1) for i, body in enumerate(bodies)]


class ClientTests(unittest.TestCase):
    def test_pagination_follows_next_links_one_call_per_page(self):
        after = "https://api.github.com/repositories/1/pulls?state=open&per_page=100&page=2"
        gh = fake_github({f"repos/{REPO}/pulls?state=open&per_page=100":
                          Page([{"number": 1}, {"number": 2}], after), after: [{"number": 3}]})
        self.assertEqual([p["number"] for p in gh.open_pulls()], [1, 2, 3])
        self.assertEqual((gh.calls, gh.remaining_seen), (2, 4321))

    def test_object_pages_name_their_list(self):
        gh = fake_github({"runs": {"total_count": 1, "check_runs": [{"id": 5}]}})
        self.assertEqual(gh.get_all("runs", "check_runs"), [{"id": 5}])

    def test_rate_limit_backs_off_and_retries(self):
        limited = subprocess.CalledProcessError(
            1, "gh", stderr="gh: API rate limit exceeded for user ID 1. (HTTP 403)")
        sleeps = []
        run = FakeRun({"repos/o/r": Seq(limited, {"ok": True})})
        gh = gr.GitHub(REPO, run=run, sleep=sleeps.append, backoff=30)
        self.assertEqual(gh.get("repos/o/r"), {"ok": True})
        self.assertEqual((sleeps, gh.calls), ([30], 2))

    def test_errors_carry_the_http_status_and_do_not_retry(self):
        gh = fake_github({})
        with self.assertRaises(gr.GitHubError) as caught:
            gh.get("repos/o/r/git/ref/heads/x")
        self.assertEqual((caught.exception.status, gh.calls), (404, 1))

    def test_budget_floor_refuses_before_scanning(self):
        with self.assertRaisesRegex(gr.GitHubError, "12 REST calls left"):
            fake_github({}, remaining=12).require_budget(500)
        gh = fake_github({}, remaining=900)
        gh.require_budget(500)
        self.assertEqual(gh.calls, 0)

    def test_write_sends_a_json_body(self):
        run = FakeRun({f"POST repos/{REPO}/issues/3/comments": lambda body: {"id": 9}})
        gh = gr.GitHub(REPO, run=run, sleep=lambda s: None)
        self.assertEqual(gh.write("POST", f"repos/{REPO}/issues/3/comments", {"body": "hi"}),
                         {"id": 9})
        self.assertEqual(json.loads(run.writes()[0][2]), {"body": "hi"})

    def test_ref_paths_quote_branch_names(self):
        self.assertEqual(gr.GitHub(REPO).ref_path("feat/a#b"),
                         "repos/o/r/git/refs/heads/feat/a%23b")


class TimelineTests(unittest.TestCase):
    def test_posts_orders_body_comments_and_submitted_reviews(self):
        pr = {"created_at": stamp(0), "user": {"login": "author"}, "body": "B", "html_url": "pr"}
        events = [
            {"event": "reviewed", "submitted_at": stamp(2), "state": "approved",
             "commit_id": HEAD, "body": "R", "user": {"login": "rev"}, "html_url": "r"},
            {"event": "commented", "created_at": stamp(1), "body": "C",
             "user": {"login": "c"}, "html_url": "c"},
            {"event": "reviewed", "submitted_at": None, "state": "pending", "body": "P"},
            {"event": "committed", "sha": HEAD},
        ]
        found = gr.posts(pr, events)
        self.assertEqual([(p.kind, p.body, p.seq) for p in found],
                         [("body", "B", 0), ("comment", "C", 1), ("review", "R", 2)])
        self.assertEqual((found[2].state, found[2].commit), ("approved", HEAD))

    def test_queue_state_follows_the_last_queue_event(self):
        added = {"event": "added_to_merge_queue"}
        removed = {"event": "removed_from_merge_queue"}
        self.assertTrue(gr.queued([removed, added]))
        self.assertFalse(gr.queued([added, removed]))
        self.assertFalse(gr.queued([]))

    def test_base_changes(self):
        events = [{"event": "automatic_base_change_succeeded", "created_at": stamp(1)},
                  {"event": "base_ref_changed", "created_at": stamp(2)},
                  {"event": "commented", "created_at": stamp(3)}]
        self.assertEqual(gr.base_changes(events), [T0 + timedelta(hours=1),
                                                   T0 + timedelta(hours=2)])


class VerdictTests(unittest.TestCase):
    def test_verdict_line_must_open_the_post(self):
        found = gr.verdict_of(post(f"\n  **APPROVE** at `{HEAD}` by `rev-1` (agent review)"))
        self.assertEqual((found.decision, found.sha, found.reviewer, found.formal),
                         ("APPROVE", HEAD, "rev-1", False))
        punct = gr.verdict_of(post(f"**APPROVE** at {HEAD} by reviewer-425b-8488. Agent review."))
        self.assertEqual(punct.reviewer, "reviewer-425b-8488")
        paren = gr.verdict_of(post(f"**APPROVE** at `{HEAD}` by `rev-b`), independent review"))
        self.assertEqual(paren.reviewer, "rev-b")
        no_by = gr.verdict_of(post(f"**APPROVE** at {HEAD} (agent review; covered by tests)"))
        self.assertEqual(no_by.reviewer, "")
        self.assertIsNone(gr.verdict_of(post(f"`me` (agent)\n**APPROVE** at {HEAD}")))
        self.assertIsNone(gr.verdict_of(post(f"**APPROVE (queueing held)** at head `{HEAD}`")))
        self.assertIsNone(gr.verdict_of(post(f"**approve** at {HEAD}")))
        self.assertEqual(gr.verdict_of(post("**REQUEST_CHANGES** at 1234567: split")).sha,
                         "1234567")

    def test_review_state_counts_without_a_verdict_line(self):
        review = post("Looks right.", kind="review", state="approved", commit=HEAD, author="rev")
        self.assertEqual(gr.verdict_of(review), gr.Verdict("APPROVE", HEAD, review, True, "rev"))
        self.assertIsNone(gr.verdict_of(post("x", kind="review", state="commented", commit=HEAD)))
        dismissed = post(f"**APPROVE** at {HEAD}", kind="review", state="dismissed", commit=HEAD)
        self.assertIsNone(gr.verdict_of(dismissed))

    def test_a_later_request_for_changes_cancels_the_approval(self):
        approve, request = f"**APPROVE** at {HEAD}", f"**REQUEST_CHANGES** at {HEAD}"
        self.assertEqual(gr.current_approval(thread(approve)).sha, HEAD)
        self.assertIsNone(gr.current_approval(thread(approve, request)))
        self.assertEqual(gr.current_approval(thread(request, approve)).post.seq, 2)

    def test_sha_prefixes(self):
        self.assertTrue(gr.sha_matches(HEAD[:7], HEAD))
        self.assertFalse(gr.sha_matches(HEAD[:6], HEAD))
        self.assertFalse(gr.sha_matches(OLD[:12], HEAD))


class HoldTests(unittest.TestCase):
    def test_line_format_tolerates_indentation_and_bold(self):
        items = thread("Hold for review.\n  **HOLD owner=rev-1 until=2026-11-21T00:00Z "
                       "reason=waiting for #12**\nhold owner=x until=2026-11-21T00:00Z reason=y")
        [hold] = gr.holds(items)
        self.assertEqual((hold.owner, hold.until, hold.reason),
                         ("rev-1", datetime(2026, 11, 21, tzinfo=timezone.utc), "waiting for #12"))
        self.assertEqual(hold.state(T0), "active")
        self.assertEqual(hold.state(T0 + timedelta(days=2)), "expired")

    def test_release_by_owner_maintainer_alias_and_expiry_sweep(self):
        hold = "HOLD owner={} until=2026-11-20T15:00Z reason=r"
        released = gr.holds(thread(hold.format("rev-1"), "HOLD-RELEASED by=rev-1 reason=done"))
        self.assertEqual(released[0].state(T0), "released")
        wrong_case = gr.holds(thread(hold.format("rev-1"), "HOLD-RELEASED by=Rev-1 reason=done"))
        self.assertEqual((wrong_case[0].state(T0), wrong_case[0].other_releases),
                         ("active", ["Rev-1"]))
        alias = gr.holds(thread(hold.format("maintainer"),
                                "HOLD-RELEASED by=SamuelSchlesinger reason=ok"))
        self.assertEqual(alias[0].state(T0), "released")
        alias_case = gr.holds(thread(hold.format("maintainer"),
                                     "HOLD-RELEASED by=samuelschlesinger reason=ok"))
        self.assertEqual((alias_case[0].state(T0), alias_case[0].other_releases),
                         ("active", ["samuelschlesinger"]))
        # Posted at 13:00, before the hold expires at 15:00: not a valid sweep.
        early = gr.holds(thread(hold.format("rev-1"), "HOLD-RELEASED by=coord reason=expired"))
        self.assertEqual((early[0].state(T0), early[0].other_releases), ("active", ["coord"]))
        swept = gr.holds(thread(hold.format("rev-1"), "HOLD-RELEASED by=coord reason=expired",
                                start=4))
        self.assertEqual(swept[0].state(T0 + timedelta(days=1)), "released")

    def test_release_before_the_hold_does_not_count(self):
        items = thread("HOLD-RELEASED by=rev-1 reason=done",
                       "HOLD owner=rev-1 until=2026-11-30T00:00Z reason=r")
        self.assertEqual(gr.holds(items)[0].state(T0), "active")

    def test_fenced_code_blocks_and_invalid_dates_are_ignored(self):
        items = thread("```\nHOLD owner=rev-1 until=2026-11-30T00:00Z reason=example\n```\n"
                       "~~~text\nHOLD owner=rev-2 until=2026-11-30T00:00Z reason=example\n~~~\n"
                       "HOLD owner=rev-3 until=2026-99-99T00:00Z reason=bad date")
        self.assertEqual(gr.holds(items), [])


class ClaimTests(unittest.TestCase):
    def claim(self, by="rev-1", until="2026-11-20T13:30Z", head=HEAD):
        return f"CLAIM review head={head} by={by} until={until}"

    def test_only_the_claimants_verdict_at_the_claimed_head_ends_the_claim(self):
        [open_claim] = gr.claims(thread(self.claim()))
        self.assertIsNone(open_claim.ended_by)
        [ended] = gr.claims(thread(self.claim(), f"**APPROVE** at `{HEAD[:12]}` by `rev-1`."))
        self.assertIsNotNone(ended.ended_by)
        [in_body] = gr.claims(thread(self.claim(), f"**APPROVE** at {HEAD}\n`rev-1` (agent)"))
        self.assertIsNotNone(in_body.ended_by)
        [wrong_head] = gr.claims(thread(self.claim(), f"**APPROVE** at {OLD} by `rev-1`."))
        self.assertIsNone(wrong_head.ended_by)
        [other_at_head] = gr.claims(thread(self.claim(),
                                           f"**REQUEST_CHANGES** at {HEAD} by `other`"))
        self.assertIsNone(other_at_head.ended_by)
        both_heads = gr.claims(thread(self.claim(head=HEAD), self.claim(head=OLD)))
        self.assertEqual([(c.by, c.head) for c in both_heads], [("rev-1", HEAD), ("rev-1", OLD)])
        self.assertEqual(gr.claims(thread(f"```\n{self.claim()}\n```")), [])

    def test_renewal_replaces_the_claim_and_long_leases_are_capped_and_flagged(self):
        claims = gr.claims(thread(self.claim(until="2026-11-20T13:30Z"),
                                  f"**{self.claim(until='2026-11-20T16:00Z')}**",
                                  self.claim(by="rev-2")))
        self.assertEqual([(c.by, c.post.seq) for c in claims], [("rev-1", 2), ("rev-2", 3)])
        self.assertTrue(claims[0].lease_too_long)
        self.assertEqual(claims[0].expires, T0 + timedelta(hours=1, minutes=45))
        self.assertFalse(claims[1].lease_too_long)


class FreeTextHoldTests(unittest.TestCase):
    def test_strong_wording_anywhere_weak_wording_only_from_the_approval(self):
        items = thread("Please do not queue until #5 lands.", "Hold 2: CI pending.",
                       f"**APPROVE** at {HEAD} (held until #7 lands)")
        found = gr.free_text_holds(items, items[3])
        self.assertEqual([(p.seq, text) for p, text in found],
                         [(1, "Please do not queue until #5 lands."),
                          (3, f"**APPROVE** at {HEAD} (held until #7 lands)")])

    def test_formatted_lines_convert_earlier_free_text(self):
        items = thread("HOLD: waiting for Samuel", "HOLD-RELEASED by=maintainer reason=ok",
                       f"**APPROVE** at {HEAD}")
        self.assertEqual(gr.free_text_holds(items, items[3]), [])
        unrelated = thread("Hold for human review.",
                           "HOLD owner=x until=2026-11-30T00:00Z reason=wait for #9",
                           "HOLD-RELEASED by=x reason=#9 landed",
                           f"**APPROVE** at {HEAD}")
        self.assertEqual([p.seq for p, _ in gr.free_text_holds(unrelated, unrelated[4])], [1])
        malformed = thread("Hold for human review please.",
                           "HOLD owner=maintainer until=2026-12-01 reason=human review",
                           f"**APPROVE** at {HEAD}")
        self.assertEqual([p.seq for p, _ in gr.free_text_holds(malformed, malformed[3])], [1, 2])
        fenced = thread("Do not queue: waiting on #77.", f"**APPROVE** at {HEAD}",
                        "Example:\n```\nHOLD owner=<id> until=<YYYY-MM-DDTHH:MMZ> reason=x\n```")
        self.assertEqual([p.seq for p, _ in gr.free_text_holds(fenced, fenced[2])], [1])

    def test_mathematical_prose_is_not_a_hold(self):
        items = [post("The bound holds for all n; units ever held.", seq=0, kind="body")] + [
            post(f"**APPROVE** at {HEAD}\nThe invariant holds for every step.", seq=1)]
        self.assertEqual(gr.free_text_holds(items, items[1]), [])

    def test_lowercase_hold_word_is_weak(self):
        items = thread("hold on, checking", f"**APPROVE** at {HEAD}")
        self.assertEqual(gr.free_text_holds(items, items[2]), [])
        self.assertEqual(len(gr.free_text_holds(items, items[1])), 1)

    def test_human_review_requests_bind_and_a_review_claim_does_not_release_them(self):
        body = post("**Hold for human review.**", -1, seq=0, kind="body")
        items = [body, post(f"**APPROVE** at {HEAD} (agent review, not human review)", seq=1),
                 post(f"CLAIM review head={HEAD} by=rev until=2026-11-20T12:40Z", 1, seq=2)]
        self.assertEqual([p.seq for p, _ in gr.free_text_holds(items, items[1])], [0])
        self.assertEqual(gr.free_text_holds(items[1:], items[1]), [])
        for text in ("Human review requested before merge.", "This needs a human review.",
                     "Waiting for human review."):
            with self.subTest(text=text):
                self.assertEqual(len(gr.free_text_holds(thread(text), None)), 1)

    def test_a_sequencing_note_after_the_approval_is_a_possible_hold(self):
        note = "The queue now has #8474 ahead. I'll verify the resulting delta before queueing."
        items = thread("Restacked; please queue when ready.", f"**APPROVE** at {HEAD}", note)
        self.assertEqual([p.seq for p, _ in gr.free_text_holds(items, items[2])], [3])
        bot = items[:3] + [post("Merge queue notice.", 4, seq=3, author="github-actions[bot]")]
        self.assertEqual(gr.free_text_holds(bot, bot[2]), [])


class HelperTests(unittest.TestCase):
    def test_ages(self):
        self.assertEqual(gr.parse_age("14d"), timedelta(days=14))
        self.assertEqual(gr.parse_age("48h"), timedelta(hours=48))
        with self.assertRaises(ValueError):
            gr.parse_age("2w")
        self.assertEqual(gr.fmt_age(T0 + timedelta(hours=50), T0), "2d")
        self.assertEqual(gr.fmt_age(T0 + timedelta(minutes=30), T0), "30m")

    def test_parallel_keeps_order(self):
        self.assertEqual(gr.parallel(lambda n: n * n, range(6), 3), [0, 1, 4, 9, 16, 25])


if __name__ == "__main__":
    unittest.main()
