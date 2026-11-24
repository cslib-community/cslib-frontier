"""Regression tests for the read-only merge-prefix replay and cache-hold signal."""

import contextlib
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import queue_status as qs
from test_queue_pr import SHA, check_run, pr

BASE = "b" * 40
OTHER = "c" * 40


def page(entries, *, total=None, cursor=None, base=BASE, head=SHA):
    return {"repository": {"ref": {"target": {"oid": base}},
                           "pullRequest": {"headRefOid": head, "state": "OPEN", "baseRefName": "main"},
                           "mergeQueue": {"entries": {
                               "totalCount": len(entries) if total is None else total,
                               "nodes": [{"position": i, "pullRequest": {"number": n, "headRefOid": h}}
                                         for i, n, h in entries],
                               "pageInfo": {"hasNextPage": cursor is not None, "endCursor": cursor}}}}}


class QueueStatusTests(unittest.TestCase):
    def test_prefix_ends_before_target_and_spans_pages(self):
        pages = [page([(1, 10, OTHER)], total=3, cursor="next"),
                 page([(2, 11, BASE), (3, 12, SHA)], total=3)]
        with mock.patch.object(qs.queue_pr, "gh_graphql", side_effect=pages) as api:
            self.assertEqual(qs.prefix("o", "r", 12, SHA), (BASE, [(10, OTHER), (11, BASE)]))
            self.assertEqual(api.call_args.kwargs["cursor"], "next")
            self.assertTrue(all(c.args[0].lstrip().startswith("query") for c in api.call_args_list))

    def test_moved_pr_or_inconsistent_listing_is_incomplete(self):
        for pages in ([page([], head=OTHER)], [page([(2, 11, OTHER)])],
                      [page([(1, 11, OTHER)], total=2, cursor="x"), page([], total=1)],
                      [page([(1, 11, OTHER)], total=2, cursor="x"), page([], total=2)]):
            with self.subTest(pages=pages), mock.patch.object(qs.queue_pr, "gh_graphql",
                                                               side_effect=pages):
                with self.assertRaises(ValueError):
                    qs.prefix("o", "r", 12, SHA)

    def test_replay_locates_conflict_in_prior_pr_and_preserves_refs(self):
        env = {"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1", "GIT_AUTHOR_NAME": "t",
               "GIT_AUTHOR_EMAIL": "t@example.test", "GIT_COMMITTER_NAME": "t",
               "GIT_COMMITTER_EMAIL": "t@example.test"}
        with tempfile.TemporaryDirectory() as tmp, mock.patch.dict(os.environ, env):
            root = Path(tmp)
            def git(*args):
                return subprocess.check_output(["git", *args], cwd=root, text=True).strip()
            def commit(path, content):
                (root / path).write_text(content)
                git("add", ".")
                git("commit", "-qm", path)
                return git("rev-parse", "HEAD")
            git("init", "-q", "-b", "main")
            (root / ".gitattributes").write_text("rows merge=union\n")
            base = commit("rows", "old\n")
            before = commit("other", "first PR\n")
            git("switch", "-q", "--detach", base)
            overlap = commit("rows", "second PR\n")
            git("switch", "-q", "--detach", base)
            candidate = commit("rows", "candidate\n")
            refs = git("show-ref")
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                self.assertEqual(qs.check_prefix(root, base, [(10, before)], candidate), 0)
                self.assertEqual(qs.check_prefix(root, base, [(10, before), (11, overlap)], candidate), 1)
                self.assertEqual(qs.check_prefix(root, base, [(11, overlap), (12, candidate)], before), 1)
            git("config", "merge.text.driver", "false")
            with self.assertRaisesRegex(qs.cr.GitError, "replace Git's built-in"):
                qs.check_prefix(root, base, [(11, overlap)], candidate)
            self.assertIn("'rows' first conflicts at #11", output.getvalue())
            self.assertIn("prefix itself conflicts at #12", output.getvalue())
            self.assertEqual((git("show-ref"), git("rev-parse", "HEAD"), git("status", "--porcelain")),
                             (refs, candidate, ""))

    def test_probe_requires_a_mapping_row_and_bounds_the_read(self):
        header = b'"2026-03-17"\n'
        row = b'["0000000000000001","deadbeefdeadbeef.ltar"]'
        for content, expected in ((header + row + b"\n", True), (header + row, False),
                                  (b'"future"\n' + row + b"\n", False), (header + b"{}\n", False),
                                  (header + b'["input","danger"]\n', False), (b"", False)):
            with self.subTest(content=content), mock.patch.object(qs, "urlopen") as open_url:
                response = open_url.return_value.__enter__.return_value
                response.status = 206
                response.geturl.return_value = "https://example.test/rev.jsonl"
                response.read.return_value = content
                self.assertEqual(qs.published("https://example.test/rev.jsonl"), expected)
                response.read.assert_called_once_with(1024)
                request = open_url.call_args.args[0]
                self.assertEqual(request.get_header("Range"), "bytes=0-1023")

    def test_pin_wait_uses_landed_toolchain_and_configured_mirrors(self):
        with mock.patch.dict(os.environ, {"COMPLEXITYLIB_CACHE_URLS": "https://a https://b"},
                             clear=True), mock.patch.object(qs.cr, "out", return_value="owner/tc:v1") as git, \
             mock.patch.object(qs, "published", side_effect=[OSError("offline"), False, True]) as probe, \
             mock.patch.object(qs, "compatible_main_pushes", return_value=[]), \
             mock.patch.object(qs.time, "sleep") as sleep, contextlib.redirect_stdout(io.StringIO()):
            self.assertTrue(qs.pin_ready(Path("."), qs.queue_pr.REPO, BASE, 2))
            git.assert_called_once_with(Path("."), "show", BASE + ":lean-toolchain")
            path = f"/r0/{qs.restore.SCOPE}/tc/owner--tc---v1/{BASE}.jsonl"
            self.assertEqual(probe.call_args_list, [mock.call(u + path) for u in
                                                    ("https://a", "https://b", "https://a")])
            sleep.assert_called_once_with(60)

    def test_coalesced_pin_only_accepts_a_first_parent_descendant_with_matching_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            def git(*args):
                return subprocess.check_output(["git", "-c", "user.name=t", "-c", "user.email=t@x",
                                                *args], cwd=root, text=True).strip()
            def commit(name, path):
                (root / path).write_text(name)
                git("add", ".")
                git("commit", "-qm", name)
                return git("rev-parse", "HEAD")
            git("init", "-q", "-b", "main")
            before = commit("initial", "lean-toolchain")
            pin = commit("landed", "lake-manifest.json")
            eligible = commit("doc", "readme")
            wrong = commit("changed", "lakefile.toml")
            git("switch", "-q", "--detach", before)
            commit("other", "extra")
            git("merge", "-q", "--no-ff", pin, "-m", "pin only via second parent")
            side = git("rev-parse", "HEAD")
            runs = {"workflow_runs": [{"head_sha": sha} for sha in (wrong, side, eligible, pin, before)]}
            with mock.patch.object(qs.cache_handoff, "gh_get", return_value=runs), \
                 mock.patch.object(qs, "fetch_objects"):
                self.assertEqual(list(qs.compatible_main_pushes(root, qs.queue_pr.REPO, pin)), [eligible])
            with mock.patch.dict(os.environ, {"COMPLEXITYLIB_CACHE_URL": "https://a"}, clear=True), \
                 mock.patch.object(qs, "compatible_main_pushes", return_value=[eligible]), \
                 mock.patch.object(qs, "published_origin", side_effect=[False, True]) as probe, \
                 contextlib.redirect_stdout(io.StringIO()):
                self.assertTrue(qs.pin_ready(root, qs.queue_pr.REPO, pin, 0))
                self.assertEqual([c.args[2] for c in probe.call_args_list], [pin, eligible])

    def test_cache_scope_rejects_an_unrelated_repo_before_probing(self):
        with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()), \
             mock.patch.object(qs, "fetch_objects") as fetch:
            qs.main(["--repo", "someone/fork", "cache-ready", BASE, "12@" + SHA])
        fetch.assert_not_called()

    def test_cache_signal_reports_moved_heads_only_after_publication(self):
        args = ["cache-ready", BASE, "12@" + SHA]
        for available in (False, True):
            with self.subTest(available=available), mock.patch.object(qs, "fetch_objects"), \
                 mock.patch.object(qs, "pin_ready", return_value=available), \
                 mock.patch.object(qs.queue_pr, "fetch_pr", return_value=pr(check_run(), headRefOid=OTHER)) as read, \
                 mock.patch.object(qs.queue_pr, "gh_graphql") as api, contextlib.redirect_stdout(io.StringIO()) as out:
                self.assertEqual(qs.main(args), 0 if available else 1)
                self.assertEqual(read.called, available)
                if available:
                    self.assertIn("refused (its head is " + OTHER, out.getvalue())
                api.assert_not_called()


if __name__ == "__main__":
    unittest.main()
