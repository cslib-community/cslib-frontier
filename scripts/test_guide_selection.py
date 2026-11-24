"""Exercise Guide selection against real independent shallow Git checkouts.

Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
"""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SELECTOR = ROOT / "scripts/ci/select_guide.py"
sys.path.insert(0, str(ROOT / "scripts/ci"))
import select_guide  # noqa: E402


def parse_outputs(text: str) -> dict[str, str]:
    pairs: dict[str, str] = {}
    for line in text.splitlines():
        if "=" in line:
            key, value = line.split("=", 1)
            pairs[key] = value
    return pairs


class GuideSelectionTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="guide-selector-test-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.env = dict(os.environ)
        for name in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE",
                     "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES"):
            self.env.pop(name, None)
        self.env.update({
            "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_TERMINAL_PROMPT": "0", "GIT_ALLOW_PROTOCOL": "file",
            "GIT_CONFIG_COUNT": "2", "GIT_CONFIG_KEY_0": "gc.auto",
            "GIT_CONFIG_VALUE_0": "0", "GIT_CONFIG_KEY_1": "maintenance.auto",
            "GIT_CONFIG_VALUE_1": "false",
        })

    def git(self, repo, *args, check=True):
        return subprocess.run(
            ["git", "-c", "gc.auto=0", "-c", "maintenance.auto=false",
             "-c", "user.name=Guide selector test",
             "-c", "user.email=guide-selector@example.invalid", "-C", str(repo), *args],
            env=self.env, text=True, capture_output=True, check=check)

    def make_repo(self, base_files: dict[str, str], head_writes: dict[str, str] | None = None,
                  deletes: tuple[str, ...] = (), depth: int = 1, name: str = "default"):
        """Create an independent two-commit origin and shallow checkout."""
        box = self.root / name
        writer = box / "writer"
        writer.mkdir(parents=True)
        self.git(writer, "init", "-q", "--initial-branch=main")
        for rel, content in base_files.items():
            target = writer / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content, encoding="utf-8")
        self.git(writer, "add", ".")
        self.git(writer, "commit", "-qm", "base")
        base = self.git(writer, "rev-parse", "HEAD").stdout.strip()
        for rel, content in (head_writes or {}).items():
            target = writer / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content, encoding="utf-8")
        for rel in deletes:
            (writer / rel).unlink()
        self.git(writer, "add", "-A")
        self.git(writer, "commit", "-qm", "head", "--allow-empty")
        head = self.git(writer, "rev-parse", "HEAD").stdout.strip()
        origin = box / "origin.git"
        origin.mkdir()
        self.git(origin, "init", "--bare", "-q")
        self.git(writer, "push", "-q", origin.as_uri(), "main")
        checkout = box / "checkout"
        checkout.mkdir()
        self.git(checkout, "init", "-q")
        self.git(checkout, "remote", "add", "origin", origin.as_uri())
        self.git(checkout, "fetch", "-q", f"--depth={depth}", "origin", "main")
        self.git(checkout, "checkout", "-q", "--detach", "FETCH_HEAD")
        common = Path(self.git(checkout, "rev-parse", "--path-format=absolute",
                               "--git-common-dir").stdout.strip())
        self.assertEqual(common, checkout / ".git")
        self.assertFalse((common / "objects/info/alternates").exists())
        return checkout, base, head

    def base_tree(self) -> dict[str, str]:
        return {
            "README.md": "base\n",
            "CslibFrontier.lean": (
                "public import CslibFrontier.Core\n"
                "public import CslibFrontier.Direct\n"
                "public import CslibFrontier.Unrelated\n"
            ),
            "CslibFrontier/Core.lean": "module -- shake: keep-all\ndef core := 1\n",
            "CslibFrontier/Direct.lean": (
                "module\npublic import\n  CslibFrontier.Core\ndef direct := core\n"
            ),
            "CslibFrontier/Unrelated.lean": "module\ndef leaf := 1\n",
            "guide/CslibFrontierGuide.lean": (
                "import CslibFrontier.Direct\n"
            ),
        }

    def run_selector(self, checkout: Path, base: str, event: str = "pull_request"):
        output = checkout.parent / "github-output"
        if output.exists():
            output.unlink()
        env = {**self.env, "GITHUB_EVENT_NAME": event,
               "GUIDE_BASE_SHA": base, "GITHUB_OUTPUT": str(output)}
        result = subprocess.run([sys.executable, "-B", str(SELECTOR)], cwd=checkout,
                                env=env, text=True, capture_output=True, check=False)
        return result, output.read_text() if output.exists() else ""

    def test_workflow_invokes_select_guide_script(self):
        workflow = (ROOT / ".github/workflows/guide.yml").read_text(encoding="utf-8")
        self.assertIn("run: python3 -B scripts/ci/select_guide.py", workflow)
        self.assertIn('"scripts/ci/select_guide.py"', workflow)
        self.assertIn("steps.changes.outputs.check == 'true'", workflow)
        self.assertIn("steps.changes.outputs.render == 'true'", workflow)

    def test_unimported_leaf_and_added_module_skip_check_and_render(self):
        checkout, base, head = self.make_repo(
            self.base_tree(),
            head_writes={
                "CslibFrontier/Unrelated.lean": "module\ndef leaf := 2\n",
                "CslibFrontier/BrandNew.lean": "module\ndef added := 1\n",
                "CslibFrontier.lean": (
                    "public import CslibFrontier.BrandNew\n"
                    "public import CslibFrontier.Core\n"
                    "public import CslibFrontier.Direct\n"
                    "public import CslibFrontier.Unrelated\n"
                ),
                "CslibFrontierTests/Test.lean": "module\n",
                "ROADMAP.md": "updated\n",
            },
        )
        self.assertNotEqual(self.git(checkout, "cat-file", "-e", base + "^{commit}",
                                     check=False).returncode, 0)
        result, output = self.run_selector(checkout, base)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(parse_outputs(output), {"check": "false", "render": "false"})
        self.assertEqual(self.git(checkout, "rev-parse", "HEAD").stdout.strip(), head)
        self.assertEqual(self.git(checkout, "rev-list", "--count", "HEAD").stdout.strip(), "1")

    def test_direct_and_transitive_guide_imports_check_without_rendering(self):
        for rel, body in (
            ("CslibFrontier/Direct.lean", "module\npublic import CslibFrontier.Core\ndef direct := 2\n"),
            ("CslibFrontier/Core.lean", "module -- shake: keep-all\ndef core := 2\n"),
        ):
            with self.subTest(rel=rel):
                checkout, base, _ = self.make_repo(
                    self.base_tree(), head_writes={rel: body}, name=rel.replace("/", "_"),
                )
                result, output = self.run_selector(checkout, base)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(parse_outputs(output), {"check": "true", "render": "false"})

    def test_arbitrary_root_aggregate_edit_or_deletion_fails_closed(self):
        checkout, base, _ = self.make_repo(
            self.base_tree(),
            head_writes={"CslibFrontier.lean": "public import CslibFrontier.Direct\n"},
            name="agg",
        )
        result, output = self.run_selector(checkout, base)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(parse_outputs(output), {"check": "true", "render": "false"})

        checkout2, base2, _ = self.make_repo(
            self.base_tree(),
            deletes=("CslibFrontier/Unrelated.lean",),
            name="del",
        )
        result2, output2 = self.run_selector(checkout2, base2)
        self.assertEqual(result2.returncode, 0, result2.stderr)
        self.assertEqual(parse_outputs(output2), {"check": "true", "render": "false"})

    def test_guide_and_tooling_changes_render(self):
        for rel in (
            "guide/Chapter.lean",
            "scripts/check_docs.py",
            "scripts/ci/select_guide.py",
            "lakefile.toml",
            "lake-manifest.json",
            "lean-toolchain",
            ".github/actions/cache-guide-deps/key.py",
            ".github/workflows/guide.yml",
        ):
            with self.subTest(rel=rel):
                checkout, base, _ = self.make_repo(
                    self.base_tree(), head_writes={rel: "changed\n"},
                    name="render_" + rel.replace("/", "_").replace(".", "_"),
                )
                result, output = self.run_selector(checkout, base)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(parse_outputs(output), {"check": "true", "render": "true"})

    def test_absent_guide_directory_fails_closed_for_check_only(self):
        checkout, base, _ = self.make_repo(
            {"README.md": "base\n"},
            head_writes={"CslibFrontier/Example.lean": "changed\n"},
            name="noguide",
        )
        result, output = self.run_selector(checkout, base)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(parse_outputs(output), {"check": "true", "render": "false"})

    def test_present_base_needs_no_remote(self):
        checkout, base, head = self.make_repo(
            self.base_tree(),
            head_writes={"CslibFrontier/Unrelated.lean": "module\ndef leaf := 9\n"},
            depth=2,
            name="present",
        )
        self.git(checkout, "remote", "remove", "origin")
        result, output = self.run_selector(checkout, base)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(parse_outputs(output), {"check": "false", "render": "false"})
        self.assertEqual(self.git(checkout, "rev-parse", "HEAD").stdout.strip(), head)

    def test_unavailable_base_fails_without_selecting_a_mode(self):
        checkout, base, head = self.make_repo(
            self.base_tree(), head_writes={"guide/Chapter.lean": "changed\n"}, name="missing",
        )
        empty = self.root / "unavailable.git"
        empty.mkdir()
        self.git(empty, "init", "--bare", "-q")
        self.git(checkout, "remote", "set-url", "origin", empty.as_uri())
        result, output = self.run_selector(checkout, base)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(output, "")
        self.assertEqual(self.git(checkout, "rev-parse", "HEAD").stdout.strip(), head)

    def test_manual_run_renders_without_base_or_remote(self):
        checkout, _, head = self.make_repo(
            self.base_tree(),
            head_writes={"CslibFrontier/Unrelated.lean": "module\ndef leaf := 9\n"},
            name="manual",
        )
        self.git(checkout, "remote", "remove", "origin")
        result, output = self.run_selector(checkout, "", event="workflow_dispatch")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(parse_outputs(output), {"check": "true", "render": "true"})
        self.assertEqual(self.git(checkout, "rev-parse", "HEAD").stdout.strip(), head)

    def test_ambiguous_headers_and_root_import_fail_closed(self):
        bad_tree = {
            **self.base_tree(),
            "guide/CslibFrontierGuide.lean": "import CslibFrontier\n",
        }
        checkout, base, _ = self.make_repo(
            bad_tree,
            head_writes={"CslibFrontier/Unrelated.lean": "module\ndef leaf := 3\n"},
            name="root_imp",
        )
        result, output = self.run_selector(checkout, base)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(parse_outputs(output), {"check": "true", "render": "false"})

        for bad_header in (
            "import «unterminated\n",
            "import «»\n",
            "import CslibFrontier.«Dot.Inside»\n",
            "import CslibFrontier.«Slash/Inside»\n",
            "import CslibFrontier.Example$extra\n",
            "import CslibFrontier.Example-bar\n",
            "import CslibFrontier.Example.\n",
            "import CslibFrontier..Core\n",
            "import CslibFrontier . Core\nimport CslibFrontier.Leaf\n",
            "import CslibFrontier.Example«extra»\n",
            "import«CslibFrontier»\n",
            "scoped import CslibFrontier.Core\n",
            "public public import CslibFrontier.Core\n",
            "meta meta import CslibFrontier.Core\n",
            "public scoped import CslibFrontier.Core\n",
            "prelude\nmodule\nimport CslibFrontier.Core\n",
            "/- unterminated comment\nimport CslibFrontier.Core\n",
            "meta public import CslibFrontier.Core\n",
        ):
            with self.subTest(bad_header=bad_header):
                with self.assertRaises(select_guide.AmbiguousHeader):
                    select_guide.parse_header_imports_text(bad_header)

    def test_parse_header_details_modifiers_comments_and_module_flag(self):
        header = (
            "/- outer /- nested -/ header comment -/\n"
            "module -- inline comment\n"
            "prelude\n"
            "import A.Plain\n"
            "public\n  import\n  B.Pub\n"
            "private import C.Priv\n"
            "meta /- mid -/ import D.Meta\n"
            "public meta import E.PubMeta\n"
            "private meta import F.PrivMeta\n"
            "import -- between import and all\n  all G.All\n"
            "public import all H.PubAll\n"
            "meta import all I.MetaAll\n"
            "public meta import all J.PubMetaAll\n"
            "/-! Module docstring terminates header scanning:\n"
            "public import ShouldNotParse\n"
            "-/\n"
            "public section\n"
        )
        has_module, details = select_guide.parse_header_details_text(header)
        self.assertTrue(has_module)
        self.assertEqual(
            details,
            [
                select_guide.HeaderImport("A.Plain", is_public=False, is_meta=False, is_all=False),
                select_guide.HeaderImport("B.Pub", is_public=True, is_meta=False, is_all=False),
                select_guide.HeaderImport("C.Priv", is_public=False, is_meta=False, is_all=False),
                select_guide.HeaderImport("D.Meta", is_public=False, is_meta=True, is_all=False),
                select_guide.HeaderImport("E.PubMeta", is_public=True, is_meta=True, is_all=False),
                select_guide.HeaderImport("F.PrivMeta", is_public=False, is_meta=True, is_all=False),
                select_guide.HeaderImport("G.All", is_public=False, is_meta=False, is_all=True),
                select_guide.HeaderImport("H.PubAll", is_public=True, is_meta=False, is_all=True),
                select_guide.HeaderImport("I.MetaAll", is_public=False, is_meta=True, is_all=True),
                select_guide.HeaderImport("J.PubMetaAll", is_public=True, is_meta=True, is_all=True),
            ],
        )
        self.assertEqual(
            select_guide.parse_header_imports_text(header),
            [imp.module for imp in details],
        )

        legacy_has_module, legacy_details = select_guide.parse_header_details_text(
            "-- classic file without `module`\n"
            "import CslibFrontier.Core\n"
            "public meta def bodyDecl := 1\n"
        )
        self.assertFalse(legacy_has_module)
        self.assertEqual(
            legacy_details,
            [select_guide.HeaderImport("CslibFrontier.Core", False, False, False)],
        )

    def test_primed_module_with_unprimed_sibling_tracks_transitive_leaf(self):
        tree = {
            "README.md": "base\n",
            "CslibFrontier.lean": (
                "public import CslibFrontier.Example\n"
                "public import CslibFrontier.Example'\n"
                "public import CslibFrontier.Leaf\n"
            ),
            "CslibFrontier/Leaf.lean": "module\ndef leaf := 1\n",
            "CslibFrontier/Example.lean": "module\ndef plain := 1\n",
            "CslibFrontier/Example'.lean": (
                "module\npublic import CslibFrontier.Leaf\ndef primed := leaf\n"
            ),
            "guide/CslibFrontierGuide.lean": "import CslibFrontier.Example'\n",
        }
        checkout_leaf, base_leaf, _ = self.make_repo(
            tree,
            head_writes={"CslibFrontier/Leaf.lean": "module\ndef leaf := 2\n"},
            name="primed_leaf",
        )
        self.assertEqual(
            select_guide.guide_import_closure(checkout_leaf),
            {"CslibFrontier.Example'", "CslibFrontier.Leaf"},
        )
        res_leaf, out_leaf = self.run_selector(checkout_leaf, base_leaf)
        self.assertEqual(res_leaf.returncode, 0, res_leaf.stderr)
        self.assertEqual(parse_outputs(out_leaf), {"check": "true", "render": "false"})

        checkout_primed, base_primed, _ = self.make_repo(
            tree,
            head_writes={
                "CslibFrontier/Example'.lean": (
                    "module\npublic import CslibFrontier.Leaf\ndef primed := leaf + 1\n"
                ),
            },
            name="primed_direct",
        )
        res_primed, out_primed = self.run_selector(checkout_primed, base_primed)
        self.assertEqual(res_primed.returncode, 0, res_primed.stderr)
        self.assertEqual(parse_outputs(out_primed), {"check": "true", "render": "false"})

        checkout_plain, base_plain, _ = self.make_repo(
            tree,
            head_writes={"CslibFrontier/Example.lean": "module\ndef plain := 2\n"},
            name="unprimed_sibling",
        )
        res_plain, out_plain = self.run_selector(checkout_plain, base_plain)
        self.assertEqual(res_plain.returncode, 0, res_plain.stderr)
        self.assertEqual(parse_outputs(out_plain), {"check": "false", "render": "false"})

    def test_guillemet_unicode_identifiers_and_unsupported_continuation_fail_closed(self):
        self.assertEqual(
            select_guide.parse_header_imports_text(
                "module\n"
                "public import «Quoted»\n"
                "import «CslibFrontier».«Example'»\n"
                "meta import CslibFrontier.«My-Mod»\n"
                "import all CslibFrontier.α₁_β?!'\n"
                "public section\n"
            ),
            [
                "Quoted",
                "CslibFrontier.Example'",
                "CslibFrontier.My-Mod",
                "CslibFrontier.α₁_β?!'",
            ],
        )
        # Transitive closure through a guillemet-escaped module with an unescaped prefix sibling.
        quoted_tree = {
            **self.base_tree(),
            "CslibFrontier/Leaf.lean": "module\ndef leaf := 1\n",
            "CslibFrontier/My.lean": "module\ndef plain := 1\n",
            "CslibFrontier/My-Mod.lean": "module\npublic import CslibFrontier.Leaf\n",
            "guide/CslibFrontierGuide.lean": "import CslibFrontier.«My-Mod»\n",
        }
        checkout_q, base_q, _ = self.make_repo(
            quoted_tree,
            head_writes={"CslibFrontier/Leaf.lean": "module\ndef leaf := 2\n"},
            name="quoted_trans",
        )
        res_q, out_q = self.run_selector(checkout_q, base_q)
        self.assertEqual(res_q.returncode, 0, res_q.stderr)
        self.assertEqual(parse_outputs(out_q), {"check": "true", "render": "false"})

        # Unsupported continuation after an ASCII prefix retains the Guide compile (`check=true`).
        cont_tree = {
            **self.base_tree(),
            "CslibFrontier/Example.lean": "module\ndef plain := 1\n",
            "guide/CslibFrontierGuide.lean": "import CslibFrontier.Example$extra\n",
        }
        checkout_c, base_c, _ = self.make_repo(
            cont_tree,
            head_writes={"CslibFrontier/Unrelated.lean": "module\ndef leaf := 2\n"},
            name="unsupported_cont",
        )
        res_c, out_c = self.run_selector(checkout_c, base_c)
        self.assertEqual(res_c.returncode, 0, res_c.stderr)
        self.assertEqual(parse_outputs(out_c), {"check": "true", "render": "false"})

    def test_merge_commit_uses_first_parent_instead_of_stale_base(self):
        box = self.root / "merge"
        writer = box / "writer"
        writer.mkdir(parents=True)
        self.git(writer, "init", "-q", "--initial-branch=main")
        for rel, content in self.base_tree().items():
            p = writer / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(content, encoding="utf-8")
        self.git(writer, "add", ".")
        self.git(writer, "commit", "-qm", "old-main")
        stale_base = self.git(writer, "rev-parse", "HEAD").stdout.strip()
        self.git(writer, "checkout", "-qb", "pr")
        (writer / "CslibFrontier/Unrelated.lean").write_text("module\ndef leaf := 42\n")
        self.git(writer, "add", ".")
        self.git(writer, "commit", "-qm", "pr-change")
        # Meanwhile `main` moved forward touching `guide/`.
        self.git(writer, "checkout", "-q", "main")
        (writer / "guide/New.lean").write_text("-- main updated guide\n")
        self.git(writer, "add", ".")
        self.git(writer, "commit", "-qm", "main-guide")
        self.git(writer, "merge", "--no-ff", "-qm", "merge-pr", "pr")
        result, output = self.run_selector(writer, stale_base)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(parse_outputs(output), {"check": "false", "render": "false"})

    def test_real_repository_guide_closure_parses_cleanly(self):
        closure = select_guide.guide_import_closure(ROOT)
        self.assertGreater(len(closure), 0)
        self.assertNotIn("CslibFrontier", closure)


if __name__ == "__main__":
    unittest.main()
