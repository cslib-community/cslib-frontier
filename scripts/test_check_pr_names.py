"""Unit tests for scripts/check_pr_names.py."""

from __future__ import annotations

import io
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_pr_names as cpn  # noqa: E402

LIBRARY = """\
module
-- upstream: candidate

public import CslibFrontier.Init

/-! # Demo

* `Cslib.Demo.ghostInDocstring` is only mentioned in this docstring.
-/

@[expose] public section

namespace Cslib.Demo

/-- A structure. -/
structure Pair (α : Type) extends Inhabited α where
  {width : ℕ}
  first : α
  second second' : α
  mk' ::

inductive Color where
  | red
  | green : Color

@[simp] theorem pair_first_eq {α : Type} (p : Pair α) : p.first = p.first := rfl

theorem foo_iff : True ↔ True := Iff.rfl

theorem hasCollision_of_le (hfA : True) (h_le : True) : True := hfA

noncomputable def nonceGame (n : ℕ) : ℕ := go n
where
  go (k : ℕ) : ℕ := k

private lemma hidden_helper : True := trivial

alias ⟨foo_mp, foo_mpr⟩ := foo_iff

section Inner
variable (padFn : ℕ → ℕ)
def secureGame : ℕ := 0
end Inner

end Cslib.Demo

namespace Finset
theorem prod_swap_demo : True := trivial
end Finset

theorem _root_.Nat.demo_root : True := trivial

theorem Iff.mp : True := trivial
"""

ENCODINGS = """\
namespace Cslib.Crypto.VOLE

enc_structure Native.encShare (eF : Encoding F) : Share F where
  key : eF
  tags : encList eF

enc_structure
  Native.encView
  (eF : Encoding F) (eResult : Encoding R) : View F R where
  share : Native.encShare eF
  result : eResult

end Cslib.Crypto.VOLE
"""

ENCODING_NAMES = ["Native.encShare", "Native.encView", "encViewFields", "encShare_apply",
                  "encView_apply", "Cslib.Crypto.VOLE.Native.encShareFields"]


class CheckPrNamesTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.write("CslibFrontier/Demo/Basic.lean", LIBRARY)

    def write(self, rel: str, content: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")

    def check(self, text: str, base: str | None = None) -> dict[str, cpn.Finding]:
        report = cpn.check(text, self.root, core=False, base=base)
        return {f.token: f for f in report.findings}

    # --- Extraction ---------------------------------------------------------------------------

    def test_extracts_backticked_spans_outside_code_blocks_and_comments(self) -> None:
        text = ("Adds `foo` and ``bar `x` baz``.\n\n```lean\ntheorem `inFence` : True\n```\n"
                "<!-- `inComment` -->\nThen `foo` again and `qux`.")
        self.assertEqual(cpn.extract_tokens(text), ["foo", "bar `x` baz", "qux"])

    def test_candidates_skip_non_names(self) -> None:
        skipped = ["h k m + padFn 𝒩", "CslibFrontier/Demo/Basic.lean", "CarterWegman.lean",
                   "0", "c69067ba", "simp", "ε", "trace", "hx", "_leaf_le", "pull_request",
                   "GITHUB_EVENT_PATH",
                   "PRF", "lake build", "mk_all --check", "lint-style", "native_decide", "theorem",
                   "-1", "@[simp]", "x.1", "Y", ".symm", "maxHeartbeats", "linter.style.longLine"]
        for token in skipped:
            with self.subTest(token=token):
                self.assertFalse(cpn.is_candidate(token))
        kept = ["nonceSignOracle", "IsDiffUniversal", "secureNonceMAC_of_isPRF", "Nodup",
                "List.Nodup", "Cslib.Demo.Pair.first", ".Nodup", "foo_iff.mp", "Nat.succ_le'",
                "_root_.Nat.demo_root", "card_inv_le"]
        for token in kept:
            with self.subTest(token=token):
                self.assertTrue(cpn.is_candidate(token))

    # --- Resolution ---------------------------------------------------------------------------

    def test_declarations_resolve_by_full_name_and_suffix(self) -> None:
        names = ["Cslib.Demo.pair_first_eq", "Demo.pair_first_eq", "pair_first_eq", "Pair",
                 "Cslib.Demo.Pair", "Cslib.Demo", "Demo", "Nat.demo_root", "secureGame",
                 "Cslib.Demo.secureGame", "hidden_helper", "foo_mp", "Demo.foo_mpr"]
        self.assertEqual(self.check(" ".join(f"`{n}`" for n in names)), {})

    def test_members_and_generated_names_resolve(self) -> None:
        names = ["Pair.first", "Pair.width", "Pair.second", "Pair.second'", "Pair.toInhabited",
                 "Pair.mk'",
                 "Color.red", "Color.green", "Color.rec", "Pair.ext_iff", "pair_first_eq.eq_1",
                 "nonceGame.go", "foo_iff.mp", "pair_first_eq_apply"]
        self.assertEqual(self.check(" ".join(f"`{n}`" for n in names)), {})

    def test_to_additive_translation_and_modules_resolve(self) -> None:
        names = ["Finset.sum_swap_demo", "CslibFrontier.Demo.Basic", "Demo.Basic"]
        self.assertEqual(self.check(" ".join(f"`{n}`" for n in names)), {})

    def test_missing_names_are_reported_with_context(self) -> None:
        found = self.check("`nonceSignOracle`, `ghostInDocstring`, `Cslib.Wrong.secureGame`, "
                           "`Pair.third`, `padFn` and `nonceGame`.")
        self.assertEqual(list(found), ["nonceSignOracle", "ghostInDocstring",
                                       "Cslib.Wrong.secureGame", "Pair.third", "padFn"])
        self.assertEqual(found["nonceSignOracle"].mentions, 0)
        self.assertEqual(found["ghostInDocstring"].mentions, 1)
        self.assertEqual(found["Cslib.Wrong.secureGame"].declared_as, ["Cslib.Demo.secureGame"])
        self.assertEqual(found["padFn"].mentions, 1)
        self.assertIn("not found in any source file", found["nonceSignOracle"].note(None))
        self.assertIn("did you mean `Cslib.Demo.secureGame`",
                      found["Cslib.Wrong.secureGame"].note(None))

    def test_parent_projections_resolve_from_the_structure_file(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.write("CslibFrontier/Parent.lean", "class Base (α : Type) where\n  base : α\n")
        self.write("CslibFrontier/Child.lean",
                   "structure Pair (α : Type) extends Base α where\n  first : α\n")
        self.assertEqual(self.check("`Pair.toBase`"), {})
        self.assertEqual(list(self.check("`Pair.toNotAThing`")), ["Pair.toNotAThing"])

    def test_hypothesis_shaped_names(self) -> None:
        found = self.check("`hasCollision_of_le`, `hfA`, `h_le`, `hasNothing`, `hFoo`")
        self.assertEqual(list(found), ["hasNothing", "hFoo"])

    def test_generated_names_read_the_head_only_when_needed(self) -> None:
        self.assertEqual(cpn.search_words("Nat.succ_le_of_lt"), {"succ_le_of_lt"})
        self.assertEqual(cpn.head_words("Nat.succ_le_of_lt"), set())
        self.assertEqual(cpn.head_words("Pair.mk"), {"Pair"})
        self.assertEqual(cpn.head_words("foo_iff.mp"), {"foo_iff"})

    def test_python_script_names_resolve(self) -> None:
        self.write("scripts/check_demo.py", "def changed_files():\n    pass\n")
        found = self.check("`check_demo.changed_files`, `changed_files`, `check_demo.missing_fn`")
        self.assertEqual(list(found), ["check_demo.missing_fn"])

    def test_python_search_matches_ripgrep(self) -> None:
        text = "`Cslib.Demo.Pair.first` `nonceSignOracle` `Color.red`"
        with mock.patch.object(cpn.shutil, "which", return_value=None):
            fallback = self.check(text)
        self.assertEqual(list(fallback), ["nonceSignOracle"])
        self.assertEqual(list(self.check(text)), ["nonceSignOracle"])

    def test_comments_are_not_declarations(self) -> None:
        self.write("CslibFrontier/Demo/Commented.lean",
                   "/- theorem inBlock : True := trivial -/\n-- theorem inLine : True := trivial\n"
                   "/-- doc\ntheorem inDoc : True := trivial -/\n"
                   "theorem real_decl : True := trivial\n")
        self.assertEqual(list(self.check("`inBlock` `inLine` `inDoc` `real_decl`")),
                         ["inBlock", "inLine", "inDoc"])

    def test_comment_delimiters_in_literals_preserve_following_declarations(self) -> None:
        literals = ['"/-"', '"--"', '"-/"', 'r#"/- nested -- -/"#', "'/'", "'-'"]
        for literal in literals:
            with self.subTest(literal=literal):
                decls = cpn.Declarations()
                cpn.parse_source(
                    "namespace Sample\n"
                    f"def marker := {literal}\n"
                    "/- outer /- nested -/ comment -/\n"
                    "def after_marker : Nat := 0\nend Sample\n", decls)
                self.assertTrue(decls.declared("Sample.after_marker"))

    def test_comment_masking_preserves_syntax_keyword_literals(self) -> None:
        decls = cpn.Declarations()
        cpn.parse_source('syntax "demo_keyword" : tactic\n', decls)
        self.assertIn("demo_keyword", decls.keywords)

    def test_enc_structure_names_find_the_command_individually(self) -> None:
        self.write("CslibFrontier/Crypto/VOLE/Encoding.lean", ENCODINGS)
        for name in ENCODING_NAMES:
            with self.subTest(name=name):
                self.assertEqual(self.check(f"`{name}`"), {})
        self.assertEqual(cpn.search_words("Native.encViewFields"),
                         {"encViewFields", "encView"})
        self.assertEqual(list(self.check("`Native.encViewFieldz`")), ["Native.encViewFieldz"])

    def test_enc_structure_ignores_comments_literals_and_ordinary_defs(self) -> None:
        self.write("CslibFrontier/Demo/Encoding.lean", '''\
/- enc_structure commentedEncoder : Pair where -/
def text : String := r#"
enc_structure literalEncoder : Pair where
"#
def ordinaryEncoder : Nat := 0
''')
        names = ["commentedEncoder", "literalEncoder", "literalEncoderFields",
                 "ordinaryEncoderFields"]
        self.assertEqual(list(self.check(" ".join(f"`{name}`" for name in names))), names)

    def test_enc_structure_root_name_ignores_the_current_namespace(self) -> None:
        self.write("CslibFrontier/Demo/Encoding.lean", "namespace Inner\n"
                   "enc_structure _root_.Outer.encPair : Pair where\n"
                   "  first : encUnary\nend Inner\n")
        for name in ["Outer.encPair", "Outer.encPairFields", "Outer.encPair_apply"]:
            self.assertEqual(self.check(f"`{name}`"), {})
        self.assertEqual(list(self.check("`Inner.Outer.encPairFields`")),
                         ["Inner.Outer.encPairFields"])

    def test_enc_structure_field_is_not_a_command(self) -> None:
        self.write("CslibFrontier/Demo/State.lean", "structure ToolState where\n"
                   "  enc_structure : Nat\n  next : Nat\n")
        self.assertEqual(list(self.check("`ToolState.enc_structure` `ToolState.next` "
                                         "`nextFields`")), ["nextFields"])

    def test_enc_structure_multiple_fields_preserve_the_member_context(self) -> None:
        self.write("CslibFrontier/Demo/State.lean", "structure ToolState where\n"
                   "  enc_structure next : Nat\n  tail : Nat\n")
        self.assertEqual(list(self.check("`ToolState.enc_structure` `ToolState.next` "
                                         "`ToolState.tail` `nextFields`")), ["nextFields"])

    def test_enc_structure_continued_field_preserves_following_fields(self) -> None:
        self.write("CslibFrontier/Demo/State.lean", "structure ToolState where\n"
                   "  enc_structure\n    : Nat\n  next : Nat\n")
        self.assertEqual(list(self.check("`ToolState.next` `nextFields`")), ["nextFields"])

    def test_enc_structure_in_a_quoted_body_is_not_a_declaration(self) -> None:
        self.write("CslibFrontier/Demo/Quotation.lean", "def quotedCommand := by\n"
                   "  exact `(command|\n"
                   "    enc_structure phantomEncoder : Share where\n"
                   "      key : encUnary)\n")
        names = ["phantomEncoder", "phantomEncoderFields", "phantomEncoder_apply"]
        self.assertEqual(list(self.check(" ".join(f"`{name}`" for name in names))), names)

    # --- Base revision and CLI ----------------------------------------------------------------

    def git(self, *args: str) -> str:
        return subprocess.run(["git", *args], cwd=self.root, check=True, capture_output=True,
                              text=True).stdout.strip()

    def commit(self, *args: str) -> None:
        self.git("-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false",
                 "commit", "-q", *args)

    def test_names_removed_by_the_change_are_recognized(self) -> None:
        self.git("init", "-q")
        self.git("config", "color.ui", "always")
        self.commit("--allow-empty", "-m", "root")
        self.write("CslibFrontier/Demo/Old.lean",
                   "namespace Cslib.Old\ntheorem old_lemma : True := trivial\nend Cslib.Old\n")
        self.git("add", ".")
        self.commit("-m", "base")
        base = self.git("rev-parse", "HEAD")
        (self.root / "CslibFrontier/Demo/Old.lean").unlink()
        found = self.check("Removes `Cslib.Old.old_lemma`; adds `brandNew`.", base=base)
        self.assertTrue(found["Cslib.Old.old_lemma"].removed)
        self.assertFalse(found["brandNew"].removed)
        report = cpn.Report(["Cslib.Old.old_lemma", "brandNew"], list(found.values()), base)
        self.assertEqual([f.token for f in report.unexplained], ["brandNew"])

    def test_enc_structure_replacement_does_not_report_generated_names_removed(self) -> None:
        path = "CslibFrontier/Crypto/VOLE/Encoding.lean"
        self.write(path, "namespace Cslib.Crypto.VOLE\n"
                   "def Native.encShare := 0\ndef Native.encView := 0\n"
                   "abbrev Native.encViewFields := Nat\n"
                   "theorem Native.encShare_apply : True := trivial\n"
                   "theorem Native.encView_apply : True := trivial\n"
                   "def Native.legacyEncoder := 0\nend Cslib.Crypto.VOLE\n")
        self.git("init", "-q")
        self.git("add", ".")
        self.commit("-m", "handwritten encodings")
        base = self.git("rev-parse", "HEAD")
        self.write(path, ENCODINGS)
        names = ENCODING_NAMES + ["Native.legacyEncoder", "Native.encViewFieldz"]
        found = self.check(" ".join(f"`{name}`" for name in names), base=base)
        self.assertEqual(list(found), ["Native.legacyEncoder", "Native.encViewFieldz"])
        self.assertTrue(found["Native.legacyEncoder"].removed)
        self.assertFalse(found["Native.encViewFieldz"].removed)

    def test_cli_event_payload_strict_and_github_summary(self) -> None:
        event = self.root / "event.json"
        event.write_text(json.dumps({"pull_request": {"body": "Adds `nonceSignOracle`."}}),
                         encoding="utf-8")
        summary = self.root / "summary.md"
        out = io.StringIO()
        with mock.patch.dict(cpn.os.environ, {"GITHUB_STEP_SUMMARY": str(summary)}), \
                redirect_stdout(out):
            code = cpn.main(["--event", str(event), "--github", "--no-core", "--root",
                             str(self.root), "--base", "HEAD"], root=self.root)
        self.assertEqual(code, 0)
        self.assertIn("::notice title=PR description names::", out.getvalue())
        self.assertIn("`nonceSignOracle`: not found in any source file", summary.read_text())
        with redirect_stdout(io.StringIO()):
            self.assertEqual(cpn.main(["--event", str(event), "--strict", "--no-core", "--root",
                                       str(self.root)], root=self.root), 1)
        clean = self.root / "clean.md"
        clean.write_text("Adds `Cslib.Demo.Pair`.", encoding="utf-8")
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(cpn.main(["--file", str(clean), "--strict", "--no-core", "--root",
                                       str(self.root)], root=self.root), 0)
        self.assertIn("All 1 backticked names", out.getvalue())

    def test_fetch_deps_skips_network_when_local_sources_resolve_all_tokens(self) -> None:
        with mock.patch.object(cpn, "fetch_dependency_sources") as fetch:
            report = cpn.check("Uses `Cslib.Demo.Pair` and `Cslib.Demo.pair_first_eq`.",
                               self.root, core=False, fetch_deps=True)
        self.assertEqual(report.findings, [])
        fetch.assert_not_called()

    def test_fetch_deps_resolves_manifest_packages_and_core_sources_and_skips_bad_entries(self) -> None:
        def make_git_repo(rel: str, files: dict[str, str], tag: str | None = None) -> tuple[str, str]:
            repo = self.root / rel
            repo.mkdir(parents=True)
            for path, content in files.items():
                target = repo / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(content, encoding="utf-8")
            env = {**cpn.os.environ, "GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@t",
                   "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@t"}
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True, env=env)
            subprocess.run(["git", "add", "."], cwd=repo, check=True, env=env)
            subprocess.run(["git", "-c", "commit.gpgsign=false", "commit", "-q", "-m", "init"],
                           cwd=repo, check=True, env=env)
            rev = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
            if tag:
                subprocess.run(["git", "tag", tag], cwd=repo, check=True, env=env)
            return repo.as_uri(), rev

        pkg_url, pkg_rev = make_git_repo(
            "remotes/extpkg",
            {"ExtPkg/Basic.lean": "namespace ExtPkg\ntheorem ext_bridge : True := trivial\nend ExtPkg\n"},
        )
        sub_url, sub_rev = make_git_repo(
            "remotes/subpkg",
            {"nested/SubPkg/Basic.lean": "namespace SubPkg\ntheorem sub_bridge : True := trivial\nend SubPkg\n",
             "outside/Ignored.lean": "namespace Ignored\ntheorem not_in_subdir : True := trivial\nend Ignored\n"},
        )
        core_url, _ = make_git_repo(
            "remotes/lean4",
            {"src/Init/CoreDemo.lean": "namespace Init\ntheorem core_refl : True := trivial\nend Init\n"},
            tag="v4.99.0-test",
        )
        manifest = {
            "version": "1.3.0",
            "packages": [
                42,
                {"type": "git", "name": "nonsub", "url": pkg_url, "rev": pkg_rev, "subDir": 123},
                {"type": "git", "name": "listsub", "url": pkg_url, "rev": pkg_rev, "subDir": ["nested"]},
                {"type": "git", "name": "extpkg", "url": pkg_url, "rev": pkg_rev, "subDir": None},
                {"type": "git", "name": "extpkg", "url": pkg_url, "rev": pkg_rev, "subDir": "../escape"},
                {"type": "git", "name": "subpkg", "url": sub_url, "rev": sub_rev, "subDir": "nested"},
                {"type": "git", "name": "../escape", "url": pkg_url, "rev": pkg_rev, "subDir": None},
                {"type": "git", "name": "badrev", "url": pkg_url, "rev": "not-a-sha", "subDir": None},
                {"type": "git", "name": "badurl", "url": "-oProxyCommand=evil", "rev": pkg_rev, "subDir": None},
            ],
        }
        (self.root / "lake-manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.99.0-test\n", encoding="utf-8")
        body = ("Combines `Cslib.Demo.Pair`, `ExtPkg.ext_bridge`, `SubPkg.sub_bridge`, "
                "`Init.core_refl`, `Ignored.not_in_subdir`, and `missingSlip`.")
        with mock.patch.object(cpn.shutil, "which", side_effect=lambda cmd: None if cmd == "lean"
                               else shutil_which(cmd)), \
                mock.patch.dict(cpn.os.environ, {"LEAN_CORE_GIT_URL": core_url}):
            without_fetch = cpn.check(body, self.root, core=True, fetch_deps=False)
            with_fetch = cpn.check(body, self.root, core=True, fetch_deps=True)
        self.assertEqual([f.token for f in without_fetch.findings],
                         ["ExtPkg.ext_bridge", "SubPkg.sub_bridge", "Init.core_refl",
                          "Ignored.not_in_subdir", "missingSlip"])
        self.assertEqual([f.token for f in with_fetch.findings],
                         ["Ignored.not_in_subdir", "missingSlip"])

        for malformed in ('{"packages": 123}', '{"packages": null}', '[]', '{not-json'):
            with self.subTest(malformed=malformed):
                (self.root / "lake-manifest.json").write_text(malformed, encoding="utf-8")
                with mock.patch.object(cpn.shutil, "which", side_effect=lambda cmd: None if cmd == "lean"
                                       else shutil_which(cmd)):
                    report = cpn.check("Uses `Cslib.Demo.Pair` and `missingSlip`.",
                                       self.root, core=False, fetch_deps=True)
                self.assertEqual([f.token for f in report.findings], ["missingSlip"])


shutil_which = cpn.shutil.which


if __name__ == "__main__":
    unittest.main()
