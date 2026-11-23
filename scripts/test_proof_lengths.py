"""Unit tests for scripts/proof_lengths.py."""

from __future__ import annotations

import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import proof_lengths as pl  # noqa: E402


class ProofLengthsTests(unittest.TestCase):
    def test_self_check_passes(self) -> None:
        pl.self_check()

    def test_private_meta_def_terminates_preceding_theorem(self) -> None:
        # Regression: `CslibFrontier/Tactic/Negligible.lean:92 natCast_mul_ofNat_eq` was
        # previously miscounted at 507 body lines because `private meta def` right after it
        # was not recognized as a top-level command boundary.
        source = (
            "module\n"
            "-- upstream: candidate\n\n"
            "theorem natCast_mul_ofNat_eq (m : Nat) : m = m :=\n"
            "  rfl\n\n"
            "/-- Helper declaration in meta phase. -/\n"
            "private meta def helper (x : Nat) : Nat :=\n"
            "  let y := x + 1\n"
            "  let z := y + 2\n"
            "  z\n\n"
            "private meta partial def helperRec (n : Nat) : Nat :=\n"
            "  match n with\n"
            "  | 0 => 0\n"
            "  | k + 1 => helperRec k\n"
        )
        rows = pl.scan(source, "CslibFrontier/Tactic/Negligible.lean")
        self.assertEqual(
            [(r["name"], r["body_lines"], r["group"]) for r in rows],
            [("natCast_mul_ofNat_eq", 1, "Tactics")],
        )

    def test_meta_command_boundaries(self) -> None:
        cases = (
            "meta def f : Nat := 0\n  ",
            "private meta def f : Nat := 0\n",
            "public meta def f : Nat := 0\n",
            "protected meta def f : Nat := 0\n",
            "private meta partial def f : Nat := 0\n",
            "meta structure S where\n  x : Nat\n",
            "meta section\n",
            "public meta section\n",
            "@[expose] public meta section\n",
            "@[expose]\npublic meta section\n",
        )
        for boundary in cases:
            with self.subTest(boundary=boundary.splitlines()[0]):
                source = (
                    "theorem t : True := by\n"
                    "  trivial\n\n"
                    f"{boundary}"
                    "  -- body/inner line\n"
                    "  let ignored := 1\n"
                    "  ignored\n"
                )
                rows = pl.scan(source, "CslibFrontier/Tactic/Example.lean")
                self.assertEqual([(r["name"], r["body_lines"]) for r in rows], [("t", 1)])

    def test_meta_prefixed_section_is_one_command_start(self) -> None:
        source = (
            "theorem first : True :=\n"
            "  True.intro\n"
            "public meta section\n"
            "meta def helper : Nat := 1\n"
            "end\n"
            "@[expose]\n"
            "public meta section\n"
            "meta theorem mt : True := by\n"
            "  trivial\n"
            "private meta lemma ml : True :=\n"
            "  True.intro\n"
            "end\n"
        )
        _, syntax = pl.masks(source)
        starts = pl.command_starts(syntax)
        heads = [syntax[s:].splitlines()[0] for s in starts]
        self.assertEqual(
            heads,
            [
                "theorem first : True :=",
                "public meta section",
                "meta def helper : Nat := 1",
                "end",
                "@[expose]",
                "meta theorem mt : True := by",
                "private meta lemma ml : True :=",
                "end",
            ],
        )
        rows = pl.scan(source, "CslibFrontier/Tactic/Example.lean")
        self.assertEqual(
            [(r["name"], r["kind"], r["body_lines"]) for r in rows],
            [("first", "theorem", 1), ("mt", "theorem", 1), ("ml", "lemma", 1)],
        )

    def test_real_tactic_negligible_theorem_count(self) -> None:
        path = pl.ROOT / "CslibFrontier/Tactic/Negligible.lean"
        if not path.is_file():
            self.skipTest(f"{path} not present")
        rows = pl.scan(path.read_text(encoding="utf-8"), "CslibFrontier/Tactic/Negligible.lean")
        by_name = {r["name"]: r for r in rows}
        self.assertIn("natCast_mul_ofNat_eq", by_name)
        self.assertEqual(by_name["natCast_mul_ofNat_eq"]["body_lines"], 1)
        self.assertEqual(by_name["natCast_mul_ofNat_eq"]["group"], "Tactics")

    def test_groups_are_unshadowed_and_preserve_existing_names(self) -> None:
        prefixes = [prefix for _, prefix in pl.GROUPS]
        for idx, prefix in enumerate(prefixes):
            for earlier in prefixes[:idx]:
                self.assertFalse(
                    prefix.startswith(earlier),
                    f"group prefix {prefix!r} is shadowed by earlier prefix {earlier!r}",
                )

        def group_of(rel: str) -> str:
            rows = pl.scan("theorem t : True := True.intro\n", f"CslibFrontier/{rel}")
            return rows[0]["group"]

        # Preserve every original group label and path assignment.
        expected = {
            "Computability/Circuit/Frontier/X.lean": "Circuits: frontier",
            "Computability/Circuit/Boolean/X.lean": "Circuits: Boolean",
            "Computability/Circuit/Monotone/X.lean": "Circuits: monotone",
            "Computability/Circuit/Arithmetic/X.lean": "Circuits: arithmetic",
            "Computability/Circuit/Basic.lean": "Circuits: shared infrastructure",
            "Computability/Machines/Turing/MultiTape/Universal/X.lean": "Machines: universal interpreter",
            "Computability/Machines/Turing/MultiTape/Complexity/X.lean": "Machines: complexity calculus",
            "Computability/Machines/Other.lean": "Machines: other",
            "Computability/Complexity/CookLevin/X.lean": "Cook-Levin",
            "Computability/Complexity/X.lean": "Complexity classes and reductions",
            "Computability/PCP/X.lean": "PCP",
            "Computability/LogSpaceDerandomization/X.lean": "Logspace derandomization",
            "Computability/DecisionTree/X.lean": "Decision trees",
            "Computability/Communication/X.lean": "Communication complexity",
            "Foundations/BooleanAnalysis/X.lean": "Boolean analysis",
            "Foundations/Combinatorics/Expander/X.lean": "Expanders",
            "Foundations/LinearAlgebra/X.lean": "Linear algebra",
            "Foundations/Combinatorics/X.lean": "Combinatorics: other",
            "Foundations/Data/X.lean": "Shared data structures",
            "Foundations/Probability/X.lean": "Probability foundations",
            "Probability/X.lean": "Probability constructions",
            "Logics/Propositional/X.lean": "Propositional logic",
            "Logics/FirstOrder/X.lean": "First/second-order logic",
            "Crypto/X.lean": "Cryptography",
            # Newly bucketed top-level areas and major subdirectories.
            "Algorithms/WordRAM/X.lean": "Algorithms: Word RAM",
            "Algorithms/Lean/X.lean": "Algorithms: Lean",
            "Algorithms/Dijkstra/X.lean": "Algorithms: other",
            "DataStructure/Dictionary/X.lean": "Data structures: dictionaries",
            "DataStructure/PriorityQueue/X.lean": "Data structures: other",
            "Computability/Distributed/X.lean": "Distributed computing",
            "Computability/PolyTime/X.lean": "Polynomial-time computability",
            "Computability/WordRAM/X.lean": "Word RAM",
            "Computability/QueryComplexity/X.lean": "Query complexity",
            "Computability/MCSP/X.lean": "MCSP",
            "Computability/WangTile/X.lean": "Wang tiles",
            "Computability/Probabilistic/X.lean": "Probabilistic computability",
            "Computability/Automata/X.lean": "Computability: other",
            "Foundations/Geometry/X.lean": "Geometry foundations",
            "Foundations/Analysis/X.lean": "Analysis foundations",
            "Foundations/Quantum/X.lean": "Quantum foundations",
            "Foundations/Algebra/X.lean": "Algebra foundations",
            "Foundations/NumberTheory/X.lean": "Foundations: other",
            "GameTheory/X.lean": "Game theory",
            "MachineLearning/X.lean": "Machine learning",
            "Languages/X.lean": "Languages",
            "Privacy/X.lean": "Privacy",
            "Tactic/X.lean": "Tactics",
        }
        for rel, label in expected.items():
            with self.subTest(rel=rel):
                self.assertEqual(group_of(rel), label)

    def test_every_top_level_library_directory_is_bucketed(self) -> None:
        lib = pl.ROOT / "CslibFrontier"
        if not lib.is_dir():
            self.skipTest(f"{lib} not present")
        top_dirs = sorted(p.name for p in lib.iterdir() if p.is_dir())
        for dirname in top_dirs:
            rel = f"{dirname}/Placeholder.lean"
            with self.subTest(directory=dirname):
                matched = any(rel.startswith(prefix) for _, prefix in pl.GROUPS)
                self.assertTrue(matched, f"CslibFrontier/{dirname}/ falls into Other library modules")


if __name__ == "__main__":
    unittest.main()
