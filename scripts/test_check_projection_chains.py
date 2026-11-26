"""Unit tests for scripts/check_projection_chains.py, on synthetic Lean modules."""

from __future__ import annotations

import contextlib
import io
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_projection_chains as c  # noqa: E402

HEADER = "module\n-- upstream: candidate\n\npublic import CslibFrontier.Init\n\npublic section\n\n"


def found(source: str) -> list[tuple[str, int, str]]:
    return [(row.declaration, row.line, row.chain)
            for row in c.module_chains(HEADER + source)]


def chains(source: str) -> list[str]:
    return [chain for _, _, chain in found(source)]


class RuleTests(unittest.TestCase):
    def test_statements_and_definition_bodies_count(self) -> None:
        self.assertEqual(found("theorem t (c : (ℕ × ℕ) × ℕ) : c.1.2 = c.1.2 := rfl\n"),
                         [("t", 8, ".1.2"), ("t", 8, ".1.2")])
        self.assertEqual(found("def f (c : (ℕ × ℕ) × ℕ) : ℕ :=\n  c.1.2 + c.2.fst\n"),
                         [("f", 9, ".1.2"), ("f", 9, ".2.fst")])
        self.assertEqual(chains("def f (c : (ℕ × ℕ) × ℕ) : ℕ :=\n  c.1.2 + (g c).2.1.1\n"),
                         [".1.2", ".2.1.1"])
        self.assertEqual(chains("instance : Foo ((ℕ × ℕ) × ℕ) := ⟨fun c => c.1.1⟩\n"), [".1.1"])
        self.assertEqual(chains("structure S where\n  f : (ℕ × ℕ) × ℕ\n  h : f.1.2 = 0\n"),
                         [".1.2"])
        self.assertEqual(chains("def f : (ℕ × ℕ) × ℕ → ℕ := (·.1.2)\n"), [".1.2"])

    def test_single_projections_and_literals_do_not_count(self) -> None:
        self.assertEqual(chains("theorem t (p : ℕ × ℕ) : p.1 + p.2 = p.2 + p.1 := by omega\n"
                                "def x : Float := 1.5\ndef v : String := \"1.5.2\"\n"), [])
        self.assertEqual(chains("def f := g 1.5.2\n"), [])

    def test_proofs_and_tactic_blocks_do_not_count(self) -> None:
        self.assertEqual(chains("theorem t (c : (ℕ × ℕ) × ℕ) : True := by\n"
                                "  have := c.1.2\n  trivial\n"), [])
        self.assertEqual(chains("theorem t (c : (ℕ × ℕ) × ℕ) : True := ⟨c.1.2⟩\n"), [])
        self.assertEqual(chains("def f (c : (ℕ × ℕ) × ℕ) : {n // n = c.1.1} :=\n"
                                "  ⟨c.1.1, by simp [c.1.2]⟩\n"), [".1.1", ".1.1"])
        self.assertEqual(chains("def f : ℕ → ℕ\n  | n => n\ntermination_by n => n.1.2\n"), [])

    def test_private_declarations_comments_and_variables_do_not_count(self) -> None:
        self.assertEqual(chains("private def f (c : (ℕ × ℕ) × ℕ) : ℕ := c.1.2\n"
                                "-- def g := c.1.2\n/-- `c.1.2` in a docstring -/\n"
                                "theorem t : True := trivial\n"
                                "variable (h : ∀ c : (ℕ × ℕ) × ℕ, c.1.2 = 0)\n"), [])
        self.assertEqual(c.module_chains("module\n\ntheorem t (c : (ℕ × ℕ) × ℕ) : c.1.2 = 0 := "
                                         "sorry\n"), [])  # not public in a module

    def test_internal_declarations_count(self) -> None:
        self.assertEqual(chains("namespace Internal\n\n"
                                "theorem t (c : (ℕ × ℕ) × ℕ) : c.1.2 = 0 := sorry\n\nend Internal\n"),
                         [".1.2"])

    def test_standing_exceptions(self) -> None:
        # Conclusions that automation looks up by head.
        self.assertEqual(chains("@[program_certificate] theorem t :\n"
                                "    ComputableInPolyTime (fun c => step c.1.1 c.1.2) e e := sorry\n"
                                "@[fun_prop] theorem u : Foo (fun c => c.1.2) := sorry\n"), [])
        self.assertEqual(chains("theorem t (h : c.1.2 = 0) :\n"
                                "    ComputableInPolyTime (fun c => step c.1.1 c.1.2) e e := sorry\n"),
                         [".1.2"])
        # The efficiency exception does not depend on how the predicate's head is qualified;
        # a nearby chain outside the predicate still counts.
        for head in ("ComputableInPolyTime", "Turing.MultiTapeTM.ComputableInPolyTime",
                     "_root_.Turing.MultiTapeTM.ComputableInPolyTime", "ComputableInSpace",
                     "Turing.MultiTapeTM.ComputableInSpace", "IsPPT", "Cslib.Crypto.IsPPT",
                     # Oracle PPT predicates also carry `@[fun_prop]` lemmas (Memoize, Parameter).
                     "IsOraclePPT", "IsOraclePPTOn", "Cslib.Probability.IsOraclePPTOn"):
            with self.subTest(head=head):
                self.assertEqual(chains(f"theorem t : {head} (fun c => c.1.2) e e := sorry\n"),
                                 [])
                self.assertEqual(chains(f"theorem t (h : c.2.1 = 0) :\n"
                                        f"    {head} (fun c => c.1.2) e e := sorry\n"),
                                 [".2.1"])
        # A qualified name that only ends in an efficiency predicate's prefix is no exception.
        self.assertEqual(chains("theorem t : Foo.ComputableBar (fun c => c.1.2) := sorry\n"),
                         [".1.2"])
        # Named accessors are the remedy.
        self.assertEqual(chains("abbrev Ctx.desc (c : Ctx) : D := c.1.1\n"
                                "def Ctx.cfg : Ctx → C := fun c => c.1.2\n"), [])
        self.assertEqual(chains("def Ctx.both (c : Ctx) : D × C := (c.1.1, c.1.2)\n"),
                         [".1.1", ".1.2"])

    def test_nested_and_mixed_prod_projections_count(self) -> None:
        self.assertEqual(
            found("theorem t (p : ℕ × (ℕ × ℕ)) : Prod.fst (Prod.snd p) = 0 := sorry\n"),
            [("t", 8, "Prod.fst (Prod.snd …)")])
        self.assertEqual(
            chains("def f (p : ℕ × (ℕ × ℕ)) : ℕ := _root_.Prod.fst (_root_.Prod.snd p)\n"),
            ["Prod.fst (Prod.snd …)"])
        # Deeper nesting counts as one maximal chain, not two.
        self.assertEqual(
            chains("def f (p : ℕ × (ℕ × (ℕ × ℕ))) : ℕ := Prod.fst (Prod.snd (Prod.fst p))\n"),
            ["Prod.fst (Prod.snd (Prod.fst …))"])
        # Right-application operators and negation prefix.
        self.assertEqual(
            chains("def f (p : ℕ × (ℕ × ℕ)) : ℕ := Prod.fst <| Prod.snd p\n"
                   "def g (p : ℕ × (ℕ × ℕ)) : ℕ := Prod.fst $ Prod.snd p\n"
                   "def h (p : ℕ × (ℕ × (ℕ × ℕ))) : ℕ := Prod.fst <| Prod.snd <| Prod.fst p\n"
                   "def k (p : ℕ × (Bool × ℕ)) : Bool := !Prod.fst (Prod.snd p)\n"),
            ["Prod.fst (Prod.snd …)", "Prod.fst (Prod.snd …)",
             "Prod.fst (Prod.snd (Prod.fst …))", "Prod.fst (Prod.snd …)"])
        # Mixed prefix/postfix with dotted projections (no double counting).
        self.assertEqual(
            chains("def a (p : ℕ × (ℕ × ℕ)) : ℕ := Prod.fst p.2\n"
                   "def b (p : ℕ × (ℕ × ℕ)) : ℕ := Prod.fst (p.2)\n"
                   "def c (p : ℕ × (ℕ × ℕ)) : ℕ := Prod.fst (g p).2\n"
                   "def d (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := Prod.fst p.2.1\n"
                   "def e (p : ℕ × (ℕ × ℕ)) : ℕ := Prod.fst <| p.2\n"
                   "def x (p : ℕ × (ℕ × ℕ)) : ℕ := (Prod.snd p).1\n"
                   "def y (p : ℕ × ((ℕ × ℕ) × ℕ)) : ℕ := (Prod.fst (Prod.snd p)).1.2\n"
                   "def z (p : ℕ × ((ℕ × ℕ) × ℕ)) : ℕ := Prod.fst ((Prod.snd p).1)\n"),
            ["Prod.fst ….2", "Prod.fst ….2", "Prod.fst ….2", "Prod.fst ….2.1",
             "Prod.fst ….2", "(Prod.snd …).1", "(Prod.fst (Prod.snd …)).1.2",
             "Prod.fst ((Prod.snd …).1)"])
        # Pipe-forward chains.
        self.assertEqual(
            chains("def a (p : ℕ × (ℕ × ℕ)) : ℕ := p |> Prod.snd |> Prod.fst\n"
                   "def b (p : ℕ × (ℕ × ℕ)) : ℕ := p.2 |> Prod.fst\n"
                   "def c (p : ℕ × (ℕ × ℕ)) : ℕ := (Prod.snd p) |> Prod.fst\n"
                   "def d (p : ℕ × (ℕ × ℕ)) : ℕ := (p |> Prod.snd).1\n"
                   "def e (p : ℕ × (ℕ × (ℕ × ℕ))) : ℕ := p.2.1 |> Prod.fst\n"
                   "def f (p : ℕ × (ℕ × ℕ)) : ℕ :=\n"
                   "  let x := p.2 |> Prod.fst\n"
                   "  x + 1\n"
                   "def g (p : ℕ × (ℕ × ℕ)) : ℕ := p.2 |> Prod.fst |> id\n"),
            ["… |> Prod.snd |> Prod.fst", "….2 |> Prod.fst", "(Prod.snd …) |> Prod.fst",
             "(… |> Prod.snd).1", "….2.1 |> Prod.fst", "….2 |> Prod.fst", "….2 |> Prod.fst"])
        # Structure field and inner chain inside a pair literal / larger call.
        self.assertEqual(
            chains("structure S where\n  x : ℕ × (ℕ × ℕ)\n  h : Prod.fst (Prod.snd x) = 0\n"),
            ["Prod.fst (Prod.snd …)"])
        self.assertEqual(
            chains("def f (p q : (ℕ × ℕ) × ℕ) := Prod.fst (Prod.fst p, Prod.snd (Prod.fst q))\n"
                   "def g (p : (ℕ × ℕ) × ℕ) := Prod.fst (h (p.1.2))\n"),
            ["Prod.snd (Prod.fst …)", ".1.2"])
        # Inner chains remain counted when an outer <| is intercepted, and parenthesized
        # chains extend cleanly or stay separate from outer dotted projections.
        self.assertEqual(
            chains("def a (p : ℕ × (ℕ × ℕ)) := Prod.fst <| Prod.fst (Prod.snd p) |> Prod.swap\n"
                   "def b (p : ℕ × (ℕ × ℕ)) := Prod.fst <| Prod.snd <| Prod.fst p |> Prod.swap\n"
                   "def c (p : (ℕ × ℕ) × (ℕ × ℕ)) := (Prod.fst (Prod.snd p)) |> Prod.fst\n"
                   "def d (p : (ℕ × ℕ) × (ℕ × ℕ)) := (Prod.fst (Prod.snd p) + q).1.2\n"),
            ["Prod.fst (Prod.snd …)", "Prod.fst (Prod.snd …)",
             "(Prod.fst (Prod.snd …)) |> Prod.fst", "Prod.fst (Prod.snd …)", ".1.2"])

    def test_allowed_prod_projections_do_not_count(self) -> None:
        # Point-free composition is explicitly allowed by CONTRIBUTING.md, including after `|>`.
        self.assertEqual(
            chains("def f : (ℕ × (ℕ × ℕ)) → ℕ := Prod.fst ∘ Prod.snd\n"
                   "def g (p : ℕ × (ℕ × ℕ)) : ℕ := (Prod.fst ∘ Prod.snd) p\n"
                   "def h (p : ℕ × (ℕ × ℕ)) : ℕ := p.2 |> Prod.fst ∘ Prod.swap\n"
                   "def i (p : ℕ × (ℕ × ℕ)) : ℕ := p |> Prod.snd |> Prod.fst ∘ Prod.swap\n"
                   "def j (p : ℕ × (ℕ × ℕ)) : ℕ := p |> Prod.snd ∘ Prod.swap |> Prod.fst\n"), [])
        # Single projection, higher-order arguments, field separator, checked indexing proof,
        # and whole-operand / whole-parenthesized-span boundaries under <| / $ / ().
        self.assertEqual(
            chains("def a (p : ℕ × ℕ) : ℕ := Prod.fst p\n"
                   "def b := xs.map Prod.fst\n"
                   "def c := foo Prod.fst (Prod.snd p)\n"
                   "def d := p.comap Prod.fst Prod.fst\n"
                   "def e := foo! Prod.fst (Prod.snd p)\n"
                   "def f := Prod.fst p.2.field\n"
                   "def g := Prod.fst (Prod.snd p).field\n"
                   "def h := Prod.fst (Prod.fst p, x)\n"
                   "def i := Prod.fst <| p.2 + q\n"
                   "def i2 := Prod.fst <| p.2 |> f\n"
                   "def i3 := Prod.fst <| Prod.snd p |> Prod.swap\n"
                   "def i4 := Prod.fst $ Prod.snd p |> Prod.swap\n"
                   "def i5 := Prod.fst <| Prod.snd p + q\n"
                   "def i6 := Prod.fst $ Prod.snd p + q\n"
                   "def i7 := Prod.fst <| Prod.snd p x\n"
                   "def j := Prod.fst <| p.2 x\n"
                   "def k := f x.2 |> Prod.fst\n"
                   "def m := p.2 |> Prod.fst + 1\n"
                   "def n1 := Prod.fst (Prod.snd p + q)\n"
                   "def n2 := Prod.fst (Prod.snd p |> Prod.swap)\n"
                   "def n3 := (Prod.snd p + q).1\n"
                   "def n4 := (Prod.snd p |> Prod.swap).1\n"
                   "def n5 := (Prod.snd p + q) |> Prod.fst\n"
                   "def n6 := (Prod.snd p |> Prod.swap) |> Prod.fst\n"
                   "def l := Prod.fst xs[i]'h.2\n"), [])
        # Ignored inside proofs, comments, docstrings, private decls, and efficiency predicates.
        self.assertEqual(
            chains("theorem t : True := by\n  have := Prod.fst (Prod.snd p)\n  trivial\n"
                   "private def p (x : ℕ × (ℕ × ℕ)) : ℕ := Prod.fst (Prod.snd x)\n"
                   "-- Prod.fst (Prod.snd x)\n"
                   "variable (h : ∀ x : ℕ × (ℕ × ℕ), Prod.fst (Prod.snd x) = 0)\n"
                   "theorem u : ComputableInPolyTime (fun x => Prod.fst (Prod.snd x)) e e := sorry\n"),
            [])
        # Outside an efficiency predicate, a chain still counts.
        self.assertEqual(
            chains("theorem u (h : Prod.fst (Prod.snd p) = 0) :\n"
                   "    ComputableInPolyTime (fun x => Prod.fst (Prod.snd x)) e e := sorry\n"),
            ["Prod.fst (Prod.snd …)"])

    def test_let_alias_projection_chains_count(self) -> None:
        self.assertEqual(
            found("def f (p : ℕ × (ℕ × ℕ)) : ℕ :=\n"
                  "  let rest := p.2\n"
                  "  rest.1 + rest.2\n"),
            [("f", 10, "rest.1 (via let rest := ….2)"),
             ("f", 10, "rest.2 (via let rest := ….2)")])
        # Typed let, multi-hop let alias, same-line let after `:=`, Prod.fst/snd mix, pipe-forward.
        self.assertEqual(
            chains("def a (p : ℕ × (ℕ × ℕ)) : ℕ := let r : ℕ × ℕ := p.2; r.1\n"
                   "def b (p : ℕ × (ℕ × (ℕ × ℕ))) : ℕ :=\n"
                   "  let r := p.2; let s := r.2; s.1\n"
                   "def c (p : ℕ × (ℕ × ℕ)) : ℕ := let r := p.2; Prod.fst r\n"
                   "def d (p : ℕ × (ℕ × ℕ)) : ℕ := let r := p.2; Prod.fst <| r\n"
                   "def e (p : ℕ × (ℕ × ℕ)) : ℕ := let r := p.2; r |> Prod.fst\n"
                   "def g (p : ℕ × (ℕ × ℕ)) : ℕ := let r := Prod.snd p; r.1\n"
                   "def h (p : ℕ × (ℕ × ℕ)) : ℕ := let r := Prod.snd p; Prod.fst r\n"
                   "def k (p : ℕ × (ℕ × ℕ)) : ℕ := let r := (p |> Prod.snd); r.1\n"
                   "def m (p : ℕ × (ℕ × ℕ)) : ℕ := let r := (xs[i]'h).2; r.1\n"),
            ["r.1 (via let r := ….2)",
             "r.2 (via let r := ….2)", "s.1 (via let s := ….2)",
             "Prod.fst r (via let r := ….2)",
             "Prod.fst r (via let r := ….2)",
             "r |> Prod.fst (via let r := ….2)",
             "r.1 (via let r := Prod.snd …)",
             "Prod.fst r (via let r := Prod.snd …)",
             "r.1 (via let r := Prod.snd …)",
             "r.1 (via let r := ….2)"])
        # No double counting when the alias use is already a dotted or Prod chain.
        self.assertEqual(
            chains("def a (p : ℕ × ((ℕ × ℕ) × ℕ)) : ℕ := let r := p.2; r.1.2\n"
                   "def b (p : ℕ × ((ℕ × ℕ) × ℕ)) : ℕ := let r := p.2; Prod.fst (Prod.snd r)\n"
                   "def c (p : ℕ × ((ℕ × ℕ) × ℕ)) : ℕ := let r := p.2; Prod.fst r.1\n"),
            [".1.2", "Prod.fst (Prod.snd …)", "Prod.fst ….1"])
        # Alias declared before `match` remains active inside all match arms.
        self.assertEqual(
            chains("def f (p : ℕ × (ℕ × ℕ)) (o : Option ℕ) : ℕ :=\n"
                   "  let r := p.2\n"
                   "  match o with\n"
                   "  | none => r.1\n"
                   "  | some _ => r.2\n"),
            ["r.1 (via let r := ….2)", "r.2 (via let r := ….2)"])
        # Self-shadowing rebind uses outer alias in RHS, inner alias in body.
        self.assertEqual(
            chains("def f (p : ℕ × (ℕ × (ℕ × ℕ))) : ℕ := let r := p.2; let r := r.2; r.1\n"),
            ["r.2 (via let r := ….2)", "r.1 (via let r := ….2)"])

    def test_let_alias_scoping_shadowing_and_exceptions(self) -> None:
        # Single use without further projection, field access, non-projection RHS, destructuring,
        # numeric literals, checked indexing proof, higher-order pipe/arg.
        self.assertEqual(
            chains("def a (p : ℕ × ℕ) : ℕ := let r := p.2; f r\n"
                   "def b (p : ℕ × S) : ℕ := let r := p.2; r.field\n"
                   "def c (p : S) : ℕ := let r := p.field; r.1\n"
                   "def d (p : ℕ × ℕ) : ℕ := let r := f p.2; r.1\n"
                   "def e (p : ℕ × ℕ) : ℕ := let r := p.2 + 1; r.1\n"
                   "def g := let r := 1.2; r.1\n"
                   "def h (p : ℕ × (ℕ × ℕ)) : ℕ := let (a, b) := p.2; a.1\n"
                   "def i := let r := xs[k]'h.2; r.1\n"
                   "def j (p : ℕ × (ℕ × ℕ)) : ℕ := let r := p.2; foo Prod.fst r\n"
                   "def k (p : ℕ × (ℕ × ℕ)) : ℕ := let r := p.2; f r |> Prod.fst\n"
                   "def l (p : ℕ × (ℕ × ℕ)) : ℕ := let fn (x : ℕ) := p.2; fn.1\n"
                   "def m (p : ℕ × (ℕ × ℕ)) (q : ℕ × ℕ) : ℕ := let r := p.2; Prod.fst <| r + q\n"
                   "def n (p : ℕ × (ℕ × ℕ)) (q : ℕ × ℕ) : ℕ := let r := p.2; Prod.fst $ r + q\n"
                   "def o (p : ℕ × (ℕ × ℕ)) (q : ℕ × ℕ) : ℕ := let r := p.2; Prod.fst <| (r) + q\n"
                   "def p2 (p : ℕ × (ℕ × ℕ)) : ℕ := let r := p.2; Prod.fst <| r |> f\n"
                   "def q2 (p : ℕ × (ℕ × ℕ)) : ℕ := let r := p.2; Prod.fst <| r x\n"
                   "def s2 (p : ℕ × (ℕ × ℕ)) : ℕ := let r := p.2; r |> Prod.fst ∘ Prod.swap\n"
                   "def t2 (p : ℕ × (ℕ × ℕ)) : ℕ := let r := p.2; r |> Prod.fst + 1\n"), [])
        # Tight prefix `Prod.fst r + q` and `Prod.fst $ r` still count as alias chains.
        self.assertEqual(
            chains("def a (p : ℕ × (ℕ × ℕ)) : ℕ := let r := p.2; Prod.fst r\n"
                   "def b (p : ℕ × (ℕ × ℕ)) : ℕ := let r := p.2; Prod.fst r + 1\n"
                   "def c (p : ℕ × (ℕ × ℕ)) : ℕ := let r := p.2; Prod.fst $ r\n"
                   "def d (p : ℕ × (ℕ × ℕ)) : ℕ := let r := p.2; (Prod.fst <| r : ℕ)\n"),
            ["Prod.fst r (via let r := ….2)"] * 4)
        # Shadowing by fun, forall, match pattern, let :=, let ←, destructuring let, set-builder.
        self.assertEqual(
            chains("def a (p : ℕ × (ℕ × ℕ)) := let r := p.2; fun r : ℕ × ℕ => r.1\n"
                   "def b (p : ℕ × (ℕ × ℕ)) := let r := p.2; fun (r, _) => r.1\n"
                   "def c (p : ℕ × (ℕ × ℕ)) := let r := p.2; ∀ r : ℕ × ℕ, r.1 = 0\n"
                   "def d (p : ℕ × (ℕ × ℕ)) := let r := p.2; let r := q; r.1\n"
                   "def e (p : ℕ × (ℕ × ℕ)) := let r := p.2; let r ← m; r.1\n"
                   "def g (p : ℕ × (ℕ × ℕ)) := let r := p.2; let (r, s) := q; r.1\n"
                   "def h (p : ℕ × (ℕ × ℕ)) := let r := p.2; let (r, s) ← m; r.1\n"
                   "def i (p : ℕ × (ℕ × ℕ)) := let r := p.2; {r | r.1 = 0}\n"
                   "def j (p : ℕ × (ℕ × ℕ)) := let r := p.2; (r : ℕ × ℕ) → r.1 = 0\n"), [])
        # Branch & layout boundaries end inner `let` bindings cleanly.
        self.assertEqual(
            chains("def a := if c then let r := p.2; r.1 else r.2\n"
                   "def b := match x with | none => let r := p.2; r.1 | some _ => r.2\n"
                   "def c := (let r := p.2; r.1, r.2)\n"
                   "def d :=\n  let y :=\n    let r := p.2\n    r.1\n  y + r.2\n"
                   "def e := do\n  if c then\n    let r := p.2\n    f r.1\n  return r.2\n"),
            ["r.1 (via let r := ….2)"] * 5)
        # Exempt inside proofs and efficiency predicates.
        self.assertEqual(
            chains("theorem t : ComputableInPolyTime (fun p => let r := p.2; r.1) e e := sorry\n"
                   "theorem u : True := by\n  let r := p.2\n  exact r.1\n"), [])


class RatchetTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.write("CslibFrontier/A.lean", self.module(2))
        self.write("CslibFrontier/B.lean", self.module(1))
        self.write("scripts/projection_chains_baseline.json",
                   json.dumps({"CslibFrontier/A.lean": 2, "CslibFrontier/B.lean": 1}))
        self.git("add", ".")
        self.git("commit", "-qm", "base")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    @staticmethod
    def module(n: int) -> str:
        return HEADER + "".join(f"theorem t{i} (c : (ℕ × ℕ) × ℕ) : c.1.2 = 0 := sorry\n"
                                for i in range(n))

    def git(self, *args: str) -> str:
        return subprocess.check_output(["git", *args], cwd=self.root, text=True)

    def write(self, rel: str, text: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def run_main(self, *args: str) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = c.main([*args, "--root", str(self.root)])
        return code, out.getvalue(), err.getvalue()

    def baseline(self) -> dict[str, int]:
        return json.loads((self.root / "scripts/projection_chains_baseline.json").read_text())

    def test_a_changed_module_may_not_add_chains(self) -> None:
        self.write("CslibFrontier/A.lean", self.module(3))
        code, _, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/A.lean: 3 chain(s), baseline 2:", err)
        self.assertIn("CslibFrontier/A.lean:10: t2: `.1.2`", err)

    def test_a_new_module_starts_at_zero(self) -> None:
        self.write("CslibFrontier/New.lean", self.module(1))
        self.assertEqual(self.run_main()[0], 1)
        self.write("CslibFrontier/New.lean", HEADER + "theorem t (p : ℕ × ℕ) : p.1 = p.1 := rfl\n")
        self.assertEqual(self.run_main()[0], 0)

    def test_fewer_chains_pass_with_a_note_and_the_baseline_comes_down(self) -> None:
        self.write("CslibFrontier/A.lean", self.module(1))
        code, out, _ = self.run_main()
        self.assertEqual(code, 0)
        self.assertIn("CslibFrontier/A.lean: 1 (baseline 2)", out)
        self.assertEqual(self.run_main("--update-baseline")[0], 0)
        self.assertEqual(self.baseline(), {"CslibFrontier/A.lean": 1, "CslibFrontier/B.lean": 1})
        # A deleted module's entry goes away.
        (self.root / "CslibFrontier/B.lean").unlink()
        self.assertEqual(self.run_main("--update-baseline")[0], 0)
        self.assertEqual(self.baseline(), {"CslibFrontier/A.lean": 1})

    def test_removed_chains_need_no_baseline_edit(self) -> None:
        self.write("CslibFrontier/A.lean", self.module(1))
        code, out, _ = self.run_main()
        self.assertEqual(code, 0)
        self.assertIn("No baseline edit is needed", out)
        self.assertNotIn("Lower them", out)

    def make_stale(self) -> None:
        """`main` removes a chain from A without lowering A's entry, 2."""
        self.write("CslibFrontier/A.lean", self.module(1))
        self.git("commit", "-qam", "remove a chain")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    def test_chains_cannot_return_under_a_stale_entry(self) -> None:
        self.make_stale()
        self.write("CslibFrontier/A.lean", self.module(2))
        code, _, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/A.lean: 2 chain(s), limit 1 (the count at the merge base; "
                      "baseline 2):", err)
        self.assertIn("  CslibFrontier/A.lean: above 2", err)
        self.assertEqual(self.run_main("--all")[0], 0)  # the entry alone still allows 2

    def test_a_re_add_under_a_stale_entry_needs_a_raise_by_hand(self) -> None:
        self.make_stale()
        self.write("CslibFrontier/A.lean", self.module(2))
        # Recording the count would leave the entry at 2, still capped at 1: refuse, write nothing.
        for args in (("--update-baseline",), ("--update-baseline", "--allow-increase")):
            with self.subTest(args=args):
                code, _, err = self.run_main(*args)
                self.assertEqual(code, 1)
                self.assertIn("raise the entry by hand above its value at the merge base", err)
                self.assertIn("  CslibFrontier/A.lean: above 2", err)
                self.assertEqual(self.baseline()["CslibFrontier/A.lean"], 2)
        self.write("scripts/projection_chains_baseline.json",
                   json.dumps({"CslibFrontier/A.lean": 3, "CslibFrontier/B.lean": 1}))
        self.assertEqual(self.run_main()[0], 0)

    def test_an_entry_the_change_raises_is_its_limit(self) -> None:
        self.make_stale()
        self.write("CslibFrontier/A.lean", self.module(3))
        self.write("scripts/projection_chains_baseline.json",
                   json.dumps({"CslibFrontier/A.lean": 3, "CslibFrontier/B.lean": 1}))
        self.assertEqual(self.run_main()[0], 0)
        # A lowered entry stays capped at the count at the merge base.
        self.write("scripts/projection_chains_baseline.json",
                   json.dumps({"CslibFrontier/A.lean": 2, "CslibFrontier/B.lean": 1}))
        self.write("CslibFrontier/A.lean", self.module(2))
        self.assertEqual(self.run_main()[0], 1)

    def test_a_moved_module_needs_a_raised_entry(self) -> None:
        (self.root / "CslibFrontier/B.lean").rename(self.root / "CslibFrontier/C.lean")
        code, _, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/C.lean: 1 chain(s), baseline 0:", err)
        self.assertEqual(self.run_main("--update-baseline", "--allow-increase")[0], 0)
        self.assertEqual(self.baseline(), {"CslibFrontier/A.lean": 2, "CslibFrontier/C.lean": 1})
        self.assertEqual(self.run_main()[0], 0)

    def test_untouched_modules_are_only_enforced_with_all(self) -> None:
        self.write("CslibFrontier/B.lean", self.module(2))
        self.git("commit", "-qam", "drift")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.assertEqual(self.run_main()[0], 0)
        self.assertEqual(self.run_main("--all")[0], 1)
        code, out, _ = self.run_main("--report")
        self.assertEqual(code, 0)
        self.assertIn("CslibFrontier/B.lean: 2 chain(s), baseline 1:", out)

    def test_the_baseline_only_goes_up_on_request(self) -> None:
        self.write("CslibFrontier/A.lean", self.module(3))
        code, _, err = self.run_main("--update-baseline")
        self.assertEqual(code, 1)
        self.assertIn("--allow-increase", err)
        self.assertEqual(self.baseline()["CslibFrontier/A.lean"], 2)
        self.assertEqual(self.run_main("--update-baseline", "--allow-increase")[0], 0)
        self.assertEqual(self.baseline()["CslibFrontier/A.lean"], 3)

    def test_the_whole_baseline_regenerates(self) -> None:
        (self.root / "scripts/projection_chains_baseline.json").unlink()
        self.assertEqual(self.run_main("--update-baseline", "--all", "--allow-increase")[0], 0)
        self.assertEqual(self.baseline(), {"CslibFrontier/A.lean": 2, "CslibFrontier/B.lean": 1})

    def test_a_new_module_rejects_prod_and_let_workarounds(self) -> None:
        self.write("CslibFrontier/ProdBypass.lean",
                   HEADER + "theorem t (p : ℕ × (ℕ × ℕ)) : Prod.fst (Prod.snd p) = 0 := sorry\n")
        code, _, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/ProdBypass.lean: 1 chain(s), baseline 0:", err)
        self.assertIn("Prod.fst (Prod.snd …)", err)
        (self.root / "CslibFrontier/ProdBypass.lean").unlink()
        self.write("CslibFrontier/LetBypass.lean",
                   HEADER + "def f (p : ℕ × (ℕ × ℕ)) : ℕ :=\n  let rest := p.2\n  rest.1\n")
        code, _, err = self.run_main()
        self.assertEqual(code, 1)
        self.assertIn("CslibFrontier/LetBypass.lean: 1 chain(s), baseline 0:", err)
        self.assertIn("rest.1 (via let rest := ….2)", err)

    def test_list(self) -> None:
        code, out, _ = self.run_main("--list", "CslibFrontier/A.lean")
        self.assertEqual(code, 0)
        self.assertTrue(out.startswith("2 counted projection chain(s) in 1 module(s)."))
        self.assertIn("CslibFrontier/A.lean:8: t0: `.1.2`", out)


class RepositoryTests(unittest.TestCase):
    def test_the_checked_in_baseline_is_well_formed(self) -> None:
        baseline = c.load_baseline(c.BASELINE)
        self.assertEqual(c.BASELINE.read_text(), c.baseline_text(baseline))


if __name__ == "__main__":
    unittest.main()
