/-
Copyright (c) 2026 OpenAI, Andrew Barnes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Andrew Barnes
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polyhedra.RationalHPolytope
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The polynomial Hirsch conjecture and the statements refuting it

The polynomial Hirsch conjecture asks for a polynomial bound, in the number of facets, on the
graph diameter of polytopes. This module states it for bounded simple rational polytopes
(`Cslib.Polyhedra.Hirsch.PolynomialHirsch`), states the two theorems of [OpenAI2026Hirsch] that
refute it (`Cslib.Polyhedra.Hirsch.MainTheorem`, `Cslib.Polyhedra.Hirsch.ExcessTheorem`), and
proves that the first implies the negation of the conjecture
(`Cslib.Polyhedra.Hirsch.not_polynomialHirsch_of_main`). Neither theorem is proved here: they are
definitions of propositions.

## Main definitions

* `Cslib.Polyhedra.Hirsch.Subpolynomial`, `Cslib.Polyhedra.Hirsch.Superpolynomial`: growth
  `n^{o(1)}` and `n^{ω(1)}` of a sequence of natural numbers.
* `Cslib.Polyhedra.Hirsch.PolynomialHirsch`: the polynomial Hirsch conjecture for bounded simple
  rational polytopes.
* `Cslib.Polyhedra.Hirsch.MainTheorem`: the statement of [OpenAI2026Hirsch, Theorem 1.1].
* `Cslib.Polyhedra.Hirsch.ExcessTheorem`: the statement of [OpenAI2026Hirsch, Theorem 1.2].

## Main results

* `Cslib.Polyhedra.Hirsch.not_polynomialHirsch_of_main`: `MainTheorem` implies that the
  polynomial Hirsch conjecture fails.

## Implementation notes

This is a port of part of
[`Statements.lean`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Geometry/Hirsch/Statements.lean)
from the Lean formalization accompanying [OpenAI2026Hirsch] (source revision `3344da5`).
The declarations `Subpolynomial`, `Superpolynomial`, `Example`, `MainTheorem`, `ExcessTheorem`,
`PolynomialHirsch` and `not_polynomialHirsch_of_main` move from `OAI.Geometry.Hirsch` to
`Cslib.Polyhedra.Hirsch` under the same names; inside them `Polytope` reads `RationalHPolytope`,
`Simple` reads `IsSimple` and `graph` reads `faceGraph`. The source's `CappedSeed` and `CapLemma`,
intermediate statements of its proof, are not ported.

## References

* [OpenAI2026Hirsch]
-/

@[expose] public section

open Filter

namespace Cslib.Polyhedra.Hirsch

/-- A sequence of natural numbers is **subpolynomial**, `n^{o(1)}`: for every `ε > 0` it is
eventually at most `n^ε`. -/
def Subpolynomial (seq : ℕ → ℕ) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∀ᶠ n : ℕ in atTop, (seq n : ℝ) ≤ (n : ℝ) ^ eps

/-- A sequence of natural numbers is **superpolynomial**, `n^{ω(1)}`: for every real exponent `e` it
is eventually at least `n^e`. -/
def Superpolynomial (seq : ℕ → ℕ) : Prop :=
  ∀ exponent : ℝ, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ exponent ≤ (seq n : ℝ)

/-- A bounded rational polytope given by inequalities together with a linear objective: the
members of the families in `MainTheorem`. -/
structure Example where
  /-- The polytope. -/
  poly : RationalHPolytope
  /-- The objective. -/
  obj : poly.Objective

/-- The statement of [OpenAI2026Hirsch, Theorem 1.1] (superpolynomial diameter). For every
positive subpolynomial number of moves `s(n)` (`moves`) there are, for every sufficiently large
`n`, bounded simple rational polytopes `P_n` with connected graphs, exactly `n` facets and
subpolynomial dimension, with linear objectives `x`, such that

* the vertices minimizing and maximizing `x` are at superpolynomial distance in the face graph of
  level `s(n)` (the source states that the `s(n)`-move diameter is superpolynomial; the distance
  between these two vertices bounds the diameter from below, so this form is at least as strong);
* for every fixed `0 < α < 1`, any two vertices whose values of `x` differ by at least `n^{-α}`
  times the range of `x` are at superpolynomial distance at level `s(n)`.

The family is total in `n`; only its members for large `n` are constrained, as the source's "for
every sufficiently large `n`" says. "Simple" is `IsSimple` of the body, the dimension is the
affine dimension of the body, and the facet count counts geometric facets, not inequalities. -/
def MainTheorem : Prop :=
  ∀ moves : ℕ → ℕ, (∀ n, 0 < moves n) → Subpolynomial moves →
    ∃ family : ℕ → Example,
      (∀ᶠ n in atTop, let poly := (family n).poly
        IsSimple poly.body ∧ (faceGraph poly.body 1).Connected ∧ poly.facetCount = n) ∧
      Subpolynomial (fun n => (family n).poly.dimension) ∧
      Superpolynomial (fun n => (family n).poly.dist (moves n)
        (family n).obj.high (family n).obj.low) ∧
      ∀ alpha : ℝ, 0 < alpha → alpha < 1 → ∀ exponent : ℝ, ∀ᶠ n : ℕ in atTop,
        ∀ first last : (family n).poly.V, (n : ℝ) ^ (-alpha) ≤ (family n).obj.gap first last →
          (n : ℝ) ^ exponent ≤ (family n).poly.dist (moves n) first last

/-- The statement of [OpenAI2026Hirsch, Theorem 1.2] (prescribed dimension and facet excess). For
all `a, b > 0` there are `c, δ > 0` such that for all `d` and `E` with `m = min d E` sufficiently
large, some bounded simple rational polytope of dimension `d` with exactly `d + E` facets (and
connected graph) has two vertices at distance at least `c · E · min (E^a) (d^b)` in the face graph
of level `⌊m^δ⌋`. -/
def ExcessTheorem : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → ∃ c delta : ℝ, 0 < c ∧ 0 < delta ∧
    ∃ threshold : ℕ, ∀ d excess : ℕ, threshold ≤ min d excess →
      ∃ poly : RationalHPolytope, IsSimple poly.body ∧ (faceGraph poly.body 1).Connected ∧
        poly.dimension = d ∧ poly.facetCount = d + excess ∧
        ∃ first last : poly.V,
          c * excess * min ((excess : ℝ) ^ a) ((d : ℝ) ^ b) ≤
            poly.dist ⌊((min d excess : ℕ) : ℝ) ^ delta⌋₊ first last

/-- The **polynomial Hirsch conjecture** for bounded simple rational polytopes: the distance
between any two vertices of the graph is at most a fixed polynomial in the number of facets. The
conjecture is usually stated for all polytopes; restricting it to bounded simple rational
polytopes with connected graphs only weakens it, so its negation is the stronger statement. -/
def PolynomialHirsch : Prop :=
  ∃ coeff power : ℕ, ∀ poly : RationalHPolytope, IsSimple poly.body →
    (faceGraph poly.body 1).Connected →
    ∀ first last : poly.V, poly.dist 1 first last ≤ coeff * (poly.facetCount + 1) ^ power

/-- A step, not the refutation itself: `MainTheorem` ([OpenAI2026Hirsch, Theorem 1.1]), which is
not proved here, implies that the polynomial Hirsch conjecture fails. This is the deduction stated
after Theorem 1.1 in [OpenAI2026Hirsch]: take `s(n) = 1`. -/
theorem not_polynomialHirsch_of_main (main : MainTheorem) : ¬ PolynomialHirsch := by
  rintro ⟨coeff, power, bound⟩
  have sub : Subpolynomial (fun _ => 1) := by
    intro eps he
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa using Real.one_le_rpow (show (1 : ℝ) ≤ n by exact_mod_cast hn) he.le
  obtain ⟨family, hf, _, hg, _⟩ := main _ (fun _ => Nat.zero_lt_one) sub
  obtain ⟨n, ⟨hs, hc, he⟩, hd, hn⟩ :=
    (hf.and ((hg (power + 1 : ℕ)).and (eventually_gt_atTop (coeff * 2 ^ power)))).exists
  rw [Real.rpow_natCast] at hd
  have lower :
      n ^ (power + 1) ≤ (family n).poly.dist 1 (family n).obj.high (family n).obj.low := by
    exact_mod_cast hd
  have upper := bound _ hs hc (family n).obj.high (family n).obj.low
  rw [he] at upper
  have hpos : 0 < n := by omega
  apply (lower.trans upper).not_gt
  calc
    coeff * (n + 1) ^ power ≤ coeff * (2 * n) ^ power := by gcongr; omega
    _ = (coeff * 2 ^ power) * n ^ power := by rw [mul_pow, mul_assoc]
    _ < n * n ^ power := Nat.mul_lt_mul_of_pos_right hn (pow_pos hpos _)
    _ = n ^ (power + 1) := by rw [pow_succ']

end Cslib.Polyhedra.Hirsch
