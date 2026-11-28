/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Algebra.Polynomial.Bivariate
public import CslibFrontier.Foundations.Data.Code.ReedSolomon
public import CslibFrontier.Foundations.Data.Code.SudanInterpolant
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.Positivity

/-!
# Guruswami–Sudan list decoding for Reed–Solomon codes

Let `w : ι → F` be a received word on `n = |ι|` distinct evaluation points `α : ι → F` over an
arbitrary field `F` (of any characteristic). The Guruswami–Sudan list decoder
[GuruswamiSudan1999], [GuruswamiRudraSudan2019, §§12.2.3–12.2.4, Definitions 12.2.8–9,
Algorithm 12.2.3, Lemmas 12.2.10–11, and Theorem 12.2.12 (pp. 253–259)] strengthens Sudan's decoder
(`Cslib.Code.sudan`) by requiring the bivariate interpolant `Q(X, Y) ∈ F[X][Y]` of
`(1, d)`-weighted degree at most `D` to vanish to multiplicity at least `m` (or per-point
multiplicity `mult i`) at every point `(α i, w i)`.

The underlying polynomial algebra — bivariate Taylor shifts (`Polynomial.Bivariate.shift`),
bivariate Hasse derivatives (`Polynomial.Bivariate.hasseDerivBiv`), characteristic-independent
multiplicity-`m` vanishing (`Polynomial.Bivariate.VanishesToOrder`), `(1, d)`-weighted degree
(`Polynomial.Bivariate.weightedDegree`), and primitive/square-free/irreducible factor refinement —
lives in `CslibFrontier.Foundations.Algebra.Polynomial.Bivariate`. The bounded-monomial linear
system and least-`Y`-degree elimination machinery
(`Cslib.Code.Sudan.exists_weightedDegreeLE_eq_zero`, `Cslib.Code.Sudan.minDegPoly`) are shared with
`CslibFrontier.Foundations.Data.Code.SudanInterpolant`.

Each point with multiplicity `mult i` imposes `mult i * (mult i + 1) / 2` homogeneous linear
equations on the coefficients of `Q` (`Cslib.Code.GuruswamiSudan.card_multPairs`), so a nonzero
weighted-multiplicity interpolant (`Cslib.Code.GuruswamiSudan.IsWeightedInterpolant`) exists
whenever `∑ i, mult i * (mult i + 1) / 2 < #(Sudan.monomials d D)`
(`Cslib.Code.GuruswamiSudan.exists_isWeightedInterpolant`). Specializing to a constant profile
`fun _ => m` gives uniform multiplicity-`m` interpolants (`Cslib.Code.GuruswamiSudan.IsInterpolant`,
`Cslib.Code.GuruswamiSudan.exists_isInterpolant`), which exist whenever `1 ≤ d` and
`n * d * m * (m + 1) < (D + 1) * (D + 2)` (`Cslib.Code.GuruswamiSudan.exists_isInterpolant_of_lt`).
Instantiating `Cslib.Code.Sudan.minDegPoly` with shifted-coefficient rows
(`Cslib.Code.GuruswamiSudan.shiftEntry`) yields explicit least-`Y`-degree elimination interpolants
(`Cslib.Code.GuruswamiSudan.weightedInterpolant`, `Cslib.Code.GuruswamiSudan.interpolant`)
satisfying `Cslib.Code.GuruswamiSudan.isWeightedInterpolant_weightedInterpolant` and
`Cslib.Code.GuruswamiSudan.natDegree_weightedInterpolant_le`; minimizing `Y`-degree also caps every
polynomial root's multiplicity
(`Cslib.Code.GuruswamiSudan.IsWeightedInterpolant.rootMultiplicity_le_of_min`).
If `P` has `natDegree ≤ d` and `D < ∑ i ∈ {i | P.eval (α i) = w i}, mult i` (in the uniform case
`D < m * #{i | P.eval (α i) = w i}`), then `Q.eval P = 0` and `Y - C P ∣ Q`
(`Cslib.Code.GuruswamiSudan.IsWeightedInterpolant.eval_eq_zero`,
`Cslib.Code.GuruswamiSudan.IsInterpolant.X_sub_C_dvd`).

For Reed–Solomon codes of dimension `k ≥ 2`, `Cslib.Code.guruswamiSudan` achieves list decoding up
to the full Johnson radius `n * (k - 1) < (n - e) ^ 2`
(`Cslib.Code.mem_guruswamiSudan_johnson_iff`), and asymptotically up to `δ = 1 - √ρ - ε` for every
`ε > 0` with multiplicity depending only on `ε` (`Cslib.Code.exists_guruswamiSudan_of_eps`). As in
`Cslib.Code.sudan`, roots in `F[X][Y]` are taken noncomputably via `Polynomial.roots` and no
running time is formalized here.

## Main definitions

* `Cslib.Code.GuruswamiSudan.multPairs`: the `m * (m + 1) / 2` pairs `(r, s)` with `r + s < m`.
* `Cslib.Code.GuruswamiSudan.IsWeightedInterpolant`: per-point multiplicity interpolants for
  arbitrary multiplicity profiles `mult : ι → ℕ`.
* `Cslib.Code.GuruswamiSudan.IsInterpolant`: uniform multiplicity-`m` interpolants, specializing
  `IsWeightedInterpolant` to `fun _ => m`.
* `Cslib.Code.GuruswamiSudan.shiftEntry`: shifted-coefficient matrix entries for linear elimination.
* `Cslib.Code.GuruswamiSudan.weightedInterpolant`, `Cslib.Code.GuruswamiSudan.interpolant`:
  explicit least-`Y`-degree weighted and uniform interpolants via `Sudan.minDegPoly`.
* `Cslib.Code.guruswamiSudan`: the Guruswami–Sudan list decoder for Reed–Solomon codes.

## Main results

* `Cslib.Code.GuruswamiSudan.coeff_coeff_shift_bivariateOf`: shifted coefficients of
  `Sudan.bivariateOf`.
* `Cslib.Code.GuruswamiSudan.card_multPairs`: each point of multiplicity `m` imposes
  `m * (m + 1) / 2` linear constraints.
* `Cslib.Code.GuruswamiSudan.isInterpolant_one_iff_sudan`: multiplicity-`1` interpolants are
  Sudan interpolants.
* `Cslib.Code.GuruswamiSudan.IsWeightedInterpolant.rootMultiplicity_le_of_min`,
  `Cslib.Code.GuruswamiSudan.IsInterpolant.rootMultiplicity_le_of_min`: least-`Y`-degree
  interpolants bound root multiplicity by the maximum interpolation multiplicity.
* `Cslib.Code.GuruswamiSudan.exists_isWeightedInterpolant`,
  `Cslib.Code.GuruswamiSudan.exists_isWeightedInterpolant_min_natDegree`,
  `Cslib.Code.GuruswamiSudan.exists_isInterpolant`,
  `Cslib.Code.GuruswamiSudan.exists_isInterpolant_of_lt`: existence of weighted and uniform
  multiplicity interpolants.
* `Cslib.Code.GuruswamiSudan.IsWeightedInterpolant.eval_eq_zero`,
  `Cslib.Code.GuruswamiSudan.IsWeightedInterpolant.X_sub_C_dvd`,
  `Cslib.Code.GuruswamiSudan.IsInterpolant.eval_eq_zero`,
  `Cslib.Code.GuruswamiSudan.IsInterpolant.X_sub_C_dvd`: root containment from weighted and uniform
  agreement.
* `Cslib.Code.GuruswamiSudan.isWeightedInterpolant_weightedInterpolant`,
  `Cslib.Code.GuruswamiSudan.isInterpolant_interpolant`,
  `Cslib.Code.GuruswamiSudan.natDegree_weightedInterpolant_le`: correctness and least-`Y`-degree
  minimality of the explicit elimination interpolant.
* `Cslib.Code.mem_guruswamiSudan_iff`, `Cslib.Code.mem_guruswamiSudan_iff_of_lt`,
  `Cslib.Code.card_guruswamiSudan_mul_le`, `Cslib.Code.card_guruswamiSudan_le`: completeness,
  soundness, and list-size bounds of `guruswamiSudan`.
* `Cslib.Code.mem_guruswamiSudan_johnson_iff`, `Cslib.Code.exists_guruswamiSudan_of_eps`: list
  decoding up to the exact integer and asymptotic Johnson radii.

## References

* [V. Guruswami and M. Sudan, *Improved Decoding of Reed–Solomon and Algebraic-Geometry Codes*]
  [GuruswamiSudan1999]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of 26 August 2025,
  §§12.2.3–12.2.4, pp. 253–259][GuruswamiRudraSudan2019]
-/

public section

namespace Cslib.Code.GuruswamiSudan

open Finset Polynomial Polynomial.Bivariate
open scoped Polynomial.Bivariate

section Interpolation

variable {F ι : Type*} [Field F]

/-- The `(r, s)` coefficient of `Polynomial.Bivariate.shift x y` on `Sudan.bivariateOf M c`. -/
theorem coeff_coeff_shift_bivariateOf (M : Finset (ℕ × ℕ)) (c : ℕ × ℕ → F) (x y : F) (r s : ℕ) :
    ((shift x y (Sudan.bivariateOf M c)).coeff s).coeff r =
      ∑ m ∈ M, c m * ((m.1.choose r : F) * (m.2.choose s : F) *
        x ^ (m.1 - r) * y ^ (m.2 - s)) := by
  rw [Sudan.bivariateOf, map_sum, finsetSum_coeff, finsetSum_coeff]
  refine sum_congr rfl fun m _ => ?_
  rw [coeff_coeff_shift_monomial]
  ring

/-- The pairs `(r, s)` with `r + s < m`, indexing the multiplicity-`m` vanishing conditions at
each point. -/
def multPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  {rs ∈ range m ×ˢ range m | rs.1 + rs.2 < m}

/-- `(r, s) ∈ multPairs m` iff `r + s < m`. -/
theorem mem_multPairs {m : ℕ} {rs : ℕ × ℕ} : rs ∈ multPairs m ↔ rs.1 + rs.2 < m := by
  simp only [multPairs, mem_filter, mem_product, mem_range]
  omega

/-- Twice the number of multiplicity-`m` pairs is `m * (m + 1)`. -/
theorem two_mul_card_multPairs (m : ℕ) : 2 * #(multPairs m) = m * (m + 1) := by
  induction m with
  | zero =>
    simp [multPairs]
  | succ m ih =>
    have hunion : multPairs (m + 1) = multPairs m ∪ antidiagonal m := by
      ext rs
      simp only [mem_multPairs, mem_union, mem_antidiagonal]
      omega
    have hdisj : Disjoint (multPairs m) (antidiagonal m) :=
      Finset.disjoint_left.2 fun rs h1 h2 => by
        rw [mem_multPairs] at h1; rw [mem_antidiagonal] at h2; omega
    rw [hunion, card_union_of_disjoint hdisj, Finset.Nat.card_antidiagonal, mul_add, ih]
    ring

/-- The number of multiplicity-`m` pairs at each point is `m * (m + 1) / 2`. -/
theorem card_multPairs (m : ℕ) : #(multPairs m) = m * (m + 1) / 2 := by
  have := two_mul_card_multPairs m
  omega

/-- `Q` is a *weighted-multiplicity Guruswami–Sudan interpolant* for the received word `w` at
evaluation points `α`, with per-point multiplicities `mult : ι → ℕ`, weight `d`, and weighted
degree bound `D`: a nonzero bivariate polynomial of `(1, d)`-weighted degree at most `D` vanishing
to order at least `mult i` at each `(α i, w i)`. -/
structure IsWeightedInterpolant (α w : ι → F) (mult : ι → ℕ) (d D : ℕ) (Q : F[X][Y]) : Prop where
  /-- The interpolant is nonzero. -/
  ne_zero : Q ≠ 0
  /-- Every monomial `X ^ a * Y ^ b` of `Q` has `(1, d)`-weighted degree `a + d * b` at most
  `D`. -/
  weightedDegree_le : Sudan.WeightedDegreeLE d D Q
  /-- The interpolant vanishes to order at least `mult i` at each point `(α i, w i)`. -/
  vanishes : ∀ i, VanishesToOrder (mult i) (α i) (w i) Q

/-- `Q` is a *multiplicity-`m` Guruswami–Sudan interpolant* for the received word `w` at evaluation
points `α`, with weight `d` and weighted degree bound `D`: the specialization of
`IsWeightedInterpolant` to the constant multiplicity profile `fun _ => m`. -/
abbrev IsInterpolant (α w : ι → F) (m d D : ℕ) (Q : F[X][Y]) : Prop :=
  IsWeightedInterpolant α w (fun _ => m) d D Q

variable {α w : ι → F} {mult : ι → ℕ} {m d D : ℕ} {Q : F[X][Y]}

/-- The `Y`-degree of a weighted interpolant satisfies `Q.natDegree * d ≤ D`. -/
theorem IsWeightedInterpolant.natDegree_mul_le (hQ : IsWeightedInterpolant α w mult d D Q) :
    Q.natDegree * d ≤ D :=
  hQ.weightedDegree_le.natDegree_mul_le

/-- Multiplicity-`1` Guruswami–Sudan interpolants are Sudan interpolants. -/
theorem isInterpolant_one_iff_sudan :
    IsInterpolant α w 1 d D Q ↔ Sudan.IsInterpolant α w d D Q :=
  ⟨fun h => ⟨h.ne_zero, h.weightedDegree_le,
      fun i => (vanishesToOrder_one_iff (α i) (w i) Q).1 (h.vanishes i)⟩,
    fun h => ⟨h.ne_zero, h.weightedDegree_le,
      fun i => (vanishesToOrder_one_iff (α i) (w i) Q).2 (h.evalEval_eq_zero i)⟩⟩

/-- **Least-`Y`-degree multiplicity bound.** If `Q` is a weighted-multiplicity interpolant of
minimum `Y`-degree and every point multiplicity satisfies `mult i ≤ m`, then no polynomial
`P : F[X]` is a root of `Q` of multiplicity strictly exceeding `m`. -/
theorem IsWeightedInterpolant.rootMultiplicity_le_of_min (hQ : IsWeightedInterpolant α w mult d D Q)
    (hmin : ∀ Q', IsWeightedInterpolant α w mult d D Q' → Q.natDegree ≤ Q'.natDegree)
    (hmult : ∀ i, mult i ≤ m) (P : F[X]) :
    Q.rootMultiplicity P ≤ m := by
  by_contra! hlt
  set r := Q.rootMultiplicity P
  obtain ⟨S, hQS⟩ := pow_rootMultiplicity_dvd Q P
  change Q = (Y - C P) ^ r * S at hQS
  have hS0 : S ≠ 0 := fun h => hQ.ne_zero (by rw [hQS, h, mul_zero])
  let Q' : F[X][Y] := (Y - C P) ^ m * S
  have hQ'0 : Q' ≠ 0 := mul_ne_zero (pow_ne_zero m (X_sub_C_ne_zero P)) hS0
  have hQ'dvd : Q' ∣ Q := by
    rw [hQS]; exact mul_dvd_mul_right (pow_dvd_pow _ hlt.le) S
  have hQ'interp : IsWeightedInterpolant α w mult d D Q' := by
    refine ⟨hQ'0, hQ.weightedDegree_le.of_dvd hQ.ne_zero hQ'dvd, fun i => ?_⟩
    by_cases hi : P.eval (α i) = w i
    · have hm : VanishesToOrder (mult i) (α i) (w i) ((Y - C P) ^ m) :=
        ((vanishesToOrder_one_X_sub_C hi).pow m).mono (by simpa using hmult i)
      simpa only [add_zero] using hm.mul (vanishesToOrder_zero (α i) (w i) S)
    · have hne : ((Y - C P) ^ r).evalEval (α i) (w i) ≠ 0 := by
        rw [evalEval_pow, evalEval_sub, evalEval_X, evalEval_C]
        exact pow_ne_zero r (sub_ne_zero.2 (Ne.symm hi))
      have hSvan : VanishesToOrder (mult i) (α i) (w i) S :=
        VanishesToOrder.of_mul_left_of_evalEval_ne_zero hne (hQS ▸ hQ.vanishes i)
      simpa only [zero_add] using
        (vanishesToOrder_zero (α i) (w i) ((Y - C P) ^ m)).mul hSvan
  have hle := hmin Q' hQ'interp
  have hmon_m : ((Y - C P) ^ m).Monic := (monic_X_sub_C P).pow m
  have hmon_r : ((Y - C P) ^ r).Monic := (monic_X_sub_C P).pow r
  have hdegQ : Q.natDegree = r + S.natDegree := by
    rw [hQS, hmon_r.natDegree_mul' hS0, (monic_X_sub_C P).natDegree_pow, natDegree_X_sub_C, mul_one]
  have hdegQ' : Q'.natDegree = m + S.natDegree := by
    rw [hmon_m.natDegree_mul' hS0, (monic_X_sub_C P).natDegree_pow, natDegree_X_sub_C, mul_one]
  omega

/-- **Least-`Y`-degree multiplicity bound** for uniform multiplicity-`m` interpolants: no
polynomial `P : F[X]` is a root of `Q` of multiplicity strictly exceeding `m`. -/
theorem IsInterpolant.rootMultiplicity_le_of_min (hQ : IsInterpolant α w m d D Q)
    (hmin : ∀ Q', IsInterpolant α w m d D Q' → Q.natDegree ≤ Q'.natDegree) (P : F[X]) :
    Q.rootMultiplicity P ≤ m :=
  IsWeightedInterpolant.rootMultiplicity_le_of_min hQ hmin (fun _ => le_rfl) P

/-- Matrix entry for the `(r, s)`-th shifted coefficient at `(α i, w i)` of the monomial
`X ^ a * Y ^ b`. -/
def shiftEntry (α w : ι → F) (mult : ι → ℕ)
    (row : Σ i : ι, multPairs (mult i)) (ab : ℕ × ℕ) : F :=
  (ab.1.choose (row.2 : ℕ × ℕ).1 : F) * (ab.2.choose (row.2 : ℕ × ℕ).2 : F) *
    α row.1 ^ (ab.1 - (row.2 : ℕ × ℕ).1) * w row.1 ^ (ab.2 - (row.2 : ℕ × ℕ).2)

/-- The shifted-coefficient linear functional paired with `shiftEntry`. -/
private noncomputable def shiftCoeff (α w : ι → F) (mult : ι → ℕ)
    (row : Σ i : ι, multPairs (mult i)) (Q : F[X][Y]) : F :=
  ((shift (α row.1) (w row.1) Q).coeff (row.2 : ℕ × ℕ).2).coeff (row.2 : ℕ × ℕ).1

private theorem shiftCoeff_bivariateOf (α w : ι → F) (mult : ι → ℕ)
    (M : Finset (ℕ × ℕ)) (c : ℕ × ℕ → F) (row : Σ i : ι, multPairs (mult i)) :
    shiftCoeff α w mult row (Sudan.bivariateOf M c) =
      ∑ m ∈ M, c m * shiftEntry α w mult row m :=
  coeff_coeff_shift_bivariateOf M c (α row.1) (w row.1) _ _

variable [Fintype ι]

/-- **Existence of a weighted-multiplicity interpolant.** Whenever the number of monomials of
`(1, d)`-weighted degree at most `D` exceeds `∑ i, mult i * (mult i + 1) / 2`, every received word
has a nonzero weighted-multiplicity interpolant. -/
theorem exists_isWeightedInterpolant (α w : ι → F)
    (hn : ∑ i : ι, mult i * (mult i + 1) / 2 < #(Sudan.monomials d D)) :
    ∃ Q, IsWeightedInterpolant α w mult d D Q := by
  have hcard : Fintype.card (Σ i : ι, multPairs (mult i)) < #(Sudan.monomials d D) := by
    rw [Fintype.card_sigma]
    simpa [Fintype.card_coe, card_multPairs] using hn
  obtain ⟨Q, h0, hwd, hvan⟩ := Sudan.exists_weightedDegreeLE_eq_zero
    (shiftEntry α w mult) (shiftCoeff α w mult) (shiftCoeff_bivariateOf α w mult) hcard
  exact ⟨Q, h0, hwd, fun i r s hrs => hvan ⟨i, ⟨(r, s), mem_multPairs.2 hrs⟩⟩⟩

/-- Existence of a weighted-multiplicity interpolant of least `Y`-degree (valid for all `d`,
including `d = 0`). -/
theorem exists_isWeightedInterpolant_min_natDegree (α w : ι → F)
    (hn : ∑ i : ι, mult i * (mult i + 1) / 2 < #(Sudan.monomials d D)) :
    ∃ Q, IsWeightedInterpolant α w mult d D Q ∧
      ∀ Q', IsWeightedInterpolant α w mult d D Q' → Q.natDegree ≤ Q'.natDegree := by
  classical
  have hex : ∃ n : ℕ, ∃ Q, IsWeightedInterpolant α w mult d D Q ∧ Q.natDegree = n :=
    let ⟨Q, hQ⟩ := exists_isWeightedInterpolant (mult := mult) (d := d) (D := D) α w hn
    ⟨_, Q, hQ, rfl⟩
  obtain ⟨Q, hQ, hdeg⟩ := Nat.find_spec hex
  exact ⟨Q, hQ, fun Q' hQ' => hdeg ▸ Nat.find_min' hex ⟨Q', hQ', rfl⟩⟩

/-- **Existence of a multiplicity-`m` interpolant.** Whenever the number of monomials of
`(1, d)`-weighted degree at most `D` exceeds `|ι| * (m * (m + 1) / 2)`, every received word has a
nonzero multiplicity-`m` interpolant. -/
theorem exists_isInterpolant (α w : ι → F)
    (hn : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials d D)) :
    ∃ Q, IsInterpolant α w m d D Q :=
  exists_isWeightedInterpolant (mult := fun _ => m) α w (by
    simpa [Finset.sum_const, smul_eq_mul] using hn)

/-- **Closed-form existence of a multiplicity-`m` interpolant.** For `d ≥ 1`, whenever
`|ι| * d * m * (m + 1) < (D + 1) * (D + 2)`, there are strictly more monomials of `(1, d)`-weighted
degree at most `D` than multiplicity-`m` constraints, so an interpolant exists. -/
theorem card_mul_lt_card_monomials_of_lt {n m d D : ℕ} (hd : 1 ≤ d)
    (h : n * d * m * (m + 1) < (D + 1) * (D + 2)) :
    n * (m * (m + 1) / 2) < #(Sudan.monomials d D) := by
  have hmon := Sudan.add_one_mul_add_two_le_two_mul_mul_card_monomials hd D
  have heven : 2 * (m * (m + 1) / 2) = m * (m + 1) := by
    rw [← card_multPairs m, two_mul_card_multPairs m]
  have hmul : 2 * d * (n * (m * (m + 1) / 2)) < 2 * d * #(Sudan.monomials d D) := by
    calc 2 * d * (n * (m * (m + 1) / 2))
        = n * d * (2 * (m * (m + 1) / 2)) := by ring
      _ = n * d * m * (m + 1) := by rw [heven]; ring
      _ < (D + 1) * (D + 2) := h
      _ ≤ 2 * d * #(Sudan.monomials d D) := hmon
  exact Nat.lt_of_mul_lt_mul_left hmul

/-- Existence of a multiplicity-`m` interpolant from `|ι| * d * m * (m + 1) < (D + 1) * (D + 2)`. -/
theorem exists_isInterpolant_of_lt (α w : ι → F) (hd : 1 ≤ d)
    (h : Fintype.card ι * d * m * (m + 1) < (D + 1) * (D + 2)) :
    ∃ Q, IsInterpolant α w m d D Q :=
  exists_isInterpolant α w (card_mul_lt_card_monomials_of_lt hd h)

variable [DecidableEq F]

/-- **Weighted multiplicity root containment.** With distinct points `α`, if `P` has
`natDegree ≤ d` and `D < ∑ i ∈ {i | P.eval (α i) = w i}, mult i`, then `Q.eval P = 0` for every
weighted-multiplicity interpolant `Q`. -/
theorem IsWeightedInterpolant.eval_eq_zero (hα : Function.Injective α)
    (hQ : IsWeightedInterpolant α w mult d D Q) {P : F[X]} (hP : P.natDegree ≤ d)
    (hagree : D < ∑ i ∈ {i | P.eval (α i) = w i}, mult i) : Q.eval P = 0 := by
  classical
  by_contra hne
  let agree : Finset ι := {i | P.eval (α i) = w i}
  let ms : Multiset F := ∑ i ∈ agree, Multiset.replicate (mult i) (α i)
  have hle_roots : ms ≤ (Q.eval P).roots := Multiset.le_iff_count.2 fun x => by
    rw [Polynomial.count_roots, Multiset.count_sum']
    by_cases hx : ∃ i ∈ agree, α i = x
    · obtain ⟨i, hi, rfl⟩ := hx
      rw [Finset.sum_eq_single_of_mem i hi fun j _ hji => by
        rw [Multiset.count_replicate, ite_eq_right fun heq => hji (hα heq)],
        Multiset.count_replicate_self]
      exact (le_rootMultiplicity_iff hne).2
        ((hQ.vanishes i).X_sub_C_pow_dvd_eval (mem_filter.1 hi).2)
    · push Not at hx
      rw [Finset.sum_eq_zero fun j hj => by rw [Multiset.count_replicate, ite_eq_right (hx j hj)]]
      exact Nat.zero_le _
  have hcard : ∑ i ∈ agree, mult i ≤ D := by
    calc ∑ i ∈ agree, mult i = ms.card := by
          simp only [ms, Multiset.card_sum, Multiset.card_replicate]
      _ ≤ (Q.eval P).roots.card := Multiset.card_le_card hle_roots
      _ ≤ (Q.eval P).natDegree := Polynomial.card_roots' _
      _ ≤ D := hQ.weightedDegree_le.natDegree_eval_le hP
  exact absurd hcard (not_le.2 hagree)

/-- Under the hypotheses of `IsWeightedInterpolant.eval_eq_zero`, `Y - C P` divides `Q`. -/
theorem IsWeightedInterpolant.X_sub_C_dvd (hα : Function.Injective α)
    (hQ : IsWeightedInterpolant α w mult d D Q) {P : F[X]} (hP : P.natDegree ≤ d)
    (hagree : D < ∑ i ∈ {i | P.eval (α i) = w i}, mult i) : Y - C P ∣ Q :=
  dvd_iff_isRoot.2 (hQ.eval_eq_zero hα hP hagree)

/-- Under the hypotheses of `IsWeightedInterpolant.eval_eq_zero`, `P` is a root of `Q`. -/
theorem IsWeightedInterpolant.mem_roots (hα : Function.Injective α)
    (hQ : IsWeightedInterpolant α w mult d D Q) {P : F[X]} (hP : P.natDegree ≤ d)
    (hagree : D < ∑ i ∈ {i | P.eval (α i) = w i}, mult i) : P ∈ Q.roots :=
  (Polynomial.mem_roots hQ.ne_zero).2 (hQ.eval_eq_zero hα hP hagree)

/-- **Multiplicity root containment.** With distinct points `α`, if `P` has `natDegree ≤ d` and
`D < m * #{i | P.eval (α i) = w i}`, then `Q.eval P = 0` for every multiplicity-`m` interpolant
`Q`. -/
theorem IsInterpolant.eval_eq_zero (hα : Function.Injective α) (hQ : IsInterpolant α w m d D Q)
    {P : F[X]} (hP : P.natDegree ≤ d) (hagree : D < m * #{i | P.eval (α i) = w i}) :
    Q.eval P = 0 :=
  IsWeightedInterpolant.eval_eq_zero hα hQ hP (by
    simpa [Finset.sum_const, smul_eq_mul, mul_comm] using hagree)

/-- **Multiplicity root divisibility.** Under the hypotheses of `IsInterpolant.eval_eq_zero`,
`Y - C P` divides every multiplicity-`m` interpolant `Q`. -/
theorem IsInterpolant.X_sub_C_dvd (hα : Function.Injective α) (hQ : IsInterpolant α w m d D Q)
    {P : F[X]} (hP : P.natDegree ≤ d) (hagree : D < m * #{i | P.eval (α i) = w i}) :
    Y - C P ∣ Q :=
  dvd_iff_isRoot.2 (hQ.eval_eq_zero hα hP hagree)

/-- Under the hypotheses of `IsInterpolant.eval_eq_zero`, `P` is a root of `Q` in `F[X][Y]`. -/
theorem IsInterpolant.mem_roots (hα : Function.Injective α) (hQ : IsInterpolant α w m d D Q)
    {P : F[X]} (hP : P.natDegree ≤ d) (hagree : D < m * #{i | P.eval (α i) = w i}) :
    P ∈ Q.roots :=
  (Polynomial.mem_roots hQ.ne_zero).2 (hQ.eval_eq_zero hα hP hagree)

/-! ### Explicit least-`Y`-degree multiplicity interpolant -/

/-- **An explicit weighted-multiplicity interpolant of least `Y`-degree**, computed by Gaussian
elimination via `Sudan.minDegPoly`. -/
noncomputable def weightedInterpolant (α w : ι → F) (mult : ι → ℕ) (d D : ℕ) : F[X][Y] :=
  Sudan.minDegPoly (shiftEntry α w mult) d D

/-- **An explicit uniform multiplicity-`m` interpolant of least `Y`-degree**, specializing
`weightedInterpolant` to the constant multiplicity profile `fun _ => m`. -/
noncomputable abbrev interpolant (α w : ι → F) (m d D : ℕ) : F[X][Y] :=
  weightedInterpolant α w (fun _ => m) d D

/-- The elimination interpolant always has `(1, d)`-weighted degree at most `D`. -/
theorem weightedDegreeLE_weightedInterpolant (α w : ι → F) (mult : ι → ℕ) (d D : ℕ) :
    Sudan.WeightedDegreeLE d D (weightedInterpolant α w mult d D) :=
  Sudan.weightedDegreeLE_minDegPoly _ _ _

/-- The elimination interpolant always has `Y`-degree at most `D` (for all `d`, including
`d = 0`). -/
theorem natDegree_weightedInterpolant_le_bound (α w : ι → F) (mult : ι → ℕ) (d D : ℕ) :
    (weightedInterpolant α w mult d D).natDegree ≤ D :=
  Sudan.natDegree_minDegPoly_le_bound _ _ _

/-- The elimination interpolant always vanishes to order `mult i` at each `(α i, w i)` (including
when no nonzero interpolant exists and it evaluates to `0`). -/
theorem vanishesToOrder_weightedInterpolant (α w : ι → F) (mult : ι → ℕ) (d D : ℕ) (i : ι) :
    VanishesToOrder (mult i) (α i) (w i) (weightedInterpolant α w mult d D) :=
  fun r s hrs => Sudan.apply_minDegPoly_eq_zero (shiftEntry α w mult) (shiftCoeff α w mult)
    (shiftCoeff_bivariateOf α w mult) d D ⟨i, ⟨(r, s), mem_multPairs.2 hrs⟩⟩

/-- **The elimination interpolant is a weighted-multiplicity interpolant.** For `d ≥ 1` and
strictly more monomials of `(1, d)`-weighted degree at most `D` than multiplicity constraints,
`weightedInterpolant α w mult d D` satisfies `IsWeightedInterpolant α w mult d D`. -/
theorem isWeightedInterpolant_weightedInterpolant (α w : ι → F) {mult : ι → ℕ} {d D : ℕ}
    (hd : 1 ≤ d) (hn : ∑ i : ι, mult i * (mult i + 1) / 2 < #(Sudan.monomials d D)) :
    IsWeightedInterpolant α w mult d D (weightedInterpolant α w mult d D) := by
  obtain ⟨Q₀, hQ₀⟩ := exists_isWeightedInterpolant (mult := mult) (d := d) (D := D) α w hn
  obtain ⟨h0, hwd, hvan⟩ := Sudan.minDegPoly_spec (shiftEntry α w mult) (shiftCoeff α w mult)
    (shiftCoeff_bivariateOf α w mult) hd
    ⟨Q₀, hQ₀.ne_zero, hQ₀.weightedDegree_le,
      fun row => hQ₀.vanishes row.1 _ _ (mem_multPairs.1 row.2.property)⟩
  exact ⟨h0, hwd, fun i r s hrs => hvan ⟨i, ⟨(r, s), mem_multPairs.2 hrs⟩⟩⟩

/-- **The elimination interpolant has least `Y`-degree** among all weighted-multiplicity
interpolants (and in particular, for `mult = fun _ => m`, among all uniform multiplicity-`m`
interpolants). -/
theorem natDegree_weightedInterpolant_le (α w : ι → F) {mult : ι → ℕ} {d D : ℕ} (hd : 1 ≤ d)
    {Q : F[X][Y]} (hQ : IsWeightedInterpolant α w mult d D Q) :
    (weightedInterpolant α w mult d D).natDegree ≤ Q.natDegree :=
  Sudan.natDegree_minDegPoly_le (shiftEntry α w mult) (shiftCoeff α w mult)
    (shiftCoeff_bivariateOf α w mult) hd hQ.ne_zero hQ.weightedDegree_le
    fun row => hQ.vanishes row.1 _ _ (mem_multPairs.1 row.2.property)

/-- **The uniform elimination interpolant is a multiplicity-`m` interpolant.** For `d ≥ 1` and
strictly more monomials of `(1, d)`-weighted degree at most `D` than multiplicity-`m` constraints,
`interpolant α w m d D` satisfies `IsInterpolant α w m d D`. -/
theorem isInterpolant_interpolant (α w : ι → F) {m d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials d D)) :
    IsInterpolant α w m d D (interpolant α w m d D) :=
  isWeightedInterpolant_weightedInterpolant α w hd (by
    simpa [Finset.sum_const, smul_eq_mul] using hn)

end Interpolation

end Cslib.Code.GuruswamiSudan

/-! ### Guruswami–Sudan list decoder for Reed–Solomon codes -/

namespace Cslib.Code

open Finset Polynomial

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]

/-- **Guruswami–Sudan list decoder** [GuruswamiSudan1999], [GuruswamiRudraSudan2019,
Algorithm 12.2.3 (p. 256)] for Reed–Solomon codes of dimension `k`, multiplicity `m`, and
`(1, k - 1)`-weighted degree bound `D`: the roots `P` in `F[X]` of the least-`Y`-degree
multiplicity-`m` interpolant `GuruswamiSudan.interpolant α w m (k - 1) D` that have degree less
than `k` and satisfy `D < m * #{i | P.eval (α i) = w i}`. Roots in `F[X][Y]` are taken
noncomputably via `Polynomial.roots`. -/
noncomputable def guruswamiSudan (α w : ι → F) (m k D : ℕ) : Finset F[X] :=
  {P ∈ (GuruswamiSudan.interpolant α w m (k - 1) D).roots.toFinset |
    P.degree < k ∧ D < m * #{i | P.eval (α i) = w i}}

variable {α w : ι → F} {m k D : ℕ} {P : F[X]}

/-- Every polynomial returned by `guruswamiSudan` has degree less than `k` and satisfies
`D < m * #{i | P.eval (α i) = w i}`. -/
theorem degree_lt_and_lt_mul_card_of_mem_guruswamiSudan (h : P ∈ guruswamiSudan α w m k D) :
    P.degree < k ∧ D < m * #{i | P.eval (α i) = w i} :=
  (mem_filter.1 h).2

/-- The list size of `guruswamiSudan` is at most the `Y`-degree of the elimination interpolant. -/
theorem card_guruswamiSudan_le_natDegree :
    #(guruswamiSudan α w m k D) ≤ (GuruswamiSudan.interpolant α w m (k - 1) D).natDegree :=
  (card_filter_le _ _).trans (Multiset.toFinset_card_le _ |>.trans (card_roots' _))

/-- The list size of `guruswamiSudan` is always at most `D` (including the case `k = 1`). -/
theorem card_guruswamiSudan_le : #(guruswamiSudan α w m k D) ≤ D :=
  card_guruswamiSudan_le_natDegree.trans
    (GuruswamiSudan.natDegree_weightedInterpolant_le_bound _ _ _ _ _)

/-- **List size of the Guruswami–Sudan decoder.** The list size `L` satisfies `L * (k - 1) ≤ D`,
so at most `D / (k - 1)` polynomials are returned when `k ≥ 2`. -/
theorem card_guruswamiSudan_mul_le : #(guruswamiSudan α w m k D) * (k - 1) ≤ D :=
  (Nat.mul_le_mul_right _ card_guruswamiSudan_le_natDegree).trans
    (GuruswamiSudan.weightedDegreeLE_weightedInterpolant
      α w (fun _ => m) (k - 1) D).natDegree_mul_le

/-- **Completeness and soundness of Guruswami–Sudan list decoding.** With distinct points `α`,
`k ≥ 2`, and `|ι| * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D)`, the decoder lists exactly
the polynomials of degree less than `k` with `D < m * #{i | P.eval (α i) = w i}`. -/
theorem mem_guruswamiSudan_iff (hα : Function.Injective α) (hk : 2 ≤ k)
    (hn : Fintype.card ι * (m * (m + 1) / 2) < #(Sudan.monomials (k - 1) D)) :
    P ∈ guruswamiSudan α w m k D ↔ P.degree < k ∧ D < m * #{i | P.eval (α i) = w i} := by
  refine ⟨degree_lt_and_lt_mul_card_of_mem_guruswamiSudan, fun hP => ?_⟩
  have hQ := GuruswamiSudan.isInterpolant_interpolant α w (by omega) hn
  have hPdeg : P.natDegree ≤ k - 1 := by
    rcases eq_or_ne P 0 with rfl | hP0
    · simp
    · have := (natDegree_lt_iff_degree_lt hP0).2 hP.1
      omega
  exact mem_filter.2 ⟨Multiset.mem_toFinset.2 (hQ.mem_roots hα hPdeg hP.2), hP⟩

/-- **Guruswami–Sudan list decoding** [GuruswamiSudan1999], [GuruswamiRudraSudan2019,
Lemmas 12.2.10–11 (pp. 256–257)] under the closed-form condition
`|ι| * (k - 1) * m * (m + 1) < (D + 1) * (D + 2)`. -/
theorem mem_guruswamiSudan_iff_of_lt (hα : Function.Injective α) (hk : 2 ≤ k)
    (hn : Fintype.card ι * (k - 1) * m * (m + 1) < (D + 1) * (D + 2)) :
    P ∈ guruswamiSudan α w m k D ↔ P.degree < k ∧ D < m * #{i | P.eval (α i) = w i} :=
  mem_guruswamiSudan_iff hα hk (GuruswamiSudan.card_mul_lt_card_monomials_of_lt (by omega) hn)

/-- Every Reed–Solomon codeword agreeing with `w` at more than `D / m` points is decoded by
`guruswamiSudan`. -/
theorem exists_mem_guruswamiSudan_of_mem_reedSolomon (hα : Function.Injective α) (hk : 2 ≤ k)
    (hn : Fintype.card ι * (k - 1) * m * (m + 1) < (D + 1) * (D + 2)) {c : ι → F}
    (hc : c ∈ reedSolomon α k) (hagree : D < m * #{i | c i = w i}) :
    ∃ P ∈ guruswamiSudan α w m k D, (fun i => P.eval (α i)) = c := by
  obtain ⟨P, hP, rfl⟩ := mem_reedSolomon.1 hc
  exact ⟨P, (mem_guruswamiSudan_iff_of_lt hα hk hn).2 ⟨hP, hagree⟩, rfl⟩

/-! ### List decoding up to the full Johnson radius -/

/-- Exact integer Johnson-bound parameter choice: whenever `n * d < t ^ 2`, choosing
`m = n * d / (t ^ 2 - n * d) + 1` and `D = m * t - 1` satisfies the Guruswami–Sudan interpolation
inequality `n * d * m * (m + 1) < (D + 1) * (D + 2)`. -/
theorem guruswamiSudan_johnson_ineq {n d t : ℕ} (ht : n * d < t ^ 2) :
    let m := n * d / (t ^ 2 - n * d) + 1
    let D := m * t - 1
    1 ≤ m ∧ D + 1 = m * t ∧ n * d * m * (m + 1) < (D + 1) * (D + 2) := by
  intro m D
  have hpos_Δ : 0 < t ^ 2 - n * d := Nat.sub_pos_of_lt ht
  have ht_pos : 0 < t := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at ht
  have hm_pos : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le _)
  have hmt_pos : 1 ≤ m * t := Nat.mul_pos hm_pos ht_pos
  have hD1 : D + 1 = m * t := Nat.sub_add_cancel hmt_pos
  have hD2 : D + 2 = m * t + 1 := by omega
  have hdiv : n * d < m * (t ^ 2 - n * d) := by
    have hlt := Nat.lt_mul_div_succ (n * d) hpos_Δ
    simpa [m, Nat.mul_comm] using hlt
  have hstep : n * d * (m + 1) < t * (m * t + 1) := by
    have hsq : m * (t ^ 2 - n * d) + m * (n * d) = m * t ^ 2 := by
      rw [← Nat.mul_add, Nat.sub_add_cancel ht.le]
    nlinarith
  refine ⟨hm_pos, hD1, ?_⟩
  rw [hD1, hD2]
  have hmul := Nat.mul_lt_mul_of_pos_left hstep hm_pos
  linarith

/-- **Guruswami–Sudan list decoding up to the exact integer Johnson radius** [GuruswamiSudan1999],
[GuruswamiRudraSudan2019, Theorem 12.2.12 (pp. 257–259)]. With distinct points `α`, `k ≥ 2`, and
`n * (k - 1) < (n - e) ^ 2` (equivalently `e < n - √(n * (k - 1))`), choosing
`m = n * (k - 1) / ((n - e) ^ 2 - n * (k - 1)) + 1` and `D = m * (n - e) - 1`,
`guruswamiSudan α w m k D` lists exactly the polynomials of degree less than `k` whose codeword is
within Hamming distance `e` of `w`. -/
theorem mem_guruswamiSudan_johnson_iff (hα : Function.Injective α) (hk : 2 ≤ k) {e : ℕ}
    (he : Fintype.card ι * (k - 1) < (Fintype.card ι - e) ^ 2) :
    let n := Fintype.card ι
    let m := n * (k - 1) / ((n - e) ^ 2 - n * (k - 1)) + 1
    let D := m * (n - e) - 1
    P ∈ guruswamiSudan α w m k D ↔
      P.degree < k ∧ hammingDist (fun i => P.eval (α i)) w ≤ e := by
  intro n m D
  obtain ⟨hm, hD1, hineq⟩ := guruswamiSudan_johnson_ineq he
  change 1 ≤ m at hm
  change D + 1 = m * (n - e) at hD1
  rw [mem_guruswamiSudan_iff_of_lt hα hk hineq]
  have hne : e ≤ n := by
    by_contra hgt
    rw [Nat.sub_eq_zero_of_le (le_of_not_ge hgt)] at he
    simp at he
  have hcard_sum : #{i | P.eval (α i) = w i} + hammingDist (fun i => P.eval (α i)) w = n :=
    card_filter_eq_add_hammingDist (fun i => P.eval (α i)) w
  refine and_congr_right fun _ => ⟨fun hagree => ?_, fun hdist => ?_⟩
  · change D < m * #{i | P.eval (α i) = w i} at hagree
    have hle : n - e ≤ #{i | P.eval (α i) = w i} := Nat.le_of_mul_le_mul_left (by omega) hm
    omega
  · change D < m * #{i | P.eval (α i) = w i}
    have hmt := Nat.mul_le_mul_left m (show n - e ≤ #{i | P.eval (α i) = w i} by omega)
    omega

/-- **Asymptotic / real Johnson-bound corollary** [GuruswamiSudan1999], [GuruswamiRudraSudan2019,
Theorem 12.2.12 (pp. 257–259)]. For any nonempty set of `n` distinct evaluation points `α`,
dimension `2 ≤ k ≤ n`, and any `ε > 0`, there exist multiplicity `m` (bounded by
`⌊1 / (2 * ε)⌋₊ + 1`, independent of `n` and `k`) and weighted degree `D < m * n` such that for
every received word `w`, `guruswamiSudan α w m k D` recovers every polynomial `P` of degree less
than `k` within relative Hamming distance `1 - √(k / n) - ε`, with list size bounded by
`D / (k - 1)` (in particular
`#(guruswamiSudan α w m k D) ≤ (1 / (2 * ε) + 1) / ((k - 1) / n)`). -/
theorem exists_guruswamiSudan_of_eps [Nonempty ι] (hα : Function.Injective α)
    (hk : 2 ≤ k) (hkn : k ≤ Fintype.card ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ m D : ℕ, 1 ≤ m ∧ m ≤ ⌊1 / (2 * ε)⌋₊ + 1 ∧ D < m * Fintype.card ι ∧
      ∀ (w : ι → F),
        #(guruswamiSudan α w m k D) * (k - 1) ≤ D ∧
        ∀ P : F[X], P.degree < k →
          (hammingDist (fun i => P.eval (α i)) w : ℝ) ≤
            (1 - Real.sqrt ((k : ℝ) / Fintype.card ι) - ε) * Fintype.card ι →
          P ∈ guruswamiSudan α w m k D := by
  set n := Fintype.card ι
  have hn0 : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  set ρ : ℝ := (k : ℝ) / n
  set ρ' : ℝ := ((k - 1 : ℕ) : ℝ) / n
  by_cases hgap : 1 < Real.sqrt ρ + ε
  · refine ⟨1, 0, le_rfl, Nat.le_add_left 1 _, by simpa using hn0, fun w => ?_⟩
    refine ⟨by simpa using card_guruswamiSudan_mul_le (α := α) (w := w) (m := 1) (k := k) (D := 0),
      fun P _ hdist => ?_⟩
    have hnonneg : (0 : ℝ) ≤ hammingDist (fun i => P.eval (α i)) w := Nat.cast_nonneg _
    have hneg : (1 - Real.sqrt ρ - ε) * n < 0 := mul_neg_of_neg_of_pos (by linarith) hnR
    linarith
  · push Not at hgap
    have hρ'pos : 0 < ρ' := div_pos (Nat.cast_pos.2 (by omega)) hnR
    have hρ'leρ : ρ' ≤ ρ := by dsimp only [ρ', ρ]; gcongr; exact_mod_cast Nat.sub_le k 1
    set m : ℕ := ⌊Real.sqrt ρ' / (2 * ε)⌋₊ + 1
    set t : ℕ := ⌈(Real.sqrt ρ + ε) * n⌉₊
    set D : ℕ := m * t - 1
    have hm_pos : 1 ≤ m := Nat.le_add_left 1 _
    have hm_bound : m ≤ ⌊1 / (2 * ε)⌋₊ + 1 := by
      dsimp only [m]; gcongr
      exact Real.sqrt_le_one.2 ((div_le_one hnR).2 (by exact_mod_cast (by omega : k - 1 ≤ n)))
    have ht_ge : (Real.sqrt ρ + ε) * n ≤ (t : ℝ) := Nat.le_ceil _
    have ht_pos : 0 < t := Nat.cast_pos.1 ((mul_pos (by positivity) hnR).trans_le ht_ge)
    have ht_le_n : t ≤ n := Nat.ceil_le.2 (by nlinarith)
    have hD1 : D + 1 = m * t := Nat.sub_add_cancel (Nat.mul_pos hm_pos ht_pos)
    have hD_lt : D < m * n := by have := Nat.mul_le_mul_left m ht_le_n; omega
    have hm_gt : Real.sqrt ρ' / (2 * ε) < (m : ℝ) := by
      simpa [m] using Nat.lt_floor_add_one (Real.sqrt ρ' / (2 * ε))
    have ht_ge' : (Real.sqrt ρ' + ε) * n ≤ (t : ℝ) :=
      (mul_le_mul_of_nonneg_right (by linarith [Real.sqrt_le_sqrt hρ'leρ]) hnR.le).trans ht_ge
    have htsq : (ρ' + 2 * ε * Real.sqrt ρ' + ε ^ 2) * (n : ℝ) ^ 2 ≤ (t : ℝ) ^ 2 := by
      linear_combination pow_le_pow_left₀ (by positivity) ht_ge' 2 -
        (n : ℝ) ^ 2 * Real.sq_sqrt hρ'pos.le
    have hmul_gt : ρ' < (m : ℝ) * (2 * ε * Real.sqrt ρ') := by
      have h2 := mul_lt_mul_of_pos_right ((div_lt_iff₀ (by positivity)).1 hm_gt)
        (Real.sqrt_pos.2 hρ'pos)
      linarith [Real.mul_self_sqrt hρ'pos.le]
    have hnd_eq : (n : ℝ) * ((k - 1 : ℕ) : ℝ) = ρ' * (n : ℝ) ^ 2 := by dsimp only [ρ']; field_simp
    have hstepR :
        (n : ℝ) * ((k - 1 : ℕ) : ℝ) * ((m : ℝ) + 1) < (t : ℝ) * ((m : ℝ) * (t : ℝ) + 1) := by
      have h1 : (n : ℝ) * ((k - 1 : ℕ) : ℝ) <
          (m : ℝ) * ((t : ℝ) ^ 2 - (n : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
        rw [hnd_eq]
        calc ρ' * (n : ℝ) ^ 2 < (m : ℝ) * (2 * ε * Real.sqrt ρ' + ε ^ 2) * (n : ℝ) ^ 2 := by
              gcongr; linarith [(by positivity : (0 : ℝ) < m * ε ^ 2)]
          _ ≤ (m : ℝ) * ((t : ℝ) ^ 2 - ρ' * (n : ℝ) ^ 2) := by rw [mul_assoc]; gcongr; linarith
      cast_nlinarith [ht_pos]
    have hstepN : n * (k - 1) * (m + 1) < t * (m * t + 1) := by exact_mod_cast hstepR
    have hineq : n * (k - 1) * m * (m + 1) < (D + 1) * (D + 2) := by
      rw [show D + 2 = m * t + 1 by omega, hD1]
      linarith [Nat.mul_lt_mul_of_pos_left hstepN hm_pos]
    refine ⟨m, D, hm_pos, hm_bound, hD_lt,
      fun w => ⟨card_guruswamiSudan_mul_le, fun P hP hdist => ?_⟩⟩
    refine (mem_guruswamiSudan_iff_of_lt hα hk hineq).2 ⟨hP, ?_⟩
    have hcard_sumR : (#{i | P.eval (α i) = w i} : ℝ) +
        (hammingDist (fun i => P.eval (α i)) w : ℝ) = n := by
      exact_mod_cast card_filter_eq_add_hammingDist (fun i => P.eval (α i)) w
    have hmt : m * t ≤ m * #{i | P.eval (α i) = w i} :=
      Nat.mul_le_mul_left m (Nat.ceil_le.2 (by linarith))
    omega

end Cslib.Code
