/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.EdgeScores
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Matching
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Raw-sum edge vectors and local Gram-matrix profiles

For a finite loopless cubic multigraph `G` (parallel edges allowed), fix the rational decay rate
`rawRatio = 7071 / 10000` (`2 * rawRatio ^ 2 = 49999041 / 50000000 < 1`) and define the
*raw-sum* edge vector

`rawEdgeVector G q R e = ‖kernelRow H q R (G.src e) + kernelRow H q R (G.tgt e)‖⁻¹ •`
`  (kernelRow H q R (G.src e) + kernelRow H q R (G.tgt e))`

where `H = G.toSimpleGraph`. Normalizing *after* summing the unnormalized vertex kernel rows keeps
coordinate ratios invariant on non-vertex-transitive graphs.

At every interior coordinate `z` (`H.edist u z ≤ R - 2`), the triangle inequality along the edges
of a `3`-edge star around `v` or the `5` edges of an `H`-configuration around a matched edge
`e = (u, v)` restricts the relative distances to `{-1, 0, 1}`, yielding `3 ^ 3 = 27` star profiles
and `3 ^ 5 = 243` matched-pair profiles in exact integer arithmetic. Outside `H.edist u z ≤ R - 2`,
the support lies in at most four spheres `H.edist u z ∈ {R - 1, R, R + 1, R + 2}` of total `ℓ²`
weight `O((2 * rawRatio ^ 2) ^ R) → 0`. Choosing a single universal radius `R` absorbs this
truncation error into the strict rational slack of `7071 / 10000`, producing clean `R`-independent
polynomial Gram-matrix bounds (`IsAdmissibleStar`, `IsAdmissiblePair`) after eliminating vertex
norms via `3 × 3` and `2 × 2` completions of squares.

## Main definitions

* `Cslib.Circuits.Frontier.Gaussian.PairBound.rawRatio`: rational decay ratio `7071 / 10000`.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.rawSum`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.rawEdgeVector`: unnormalized sum of endpoint kernel
  rows and its unit vector.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.IsAdmissibleStar`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.IsAdmissiblePair`: Gram-matrix constraints satisfied
  by the three incident edge vectors of a vertex and the four outer edge vectors of an edge.

## Main results

* `Cslib.Circuits.Frontier.Gaussian.PairBound.norm_rawEdgeVector`,
  `Cslib.Circuits.Frontier.Gaussian.PairBound.rawEdgeVector_apply_eq_zero`: unit norm and
  `R + 1`-locality of `rawEdgeVector`.
* `Cslib.Circuits.Frontier.Gaussian.PairBound.exists_radius_admissible`: existence of a universal
  radius `R` at which every finite loopless cubic multigraph satisfies `IsAdmissibleStar` at every
  vertex and `IsAdmissiblePair` at every edge.
-/

public section

open Filter Finset Real Set
open scoped RealInnerProductSpace Topology

namespace Cslib.Circuits.Frontier.Gaussian.PairBound

/-! ### Raw-sum edge vectors -/

/-- Rational kernel decay ratio `7071 / 10000` (`≈ 1 / √2`, with `2 * rawRatio ^ 2 < 1`). -/
@[expose] noncomputable def rawRatio : ℝ := 7071 / 10000

theorem rawRatio_pos : 0 < rawRatio := by norm_num [rawRatio]

private theorem profileScale_pos (d : ℕ) :
    0 < (7071 : ℝ) ^ 2 * (10000 : ℝ) ^ 2 / rawRatio ^ d :=
  div_pos (by norm_num) (pow_pos rawRatio_pos _)

/-- Unnormalized sum of the kernel rows of the two endpoints of `e` in `G.toSimpleGraph`. -/
noncomputable def rawSum {V E : Type*} (G : Multigraph V E) (q : ℝ) (R : ℕ) (e : E) :
    EuclideanSpace ℝ V :=
  kernelRow G.toSimpleGraph q R (G.src e) + kernelRow G.toSimpleGraph q R (G.tgt e)

/-- Unit vector in the direction of `rawSum G q R e`. -/
noncomputable def rawEdgeVector {V E : Type*} [Fintype V] (G : Multigraph V E) (q : ℝ) (R : ℕ)
    (e : E) : EuclideanSpace ℝ V :=
  ‖rawSum G q R e‖⁻¹ • rawSum G q R e

section RawBasic

variable {V E : Type*} [Fintype V] {G : Multigraph V E}

omit [Fintype V] in
private theorem rawSum_apply (q : ℝ) (R : ℕ) (e : E) (z : V) :
    rawSum G q R e z =
      kernelRow G.toSimpleGraph q R (G.src e) z + kernelRow G.toSimpleGraph q R (G.tgt e) z :=
  rfl

omit [Fintype V] in
private theorem rawSum_nonneg {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (e : E) (z : V) :
    0 ≤ rawSum G q R e z :=
  add_nonneg (kernelRow_nonneg hq R _ z) (kernelRow_nonneg hq R _ z)

private theorem one_le_norm_rawSum {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (e : E) :
    1 ≤ ‖rawSum G q R e‖ := by
  have h1 : 1 ≤ rawSum G q R e (G.src e) := by
    rw [rawSum_apply, kernelRow_self]
    linarith [kernelRow_nonneg (G := G.toSimpleGraph) hq R (G.tgt e) (G.src e)]
  have hsq : 1 ≤ ‖rawSum G q R e‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc (1 : ℝ) ≤ rawSum G q R e (G.src e) ^ 2 := by nlinarith
      _ ≤ ∑ z, rawSum G q R e z ^ 2 :=
        single_le_sum (f := fun z => rawSum G q R e z ^ 2) (fun z _ => sq_nonneg _)
          (mem_univ (G.src e))
  nlinarith [norm_nonneg (rawSum G q R e)]

/-- **Unit norm.** For every `q ≥ 0` and every `R : ℕ`, `rawEdgeVector G q R e` is a unit vector. -/
theorem norm_rawEdgeVector {q : ℝ} (hq : 0 ≤ q) (R : ℕ) (e : E) :
    ‖rawEdgeVector G q R e‖ = 1 := by
  have h := one_le_norm_rawSum (G := G) hq R e
  rw [rawEdgeVector, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (by linarith)]

/-- **Locality.** At an incident vertex `v` of `e`, `rawEdgeVector G q R e` vanishes outside the
closed ball of radius `R + 1` around `v`. -/
theorem rawEdgeVector_apply_eq_zero {q : ℝ} {R : ℕ} {v : V} {e : E} (he : e ∈ G.incidenceSet v)
    {z : V} (hz : z ∉ closedBall G.toSimpleGraph v (R + 1)) :
    rawEdgeVector G q R e z = 0 := by
  have hend (w : V) (hw : e ∈ G.incidenceSet w) :
      kernelRow G.toSimpleGraph q R w z = 0 := by
    have hlt : (R : ℕ∞) < G.toSimpleGraph.edist w z :=
      lt_of_not_ge fun hle => hz (closedBall_subset_of_mem_incidenceSet he hw R hle)
    rw [kernelRow_apply, ite_eq_right_iff.mpr fun h => (hlt.not_ge h).elim]
  have hsum : rawSum G q R e z = 0 := by
    rw [rawSum_apply, hend _ (Or.inl rfl), hend _ (Or.inr rfl), add_zero]
  simp [rawEdgeVector, hsum]

end RawBasic

/-! ### Admissible star and matched-pair Gram conditions -/

section Conditions

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Gram-matrix constraints satisfied by the three `rawEdgeVector`s at a degree-`3` vertex. -/
@[expose] def IsAdmissibleStar (u : Fin 3 → F) : Prop :=
  (∀ i, ‖u i‖ = 1) ∧
  (9428 / 10000 : ℝ) ≤ ⟪u 0, u 1⟫ ∧
  (9428 / 10000 : ℝ) ≤ ⟪u 0, u 2⟫ ∧
  (9428 / 10000 : ℝ) ≤ ⟪u 1, u 2⟫ ∧
  4 * (9571 / 10000 : ℝ) ^ 3 -
      (9571 / 10000) * (⟪u 0, u 1⟫ ^ 2 + ⟪u 0, u 2⟫ ^ 2 + ⟪u 1, u 2⟫ ^ 2) -
      ⟪u 0, u 1⟫ * ⟪u 0, u 2⟫ * ⟪u 1, u 2⟫ ≤ 0

/-- Polynomial `2 × 2` Schur determinant inequality for a sign `σ ∈ {+1, -1}` at
`(α, β, c₂) = (3 / 14, 8 / 35, 1322905 / 1000000)`. -/
@[expose] def schurPairIneq (sab scd sac sbd sad sbc σ : ℝ) : Prop :=
  let c2 : ℝ := 1322905 / 1000000
  let a : ℝ := 3 / 14
  let b : ℝ := 8 / 35
  let rbar := (sac + sbd + sad + sbc) / 4
  let o1 := (sac - sbd + sad - sbc) / 4
  let o2 := (sac - sbd - sad + sbc) / 4
  let tau0 := (sac + sbd - sad - sbc) / 4
  let A1 := c2 - sab
  let A2 := c2 + sab
  let D1 := c2 - scd
  let D2 := c2 + scd
  let M11 := 2 * (a * rbar + σ * b * tau0)
  let M12 := 2 * (a * o2 + σ * b * o1)
  let M21 := 2 * (a * o1 + σ * b * o2)
  let M22 := 2 * (a * tau0 + σ * b * rbar)
  (A2 * (A1 * D1 - M11 ^ 2) - A1 * M21 ^ 2) * (A2 * (A1 * D2 - M12 ^ 2) - A1 * M22 ^ 2) ≤
    (A2 * M11 * M12 + A1 * M21 * M22) ^ 2

/-- Gram-matrix constraints satisfied by the four outer `rawEdgeVector`s `0, 1` (at `src e`) and
`2, 3` (at `tgt e`) of an edge `e` in a loopless cubic multigraph. -/
@[expose] def IsAdmissiblePair (u : Fin 4 → F) : Prop :=
  (∀ i, ‖u i‖ = 1) ∧
  (9428 / 10000 : ℝ) ≤ ⟪u 0, u 1⟫ ∧
  (9428 / 10000 : ℝ) ≤ ⟪u 2, u 3⟫ ∧
  (79998 / 100000 : ℝ) ≤ ⟪u 0, u 2⟫ ∧
  (79998 / 100000 : ℝ) ≤ ⟪u 0, u 3⟫ ∧
  (79998 / 100000 : ℝ) ≤ ⟪u 1, u 2⟫ ∧
  (79998 / 100000 : ℝ) ≤ ⟪u 1, u 3⟫ ∧
  schurPairIneq ⟪u 0, u 1⟫ ⟪u 2, u 3⟫ ⟪u 0, u 2⟫ ⟪u 1, u 3⟫ ⟪u 0, u 3⟫ ⟪u 1, u 2⟫ 1 ∧
  schurPairIneq ⟪u 0, u 1⟫ ⟪u 2, u 3⟫ ⟪u 0, u 2⟫ ⟪u 1, u 3⟫ ⟪u 0, u 3⟫ ⟪u 1, u 2⟫ (-1) ∧
  schurPairIneq ⟪u 2, u 3⟫ ⟪u 0, u 1⟫ ⟪u 0, u 2⟫ ⟪u 1, u 3⟫ ⟪u 1, u 2⟫ ⟪u 0, u 3⟫ 1 ∧
  schurPairIneq ⟪u 2, u 3⟫ ⟪u 0, u 1⟫ ⟪u 0, u 2⟫ ⟪u 1, u 3⟫ ⟪u 1, u 2⟫ ⟪u 0, u 3⟫ (-1)

end Conditions

/-! ### Exact integer profile tables (`27` star profiles and `243` `H`-profiles) -/

/-- Cleared integer powers `7071 ^ 2 * 10000 ^ 2 * (7071 / 10000) ^ (k - 2)` for `k ∈ {0..4}`
corresponding to exponent `d = k - 2 ∈ {-2, -1, 0, 1, 2}`. -/
private def pkInt : Fin 5 → ℤ
  | 0 => 10000000000000000
  | 1 => 7071000000000000
  | 2 => 4999904100000000
  | 3 => 3535432189110000
  | 4 => 2499904100919681

private theorem pkInt_cast (k : Fin 5) :
    (pkInt k : ℝ) = (7071 : ℝ) ^ 2 * (10000 : ℝ) ^ 2 * rawRatio ^ ((k : ℤ) - 2) := by
  fin_cases k <;> norm_num [pkInt, rawRatio, zpow_neg, zpow_ofNat]

private def starEntry (d : Fin 3) : ℤ :=
  pkInt 2 + pkInt ⟨(d : ℕ) + 1, by omega⟩

private theorem star27_int :
    ∀ d1 d2 d3 : Fin 3,
      957104 * (starEntry d1 ^ 2 + starEntry d2 ^ 2 + starEntry d3 ^ 2) ≤
        1000000 * (starEntry d1 * starEntry d2 + starEntry d1 * starEntry d3 +
          starEntry d2 * starEntry d3) := by
  decide

private theorem samePair9_int :
    ∀ d1 d2 : Fin 3,
      942806 * (starEntry d1 ^ 2 + starEntry d2 ^ 2) ≤
        2000000 * (starEntry d1 * starEntry d2) := by
  decide

private def shiftEntry (dv d : Fin 3) : ℤ :=
  pkInt ⟨(dv : ℕ) + 1, by omega⟩ + pkInt ⟨(dv : ℕ) + (d : ℕ), by omega⟩

private theorem crossPair27_int :
    ∀ dv d1 d3 : Fin 3,
      799990 * (starEntry d1 ^ 2 + shiftEntry dv d3 ^ 2) ≤
        2000000 * (starEntry d1 * shiftEntry dv d3) := by
  decide

private def h243Check (dv d1 d2 d3 d4 : Fin 3) : Bool :=
  let fa := starEntry d1
  let fb := starEntry d2
  let fc := shiftEntry dv d3
  let fd := shiftEntry dv d4
  let tw := (fa - fb) * (fc - fd)
  let atw := if 0 ≤ tw then tw else -tw
  decide (70 * 1322909 * (fa ^ 2 + fb ^ 2 + fc ^ 2 + fd ^ 2) ≤
    2000000 * (70 * (fa * fb + fc * fd) + 15 * (fa + fb) * (fc + fd) - 16 * atw))

private theorem h243_int :
    ∀ dv d1 d2 d3 d4 : Fin 3, h243Check dv d1 d2 d3 d4 = true := by
  decide

/-! ### Pointwise interior coordinate identities at `q = rawRatio` -/

private def diffToFin3 (a b : ℕ) : Fin 3 :=
  if b + 1 = a then 0 else if b = a then 1 else 2

private theorem pkInt_step {du dw : ℕ} (h : dw ≤ du + 1 ∧ du ≤ dw + 1) :
    (pkInt ⟨(diffToFin3 du dw : ℕ) + 1, by omega⟩ : ℝ) =
      (7071 : ℝ) ^ 2 * (10000 : ℝ) ^ 2 * rawRatio ^ dw / rawRatio ^ du := by
  have hr := rawRatio_pos
  unfold diffToFin3
  split_ifs with h1 h2
  · subst h1
    change (pkInt 1 : ℝ) = _
    rw [pkInt_cast 1, show ((1 : Fin 5) : ℤ) - 2 = -1 by decide, zpow_neg_one]
    field_simp; ring
  · subst h2
    change (pkInt 2 : ℝ) = _
    rw [pkInt_cast 2, show ((2 : Fin 5) : ℤ) - 2 = 0 by decide, zpow_zero, mul_one]
    field_simp
  · have h3 : dw = du + 1 := by omega
    subst h3
    change (pkInt 3 : ℝ) = _
    rw [pkInt_cast 3, show ((3 : Fin 5) : ℤ) - 2 = 1 by decide, zpow_one]
    field_simp; ring

private theorem pkInt_two_step {du dv dw : ℕ}
    (huv : dv ≤ du + 1 ∧ du ≤ dv + 1) (hvw : dw ≤ dv + 1 ∧ dv ≤ dw + 1) :
    (pkInt ⟨(diffToFin3 du dv : ℕ) + (diffToFin3 dv dw : ℕ), by omega⟩ : ℝ) =
      (7071 : ℝ) ^ 2 * (10000 : ℝ) ^ 2 * rawRatio ^ dw / rawRatio ^ du := by
  have hr := rawRatio_pos
  unfold diffToFin3
  split_ifs
  · have heq : du = dw + 2 := by omega
    subst heq
    change (pkInt 0 : ℝ) = _
    rw [pkInt_cast 0, show ((0 : Fin 5) : ℤ) - 2 = -2 by decide, pow_add]
    norm_num [zpow_neg, rawRatio]; field_simp; norm_num
  · have heq : du = dw + 1 := by omega
    subst heq
    change (pkInt 1 : ℝ) = _
    rw [pkInt_cast 1, show ((1 : Fin 5) : ℤ) - 2 = -1 by decide, zpow_neg_one]
    field_simp; ring
  · have heq : dw = du := by omega
    subst heq
    change (pkInt 2 : ℝ) = _
    rw [pkInt_cast 2, show ((2 : Fin 5) : ℤ) - 2 = 0 by decide, zpow_zero, mul_one]
    field_simp
  · have heq : du = dw + 1 := by omega
    subst heq
    change (pkInt 1 : ℝ) = _
    rw [pkInt_cast 1, show ((1 : Fin 5) : ℤ) - 2 = -1 by decide, zpow_neg_one]
    field_simp; ring
  · have heq : dw = du := by omega
    subst heq
    change (pkInt 2 : ℝ) = _
    rw [pkInt_cast 2, show ((2 : Fin 5) : ℤ) - 2 = 0 by decide, zpow_zero, mul_one]
    field_simp
  · have heq : dw = du + 1 := by omega
    subst heq
    change (pkInt 3 : ℝ) = _
    rw [pkInt_cast 3, show ((3 : Fin 5) : ℤ) - 2 = 1 by decide, zpow_one]
    field_simp; ring
  · have heq : dw = du := by omega
    subst heq
    change (pkInt 2 : ℝ) = _
    rw [pkInt_cast 2, show ((2 : Fin 5) : ℤ) - 2 = 0 by decide, zpow_zero, mul_one]
    field_simp
  · have heq : dw = du + 1 := by omega
    subst heq
    change (pkInt 3 : ℝ) = _
    rw [pkInt_cast 3, show ((3 : Fin 5) : ℤ) - 2 = 1 by decide, zpow_one]
    field_simp; ring
  · have heq : dw = du + 2 := by omega
    subst heq
    change (pkInt 4 : ℝ) = _
    rw [pkInt_cast 4, show ((4 : Fin 5) : ℤ) - 2 = 2 by decide, pow_add]
    norm_num [rawRatio]; field_simp; norm_num

private theorem starEntry_eq {du dw : ℕ} (h : dw ≤ du + 1 ∧ du ≤ dw + 1) :
    (starEntry (diffToFin3 du dw) : ℝ) =
      ((7071 : ℝ) ^ 2 * (10000 : ℝ) ^ 2 / rawRatio ^ du) * (rawRatio ^ du + rawRatio ^ dw) := by
  have hr := rawRatio_pos
  rw [starEntry, Int.cast_add, pkInt_cast 2, show ((2 : Fin 5) : ℤ) - 2 = 0 by decide, zpow_zero,
    mul_one, pkInt_step h]
  field_simp

private theorem shiftEntry_eq {du dv dw : ℕ}
    (huv : dv ≤ du + 1 ∧ du ≤ dv + 1) (hvw : dw ≤ dv + 1 ∧ dv ≤ dw + 1) :
    (shiftEntry (diffToFin3 du dv) (diffToFin3 dv dw) : ℝ) =
      ((7071 : ℝ) ^ 2 * (10000 : ℝ) ^ 2 / rawRatio ^ du) * (rawRatio ^ dv + rawRatio ^ dw) := by
  have hr := rawRatio_pos
  rw [shiftEntry, Int.cast_add, pkInt_step huv, pkInt_two_step huv hvw]
  field_simp

/-! ### Norm elimination by completing squares (`3 × 3` star and `2 × 2` pair) -/

private theorem star_cubic_of_quad {r1 r2 r3 s1 s2 s3 : ℝ}
    (hr1_lo : 0 ≤ r1) (hr1_hi : r1 ≤ 1) (hs3 : 0 < s3)
    (hq : (9571 / 10000 : ℝ) * (s1 ^ 2 + s2 ^ 2 + s3 ^ 2) ≤
      r1 * s1 * s2 + r2 * s1 * s3 + r3 * s2 * s3) :
    4 * (9571 / 10000 : ℝ) ^ 3 - (9571 / 10000) * (r1 ^ 2 + r2 ^ 2 + r3 ^ 2) -
      r1 * r2 * r3 ≤ 0 := by
  set rs : ℝ := 9571 / 10000
  set a : ℝ := 2 * rs
  have ha : 0 < a := by norm_num [a, rs]
  have ha2 : 0 < a ^ 2 - r1 ^ 2 := by
    have : (1 : ℝ) < a := by norm_num [a, rs]
    nlinarith
  have hlhs : a * (a ^ 2 - r1 ^ 2) *
      (a * (s1 ^ 2 + s2 ^ 2 + s3 ^ 2) - 2 * (r1 * s1 * s2 + r2 * s1 * s3 + r3 * s2 * s3)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by dsimp [a, rs] at hq ⊢; linarith)
  have hid : a * (a ^ 2 - r1 ^ 2) *
      (a * (s1 ^ 2 + s2 ^ 2 + s3 ^ 2) - 2 * (r1 * s1 * s2 + r2 * s1 * s3 + r3 * s2 * s3)) =
      (a ^ 2 - r1 ^ 2) * (a * s1 - r1 * s2 - r2 * s3) ^ 2 +
      ((a ^ 2 - r1 ^ 2) * s2 - (r1 * r2 + a * r3) * s3) ^ 2 +
      a * (a ^ 3 - a * (r1 ^ 2 + r2 ^ 2 + r3 ^ 2) - 2 * r1 * r2 * r3) * s3 ^ 2 := by
    ring
  rw [hid] at hlhs
  have hsq1 : 0 ≤ (a ^ 2 - r1 ^ 2) * (a * s1 - r1 * s2 - r2 * s3) ^ 2 := by positivity
  have hsq2 : 0 ≤ ((a ^ 2 - r1 ^ 2) * s2 - (r1 * r2 + a * r3) * s3) ^ 2 := sq_nonneg _
  have hterm : a * (a ^ 3 - a * (r1 ^ 2 + r2 ^ 2 + r3 ^ 2) - 2 * r1 * r2 * r3) * s3 ^ 2 ≤ 0 := by
    linarith
  have hdiv : a ^ 3 - a * (r1 ^ 2 + r2 ^ 2 + r3 ^ 2) - 2 * r1 * r2 * r3 ≤ 0 := by
    by_contra hpos
    have hgt : 0 < a * (a ^ 3 - a * (r1 ^ 2 + r2 ^ 2 + r3 ^ 2) - 2 * r1 * r2 * r3) * s3 ^ 2 :=
      mul_pos (mul_pos ha (not_le.mp hpos)) (sq_pos_of_pos hs3)
    linarith
  have heq : a ^ 3 - a * (r1 ^ 2 + r2 ^ 2 + r3 ^ 2) - 2 * r1 * r2 * r3 =
      2 * (4 * rs ^ 3 - rs * (r1 ^ 2 + r2 ^ 2 + r3 ^ 2) - r1 * r2 * r3) := by
    dsimp [a]; ring
  linarith

private theorem schur_2x2_elim {A1 A2 D1 D2 M11 M12 M21 M22 p1 q1 p2 q2 : ℝ}
    (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hV : 0 < A2 * (A1 * D2 - M12 ^ 2) - A1 * M22 ^ 2)
    (hp2 : 0 < p2)
    (hlin : A1 * p1 ^ 2 + A2 * q1 ^ 2 + D1 * p2 ^ 2 + D2 * q2 ^ 2 -
      2 * (M11 * p1 * p2 + M12 * p1 * q2 + M21 * q1 * p2 + M22 * q1 * q2) ≤ 0) :
    (A2 * (A1 * D1 - M11 ^ 2) - A1 * M21 ^ 2) * (A2 * (A1 * D2 - M12 ^ 2) - A1 * M22 ^ 2) ≤
      (A2 * M11 * M12 + A1 * M21 * M22) ^ 2 := by
  have hmul : A1 * A2 * (A1 * p1 ^ 2 + A2 * q1 ^ 2 + D1 * p2 ^ 2 + D2 * q2 ^ 2 -
      2 * (M11 * p1 * p2 + M12 * p1 * q2 + M21 * q1 * p2 + M22 * q1 * q2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_pos hA1 hA2).le hlin
  have hid1 : A1 * A2 * (A1 * p1 ^ 2 + A2 * q1 ^ 2 + D1 * p2 ^ 2 + D2 * q2 ^ 2 -
      2 * (M11 * p1 * p2 + M12 * p1 * q2 + M21 * q1 * p2 + M22 * q1 * q2)) =
      A2 * (A1 * p1 - (M11 * p2 + M12 * q2)) ^ 2 +
      A1 * (A2 * q1 - (M21 * p2 + M22 * q2)) ^ 2 +
      ((A2 * (A1 * D1 - M11 ^ 2) - A1 * M21 ^ 2) * p2 ^ 2 -
        2 * (A2 * M11 * M12 + A1 * M21 * M22) * p2 * q2 +
        (A2 * (A1 * D2 - M12 ^ 2) - A1 * M22 ^ 2) * q2 ^ 2) := by ring
  rw [hid1] at hmul
  have hs1 : 0 ≤ A2 * (A1 * p1 - (M11 * p2 + M12 * q2)) ^ 2 :=
    mul_nonneg hA2.le (sq_nonneg _)
  have hs2 : 0 ≤ A1 * (A2 * q1 - (M21 * p2 + M22 * q2)) ^ 2 :=
    mul_nonneg hA1.le (sq_nonneg _)
  have hquad2 : (A2 * (A1 * D1 - M11 ^ 2) - A1 * M21 ^ 2) * p2 ^ 2 -
      2 * (A2 * M11 * M12 + A1 * M21 * M22) * p2 * q2 +
      (A2 * (A1 * D2 - M12 ^ 2) - A1 * M22 ^ 2) * q2 ^ 2 ≤ 0 := by linarith
  have hVmul := mul_nonpos_of_nonneg_of_nonpos hV.le hquad2
  have hid2 : (A2 * (A1 * D2 - M12 ^ 2) - A1 * M22 ^ 2) *
      ((A2 * (A1 * D1 - M11 ^ 2) - A1 * M21 ^ 2) * p2 ^ 2 -
        2 * (A2 * M11 * M12 + A1 * M21 * M22) * p2 * q2 +
        (A2 * (A1 * D2 - M12 ^ 2) - A1 * M22 ^ 2) * q2 ^ 2) =
      ((A2 * (A1 * D2 - M12 ^ 2) - A1 * M22 ^ 2) * q2 -
        (A2 * M11 * M12 + A1 * M21 * M22) * p2) ^ 2 +
      (((A2 * (A1 * D1 - M11 ^ 2) - A1 * M21 ^ 2) *
          (A2 * (A1 * D2 - M12 ^ 2) - A1 * M22 ^ 2) -
        (A2 * M11 * M12 + A1 * M21 * M22) ^ 2) * p2 ^ 2) := by ring
  rw [hid2] at hVmul
  by_contra hgt
  have hpos : 0 < (((A2 * (A1 * D1 - M11 ^ 2) - A1 * M21 ^ 2) *
        (A2 * (A1 * D2 - M12 ^ 2) - A1 * M22 ^ 2) -
      (A2 * M11 * M12 + A1 * M21 * M22) ^ 2) * p2 ^ 2) :=
    mul_pos (by linarith) (sq_pos_of_pos hp2)
  linarith [sq_nonneg ((A2 * (A1 * D2 - M12 ^ 2) - A1 * M22 ^ 2) * q2 -
    (A2 * M11 * M12 + A1 * M21 * M22) * p2)]

private theorem schurPairIneq_of_quad {sab scd sac sbd sad sbc σ sa sb sc sd : ℝ}
    (hsab_lo : (9428 / 10000 : ℝ) ≤ sab) (hsab_hi : sab ≤ 1)
    (hscd_lo : (9428 / 10000 : ℝ) ≤ scd)
    (hsac_lo : (79998 / 100000 : ℝ) ≤ sac) (hsac_hi : sac ≤ 1)
    (hsbd_lo : (79998 / 100000 : ℝ) ≤ sbd) (hsbd_hi : sbd ≤ 1)
    (hsad_lo : (79998 / 100000 : ℝ) ≤ sad) (hsad_hi : sad ≤ 1)
    (hsbc_lo : (79998 / 100000 : ℝ) ≤ sbc) (hsbc_hi : sbc ≤ 1)
    (hσ : σ = 1 ∨ σ = -1) (hsc_pos : 1 ≤ sc) (hsd_pos : 1 ≤ sd)
    (hq : (1322905 / 1000000 : ℝ) / 2 * (sa ^ 2 + sb ^ 2 + sc ^ 2 + sd ^ 2) ≤
      (sa * sb * sab + sc * sd * scd) +
      (3 / 14 : ℝ) * (sa * sc * sac + sa * sd * sad + sb * sc * sbc + sb * sd * sbd) +
      σ * (8 / 35 : ℝ) * (sa * sc * sac - sa * sd * sad - sb * sc * sbc + sb * sd * sbd)) :
    schurPairIneq sab scd sac sbd sad sbc σ := by
  unfold schurPairIneq
  dsimp only
  refine schur_2x2_elim (p1 := sa + sb) (q1 := sa - sb) (p2 := sc + sd) (q2 := sc - sd)
    (by linarith) (by linarith) ?_ (by linarith) ?_
  · -- `0 < V` on the admissible box `[0.9428, 1]² × [0.79998, 1]⁴`.
    have hm12 : (2 * ((3 / 14 : ℝ) * ((sac - sbd - sad + sbc) / 4) +
        σ * (8 / 35 : ℝ) * ((sac - sbd + sad - sbc) / 4))) ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := by
      rw [sq_le_sq, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10), abs_le]
      rcases hσ with rfl | rfl <;> (constructor <;> linarith)
    have hm22 : (2 * ((3 / 14 : ℝ) * ((sac + sbd - sad - sbc) / 4) +
        σ * (8 / 35 : ℝ) * ((sac + sbd + sad + sbc) / 4))) ^ 2 ≤ (51 / 100 : ℝ) ^ 2 := by
      rw [sq_le_sq, abs_of_pos (by norm_num : (0 : ℝ) < 51 / 100), abs_le]
      rcases hσ with rfl | rfl <;> (constructor <;> linarith)
    have hprod1 : (73 / 100 : ℝ) ≤ (1322905 / 1000000 - sab) * (1322905 / 1000000 + scd) := by
      calc (73 / 100 : ℝ) ≤ (1322905 / 1000000 - 1) * (1322905 / 1000000 + 9428 / 10000) := by
            norm_num
        _ ≤ (1322905 / 1000000 - sab) * (1322905 / 1000000 + scd) :=
            mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
    have hprod2 : (1322905 / 1000000 - sab) *
        (2 * ((3 / 14 : ℝ) * ((sac + sbd - sad - sbc) / 4) +
          σ * (8 / 35 : ℝ) * ((sac + sbd + sad + sbc) / 4))) ^ 2 ≤ 11 / 100 := by
      calc (1322905 / 1000000 - sab) *
            (2 * ((3 / 14 : ℝ) * ((sac + sbd - sad - sbc) / 4) +
              σ * (8 / 35 : ℝ) * ((sac + sbd + sad + sbc) / 4))) ^ 2
          ≤ (1322905 / 1000000 - 9428 / 10000) * (51 / 100 : ℝ) ^ 2 :=
            mul_le_mul (by linarith) hm22 (sq_nonneg _) (by norm_num)
        _ ≤ 11 / 100 := by norm_num
    have hprod3 : (226 / 100 : ℝ) * (72 / 100) ≤
        (1322905 / 1000000 + sab) * ((1322905 / 1000000 - sab) * (1322905 / 1000000 + scd) -
          (2 * ((3 / 14 : ℝ) * ((sac - sbd - sad + sbc) / 4) +
            σ * (8 / 35 : ℝ) * ((sac - sbd + sad - sbc) / 4))) ^ 2) :=
      mul_le_mul (by linarith) (by norm_num at hm12; linarith) (by norm_num) (by linarith)
    linarith
  · -- Linear identity relating `(p1, q1, p2, q2)` back to `(sa, sb, sc, sd)`.
    have hid : (1322905 / 1000000 - sab) * (sa + sb) ^ 2 +
        (1322905 / 1000000 + sab) * (sa - sb) ^ 2 +
        (1322905 / 1000000 - scd) * (sc + sd) ^ 2 +
        (1322905 / 1000000 + scd) * (sc - sd) ^ 2 -
        2 * (2 * (3 / 14 * ((sac + sbd + sad + sbc) / 4) +
              σ * (8 / 35) * ((sac + sbd - sad - sbc) / 4)) * (sa + sb) * (sc + sd) +
            2 * (3 / 14 * ((sac - sbd - sad + sbc) / 4) +
              σ * (8 / 35) * ((sac - sbd + sad - sbc) / 4)) * (sa + sb) * (sc - sd) +
            2 * (3 / 14 * ((sac - sbd + sad - sbc) / 4) +
              σ * (8 / 35) * ((sac - sbd - sad + sbc) / 4)) * (sa - sb) * (sc + sd) +
            2 * (3 / 14 * ((sac + sbd - sad - sbc) / 4) +
              σ * (8 / 35) * ((sac + sbd + sad + sbc) / 4)) * (sa - sb) * (sc - sd)) =
        4 * ((1322905 / 1000000 : ℝ) / 2 * (sa ^ 2 + sb ^ 2 + sc ^ 2 + sd ^ 2) -
          ((sa * sb * sab + sc * sd * scd) +
            (3 / 14 : ℝ) * (sa * sc * sac + sa * sd * sad + sb * sc * sbc + sb * sd * sbd) +
            σ * (8 / 35 : ℝ) *
              (sa * sc * sac - sa * sd * sad - sb * sc * sbc + sb * sd * sbd))) := by ring
    linarith

/-! ### Boundary shell `ℓ²` bound and existence of a universal radius -/

section GraphBounds

variable {V E : Type*} [Fintype V] {G : Multigraph V E}

omit [Fintype V] in
private theorem other_adj_of_mem_incidenceSet (hloop : G.Loopless) {w : V} {e : E}
    (he : e ∈ G.incidenceSet w) :
    ∃ w' : V, G.toSimpleGraph.Adj w w' ∧
      ∀ q R, rawSum G q R e =
        kernelRow G.toSimpleGraph q R w + kernelRow G.toSimpleGraph q R w' := by
  rcases he with rfl | rfl
  · exact ⟨G.tgt e, Multigraph.toSimpleGraph_adj.mpr ⟨hloop e, e, rfl⟩, fun _ _ => rfl⟩
  · refine ⟨G.src e, (Multigraph.toSimpleGraph_adj.mpr ⟨hloop e, e, rfl⟩).symm, fun q R => ?_⟩
    rw [rawSum, add_comm]

omit [Fintype V] in
private theorem edist_adj_le {H : SimpleGraph V} {x y z : V} {k : ℕ}
    (hadj : H.Adj x y) (hx : H.edist x z ≤ k) :
    H.edist y z ≤ ((k + 1 : ℕ) : ℕ∞) :=
  (hadj.symm.edist_le_edist_add_one z).trans (by
    simpa [Nat.cast_add, Nat.cast_one] using add_le_add hx (le_rfl : (1 : ℕ∞) ≤ 1))

omit [Fintype V] in
private theorem dist_step_of_adj {H : SimpleGraph V} {x y z : V} {R : ℕ}
    (hadj : H.Adj x y) (hx : H.edist x z ≤ R) (hy : H.edist y z ≤ R) :
    H.dist y z ≤ H.dist x z + 1 ∧ H.dist x z ≤ H.dist y z + 1 := by
  have h1 := hadj.symm.edist_le_edist_add_one z
  have h2 := hadj.edist_le_edist_add_one z
  have ex : H.edist x z = H.dist x z :=
    (SimpleGraph.reachable_of_edist_ne_top
      (ne_top_of_le_ne_top (ENat.natCast_ne_top R) hx)).coe_dist_eq_edist.symm
  have ey : H.edist y z = H.dist y z :=
    (SimpleGraph.reachable_of_edist_ne_top
      (ne_top_of_le_ne_top (ENat.natCast_ne_top R) hy)).coe_dist_eq_edist.symm
  rw [ex, ey] at h1 h2
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- Outside `edist u z ≤ R - 2` (`R ≥ 3`), any edge `e'` with an endpoint at distance `≤ 1` from
`u` has `∑_{z ∉ IntSet} (rawSum G rawRatio R e' z) ^ 2 ≤ 360 * (2 * rawRatio ^ 2) ^ (R - 3)`. -/
private theorem sum_ext_rawSum_sq_le [Finite E] (hloop : G.Loopless) (hdeg : G.MaxDegreeLE 3)
    {R : ℕ} (hR : 3 ≤ R) (u : V) {w : V} (huw : G.toSimpleGraph.edist u w ≤ 1)
    {e' : E} (he' : e' ∈ G.incidenceSet w) :
    ∑ z ∈ univ.filter (fun z => ¬G.toSimpleGraph.edist u z ≤ ((R - 2 : ℕ) : ℕ∞)),
      rawSum G rawRatio R e' z ^ 2 ≤ 360 * (2 * rawRatio ^ 2) ^ (R - 3) := by
  classical
  set H := G.toSimpleGraph
  obtain ⟨w', hww', hraw⟩ := other_adj_of_mem_incidenceSet hloop he'
  have huw' : H.edist u w' ≤ 2 := by
    calc H.edist u w' ≤ H.edist u w + H.edist w w' := SimpleGraph.edist_triangle
      _ ≤ 1 + 1 := add_le_add huw (SimpleGraph.edist_le_one_iff_adj_or_eq.mpr (.inl hww'))
      _ = 2 := by norm_num
  let S4 : Finset V := (univ.filter fun z => H.edist u z = ((R - 1 : ℕ) : ℕ∞)) ∪
    (univ.filter fun z => H.edist u z = (R : ℕ∞)) ∪
    (univ.filter fun z => H.edist u z = ((R + 1 : ℕ) : ℕ∞)) ∪
    (univ.filter fun z => H.edist u z = ((R + 2 : ℕ) : ℕ∞))
  -- Every `z` outside `R - 2` where `rawSum ... z ≠ 0` lies in `S4`, with `rawSum ≤ 2 * q^(R-3)`.
  have hpt (z : V) (hz : ¬H.edist u z ≤ ((R - 2 : ℕ) : ℕ∞)) :
      rawSum G rawRatio R e' z ^ 2 ≤
        (if z ∈ S4 then (1 : ℝ) else 0) * (4 * (rawRatio ^ 2) ^ (R - 3)) := by
    have hq0 : 0 ≤ rawRatio := rawRatio_pos.le
    have hq1 : rawRatio ≤ 1 := by norm_num [rawRatio]
    by_cases hle : H.edist u z ≤ ((R + 2 : ℕ) : ℕ∞)
    · have hed : H.edist u z = H.dist u z :=
        (SimpleGraph.reachable_of_edist_ne_top
          (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle)).coe_dist_eq_edist.symm
      have hgt : R - 2 < H.dist u z := by
        rw [hed] at hz
        exact not_le.mp fun h => hz (by exact_mod_cast h)
      have hhi : H.dist u z ≤ R + 2 := by
        rw [hed] at hle
        exact_mod_cast hle
      have hzS4 : z ∈ S4 := by
        simp only [S4, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hed]
        rcases (by omega : H.dist u z = R - 1 ∨ H.dist u z = R ∨
            H.dist u z = R + 1 ∨ H.dist u z = R + 2) with h | h | h | h
        · exact Or.inl (Or.inl (Or.inl (by exact_mod_cast h)))
        · exact Or.inl (Or.inl (Or.inr (by exact_mod_cast h)))
        · exact Or.inl (Or.inr (by exact_mod_cast h))
        · exact Or.inr (by exact_mod_cast h)
      have hkw {x : V} (hux : H.edist u x ≤ 2) :
          kernelRow H rawRatio R x z ≤ rawRatio ^ (R - 3) := by
        rw [kernelRow_apply]
        split_ifs with hxz
        · have hex : H.edist x z = H.dist x z :=
            (SimpleGraph.reachable_of_edist_ne_top
              (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hxz)).coe_dist_eq_edist.symm
          have htri : H.edist u z ≤ 2 + H.edist x z :=
            SimpleGraph.edist_triangle.trans (add_le_add hux le_rfl)
          rw [hed, hex] at htri
          have hdist : R - 3 ≤ H.dist x z := by
            have : H.dist u z ≤ 2 + H.dist x z := by exact_mod_cast htri
            omega
          exact pow_le_pow_of_le_one hq0 hq1 hdist
        · positivity
      have hsum_le : rawSum G rawRatio R e' z ≤ 2 * rawRatio ^ (R - 3) := by
        have happ : rawSum G rawRatio R e' z =
            kernelRow H rawRatio R w z + kernelRow H rawRatio R w' z := by
          rw [hraw]; rfl
        rw [happ]
        linarith [hkw (huw.trans (by norm_num)), hkw huw']
      have hnn := rawSum_nonneg (G := G) hq0 R e' z
      simp only [hzS4, ↓reduceIte, one_mul]
      have hpow : (2 * rawRatio ^ (R - 3)) ^ 2 = 4 * (rawRatio ^ 2) ^ (R - 3) := by
        rw [mul_pow, ← pow_mul, mul_comm (R - 3) 2, pow_mul]; norm_num
      rw [← hpow]
      nlinarith
    · -- `edist u z > R + 2`, so both `w` and `w'` are at distance `> R` from `z`.
      have hzero {x : V} (hux : H.edist u x ≤ 2) : kernelRow H rawRatio R x z = 0 := by
        rw [kernelRow_apply]
        split_ifs with hxz
        · refine (hle ?_).elim
          calc H.edist u z ≤ H.edist u x + H.edist x z := SimpleGraph.edist_triangle
            _ ≤ 2 + (R : ℕ∞) := add_le_add hux hxz
            _ = ((R + 2 : ℕ) : ℕ∞) := by push_cast; ring
        · rfl
      have happ : rawSum G rawRatio R e' z = 0 := by
        rw [hraw, PiLp.add_apply, hzero (huw.trans (by norm_num)), hzero huw', add_zero]
      rw [happ, zero_pow two_ne_zero]
      split_ifs <;> positivity
  -- Bound `#S4 ≤ 90 * 2 ^ (R - 3)` via `SimpleGraph.card_edist_eq_add_one_le`.
  have hdegH := hdeg.degree_toSimpleGraph_le
  have hsph (d : ℕ) : #(univ.filter fun z => H.edist u z = ((d + 1 : ℕ) : ℕ∞)) ≤ 3 * 2 ^ d := by
    have h := SimpleGraph.card_edist_eq_add_one_le hdegH u d
    simpa using h
  have hcardS4 : S4.card ≤ 90 * 2 ^ (R - 3) := by
    have c1 : #(univ.filter fun z => H.edist u z = ((R - 1 : ℕ) : ℕ∞)) ≤ 3 * 2 ^ (R - 2) := by
      have : R - 1 = (R - 2) + 1 := by omega
      rw [this]; exact hsph (R - 2)
    have c2 : #(univ.filter fun z => H.edist u z = (R : ℕ∞)) ≤ 3 * 2 ^ (R - 1) := by
      have : R = (R - 1) + 1 := by omega
      conv_lhs => rw [this]
      exact hsph (R - 1)
    have c3 := hsph R
    have c4 : #(univ.filter fun z => H.edist u z = ((R + 2 : ℕ) : ℕ∞)) ≤ 3 * 2 ^ (R + 1) :=
      hsph (R + 1)
    have hu_card : S4.card ≤
        #(univ.filter fun z => H.edist u z = ((R - 1 : ℕ) : ℕ∞)) +
        #(univ.filter fun z => H.edist u z = (R : ℕ∞)) +
        #(univ.filter fun z => H.edist u z = ((R + 1 : ℕ) : ℕ∞)) +
        #(univ.filter fun z => H.edist u z = ((R + 2 : ℕ) : ℕ∞)) := by
      dsimp [S4]
      linarith [card_union_le ((univ.filter fun z => H.edist u z = ((R - 1 : ℕ) : ℕ∞)) ∪
          (univ.filter fun z => H.edist u z = (R : ℕ∞)) ∪
          (univ.filter fun z => H.edist u z = ((R + 1 : ℕ) : ℕ∞)))
          (univ.filter fun z => H.edist u z = ((R + 2 : ℕ) : ℕ∞)),
        card_union_le ((univ.filter fun z => H.edist u z = ((R - 1 : ℕ) : ℕ∞)) ∪
          (univ.filter fun z => H.edist u z = (R : ℕ∞)))
          (univ.filter fun z => H.edist u z = ((R + 1 : ℕ) : ℕ∞)),
        card_union_le (univ.filter fun z => H.edist u z = ((R - 1 : ℕ) : ℕ∞))
          (univ.filter fun z => H.edist u z = (R : ℕ∞))]
    have hp1 : 2 ^ (R - 2) = 2 * 2 ^ (R - 3) := by
      conv_lhs => rw [show R - 2 = (R - 3) + 1 by omega]
      ring
    have hp2 : 2 ^ (R - 1) = 4 * 2 ^ (R - 3) := by
      conv_lhs => rw [show R - 1 = (R - 3) + 2 by omega]
      ring
    have hp3 : 2 ^ R = 8 * 2 ^ (R - 3) := by
      conv_lhs => rw [show R = (R - 3) + 3 by omega]
      ring
    have hp4 : 2 ^ (R + 1) = 16 * 2 ^ (R - 3) := by
      conv_lhs => rw [show R + 1 = (R - 3) + 4 by omega]
      ring
    omega
  calc ∑ z ∈ univ.filter (fun z => ¬H.edist u z ≤ ((R - 2 : ℕ) : ℕ∞)),
        rawSum G rawRatio R e' z ^ 2
      ≤ ∑ z ∈ univ.filter (fun z => ¬H.edist u z ≤ ((R - 2 : ℕ) : ℕ∞)),
          (if z ∈ S4 then (1 : ℝ) else 0) * (4 * (rawRatio ^ 2) ^ (R - 3)) :=
        sum_le_sum fun z hz => hpt z (mem_filter.mp hz).2
    _ ≤ ∑ z : V, (if z ∈ S4 then (1 : ℝ) else 0) * (4 * (rawRatio ^ 2) ^ (R - 3)) :=
        sum_le_univ_sum_of_nonneg fun z => by split_ifs <;> positivity
    _ = (S4.card : ℝ) * (4 * (rawRatio ^ 2) ^ (R - 3)) := by
        rw [← sum_mul, sum_boole, filter_mem_eq_inter, Finset.univ_inter]
    _ ≤ (90 * (2 : ℝ) ^ (R - 3)) * (4 * (rawRatio ^ 2) ^ (R - 3)) := by
        gcongr
        exact_mod_cast hcardS4
    _ = 360 * (2 * rawRatio ^ 2) ^ (R - 3) := by
        rw [mul_pow]; ring

open Classical in
private noncomputable def intBall (G : Multigraph V E) (R : ℕ) (u : V) : Finset V :=
  univ.filter fun z => G.toSimpleGraph.edist u z ≤ ((R - 2 : ℕ) : ℕ∞)

open Classical in
private noncomputable def extBall (G : Multigraph V E) (R : ℕ) (u : V) : Finset V :=
  univ.filter fun z => ¬G.toSimpleGraph.edist u z ≤ ((R - 2 : ℕ) : ℕ∞)

private theorem mem_intBall_iff {R : ℕ} {u z : V} :
    z ∈ intBall G R u ↔ G.toSimpleGraph.edist u z ≤ ((R - 2 : ℕ) : ℕ∞) := by
  classical
  simp only [intBall, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem sum_intBall_add_extBall (R : ℕ) (u : V) (g : V → ℝ) :
    ∑ z : V, g z = ∑ z ∈ intBall G R u, g z + ∑ z ∈ extBall G R u, g z := by
  classical
  exact (sum_filter_add_sum_filter_not univ
    (fun z => G.toSimpleGraph.edist u z ≤ ((R - 2 : ℕ) : ℕ∞)) g).symm

private theorem inner_rawEdgeVector_mul_norms (R : ℕ) (e1 e2 : E) :
    ⟪rawEdgeVector G rawRatio R e1, rawEdgeVector G rawRatio R e2⟫ *
        (‖rawSum G rawRatio R e1‖ * ‖rawSum G rawRatio R e2‖) =
      ∑ z : V, rawSum G rawRatio R e1 z * rawSum G rawRatio R e2 z := by
  have h1 := one_le_norm_rawSum (G := G) rawRatio_pos.le R e1
  have h2 := one_le_norm_rawSum (G := G) rawRatio_pos.le R e2
  have hlhs : ⟪rawEdgeVector G rawRatio R e1, rawEdgeVector G rawRatio R e2⟫ *
        (‖rawSum G rawRatio R e1‖ * ‖rawSum G rawRatio R e2‖) =
      ⟪rawSum G rawRatio R e1, rawSum G rawRatio R e2⟫ := by
    rw [rawEdgeVector, rawEdgeVector, real_inner_smul_left, real_inner_smul_right]
    field_simp
  rw [hlhs, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

private theorem inner_rawEdgeVector_le_one (R : ℕ) (e1 e2 : E) :
    ⟪rawEdgeVector G rawRatio R e1, rawEdgeVector G rawRatio R e2⟫ ≤ 1 := by
  simpa [norm_rawEdgeVector rawRatio_pos.le R] using
    real_inner_le_norm (rawEdgeVector G rawRatio R e1) (rawEdgeVector G rawRatio R e2)

omit [Fintype V] in
private theorem pair_scale {k sc a b : ℝ} (hsc : 0 < sc)
    (h : k * ((sc * a) ^ 2 + (sc * b) ^ 2) ≤ 2000000 * ((sc * a) * (sc * b))) :
    k / 1000000 * (a ^ 2 + b ^ 2) ≤ 2 * (a * b) := by
  have hid : sc ^ 2 * (k / 1000000 * (a ^ 2 + b ^ 2) - 2 * (a * b)) =
      1 / 1000000 * (k * ((sc * a) ^ 2 + (sc * b) ^ 2) - 2000000 * ((sc * a) * (sc * b))) := by
    ring
  nlinarith [sq_pos_of_pos hsc]

private theorem le_inner_rawEdgeVector_of_intBall [Finite E] (hloop : G.Loopless)
    (hdeg : G.MaxDegreeLE 3) {R : ℕ} (hR : 3 ≤ R)
    (hsmall : (2 * rawRatio ^ 2) ^ (R - 3) ≤ (1 : ℝ) / 10 ^ 9)
    {w u v : V} {e1 e2 : E} (hu : G.toSimpleGraph.edist w u ≤ 1) (he1 : e1 ∈ G.incidenceSet u)
    (hv : G.toSimpleGraph.edist w v ≤ 1) (he2 : e2 ∈ G.incidenceSet v)
    {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (hint_z : ∀ z ∈ intBall G R w,
      c * (rawSum G rawRatio R e1 z ^ 2 + rawSum G rawRatio R e2 z ^ 2) ≤
        2 * (rawSum G rawRatio R e1 z * rawSum G rawRatio R e2 z)) :
    c - 36 / 10 ^ 8 ≤ ⟪rawEdgeVector G rawRatio R e1, rawEdgeVector G rawRatio R e2⟫ := by
  have hsum_int := sum_le_sum hint_z
  rw [← mul_sum, sum_add_distrib, ← mul_sum] at hsum_int
  have herr : 360 * (2 * rawRatio ^ 2) ^ (R - 3) ≤ 36 / 10 ^ 8 := by linarith
  have hext (e : E) {v : V} (hv : G.toSimpleGraph.edist w v ≤ 1) (he : e ∈ G.incidenceSet v) :
      ∑ z ∈ extBall G R w, rawSum G rawRatio R e z ^ 2 ≤ 36 / 10 ^ 8 := by
    classical exact (sum_ext_rawSum_sq_le hloop hdeg hR w hv he).trans herr
  have hext_nn : 0 ≤ ∑ z ∈ extBall G R w, rawSum G rawRatio R e1 z * rawSum G rawRatio R e2 z :=
    sum_nonneg fun z _ => mul_nonneg (rawSum_nonneg rawRatio_pos.le R e1 z)
      (rawSum_nonneg rawRatio_pos.le R e2 z)
  have hn1 := one_le_norm_rawSum (G := G) rawRatio_pos.le R e1
  have hn2 := one_le_norm_rawSum (G := G) rawRatio_pos.le R e2
  have hnorm (e : E) : ‖rawSum G rawRatio R e‖ ^ 2 =
      ∑ z ∈ intBall G R w, rawSum G rawRatio R e z ^ 2 +
        ∑ z ∈ extBall G R w, rawSum G rawRatio R e z ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, sum_intBall_add_extBall R w]
  have htot12 : ⟪rawEdgeVector G rawRatio R e1, rawEdgeVector G rawRatio R e2⟫ *
        (‖rawSum G rawRatio R e1‖ * ‖rawSum G rawRatio R e2‖) =
      ∑ z ∈ intBall G R w, rawSum G rawRatio R e1 z * rawSum G rawRatio R e2 z +
        ∑ z ∈ extBall G R w, rawSum G rawRatio R e1 z * rawSum G rawRatio R e2 z := by
    rw [inner_rawEdgeVector_mul_norms, sum_intBall_add_extBall R w]
  have hamgm : 2 * (‖rawSum G rawRatio R e1‖ * ‖rawSum G rawRatio R e2‖) ≤
      ‖rawSum G rawRatio R e1‖ ^ 2 + ‖rawSum G rawRatio R e2‖ ^ 2 := by
    nlinarith [sq_nonneg (‖rawSum G rawRatio R e1‖ - ‖rawSum G rawRatio R e2‖)]
  have hscaled := mul_le_mul_of_nonneg_left hamgm hc
  rw [hnorm e1, hnorm e2] at hscaled
  have htail := mul_le_mul_of_nonneg_left (add_le_add (hext e1 hu he1) (hext e2 hv he2)) hc
  have hp := one_le_mul_of_one_le_of_one_le hn1 hn2
  refine le_of_mul_le_mul_right ?_ (zero_lt_one.trans_le hp)
  linarith only [hscaled, htail, hc1, hsum_int, hext_nn, htot12, hp]

private theorem le_inner_rawEdgeVector_same [Finite E] (hloop : G.Loopless)
    (hdeg : G.MaxDegreeLE 3) {R : ℕ} (hR : 3 ≤ R)
    (hsmall : (2 * rawRatio ^ 2) ^ (R - 3) ≤ (1 : ℝ) / 10 ^ 9)
    {w : V} {e1 e2 : E} (he1 : e1 ∈ G.incidenceSet w) (he2 : e2 ∈ G.incidenceSet w) :
    (9428 / 10000 : ℝ) ≤ ⟪rawEdgeVector G rawRatio R e1, rawEdgeVector G rawRatio R e2⟫ := by
  obtain ⟨w1, hw1, hr1⟩ := other_adj_of_mem_incidenceSet hloop he1
  obtain ⟨w2, hw2, hr2⟩ := other_adj_of_mem_incidenceSet hloop he2
  have hw_self : G.toSimpleGraph.edist w w ≤ 1 := by simp
  have hint_z : ∀ z ∈ intBall G R w,
      (942806 / 1000000 : ℝ) * (rawSum G rawRatio R e1 z ^ 2 + rawSum G rawRatio R e2 z ^ 2) ≤
        2 * (rawSum G rawRatio R e1 z * rawSum G rawRatio R e2 z) := by
    intro z hz
    have hzw : G.toSimpleGraph.edist w z ≤ ((R - 2 : ℕ) : ℕ∞) := mem_intBall_iff.mp hz
    have hzwR : G.toSimpleGraph.edist w z ≤ R :=
      hzw.trans (by exact_mod_cast (by omega : R - 2 ≤ R))
    have hzw1 : G.toSimpleGraph.edist w1 z ≤ R :=
      (edist_adj_le hw1 hzw).trans (by exact_mod_cast (by omega : R - 2 + 1 ≤ R))
    have hzw2 : G.toSimpleGraph.edist w2 z ≤ R :=
      (edist_adj_le hw2 hzw).trans (by exact_mod_cast (by omega : R - 2 + 1 ≤ R))
    have hs1 := dist_step_of_adj hw1 hzwR hzw1
    have hs2 := dist_step_of_adj hw2 hzwR hzw2
    have hf1 : rawSum G rawRatio R e1 z =
        rawRatio ^ G.toSimpleGraph.dist w z + rawRatio ^ G.toSimpleGraph.dist w1 z := by
      rw [hr1, PiLp.add_apply, kernelRow_of_le hzwR, kernelRow_of_le hzw1]
    have hf2 : rawSum G rawRatio R e2 z =
        rawRatio ^ G.toSimpleGraph.dist w z + rawRatio ^ G.toSimpleGraph.dist w2 z := by
      rw [hr2, PiLp.add_apply, kernelRow_of_le hzwR, kernelRow_of_le hzw2]
    have hi : (942806 : ℝ) *
          ((starEntry (diffToFin3 (G.toSimpleGraph.dist w z) (G.toSimpleGraph.dist w1 z)) : ℝ) ^ 2 +
            (starEntry (diffToFin3 (G.toSimpleGraph.dist w z) (G.toSimpleGraph.dist w2 z)) : ℝ) ^
              2) ≤
        2000000 *
          ((starEntry (diffToFin3 (G.toSimpleGraph.dist w z) (G.toSimpleGraph.dist w1 z)) : ℝ) *
            (starEntry (diffToFin3 (G.toSimpleGraph.dist w z) (G.toSimpleGraph.dist w2 z)) : ℝ)) :=
      by exact_mod_cast samePair9_int _ _
    rw [starEntry_eq hs1, starEntry_eq hs2, ← hf1, ← hf2] at hi
    exact pair_scale (profileScale_pos (G.toSimpleGraph.dist w z)) hi
  exact le_trans (by norm_num) (le_inner_rawEdgeVector_of_intBall hloop hdeg hR hsmall
    hw_self he1 hw_self he2 (c := 942806 / 1000000) (by norm_num) (by norm_num) hint_z)

private theorem isAdmissibleStar_rawEdgeVector [Finite E] (hloop : G.Loopless)
    (hdeg : G.MaxDegreeLE 3) {R : ℕ} (hR : 3 ≤ R)
    (hsmall : (2 * rawRatio ^ 2) ^ (R - 3) ≤ (1 : ℝ) / 10 ^ 9)
    (u : V) (f : Fin 3 → E) (hf : ∀ i, f i ∈ G.incidenceSet u) :
    IsAdmissibleStar (fun i => rawEdgeVector G rawRatio R (f i)) := by
  have hq0 := rawRatio_pos.le
  have hu_self : G.toSimpleGraph.edist u u ≤ 1 := by simp
  refine ⟨fun i => norm_rawEdgeVector hq0 R (f i),
    le_inner_rawEdgeVector_same hloop hdeg hR hsmall (hf 0) (hf 1),
    le_inner_rawEdgeVector_same hloop hdeg hR hsmall (hf 0) (hf 2),
    le_inner_rawEdgeVector_same hloop hdeg hR hsmall (hf 1) (hf 2), ?_⟩
  obtain ⟨w0, hw0, hr0⟩ := other_adj_of_mem_incidenceSet hloop (hf 0)
  obtain ⟨w1, hw1, hr1⟩ := other_adj_of_mem_incidenceSet hloop (hf 1)
  obtain ⟨w2, hw2, hr2⟩ := other_adj_of_mem_incidenceSet hloop (hf 2)
  have hint_z : ∀ z ∈ intBall G R u,
      (957104 / 1000000 : ℝ) * (rawSum G rawRatio R (f 0) z ^ 2 +
          rawSum G rawRatio R (f 1) z ^ 2 + rawSum G rawRatio R (f 2) z ^ 2) ≤
        rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 1) z +
        rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 2) z +
        rawSum G rawRatio R (f 1) z * rawSum G rawRatio R (f 2) z := by
    intro z hz
    have hzu : G.toSimpleGraph.edist u z ≤ ((R - 2 : ℕ) : ℕ∞) := mem_intBall_iff.mp hz
    have hzuR : G.toSimpleGraph.edist u z ≤ R :=
      hzu.trans (by exact_mod_cast (by omega : R - 2 ≤ R))
    have hstep_R {w : V} (hw : G.toSimpleGraph.Adj u w) : G.toSimpleGraph.edist w z ≤ R :=
      (edist_adj_le hw hzu).trans (by exact_mod_cast (by omega : R - 2 + 1 ≤ R))
    have hz0 := hstep_R hw0; have hz1 := hstep_R hw1; have hz2 := hstep_R hw2
    have hs0 := dist_step_of_adj hw0 hzuR hz0
    have hs1 := dist_step_of_adj hw1 hzuR hz1
    have hs2 := dist_step_of_adj hw2 hzuR hz2
    have hf0 : rawSum G rawRatio R (f 0) z =
        rawRatio ^ G.toSimpleGraph.dist u z + rawRatio ^ G.toSimpleGraph.dist w0 z := by
      rw [hr0, PiLp.add_apply, kernelRow_of_le hzuR, kernelRow_of_le hz0]
    have hf1 : rawSum G rawRatio R (f 1) z =
        rawRatio ^ G.toSimpleGraph.dist u z + rawRatio ^ G.toSimpleGraph.dist w1 z := by
      rw [hr1, PiLp.add_apply, kernelRow_of_le hzuR, kernelRow_of_le hz1]
    have hf2 : rawSum G rawRatio R (f 2) z =
        rawRatio ^ G.toSimpleGraph.dist u z + rawRatio ^ G.toSimpleGraph.dist w2 z := by
      rw [hr2, PiLp.add_apply, kernelRow_of_le hzuR, kernelRow_of_le hz2]
    have hi : (957104 : ℝ) *
          ((starEntry (diffToFin3 (G.toSimpleGraph.dist u z) (G.toSimpleGraph.dist w0 z)) : ℝ) ^ 2 +
            (starEntry (diffToFin3 (G.toSimpleGraph.dist u z) (G.toSimpleGraph.dist w1 z)) : ℝ) ^
              2 +
            (starEntry (diffToFin3 (G.toSimpleGraph.dist u z) (G.toSimpleGraph.dist w2 z)) : ℝ) ^
              2) ≤
        1000000 *
          ((starEntry (diffToFin3 (G.toSimpleGraph.dist u z) (G.toSimpleGraph.dist w0 z)) : ℝ) *
              (starEntry (diffToFin3 (G.toSimpleGraph.dist u z) (G.toSimpleGraph.dist w1 z)) : ℝ) +
            (starEntry (diffToFin3 (G.toSimpleGraph.dist u z) (G.toSimpleGraph.dist w0 z)) : ℝ) *
              (starEntry (diffToFin3 (G.toSimpleGraph.dist u z) (G.toSimpleGraph.dist w2 z)) : ℝ) +
            (starEntry (diffToFin3 (G.toSimpleGraph.dist u z) (G.toSimpleGraph.dist w1 z)) : ℝ) *
              (starEntry (diffToFin3 (G.toSimpleGraph.dist u z) (G.toSimpleGraph.dist w2 z)) :
                ℝ)) := by exact_mod_cast star27_int _ _ _
    rw [starEntry_eq hs0, starEntry_eq hs1, starEntry_eq hs2, ← hf0, ← hf1, ← hf2] at hi
    have hsc := profileScale_pos (G.toSimpleGraph.dist u z)
    set sc := (7071 : ℝ) ^ 2 * (10000 : ℝ) ^ 2 / rawRatio ^ G.toSimpleGraph.dist u z
    have hid : sc ^ 2 * ((957104 / 1000000 : ℝ) * (rawSum G rawRatio R (f 0) z ^ 2 +
          rawSum G rawRatio R (f 1) z ^ 2 + rawSum G rawRatio R (f 2) z ^ 2) -
        (rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 1) z +
          rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 2) z +
          rawSum G rawRatio R (f 1) z * rawSum G rawRatio R (f 2) z)) =
        (1 / 1000000 : ℝ) * (957104 * ((sc * rawSum G rawRatio R (f 0) z) ^ 2 +
            (sc * rawSum G rawRatio R (f 1) z) ^ 2 +
            (sc * rawSum G rawRatio R (f 2) z) ^ 2) -
          1000000 * ((sc * rawSum G rawRatio R (f 0) z) * (sc * rawSum G rawRatio R (f 1) z) +
            (sc * rawSum G rawRatio R (f 0) z) * (sc * rawSum G rawRatio R (f 2) z) +
            (sc * rawSum G rawRatio R (f 1) z) *
              (sc * rawSum G rawRatio R (f 2) z))) := by ring
    have hdiv : sc ^ 2 * ((957104 / 1000000 : ℝ) * (rawSum G rawRatio R (f 0) z ^ 2 +
          rawSum G rawRatio R (f 1) z ^ 2 + rawSum G rawRatio R (f 2) z ^ 2) -
        (rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 1) z +
          rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 2) z +
          rawSum G rawRatio R (f 1) z * rawSum G rawRatio R (f 2) z)) ≤ 0 := by linarith
    nlinarith [sq_pos_of_pos hsc]
  have hsum_int := sum_le_sum hint_z
  rw [← mul_sum, sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib] at hsum_int
  have hext (i : Fin 3) : ∑ z ∈ extBall G R u, rawSum G rawRatio R (f i) z ^ 2 ≤
      360 * (2 * rawRatio ^ 2) ^ (R - 3) :=
    sum_ext_rawSum_sq_le hloop hdeg hR u hu_self (hf i)
  have hext_nn (i j : Fin 3) :
      0 ≤ ∑ z ∈ extBall G R u, rawSum G rawRatio R (f i) z * rawSum G rawRatio R (f j) z :=
    sum_nonneg fun z _ => mul_nonneg (rawSum_nonneg hq0 R _ z) (rawSum_nonneg hq0 R _ z)
  have hnorm (i : Fin 3) := one_le_norm_rawSum (G := G) hq0 R (f i)
  have norm_split (i : Fin 3) : ‖rawSum G rawRatio R (f i)‖ ^ 2 =
      ∑ z ∈ intBall G R u, rawSum G rawRatio R (f i) z ^ 2 +
        ∑ z ∈ extBall G R u, rawSum G rawRatio R (f i) z ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, sum_intBall_add_extBall R u]
  have inner_split (i j : Fin 3) :
      ⟪rawEdgeVector G rawRatio R (f i), rawEdgeVector G rawRatio R (f j)⟫ *
        (‖rawSum G rawRatio R (f i)‖ * ‖rawSum G rawRatio R (f j)‖) =
      ∑ z ∈ intBall G R u, rawSum G rawRatio R (f i) z * rawSum G rawRatio R (f j) z +
        ∑ z ∈ extBall G R u, rawSum G rawRatio R (f i) z * rawSum G rawRatio R (f j) z := by
    rw [inner_rawEdgeVector_mul_norms, sum_intBall_add_extBall R u]
  have hr01_lo : 0 ≤ ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 1)⟫ :=
    (by norm_num : (0 : ℝ) ≤ 9428 / 10000).trans
      (le_inner_rawEdgeVector_same hloop hdeg hR hsmall (hf 0) (hf 1))
  refine star_cubic_of_quad (s1 := ‖rawSum G rawRatio R (f 0)‖)
    (s2 := ‖rawSum G rawRatio R (f 1)‖) (s3 := ‖rawSum G rawRatio R (f 2)‖)
    hr01_lo (inner_rawEdgeVector_le_one R (f 0) (f 1)) (lt_of_lt_of_le zero_lt_one (hnorm 2)) ?_
  have hsq_sum : 3 ≤ ‖rawSum G rawRatio R (f 0)‖ ^ 2 + ‖rawSum G rawRatio R (f 1)‖ ^ 2 +
      ‖rawSum G rawRatio R (f 2)‖ ^ 2 := by nlinarith [hnorm 0, hnorm 1, hnorm 2]
  have herr : 360 * (2 * rawRatio ^ 2) ^ (R - 3) ≤ 36 / 10 ^ 8 := by linarith
  nlinarith only [hsum_int, hsq_sum, herr, hext 0, hext 1, hext 2, hext_nn 0 1, hext_nn 0 2,
    hext_nn 1 2, norm_split 0, norm_split 1, norm_split 2, inner_split 0 1, inner_split 0 2,
    inner_split 1 2]

private theorem le_inner_rawEdgeVector_adj [Finite E] (hloop : G.Loopless)
    (hdeg : G.MaxDegreeLE 3) {R : ℕ} (hR : 3 ≤ R)
    (hsmall : (2 * rawRatio ^ 2) ^ (R - 3) ≤ (1 : ℝ) / 10 ^ 9)
    {u v : V} (huv : G.toSimpleGraph.Adj u v)
    {eu ev : E} (heu : eu ∈ G.incidenceSet u) (hev : ev ∈ G.incidenceSet v) :
    (79998 / 100000 : ℝ) ≤ ⟪rawEdgeVector G rawRatio R eu, rawEdgeVector G rawRatio R ev⟫ := by
  have hu_self : G.toSimpleGraph.edist u u ≤ 1 := by simp
  have huv_ed : G.toSimpleGraph.edist u v ≤ 1 :=
    SimpleGraph.edist_le_one_iff_adj_or_eq.mpr (.inl huv)
  obtain ⟨wu, hwu, hru⟩ := other_adj_of_mem_incidenceSet hloop heu
  obtain ⟨wv, hwv, hrv⟩ := other_adj_of_mem_incidenceSet hloop hev
  have hint_z : ∀ z ∈ intBall G R u,
      (799990 / 1000000 : ℝ) * (rawSum G rawRatio R eu z ^ 2 +
          rawSum G rawRatio R ev z ^ 2) ≤
        2 * (rawSum G rawRatio R eu z * rawSum G rawRatio R ev z) := by
    intro z hz
    have hzu : G.toSimpleGraph.edist u z ≤ ((R - 2 : ℕ) : ℕ∞) := mem_intBall_iff.mp hz
    have hzuR : G.toSimpleGraph.edist u z ≤ R :=
      hzu.trans (by exact_mod_cast (by omega : R - 2 ≤ R))
    have hzv1 : G.toSimpleGraph.edist v z ≤ ((R - 1 : ℕ) : ℕ∞) :=
      (edist_adj_le huv hzu).trans (by exact_mod_cast (by omega : R - 2 + 1 ≤ R - 1))
    have hzvR : G.toSimpleGraph.edist v z ≤ R :=
      hzv1.trans (by exact_mod_cast (by omega : R - 1 ≤ R))
    have hzwu : G.toSimpleGraph.edist wu z ≤ R :=
      (edist_adj_le hwu hzu).trans (by exact_mod_cast (by omega : R - 2 + 1 ≤ R))
    have hzwv : G.toSimpleGraph.edist wv z ≤ R :=
      (edist_adj_le hwv hzv1).trans (by exact_mod_cast (by omega : R - 1 + 1 ≤ R))
    have hsu := dist_step_of_adj hwu hzuR hzwu
    have hsv := dist_step_of_adj huv hzuR hzvR
    have hsvw := dist_step_of_adj hwv hzvR hzwv
    have hfu : rawSum G rawRatio R eu z =
        rawRatio ^ G.toSimpleGraph.dist u z + rawRatio ^ G.toSimpleGraph.dist wu z := by
      rw [hru, PiLp.add_apply, kernelRow_of_le hzuR, kernelRow_of_le hzwu]
    have hfv : rawSum G rawRatio R ev z =
        rawRatio ^ G.toSimpleGraph.dist v z + rawRatio ^ G.toSimpleGraph.dist wv z := by
      rw [hrv, PiLp.add_apply, kernelRow_of_le hzvR, kernelRow_of_le hzwv]
    have hi : (799990 : ℝ) *
          ((starEntry (diffToFin3 (G.toSimpleGraph.dist u z) (G.toSimpleGraph.dist wu z)) : ℝ) ^ 2 +
            (shiftEntry (diffToFin3 (G.toSimpleGraph.dist u z) (G.toSimpleGraph.dist v z))
              (diffToFin3 (G.toSimpleGraph.dist v z) (G.toSimpleGraph.dist wv z)) : ℝ) ^ 2) ≤
        2000000 *
          ((starEntry (diffToFin3 (G.toSimpleGraph.dist u z) (G.toSimpleGraph.dist wu z)) : ℝ) *
            (shiftEntry (diffToFin3 (G.toSimpleGraph.dist u z) (G.toSimpleGraph.dist v z))
              (diffToFin3 (G.toSimpleGraph.dist v z) (G.toSimpleGraph.dist wv z)) : ℝ)) := by
      exact_mod_cast crossPair27_int _ _ _
    rw [starEntry_eq hsu, shiftEntry_eq hsv hsvw, ← hfu, ← hfv] at hi
    exact pair_scale (profileScale_pos (G.toSimpleGraph.dist u z)) hi
  exact le_trans (by norm_num) (le_inner_rawEdgeVector_of_intBall hloop hdeg hR hsmall
    hu_self heu huv_ed hev (c := 799990 / 1000000) (by norm_num) (by norm_num) hint_z)

omit [Fintype V] in
private theorem h243_scale {sc fa fb fc fd σ : ℝ} (hsc : 0 < sc) (hσ : σ = 1 ∨ σ = -1)
    (h : (70 * 1322909 : ℝ) * ((sc * fa) ^ 2 + (sc * fb) ^ 2 + (sc * fc) ^ 2 + (sc * fd) ^ 2) ≤
      2000000 * (70 * ((sc * fa) * (sc * fb) + (sc * fc) * (sc * fd)) +
        15 * (sc * fa + sc * fb) * (sc * fc + sc * fd) -
        16 * |(sc * fa - sc * fb) * (sc * fc - sc * fd)|)) :
    (1322909 / 1000000 : ℝ) / 2 * (fa ^ 2 + fb ^ 2 + fc ^ 2 + fd ^ 2) ≤
      (fa * fb + fc * fd) + (3 / 14 : ℝ) * (fa + fb) * (fc + fd) +
      σ * (8 / 35 : ℝ) * (fa - fb) * (fc - fd) := by
  have habs : |(sc * fa - sc * fb) * (sc * fc - sc * fd)| =
      sc ^ 2 * |(fa - fb) * (fc - fd)| := by
    have : (sc * fa - sc * fb) * (sc * fc - sc * fd) = sc ^ 2 * ((fa - fb) * (fc - fd)) := by ring
    rw [this, abs_mul, abs_of_pos (sq_pos_of_pos hsc)]
  rw [habs] at h
  have hsign : -|(fa - fb) * (fc - fd)| ≤ σ * (fa - fb) * (fc - fd) := by
    rcases hσ with rfl | rfl
    · linarith [neg_abs_le ((fa - fb) * (fc - fd))]
    · linarith [le_abs_self ((fa - fb) * (fc - fd))]
  have hid : 2000000 * (70 * ((sc * fa) * (sc * fb) + (sc * fc) * (sc * fd)) +
        15 * (sc * fa + sc * fb) * (sc * fc + sc * fd) -
        16 * (sc ^ 2 * |(fa - fb) * (fc - fd)|)) -
      (70 * 1322909 : ℝ) * ((sc * fa) ^ 2 + (sc * fb) ^ 2 + (sc * fc) ^ 2 + (sc * fd) ^ 2) =
      140000000 * sc ^ 2 * (((fa * fb + fc * fd) + (3 / 14 : ℝ) * (fa + fb) * (fc + fd) -
          (8 / 35 : ℝ) * |(fa - fb) * (fc - fd)|) -
        (1322909 / 1000000 : ℝ) / 2 * (fa ^ 2 + fb ^ 2 + fc ^ 2 + fd ^ 2)) := by ring
  nlinarith [sq_pos_of_pos hsc]

private theorem isAdmissiblePair_rawEdgeVector [Finite E] (hloop : G.Loopless)
    (hdeg : G.MaxDegreeLE 3) {R : ℕ} (hR : 3 ≤ R)
    (hsmall : (2 * rawRatio ^ 2) ^ (R - 3) ≤ (1 : ℝ) / 10 ^ 9)
    (e : E) (f : Fin 4 → E)
    (h0 : f 0 ∈ G.incidenceSet (G.src e)) (h1 : f 1 ∈ G.incidenceSet (G.src e))
    (h2 : f 2 ∈ G.incidenceSet (G.tgt e)) (h3 : f 3 ∈ G.incidenceSet (G.tgt e)) :
    IsAdmissiblePair (fun i => rawEdgeVector G rawRatio R (f i)) := by
  have hq0 := rawRatio_pos.le
  have huv : G.toSimpleGraph.Adj (G.src e) (G.tgt e) :=
    Multigraph.toSimpleGraph_adj.mpr ⟨hloop e, e, rfl⟩
  have hu_self : G.toSimpleGraph.edist (G.src e) (G.src e) ≤ 1 := by simp
  have huv_ed : G.toSimpleGraph.edist (G.src e) (G.tgt e) ≤ 1 :=
    SimpleGraph.edist_le_one_iff_adj_or_eq.mpr (.inl huv)
  have hsab_lo := le_inner_rawEdgeVector_same hloop hdeg hR hsmall h0 h1
  have hscd_lo := le_inner_rawEdgeVector_same hloop hdeg hR hsmall h2 h3
  have hsac_lo := le_inner_rawEdgeVector_adj hloop hdeg hR hsmall huv h0 h2
  have hsad_lo := le_inner_rawEdgeVector_adj hloop hdeg hR hsmall huv h0 h3
  have hsbc_lo := le_inner_rawEdgeVector_adj hloop hdeg hR hsmall huv h1 h2
  have hsbd_lo := le_inner_rawEdgeVector_adj hloop hdeg hR hsmall huv h1 h3
  obtain ⟨ua, hua, hra⟩ := other_adj_of_mem_incidenceSet hloop h0
  obtain ⟨ub, hub, hrb⟩ := other_adj_of_mem_incidenceSet hloop h1
  obtain ⟨vc, hvc, hrc⟩ := other_adj_of_mem_incidenceSet hloop h2
  obtain ⟨vd, hvd, hrd⟩ := other_adj_of_mem_incidenceSet hloop h3
  have hschur (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
      schurPairIneq
        ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 1)⟫
        ⟪rawEdgeVector G rawRatio R (f 2), rawEdgeVector G rawRatio R (f 3)⟫
        ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 2)⟫
        ⟪rawEdgeVector G rawRatio R (f 1), rawEdgeVector G rawRatio R (f 3)⟫
        ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 3)⟫
        ⟪rawEdgeVector G rawRatio R (f 1), rawEdgeVector G rawRatio R (f 2)⟫ σ ∧
      schurPairIneq
        ⟪rawEdgeVector G rawRatio R (f 2), rawEdgeVector G rawRatio R (f 3)⟫
        ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 1)⟫
        ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 2)⟫
        ⟪rawEdgeVector G rawRatio R (f 1), rawEdgeVector G rawRatio R (f 3)⟫
        ⟪rawEdgeVector G rawRatio R (f 1), rawEdgeVector G rawRatio R (f 2)⟫
        ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 3)⟫ σ := by
    have hint_z : ∀ z ∈ intBall G R (G.src e),
        (1322909 / 1000000 : ℝ) / 2 *
            (rawSum G rawRatio R (f 0) z ^ 2 + rawSum G rawRatio R (f 1) z ^ 2 +
              rawSum G rawRatio R (f 2) z ^ 2 + rawSum G rawRatio R (f 3) z ^ 2) ≤
          (rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 1) z +
            rawSum G rawRatio R (f 2) z * rawSum G rawRatio R (f 3) z) +
          (3 / 14 : ℝ) * (rawSum G rawRatio R (f 0) z + rawSum G rawRatio R (f 1) z) *
            (rawSum G rawRatio R (f 2) z + rawSum G rawRatio R (f 3) z) +
          σ * (8 / 35 : ℝ) * (rawSum G rawRatio R (f 0) z - rawSum G rawRatio R (f 1) z) *
            (rawSum G rawRatio R (f 2) z - rawSum G rawRatio R (f 3) z) := by
      intro z hz
      have hzu : G.toSimpleGraph.edist (G.src e) z ≤ ((R - 2 : ℕ) : ℕ∞) := mem_intBall_iff.mp hz
      have hzuR : G.toSimpleGraph.edist (G.src e) z ≤ R :=
        hzu.trans (by exact_mod_cast (by omega : R - 2 ≤ R))
      have hzv1 : G.toSimpleGraph.edist (G.tgt e) z ≤ ((R - 1 : ℕ) : ℕ∞) :=
        (edist_adj_le huv hzu).trans (by exact_mod_cast (by omega : R - 2 + 1 ≤ R - 1))
      have hzvR : G.toSimpleGraph.edist (G.tgt e) z ≤ R :=
        hzv1.trans (by exact_mod_cast (by omega : R - 1 ≤ R))
      have hzua : G.toSimpleGraph.edist ua z ≤ R :=
        (edist_adj_le hua hzu).trans (by exact_mod_cast (by omega : R - 2 + 1 ≤ R))
      have hzub : G.toSimpleGraph.edist ub z ≤ R :=
        (edist_adj_le hub hzu).trans (by exact_mod_cast (by omega : R - 2 + 1 ≤ R))
      have hzvc : G.toSimpleGraph.edist vc z ≤ R :=
        (edist_adj_le hvc hzv1).trans (by exact_mod_cast (by omega : R - 1 + 1 ≤ R))
      have hzvd : G.toSimpleGraph.edist vd z ≤ R :=
        (edist_adj_le hvd hzv1).trans (by exact_mod_cast (by omega : R - 1 + 1 ≤ R))
      have hsv := dist_step_of_adj huv hzuR hzvR
      have hsa := dist_step_of_adj hua hzuR hzua
      have hsb := dist_step_of_adj hub hzuR hzub
      have hsc := dist_step_of_adj hvc hzvR hzvc
      have hsd := dist_step_of_adj hvd hzvR hzvd
      have hfa : rawSum G rawRatio R (f 0) z =
          rawRatio ^ G.toSimpleGraph.dist (G.src e) z + rawRatio ^ G.toSimpleGraph.dist ua z := by
        rw [hra, PiLp.add_apply, kernelRow_of_le hzuR, kernelRow_of_le hzua]
      have hfb : rawSum G rawRatio R (f 1) z =
          rawRatio ^ G.toSimpleGraph.dist (G.src e) z + rawRatio ^ G.toSimpleGraph.dist ub z := by
        rw [hrb, PiLp.add_apply, kernelRow_of_le hzuR, kernelRow_of_le hzub]
      have hfc : rawSum G rawRatio R (f 2) z =
          rawRatio ^ G.toSimpleGraph.dist (G.tgt e) z + rawRatio ^ G.toSimpleGraph.dist vc z := by
        rw [hrc, PiLp.add_apply, kernelRow_of_le hzvR, kernelRow_of_le hzvc]
      have hfd : rawSum G rawRatio R (f 3) z =
          rawRatio ^ G.toSimpleGraph.dist (G.tgt e) z + rawRatio ^ G.toSimpleGraph.dist vd z := by
        rw [hrd, PiLp.add_apply, kernelRow_of_le hzvR, kernelRow_of_le hzvd]
      let dv := diffToFin3 (G.toSimpleGraph.dist (G.src e) z) (G.toSimpleGraph.dist (G.tgt e) z)
      let d1 := diffToFin3 (G.toSimpleGraph.dist (G.src e) z) (G.toSimpleGraph.dist ua z)
      let d2 := diffToFin3 (G.toSimpleGraph.dist (G.src e) z) (G.toSimpleGraph.dist ub z)
      let d3 := diffToFin3 (G.toSimpleGraph.dist (G.tgt e) z) (G.toSimpleGraph.dist vc z)
      let d4 := diffToFin3 (G.toSimpleGraph.dist (G.tgt e) z) (G.toSimpleGraph.dist vd z)
      have h243 := of_decide_eq_true (h243_int dv d1 d2 d3 d4)
      dsimp [h243Check] at h243
      have hreal : (70 * 1322909 : ℝ) *
            ((starEntry d1 : ℝ) ^ 2 + (starEntry d2 : ℝ) ^ 2 +
              (shiftEntry dv d3 : ℝ) ^ 2 + (shiftEntry dv d4 : ℝ) ^ 2) ≤
          2000000 * (70 * ((starEntry d1 : ℝ) * starEntry d2 +
              (shiftEntry dv d3 : ℝ) * shiftEntry dv d4) +
            15 * ((starEntry d1 : ℝ) + starEntry d2) *
              ((shiftEntry dv d3 : ℝ) + shiftEntry dv d4) -
            16 * |(starEntry d1 - starEntry d2 : ℝ) * (shiftEntry dv d3 - shiftEntry dv d4)|) := by
        have hcast : ((70 * 1322909 : ℤ) * (starEntry d1 ^ 2 + starEntry d2 ^ 2 +
              shiftEntry dv d3 ^ 2 + shiftEntry dv d4 ^ 2) : ℝ) ≤
            (2000000 * (70 * (starEntry d1 * starEntry d2 + shiftEntry dv d3 * shiftEntry dv d4) +
              15 * (starEntry d1 + starEntry d2) * (shiftEntry dv d3 + shiftEntry dv d4) -
              16 * (if 0 ≤ (starEntry d1 - starEntry d2) * (shiftEntry dv d3 - shiftEntry dv d4)
                then (starEntry d1 - starEntry d2) * (shiftEntry dv d3 - shiftEntry dv d4)
                else -((starEntry d1 - starEntry d2) *
                  (shiftEntry dv d3 - shiftEntry dv d4)))) : ℝ) := by
          exact_mod_cast h243
        have habs_eq : (if 0 ≤ (starEntry d1 - starEntry d2) *
              (shiftEntry dv d3 - shiftEntry dv d4)
            then ((starEntry d1 : ℝ) - starEntry d2) * (shiftEntry dv d3 - shiftEntry dv d4)
            else -(((starEntry d1 : ℝ) - starEntry d2) *
              (shiftEntry dv d3 - shiftEntry dv d4))) =
            |(starEntry d1 - starEntry d2 : ℝ) * (shiftEntry dv d3 - shiftEntry dv d4)| := by
          split_ifs with h0
          · exact (abs_of_nonneg (by exact_mod_cast h0)).symm
          · exact (abs_of_neg (by exact_mod_cast not_le.mp h0)).symm
        push_cast at hcast
        rw [habs_eq] at hcast
        linarith
      rw [starEntry_eq hsa, starEntry_eq hsb, shiftEntry_eq hsv hsc, shiftEntry_eq hsv hsd,
        ← hfa, ← hfb, ← hfc, ← hfd] at hreal
      exact h243_scale (profileScale_pos (G.toSimpleGraph.dist (G.src e) z)) hσ hreal
    have hsum_int := sum_le_sum hint_z
    have hext_pt : ∀ z ∈ extBall G R (G.src e),
        -((rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 1) z +
            rawSum G rawRatio R (f 2) z * rawSum G rawRatio R (f 3) z) +
          (3 / 14 : ℝ) * (rawSum G rawRatio R (f 0) z + rawSum G rawRatio R (f 1) z) *
            (rawSum G rawRatio R (f 2) z + rawSum G rawRatio R (f 3) z) +
          σ * (8 / 35 : ℝ) * (rawSum G rawRatio R (f 0) z - rawSum G rawRatio R (f 1) z) *
            (rawSum G rawRatio R (f 2) z - rawSum G rawRatio R (f 3) z)) ≤
          (4 / 35 : ℝ) * (rawSum G rawRatio R (f 0) z ^ 2 + rawSum G rawRatio R (f 1) z ^ 2 +
            rawSum G rawRatio R (f 2) z ^ 2 + rawSum G rawRatio R (f 3) z ^ 2) := by
      intro z _
      have ha0 := rawSum_nonneg (G := G) hq0 R (f 0) z
      have hb0 := rawSum_nonneg (G := G) hq0 R (f 1) z
      have hc0 := rawSum_nonneg (G := G) hq0 R (f 2) z
      have hd0 := rawSum_nonneg (G := G) hq0 R (f 3) z
      rcases hσ with rfl | rfl
      · nlinarith [sq_nonneg ((rawSum G rawRatio R (f 0) z - rawSum G rawRatio R (f 1) z) +
          (rawSum G rawRatio R (f 2) z - rawSum G rawRatio R (f 3) z)),
          mul_nonneg ha0 hb0, mul_nonneg hc0 hd0,
          mul_nonneg (add_nonneg ha0 hb0) (add_nonneg hc0 hd0)]
      · nlinarith [sq_nonneg ((rawSum G rawRatio R (f 0) z - rawSum G rawRatio R (f 1) z) -
          (rawSum G rawRatio R (f 2) z - rawSum G rawRatio R (f 3) z)),
          mul_nonneg ha0 hb0, mul_nonneg hc0 hd0,
          mul_nonneg (add_nonneg ha0 hb0) (add_nonneg hc0 hd0)]
    have hsum_ext := sum_le_sum hext_pt
    rw [sum_neg_distrib, ← mul_sum] at hsum_ext
    conv at hsum_ext => rhs; rw [sum_add_distrib, sum_add_distrib, sum_add_distrib]
    have hexta : ∑ z ∈ extBall G R (G.src e), rawSum G rawRatio R (f 0) z ^ 2 ≤
        360 * (2 * rawRatio ^ 2) ^ (R - 3) := by
      classical exact sum_ext_rawSum_sq_le hloop hdeg hR (G.src e) hu_self h0
    have hextb : ∑ z ∈ extBall G R (G.src e), rawSum G rawRatio R (f 1) z ^ 2 ≤
        360 * (2 * rawRatio ^ 2) ^ (R - 3) := by
      classical exact sum_ext_rawSum_sq_le hloop hdeg hR (G.src e) hu_self h1
    have hextc : ∑ z ∈ extBall G R (G.src e), rawSum G rawRatio R (f 2) z ^ 2 ≤
        360 * (2 * rawRatio ^ 2) ^ (R - 3) := by
      classical exact sum_ext_rawSum_sq_le hloop hdeg hR (G.src e) huv_ed h2
    have hextd : ∑ z ∈ extBall G R (G.src e), rawSum G rawRatio R (f 3) z ^ 2 ≤
        360 * (2 * rawRatio ^ 2) ^ (R - 3) := by
      classical exact sum_ext_rawSum_sq_le hloop hdeg hR (G.src e) huv_ed h3
    have hna := one_le_norm_rawSum (G := G) hq0 R (f 0)
    have hnb := one_le_norm_rawSum (G := G) hq0 R (f 1)
    have hnc := one_le_norm_rawSum (G := G) hq0 R (f 2)
    have hnd := one_le_norm_rawSum (G := G) hq0 R (f 3)
    have hRHS_split := sum_intBall_add_extBall (G := G) R (G.src e) (fun z =>
      (rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 1) z +
        rawSum G rawRatio R (f 2) z * rawSum G rawRatio R (f 3) z) +
      (3 / 14 : ℝ) * (rawSum G rawRatio R (f 0) z + rawSum G rawRatio R (f 1) z) *
        (rawSum G rawRatio R (f 2) z + rawSum G rawRatio R (f 3) z) +
      σ * (8 / 35 : ℝ) * (rawSum G rawRatio R (f 0) z - rawSum G rawRatio R (f 1) z) *
        (rawSum G rawRatio R (f 2) z - rawSum G rawRatio R (f 3) z))
    have hRHS_eq : ∑ z : V, ((rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 1) z +
          rawSum G rawRatio R (f 2) z * rawSum G rawRatio R (f 3) z) +
        (3 / 14 : ℝ) * (rawSum G rawRatio R (f 0) z + rawSum G rawRatio R (f 1) z) *
          (rawSum G rawRatio R (f 2) z + rawSum G rawRatio R (f 3) z) +
        σ * (8 / 35 : ℝ) * (rawSum G rawRatio R (f 0) z - rawSum G rawRatio R (f 1) z) *
          (rawSum G rawRatio R (f 2) z - rawSum G rawRatio R (f 3) z)) =
        (‖rawSum G rawRatio R (f 0)‖ * ‖rawSum G rawRatio R (f 1)‖ *
            ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 1)⟫ +
          ‖rawSum G rawRatio R (f 2)‖ * ‖rawSum G rawRatio R (f 3)‖ *
            ⟪rawEdgeVector G rawRatio R (f 2), rawEdgeVector G rawRatio R (f 3)⟫) +
        (3 / 14 : ℝ) * (
          ‖rawSum G rawRatio R (f 0)‖ * ‖rawSum G rawRatio R (f 2)‖ *
            ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 2)⟫ +
          ‖rawSum G rawRatio R (f 0)‖ * ‖rawSum G rawRatio R (f 3)‖ *
            ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 3)⟫ +
          ‖rawSum G rawRatio R (f 1)‖ * ‖rawSum G rawRatio R (f 2)‖ *
            ⟪rawEdgeVector G rawRatio R (f 1), rawEdgeVector G rawRatio R (f 2)⟫ +
          ‖rawSum G rawRatio R (f 1)‖ * ‖rawSum G rawRatio R (f 3)‖ *
            ⟪rawEdgeVector G rawRatio R (f 1), rawEdgeVector G rawRatio R (f 3)⟫) +
        σ * (8 / 35 : ℝ) * (
          ‖rawSum G rawRatio R (f 0)‖ * ‖rawSum G rawRatio R (f 2)‖ *
            ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 2)⟫ -
          ‖rawSum G rawRatio R (f 0)‖ * ‖rawSum G rawRatio R (f 3)‖ *
            ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 3)⟫ -
          ‖rawSum G rawRatio R (f 1)‖ * ‖rawSum G rawRatio R (f 2)‖ *
            ⟪rawEdgeVector G rawRatio R (f 1), rawEdgeVector G rawRatio R (f 2)⟫ +
          ‖rawSum G rawRatio R (f 1)‖ * ‖rawSum G rawRatio R (f 3)‖ *
            ⟪rawEdgeVector G rawRatio R (f 1), rawEdgeVector G rawRatio R (f 3)⟫) := by
      have hpt_alg (z : V) : (rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 1) z +
            rawSum G rawRatio R (f 2) z * rawSum G rawRatio R (f 3) z) +
          (3 / 14 : ℝ) * (rawSum G rawRatio R (f 0) z + rawSum G rawRatio R (f 1) z) *
            (rawSum G rawRatio R (f 2) z + rawSum G rawRatio R (f 3) z) +
          σ * (8 / 35 : ℝ) * (rawSum G rawRatio R (f 0) z - rawSum G rawRatio R (f 1) z) *
            (rawSum G rawRatio R (f 2) z - rawSum G rawRatio R (f 3) z) =
          (rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 1) z +
            rawSum G rawRatio R (f 2) z * rawSum G rawRatio R (f 3) z) +
          (3 / 14 : ℝ) * (
            rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 2) z +
            rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 3) z +
            rawSum G rawRatio R (f 1) z * rawSum G rawRatio R (f 2) z +
            rawSum G rawRatio R (f 1) z * rawSum G rawRatio R (f 3) z) +
          σ * (8 / 35 : ℝ) * (
            rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 2) z -
            rawSum G rawRatio R (f 0) z * rawSum G rawRatio R (f 3) z -
            rawSum G rawRatio R (f 1) z * rawSum G rawRatio R (f 2) z +
            rawSum G rawRatio R (f 1) z * rawSum G rawRatio R (f 3) z) := by ring
      simp_rw [hpt_alg]
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← inner_rawEdgeVector_mul_norms]
      ring
    have hLHS_split :
        ∑ z ∈ intBall G R (G.src e), (rawSum G rawRatio R (f 0) z ^ 2 +
          rawSum G rawRatio R (f 1) z ^ 2 + rawSum G rawRatio R (f 2) z ^ 2 +
          rawSum G rawRatio R (f 3) z ^ 2) +
        ∑ z ∈ extBall G R (G.src e), (rawSum G rawRatio R (f 0) z ^ 2 +
          rawSum G rawRatio R (f 1) z ^ 2 + rawSum G rawRatio R (f 2) z ^ 2 +
          rawSum G rawRatio R (f 3) z ^ 2) =
        ‖rawSum G rawRatio R (f 0)‖ ^ 2 + ‖rawSum G rawRatio R (f 1)‖ ^ 2 +
        ‖rawSum G rawRatio R (f 2)‖ ^ 2 + ‖rawSum G rawRatio R (f 3)‖ ^ 2 := by
      rw [← sum_intBall_add_extBall R (G.src e)]
      simp only [sum_add_distrib, ← EuclideanSpace.real_norm_sq_eq]
    rw [← mul_sum] at hsum_int
    simp only [sum_add_distrib] at hLHS_split
    conv at hsum_int => lhs; rw [sum_add_distrib, sum_add_distrib, sum_add_distrib]
    have hsq_sum : 4 ≤ ‖rawSum G rawRatio R (f 0)‖ ^ 2 + ‖rawSum G rawRatio R (f 1)‖ ^ 2 +
        ‖rawSum G rawRatio R (f 2)‖ ^ 2 + ‖rawSum G rawRatio R (f 3)‖ ^ 2 := by nlinarith
    have herr : 360 * (2 * rawRatio ^ 2) ^ (R - 3) ≤ 36 / 10 ^ 8 := by linarith
    have hquad : (1322905 / 1000000 : ℝ) / 2 *
          (‖rawSum G rawRatio R (f 0)‖ ^ 2 + ‖rawSum G rawRatio R (f 1)‖ ^ 2 +
            ‖rawSum G rawRatio R (f 2)‖ ^ 2 + ‖rawSum G rawRatio R (f 3)‖ ^ 2) ≤
        (‖rawSum G rawRatio R (f 0)‖ * ‖rawSum G rawRatio R (f 1)‖ *
            ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 1)⟫ +
          ‖rawSum G rawRatio R (f 2)‖ * ‖rawSum G rawRatio R (f 3)‖ *
            ⟪rawEdgeVector G rawRatio R (f 2), rawEdgeVector G rawRatio R (f 3)⟫) +
        (3 / 14 : ℝ) * (
          ‖rawSum G rawRatio R (f 0)‖ * ‖rawSum G rawRatio R (f 2)‖ *
            ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 2)⟫ +
          ‖rawSum G rawRatio R (f 0)‖ * ‖rawSum G rawRatio R (f 3)‖ *
            ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 3)⟫ +
          ‖rawSum G rawRatio R (f 1)‖ * ‖rawSum G rawRatio R (f 2)‖ *
            ⟪rawEdgeVector G rawRatio R (f 1), rawEdgeVector G rawRatio R (f 2)⟫ +
          ‖rawSum G rawRatio R (f 1)‖ * ‖rawSum G rawRatio R (f 3)‖ *
            ⟪rawEdgeVector G rawRatio R (f 1), rawEdgeVector G rawRatio R (f 3)⟫) +
        σ * (8 / 35 : ℝ) * (
          ‖rawSum G rawRatio R (f 0)‖ * ‖rawSum G rawRatio R (f 2)‖ *
            ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 2)⟫ -
          ‖rawSum G rawRatio R (f 0)‖ * ‖rawSum G rawRatio R (f 3)‖ *
            ⟪rawEdgeVector G rawRatio R (f 0), rawEdgeVector G rawRatio R (f 3)⟫ -
          ‖rawSum G rawRatio R (f 1)‖ * ‖rawSum G rawRatio R (f 2)‖ *
            ⟪rawEdgeVector G rawRatio R (f 1), rawEdgeVector G rawRatio R (f 2)⟫ +
          ‖rawSum G rawRatio R (f 1)‖ * ‖rawSum G rawRatio R (f 3)‖ *
            ⟪rawEdgeVector G rawRatio R (f 1), rawEdgeVector G rawRatio R (f 3)⟫) := by
      rw [← hRHS_eq, hRHS_split]
      linarith
    exact ⟨schurPairIneq_of_quad (sa := ‖rawSum G rawRatio R (f 0)‖)
        (sb := ‖rawSum G rawRatio R (f 1)‖) (sc := ‖rawSum G rawRatio R (f 2)‖)
        (sd := ‖rawSum G rawRatio R (f 3)‖)
        hsab_lo (inner_rawEdgeVector_le_one R _ _) hscd_lo
        hsac_lo (inner_rawEdgeVector_le_one R _ _) hsbd_lo (inner_rawEdgeVector_le_one R _ _)
        hsad_lo (inner_rawEdgeVector_le_one R _ _) hsbc_lo (inner_rawEdgeVector_le_one R _ _)
        hσ hnc hnd hquad,
      schurPairIneq_of_quad (sa := ‖rawSum G rawRatio R (f 2)‖)
        (sb := ‖rawSum G rawRatio R (f 3)‖) (sc := ‖rawSum G rawRatio R (f 0)‖)
        (sd := ‖rawSum G rawRatio R (f 1)‖)
        hscd_lo (inner_rawEdgeVector_le_one R _ _) hsab_lo
        hsac_lo (inner_rawEdgeVector_le_one R _ _) hsbd_lo (inner_rawEdgeVector_le_one R _ _)
        hsbc_lo (inner_rawEdgeVector_le_one R _ _) hsad_lo (inner_rawEdgeVector_le_one R _ _)
        hσ hna hnb (by linarith)⟩
  exact ⟨fun i => norm_rawEdgeVector hq0 R (f i),
    hsab_lo, hscd_lo, hsac_lo, hsad_lo, hsbc_lo, hsbd_lo,
    (hschur 1 (Or.inl rfl)).1, (hschur (-1) (Or.inr rfl)).1,
    (hschur 1 (Or.inl rfl)).2, (hschur (-1) (Or.inr rfl)).2⟩

end GraphBounds

/-- **Universal admissibility radius.** There exists a single radius `R : ℕ` such that for *every*
finite loopless cubic multigraph `G`, every three incident edges at any vertex satisfy
`IsAdmissibleStar` and every four outer incident edges at any edge satisfy `IsAdmissiblePair` under
`rawEdgeVector G rawRatio R`. -/
theorem exists_radius_admissible :
    ∃ R : ℕ, ∀ (V E : Type) [Fintype V] [Fintype E] (G : Multigraph V E),
      G.Loopless → G.MaxDegreeLE 3 →
      (∀ (u : V) (f : Fin 3 → E), (∀ i, f i ∈ G.incidenceSet u) →
        IsAdmissibleStar (fun i => rawEdgeVector G rawRatio R (f i))) ∧
      (∀ (e : E) (f : Fin 4 → E),
        f 0 ∈ G.incidenceSet (G.src e) → f 1 ∈ G.incidenceSet (G.src e) →
        f 2 ∈ G.incidenceSet (G.tgt e) → f 3 ∈ G.incidenceSet (G.tgt e) →
        IsAdmissiblePair (fun i => rawEdgeVector G rawRatio R (f i))) := by
  have hlt1 : 2 * rawRatio ^ 2 < 1 := by norm_num [rawRatio]
  have hnn : 0 ≤ 2 * rawRatio ^ 2 := by positivity
  have htend := tendsto_pow_atTop_nhds_zero_of_lt_one hnn hlt1
  obtain ⟨N, hN⟩ := (tendsto_atTop_nhds.mp htend (Set.Iio ((1 : ℝ) / 10 ^ 9))
    (by norm_num : (0 : ℝ) ∈ Set.Iio (1 / 10 ^ 9)) isOpen_Iio)
  refine ⟨N + 3, fun V E _ _ G hloop hdeg => ?_⟩
  have hsmall : (2 * rawRatio ^ 2) ^ (N + 3 - 3) ≤ (1 : ℝ) / 10 ^ 9 := by
    rw [Nat.add_sub_cancel]
    exact (hN N le_rfl).le
  exact ⟨isAdmissibleStar_rawEdgeVector hloop hdeg (by omega) hsmall,
    isAdmissiblePair_rawEdgeVector hloop hdeg (by omega) hsmall⟩

end Cslib.Circuits.Frontier.Gaussian.PairBound
