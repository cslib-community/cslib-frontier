/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.MatrixMultiplication.NineQuarters
public import CslibFrontier.Computability.Circuit.Arithmetic.MatrixMultiplication.StrassenRank
public import CslibFrontier.Computability.Circuit.Frontier.Compiler
public import CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `3`-tensor CP-rank fan-in-`2` circuit lower bounds (`3.041n`)

Rather than sweeping a circuit graph along a `1`D layout into a read-once branching program (`2`-way
matrix rank), this module cuts `Compiler.graph c` once into three vertex parts `V = V₀ ⊔ V₁ ⊔ V₂`
using `exists_balanced_threeWayCut`:

1. **`3`-way network splicing into square matrix multiplication.** Given a coloring
   `col : Compiler.Vertex c → Fin 3` compatible with an input tripartition `p : Fin n → Fin 3`
   (`Compiler.site c i = some v → p i = col v`), the unique satisfying edge assignment of
   `Compiler.network c I Acc` decomposes into three local validity predicates on `V₀, V₁, V₂`
   communicating solely across the three pairwise cuts `E(V₀, V₁)`, `E(V₁, V₂)`, `E(V₂, V₀)`. Over
   any commutative semiring `K`, `partitionThreeTensor K p S` is therefore a tensor restriction of
   `Tensor.mm D D D` with `D = |U| ^ max(|E₀₁|, |E₁₂|, |E₂₀|)`.
2. **Degree-`≤ 1` input rebalancing and unread-input rank shortcut.** Every input vertex
   `.signal ⟨.input i, hi⟩` in `Compiler.graph c` has degree at most `1`, so greedy single-input
   moves convert the `o(|V|)`-balanced `3`-way cut into an *exact* `BalancedTripartition` (`≥ ⌊n/3⌋`
   inputs per leg) while perturbing each pairwise cut by `o(|V|)`. If the circuit ignores more than
   `2 δ n` inputs, `partitionThreeTensor` already has trivial CP-rank `|U| ^ ((2 / 3 - o(1)) n)`
   without invoking matrix multiplication; otherwise `β₁ ≤ s - n + 2 δ n + 1`.
3. **Wiring `ω ≤ 9 / 4` (`3.041n`).** Combining `exists_rank_mm_le_rpow` with
   `NineQuarters.omega_le_nine_quarters` (`ω(K) ≤ 9 / 4` in characteristic zero) and
   `threeWayCapCoefficient ≤ 21773 / 100000` yields `(3041 / 1000 - ε) n < c.innerSize` for every
   fan-in-`2` circuit deciding a `ThreeTensorHard` set (`innerSize_gt_3041_of_threeTensorHard`),
   together with unconditional finite-counting non-vacuity (`exists_threeTensorHard` over arbitrary
   fields and `exists_set_innerSize_gt_3041`).

## Main definitions

* `Cslib.Circuits.Frontier.TensorRank.BalancedTripartition`: an input `3`-coloring
  `p : Fin n → Fin 3` with at least `n / 3` inputs in each part.
* `Cslib.Circuits.Frontier.TensorRank.mergeTripartition`: reassembles `Fin n → U` from its three
  part restrictions.
* `Cslib.Circuits.Frontier.TensorRank.partitionThreeTensor`: the `0-1` order-three tensor of
  `S ⊆ (Fin n → U)` under an input tripartition `p`.
* `Cslib.Circuits.Frontier.TensorRank.ThreeTensorHard`:
  `¬Tensor.Rank r (partitionThreeTensor K p S)` simultaneously across every
  `BalancedTripartition n p`.

## Main results

* `Cslib.Circuits.Frontier.TensorRank.isRestriction_partitionThreeTensor_mm`: `3`-way network
  splicing of a circuit into `Tensor.mm D D D`.
* `Cslib.Circuits.Frontier.TensorRank.exists_threeTensorHard`: nonconstructive finite-counting
  existence of `ThreeTensorHard` sets over *any* field `K` (including `ZMod 2` and `ℚ`).
* `Cslib.Circuits.Frontier.TensorRank.innerSize_gt_of_threeTensorHard`: parametric fan-in-`2` lower
  bound `(1 + 1 / (omega K * threeWayCapCoefficient) - ε) * n < c.innerSize`.
* `Cslib.Circuits.Frontier.TensorRank.innerSize_gt_3041_of_threeTensorHard`: unconditional
  `(3041 / 1000 - ε) * n < c.innerSize` via `NineQuarters.omega_le_nine_quarters`.
* `Cslib.Circuits.Frontier.TensorRank.exists_set_innerSize_gt_3041`: end-to-end unconditional
  existence of `U`-ary functions requiring `> (3.041 - ε) n` inner fan-in-`2` gates.
-/

public section

open Real Set

namespace Cslib.Circuits.Frontier.TensorRank

open Cslib.Circuits Cslib.Circuits.Arithmetic.MatrixMultiplication Cslib.Tensor

/-! ### Balanced input tripartitions and `ThreeTensorHard` predicates -/

/-- An input `3`-coloring `p : Fin n → Fin 3` is *balanced* when each color class has size at least
`n / 3`. -/
def BalancedTripartition (n : ℕ) (p : Fin n → Fin 3) : Prop :=
  ∀ c : Fin 3, n / 3 ≤ {i : Fin n | p i = c}.ncard

/-- Characterization of `BalancedTripartition`: every fiber has size at least `n / 3`. -/
theorem balancedTripartition_iff (n : ℕ) (p : Fin n → Fin 3) :
    BalancedTripartition n p ↔ ∀ c : Fin 3, n / 3 ≤ {i : Fin n | p i = c}.ncard := by
  rfl

/-- Reassemble a full input `Fin n → U` from partial assignments on the three fibers of `p`. -/
def mergeTripartition {n : ℕ} {U : Type*} (p : Fin n → Fin 3)
    (x₀ : {i : Fin n // p i = 0} → U)
    (x₁ : {i : Fin n // p i = 1} → U)
    (x₂ : {i : Fin n // p i = 2} → U) (i : Fin n) : U :=
  if h0 : p i = 0 then x₀ ⟨i, h0⟩
  else if h1 : p i = 1 then x₁ ⟨i, h1⟩
  else x₂ ⟨i, by
    rcases hp : p i with ⟨_ | _ | _ | _, hlt⟩
    · exact absurd hp h0
    · exact absurd hp h1
    · rfl
    · omega⟩

/-- The `0-1` order-three tensor over `K` induced by `S : Set (Fin n → U)` under an input
tripartition `p : Fin n → Fin 3`. -/
noncomputable def partitionThreeTensor (K : Type*) [Zero K] [One K]
    {n : ℕ} {U : Type*} (p : Fin n → Fin 3) (S : Set (Fin n → U)) :
    Tensor K ({i : Fin n // p i = 0} → U) ({i : Fin n // p i = 1} → U)
      ({i : Fin n // p i = 2} → U) :=
  open Classical in
  fun x₀ x₁ x₂ => if mergeTripartition p x₀ x₁ x₂ ∈ S then 1 else 0

/-- Evaluation of `partitionThreeTensor K p S` on partial assignments `(x₀, x₁, x₂)`. -/
theorem partitionThreeTensor_apply (K : Type*) [Zero K] [One K] {n : ℕ} {U : Type*}
    (p : Fin n → Fin 3) (S : Set (Fin n → U))
    (x₀ : {i : Fin n // p i = 0} → U) (x₁ : {i : Fin n // p i = 1} → U)
    (x₂ : {i : Fin n // p i = 2} → U) :
    partitionThreeTensor K p S x₀ x₁ x₂ =
      open Classical in if mergeTripartition p x₀ x₁ x₂ ∈ S then 1 else 0 := by
  rfl

/-- A subset `S ⊆ (Fin n → U)` is *`3`-tensor hard* at CP-rank `r` over `K` if for *every* balanced
input tripartition `p`, `partitionThreeTensor K p S` does not have CP-rank `≤ r`. -/
@[expose] def ThreeTensorHard (K : Type*) [CommSemiring K] {n : ℕ} {U : Type*}
    (r : ℕ) (S : Set (Fin n → U)) : Prop :=
  ∀ p : Fin n → Fin 3, BalancedTripartition n p → ¬Tensor.Rank r (partitionThreeTensor K p S)

/-- `mergeTripartition` reads `x₀` on fiber `0`. -/
@[simp] theorem mergeTripartition_apply_zero {n : ℕ} {U : Type*} (p : Fin n → Fin 3)
    (x₀ : {i : Fin n // p i = 0} → U) (x₁ : {i : Fin n // p i = 1} → U)
    (x₂ : {i : Fin n // p i = 2} → U) {i : Fin n} (h0 : p i = 0) :
    mergeTripartition p x₀ x₁ x₂ i = x₀ ⟨i, h0⟩ := by
  simp [mergeTripartition, h0]

/-- `mergeTripartition` reads `x₁` on fiber `1`. -/
@[simp] theorem mergeTripartition_apply_one {n : ℕ} {U : Type*} (p : Fin n → Fin 3)
    (x₀ : {i : Fin n // p i = 0} → U) (x₁ : {i : Fin n // p i = 1} → U)
    (x₂ : {i : Fin n // p i = 2} → U) {i : Fin n} (h1 : p i = 1) :
    mergeTripartition p x₀ x₁ x₂ i = x₁ ⟨i, h1⟩ := by
  simp [mergeTripartition, h1]

/-- `mergeTripartition` reads `x₂` on fiber `2`. -/
@[simp] theorem mergeTripartition_apply_two {n : ℕ} {U : Type*} (p : Fin n → Fin 3)
    (x₀ : {i : Fin n // p i = 0} → U) (x₁ : {i : Fin n // p i = 1} → U)
    (x₂ : {i : Fin n // p i = 2} → U) {i : Fin n} (h2 : p i = 2) :
    mergeTripartition p x₀ x₁ x₂ i = x₂ ⟨i, h2⟩ := by
  have hn0 : p i ≠ 0 := by rw [h2]; decide
  have hn1 : p i ≠ 1 := by rw [h2]; decide
  simp [mergeTripartition, hn0, hn1]

private def mergeTripartitionEquiv {n : ℕ} {U : Type*} (p : Fin n → Fin 3) :
    (({i : Fin n // p i = 0} → U) × ({i : Fin n // p i = 1} → U) ×
      ({i : Fin n // p i = 2} → U)) ≃ (Fin n → U) where
  toFun q := mergeTripartition p q.1 q.2.1 q.2.2
  invFun x := (fun i => x i.val, fun i => x i.val, fun i => x i.val)
  left_inv q := by
    rcases q with ⟨x₀, x₁, x₂⟩
    ext ⟨i, hi⟩
    · exact mergeTripartition_apply_zero p x₀ x₁ x₂ hi
    · exact mergeTripartition_apply_one p x₀ x₁ x₂ hi
    · exact mergeTripartition_apply_two p x₀ x₁ x₂ hi
  right_inv x := by
    funext i
    rcases hp : p i with ⟨_ | _ | _ | _, hlt⟩
    · exact mergeTripartition_apply_zero p _ _ _ hp
    · exact mergeTripartition_apply_one p _ _ _ hp
    · exact mergeTripartition_apply_two p _ _ _ hp
    · omega

private theorem ncard_parts_sum {n : ℕ} (p : Fin n → Fin 3) :
    {i : Fin n | p i = 0}.ncard + {i : Fin n | p i = 1}.ncard +
      {i : Fin n | p i = 2}.ncard = n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := p) (s := Finset.univ) (t := Finset.univ)
    fun _ _ => Finset.mem_univ _
  simp only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_three] at h
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  omega

private theorem BalancedTripartition.ncard_le {n : ℕ} {p : Fin n → Fin 3}
    (hp : BalancedTripartition n p) (c : Fin 3) :
    {i : Fin n | p i = c}.ncard ≤ n / 3 + 2 := by
  have hsum := ncard_parts_sum p
  have h0 := hp 0; have h1 := hp 1; have h2 := hp 2
  fin_cases c <;> dsimp only [Fin.reduceFinMk] <;> omega

/-! ### Non-vacuity: counting existence of `ThreeTensorHard` sets over arbitrary fields -/

/-- **Existence of `ThreeTensorHard` sets over any field `K`.** By union-bounding
`card_rank_indicatorThreeTensor_le` over all balanced `p : Fin n → Fin 3` (`≤ 3 ^ n` partitions),
whenever `3 ^ n * (3 * |U| ^ n + 1) ^ (3 * r * |U| ^ (n / 3 + 2)) < 2 ^ (|U| ^ n)`, there exists
`S : Set (Fin n → U)` satisfying `ThreeTensorHard K r S` (nonconstructive finite counting). -/
theorem exists_threeTensorHard (K : Type*) [Field K] {n : ℕ} {U : Type*} [Fintype U]
    (hU : 1 ≤ Fintype.card U) {r : ℕ}
    (hcount :
      3 ^ n * (3 * Fintype.card U ^ n + 1) ^ (3 * r * Fintype.card U ^ (n / 3 + 2)) <
        2 ^ (Fintype.card U ^ n)) :
    ∃ S : Set (Fin n → U), ThreeTensorHard K r S := by
  classical
  set q := Fintype.card U
  let BadP (p : Fin n → Fin 3) : Finset (Finset (Fin n → U)) :=
    Finset.univ.filter fun S => Tensor.Rank r (partitionThreeTensor K p (S : Set (Fin n → U)))
  let BalFin : Finset (Fin n → Fin 3) := Finset.univ.filter (BalancedTripartition n)
  have hBal_card : BalFin.card ≤ 3 ^ n := (Finset.card_filter_le _ _).trans (by simp)
  have hBadP_le (p : Fin n → Fin 3) (hp : p ∈ BalFin) :
      (BadP p).card ≤ (3 * q ^ n + 1) ^ (3 * r * q ^ (n / 3 + 2)) := by
    have hbal : BalancedTripartition n p := (Finset.mem_filter.mp hp).2
    let X₀ := {i : Fin n // p i = 0} → U
    let X₁ := {i : Fin n // p i = 1} → U
    let X₂ := {i : Fin n // p i = 2} → U
    let eqv := mergeTripartitionEquiv (U := U) p
    let finEqv : Finset (X₀ × X₁ × X₂) ≃ Finset (Fin n → U) :=
      { toFun := fun T => T.map eqv.toEmbedding
        invFun := fun S => S.map eqv.symm.toEmbedding
        left_inv := fun T => by ext x; simp
        right_inv := fun S => by ext y; simp }
    have hbij : (BadP p).card =
        (Finset.univ.filter fun T : Finset (X₀ × X₁ × X₂) =>
          Tensor.Rank r (indicatorThreeTensor K (T : Set (X₀ × X₁ × X₂)))).card := by
      refine Finset.card_equiv finEqv.symm fun S => ?_
      have hten_eq :
          indicatorThreeTensor K (X₀ := X₀) (X₁ := X₁) (X₂ := X₂) ↑(finEqv.symm S) =
            partitionThreeTensor K (U := U) p ↑S := by
        funext x₀ x₁ x₂
        simp only [indicatorThreeTensor, partitionThreeTensor, finEqv, Equiv.coe_fn_symm_mk,
          Finset.mem_coe, Finset.mem_map_equiv, Equiv.symm_symm]
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd h1 h2
        · exact absurd h2 h1
        · rfl
      simp only [BadP, Finset.mem_filter, Finset.mem_univ, true_and, hten_eq]
    rw [hbij]
    have hcard_prod : Fintype.card X₀ * Fintype.card X₁ * Fintype.card X₂ = q ^ n := by
      simpa only [X₀, X₁, X₂, q, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        mul_assoc] using Fintype.card_congr eqv
    have hcard_part (c : Fin 3) : Fintype.card ({i : Fin n // p i = c} → U) ≤ q ^ (n / 3 + 2) := by
      rw [Fintype.card_fun]
      have hsub_card : Fintype.card {i : Fin n // p i = c} = {i : Fin n | p i = c}.ncard := by
        rw [← Nat.card_eq_fintype_card]; exact Nat.card_coe_set_eq {i : Fin n | p i = c}
      rw [hsub_card]
      exact Nat.pow_le_pow_right hU (hbal.ncard_le c)
    have hsum_parts : Fintype.card X₀ + Fintype.card X₁ + Fintype.card X₂ ≤
        3 * q ^ (n / 3 + 2) := by
      have h0 := hcard_part 0; have h1 := hcard_part 1; have h2 := hcard_part 2
      dsimp [X₀, X₁, X₂]; omega
    refine (card_rank_indicatorThreeTensor_le K X₀ X₁ X₂ r).trans ?_
    rw [hcard_prod]
    exact Nat.pow_le_pow_right (by omega)
      (by calc r * (Fintype.card X₀ + Fintype.card X₁ + Fintype.card X₂)
            ≤ r * (3 * q ^ (n / 3 + 2)) := Nat.mul_le_mul_left r hsum_parts
          _ = 3 * r * q ^ (n / 3 + 2) := by ring)
  by_contra! hall
  have huniv_sub : (Finset.univ : Finset (Finset (Fin n → U))) ⊆ BalFin.biUnion BadP := by
    intro S _
    have hnot : ¬ThreeTensorHard K r (S : Set (Fin n → U)) := hall (S : Set (Fin n → U))
    unfold ThreeTensorHard at hnot
    push Not at hnot
    obtain ⟨p, hbal, hrk⟩ := hnot
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hbal⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ S, hrk⟩⟩
  have hcard_univ : 2 ^ (q ^ n) = (Finset.univ : Finset (Finset (Fin n → U))).card := by
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fun, Fintype.card_fin]
  have hle_tot : 2 ^ (q ^ n) ≤ 3 ^ n * (3 * q ^ n + 1) ^ (3 * r * q ^ (n / 3 + 2)) := by
    rw [hcard_univ]
    calc (Finset.univ : Finset (Finset (Fin n → U))).card
        ≤ (BalFin.biUnion BadP).card := Finset.card_le_card huniv_sub
      _ ≤ ∑ p ∈ BalFin, (BadP p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ BalFin, (3 * q ^ n + 1) ^ (3 * r * q ^ (n / 3 + 2)) :=
          Finset.sum_le_sum hBadP_le
      _ = BalFin.card * (3 * q ^ n + 1) ^ (3 * r * q ^ (n / 3 + 2)) := by simp
      _ ≤ 3 ^ n * (3 * q ^ n + 1) ^ (3 * r * q ^ (n / 3 + 2)) :=
          Nat.mul_le_mul_right _ hBal_card
  exact absurd hle_tot (not_le.mpr hcount)

/-- **Asymptotic existence of `ThreeTensorHard` sets.** For any field `K`, finite alphabet `U` with
`2 ≤ |U|`, and `δ > 0`, for all sufficiently large `n` there exists `S : Set (Fin n → U)` that is
`ThreeTensorHard` at rank `⌊(|U| : ℝ) ^ ((2 / 3 - δ) * n)⌋₊`. -/
private theorem exists_threeTensorHard_eventually (K : Type*) [Field K] {U : Type*} [Fintype U]
    (hU : 2 ≤ Fintype.card U) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ S : Set (Fin n → U),
        ThreeTensorHard K ⌊(Fintype.card U : ℝ) ^ ((2 / 3 - δ) * (n : ℝ))⌋₊ S := by
  set q : ℕ := Fintype.card U
  have hq2 : 2 ≤ q := hU
  have hq_real_gt1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hq_pos : (0 : ℝ) < (q : ℝ) := by positivity
  set b : ℝ := (q : ℝ) ^ δ
  have hb_gt1 : 1 < b := Real.one_lt_rpow hq_real_gt1 hδ
  -- Both `(n : ℝ) / (q : ℝ) ^ n → 0` and `(n : ℝ) ^ 2 / b ^ n → 0` as `n → ∞`.
  have ht1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hq_real_gt1
  have ht2 := tendsto_pow_const_div_const_pow_of_one_lt 2 hb_gt1
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp ht1 (1 / 8) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp ht2
    (1 / (24 * (q : ℝ) ^ 5)) (by positivity)
  refine ⟨max (max N₁ N₂) 4, fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn2 : N₂ ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  refine exists_threeTensorHard K (by omega : 1 ≤ q) ?_
  set r := ⌊(q : ℝ) ^ ((2 / 3 - δ) * (n : ℝ))⌋₊
  -- Coarse base-`2` exponent comparison:
  -- `3 ^ n ≤ 2 ^ (2 * n)` and `3 * q ^ n + 1 ≤ 4 * q ^ n ≤ q ^ (n + 2) ≤ (2 ^ q) ^ (n + 2)`.
  have h3_pow : 3 ^ n ≤ 2 ^ (2 * n) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by norm_num : 3 ≤ 2 ^ 2) n
  have hbase_le : 3 * q ^ n + 1 ≤ 2 ^ (q * (n + 2)) := by
    have hq_pow_ge1 : 1 ≤ q ^ n := Nat.one_le_pow n q (by omega)
    have h4 : 4 ≤ q ^ 2 := by nlinarith only [hq2]
    have hq_lt_2q : q ≤ 2 ^ q := Nat.lt_two_pow_self.le
    calc 3 * q ^ n + 1 ≤ 4 * q ^ n := by omega
      _ ≤ q ^ 2 * q ^ n := Nat.mul_le_mul_right _ h4
      _ = q ^ (n + 2) := by rw [← pow_add, add_comm]
      _ ≤ (2 ^ q) ^ (n + 2) := Nat.pow_le_pow_left hq_lt_2q (n + 2)
      _ = 2 ^ (q * (n + 2)) := (pow_mul 2 q (n + 2)).symm
  set M := 3 * r * q ^ (n / 3 + 2)
  have hlhs_le : 3 ^ n * (3 * q ^ n + 1) ^ M ≤ 2 ^ (2 * n + q * (n + 2) * M) := by
    calc 3 ^ n * (3 * q ^ n + 1) ^ M
        ≤ 2 ^ (2 * n) * (2 ^ (q * (n + 2))) ^ M := by gcongr
      _ = 2 ^ (2 * n + q * (n + 2) * M) := by rw [← pow_mul, ← pow_add]
  refine hlhs_le.trans_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) ?_)
  -- Show `2 * n + q * (n + 2) * M < q ^ n` in `ℝ`.
  suffices hreal : ((2 * n + q * (n + 2) * M : ℕ) : ℝ) < ((q ^ n : ℕ) : ℝ) by
    exact_mod_cast hreal
  push_cast
  have hr_le : (r : ℝ) ≤ (q : ℝ) ^ ((2 / 3 - δ) * (n : ℝ)) :=
    Nat.floor_le (by positivity)
  have hdiv3 : ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := by exact_mod_cast Nat.cast_div_le
  have hqn3 : (q : ℝ) ^ (n / 3 + 2 : ℕ) ≤ (q : ℝ) ^ 2 * (q : ℝ) ^ ((n : ℝ) / 3) := by
    rw [pow_add, mul_comm _ ((q : ℝ) ^ 2), ← Real.rpow_natCast (q : ℝ) (n / 3)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq_real_gt1.le hdiv3)
      (by positivity)
  have hprod_rpow : (q : ℝ) ^ ((2 / 3 - δ) * (n : ℝ)) * (q : ℝ) ^ ((n : ℝ) / 3) =
      (q : ℝ) ^ n / b ^ n := by
    rw [← Real.rpow_add hq_pos,
      show (2 / 3 - δ) * (n : ℝ) + (n : ℝ) / 3 = (n : ℝ) - δ * (n : ℝ) by ring,
      Real.rpow_sub hq_pos, Real.rpow_natCast]
    congr 1
    dsimp [b]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq_pos.le]
  have hM_real : (M : ℝ) ≤ 3 * (q : ℝ) ^ 2 * ((q : ℝ) ^ n / b ^ n) := by
    dsimp [M]
    push_cast
    calc 3 * (r : ℝ) * (q : ℝ) ^ (n / 3 + 2 : ℕ)
        ≤ 3 * (q : ℝ) ^ ((2 / 3 - δ) * (n : ℝ)) * ((q : ℝ) ^ 2 * (q : ℝ) ^ ((n : ℝ) / 3)) := by
          gcongr
      _ = 3 * (q : ℝ) ^ 2 * ((q : ℝ) ^ ((2 / 3 - δ) * (n : ℝ)) * (q : ℝ) ^ ((n : ℝ) / 3)) := by
          ring
      _ = 3 * (q : ℝ) ^ 2 * ((q : ℝ) ^ n / b ^ n) := by rw [hprod_rpow]
  have hn_add2 : (n : ℝ) + 2 ≤ 2 * (n : ℝ) := by
    have : (4 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn4
    linarith only [this]
  have hd1 := hN₁ n hn1
  rw [Real.dist_eq, sub_zero, pow_one, abs_of_nonneg (by positivity)] at hd1
  have hterm1 : 2 * (n : ℝ) < 1 / 4 * (q : ℝ) ^ n := by
    have hm := mul_lt_mul_of_pos_right hd1 (pow_pos hq_pos n)
    rw [div_mul_cancel₀ _ (pow_pos hq_pos n).ne'] at hm
    linarith only [hm]
  have hd2 := hN₂ n hn2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hd2
  have hterm2 : (q : ℝ) * ((n : ℝ) + 2) * (M : ℝ) < 1 / 2 * (q : ℝ) ^ n := by
    have hm := mul_lt_mul_of_pos_right hd2 (pow_pos (by positivity : 0 < b) n)
    rw [div_mul_cancel₀ _ (pow_pos (by positivity : 0 < b) n).ne'] at hm
    have hstep1 : (q : ℝ) * ((n : ℝ) + 2) * (M : ℝ) ≤
        6 * (q : ℝ) ^ 3 * (n : ℝ) * ((q : ℝ) ^ n / b ^ n) := by
      have hm1 := mul_le_mul (mul_le_mul_of_nonneg_left hn_add2 hq_pos.le) hM_real
        (Nat.cast_nonneg _) (by positivity)
      linarith only [hm1, show (q : ℝ) * (2 * (n : ℝ)) *
        (3 * (q : ℝ) ^ 2 * ((q : ℝ) ^ n / b ^ n)) =
        6 * (q : ℝ) ^ 3 * (n : ℝ) * ((q : ℝ) ^ n / b ^ n) by ring]
    have hn_le_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 :=
      le_self_pow₀ (by exact_mod_cast (by omega : 1 ≤ n)) two_ne_zero
    have hq3_le_q5 : (q : ℝ) ^ 3 ≤ (q : ℝ) ^ 5 := pow_le_pow_right₀ hq_real_gt1.le (by norm_num)
    have hfrac_lt : 6 * (q : ℝ) ^ 3 * (n : ℝ) / b ^ n < 1 / 2 := by
      rw [div_lt_iff₀ (pow_pos (by positivity : 0 < b) n)]
      have hle_n2 : 6 * (q : ℝ) ^ 3 * (n : ℝ) ≤ 6 * (q : ℝ) ^ 5 * (n : ℝ) ^ 2 := by
        have hm_q := mul_le_mul hq3_le_q5 hn_le_sq (Nat.cast_nonneg _) (by positivity)
        linarith only [hm_q]
      have hm_b := mul_lt_mul_of_pos_left hm (by positivity : (0 : ℝ) < 6 * (q : ℝ) ^ 5)
      have hsimpl : 6 * (q : ℝ) ^ 5 * (1 / (24 * (q : ℝ) ^ 5) * b ^ n) = 1 / 4 * b ^ n := by
        field_simp; ring
      rw [hsimpl] at hm_b
      have hb_pos : 0 < b ^ n := pow_pos (by positivity : 0 < b) n
      linarith only [hle_n2, hm_b, hb_pos]
    have hm_qn := mul_lt_mul_of_pos_right hfrac_lt (pow_pos hq_pos n)
    have heq_rhs : 6 * (q : ℝ) ^ 3 * (n : ℝ) / b ^ n * (q : ℝ) ^ n =
        6 * (q : ℝ) ^ 3 * (n : ℝ) * ((q : ℝ) ^ n / b ^ n) := by ring
    rw [heq_rhs] at hm_qn
    linarith only [hstep1, hm_qn]
  have hqn_pos : 0 < (q : ℝ) ^ n := pow_pos hq_pos n
  linarith only [hterm1, hterm2, hqn_pos]

/-! ### `3`-way network splicing into `Tensor.mm D D D` -/

private theorem finThreeCases (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  fin_cases k <;> decide

section Splicing

/-- **`3`-way circuit splicing into square matrix multiplication.** Let `c : Circuit σ n 1` be a
circuit over a finite nonempty alphabet `U`, `col : Compiler.Vertex c → Fin 3` a vertex
`3`-coloring, and `p : Fin n → Fin 3` an input `3`-coloring compatible with `Compiler.site c`
(`site c i = some v → p i = col v`). If every pairwise edge cut
`G.edgeCut {v | col v = k} ∩ G.edgeCut {v | col v = k + 1}` has size at most `B`, then over *any*
commutative semiring `K`, `partitionThreeTensor K p {x | c.eval I x 0 ∈ Acc 0}` is a restriction of
`Tensor.mm (|U| ^ B) (|U| ^ B) (|U| ^ B)`. -/
theorem isRestriction_partitionThreeTensor_mm (K : Type*) [CommSemiring K]
    {σ : Signature} {n : ℕ} {U : Type*} [Fintype U] [Nonempty U]
    (c : Circuit σ n 1) (I : Interpretation σ U) (Acc : Fin 1 → Set U)
    (col : Compiler.Vertex c → Fin 3) (p : Fin n → Fin 3)
    (hcompat : ∀ i v, Compiler.site c i = some v → p i = col v) {B : ℕ}
    (hcut : ∀ k : Fin 3,
      ((Compiler.graph c).edgeCut {v | col v = k} ∩
        (Compiler.graph c).edgeCut {v | col v = k + 1}).ncard ≤ B) :
    Tensor.IsRestriction
      (partitionThreeTensor K p {x | c.eval I x 0 ∈ Acc 0})
      (Tensor.mm (Fintype.card U ^ B) (Fintype.card U ^ B) (Fintype.card U ^ B) :
        Tensor K _ _ _) := by
  classical
  set G := Compiler.graph c
  set N_net := Compiler.network c I Acc
  set S_acc : Set (Fin n → U) := {x | c.eval I x 0 ∈ Acc 0}
  obtain ⟨u₀⟩ := ‹Nonempty U›
  have : Fintype (Compiler.Edge c) := Fintype.ofFinite _
  -- Six disjoint edge classes: internal `IntE k` and pairwise cross-cuts `CutE k`.
  let IntE (k : Fin 3) := {e : Compiler.Edge c // col (G.src e) = k ∧ col (G.tgt e) = k}
  let CutE (k : Fin 3) :=
    {e : Compiler.Edge c // e ∈ G.edgeCut {v | col v = k} ∩ G.edgeCut {v | col v = k + 1}}
  have mem_inter_edgeCut_iff (a b : Fin 3) (hab : a ≠ b) (e : Compiler.Edge c) :
      (e ∈ G.edgeCut {v | col v = a} ∩ G.edgeCut {v | col v = b}) ↔
        ((col (G.src e) = a ∧ col (G.tgt e) = b) ∨
          (col (G.src e) = b ∧ col (G.tgt e) = a)) := by
    simp only [mem_inter_iff, Multigraph.mem_edgeCut, mem_ofPred_eq]
    have hsrc : ¬(col (G.src e) = a ∧ col (G.src e) = b) :=
      fun h => hab (h.1.symm.trans h.2)
    have htgt : ¬(col (G.tgt e) = a ∧ col (G.tgt e) = b) :=
      fun h => hab (h.1.symm.trans h.2)
    tauto
  have hcut01 := mem_inter_edgeCut_iff 0 1 (by decide)
  have hcut12 := mem_inter_edgeCut_iff 1 2 (by decide)
  have hcut20 := mem_inter_edgeCut_iff 2 0 (by decide)
  let triple {A : Fin 3 → Type _} (x₀ : A 0) (x₁ : A 1) (x₂ : A 2) : ∀ k, A k :=
    Fin.cons x₀ (Fin.cons x₁ (Fin.cons x₂ (fun i => i.elim0)))
  let glueEdges (α : ∀ k, IntE k → U) (a : ∀ k, CutE k → U) (e : Compiler.Edge c) : U :=
    if h0 : col (G.src e) = 0 ∧ col (G.tgt e) = 0 then α 0 ⟨e, h0⟩
    else if h1 : col (G.src e) = 1 ∧ col (G.tgt e) = 1 then α 1 ⟨e, h1⟩
    else if h2 : col (G.src e) = 2 ∧ col (G.tgt e) = 2 then α 2 ⟨e, h2⟩
    else if hc0 : e ∈ G.edgeCut {v | col v = 0} ∩ G.edgeCut {v | col v = 1} then a 0 ⟨e, hc0⟩
    else if hc1 : e ∈ G.edgeCut {v | col v = 1} ∩ G.edgeCut {v | col v = 2} then a 1 ⟨e, hc1⟩
    else if hc2 : e ∈ G.edgeCut {v | col v = 2} ∩ G.edgeCut {v | col v = 0} then a 2 ⟨e, hc2⟩
    else u₀
  -- A vertex sees only its own internal edges and the cuts incident to its colour.
  let localInternal (k : Fin 3) (α : ∀ j, IntE j → U) (j : Fin 3) (e : IntE j) :=
    if j = k then α j e else u₀
  let localCut (k : Fin 3) (a : ∀ j, CutE j → U) (j : Fin 3) (e : CutE j) :=
    if j = k ∨ j + 1 = k then a j e else u₀
  have glue_eq_at (α : ∀ k, IntE k → U) (a : ∀ k, CutE k → U) (k : Fin 3)
      {v : Compiler.Vertex c} (hv : col v = k) {e : Compiler.Edge c}
      (he : G.src e = v ∨ G.tgt e = v) :
      glueEdges α a e = glueEdges (localInternal k α) (localCut k a) e := by
    rcases finThreeCases k with rfl | rfl | rfl <;> rcases he with rfl | rfl <;>
      simp only [glueEdges, hcut01, hcut12, hcut20, hv, Fin.reduceEq,
        true_and, false_and, and_true, and_false, false_or, or_false, ↓reduceDIte] <;> rfl
  have glue_restrict (β : Compiler.Edge c → U) :
      glueEdges (fun _ e => β e.val) (fun _ e => β e.val) = β := by
    funext e
    simp only [glueEdges, hcut01, hcut12, hcut20]
    split_ifs <;> first | rfl | omega
  have glue_on_cut (α : ∀ k, IntE k → U) (a : ∀ k, CutE k → U)
      (k : Fin 3) (e : CutE k) : glueEdges α a e.val = a k e := by
    have hk : k ≠ k + 1 := by fin_cases k <;> decide
    obtain ⟨hi, hj⟩ | ⟨hi, hj⟩ := (mem_inter_edgeCut_iff k (k + 1) hk e.val).mp e.property <;>
      rcases finThreeCases k with rfl | rfl | rfl <;>
      simp only [Fin.reduceAdd] at hi hj <;>
      simp [glueEdges, hcut01, hcut12, hcut20, hi, hj]
  -- Local validity predicates for parts `0, 1, 2`.
  let d0 : {i : Fin n // p i = 0} → U := fun _ => u₀
  let d1 : {i : Fin n // p i = 1} → U := fun _ => u₀
  let d2 : {i : Fin n // p i = 2} → U := fun _ => u₀
  let Valid₀ (x₀ : {i : Fin n // p i = 0} → U) (a₂ : CutE 2 → U) (a₀ : CutE 0 → U) : Prop :=
    ∃ α₀ : IntE 0 → U, ∀ v : Compiler.Vertex c, col v = 0 →
      N_net.Constraint v (mergeTripartition p x₀ d1 d2)
        (glueEdges (triple α₀ (fun _ => u₀) (fun _ => u₀)) (triple a₀ (fun _ => u₀) a₂))
  let Valid₁ (x₁ : {i : Fin n // p i = 1} → U) (a₀ : CutE 0 → U) (a₁ : CutE 1 → U) : Prop :=
    ∃ α₁ : IntE 1 → U, ∀ v : Compiler.Vertex c, col v = 1 →
      N_net.Constraint v (mergeTripartition p d0 x₁ d2)
        (glueEdges (triple (fun _ => u₀) α₁ (fun _ => u₀)) (triple a₀ a₁ (fun _ => u₀)))
  let Valid₂ (x₂ : {i : Fin n // p i = 2} → U) (a₂ : CutE 2 → U) (a₁ : CutE 1 → U) : Prop :=
    ∃ α₂ : IntE 2 → U, ∀ v : Compiler.Vertex c, col v = 2 →
      N_net.Constraint v (mergeTripartition p d0 d1 x₂)
        (glueEdges (triple (fun _ => u₀) (fun _ => u₀) α₂) (triple (fun _ => u₀) a₁ a₂))
  -- Exact equivalence: `(Valid₀ ∧ Valid₁ ∧ Valid₂)` iff `x ∈ S_acc` and `(a₂, a₀, a₁)` = trace.
  have valid_iff (x₀ : {i : Fin n // p i = 0} → U) (x₁ : {i : Fin n // p i = 1} → U)
      (x₂ : {i : Fin n // p i = 2} → U) (a₂ : CutE 2 → U) (a₀ : CutE 0 → U) (a₁ : CutE 1 → U) :
      (Valid₀ x₀ a₂ a₀ ∧ Valid₁ x₁ a₀ a₁ ∧ Valid₂ x₂ a₂ a₁) ↔
        mergeTripartition p x₀ x₁ x₂ ∈ S_acc ∧
          a₂ = (fun e => c.program.trace I (mergeTripartition p x₀ x₁ x₂) e.val.signal.val) ∧
          a₀ = (fun e => c.program.trace I (mergeTripartition p x₀ x₁ x₂) e.val.signal.val) ∧
          a₁ = (fun e => c.program.trace I (mergeTripartition p x₀ x₁ x₂) e.val.signal.val) := by
    set x := mergeTripartition p x₀ x₁ x₂
    constructor
    · rintro ⟨⟨α₀, h0⟩, ⟨α₁, h1⟩, ⟨α₂, h2⟩⟩
      let α := triple (A := fun k => IntE k → U) α₀ α₁ α₂
      let a := triple (A := fun k => CutE k → U) a₀ a₁ a₂
      have hsat : N_net.Satisfies x (glueEdges α a) := by
        intro v
        rcases finThreeCases (col v) with hv | hv | hv
        · refine N_net.constraint_congr v _ x _ _ (fun i hi => ?_) (fun e he => ?_) (h0 v hv)
          · simp only [x, mergeTripartition_apply_zero _ _ _ _ ((hcompat i v hi).trans hv)]
          · exact (glue_eq_at α a 0 hv he).symm
        · refine N_net.constraint_congr v _ x _ _ (fun i hi => ?_) (fun e he => ?_) (h1 v hv)
          · simp only [x, mergeTripartition_apply_one _ _ _ _ ((hcompat i v hi).trans hv)]
          · exact (glue_eq_at α a 1 hv he).symm
        · refine N_net.constraint_congr v _ x _ _ (fun i hi => ?_) (fun e he => ?_) (h2 v hv)
          · simp only [x, mergeTripartition_apply_two _ _ _ _ ((hcompat i v hi).trans hv)]
          · exact (glue_eq_at α a 2 hv he).symm
      obtain ⟨hacc, htr⟩ := Compiler.satisfies_iff.mp hsat
      refine ⟨hacc 0, ?_, ?_, ?_⟩ <;> funext e
      · exact (glue_on_cut α a 2 e).symm.trans (congrFun htr e.val)
      · exact (glue_on_cut α a 0 e).symm.trans (congrFun htr e.val)
      · exact (glue_on_cut α a 1 e).symm.trans (congrFun htr e.val)
    · rintro ⟨hx, rfl, rfl, rfl⟩
      set β : Compiler.Edge c → U := fun e => c.program.trace I x e.signal.val
      have hsat : N_net.Satisfies x β :=
        Compiler.satisfies_trace fun o => Subsingleton.elim (0 : Fin 1) o ▸ hx
      have hβ_eq := (glue_restrict β).symm
      refine ⟨⟨fun e => β e.val, fun v hv0 => ?_⟩,
              ⟨fun e => β e.val, fun v hv1 => ?_⟩,
              ⟨fun e => β e.val, fun v hv2 => ?_⟩⟩
      · refine N_net.constraint_congr v x _ β _ (fun i hi => ?_) (fun e he => ?_) (hsat v)
        · simp only [x, mergeTripartition_apply_zero _ _ _ _ ((hcompat i v hi).trans hv0)]
        · exact (congrFun hβ_eq e).trans
            (glue_eq_at (fun _ e => β e.val) (fun _ e => β e.val) 0 hv0 he)
      · refine N_net.constraint_congr v x _ β _ (fun i hi => ?_) (fun e he => ?_) (hsat v)
        · simp only [x, mergeTripartition_apply_one _ _ _ _ ((hcompat i v hi).trans hv1)]
        · exact (congrFun hβ_eq e).trans
            (glue_eq_at (fun _ e => β e.val) (fun _ e => β e.val) 1 hv1 he)
      · refine N_net.constraint_congr v x _ β _ (fun i hi => ?_) (fun e he => ?_) (hsat v)
        · simp only [x, mergeTripartition_apply_two _ _ _ _ ((hcompat i v hi).trans hv2)]
        · exact (congrFun hβ_eq e).trans
            (glue_eq_at (fun _ e => β e.val) (fun _ e => β e.val) 2 hv2 he)
  -- Embed each `CutE k → U` injectively into `Fin (Fintype.card U ^ B)`.
  set D := Fintype.card U ^ B
  have hcard_le (k : Fin 3) : Fintype.card (CutE k → U) ≤ Fintype.card (Fin D) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    have hsub : Fintype.card (CutE k) =
        (G.edgeCut {v | col v = k} ∩ G.edgeCut {v | col v = k + 1}).ncard := by
      rw [← Nat.card_eq_fintype_card]; exact Nat.card_coe_set_eq _
    rw [hsub]
    exact Nat.pow_le_pow_right Fintype.card_pos (hcut k)
  obtain ⟨emb₀⟩ := Function.Embedding.nonempty_of_card_le (hcard_le 0)
  obtain ⟨emb₁⟩ := Function.Embedding.nonempty_of_card_le (hcard_le 1)
  obtain ⟨emb₂⟩ := Function.Embedding.nonempty_of_card_le (hcard_le 2)
  let M₀ : Matrix (Fin D × Fin D) ({i : Fin n // p i = 0} → U) K :=
    Matrix.of fun ij x₀ =>
      if ∃ a₂ a₀, emb₂ a₂ = ij.1 ∧ emb₀ a₀ = ij.2 ∧ Valid₀ x₀ a₂ a₀ then 1 else 0
  let M₁ : Matrix (Fin D × Fin D) ({i : Fin n // p i = 1} → U) K :=
    Matrix.of fun jk x₁ =>
      if ∃ a₀ a₁, emb₀ a₀ = jk.1 ∧ emb₁ a₁ = jk.2 ∧ Valid₁ x₁ a₀ a₁ then 1 else 0
  let M₂ : Matrix ({i : Fin n // p i = 2} → U) (Fin D × Fin D) K :=
    Matrix.of fun x₂ ik =>
      if ∃ a₂ a₁, emb₂ a₂ = ik.1 ∧ emb₁ a₁ = ik.2 ∧ Valid₂ x₂ a₂ a₁ then 1 else 0
  -- Collapse the triple sum over `(Fin D × Fin D)³` via the matrix-multiplication Kronecker delta.
  have hcollapse (F G H : Fin D × Fin D → K) :
      ∑ u, ∑ v, ∑ w, F u * G v * H w * (if u.1 = w.1 ∧ u.2 = v.1 ∧ v.2 = w.2 then 1 else 0) =
        ∑ i₂, ∑ i₀, ∑ i₁, F (i₂, i₀) * G (i₀, i₁) * H (i₂, i₁) := by
    simp only [Fintype.sum_prod_type, ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  refine ⟨M₀, M₁, M₂, ?_⟩
  funext x₀ x₁ x₂
  simp only [Tensor.restrict, Tensor.mm_apply, partitionThreeTensor]
  refine (hcollapse _ _ _).trans ?_
  simp only [M₀, M₁, M₂, Matrix.of_apply]
  set x := mergeTripartition p x₀ x₁ x₂
  let tr₂ : CutE 2 → U := fun e => c.program.trace I x e.val.signal.val
  let tr₀ : CutE 0 → U := fun e => c.program.trace I x e.val.signal.val
  let tr₁ : CutE 1 → U := fun e => c.program.trace I x e.val.signal.val
  -- Only `(emb₂ tr₂, emb₀ tr₀, emb₁ tr₁)` can survive in the triple sum.
  have hall_iff (i₂ i₀ i₁ : Fin D) :
      ((∃ a₂ a₀, emb₂ a₂ = i₂ ∧ emb₀ a₀ = i₀ ∧ Valid₀ x₀ a₂ a₀) ∧
        (∃ a₀ a₁, emb₀ a₀ = i₀ ∧ emb₁ a₁ = i₁ ∧ Valid₁ x₁ a₀ a₁) ∧
        (∃ a₂ a₁, emb₂ a₂ = i₂ ∧ emb₁ a₁ = i₁ ∧ Valid₂ x₂ a₂ a₁)) ↔
        x ∈ S_acc ∧ i₂ = emb₂ tr₂ ∧ i₀ = emb₀ tr₀ ∧ i₁ = emb₁ tr₁ := by
    constructor
    · rintro ⟨⟨a₂, a₀, rfl, rfl, hv0⟩, ⟨a₀', a₁, he0, rfl, hv1⟩, ⟨a₂', a₁', he2, he1, hv2⟩⟩
      obtain rfl := emb₀.injective he0
      obtain rfl := emb₂.injective he2
      obtain rfl := emb₁.injective he1
      obtain ⟨hx, rfl, rfl, rfl⟩ := (valid_iff x₀ x₁ x₂ _ _ _).mp ⟨hv0, hv1, hv2⟩
      exact ⟨hx, rfl, rfl, rfl⟩
    · rintro ⟨hx, rfl, rfl, rfl⟩
      have hv := (valid_iff x₀ x₁ x₂ tr₂ tr₀ tr₁).mpr ⟨hx, rfl, rfl, rfl⟩
      exact ⟨⟨_, _, rfl, rfl, hv.1⟩, ⟨_, _, rfl, rfl, hv.2.1⟩, ⟨_, _, rfl, rfl, hv.2.2⟩⟩
  simp only [ite_zero_mul_ite_zero, mul_one, and_assoc, hall_iff]
  by_cases hx : x ∈ S_acc
  · simp only [hx, true_and, ↓reduceIte]
    rw [Fintype.sum_eq_single (emb₂ tr₂) (fun i₂ hi₂ =>
      Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => by simp [hi₂])]
    rw [Fintype.sum_eq_single (emb₀ tr₀) (fun i₀ hi₀ =>
      Finset.sum_eq_zero fun _ _ => by simp [hi₀])]
    rw [Fintype.sum_eq_single (emb₁ tr₁) (fun i₁ hi₁ => by simp [hi₁])]
    simp
  · simp [hx]

end Splicing

/-! ### Degree-`≤ 1` input-vertex rebalancing and unread-input rank shortcut -/

section Rebalancing

/-- Recoloring a single vertex `v₀` of degree at most `1` increases any pairwise cut
`G.edgeCut {v | col v = k} ∩ G.edgeCut {v | col v = k + 1}` by at most `1`. -/
private theorem ncard_crossCut_update_le {V E : Type*} [Finite E] [DecidableEq V]
    (G : Multigraph V E) (col : V → Fin 3) {v₀ : V} (hdeg1 : (G.incidenceSet v₀).ncard ≤ 1)
    (c_new k : Fin 3) :
    (G.edgeCut {v | Function.update col v₀ c_new v = k} ∩
      G.edgeCut {v | Function.update col v₀ c_new v = k + 1}).ncard ≤
      (G.edgeCut {v | col v = k} ∩ G.edgeCut {v | col v = k + 1}).ncard + 1 := by
  set S' := G.edgeCut {v | Function.update col v₀ c_new v = k} ∩
    G.edgeCut {v | Function.update col v₀ c_new v = k + 1}
  set S := G.edgeCut {v | col v = k} ∩ G.edgeCut {v | col v = k + 1}
  have hsub : S' ⊆ S ∪ G.incidenceSet v₀ := by
    intro e he
    by_cases hinc : e ∈ G.incidenceSet v₀
    · exact Or.inr hinc
    · left
      rw [Multigraph.mem_incidenceSet, not_or] at hinc
      have hs : Function.update col v₀ c_new (G.src e) = col (G.src e) :=
        Function.update_of_ne hinc.1 _ _
      have ht : Function.update col v₀ c_new (G.tgt e) = col (G.tgt e) :=
        Function.update_of_ne hinc.2 _ _
      simp only [S', S, mem_inter_iff, Multigraph.mem_edgeCut, mem_ofPred_eq] at he ⊢
      rwa [hs, ht] at he
  exact ((ncard_le_ncard hsub (toFinite _)).trans (ncard_union_le _ _)).trans
    (Nat.add_le_add_left hdeg1 _)

/-- **Greedy single-input rebalancing.** Any `(p, col)` compatible with `Compiler.site c` can be
adjusted in at most `∑ k, (n / 3 - #{i | p i = k})` single-input moves to satisfy
`BalancedTripartition n p'`, increasing each pairwise edge cut by at most that deficit. -/
private theorem exists_rebalanced_coloring {σ : Signature} {n : ℕ} (c : Circuit σ n 1) :
    ∀ (fuel : ℕ) (p : Fin n → Fin 3) (col : Compiler.Vertex c → Fin 3),
      (∀ i v, Compiler.site c i = some v → p i = col v) →
      (∑ k : Fin 3, (n / 3 - {i : Fin n | p i = k}.ncard)) ≤ fuel →
      ∃ (p' : Fin n → Fin 3) (col' : Compiler.Vertex c → Fin 3),
        BalancedTripartition n p' ∧
        (∀ i v, Compiler.site c i = some v → p' i = col' v) ∧
        (∀ k : Fin 3,
          ((Compiler.graph c).edgeCut {v | col' v = k} ∩
            (Compiler.graph c).edgeCut {v | col' v = k + 1}).ncard ≤
            ((Compiler.graph c).edgeCut {v | col v = k} ∩
              (Compiler.graph c).edgeCut {v | col v = k + 1}).ncard + fuel)
  | 0, p, col, hcompat, hfuel => by
      refine ⟨p, col, fun k => ?_, hcompat, fun k => by simp⟩
      rw [Fin.sum_univ_three] at hfuel
      fin_cases k <;> dsimp only [Fin.reduceFinMk] <;> omega
  | fuel + 1, p, col, hcompat, hfuel => by
      classical
      by_cases hbal : BalancedTripartition n p
      · exact ⟨p, col, hbal, hcompat, fun k => Nat.le_add_right _ _⟩
      · unfold BalancedTripartition at hbal
        push Not at hbal
        obtain ⟨k_lo, hk_lo⟩ := hbal
        -- Since the three parts sum to `n ≥ 3 * (n / 3)`, some `k_hi` has size `≥ n / 3 + 1`.
        have hex_hi : ∃ k_hi : Fin 3, n / 3 + 1 ≤ {i : Fin n | p i = k_hi}.ncard := by
          by_contra! hall_le
          have hsum := ncard_parts_sum p
          have h0 := hall_le 0; have h1 := hall_le 1; have h2 := hall_le 2
          have hmul : 3 * (n / 3) ≤ n := Nat.mul_div_le n 3
          fin_cases k_lo <;> dsimp only [Fin.reduceFinMk] at hk_lo <;> omega
        obtain ⟨k_hi, hk_hi⟩ := hex_hi
        have hlo_ne_hi : k_lo ≠ k_hi := fun h => by subst h; omega
        obtain ⟨i₀, hi₀⟩ :=
          (ncard_pos (toFinite _)).mp (by omega : 0 < {i : Fin n | p i = k_hi}.ncard)
        rw [mem_ofPred_eq] at hi₀
        let p₁ := Function.update p i₀ k_lo
        let col₁ : Compiler.Vertex c → Fin 3 :=
          match Compiler.site c i₀ with
          | none => col
          | some v₀ => Function.update col v₀ k_lo
        have hcompat₁ : ∀ i v, Compiler.site c i = some v → p₁ i = col₁ v := by
          intro i v hsite
          by_cases hii₀ : i = i₀
          · subst hii₀
            simp only [p₁, Function.update_self, col₁, hsite, Function.update_self]
          · simp only [p₁, Function.update_of_ne hii₀]
            dsimp [col₁]
            rcases hs₀ : Compiler.site c i₀ with _ | v₀
            · exact hcompat i v hsite
            · dsimp only
              have hv_ne : v ≠ v₀ := fun hv_eq => by
                subst hv_eq
                obtain ⟨_, rfl⟩ := Compiler.site_eq_some hsite
                obtain ⟨_, heq_sig⟩ := Compiler.site_eq_some hs₀
                exact hii₀
                  (Wire.input.inj (congrArg Subtype.val (Compiler.Vertex.signal.inj heq_sig)))
              rw [Function.update_of_ne hv_ne]
              exact hcompat i v hsite
        -- Compute updated part sizes to show the deficit drops by `1`.
        have hcard_lo : {i : Fin n | p₁ i = k_lo}.ncard = {i : Fin n | p i = k_lo}.ncard + 1 := by
          have hset : {i : Fin n | p₁ i = k_lo} = insert i₀ {i : Fin n | p i = k_lo} := by
            ext i
            simp only [p₁, mem_ofPred_eq, mem_insert_iff]
            by_cases hi : i = i₀
            · subst hi; simp [hi₀, hlo_ne_hi.symm]
            · simp [hi]
          rw [hset, ncard_insert_of_notMem (by simp [hi₀, hlo_ne_hi.symm]) (toFinite _)]
        have hcard_hi : {i : Fin n | p₁ i = k_hi}.ncard + 1 = {i : Fin n | p i = k_hi}.ncard := by
          have hset : {i : Fin n | p i = k_hi} = insert i₀ {i : Fin n | p₁ i = k_hi} := by
            ext i
            simp only [p₁, mem_ofPred_eq, mem_insert_iff]
            by_cases hi : i = i₀
            · subst hi; simp [hi₀]
            · simp [hi]
          conv_rhs => rw [hset]
          rw [ncard_insert_of_notMem (by simp [p₁, hlo_ne_hi]) (toFinite _)]
        have hcard_other (k : Fin 3) (hkl : k ≠ k_lo) (hkh : k ≠ k_hi) :
            {i : Fin n | p₁ i = k}.ncard = {i : Fin n | p i = k}.ncard := by
          congr 1; ext i
          simp only [p₁, mem_ofPred_eq]
          by_cases hi : i = i₀
          · subst hi; simp [hi₀, hkl.symm, hkh.symm]
          · simp [Function.update_of_ne hi]
        have hdef_step :
            (∑ k : Fin 3, (n / 3 - {i : Fin n | p₁ i = k}.ncard)) + 1 =
              ∑ k : Fin 3, (n / 3 - {i : Fin n | p i = k}.ncard) := by
          rw [Fin.sum_univ_three, Fin.sum_univ_three]
          rcases finThreeCases k_lo with rfl | rfl | rfl <;>
            rcases finThreeCases k_hi with rfl | rfl | rfl <;>
            first
            | exact absurd rfl hlo_ne_hi
            | have := hcard_other 0 (by decide) (by decide); omega
            | have := hcard_other 1 (by decide) (by decide); omega
            | have := hcard_other 2 (by decide) (by decide); omega
        have hcut_step (k : Fin 3) :
            ((Compiler.graph c).edgeCut {v | col₁ v = k} ∩
              (Compiler.graph c).edgeCut {v | col₁ v = k + 1}).ncard ≤
              ((Compiler.graph c).edgeCut {v | col v = k} ∩
                (Compiler.graph c).edgeCut {v | col v = k + 1}).ncard + 1 := by
          dsimp [col₁]
          rcases hs₀ : Compiler.site c i₀ with _ | v₀
          · exact Nat.le_add_right _ _
          · exact ncard_crossCut_update_le (Compiler.graph c) col
              (Compiler.ncard_incidenceSet_site_le_one hs₀) k_lo k
        obtain ⟨p', col', hbal', hcompat', hcut'⟩ :=
          exists_rebalanced_coloring c fuel p₁ col₁ hcompat₁ (by omega)
        refine ⟨p', col', hbal', hcompat', fun k => ?_⟩
        exact (hcut' k).trans (by have := hcut_step k; omega)

/-- **Low-read-count rank shortcut.** If a circuit `c : Circuit σ n 1` reads only `m` of its `n`
inputs, there exists a `BalancedTripartition n p` under which
`partitionThreeTensor K p {x | c.eval I x 0 ∈ Acc 0}` has CP-rank at most
`|U| ^ (2 * (m / 3 + 1))`. -/
private theorem exists_balanced_rank_of_read_ncard (K : Type*) [CommSemiring K]
    {σ : Signature} {n : ℕ} {U : Type*} [Fintype U] [Nonempty U]
    (c : Circuit σ n 1) (I : Interpretation σ U) (Acc : Fin 1 → Set U) :
    ∃ p : Fin n → Fin 3, BalancedTripartition n p ∧
      Tensor.Rank (Fintype.card U ^ (2 * ((Compiler.network c I Acc).read.ncard / 3 + 1)))
        (partitionThreeTensor K p {x | c.eval I x 0 ∈ Acc 0}) := by
  classical
  set R_set := (Compiler.network c I Acc).read
  set m := R_set.ncard
  -- Order `Fin n` with `R_set` in positions `0 .. m - 1` and `R_setᶜ` in positions `m .. n - 1`,
  -- then assign `idx i % 3`: each residue appears `≥ n / 3` times globally (`BalancedTripartition`)
  -- and `≤ m / 3 + 1` times on `R_set`.
  let R_fin := R_set.toFinset
  have hcard_R : R_fin.card = m := (Set.ncard_eq_toFinset_card' R_set).symm
  -- `eqvIdx` lists `R_set` first, then its complement.
  let eqvIdx : Fin n ≃ Fin n :=
    ((Equiv.sumCompl (· ∈ R_fin)).symm.trans
      ((R_fin.equivFin.sumCongr (Fintype.equivFin _)).trans finSumFinEquiv)).trans
      (finCongr (by
        rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
        have := R_fin.card_le_univ; simp only [Fintype.card_fin] at this; omega))
  have hidx_lt {i : Fin n} (hi : i ∈ R_fin) : (eqvIdx i).val < m := by
    simp only [eqvIdx, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hi,
      Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left, finCongr_apply,
      Fin.val_cast, Fin.val_castAdd]
    exact hcard_R ▸ Fin.isLt _
  let p (i : Fin n) : Fin 3 := ⟨(eqvIdx i).val % 3, Nat.mod_lt _ (by norm_num)⟩
  -- 1. `p` is a `BalancedTripartition`: each mod-`3` class in `Fin n` has size `≥ n / 3`.
  have hbal : BalancedTripartition n p := by
    intro c
    have hbij : {i : Fin n | p i = c}.ncard = {j : Fin n | j.val % 3 = c.val}.ncard := by
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      refine Nat.card_congr ⟨fun x => ⟨eqvIdx x.val, by
          have hx := x.property; rw [mem_ofPred_eq] at hx ⊢
          exact congrArg Fin.val hx⟩,
        fun y => ⟨eqvIdx.symm y.val, by
          have hy := y.property; rw [mem_ofPred_eq] at hy ⊢
          apply Fin.ext
          change (eqvIdx (eqvIdx.symm y.val)).val % 3 = c.val
          rw [Equiv.apply_symm_apply]; exact hy⟩,
        fun x => Subtype.ext (eqvIdx.symm_apply_apply x.val),
        fun y => Subtype.ext (eqvIdx.apply_symm_apply y.val)⟩
    rw [hbij]
    have hinj_mod : Set.InjOn (fun t : Fin (n / 3) =>
        (⟨3 * t.val + c.val, by have := t.isLt; have := c.isLt; omega⟩ : Fin n)) univ := by
      intro t₁ _ t₂ _ heq
      have hv : 3 * t₁.val + c.val = 3 * t₂.val + c.val := Fin.ext_iff.mp heq
      exact Fin.ext (by omega)
    have hmaps : Set.MapsTo (fun t : Fin (n / 3) =>
        (⟨3 * t.val + c.val, by have := t.isLt; have := c.isLt; omega⟩ : Fin n))
        univ {j : Fin n | j.val % 3 = c.val} := by
      intro t _
      rw [mem_ofPred_eq]
      dsimp
      have hc_lt := c.isLt
      omega
    have hle := ncard_le_ncard_of_injOn _ hmaps hinj_mod (toFinite _)
    rwa [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  -- 2. On `R_set`, each mod-`3` class has size `≤ m / 3 + 1`.
  have hread_part_le (c : Fin 3) :
      Fintype.card {i : Fin n // p i = c ∧ i ∈ R_set} ≤ m / 3 + 1 := by
    let toQuot (x : {i : Fin n // p i = c ∧ i ∈ R_set}) : Fin (m / 3 + 1) :=
      ⟨(eqvIdx x.val).val / 3, by
        have := hidx_lt (Set.mem_toFinset.mpr x.property.2); omega⟩
    have hinj_q : Function.Injective toQuot := by
      intro x₁ x₂ hq
      have hdiv : (eqvIdx x₁.val).val / 3 = (eqvIdx x₂.val).val / 3 := Fin.ext_iff.mp hq
      have hmod1 : (eqvIdx x₁.val).val % 3 = c.val := congrArg Fin.val x₁.property.1
      have hmod2 : (eqvIdx x₂.val).val % 3 = c.val := congrArg Fin.val x₂.property.1
      have hval_eq : (eqvIdx x₁.val).val = (eqvIdx x₂.val).val := by omega
      exact Subtype.ext (eqvIdx.injective (Fin.ext hval_eq))
    simpa using Fintype.card_le_of_injective toQuot hinj_q
  -- 3. `partitionThreeTensor K p S` factors through `{i // p i = 0 ∧ i ∈ R_set} → U` and
  -- `{i // p i = 1 ∧ i ∈ R_set} → U` via `Compiler.accepted_network` + `Network.dependsOn_read`!
  refine ⟨p, hbal, ?_⟩
  obtain ⟨u_def⟩ := ‹Nonempty U›
  let Y₀ := {i : Fin n // p i = 0 ∧ i ∈ R_set} → U
  let Y₁ := {i : Fin n // p i = 1 ∧ i ∈ R_set} → U
  let π₀ (x₀ : {i : Fin n // p i = 0} → U) : Y₀ := fun j => x₀ ⟨j.val, j.property.1⟩
  let π₁ (x₁ : {i : Fin n // p i = 1} → U) : Y₁ := fun j => x₁ ⟨j.val, j.property.1⟩
  let ext₀ (y₀ : Y₀) : {i : Fin n // p i = 0} → U :=
    fun i => if hi : i.val ∈ R_set then y₀ ⟨i.val, i.property, hi⟩ else u_def
  let ext₁ (y₁ : Y₁) : {i : Fin n // p i = 1} → U :=
    fun i => if hi : i.val ∈ R_set then y₁ ⟨i.val, i.property, hi⟩ else u_def
  let g (y₀ : Y₀) (y₁ : Y₁) (x₂ : {i : Fin n // p i = 2} → U) : K :=
    partitionThreeTensor K p {x | c.eval I x 0 ∈ Acc 0} (ext₀ y₀) (ext₁ y₁) x₂
  have hten_eq : partitionThreeTensor K p {x | c.eval I x 0 ∈ Acc 0} =
      fun x₀ x₁ x₂ => g (π₀ x₀) (π₁ x₁) x₂ := by
    funext x₀ x₁ x₂
    dsimp [g, partitionThreeTensor]
    have hmem_iff : mergeTripartition p x₀ x₁ x₂ ∈ {x | c.eval I x 0 ∈ Acc 0} ↔
        mergeTripartition p (ext₀ (π₀ x₀)) (ext₁ (π₁ x₁)) x₂ ∈ {x | c.eval I x 0 ∈ Acc 0} := by
      have hacc_eq : {x : Fin n → U | c.eval I x 0 ∈ Acc 0} =
          (Compiler.network c I Acc).accepted := by
        rw [Compiler.accepted_network]
        ext x; simp [Fin.forall_fin_one]
      rw [hacc_eq]
      have hdep := (Compiler.network c I Acc).dependsOn_read
        (x := mergeTripartition p x₀ x₁ x₂)
        (y := mergeTripartition p (ext₀ (π₀ x₀)) (ext₁ (π₁ x₁)) x₂)
      refine Eq.to_iff (hdep fun i (hi : i ∈ R_set) => ?_)
      rcases hp : p i with ⟨_ | _ | _ | _, hlt⟩
      · have hp0 : p i = 0 := hp
        rw [mergeTripartition_apply_zero _ _ _ _ hp0, mergeTripartition_apply_zero _ _ _ _ hp0]
        simp [ext₀, π₀, hi]
      · have hp1 : p i = 1 := hp
        rw [mergeTripartition_apply_one _ _ _ _ hp1, mergeTripartition_apply_one _ _ _ _ hp1]
        simp [ext₁, π₁, hi]
      · have hp2 : p i = 2 := hp
        rw [mergeTripartition_apply_two _ _ _ _ hp2, mergeTripartition_apply_two _ _ _ _ hp2]
      · omega
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hmem_iff.mp h1) h2
    · exact absurd (hmem_iff.mpr h2) h1
    · rfl
  rw [hten_eq]
  refine (rank_of_factors_left_mid π₀ π₁ g).mono ?_
  calc Fintype.card Y₀ * Fintype.card Y₁
      = Fintype.card U ^ Fintype.card {i : Fin n // p i = 0 ∧ i ∈ R_set} *
          Fintype.card U ^ Fintype.card {i : Fin n // p i = 1 ∧ i ∈ R_set} := by
        simp [Y₀, Y₁]
    _ = Fintype.card U ^
          (Fintype.card {i : Fin n // p i = 0 ∧ i ∈ R_set} +
            Fintype.card {i : Fin n // p i = 1 ∧ i ∈ R_set}) := (pow_add _ _ _).symm
    _ ≤ Fintype.card U ^ (2 * (m / 3 + 1)) :=
        Nat.pow_le_pow_right Fintype.card_pos
          (by have := hread_part_le 0; have := hread_part_le 1; omega)

end Rebalancing

/-! ### Fan-in-`2` circuit lower bounds (`innerSize_gt_of_threeTensorHard` & `3.041n`) -/

/-- **Parametric fan-in-`2` circuit lower bound from `ThreeTensorHard`.** Over any
characteristic-zero field `K`, for every `ε > 0` there is `δ > 0` and `N₀ : ℕ` (depending only on
`K`, `|U|`, and `ε`) such that for all `n ≥ N₀`, every fan-in-`2` circuit deciding a
`ThreeTensorHard` set at CP-rank `⌊|U| ^ ((2 / 3 - δ) * n)⌋₊` has strictly more than
`(1 + 1 / (omega K * threeWayCapCoefficient) - ε) * n` inner gates.

Each of the three pairwise edge cuts has size `B ≈ (2 / 3) · threeWayCapCoefficient · (s - n)`, so
`Tensor.mm (|U| ^ B) (|U| ^ B) (|U| ^ B)` has rank `|U| ^ ((2 / 3) · omega K ·
threeWayCapCoefficient · (s - n) + o(n))`. Requiring this exponent to reach `(2 / 3) n` cancels the
factor of `2 / 3` and gives `s ≥ (1 + 1 / (omega K * threeWayCapCoefficient) - o(1)) n`. -/
theorem innerSize_gt_of_threeTensorHard (K : Type*) [Field K] [CharZero K]
    {U : Type*} [Fintype U] (hU : 2 ≤ Fintype.card U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ {σ : Signature} {n : ℕ}, N₀ ≤ n →
      ∀ {S : Set (Fin n → U)},
        ThreeTensorHard K ⌊(Fintype.card U : ℝ) ^ ((2 / 3 - δ) * (n : ℝ))⌋₊ S →
        ∀ (c : Circuit σ n 1) (I : Interpretation σ U) (Acc : Fin 1 → Set U),
          c.FanInAtMost 2 → (∀ x, c.eval I x 0 ∈ Acc 0 ↔ x ∈ S) →
          (1 + 1 / (omega K * threeWayCapCoefficient) - ε) * (n : ℝ) < (c.innerSize : ℝ) := by
  have : Nonempty U := Fintype.card_pos_iff.mp (by omega)
  set q : ℕ := Fintype.card U
  have hq_gt1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hq_pos : (0 : ℝ) < (q : ℝ) := by positivity
  have hlog_pos : 0 < Real.log (q : ℝ) := Real.log_pos hq_gt1
  have hω_ge2 : (2 : ℝ) ≤ omega K := two_le_omega K
  have hω_pos : 0 < omega K := by linarith only [hω_ge2]
  have hcap_pos : 0 < threeWayCapCoefficient := threeWayCapCoefficient_pos
  have hcap_21773 : threeWayCapCoefficient ≤ 21773 / 100000 := threeWayCapCoefficient_le_21773
  have hcap_le1 : 2 / 3 * threeWayCapCoefficient ≤ 1 := by linarith only [hcap_21773]
  set L_coef : ℝ := 1 + 1 / (omega K * threeWayCapCoefficient)
  have hL_gt1 : 1 < L_coef := by
    dsimp [L_coef]
    have hpos : 0 < 1 / (omega K * threeWayCapCoefficient) := by positivity
    linarith only [hpos]
  set ε' : ℝ := min (ε / 2) (1 / 2)
  have hε'_pos : 0 < ε' := lt_min (by positivity) (by norm_num)
  have hε'_lt_ε : ε' < ε := (min_le_left _ _).trans_lt (by linarith)
  set gap : ℝ := 2 / 3 * omega K * threeWayCapCoefficient * ε'
  have hgap_pos : 0 < gap := by positivity
  set δ : ℝ := min (gap / (4 * (7 * omega K + 2))) (1 / 12)
  have hδ_pos : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ_le_12 : δ ≤ 1 / 12 := min_le_right _ _
  have hδ_mul_le : 4 * (7 * omega K + 2) * δ ≤ gap := by
    have hle : δ ≤ gap / (4 * (7 * omega K + 2)) := min_le_left _ _
    have hden : 0 < 4 * (7 * omega K + 2) := by positivity
    rw [mul_comm]
    exact (le_div_iff₀ hden).mp hle
  set τ : ℝ := omega K + δ
  have hτ_pos : 0 < τ := by positivity
  obtain ⟨c_mm, hc_mm_pos, h_mm⟩ := exists_rank_mm_le_rpow K (τ := τ) (by dsimp [τ]; linarith)
  set ξ : ℝ := δ / (32 * (L_coef + 1))
  have hξ_pos : 0 < ξ := by positivity
  obtain ⟨C₀, hcut3⟩ := exists_balanced_threeWayCut hξ_pos
  set K_const : ℝ := τ * (4 * (C₀ : ℝ) + 1) + |Real.log c_mm| / Real.log (q : ℝ) + 2
  set N₀ : ℕ := max ⌈max 2 K_const / δ⌉₊ 12
  refine ⟨δ, hδ_pos, N₀, fun {σ n} hn {S} hHard c I Acc hfan hdec => ?_⟩
  have hn12 : 12 ≤ n := (le_max_right _ _).trans hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_K : max 2 K_const ≤ δ * (n : ℝ) := by
    have h1 : max 2 K_const / δ ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_left _ _).trans hn))
    have hm1 := (div_le_iff₀ hδ_pos).mp h1
    linarith only [hm1]
  have hS_eq : {x : Fin n → U | c.eval I x 0 ∈ Acc 0} = S := by
    ext x; exact hdec x
  -- Suffices to refute `(c.innerSize : ℝ) ≤ (L_coef - ε') * n`.
  suffices hgt' : (L_coef - ε') * (n : ℝ) < (c.innerSize : ℝ) by
    have hlt_coef : L_coef - ε < L_coef - ε' := by linarith only [hε'_lt_ε]
    exact (mul_lt_mul_of_pos_right hlt_coef hn_pos).trans hgt'
  by_contra! hs_le
  set r_hard := ⌊(q : ℝ) ^ ((2 / 3 - δ) * (n : ℝ))⌋₊
  set m := (Compiler.network c I Acc).read.ncard
  -- Case split on whether `m` is below `(1 - 3 * δ) * n` (low-read shortcut) or above.
  by_cases hm_low : (m : ℝ) < (1 - 3 * δ) * (n : ℝ)
  · obtain ⟨p, hbal, hrk⟩ := exists_balanced_rank_of_read_ncard K c I Acc
    rw [hS_eq] at hrk
    have hexp_le : (2 * (m / 3 + 1) : ℕ) ≤ (2 / 3 - δ) * (n : ℝ) := by
      have hdiv3 : ((m / 3 : ℕ) : ℝ) ≤ (m : ℝ) / 3 := by exact_mod_cast Nat.cast_div_le
      have hn_large : 2 ≤ δ * (n : ℝ) := (le_max_left 2 K_const).trans hn_K
      push_cast
      linarith only [hm_low, hdiv3, hn_large]
    have hrk_le : q ^ (2 * (m / 3 + 1)) ≤ r_hard := by
      refine Nat.le_floor ?_
      rw [Nat.cast_pow, ← Real.rpow_natCast (q : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hq_gt1.le hexp_le
    exact hHard p hbal (hrk.mono hrk_le)
  · -- High-read case: `(1 - 3 * δ) * n ≤ m`.
    push Not at hm_low
    set G := Compiler.graph c
    have hloop : G.Loopless := Compiler.loopless
    have hconn : G.toSimpleGraph.Connected := Compiler.connected c
    have hdeg : G.MaxDegreeLE 3 := Compiler.maxDegreeLE (by norm_num : 2 ≤ 2) hfan
    have hcyc_read : G.cycleRank + m ≤ c.innerSize + 1 := by
      have h := Compiler.cycleRank_add_ncard_read_le I Acc hfan hconn
      simpa [G, m] using h
    have hV_le : Nat.card (Compiler.Vertex c) ≤ 4 * c.innerSize + 3 := by
      have h := Compiler.card_vertex_le (c := c) hfan
      omega
    -- Apply `exists_balanced_threeWayCut` to `A_in := {v | ∃ i, site c i = some v}`.
    let A_in : Set (Compiler.Vertex c) := {v | ∃ i : Fin n, Compiler.site c i = some v}
    have hA_in_card : A_in.ncard = m := by
      dsimp only [m]
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      have hread_eq : (Compiler.network c I Acc).read = {i : Fin n | Compiler.Reach c (.input i)} :=
        Compiler.read_network I Acc
      rw [hread_eq]
      refine Nat.card_congr
        { toFun := fun v => ⟨v.property.choose, (Compiler.site_eq_some v.property.choose_spec).1⟩
          invFun := fun i =>
            ⟨.signal ⟨.input i.val, i.property⟩, i.val, Compiler.site_of_reach i.property⟩
          left_inv := fun v => by
            obtain ⟨_, hv_eq⟩ := Compiler.site_eq_some v.property.choose_spec
            ext; exact hv_eq.symm
          right_inv := fun i => by
            ext1
            have hs := ((⟨.signal ⟨.input i.val, i.property⟩, i.val,
              Compiler.site_of_reach i.property⟩ : A_in).property).choose_spec
            obtain ⟨_, heq⟩ := Compiler.site_eq_some hs
            exact (Wire.input.inj (congrArg Subtype.val (Compiler.Vertex.signal.inj heq))).symm }
    obtain ⟨col₀, hbal₀, hcut₀⟩ := hcut3 G hloop hconn hdeg A_in
    let p₀ (i : Fin n) : Fin 3 :=
      match Compiler.site c i with
      | some v => col₀ v
      | none => 0
    have hcompat₀ : ∀ i v, Compiler.site c i = some v → p₀ i = col₀ v := by
      intro i v hs; simp [p₀, hs]
    -- Inject `A_in ∩ {v | col₀ v = k}` into `{i : Fin n | p₀ i = k}` via `invSite`.
    classical
    let invSite (v : Compiler.Vertex c) : Fin n :=
      if hv : v ∈ A_in then hv.choose else ⟨0, by omega⟩
    have hinv_spec {v : Compiler.Vertex c} (hv : v ∈ A_in) :
        Compiler.site c (invSite v) = some v := by
      simp only [invSite, hv, ↓reduceDIte]
      exact hv.choose_spec
    have hpart_ge (k : Fin 3) :
        ((A_in ∩ {v | col₀ v = k}).ncard : ℝ) ≤ ({i : Fin n | p₀ i = k}.ncard : ℝ) := by
      refine Nat.cast_le.mpr (ncard_le_ncard_of_injOn invSite ?_ ?_ (toFinite _))
      · intro v hv
        rw [mem_ofPred_eq]
        exact (hcompat₀ (invSite v) v (hinv_spec hv.1)).trans hv.2
      · intro v₁ hv₁ v₂ hv₂ heq
        have hs₁ := hinv_spec hv₁.1
        rw [heq, hinv_spec hv₂.1] at hs₁
        exact Option.some.inj hs₁.symm
    -- Bound the rebalancing deficit `fuel := ∑ k, (n / 3 - #{i | p₀ i = k})`.
    set V_card : ℝ := (Nat.card (Compiler.Vertex c) : ℝ)
    have hV_nonneg : 0 ≤ V_card := Nat.cast_nonneg _
    set fuel : ℕ := ∑ k : Fin 3, (n / 3 - {i : Fin n | p₀ i = k}.ncard)
    have hdiv3_n : ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := by exact_mod_cast Nat.cast_div_le
    have hdef_part (k : Fin 3) :
        ((n / 3 - {i : Fin n | p₀ i = k}.ncard : ℕ) : ℝ) ≤
          δ * (n : ℝ) + ξ * V_card + (C₀ : ℝ) := by
      have hb_abs := neg_le_of_abs_le (hbal₀ k)
      rw [hA_in_card] at hb_abs
      have hp_lo := hpart_ge k
      by_cases hab : {i : Fin n | p₀ i = k}.ncard ≤ n / 3
      · rw [Nat.cast_sub hab]
        linarith only [hb_abs, hp_lo, hm_low, hdiv3_n]
      · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero]
        positivity
    have hfuel_le : (fuel : ℝ) ≤ 3 * δ * (n : ℝ) + 3 * ξ * V_card + 3 * (C₀ : ℝ) := by
      simp only [fuel, Fin.sum_univ_three, Nat.cast_add]
      linarith only [hdef_part 0, hdef_part 1, hdef_part 2]
    -- Rebalance `p₀` to an exact `BalancedTripartition n p'` and splice into `Tensor.mm`.
    obtain ⟨p', col', hbal', hcompat', hcut'⟩ :=
      exists_rebalanced_coloring c fuel p₀ col₀ hcompat₀ le_rfl
    let c_sz (k : Fin 3) : ℕ :=
      (G.edgeCut {v | col' v = k} ∩ G.edgeCut {v | col' v = k + 1}).ncard
    set B : ℕ := max (c_sz 0) (max (c_sz 1) (c_sz 2))
    have hc_le_B (k : Fin 3) : c_sz k ≤ B := by
      fin_cases k
      · exact le_max_left _ _
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
    have hrestr : IsRestriction (partitionThreeTensor K p' S)
        (Tensor.mm (q ^ B) (q ^ B) (q ^ B)) := by
      rw [← hS_eq]
      exact isRestriction_partitionThreeTensor_mm K c I Acc col' p' hcompat' hc_le_B
    -- Bound `(B : ℝ)` in terms of `n`.
    have h4ξV : 4 * ξ * V_card ≤ δ * (n : ℝ) := by
      have hV_real : V_card ≤ 4 * (L_coef + 1) * (n : ℝ) := by
        have hv1 : V_card ≤ 4 * (c.innerSize : ℝ) + 3 := by
          dsimp only [V_card]; exact_mod_cast hV_le
        have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 3 ≤ n)
        have hε_n : 0 ≤ ε' * (n : ℝ) := by positivity
        linarith only [hv1, hs_le, hn3, hε_n]
      have hm := mul_le_mul_of_nonneg_left hV_real (show 0 ≤ 4 * ξ by positivity)
      have hid : 4 * ξ * (4 * (L_coef + 1) * (n : ℝ)) = 1 / 2 * (δ * (n : ℝ)) := by
        dsimp [ξ]
        have hne : L_coef + 1 ≠ 0 := by linarith only [hL_gt1]
        field_simp
        ring
      rw [hid] at hm
      have hδn : 0 ≤ δ * (n : ℝ) := by positivity
      linarith only [hm, hδn]
    set α : ℝ := 2 / 3 * threeWayCapCoefficient * (L_coef - 1 - ε')
    have hcyc_real :
        (G.cycleRank : ℝ) ≤ (L_coef - 1 - ε') * (n : ℝ) + (3 * δ * (n : ℝ) + 1) := by
      have hc : (G.cycleRank : ℝ) + (m : ℝ) ≤ (c.innerSize : ℝ) + 1 := by
        exact_mod_cast hcyc_read
      linarith only [hc, hs_le, hm_low]
    have hcap_cyc : 2 / 3 * threeWayCapCoefficient * (G.cycleRank : ℝ) ≤
        α * (n : ℝ) + 3 * δ * (n : ℝ) + 1 := by
      have hm1 := mul_le_mul_of_nonneg_left hcyc_real
        (by positivity : 0 ≤ 2 / 3 * threeWayCapCoefficient)
      have hpos3 : 0 ≤ 3 * δ * (n : ℝ) + 1 := by positivity
      have hm2 :
          2 / 3 * threeWayCapCoefficient * (3 * δ * (n : ℝ) + 1) ≤ 3 * δ * (n : ℝ) + 1 :=
        mul_le_of_le_one_left hpos3 hcap_le1
      have hα_eq : 2 / 3 * threeWayCapCoefficient *
          ((L_coef - 1 - ε') * (n : ℝ) + (3 * δ * (n : ℝ) + 1)) =
          α * (n : ℝ) + 2 / 3 * threeWayCapCoefficient * (3 * δ * (n : ℝ) + 1) := by
        dsimp [α]; ring
      linarith only [hm1, hm2, hα_eq]
    have hc_sz_real (k : Fin 3) :
        (c_sz k : ℝ) ≤ (α + 7 * δ) * (n : ℝ) + (4 * (C₀ : ℝ) + 1) := by
      have hstep : (c_sz k : ℝ) ≤
          ((G.edgeCut {v | col₀ v = k} ∩ G.edgeCut {v | col₀ v = k + 1}).ncard : ℝ) +
            (fuel : ℝ) := by
        exact_mod_cast hcut' k
      have hc0 := hcut₀ k
      have hexp_n : α * (n : ℝ) + 3 * δ * (n : ℝ) + 3 * δ * (n : ℝ) + δ * (n : ℝ) =
          (α + 7 * δ) * (n : ℝ) := by ring
      linarith only [hstep, hc0, hfuel_le, hcap_cyc, h4ξV, hexp_n]
    have hB_real : (B : ℝ) ≤ (α + 7 * δ) * (n : ℝ) + (4 * (C₀ : ℝ) + 1) := by
      simp only [B, Nat.cast_max]
      exact max_le (hc_sz_real 0) (max_le (hc_sz_real 1) (hc_sz_real 2))
    -- Multiply `(B : ℝ)` by `τ = omega K + δ` and compare against `(2 / 3 - δ) * n`.
    have hωα : omega K * α = 2 / 3 - gap := by
      dsimp [α, L_coef, gap]
      have h1 : omega K ≠ 0 := hω_pos.ne'
      have h2 : threeWayCapCoefficient ≠ 0 := hcap_pos.ne'
      field_simp
      ring
    have hα_le1 : α ≤ 1 := by
      have hsub : L_coef - 1 - ε' ≤ 1 / (omega K * threeWayCapCoefficient) := by
        dsimp [L_coef]; linarith only [hε'_pos]
      have hm := mul_le_mul_of_nonneg_left hsub
        (by positivity : 0 ≤ 2 / 3 * threeWayCapCoefficient)
      have hid : 2 / 3 * threeWayCapCoefficient * (1 / (omega K * threeWayCapCoefficient)) =
          2 / (3 * omega K) := by
        have h1 : omega K ≠ 0 := hω_pos.ne'
        have h2 : threeWayCapCoefficient ≠ 0 := hcap_pos.ne'
        field_simp
      have h23 : 2 / (3 * omega K) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith only [hω_ge2]
      dsimp [α]
      linarith only [hm, hid, h23]
    have hτ_slope : τ * (α + 7 * δ) ≤ 2 / 3 - 2 * δ := by
      have hexp : τ * (α + 7 * δ) = omega K * α + (7 * omega K + α + 7 * δ) * δ := by
        dsimp [τ]; ring
      have hcoef : (7 * omega K + α + 7 * δ) * δ ≤ (7 * omega K + 2) * δ :=
        mul_le_mul_of_nonneg_right (by linarith only [hα_le1, hδ_le_12]) hδ_pos.le
      have hgap_8δ : 8 * δ ≤ gap := by
        have h16 : (16 : ℝ) ≤ 4 * (7 * omega K + 2) := by linarith only [hω_ge2]
        have hm := mul_le_mul_of_nonneg_right h16 hδ_pos.le
        linarith only [hm, hδ_mul_le, hδ_pos]
      linarith only [hexp, hωα, hcoef, hδ_mul_le, hgap_8δ, hδ_pos]
    have hexp_tot :
        Real.log c_mm / Real.log (q : ℝ) + (B : ℝ) * τ ≤ (2 / 3 - δ) * (n : ℝ) := by
      have hmB := mul_le_mul_of_nonneg_right hB_real hτ_pos.le
      have hm_n := mul_le_mul_of_nonneg_right hτ_slope hn_pos.le
      have hlog_abs : Real.log c_mm / Real.log (q : ℝ) ≤ |Real.log c_mm| / Real.log (q : ℝ) :=
        div_le_div_of_nonneg_right (le_abs_self _) hlog_pos.le
      have hK_le : K_const ≤ δ * (n : ℝ) := (le_max_right 2 K_const).trans hn_K
      have halg : ((α + 7 * δ) * (n : ℝ) + (4 * (C₀ : ℝ) + 1)) * τ =
          τ * (α + 7 * δ) * (n : ℝ) + τ * (4 * (C₀ : ℝ) + 1) := by ring
      dsimp [K_const] at hK_le
      linarith only [hmB, hm_n, hlog_abs, hK_le, halg]
    -- Apply `h_mm (q ^ B)` to obtain a CP-rank `≤ r_hard` decomposition, contradicting `hHard`.
    obtain ⟨r_mm, hr_mm_le, hrank_mm⟩ := h_mm (q ^ B) (Nat.one_le_pow B q (by omega))
    have hc_mm_eq : c_mm = (q : ℝ) ^ (Real.log c_mm / Real.log (q : ℝ)) := by
      rw [Real.rpow_def_of_pos hq_pos, mul_div_cancel₀ _ hlog_pos.ne', Real.exp_log hc_mm_pos]
    have hqB_eq : ((q ^ B : ℕ) : ℝ) ^ τ = (q : ℝ) ^ ((B : ℝ) * τ) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast (q : ℝ) B, ← Real.rpow_mul hq_pos.le]
    have hr_le_hard : r_mm ≤ r_hard := by
      refine Nat.le_floor (hr_mm_le.trans ?_)
      rw [hc_mm_eq, hqB_eq, ← Real.rpow_add hq_pos]
      exact Real.rpow_le_rpow_of_exponent_le hq_gt1.le hexp_tot
    exact hHard p' hbal' ((Rank.of_isRestriction hrestr hrank_mm).mono hr_le_hard)

/-- **Unconditional `3.041n` fan-in-`2` circuit lower bound from `ThreeTensorHard`.** Wiring
`omega_le_nine_quarters` (`ω(K) ≤ 9 / 4` over any characteristic-zero field `K`) and
`circuitThreshold_gt_3041` (`3041 / 1000 < 1 + 4 / (9 * threeWayCapCoefficient)`) into
`innerSize_gt_of_threeTensorHard` yields `(3041 / 1000 - ε) * n < c.innerSize`. -/
theorem innerSize_gt_3041_of_threeTensorHard (K : Type*) [Field K] [CharZero K]
    {U : Type*} [Fintype U] (hU : 2 ≤ Fintype.card U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ {σ : Signature} {n : ℕ}, N₀ ≤ n →
      ∀ {S : Set (Fin n → U)},
        ThreeTensorHard K ⌊(Fintype.card U : ℝ) ^ ((2 / 3 - δ) * (n : ℝ))⌋₊ S →
        ∀ (c : Circuit σ n 1) (I : Interpretation σ U) (Acc : Fin 1 → Set U),
          c.FanInAtMost 2 → (∀ x, c.eval I x 0 ∈ Acc 0 ↔ x ∈ S) →
          (3041 / 1000 - ε) * (n : ℝ) < (c.innerSize : ℝ) := by
  obtain ⟨δ, hδ, N₀, hlb⟩ := innerSize_gt_of_threeTensorHard K hU hε
  have hω_94 : omega K ≤ 9 / 4 := omega_le_nine_quarters K
  have hω_ge2 : (2 : ℝ) ≤ omega K := two_le_omega K
  have hcap_pos : 0 < threeWayCapCoefficient := threeWayCapCoefficient_pos
  have hth : 3041 / 1000 < 1 + 4 / (9 * threeWayCapCoefficient) := circuitThreshold_gt_3041
  have hcoef : 3041 / 1000 ≤ 1 + 1 / (omega K * threeWayCapCoefficient) := by
    have hdiv : 4 / (9 * threeWayCapCoefficient) ≤ 1 / (omega K * threeWayCapCoefficient) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hω_94, hcap_pos]
    linarith only [hth, hdiv]
  refine ⟨δ, hδ, N₀, fun {σ n} hn {S} hHard c I Acc hfan hdec => ?_⟩
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hle : (3041 / 1000 - ε) * (n : ℝ) ≤
      (1 + 1 / (omega K * threeWayCapCoefficient) - ε) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith only [hcoef]) hn_nonneg
  exact hle.trans_lt (hlb hn hHard c I Acc hfan hdec)

/-- **End-to-end unconditional existence of `U`-ary functions requiring `> (3.041 - ε) n` inner
fan-in-`2` gates.** Instantiates `innerSize_gt_3041_of_threeTensorHard` over `ℚ` together with the
finite-counting witness `exists_threeTensorHard_eventually ℚ`. Note that `S` is a nonconstructive
counting witness (independent of the circuit signature `σ`, interpretation `I`, and acceptance set
`Acc`), not a polynomial-time explicit function family. -/
theorem exists_set_innerSize_gt_3041 {U : Type*} [Fintype U] (hU : 2 ≤ Fintype.card U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ S : Set (Fin n → U),
        ∀ {σ : Signature} (c : Circuit σ n 1) (I : Interpretation σ U) (Acc : Fin 1 → Set U),
          c.FanInAtMost 2 → (∀ x, c.eval I x 0 ∈ Acc 0 ↔ x ∈ S) →
          (3041 / 1000 - ε) * (n : ℝ) < (c.innerSize : ℝ) := by
  obtain ⟨δ, hδ, N₁, hlb⟩ := innerSize_gt_3041_of_threeTensorHard ℚ hU hε
  obtain ⟨N₂, hex⟩ := exists_threeTensorHard_eventually ℚ hU hδ
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  obtain ⟨S, hHard⟩ := hex n ((le_max_right N₁ N₂).trans hn)
  exact ⟨S, fun c I Acc hfan hdec => hlb ((le_max_left N₁ N₂).trans hn) hHard c I Acc hfan hdec⟩

end Cslib.Circuits.Frontier.TensorRank
