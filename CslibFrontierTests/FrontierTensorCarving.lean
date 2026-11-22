/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Frontier.Layouts.Carving
import CslibFrontier.Computability.Circuit.Frontier.TensorRank
import Mathlib.Algebra.Field.ZMod

/-! Checked clients for cubic multigraph carving-width / branchwidth and `3`-tensor CP-rank
fan-in-`2` circuit lower bounds (`3.041n`). -/

set_option linter.privateModule false

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic.MatrixMultiplication
open Cslib.Circuits.Frontier Cslib.Tensor Set

namespace CslibFrontierTests.FrontierTensorCarving

/-! ### Numerical coefficient comparisons -/

example : Carving.carvingCoefficient ≤ 137432 / 1000000 :=
  Carving.carvingCoefficient_le_137432

example : Carving.carvingCoefficient < Switched.switchedCoefficient :=
  Carving.carvingCoefficient_lt_switchedCoefficient

example : TensorRank.threeWayCapCoefficient ≤ 21773 / 100000 :=
  TensorRank.threeWayCapCoefficient_le_21773

example : (3041 / 1000 : ℝ) < 1 + 4 / (9 * TensorRank.threeWayCapCoefficient) :=
  TensorRank.circuitThreshold_gt_3041

/-! ### Concrete cubic multigraphs: theta multigraph (parallel edges) and `K₄` -/

/-- The cubic theta multigraph `Θ₃`: two vertices joined by three parallel edges. -/
private def thetaGraph : Multigraph Bool (Fin 3) where
  src _ := false
  tgt _ := true

private theorem thetaGraph_loopless : thetaGraph.Loopless := by
  intro e; simp [thetaGraph]

private theorem thetaGraph_cubic : ∀ v : Bool, (thetaGraph.incidenceSet v).ncard = 3 := by
  intro v
  have h : thetaGraph.incidenceSet v = univ := by
    ext e; cases v <;> simp [Multigraph.incidenceSet, thetaGraph]
  rw [h, ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

example : thetaGraph.branchwidth ≤ thetaGraph.carvingWidth :=
  thetaGraph.branchwidth_le_carvingWidth thetaGraph_loopless thetaGraph_cubic

example : thetaGraph.carvingWidth ≤ 3 := by
  have hp := Carving.BinTree.isPartition_node
    (Carving.BinTree.isPartition_leaf false)
    (Carving.BinTree.isPartition_leaf true) (by simp)
  have huniv : ({false} ∪ {true} : Set Bool) = univ := by
    ext b; cases b <;> simp
  rw [huniv] at hp
  exact thetaGraph.carvingWidth_le_of_binTree hp fun S _ =>
    (ncard_le_card (thetaGraph.edgeCut S)).trans (by simp)

/-- The complete cubic graph `K₄` on `Fin 4` with `6` edges. -/
private def k4Src : Fin 6 → Fin 4
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 1 | 5 => 2

private def k4Tgt : Fin 6 → Fin 4
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 2 | 4 => 3 | 5 => 3

private def k4Graph : Multigraph (Fin 4) (Fin 6) where
  src := k4Src
  tgt := k4Tgt

private theorem k4Graph_loopless : k4Graph.Loopless := by
  intro e; fin_cases e <;> decide

private theorem k4Graph_cubic : ∀ v : Fin 4, (k4Graph.incidenceSet v).ncard = 3 := by
  intro v
  have hset : k4Graph.incidenceSet v =
      ↑(Finset.univ.filter fun e : Fin 6 => k4Src e = v ∨ k4Tgt e = v) := by
    ext e; simp [Multigraph.incidenceSet, k4Graph]
  rw [hset, Set.ncard_coe_finset]
  fin_cases v <;> decide

example : k4Graph.branchwidth ≤ k4Graph.carvingWidth :=
  k4Graph.branchwidth_le_carvingWidth k4Graph_loopless k4Graph_cubic

/-! ### Asymptotic carving-width and branchwidth bounds below `c₃` -/

example : ∃ N₀ : ℕ, ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
    G.Loopless → (∀ v, (G.incidenceSet v).ncard = 3) → N₀ < Nat.card V →
      G.branchwidth ≤ G.carvingWidth ∧
        (G.carvingWidth : ℝ) ≤ (137432 / 1000000 + 1 / 1000000) * Nat.card V := by
  obtain ⟨N₀, hN₀⟩ := Carving.exists_carvingWidth_le_137432 (ξ := 1 / 1000000) (by norm_num)
  exact ⟨N₀, fun V E _ _ G hloop h3 hN =>
    ⟨G.branchwidth_le_carvingWidth hloop h3, hN₀ V E G hloop h3 hN⟩⟩

example : ∃ N₀ : ℕ, ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
    G.Loopless → (∀ v, (G.incidenceSet v).ncard = 3) → N₀ < Nat.card V →
      (G.branchwidth : ℝ) ≤ (Carving.carvingCoefficient + 1 / 1000) * Nat.card V :=
  Carving.exists_branchwidth_le_carvingCoefficient (by norm_num)

/-! ### Strassen rank extraction and concrete `ThreeTensorHard` witnesses (`ZMod 2` and `ℚ`) -/

example {n : ℕ} (C : Circuit (arithSignature ℚ) (n * n + n * n) (n * n))
    (hC : ComputesMatMul ℚ C) :
    Rank (2 * C.program.cost ArithOp.mulCost) (Tensor.mm n n n : Tensor ℚ _ _ _) :=
  rank_mm_two_mul_mulCost hC

example {n : ℕ} (C : Circuit (arithSignature ℚ) (n * n + n * n) (n * n))
    (hC : ComputesMatMul ℚ C) : Rank (2 * C.size) (Tensor.mm n n n : Tensor ℚ _ _ _) :=
  rank_mm_two_mul_size hC

example : TensorRank.BalancedTripartition 3 id := by
  rw [TensorRank.balancedTripartition_iff]
  intro c
  have h : {i : Fin 3 | id i = c} = {c} := by ext i; simp
  rw [h, Set.ncard_singleton]

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Explicit finite-`n` counting check (`n = 11`, `U = Bool`, `r = 1`) for
`exists_threeTensorHard`. -/
private theorem count_fin11_bool :
    3 ^ 11 * (3 * Fintype.card Bool ^ 11 + 1) ^ (3 * 1 * Fintype.card Bool ^ (11 / 3 + 2)) <
      2 ^ (Fintype.card Bool ^ 11) := by
  simp only [Fintype.card_bool]
  have h1 : 3 ^ 11 ≤ (2 ^ 16) ^ 2 := by decide
  have h2 : (3 * 2 ^ 11 + 1) ^ (3 * 1 * 2 ^ (11 / 3 + 2)) ≤ (2 ^ 16) ^ 96 := by
    have hexp : 3 * 1 * 2 ^ (11 / 3 + 2) = 96 := by decide
    rw [hexp]
    exact Nat.pow_le_pow_left (by decide) 96
  calc 3 ^ 11 * (3 * 2 ^ 11 + 1) ^ (3 * 1 * 2 ^ (11 / 3 + 2))
      ≤ (2 ^ 16) ^ 2 * (2 ^ 16) ^ 96 := Nat.mul_le_mul h1 h2
    _ = (2 ^ 16) ^ (2 + 96) := (pow_add (2 ^ 16) 2 96).symm
    _ < (2 ^ 16) ^ 128 := Nat.pow_lt_pow_right (a := 2 ^ 16) (by decide) (by decide)
    _ = 2 ^ (2 ^ 11) := by
        rw [← pow_mul, show 16 * 128 = 2 ^ 11 by decide]

example : ∃ S : Set (Fin 11 → Bool), TensorRank.ThreeTensorHard (ZMod 2) 1 S :=
  TensorRank.exists_threeTensorHard (ZMod 2) (n := 11) (U := Bool) (r := 1)
    (by decide) count_fin11_bool

example : ∃ S : Set (Fin 11 → Bool), TensorRank.ThreeTensorHard ℚ 1 S :=
  TensorRank.exists_threeTensorHard ℚ (n := 11) (U := Bool) (r := 1)
    (by decide) count_fin11_bool

/-! ### End-to-end `3.041n` fan-in-`2` circuit lower bound clients -/

example : ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ {σ : Signature.{0}} {n : ℕ}, N₀ ≤ n →
    ∀ {S : Set (Fin n → Bool)},
      TensorRank.ThreeTensorHard ℚ ⌊(2 : ℝ) ^ ((2 / 3 - δ) * (n : ℝ))⌋₊ S →
      ∀ (c : Circuit σ n 1) (I : Interpretation σ Bool) (Acc : Fin 1 → Set Bool),
        c.FanInAtMost 2 → (∀ x, c.eval I x 0 ∈ Acc 0 ↔ x ∈ S) →
        (3041 / 1000 - 1 / 1000) * (n : ℝ) < (c.innerSize : ℝ) := by
  simpa [Fintype.card_bool] using
    TensorRank.innerSize_gt_3041_of_threeTensorHard ℚ (U := Bool) (by decide)
      (ε := 1 / 1000) (by norm_num)

example : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ S : Set (Fin n → Bool),
      ∀ {σ : Signature.{0}} (c : Circuit σ n 1) (I : Interpretation σ Bool)
        (Acc : Fin 1 → Set Bool),
        c.FanInAtMost 2 → (∀ x, c.eval I x 0 ∈ Acc 0 ↔ x ∈ S) →
        (304 / 100 : ℝ) * (n : ℝ) < (c.innerSize : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := TensorRank.exists_set_innerSize_gt_3041 (U := Bool) (by decide)
    (ε := 1 / 1000) (by norm_num)
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨S, hS⟩ := hN₀ n hn
  refine ⟨S, fun c I Acc hfan hdec => ?_⟩
  have hle : (304 / 100 : ℝ) * (n : ℝ) ≤ (3041 / 1000 - 1 / 1000) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg n)
  exact hle.trans_lt (hS c I Acc hfan hdec)

end CslibFrontierTests.FrontierTensorCarving
