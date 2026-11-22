/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Frontier.BoundedFanIn
import CslibFrontier.Computability.Circuit.Frontier.Linear.Unconditional
import CslibFrontier.Computability.Circuit.Frontier.MultiPass
import CslibFrontier.Computability.Circuit.Frontier.Witness
import Mathlib.Analysis.Real.Pi.Bounds

/-! Checked clients for the degree-weighted walk kernel (`r = 3, 4, 5`) and multi-pass sweeps. -/

open Cslib.Circuits Cslib.Circuits.Frontier Matrix Real Filter Set

namespace CslibFrontierTests.FrontierWeightedKernel

/-! ### Strict improvements over the uniform `degreeCoefficient` baseline -/

example : (1 / 3 : ℝ) < Gaussian.degreeCoefficient 4 := by
  rw [Gaussian.degreeCoefficient_four]
  norm_num

example : WeightedKernel.fiveCoefficient < Gaussian.degreeCoefficient 5 := by
  have ha5 : arccos (4 / 5) ≤ 64351 / 100000 := WeightedKernel.arccos_four_fifths_le
  have hcorr5 : Gaussian.vertexCorrelation 5 = 4 / 5 := by
    unfold Gaussian.vertexCorrelation
    push_cast
    have h4 : √((5 : ℝ) - 1) = 2 := by
      norm_num
      exact (sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
    rw [h4]
    norm_num
  unfold WeightedKernel.fiveCoefficient Gaussian.degreeCoefficient Gaussian.vertexCoefficient
  rw [hcorr5]
  have ha_pos : 0 < arccos (4 / 5) := arccos_pos.mpr (by norm_num)
  have hpi : 0 < π := pi_pos
  have hleft : 5 / 3 * arccos (4 / 5) / π = 5 / 3 * (arccos (4 / 5) / π) := by ring
  have hright : (3 * (5 : ℕ) : ℝ) / (2 * (5 : ℕ) - 3) * (arccos (4 / 5) / π) =
      15 / 7 * (arccos (4 / 5) / π) := by
    push_cast
    ring
  rw [hleft, hright]
  have hpos : 0 < arccos (4 / 5) / π := div_pos ha_pos hpi
  linarith

example : WeightedKernel.sixCoefficient < Gaussian.degreeCoefficient 6 := by
  have hs5 : √5 < 3 := (sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hcorr6 : Gaussian.vertexCorrelation 6 = √5 / 3 := by
    unfold Gaussian.vertexCorrelation
    norm_num
    ring
  unfold WeightedKernel.sixCoefficient Gaussian.degreeCoefficient Gaussian.vertexCoefficient
  rw [hcorr6]
  have ha_pos : 0 < arccos (√5 / 3) := arccos_pos.mpr (by linarith)
  have hpos : 0 < arccos (√5 / 3) / π := div_pos ha_pos pi_pos
  have hleft : 3 / 2 * arccos (√5 / 3) / π = 3 / 2 * (arccos (√5 / 3) / π) := by ring
  have hright : (3 * (6 : ℕ) : ℝ) / (2 * (6 : ℕ) - 3) * (arccos (√5 / 3) / π) =
      2 * (arccos (√5 / 3) / π) := by
    push_cast
    ring
  rw [hleft, hright]
  linarith

example : (3929 / 1000 : ℝ) ≤ 1 + 3 * π / (5 * arccos (4 / 5)) :=
  WeightedKernel.fiveCircuitCoefficient_ge_3929

example : (387 / 100 : ℝ) ≤ 1 + 2 * π / (3 * arccos (√5 / 3)) :=
  WeightedKernel.sixCircuitCoefficient_ge_387

/-! ### Concrete mixed-degree `(3, 4)` parallel-edge multigraph check -/

/-- Three-vertex loopless multigraph with parallel edges and degrees `(4, 3, 3)`:
two parallel edges `(0, 1)`, two parallel edges `(0, 2)`, and one edge `(1, 2)`. -/
private def mixedParallelGraph : Multigraph (Fin 3) (Fin 5) where
  src e := match e.val with
    | 0 | 1 | 2 | 3 => 0
    | _ => 1
  tgt e := match e.val with
    | 0 | 1 => 1
    | _ => 2

private theorem mixedParallelGraph_loopless : mixedParallelGraph.Loopless := by
  intro e
  fin_cases e <;> decide

private theorem mixedParallelGraph_deg_pos (v : Fin 3) :
    0 < (mixedParallelGraph.incidenceSet v).ncard := by
  refine (ncard_pos (toFinite _)).mpr ?_
  fin_cases v
  · exact ⟨0, Or.inl rfl⟩
  · exact ⟨0, Or.inr rfl⟩
  · exact ⟨2, Or.inr rfl⟩

example : (∑ e : Fin 5,
      (1 - 1 / ((mixedParallelGraph.incidenceSet (mixedParallelGraph.src e)).ncard : ℝ) -
        1 / ((mixedParallelGraph.incidenceSet (mixedParallelGraph.tgt e)).ncard : ℝ))) = 2 := by
  rw [WeightedKernel.sum_one_sub_inv_deg_eq mixedParallelGraph_loopless
    mixedParallelGraph_deg_pos]
  norm_num

/-! ### Unconditional non-vacuous circuit and Cauchy linear-map clients (`r = 3, 4, 5`) -/

example : ∃ (S : ∀ n, Set (Fin n → Bool)) (K : ℕ → ℕ), DenseRectangleFree S K ∧
    ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), c.FanInAtMost 3 → c.Decides I Acc (S n) →
        (2 - 1 / 100 : ℝ) * n < c.innerSize := by
  obtain ⟨S, hrf, hlog, hdef, _⟩ := exists_rectangleFree_family
  have hSK : DenseRectangleFree S (fun n => n + 2) := ⟨hrf, hlog, hdef⟩
  exact ⟨S, fun n => n + 2, hSK,
    eventually_two_sub_mul_lt_innerSize_fanInThree.{0, 0} hSK (by norm_num)⟩

example : ∃ (S : ∀ n, Set (Fin n → Bool)) (K : ℕ → ℕ), DenseRectangleFree S K ∧
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 3 → c.NondeterministicDecides I Acc (S n) →
        (4 - 1 / 100 : ℝ) * n < 2 * c.innerSize := by
  obtain ⟨S, hrf, hlog, hdef, _⟩ := exists_rectangleFree_family
  have hSK : DenseRectangleFree S (fun n => n + 2) := ⟨hrf, hlog, hdef⟩
  exact ⟨S, fun n => n + 2, hSK,
    eventually_four_sub_mul_lt_two_mul_innerSize_of_nondeterministicDecides.{0, 0} hSK
      (by norm_num)⟩

example : ∃ (S : ∀ n, Set (Fin n → Bool)) (K : ℕ → ℕ), DenseRectangleFree S K ∧
    ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), c.FanInAtMost 4 → c.Decides I Acc (S n) →
        (3929 / 1000 - 1 / 100 : ℝ) * n < 3 * c.innerSize := by
  obtain ⟨S, hrf, hlog, hdef, _⟩ := exists_rectangleFree_family
  have hSK : DenseRectangleFree S (fun n => n + 2) := ⟨hrf, hlog, hdef⟩
  exact ⟨S, fun n => n + 2, hSK,
    eventually_3929_div_1000_lt_three_mul_innerSize.{0, 0} hSK (by norm_num)⟩

example : ∃ (S : ∀ n, Set (Fin n → Bool)) (K : ℕ → ℕ), DenseRectangleFree S K ∧
    ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), c.FanInAtMost 5 → c.Decides I Acc (S n) →
        (387 / 100 - 1 / 100 : ℝ) * n < 4 * c.innerSize := by
  obtain ⟨S, hrf, hlog, hdef, _⟩ := exists_rectangleFree_family
  have hSK : DenseRectangleFree S (fun n => n + 2) := ⟨hrf, hlog, hdef⟩
  exact ⟨S, fun n => n + 2, hSK,
    eventually_387_div_100_lt_four_mul_innerSize.{0, 0} hSK (by norm_num)⟩

example : ∀ᶠ N in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ ℚ),
    I.IsPolynomial → ∀ (c : Circuit σ N N), c.FanInAtMost 3 →
      c.Computes I (fun x => Matrix.cauchyNat ℚ N *ᵥ x) →
        (4 - 1 / 100 : ℝ) * N < 2 * c.innerSize := by
  have h := eventually_four_sub_mul_lt_two_mul_innerSize_of_isTotallyRegular_isPolynomial.{0, 0}
    (ε := 1 / 100) (by norm_num)
  filter_upwards [h] with N hN σ I hpoly c hfan hc
  exact hN ℚ σ I hpoly (Matrix.cauchyNat ℚ N) c (Matrix.isTotallyRegular_cauchyNat N) hfan hc

/-! ### Concrete non-vacuous `MultiPass` client checks -/

/-- Explicit 2-pass alternating deterministic BP on `Fin 2 → Bool` accepting `{x | x 0 = x 1}`
with 2-element state space `Bool`. -/
private def eqAlt2Pass : AlternatingPassNBP (Fin 2) Bool Bool where
  passes := 2
  passes_pos := by decide
  length := 2
  revealed t := {i : Fin 2 | i.val < t}
  revealed_zero := by ext i; simp
  revealed_length := by
    ext i
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact i.isLt
  revealed_mono _ _ hab _ hi := lt_of_lt_of_le hi hab
  start := false
  accept := true
  Edge p s m a m' :=
    if hp0 : p = 0 then
      if hs0 : s = 0 then
        m' = a ⟨0, by subst hp0 hs0; simp [passCoord]⟩
      else m' = m
    else if hp1 : p = 1 then
      if hs0 : s = 0 then
        m' = (m == a ⟨1, by subst hp1 hs0; simp [passCoord]⟩)
      else m' = m
    else m' = m

private theorem eqAlt2Pass_deterministic : eqAlt2Pass.Deterministic := by
  intro p _ s _ m a m₁ m₂ h₁ h₂
  dsimp only [eqAlt2Pass] at h₁ h₂
  split_ifs at h₁ h₂ <;> exact h₁.trans h₂.symm

private theorem eqAlt2Pass_unit : ∀ t < eqAlt2Pass.length, (eqAlt2Pass.newly t).ncard ≤ 1 := by
  intro t _
  refine (ncard_le_one (toFinite _)).mpr ?_
  rintro i ⟨hi₁, hi₂⟩ j ⟨hj₁, hj₂⟩
  simp only [eqAlt2Pass, mem_ofPred_eq, not_lt] at hi₁ hi₂ hj₁ hj₂
  exact Fin.ext (by omega)

/-- Any subset of `Fin 2 → Bool` with at most `2` elements is `2`-rectangle-free (since a `2 × 2`
rectangle has `4` elements). -/
private theorem rectangleFree_of_ncard_le_two {S : Set (Fin 2 → Bool)} (hS : S.ncard ≤ 2) :
    RectangleFree S 2 := by
  rw [rectangleFree_iff]
  intro X A B hAB
  by_contra! hge
  have hrect : 4 ≤ (rectangle X A B).ncard := by
    rw [ncard_rectangle]
    exact Nat.mul_le_mul hge.1 hge.2
  have hle : (rectangle X A B).ncard ≤ S.ncard := ncard_le_ncard hAB (toFinite _)
  omega

private theorem eqAlt2Pass_accepted_sub : eqAlt2Pass.accepted ⊆ {x | x 0 = x 1} := by
  rintro x ⟨γ, _, hacc, hturn, hedge⟩
  have he00 := hedge 0 (by decide) 0 (by decide)
  have he01 := hedge 0 (by decide) 1 (by decide)
  have he10 := hedge 1 (by decide) 0 (by decide)
  have he11 := hedge 1 (by decide) 1 (by decide)
  have ht0 := hturn 0 (by decide)
  simp only [eqAlt2Pass, ↓reduceDIte, Nat.one_ne_zero, AlternatingPassNBP.stepCoords,
    AlternatingPassNBP.newly, domRestrict] at he00 he01 he10 he11 hacc ht0
  rw [he11, he10, ht0, he01, he00] at hacc
  exact beq_iff_eq.mp hacc

private theorem eqAlt2Pass_nonempty : eqAlt2Pass.accepted.Nonempty := by
  refine ⟨fun _ => false, fun p s =>
    match p, s with
    | 0, _ => false
    | _, 0 => false
    | _, _ => true, rfl, rfl, ?_, ?_⟩
  · intro p hp
    have hp0 : p = 0 := by change p + 1 < 2 at hp; omega
    subst p
    rfl
  · intro p hp s hs
    have hp2 : p = 0 ∨ p = 1 := by change p < 2 at hp; omega
    have hs2 : s = 0 ∨ s = 1 := by change s < 2 at hs; omega
    rcases hp2 with rfl | rfl <;> rcases hs2 with rfl | rfl <;>
      simp [eqAlt2Pass, AlternatingPassNBP.stepCoords, domRestrict]

private theorem eqAlt2Pass_rectangleFree : RectangleFree eqAlt2Pass.accepted 2 := by
  refine rectangleFree_of_ncard_le_two ?_
  calc eqAlt2Pass.accepted.ncard
      ≤ ({x : Fin 2 → Bool | x 0 = x 1} : Set _).ncard :=
        ncard_le_ncard eqAlt2Pass_accepted_sub (toFinite _)
    _ ≤ ({(fun _ : Fin 2 => false), (fun _ : Fin 2 => true)} : Set _).ncard := by
        refine ncard_le_ncard (fun x hx => ?_) (toFinite _)
        simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff] at hx ⊢
        cases h0 : x 0
        · left
          funext i
          fin_cases i <;> simp [h0, ← hx]
        · right
          funext i
          fin_cases i <;> simp [h0, ← hx]
    _ ≤ ({(fun _ : Fin 2 => true)} : Set _).ncard + 1 := ncard_insert_le _ _
    _ = 2 := by rw [ncard_singleton]

example : eqAlt2Pass.accepted.ncard ≤
    (2 - 1) ^ 2 * eqAlt2Pass.length * Nat.card Bool * Nat.card Bool ^ eqAlt2Pass.passes :=
  eqAlt2Pass.ncard_accepted_le_deterministic eqAlt2Pass_deterministic (by decide)
    eqAlt2Pass_unit eqAlt2Pass_rectangleFree

example : Real.logb (Nat.card Bool) eqAlt2Pass.accepted.ncard -
      2 * Real.logb (Nat.card Bool) 2 - Real.logb (Nat.card Bool) eqAlt2Pass.length - 1 ≤
    (eqAlt2Pass.passes : ℝ) * Real.logb (Nat.card Bool) (Nat.card Bool) :=
  eqAlt2Pass.le_passes_mul_logb_card eqAlt2Pass_deterministic (by decide)
    eqAlt2Pass_unit eqAlt2Pass_rectangleFree eqAlt2Pass_nonempty

example (O : Set (Fin 2)) (a : O → Bool) :
    RectangleFree (restrictSlice eqAlt2Pass.accepted O a) 2 :=
  eqAlt2Pass_rectangleFree.restrictSlice O a

end CslibFrontierTests.FrontierWeightedKernel
