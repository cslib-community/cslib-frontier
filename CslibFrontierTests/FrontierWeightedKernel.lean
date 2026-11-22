/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Computability.Circuit.Frontier.BoundedFanIn
public import CslibFrontier.Computability.Circuit.Frontier.Linear.Unconditional
public import CslibFrontier.Computability.Circuit.Frontier.MultiPass
public import CslibFrontier.Computability.Circuit.Frontier.Witness
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Analysis.Real.Pi.Bounds

/-! Checked `module` clients for `WeightedKernel` (`r = 3, 4, 5`) and `MultiPass`. -/

public section

open Cslib.Circuits Cslib.Circuits.Frontier Matrix Real Filter Set

namespace CslibFrontierTests.FrontierWeightedKernel

/-! ### Direct `module` checks of `@[expose]` definitions and `layoutBound_of_weightedKernel` -/

/-- Direct `@[expose]` check unfolding `pairCorrelation` and `pairWeight` under `module`. -/
theorem pairCorrelation_three_three : WeightedKernel.pairCorrelation 3 3 = 2 * √2 / 3 := by
  unfold WeightedKernel.pairCorrelation WeightedKernel.pairWeight
  push_cast
  have hss : √(√(3 - 1 : ℝ)) * √(√(3 - 1 : ℝ)) = √2 := by norm_num
  rw [hss]
  have hne : (√2 : ℝ) ≠ 0 := by positivity
  have hsq : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  field_simp
  nlinarith [hsq]

example : LayoutBound 3 (Gaussian.degreeCoefficient 3) := by
  have hcoeff : Gaussian.degreeCoefficient 3 =
      3 * (arccos (Gaussian.vertexCorrelation 3) / π) := by
    unfold Gaussian.degreeCoefficient Gaussian.vertexCoefficient
    norm_num
  have hA0 : 0 ≤ Gaussian.degreeCoefficient 3 := by
    rw [hcoeff]
    have hcorr : Gaussian.vertexCorrelation 3 ≤ 1 := by
      rw [← WeightedKernel.pairCorrelation_self (by decide)]
      unfold WeightedKernel.pairCorrelation
      have hq0 : 0 ≤ WeightedKernel.pairWeight 3 3 := by
        unfold WeightedKernel.pairWeight; positivity
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg (WeightedKernel.pairWeight 3 3 - 1)]
    exact mul_nonneg (by norm_num) (div_nonneg (arccos_nonneg _) pi_pos.le)
  refine layoutBound_of_weightedKernel (by decide) hA0 fun d₁ d₂ h1lo h12 h2hi _ => ?_
  have hd1 : d₁ = 3 := by omega
  have hd2 : d₂ = 3 := by omega
  subst hd1 hd2
  rw [WeightedKernel.pairCorrelation_self (by decide), hcoeff]
  push_cast
  linarith

example : passBoundary 2 1 1 = 1 := rfl

/-! ### Strict improvements over the uniform `degreeCoefficient` baseline -/

example : (1 / 3 : ℝ) < Gaussian.degreeCoefficient 4 := by
  rw [Gaussian.degreeCoefficient_four]
  norm_num

example : WeightedKernel.fiveCoefficient < Gaussian.degreeCoefficient 5 := by
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
        (2 - 1 / 100 : ℝ) * n < c.multiarySize := by
  obtain ⟨S, hrf, hlog, hdef, _⟩ := exists_rectangleFree_family
  have hSK : DenseRectangleFree S (fun n => n + 2) := ⟨hrf, hlog, hdef⟩
  exact ⟨S, fun n => n + 2, hSK,
    eventually_two_sub_mul_lt_multiarySize_fanInThree.{0, 0} hSK (by norm_num)⟩

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

/-! ### Checked `SameOrderPassNBP` client (`2`-pass forward-only equality BP) -/

/-- Explicit 2-pass same-order deterministic BP on `Fin 2 → Bool` accepting `{x | x 0 = x 1}`
with 2-element state space `Bool`. -/
private def eqSame2Pass : SameOrderPassNBP (Fin 2) Bool Bool where
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
    if p = 0 then
      if hs0 : s = 0 then
        m' = a ⟨0, by subst hs0; simp⟩
      else m' = m
    else if p = 1 then
      if hs1 : s = 1 then
        m' = (m == a ⟨1, by subst hs1; simp⟩)
      else m' = m
    else m' = m

private theorem eqSame2Pass_deterministic : eqSame2Pass.Deterministic := by
  intro p _ s _ m a m₁ m₂ h₁ h₂
  dsimp only [eqSame2Pass] at h₁ h₂
  split_ifs at h₁ h₂ <;> exact h₁.trans h₂.symm

private theorem eqSame2Pass_unit : ∀ t < eqSame2Pass.length, (eqSame2Pass.newly t).ncard ≤ 1 :=
  eqAlt2Pass_unit

private theorem eqSame2Pass_accepted_sub : eqSame2Pass.accepted ⊆ {x | x 0 = x 1} := by
  rintro x ⟨γ, _, hacc, hturn, hedge⟩
  have he00 := hedge 0 (by decide) 0 (by decide)
  have he01 := hedge 0 (by decide) 1 (by decide)
  have he10 := hedge 1 (by decide) 0 (by decide)
  have he11 := hedge 1 (by decide) 1 (by decide)
  have ht0 := hturn 0 (by decide)
  simp only [eqSame2Pass, ↓reduceIte, ↓reduceDIte, Nat.one_ne_zero,
    SameOrderPassNBP.newly, domRestrict] at he00 he01 he10 he11 hacc ht0
  have hne01 : ¬((0 : ℕ) = 1) := by decide
  simp only [hne01, ↓reduceDIte] at he10
  rw [he11, he10, ht0, he01, he00] at hacc
  exact beq_iff_eq.mp hacc

private theorem eqSame2Pass_nonempty : eqSame2Pass.accepted.Nonempty := by
  refine ⟨fun _ => false, fun p s =>
    match p, s with
    | 0, _ => false
    | _, 0 | _, 1 => false
    | _, _ => true, rfl, rfl, ?_, ?_⟩
  · intro p hp
    have hp0 : p = 0 := by change p + 1 < 2 at hp; omega
    subst p
    rfl
  · intro p hp s hs
    have hp2 : p = 0 ∨ p = 1 := by change p < 2 at hp; omega
    have hs2 : s = 0 ∨ s = 1 := by change s < 2 at hs; omega
    rcases hp2 with rfl | rfl <;> rcases hs2 with rfl | rfl <;>
      simp [eqSame2Pass, SameOrderPassNBP.newly, domRestrict]

private theorem eqSame2Pass_rectangleFree : RectangleFree eqSame2Pass.accepted 2 := by
  refine rectangleFree_of_ncard_le_two ?_
  calc eqSame2Pass.accepted.ncard
      ≤ ({x : Fin 2 → Bool | x 0 = x 1} : Set _).ncard :=
        ncard_le_ncard eqSame2Pass_accepted_sub (toFinite _)
    _ ≤ ({(fun _ : Fin 2 => false), (fun _ : Fin 2 => true)} : Set _).ncard := by
        refine ncard_le_ncard (fun x hx => ?_) (toFinite _)
        simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff] at hx ⊢
        cases h0 : x 0
        · left; funext i; fin_cases i <;> simp [h0, ← hx]
        · right; funext i; fin_cases i <;> simp [h0, ← hx]
    _ ≤ ({(fun _ : Fin 2 => true)} : Set _).ncard + 1 := ncard_insert_le _ _
    _ = 2 := by rw [ncard_singleton]

example : eqSame2Pass.accepted.ncard ≤
    (2 - 1) ^ 2 * eqSame2Pass.length * Nat.card Bool *
      Nat.card Bool ^ (2 * eqSame2Pass.passes - 1) :=
  eqSame2Pass.ncard_accepted_le_deterministic eqSame2Pass_deterministic (by decide)
    eqSame2Pass_unit eqSame2Pass_rectangleFree

example : Real.logb (Nat.card Bool) eqSame2Pass.accepted.ncard -
      2 * Real.logb (Nat.card Bool) 2 - Real.logb (Nat.card Bool) eqSame2Pass.length - 1 ≤
    ((2 * eqSame2Pass.passes - 1 : ℕ) : ℝ) * Real.logb (Nat.card Bool) (Nat.card Bool) :=
  eqSame2Pass.le_two_mul_passes_sub_one_mul_logb_card eqSame2Pass_deterministic (by decide)
    eqSame2Pass_unit eqSame2Pass_rectangleFree eqSame2Pass_nonempty

/-! ### Checked `RectangleBias.restrictSlice` client (`0`-bias 3-bit parity restricted to 2 bits) -/

private def parity3 : Set (Fin 3 → Bool) :=
  {x | ((x 0 != x 1) != x 2) = false}

private def flipAt (i : Fin 3) (x : Fin 3 → Bool) (j : Fin 3) : Bool :=
  if j = i then !x j else x j

private theorem flipAt_flipAt (i : Fin 3) (x : Fin 3 → Bool) :
    flipAt i (flipAt i x) = x := by
  funext j
  by_cases h : j = i <;> simp [flipAt, h]

private theorem flipAt_injective (i : Fin 3) : Function.Injective (flipAt i) :=
  Function.Involutive.injective (flipAt_flipAt i)

private theorem mem_parity3_flipAt (i : Fin 3) (x : Fin 3 → Bool) :
    flipAt i x ∈ parity3 ↔ x ∉ parity3 := by
  simp only [parity3, mem_ofPred_eq, flipAt]
  fin_cases i <;> cases x 0 <;> cases x 1 <;> cases x 2 <;> decide

private theorem parity3_rectangleBias : RectangleBias parity3 2 0 := by
  intro X A B hA hB
  have hcompl : X.ncard + Xᶜ.ncard = 3 := by simpa using ncard_add_ncard_compl X
  have hA_ub : A.ncard ≤ 2 ^ X.ncard := by
    calc A.ncard ≤ (univ : Set (X → Bool)).ncard := ncard_le_ncard (subset_univ _) (toFinite _)
      _ = 2 ^ X.ncard := by rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq]; simp
  have hB_ub : B.ncard ≤ 2 ^ Xᶜ.ncard := by
    calc B.ncard ≤ (univ : Set (↥Xᶜ → Bool)).ncard := ncard_le_ncard (subset_univ _) (toFinite _)
      _ = 2 ^ Xᶜ.ncard := by rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq]; simp
  have hX_pos : 1 ≤ X.ncard := by
    by_contra h0
    have : X.ncard = 0 := by omega
    rw [this] at hA_ub
    omega
  have hXc_pos : 1 ≤ Xᶜ.ncard := by
    by_contra h0
    have : Xᶜ.ncard = 0 := by omega
    rw [this] at hB_ub
    omega
  have hex_closed : ∃ i : Fin 3, ∀ z ∈ rectangle X A B, flipAt i z ∈ rectangle X A B := by
    rcases (show X.ncard = 1 ∨ Xᶜ.ncard = 1 by omega) with hX1 | hXc1
    · have hA_univ : A = univ := by
        refine eq_of_subset_of_ncard_le (subset_univ A) ?_ (toFinite _)
        rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq, hX1]
        simpa using hA
      obtain ⟨i, hi⟩ := (ncard_pos (toFinite X)).mp (by omega)
      refine ⟨i, fun z hz => ⟨hA_univ ▸ mem_univ _, ?_⟩⟩
      have heq : Xᶜ.domRestrict (flipAt i z) = Xᶜ.domRestrict z := by
        funext ⟨j, hj⟩
        have hji : j ≠ i := fun h => hj (h ▸ hi)
        simp [domRestrict, flipAt, hji]
      exact heq ▸ hz.2
    · have hB_univ : B = univ := by
        refine eq_of_subset_of_ncard_le (subset_univ B) ?_ (toFinite _)
        rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq, hXc1]
        simpa using hB
      obtain ⟨i, hi⟩ := (ncard_pos (toFinite Xᶜ)).mp (by omega)
      refine ⟨i, fun z hz => ⟨?_, hB_univ ▸ mem_univ _⟩⟩
      have heq : X.domRestrict (flipAt i z) = X.domRestrict z := by
        funext ⟨j, hj⟩
        have hji : j ≠ i := fun h => hi (h ▸ hj)
        simp [domRestrict, flipAt, hji]
      exact heq ▸ hz.1
  obtain ⟨i, hclosed⟩ := hex_closed
  set R := rectangle X A B
  have himg : flipAt i '' (R ∩ parity3) = R \ parity3 := by
    ext w
    constructor
    · rintro ⟨z, ⟨hzR, hzP⟩, rfl⟩
      exact ⟨hclosed z hzR, fun h => (mem_parity3_flipAt i z).mp h hzP⟩
    · rintro ⟨hwR, hwP⟩
      exact ⟨flipAt i w, ⟨hclosed w hwR, (mem_parity3_flipAt i w).mpr hwP⟩, flipAt_flipAt i w⟩
  have hcard_eq : (R ∩ parity3).ncard = (R \ parity3).ncard := by
    rw [← himg, ncard_image_of_injective _ (flipAt_injective i)]
  have htot : ((R ∩ parity3).ncard : ℝ) + (R \ parity3).ncard = R.ncard := by
    exact_mod_cast ncard_inter_add_ncard_sdiff_eq_ncard R parity3
  have hhalf : ((R ∩ parity3).ncard : ℝ) - R.ncard / 2 = 0 := by
    have : ((R ∩ parity3).ncard : ℝ) = (R \ parity3).ncard := by exact_mod_cast hcard_eq
    linarith
  rw [hhalf, abs_zero, zero_mul]

/-- Non-vacuous check on a `2 × 2` rectangle inside the 2-variable slice `↥({0}ᶜ) → Bool`:
fixing bit `0` preserves zero bias on `{1} × {2}` and forces zero `signedCount`. -/
example (a : ({0} : Set (Fin 3)) → Bool) :
    let O : Set (Fin 3) := {0}
    let Y : Set ↥Oᶜ := {⟨1, by decide⟩}
    signedCount (restrictSlice parity3 O a) (rectangle Y univ univ) = 0 := by
  intro O Y
  have hbias : RectangleBias (restrictSlice parity3 O a) 2 0 :=
    parity3_rectangleBias.restrictSlice O a
  have hY : 2 ≤ (univ : Set (Y → Bool)).ncard := by
    have hne : Y.Nonempty := ⟨⟨1, by decide⟩, rfl⟩
    have hpos : 1 ≤ Y.ncard := (ncard_pos (toFinite Y)).mpr hne
    rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq]
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ Y.ncard := Nat.pow_le_pow_right (by decide) hpos
      _ = Nat.card Bool ^ Y.ncard := by simp
  have hYc : 2 ≤ (univ : Set (↥Yᶜ → Bool)).ncard := by
    have hmem : (⟨2, by decide⟩ : ↥Oᶜ) ∈ Yᶜ := by decide
    have hpos : 1 ≤ Yᶜ.ncard := (ncard_pos (toFinite Yᶜ)).mpr ⟨_, hmem⟩
    rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq]
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ Yᶜ.ncard := Nat.pow_le_pow_right (by decide) hpos
      _ = Nat.card Bool ^ Yᶜ.ncard := by simp
  have hle := hbias.abs_signedCount_rectangle_le hY hYc
  rw [mul_zero, zero_mul, abs_nonpos_iff] at hle
  exact hle

/-! ### Checked `le_logb_card_of_slice_readOnce` client (`ReadOnceNBP` on `↥Oᶜ`) -/

private def eqSet2 : Set (Fin 2 → Bool) :=
  {x | x 0 = x 1}

private theorem eqSet2_rectangleFree : RectangleFree eqSet2 2 := by
  refine rectangleFree_of_ncard_le_two ?_
  calc eqSet2.ncard
      ≤ ({(fun _ : Fin 2 => false), (fun _ : Fin 2 => true)} : Set _).ncard := by
        refine ncard_le_ncard (fun x hx => ?_) (toFinite _)
        simp only [eqSet2, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff] at hx ⊢
        cases h0 : x 0
        · left; funext i; fin_cases i <;> simp [h0, ← hx]
        · right; funext i; fin_cases i <;> simp [h0, ← hx]
    _ ≤ ({(fun _ : Fin 2 => true)} : Set _).ncard + 1 := ncard_insert_le _ _
    _ = 2 := by rw [ncard_singleton]

private def eqSliceReadOnce (a : ({0} : Set (Fin 2)) → Bool) :
    ReadOnceNBP ↥({0} : Set (Fin 2))ᶜ Bool Bool where
  length := 1
  revealed t := if t = 0 then ∅ else univ
  revealed_zero := rfl
  revealed_length := rfl
  revealed_mono s t hst := by
    by_cases hs : s = 0
    · simp [hs]
    · have ht : t ≠ 0 := by omega
      simp [hs, ht]
  start := false
  accept := true
  Edge t _ lbl m' :=
    if ht : t = 0 then
      m' = (a ⟨0, rfl⟩ == lbl ⟨⟨1, by decide⟩, by subst ht; simp⟩)
    else False

private theorem eqSliceReadOnce_deterministic (a : ({0} : Set (Fin 2)) → Bool) :
    (eqSliceReadOnce a).Deterministic := by
  intro t ht _ lbl m₁ m₂ h₁ h₂
  have ht0 : t = 0 := by change t < 1 at ht; omega
  subst ht0
  dsimp only [eqSliceReadOnce, ↓reduceDIte] at h₁ h₂
  exact h₁.trans h₂.symm

private theorem eqSliceReadOnce_unit (a : ({0} : Set (Fin 2)) → Bool) :
    ∀ t < (eqSliceReadOnce a).length, ((eqSliceReadOnce a).newly t).ncard ≤ 1 := by
  intro t _
  refine (ncard_le_one (toFinite _)).mpr ?_
  rintro ⟨i, hi⟩ _ ⟨j, hj⟩ _
  apply Subtype.ext
  have hi0 : i ≠ 0 := by simpa using hi
  have hj0 : j ≠ 0 := by simpa using hj
  fin_cases i <;> fin_cases j <;> simp_all

private theorem eqSliceReadOnce_accepted (a : ({0} : Set (Fin 2)) → Bool) :
    (eqSliceReadOnce a).accepted = restrictSlice eqSet2 {0} a := by
  ext y
  constructor
  · rintro ⟨γ, _, hacc, hedge⟩
    have h0 := hedge 0 Nat.one_pos
    simp only [eqSliceReadOnce, ↓reduceDIte, ReadOnceNBP.newly, domRestrict] at h0 hacc
    rw [h0] at hacc
    have hay : a ⟨0, rfl⟩ = y ⟨1, by decide⟩ := beq_iff_eq.mp hacc
    change extendAssign ({0} : Set (Fin 2)) a y 0 = extendAssign ({0} : Set (Fin 2)) a y 1
    rw [extendAssign_mem (rfl : (0 : Fin 2) ∈ ({0} : Set (Fin 2))),
      extendAssign_notMem (by decide : (1 : Fin 2) ∉ ({0} : Set (Fin 2)))]
    exact hay
  · intro hy
    change extendAssign ({0} : Set (Fin 2)) a y 0 = extendAssign ({0} : Set (Fin 2)) a y 1 at hy
    rw [extendAssign_mem (rfl : (0 : Fin 2) ∈ ({0} : Set (Fin 2))),
      extendAssign_notMem (by decide : (1 : Fin 2) ∉ ({0} : Set (Fin 2)))] at hy
    refine ⟨fun t => decide (t = 1), rfl, rfl, fun t ht => ?_⟩
    have ht0 : t = 0 := by change t < 1 at ht; omega
    subst ht0
    simp only [eqSliceReadOnce, ↓reduceDIte, ReadOnceNBP.newly, domRestrict]
    simpa using beq_iff_eq.mpr hy

example : Real.logb (Nat.card Bool) eqSet2.ncard - ({0} : Set (Fin 2)).ncard -
      2 * Real.logb (Nat.card Bool) (2 : ℕ) - Real.logb (Nat.card Bool) (1 : ℕ) - 1 ≤
    Real.logb (Nat.card Bool) (Nat.card Bool) :=
  le_logb_card_of_slice_readOnce eqSet2_rectangleFree ⟨fun _ => false, rfl⟩ Nat.one_pos {0}
    fun a => ⟨eqSliceReadOnce a, rfl, eqSliceReadOnce_deterministic a,
      eqSliceReadOnce_unit a, eqSliceReadOnce_accepted a⟩

end CslibFrontierTests.FrontierWeightedKernel
