/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.Integrated
public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.ClippedTail

/-!
# Uniform actual-output moments from endpoint prefix budgets

`actualNoiseEntry` is relative first-channel noise on full terminal rank and absolute
second-channel noise on usage. `actualNoiseMax_budget` derives its row-maximum moment from
an endpoint row moment. `raw_prefix_row_budget` combines the two clipped mean and two noise
budgets, preserving actual second-channel zero extension. `uniform_moment_capacity` then
assembles final error, preloss, actual heavy tails and false-event charges for any capacity
sequence above the dyadic lower bound (and the hierarchy rank).

This conditional fourth-moment adaptation of §8.2, Proposition 8.5 (printed pp. 45–49), of
[OpenAI2026LogSpace], revision 7ef5c0cc, does not derive the lower-child input budgets or
recursive reserve choices. The H4 specialization is Christian Reitwiessner's; compression
and norm proof patterns are adapted from Samuel Schlesinger.
-/

public section
open Matrix.FourthRootHierarchyParams Matrix.HierarchyParams.H4RankEnvironment

namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Matrix Cslib.RowCompression Cslib.Probability
open scoped BigOperators

variable {P J : ℕ} [Fact P.Prime]
open Classical in
/-- Scope-correct row-noise input: relative first coordinate on full rank, absolute second
on usage. These are prefix noise moments, never compressed-output assumptions. -/
@[expose] noncomputable def actualNoiseEntry
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (ν : Fin 2) (i : ℕ) (σ : Environment P J) (x y : ZMod P) : ℝ :=
  |actualPrefix Δ raw i σ x y ν - twoMaskMean s t Ls La Lt D sourceSuffix suffix (actualPrefix Δ
    raw i) x y ν| /
    (if ν = 0 then 1 + G x y / rate k else 1)

open Classical in
lemma actualNoiseMax_budget
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    {N u e : ℝ} (hNu : 0 ≤ N * u) (ν : Fin 2) (i : ℕ)
    (hb : rowNormPow 4 N u (retainedMask s Ls D sourceSuffix)
      (retainedMask t (if ν = 0 then La else Lt) D suffix)
      (actualNoiseEntry s t Ls La Lt D sourceSuffix suffix k G Δ raw ν i) ≤ e ^ 4) :
    vertexNormPow 4 N u (retainedMask s Ls D sourceSuffix)
      (actualNoiseMax s t Ls La Lt D sourceSuffix suffix k G Δ raw ν i) ≤ e ^ 4 := by
  have hnonneg (σ : Environment P J) (x y : ZMod P) :
      0 ≤ actualNoiseEntry s t Ls La Lt D sourceSuffix suffix k G Δ raw ν i σ x y :=
    div_nonneg (abs_nonneg _) (by split_ifs <;> linarith [div_nonneg (hG x y) (rate_pos k).le])
  have hh := (vertex_row_max (retainedMask s Ls D sourceSuffix)
    (retainedMask t (if ν = 0 then La else Lt) D suffix) hNu
    (actualNoiseEntry s t Ls La Lt D sourceSuffix suffix k G Δ raw ν i)).trans hb
  simp only [abs_of_nonneg (hnonneg _ _ _)] at hh
  unfold actualNoiseMax
  simpa only [actualNoiseEntry] using hh
end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Matrix Cslib.RowCompression Cslib.Probability
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]
open Classical in
/-- The two-scope clipped mean/noise inputs give the full-rank raw-prefix moment.
Second-coordinate inputs are charged only on usage, by actual zero extension. -/
theorem raw_prefix_row_budget
    (HP : Matrix.FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (ζ : ℝ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (m i : ℕ)
    (hz : ∀ σ x y, ¬retainedMask t Lt D suffix σ y → actualPrefix Δ raw i σ x y 1 = 0)
    (hsub : ∀ σ y, retainedMask t Lt D suffix σ y → retainedMask t La D suffix σ y)
    {N u e : ℝ} (hNu : 0 ≤ N * u) (he : 0 ≤ e)
    (hmean : ∀ ν, rowNormPow 4 N u (retainedMask s Ls D sourceSuffix)
      (retainedMask t (if ν = 0 then La else Lt) D suffix)
      (fun _ x y => actualClippedMean HP s t Ls La Lt D sourceSuffix suffix k G ζ Δ raw ν i x y) ≤
      (e * 2 ^ dyadicSlack m i) ^ 4)
    (hnoise : ∀ ν, rowNormPow 4 N u (retainedMask s Ls D sourceSuffix)
      (retainedMask t (if ν = 0 then La else Lt) D suffix)
      (actualNoiseEntry s t Ls La Lt D sourceSuffix suffix k G Δ raw ν i) ≤
      (e * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4) :
    rowNormPow 4 N u (retainedMask s Ls D sourceSuffix) (retainedMask t La D suffix)
      (fun σ x y => clippedError (G x y / rate k)
        (genuineTarget HP s t Ls Lt D sourceSuffix suffix k G ζ σ x y 1)
        (actualPrefix Δ raw i σ x y)) ≤ (4 * e * 2 ^ dyadicSlack m i) ^ 4 := by
  let X := retainedMask s Ls D sourceSuffix
  let Ya := retainedMask t La D suffix
  let Yt := retainedMask t Lt D suffix
  let μ := fun ν (σ : Environment P J) x y =>
    if ν = 0 then actualClippedMean HP s t Ls La Lt D sourceSuffix suffix k G ζ Δ raw ν i x y
    else if Yt σ y then actualClippedMean HP s t Ls La Lt D sourceSuffix suffix k G ζ Δ raw ν i x
      y else 0
  let z := fun ν σ x y => if ν = 0 then actualNoiseEntry s t Ls La Lt D sourceSuffix suffix k G Δ
    raw ν i σ x y
    else if Yt σ y then actualNoiseEntry s t Ls La Lt D sourceSuffix suffix k G Δ raw ν i σ x y
      else 0
  have hm (ν : Fin 2) : rowNormPow 4 N u X Ya (μ ν) ≤ (e * 2 ^ dyadicSlack m i) ^ 4 := by
    fin_cases ν
    · simpa [μ] using hmean 0
    · simpa only [μ, Fin.reduceFinMk, Fin.isValue, one_ne_zero, ↓reduceIte, row_mask_subset X Ya Yt
        hsub] using hmean 1
  have hz' (ν : Fin 2) : rowNormPow 4 N u X Ya (z ν) ≤ (e * 2 ^ dyadicSlack m i) ^ 4 := by
    refine le_trans ?_ (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 64 : ℝ) ≤ 2) _) he) 4)
    fin_cases ν
    · simpa [z] using hnoise 0
    · simpa only [z, Fin.reduceFinMk, Fin.isValue, one_ne_zero, ↓reduceIte,
        row_mask_subset X Ya Yt hsub] using hnoise 1
  have hsum := row_add_budget X Ya hNu (by positivity) (by positivity) _ _
    (row_add_budget X Ya hNu (by positivity) (by positivity) _ _ (hm 0) (hm 1))
    (row_add_budget X Ya hNu (by positivity) (by positivity) _ _ (hz' 0) (hz' 1))
  refine (row_mono_abs X Ya hNu _
    (fun σ x y => (μ 0 σ x y + μ 1 σ x y) + (z 0 σ x y + z 1 σ x y)) fun σ x y _ _ => ?_).trans
    (hsum.trans_eq (by ring))
  rw [abs_of_nonneg (clippedError_nonneg _ _ _)]
  refine (actual_two_mask_clipped_split HP s t Ls La Lt D sourceSuffix suffix k G hG ζ
    (actualPrefix Δ raw i) hz σ x y).trans ((le_of_eq ?_).trans (le_abs_self _))
  simp only [μ, z, actualClippedMean, actualNoiseEntry, Fin.isValue, ↓reduceIte,
    one_ne_zero, div_one]
  ring
end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
namespace Matrix.FourthRootHierarchyParams.NormalizedRow
open Finset Cslib Matrix Cslib.RowCompression Cslib.Probability
  Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
variable (HP : FourthRootHierarchyParams 16 1 16 32 8) (ζ : ℝ) (hζ : 0 < ζ)
include hζ
open Classical in
/-- Uniform assembly with raw-prefix input moments, not final-output certificates.
C is fixed before η, and A after η. The full-rank error is stronger than usage error. -/
theorem uniform_moment_capacity {scale : ℝ} (hs : 0 < scale) (hmargin : scale ≤ HP.η) (hcapscale :
  scale ≤ HP.toHierarchyParams.atomCap / 10000) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ scale → η ≤ 1 →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω V : Type*} [Fintype Ω] [Fintype V]
      (N u : ℝ) ( _hNu : 0 ≤ N * u) (X Y : Ω → V → Prop)
      (m : ℕ) ( _hm : 0 < m) (n : ℕ → ℕ)
      (_hnscale : ∀ i < m, 2 ^ (64 * dyadicSlack m i) ≤ n i)
      (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (raw truth : Ω → V → V → Fin 2 → ℝ),
      let S := fun σ => ({y | Y σ y} : Finset V)
      let e := fun i σ x => kthLargest 1 (S σ) (fun y =>
        clippedError (truth σ x y 0) (truth σ x y 1) (uncompressedRow (Δ σ x) (raw σ x) (i + 1) y))
      (∀ i < m, HP.K ≤ n i) →
      (∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0) →
      (∀ σ x y, X σ x → Y σ y → |truth σ x y 1| ≤ scale / 2) →
      (∀ j < m, ∀ σ x y, X σ x → Y σ y → truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 =
        0) →
      ∀ ε T : ℝ, 0 ≤ ε → 0 ≤ T →
      (∀ i < m, rowNormPow 4 N u X Y (fun σ x y =>
        clippedError (truth σ x y 0) (truth σ x y 1) (uncompressedRow (Δ σ x) (raw σ x) (i + 1)
          y)) ≤
        (ε * 2 ^ dyadicSlack m i) ^ 4) →
      (vertexNormPow 4 N u X (fun σ x => ∑ j ∈ range m,
        if IsFirstOverflow (S σ) n (fun _ => HP.K) (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ j ∧
          heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ then
          ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * e i σ x else 0) ≤ (T * ε) ^ 4) →
      rowNormPow 4 N u X Y (fun σ x y => stateRootError (output HP ζ) (S σ) HP.K
        (iterate (S σ) n (fun _ => HP.K) (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ m)
        ⟨0, truth σ x⟩ y) ≤
      (128 * (HP.K : ℝ) * (A ^ 4 * (η / 511) ^ 4 + C ^ 4 * 2 ^ 4 + C ^ 4 * T ^ 4) + 64 * (HP.K :
        ℝ) *
        (rangeBound HP) ^ 4 / η ^ 4 / 63) * ε ^ 4 := by
  obtain ⟨C, hC, hscale⟩ := exists_compression_rowNormPow_le HP ζ hζ hs hmargin hcapscale
  refine ⟨C, hC, fun η hη hηs hη1 => ?_⟩
  obtain ⟨A, hA, hbound⟩ := hscale η hη hηs hη1
  refine ⟨A, hA, ?_⟩
  intro Ω V _ _ N u hNu X Y m hm n hnscale Δ raw truth S e hn hfirst hsecond hzero ε T hε hT hrow
    htail
  have he (i : ℕ) : vertexNormPow 4 N u X (e i) ≤ rowNormPow 4 N u X Y
      (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1) (uncompressedRow (Δ σ x) (raw σ
        x) (i + 1) y)) := by
    simpa only [abs_of_nonneg (clippedError_nonneg _ _ _)] using vertex_row_max X Y hNu
      (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
        (uncompressedRow (Δ σ x) (raw σ x) (i + 1) y))
  have herr (i : ℕ) (σ : Ω) (x y : V) (hy : Y σ y) :
      clippedError (truth σ x y 0) (truth σ x y 1) (uncompressedRow (Δ σ x) (raw σ x) (i + 1) y) ≤
        e i σ x := by
    simpa only [abs_of_nonneg (clippedError_nonneg _ _ _)] using abs_le_kthLargest_one (S σ)
      (fun y => clippedError (truth σ x y 0) (truth σ x y 1)
        (uncompressedRow (Δ σ x) (raw σ x) (i + 1) y)) y (mem_filter.mpr ⟨mem_univ _, hy⟩)
  have hb := hbound N u hNu X Y n m hn Δ raw truth hfirst hsecond hzero e (e (m - 1))
    (fun _ _ _ _ _ => kthLargest_nonneg) (fun _ _ _ => kthLargest_nonneg)
    (fun i _ σ x y _ hy => herr i σ x y hy)
    (fun σ x y _ hy => by simpa only [Nat.sub_add_cancel hm] using herr (m - 1) σ x y hy)
  dsimp only at hb
  have hp' := (vertexNormPow_sum_le_pow_sum (X := X) (by decide : 4 ≠ 0) hNu (range m) e
    (dyadicFloor η m) (fun i => ε * 2 ^ dyadicSlack m i) (fun _ _ => by positivity)
    (fun _ _ => by positivity) (fun i hi => (he i).trans (hrow i (mem_range.mp hi)))).trans
    (pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) (pre_schedule_sum hη.le hε m) 4)
  have hf : vertexNormPow 4 N u X (fun σ x => if ∀ i < m,
      stepThreshold (S σ) n (fun _ => HP.K) (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ i ≤ dyadicFloor
        η m i
      then e (m - 1) σ x else 0) ≤ (2 * ε) ^ 4 := by
    refine (vertex_mono_nonneg X hNu _ _
      (fun _ _ => by split_ifs <;> first | exact kthLargest_nonneg | exact le_rfl)
      (fun _ _ => by split_ifs <;> first | exact le_rfl | exact kthLargest_nonneg)).trans ?_
    have hd : dyadicSlack m (m - 1) = 1 := by simp [dyadicSlack, Nat.sub_add_cancel hm]
    simpa only [hd, pow_one, mul_comm] using (he (m - 1)).trans (hrow (m - 1) (by omega))
  have hcharge' := (sum_le_sum (s := range m) fun i hi =>
    mul_le_mul_of_nonneg_left (hrow i (mem_range.mp hi))
      (by positivity : 0 ≤ 64 * (HP.K : ℝ) * (rangeBound HP) ^ 4 /
        ((n i : ℝ) * dyadicFloor η m i ^ 4))).trans
    (false_schedule_sum_capacity (ε := ε) (R := rangeBound HP) hη (Nat.cast_nonneg HP.K) m n
      hnscale)
  calc
    _ ≤ 128 * (HP.K : ℝ) * (A ^ 4 * (η * ε / 511) ^ 4 + C ^ 4 * (2 * ε) ^ 4 + C ^ 4 * (T * ε) ^ 4)
 +
        64 * (HP.K : ℝ) * (rangeBound HP) ^ 4 / η ^ 4 * ε ^ 4 / 63 :=
      hb.trans (add_le_add (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hp' (by positivity))
          (mul_le_mul_of_nonneg_left hf (by positivity)))
          (mul_le_mul_of_nonneg_left htail (by positivity))) (by positivity)) hcharge')
    _ = _ := by ring
end Matrix.FourthRootHierarchyParams.NormalizedRow
