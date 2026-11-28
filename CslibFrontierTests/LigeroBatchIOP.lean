/-
Copyright (c) 2026 Mayank Rathee, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee, Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Protocols.PolynomialCommitment.LigeroBatchIOP
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Finite-field witness tests for curve-batched, Johnson-bound, and BCS Ligero proximity IOPs

Exercises `CslibFrontier.Foundations.Data.Code.InterleavedCurve` and
`CslibFrontier.Crypto.Protocols.PolynomialCommitment.LigeroBatchIOP` via ordinary `module` imports
on concrete finite-field witnesses:

1. **Joint vs. per-row Berlekamp–Welch boundary** (`berlekampWelchInterleaved` over `ZMod 11`,
   `n = 6, k = 2, e = 2`):
   * *Negative boundary witness:* a `2 × 6` word whose rows each lie at Hamming distance `2 ≤ e`
     from `0 ∈ reedSolomon` on *disjoint* column pairs (`{0, 1}` vs. `{2, 3}`, so individual row
     calls `berlekampWelch` both succeed with `some 0`) is rejected (`= none`) by
     `berlekampWelchInterleaved` because its joint column-Hamming distance is `4 > 2`.
   * *Positive witness:* corrupting a valid `2 × 6` codeword on the *shared* column pair `{0, 1}`
     is decoded (`= some P`) by `berlekampWelchInterleaved` and satisfies
     `mem_ligeroEvalProximityLang_reedSolomon_iff`.
2. **Single-scalar (`1, z, z²`) curve-batched Reed–Solomon proximity and Ligero evaluation**
   (`ZMod 29`, `m = 3, n = 8, k = 2, e = 3, q = 3`): compressing `3` row challenges to a single
   scalar `z : ZMod 29` achieves non-vacuous soundness `16 / 29 + (4 / 8) ^ 3 = 157 / 232 < 1` in
   both `ligeroCurveProximityReduction` and `ligeroBatchEvalReduction`.
3. **Strictly beyond unique decoding (`2 * e + k = 10 > 8`) in the Johnson regime**
   (`ZMod 262147`, `m = 50` rows, `n = 8, k = 2, e = 4`, `m_GS = 2, D = 7`): a `50 × 8` matrix
   whose first row `[0, 0, 0, 1, 1, 1, 2, 2]` has distance `≥ 5 > 4` from every line in
   `reedSolomon α 2` satisfies the row-count-independent Johnson proximity bound
   `156716 / 262147 < 1` in `toOuterMeasure_sum_smul_reedSolomon_close_le_johnson_exact`.
4. **Two-channel BCS/ROM batched Reed–Solomon proximity IOP** (`ZMod 17`, `d = 2, n = 4, k = 2,
   e = 1, m = 2, q = 3`): verifies `length_rsBatchProximityIOP_queries = 2`,
   `rsBatchProximityBCS_honestROMGame_eq_pure_true`, and non-vacuous two-channel ROM soundness via
   `rsCurveBatchProximityBCS_romSoundness_unique`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.LigeroBatchIOP

open Cslib Cslib.Code Cslib.Crypto.Protocols Cslib.Crypto.Protocols.BCS Cslib.Interactive
  Cslib.OracleComp Cslib.Probability
open scoped BigOperators ENNReal Matrix NNReal Polynomial

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 262147) := ⟨by norm_num⟩

private lemma far_of_rows_close_zero {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
    {α : ι → F} (hα : Function.Injective α) {e k m : ℕ}
    (hunique : 2 * e + k ≤ Fintype.card ι) {W : ι → Fin m → F}
    (hrows : ∀ r : Fin m, hammingDist (fun i => W i r) 0 ≤ e)
    (hW0 : e < hammingDist W 0) :
    ∀ V ∈ interleavedLinear (Fin m) (reedSolomon α k), e < hammingDist W V := by
  intro V hV
  by_contra hle
  have hle_e : hammingDist W V ≤ e := Nat.le_of_not_lt hle
  have hV0 : V = 0 := by
    funext i r
    have hrow : hammingDist (fun j => W j r) (fun j => V j r) ≤ e :=
      le_trans (Finset.card_le_card fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact fun hEq => hj (congrFun hEq r)) hle_e
    exact congrFun (eq_of_hammingDist_le_reedSolomon (f := fun j => W j r) hα hunique
      (mem_interleavedLinear.1 hV r) (Submodule.zero_mem _) hrow (hrows r)) i
  rw [hV0] at hle_e
  exact hW0.not_ge hle_e

/-! ### 1. Joint vs. per-row Berlekamp–Welch boundary over `ZMod 11` (`n = 6, k = 2, e = 2`) -/

def pts6_11 : Fin 6 → ZMod 11 := fun i => (i.val : ZMod 11)

lemma pts6_11_injective : Function.Injective pts6_11 := by
  decide

def disjointW_11 : Fin 6 → Fin 2 → ZMod 11 :=
  fun i r => if i.val < 2 ∧ r.val = 0 then 1
    else if (i.val = 2 ∨ i.val = 3) ∧ r.val = 1 then 1 else 0

/-- Both individual rows decode to `some 0` under `berlekampWelch`, yet `berlekampWelchInterleaved`
returns `none` because the joint column-Hamming distance is `4 > 2`. -/
theorem test_berlekampWelchInterleaved_disjoint_rows_none :
    (∀ r : Fin 2, berlekampWelch pts6_11 2 2 (fun i => disjointW_11 i r) = some 0) ∧
      berlekampWelchInterleaved pts6_11 2 2 disjointW_11 = none := by
  refine ⟨fun r => ?_, ?_⟩
  · refine berlekampWelch_eq_some pts6_11_injective (by simp) (WithBot.bot_lt_coe 2) ?_
    fin_cases r <;>
      (simp only [Polynomial.eval_zero]; decide)
  · rw [berlekampWelchInterleaved_eq_none_iff pts6_11_injective (by simp)]
    exact far_of_rows_close_zero pts6_11_injective (by simp) (by decide) (by decide)

def honestU_11 : Matrix (Fin 2) (Fin 2) (ZMod 11) := ![![1, 2], ![4, 3]]

def sharedM_11 : Matrix (Fin 2) (Fin 6) (ZMod 11) :=
  Matrix.of fun r i =>
    if i.val < 2 then 0 else (honestU_11 * reedSolomonGenerator pts6_11 2) r i

/-- Corrupting `2` shared columns preserves membership in `ligeroEvalProximityLang` and is
recovered by `berlekampWelchInterleaved` via `mem_ligeroEvalProximityLang_reedSolomon_iff`. -/
theorem test_berlekampWelchInterleaved_shared_columns_some :
    let b : Fin 2 → ZMod 11 := ![2, 5]
    let c : Fin 2 → ZMod 11 := ![3, 1]
    let w : ZMod 11 := ligeroEval honestU_11 b c
    let claim : LigeroEvalClaim (ZMod 11) 2 2 6 := ⟨sharedM_11, b, c, w⟩
    claim ∈ ligeroEvalProximityLang (reedSolomonGenerator pts6_11 2) 2 ∧
      ∃ P : Fin 2 → (ZMod 11)[X],
        berlekampWelchInterleaved pts6_11 2 2 (Function.swap sharedM_11) = some P ∧
        ligeroEval (Matrix.of fun i d => (P i).coeff (d : ℕ)) b c = w := by
  intro b c w claim
  have hmem : claim ∈ ligeroEvalProximityLang (reedSolomonGenerator pts6_11 2) 2 :=
    ⟨honestU_11, by decide, rfl⟩
  exact ⟨hmem, (mem_ligeroEvalProximityLang_reedSolomon_iff pts6_11_injective (by omega)).1 hmem⟩

/-! ### 2. Single-scalar (`1, z, z²`) 3-row curve batching over `ZMod 29` (`n = 8, k = 2, e = 3`) -/

def pts8_29 : Fin 8 → ZMod 29 := fun i => (i.val : ZMod 29)

lemma pts8_29_injective : Function.Injective pts8_29 := by
  decide

/-- Three rows with `2` errors each on disjoint column pairs `{0,1}`, `{2,3}`, `{4,5}`: each row is
within `2 ≤ 3` of `0`, while column-Hamming distance is `6 > 3`. -/
def farM3_29 : Matrix (Fin 3) (Fin 8) (ZMod 29) :=
  Matrix.of fun r i =>
    if r.val = 0 ∧ i.val < 2 then 1
    else if r.val = 1 ∧ (i.val = 2 ∨ i.val = 3) then 1
    else if r.val = 2 ∧ (i.val = 4 ∨ i.val = 5) then 1
    else 0

lemma farM3_29_not_mem :
    farM3_29 ∉ ligeroProximityLang 3 (reedSolomonGenerator pts8_29 2) 3 := by
  rintro ⟨V, hV, hle3⟩
  rw [codeOfGenerator_reedSolomonGenerator] at hV
  exact (far_of_rows_close_zero pts8_29_injective (by simp) (by decide) (by decide) V hV).not_ge
    hle3

/-- Single-scalar curve-batched proximity reduction (`m = 3, n = 8, k = 2, e = 3, q = 3`) over
`ZMod 29` has soundness error `16 / 29 + (4 / 8) ^ 3 = 157 / 232 < 1`. -/
theorem test_ligeroCurveProximityReduction_zmod29 :
    (ligeroCurveProximityReduction 3 (reedSolomonGenerator pts8_29 2) 3).Complete
        World.plain (ligeroCodewordRel 3 (reedSolomonGenerator pts8_29 2)) Accept 0 ∧
      farM3_29 ∉ ligeroProximityLang 3 (reedSolomonGenerator pts8_29 2) 3 ∧
      (∀ (α : Type) (P : ProbOracleComp OracleSpec.empty
          (ProverStrategy (ProbOracleComp OracleSpec.empty)
            (ligeroBatchProximitySpec (ZMod 29) 2 8 3 (ZMod 29)) α)),
        (World.plain.eval
            ((ligeroCurveProximityReduction 3
              (reedSolomonGenerator pts8_29 2) 3).verifier.execute farM3_29 P)).toOuterMeasure
          {r | ∃ x' ∈ (Set.univ : Set Unit), r.output = some x'} ≤ 157 / 232) ∧
      ((157 : ℝ≥0∞) / 232 < 1) := by
  have hlt1 : (157 : ℝ≥0∞) / 232 < 1 := by
    have hnn : ((157 : ℝ≥0) / 232) < 1 := by norm_num
    simpa [ENNReal.coe_div (by norm_num : (232 : ℝ≥0) ≠ 0)] using ENNReal.coe_lt_coe.2 hnn
  have hval : (((3 - 1) * 8 : ℕ) : ℝ≥0∞) / 29 + (((8 - (3 + 1) : ℕ) : ℝ≥0∞) / 8) ^ 3 =
      157 / 232 := by
    have hnn : ((16 : ℝ≥0) / 29) + ((4 : ℝ≥0) / 8) ^ 3 = 157 / 232 := by norm_num
    simpa [ENNReal.coe_add, ENNReal.coe_pow,
      ENNReal.coe_div (by norm_num : (29 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (232 : ℝ≥0) ≠ 0)] using congrArg (↑· : ℝ≥0 → ℝ≥0∞) hnn
  refine ⟨ligeroBatchProximityReduction_complete 3 (ligeroPowWeights 3)
      (reedSolomonGenerator pts8_29 2) 3, farM3_29_not_mem, fun α P => ?_, hlt1⟩
  have hs := ligeroCurveProximityReduction_reedSolomon_sound 3 (k := 2) (q := 3) (e := 3)
    pts8_29_injective (by omega) farM3_29 farM3_29_not_mem α P
  simpa only [ZMod.card, Nat.cast_ofNat, hval] using hs

/-! ### 3. Beyond unique decoding (`2 * e + k = 10 > 8`) in the Johnson regime (`m = 50` rows) -/

def pts8_big : Fin 8 → ZMod 262147 := fun i => (i.val : ZMod 262147)

lemma pts8_big_injective : Function.Injective pts8_big := by
  intro i j h
  have hi : (pts8_big i).val = i.val := ZMod.val_natCast_of_lt (by omega)
  have hj : (pts8_big j).val = j.val := ZMod.val_natCast_of_lt (by omega)
  exact Fin.ext (by rw [← hi, ← hj, h])

/-- Word `[0, 0, 0, 1, 1, 1, 2, 2]`: every constant hits at most `3` coordinates, and every
non-constant line `a X + b` hits each of `{0, 1, 2}` at most once (`≤ 3` coordinates total), so
every codeword in `reedSolomon pts8_big 2` has Hamming distance `≥ 5 > 4` from `row0_big`. -/
def row0_big : Fin 8 → ZMod 262147 :=
  fun i => if i.val < 3 then 0 else if i.val < 6 then 1 else 2

private lemma four_lt_hammingDist_row0_big {c : Fin 8 → ZMod 262147}
    (hc : c ∈ reedSolomon pts8_big 2) : 4 < hammingDist row0_big c := by
  obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hc
  have htot := card_filter_eq_add_hammingDist row0_big (fun i => p.eval (pts8_big i))
  rw [Fintype.card_fin] at htot
  suffices hle3 : (Finset.univ.filter fun i : Fin 8 => row0_big i = p.eval (pts8_big i)).card ≤ 3 by
    omega
  by_cases hp1 : p.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hp1]
    simp only [Polynomial.eval_C]
    by_cases h0 : p.coeff 0 = 0
    · rw [h0]; decide
    · by_cases h1 : p.coeff 0 = 1
      · rw [h1]; decide
      · by_cases h2 : p.coeff 0 = 2
        · rw [h2]; decide
        · have hemp : (Finset.univ.filter fun i : Fin 8 => row0_big i = p.coeff 0) = ∅ :=
            Finset.filter_eq_empty_iff.2 fun i _ => by
              dsimp only [row0_big]
              split_ifs <;> exact Ne.symm ‹_›
          simp [hemp]
  · have hp0 : p ≠ 0 := fun h => hp1 (by simp [h])
    have hdeg1 : p.natDegree ≤ 1 := by
      have hlt2 := (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hp
      omega
    let S (v : ZMod 262147) : Finset (Fin 8) :=
      Finset.univ.filter fun i => (p - Polynomial.C v).eval (pts8_big i) = 0
    have hcardS (v : ZMod 262147) : (S v).card ≤ 1 := by
      have hne : p - Polynomial.C v ≠ 0 := fun hsub => by
        have hpC : p = Polynomial.C v := sub_eq_zero.1 hsub
        exact hp1 (by simp [hpC])
      exact (card_filter_eval_eq_zero_le pts8_big_injective hne).trans
        ((Polynomial.natDegree_sub_C (p := p) (a := v)).le.trans hdeg1)
    have hsub : (Finset.univ.filter fun i : Fin 8 => row0_big i = p.eval (pts8_big i)) ⊆
        S 0 ∪ S 1 ∪ S 2 := by
      intro i hi
      have heq := (Finset.mem_filter.1 hi).2
      simp only [Finset.mem_union, S, Finset.mem_filter, Finset.mem_univ, true_and,
        Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero]
      dsimp only [row0_big] at heq
      split_ifs at heq with hlt3 hlt6
      · exact Or.inl (Or.inl heq.symm)
      · exact Or.inl (Or.inr heq.symm)
      · exact Or.inr heq.symm
    calc (Finset.univ.filter fun i : Fin 8 => row0_big i = p.eval (pts8_big i)).card
        ≤ (S 0 ∪ S 1 ∪ S 2).card := Finset.card_le_card hsub
      _ ≤ (S 0 ∪ S 1).card + (S 2).card := Finset.card_union_le _ _
      _ ≤ (S 0).card + (S 1).card + (S 2).card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ 1 + 1 + 1 := Nat.add_le_add (Nat.add_le_add (hcardS 0) (hcardS 1)) (hcardS 2)
      _ = 3 := rfl

/-- `50 × 8` matrix placing `row0_big` in row `0` and `0` elsewhere. -/
def farM50_johnson : Matrix (Fin 50) (Fin 8) (ZMod 262147) :=
  Matrix.of fun r i => if r.val = 0 then row0_big i else 0

lemma farM50_johnson_far :
    ∀ V ∈ interleavedLinear (Fin 50) (reedSolomon pts8_big 2),
      4 < hammingDist (Function.swap farM50_johnson) V := by
  intro V hV
  refine (four_lt_hammingDist_row0_big (mem_interleavedLinear.1 hV 0)).trans_le ?_
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  intro hEq
  exact hi (by simpa [Function.swap, farM50_johnson] using congrFun hEq (0 : Fin 50))

/-- **Strictly beyond unique decoding (`2 * 4 + 2 = 10 > 8`)** with `m = 50` interleaved rows:
`toOuterMeasure_sum_smul_reedSolomon_close_le_johnson_exact` (`m_GS = 2, D = 7`) bounds the
uniform `50`-row combination probability by `156716 / 262147 < 1`, independent of `m = 50`. -/
theorem test_johnson_beyond_unique_decoding_50_rows :
    2 * 4 + 2 > 8 ∧
      (PMF.uniformOfFintype (Fin 50 → ZMod 262147)).toOuterMeasure
          {z | ∃ c ∈ reedSolomon pts8_big 2,
            hammingDist (fun i => ∑ r : Fin 50, z r • Function.swap farM50_johnson i r) c ≤ 4} ≤
        156716 / 262147 ∧
      ((156716 : ℝ≥0∞) / 262147 < 1) := by
  have hjb : ProximityGap.johnsonCurveBound 8 2 1 7 1 8 = 156716 := by decide
  have hinterp : 8 * (2 * (2 + 1) / 2) < (Sudan.monomials (2 - 1) 7).card := by decide
  have hlt1 : (156716 : ℝ≥0∞) / 262147 < 1 := by
    have hnn : ((156716 : ℝ≥0) / 262147) < 1 := by norm_num
    simpa [ENNReal.coe_div (by norm_num : (262147 : ℝ≥0) ≠ 0)] using ENNReal.coe_lt_coe.2 hnn
  refine ⟨by omega, ?_, hlt1⟩
  have hb := toOuterMeasure_sum_smul_reedSolomon_close_le_johnson_exact pts8_big_injective
    (k := 2) (m := 50) (e := 4) (m_GS := 2) (D := 7)
    (by omega) (by omega) (by simp) (by simpa using hinterp) (by simp) farM50_johnson_far
  simpa only [Fintype.card_fin, ZMod.card, hjb, Nat.cast_ofNat] using hb

/-! ### 4. Two-channel BCS/ROM batched Reed–Solomon proximity IOP (`d = 2, n = 4, k = 2, e = 1`) -/

def pts4_17 : Fin (2 ^ 2) → ZMod 17 := fun i => (i.val : ZMod 17)

lemma pts4_17_injective : Function.Injective pts4_17 := by
  decide

def encZMod17 (x : ZMod 17) : List Bool :=
  List.replicate x.val true

def decZMod17 (bs : List Bool) : ZMod 17 :=
  (bs.length : ZMod 17)

lemma leftInverse_decZMod17 : Function.LeftInverse decZMod17 encZMod17 := by
  decide

def farM2_4_17 : Matrix (Fin 2) (Fin (2 ^ 2)) (ZMod 17) :=
  Matrix.of fun r i =>
    if r.val = 0 ∧ i.val = 0 then 1 else if r.val = 1 ∧ i.val = 1 then 1 else 0

theorem test_rsCurveBatchProximityBCS_zmod17 :
    let hk : 2 ≤ 2 ^ 2 := by omega
    let U : Matrix (Fin 2) (Fin 2) (ZMod 17) := ![![3, 5], ![2, 7]]
    let M : Matrix (Fin 2) (Fin (2 ^ 2)) (ZMod 17) := U * reedSolomonGenerator pts4_17 2
    let dummyPrf : BCSProof 2 (ZMod 17) := ⟨fun _ => [], []⟩
    let P_cheat : OracleComp
        (BCSROMSpec (Matrix (Fin 2) (Fin (2 ^ 2)) (ZMod 17)) (LigeroIOPChal (ZMod 17) 2 3))
        (Matrix (Fin 2) (Fin (2 ^ 2)) (ZMod 17) × BCSProof 2 (ZMod 17)) :=
      pure (farM2_4_17, dummyPrf)
    (∀ chals, ((rsCurveBatchProximityIOP 2 hk pts4_17 3).queries M chals).length = 2) ∧
      bcsHonestROMGame (rsCurveBatchProximityIOP 2 hk pts4_17 3) encZMod17 M U 128 =
        PMF.pure true ∧
      bcsSoundnessGame (rsCurveBatchProximityIOP 2 hk pts4_17 3) encZMod17
          (ligeroProximityLang 2 (reedSolomonGenerator pts4_17 2) 1) P_cheat 128 true ≤
        2 * (max (4 / 17) ((2 / 4) ^ 3) + 2 * (1 / (17 * 64 : ℕ))) := by
  intro hk U M dummyPrf P_cheat
  refine ⟨fun chals => length_rsBatchProximityIOP_queries 2 hk pts4_17 3 (ligeroPowWeights 2) M
      chals,
    rsBatchProximityBCS_honestROMGame_eq_pure_true 2 hk pts4_17 3 (ligeroPowWeights 2) encZMod17
      rfl 128, ?_⟩
  have hMT : IsCostBounded bcsMTCost P_cheat 0 := IsCostBounded.pure _ 0
  have hFS : IsCostBounded bcsFSCost P_cheat 0 := IsCostBounded.pure _ 0
  have hV : ∀ M' prf, (M', prf) ∈ P_cheat.support →
      IsCostBounded bcsMTCost
        (bcsVerifyROM (rsCurveBatchProximityIOP 2 hk pts4_17 3) encZMod17 M' prf) 0 := by
    intro M' prf hsupp
    change (M', prf) = (farM2_4_17, dummyPrf) at hsupp
    rcases Prod.mk.inj hsupp with ⟨_, rfl⟩
    exact isCostBounded_bcsMTCost_bcsVerifyROM _ encZMod17 M' dummyPrf
  have hb := rsCurveBatchProximityBCS_romSoundness_unique 2 (q := 3) (e := 1) hk pts4_17_injective
    (by omega) leftInverse_decZMod17 0 128 hMT hFS hV
  have hcard : Fintype.card (ZMod 17) = 17 := ZMod.card 17
  rw [hcard] at hb
  norm_num at hb ⊢
  exact hb

end CslibFrontierTests.LigeroBatchIOP
