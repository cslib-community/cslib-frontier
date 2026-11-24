/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Computability.Circuit.Frontier.SumsetBridge
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.SumsetCorrelationBreaker
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.SumsetExtractor
public import CslibFrontier.Probability.MinEntropy.ChainRule
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.ProductConditioning
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Checked `module` clients for Work Package 1 of #7793:
* `CslibFrontier.Probability.MinEntropy.ChainRule`
* `CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.SumsetExtractor`
* `CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.SumsetCorrelationBreaker`

Exercises concrete non-vacuous witnesses, negative boundary checks, `SumsetBridge` integration,
and clean standard-axiom dependencies (`propext`, `Classical.choice`, `Quot.sound`). -/

@[expose] public section

namespace CslibFrontierTests.LiSumsetExtractor

open Cslib Cslib.BitString Cslib.AffineDisperser.Li Cslib.Circuits.Frontier
open Cslib.Probability Cslib.Probability.PMF

/-! ### 1. Min-entropy chain rule and uniform-lifting witnesses -/

/-- Conditioning a uniform pair `(Bool × Bool)` on the first coordinate being `true` retains
min-entropy at least `0` via `minEntropy_map_conditionalSnd_ge_of_apply_ge`. -/
example :
    (0 : ℝ) ≤ minEntropy
      ((conditionalSnd (PMF.uniformOfFintype (Bool × Bool)) true).map id) := by
  have hsnd : (1 : ℝ) ≤
      minEntropy (((PMF.uniformOfFintype (Bool × Bool)).map Prod.snd).map id) := by
    rw [PMF.map_id, uniformOfFintype_prod_map_snd, minEntropy_uniformOfFintype, Fintype.card_bool]
    norm_num
  have hfst : (1 : ℝ) / Fintype.card Bool ≤
      (((PMF.uniformOfFintype (Bool × Bool)).map Prod.fst) true).toReal := by
    rw [uniformOfFintype_prod_map_fst, PMF.uniformOfFintype_apply, Fintype.card_bool]
    norm_num
  have h := minEntropy_map_conditionalSnd_ge_of_apply_ge
    (PMF.uniformOfFintype (Bool × Bool)) id (k := 1) (δ := 1) one_pos hsnd hfst
  have hcard : (Fintype.card Bool : ℝ) = 2 := by norm_num
  rw [hcard, Real.logb_self_eq_one (by norm_num), inv_one, Real.logb_one] at h
  linarith

/-- Non-vacuous uniform-lifting witness: lifting a uniform `BitString 2` distribution along
first-bit projection at `γ = 1 / 2` yields a nearby distribution with min-entropy at least `0`. -/
example :
    ∃ A' : PMF (BitString 2),
      dist (PMF.uniformOfFintype (BitString 2)) A' ≤ 1 / 2 ∧
      (0 : ℝ) ≤ minEntropy (A'.map fun x => x 0) := by
  have hunif : (PMF.uniformOfFintype (BitString 2)).map (fun x => x 0) =
      PMF.uniformOfFintype Bool := by
    rw [← pi_uniformOfFintype (α := fun _ : Fin 2 => Bool), pi_map_eval]
  obtain ⟨A', hdist, hmin⟩ := exists_dist_le_and_le_minEntropy_map_of_dist_uniform
    (PMF.uniformOfFintype (BitString 2)) (fun x => x 0) (γ := 1 / 2) (by norm_num)
    (by rw [hunif, dist_self]; norm_num)
  refine ⟨A', hdist, ?_⟩
  have hcard : (Fintype.card Bool : ℝ) = 2 := by norm_num
  have hsub : (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ := by norm_num
  rw [hcard, hsub, Real.logb_inv, Real.logb_self_eq_one (by norm_num)] at hmin
  linarith

/-! ### 2. Explicit high-entropy sumset extractor (`splitDotProduct`) and boundaries -/

/-- Even-length concrete witness: `splitDotProduct 4` is an unconditional `(3, 3, 1 / 4)` sumset
extractor on `BitString 4`. -/
theorem isSumsetExtractor_splitDotProduct_four :
    IsSumsetExtractor (fun x : BitString 4 => fun _ : Fin 1 => splitDotProduct 4 x)
      3 3 (1 / 4) := by
  have h := isSumsetExtractor_splitDotProduct 4 3 3
  refine h.mono le_rfl le_rfl (le_of_eq ?_)
  have hexp : (((4 + 4 % 2 : ℕ) : ℝ) - (3 : ℕ) - (3 : ℕ)) / 2 = -1 := by norm_num
  rw [hexp, Real.rpow_neg_one]
  norm_num

/-- Direct `SumsetBridge` integration: `splitDotProduct 4` immediately gives `(8, 1 / 4)`
rectangle bias on `BitString 4`. -/
example : RectangleBias {x : BitString 4 | splitDotProduct 4 x = true} 8 (1 / 4) := by
  simpa using rectangleBias_of_isSumsetExtractor isSumsetExtractor_splitDotProduct_four 0 true

/-- Odd-length boundary witness: `splitDotProduct 5` (exercising the `n % 2 = 1` branch) is an
unconditional `(4, 4, 1 / 4)` sumset extractor on `BitString 5`. -/
theorem isSumsetExtractor_splitDotProduct_five :
    IsSumsetExtractor (fun x : BitString 5 => fun _ : Fin 1 => splitDotProduct 5 x)
      4 4 (1 / 4) := by
  have h := isSumsetExtractor_splitDotProduct 5 4 4
  refine h.mono le_rfl le_rfl (le_of_eq ?_)
  have hexp : (((5 + 5 % 2 : ℕ) : ℝ) - (4 : ℕ) - (4 : ℕ)) / 2 = -1 := by norm_num
  rw [hexp, Real.rpow_neg_one]
  norm_num

/-- Negative boundary (exactness of the `k₁ + k₂ > n` threshold): `splitDotProduct 4` is NOT a
`(2, 2, 1 / 4)` sumset extractor. -/
example :
    ¬ IsSumsetExtractor (fun x : BitString 4 => fun _ : Fin 1 => splitDotProduct 4 x) 2 2 (1 / 4) :=
  not_isSumsetExtractor_splitDotProduct_half 2 (by norm_num)

/-- Negative boundary: a constant map is not a `(3, 3, 1 / 4)` sumset extractor on `BitString 4`. -/
example :
    ¬ IsSumsetExtractor (fun _ : BitString 4 => fun _ : Fin 1 => false) 3 3 (1 / 4) := by
  intro hext
  have hu : (3 : ℝ) ≤ minEntropy (PMF.uniformOfFintype (BitString 4)) := by
    rw [minEntropy_uniformOfFintype, BitString.logb_card]
    norm_num
  have hdist := hext (PMF.uniformOfFintype (BitString 4)) (PMF.uniformOfFintype (BitString 4)) hu hu
  have hconst : (((PMF.uniformOfFintype (BitString 4)).bind fun a =>
      (PMF.uniformOfFintype (BitString 4)).map fun b => a + b).map
      (Function.const (BitString 4) (fun _ : Fin 1 => false))) =
      PMF.pure (fun _ : Fin 1 => false) := PMF.map_const ..
  change dist (((PMF.uniformOfFintype (BitString 4)).bind fun a =>
      (PMF.uniformOfFintype (BitString 4)).map fun b => a + b).map
      (Function.const (BitString 4) (fun _ : Fin 1 => false))) _ ≤ 1 / 4 at hdist
  rw [hconst] at hdist
  let e : BitString 1 ≃ Bool := Equiv.funUnique (Fin 1) Bool
  have h1 := dist_map_le (PMF.pure (fun _ : Fin 1 => false))
    (PMF.uniformOfFintype (BitString 1)) e
  have hpure_map : (PMF.pure (fun _ : Fin 1 => false)).map e = PMF.pure false := by
    simp [PMF.map, e]
  rw [hpure_map, PMF.uniformOfFintype_map_equiv e, dist_uniformOfFintype_bool] at h1
  have hfalse : ((PMF.pure false) true).toReal = 0 := by simp [PMF.pure_apply]
  rw [hfalse] at h1
  norm_num at h1
  linarith

/-- Sumset-to-two-source bridge witness: `splitDotProduct 2` on `BitString (1 + 1)` yields a
non-vacuous `(1, 1, 1 / 2)` two-source extractor via `Fin.append`. -/
example :
    IsTwoSourceExtractor
      (fun (x y : BitString 1) => fun _ : Fin 1 => splitDotProduct (1 + 1) (Fin.append x y))
      1 1 (1 / 2) := by
  have h := isSumsetExtractor_splitDotProduct 2 1 1
  have h' : IsSumsetExtractor (fun x : BitString (1 + 1) => fun _ : Fin 1 => splitDotProduct 2 x)
      1 1 (1 / 2) := by
    refine h.mono le_rfl le_rfl (le_of_eq ?_)
    have hexp : (((2 + 2 % 2 : ℕ) : ℝ) - (1 : ℕ) - (1 : ℕ)) / 2 = 0 := by norm_num
    rw [hexp, Real.rpow_zero]
  simpa using isTwoSourceExtractor_append_of_isSumsetExtractor h'

/-- Shift invariance and symmetry closure witness on `splitDotProduct 4`. -/
example (c : BitString 4) :
    IsSumsetExtractor (fun x : BitString 4 => fun _ : Fin 1 => splitDotProduct 4 (x + c))
      3 3 (1 / 4) :=
  (isSumsetExtractor_splitDotProduct_four.comp_add_right c).symm

/-! ### 3. Linear strong extractors and arbitrary-`t` weak-seed correlation breakers -/

/-- Unconditional concrete `IsLinearStrongExtractor` witness via `BitString.LinearHash` on
`n = 12`, `m = 4`, `k = 10`, error `1 / 16`. -/
theorem isLinearStrongExtractor_linearHash_12_4 :
    IsLinearStrongExtractor
      (fun (x : BitString 12) (rows : Fin 4 → BitString 12) => LinearHash.hash rows x)
      10 (1 / 16) := by
  have h := isLinearStrongExtractor_linearHash 12 4 (δ := 1 / 8) (by norm_num) (k := 10) (by
    have hlog : Real.logb 2 ((1 / 8 : ℝ)⁻¹) = 3 := by
      rw [show (1 / 8 : ℝ)⁻¹ = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [hlog]
    norm_num)
  norm_num at h
  exact h

/-- Negative boundary: a quadratic (nonlinear) map fails `IsLinearStrongExtractor`. -/
example :
    ¬ IsLinearStrongExtractor
      (fun (x : BitString 2) (_ : Unit) => fun _ : Fin 1 => x 0 && x 1) 1 1 := by
  rintro ⟨_, hlin⟩
  have h := congrFun (hlin () ![true, false] ![false, true]) 0
  revert h
  decide

/-- Unconditional `t = 0` `IsLinearWeakSeedCB` witness on `BitString 4`. -/
theorem isLinearWeakSeedCB_dotProduct_four :
    IsLinearWeakSeedCB (fun (b y : BitString 4) (_ : Unit) => b ⬝ᵥ y) 3 3 0 (1 / 4) := by
  have h := isLinearWeakSeedCB_dotProduct (n := 4) (Advice := Unit) 3 3
  have hexp : (((4 : ℕ) : ℝ) - 3 - 3) / 2 = -1 := by norm_num
  rw [hexp, Real.rpow_neg_one] at h
  norm_num at h
  exact h

/-- Unconditional `t = 2` (3-wise) `IsLinearWeakSeedCB` witness via `blockDotCB 3 20` on
`BitString 60` (`kSrc = 59 < 60`, `kSeed = 18 < 20`, error `33 / 256 < 1 / 2`). -/
theorem isLinearWeakSeedCB_blockDot_3_20 :
    IsLinearWeakSeedCB (blockDotCB 3 20) 59 18 2 (33 / 256) := by
  have h := isLinearWeakSeedCB_blockDot (D := 3) (ℓ := 20) (by omega) 2
    (kSrc := 59) (kSeed := 18) (δ := 1 / 8) (by norm_num)
  have hlog : Real.logb 2 ((1 / 8 : ℝ)⁻¹) = 3 := by
    rw [show (1 / 8 : ℝ)⁻¹ = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hval : (1 / 8 : ℝ) +
      (2 : ℝ) ^ ((((3 * 20 : ℕ) : ℝ) - 59 - 18 + Real.logb 2 ((1 / 8 : ℝ)⁻¹)) / 2) / 2 =
      33 / 256 := by
    rw [hlog]
    have hexp : ((((3 * 20 : ℕ) : ℝ) - 59 - 18 + 3) / 2) = -(7 : ℕ) := by norm_num
    rw [hexp, Real.rpow_neg zero_le_two, Real.rpow_natCast]
    norm_num
  rwa [hval] at h

/-! ### 4. End-to-end non-vacuous reduction client -/

/-- Prefix projection `BitString (2 ^ m) → Fin 1 → BitString m`. -/
private def prefixExt (m : ℕ) (x : BitString (2 ^ m)) (_ : Fin 1) : BitString m :=
  fun i => x ⟨i.1, lt_of_lt_of_le i.2 (Nat.le_of_lt Nat.lt_two_pow_self)⟩

private theorem isLinearStrongExtractor_prefixExt (m : ℕ) :
    IsLinearStrongExtractor (prefixExt m) (2 ^ m : ℕ) 0 := by
  refine ⟨fun A hA => ?_, fun _ _ _ => rfl⟩
  have hA_unif : A = PMF.uniformOfFintype (BitString (2 ^ m)) := by
    have hle : ∀ x : BitString (2 ^ m),
        (A x).toReal ≤ (Fintype.card (BitString (2 ^ m)) : ℝ)⁻¹ := fun x => by
      have h := (le_minEntropy_iff A).mp hA x
      rw [Real.rpow_neg zero_le_two, Real.rpow_natCast] at h
      simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using h
    have hsum : ∑ x : BitString (2 ^ m), (A x).toReal =
        ∑ _x : BitString (2 ^ m), (Fintype.card (BitString (2 ^ m)) : ℝ)⁻¹ := by
      rw [PMF.sum_toReal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_inv_cancel₀ (by positivity)]
    have heq : ∀ x : BitString (2 ^ m),
        (A x).toReal = ((PMF.uniformOfFintype (BitString (2 ^ m))) x).toReal := fun x => by
      have := (Finset.sum_eq_sum_iff_of_le fun y _ => hle y).mp hsum x (Finset.mem_univ x)
      simpa [PMF.uniformOfFintype_apply] using this
    ext x
    exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top A x) (PMF.apply_ne_top _ x)).mp (heq x)
  rw [hA_unif]
  let emb : Fin m ↪ Fin (2 ^ m) :=
    ⟨fun i => ⟨i.1, lt_of_lt_of_le i.2 (Nat.le_of_lt Nat.lt_two_pow_self)⟩,
      fun _ _ h => Fin.ext (Fin.mk.inj h)⟩
  have hmap : (PMF.uniformOfFintype (BitString (2 ^ m))).map (fun a => prefixExt m a 0) =
      PMF.uniformOfFintype (BitString m) :=
    uniformOfFintype_pi_map_comp_embedding emb
  have hpair :
      ((PMF.uniformOfFintype (BitString (2 ^ m))).bind fun a =>
        (PMF.uniformOfFintype (Fin 1)).map fun s => (s, prefixExt m a s)) =
      PMF.uniformOfFintype (Fin 1 × BitString m) := by
    rw [← uniformOfFintype_prod]
    simp only [PMF.map, Function.comp_def]
    rw [PMF.bind_comm]
    refine congrArg ((PMF.uniformOfFintype (Fin 1)).bind ·) (funext fun s => ?_)
    have hs0 : s = 0 := Subsingleton.elim s 0
    subst hs0
    rw [← hmap]
    simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  rw [hpair, dist_self]

/-- Coordinate-indexing `t = 0` linear weak-seed correlation breaker
`BitString (2 ^ m) → BitString m → Fin 1 → Bool`. -/
private noncomputable def indexCB (m : ℕ) (b : BitString (2 ^ m)) (y : BitString m)
    (_ : Fin 1) : Bool :=
  b (Fintype.equivFinOfCardEq
    (by simp [Fintype.card_bool] : Fintype.card (BitString m) = 2 ^ m) y)

private theorem isLinearWeakSeedCB_indexCB (m : ℕ) {kSrc kSeed : ℝ}
    (hkSrc : kSrc ≤ (2 ^ m : ℕ)) :
    IsLinearWeakSeedCB (indexCB m) kSrc kSeed 0
      (Real.sqrt ((((2 ^ m : ℕ) : ℝ) - kSrc) * (2 : ℝ) ^ (-kSeed))) := by
  let e : BitString m ≃ Fin (2 ^ m) :=
    Fintype.equivFinOfCardEq (by simp [Fintype.card_bool])
  refine ⟨fun _ _ _ _ => rfl, ?_⟩
  intro r hr α α' _ B J hB hJ
  have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
  subst hr0
  let collapse : Bool ≃ Bool × (Fin 0 → Bool) :=
    { toFun := fun z => (z, Fin.elim0)
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, f⟩ => Prod.ext rfl (funext fun j => Fin.elim0 j) }
  let Y : PMF (BitString m) := J.map Prod.fst
  have hL :
      (B.bind fun b => J.map fun yy =>
        (indexCB m b yy.1 α, fun j : Fin 0 => indexCB m b (yy.2 j) (α' j))) =
      (Y.bind fun y => B.map fun b => b (e y)).map collapse := by
    simp only [Y, indexCB, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, collapse,
      Equiv.coe_fn_mk]
    rw [PMF.bind_comm B J]
    refine congrArg (J.bind ·) (funext fun yy => congrArg (B.bind ·) (funext fun b => ?_))
    exact congrArg PMF.pure (Prod.ext rfl (funext fun j => Fin.elim0 j))
  have hR :
      ((PMF.uniformOfFintype Bool).bind fun u =>
        B.bind fun b => J.map fun yy => (u, fun j : Fin 0 => indexCB m b (yy.2 j) (α' j))) =
      (Y.bind fun _ => PMF.uniformOfFintype Bool).map collapse := by
    rw [PMF.bind_const]
    simp only [PMF.map, Function.comp_def, collapse, Equiv.coe_fn_mk]
    refine congrArg ((PMF.uniformOfFintype Bool).bind ·) (funext fun u => ?_)
    have hconst (b : BitString (2 ^ m)) :
        (J.bind fun yy => PMF.pure (u, fun j : Fin 0 => indexCB m b (yy.2 j) (α' j))) =
        PMF.pure (u, Fin.elim0) := by
      have : (fun yy : BitString m × (Fin 0 → BitString m) =>
          PMF.pure (u, fun j : Fin 0 => indexCB m b (yy.2 j) (α' j))) =
          fun _ => PMF.pure (u, Fin.elim0) :=
        funext fun _ => congrArg PMF.pure (Prod.ext rfl (funext fun j => Fin.elim0 j))
      rw [this, PMF.bind_const]
    simp only [hconst, PMF.bind_const]
  rw [hL, hR]
  refine (dist_map_le _ _ collapse).trans ?_
  have hstep :
      dist (Y.bind fun y => B.map fun b => b (e y)) (Y.bind fun _ => PMF.uniformOfFintype Bool) ≤
      ∑ y, (Y y).toReal * dist (B.map fun b => b (e y)) (PMF.uniformOfFintype Bool) := by
    have h1 : (Y.bind fun y => B.map fun b => b (e y)) =
        (Y.bind fun y => (B.map fun b => b (e y)).map (y, ·)).map Prod.snd := by
      rw [PMF.map_bind]
      refine congrArg (Y.bind ·) (funext fun y => ?_)
      rw [PMF.map_comp]
      exact (PMF.map_id _).symm
    have h2 : (Y.bind fun _ => PMF.uniformOfFintype Bool) =
        (Y.bind fun y => (PMF.uniformOfFintype Bool).map (y, ·)).map Prod.snd := by
      rw [PMF.map_bind]
      refine congrArg (Y.bind ·) (funext fun y => ?_)
      rw [PMF.map_comp]
      exact (PMF.map_id _).symm
    rw [h1, h2]
    exact (dist_map_le _ _ Prod.snd).trans_eq (dist_bind_pair Y _ _)
  refine hstep.trans (Real.le_sqrt_of_sq_le ?_)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun y : BitString m => (Y y).toReal)
    (fun y : BitString m => dist (B.map fun b => b (e y)) (PMF.uniformOfFintype Bool))
  have hYsq : ∑ y : BitString m, (Y y).toReal ^ 2 ≤ (2 : ℝ) ^ (-kSeed) := by
    calc ∑ y : BitString m, (Y y).toReal ^ 2
        ≤ ∑ y : BitString m, (Y y).toReal * (2 : ℝ) ^ (-kSeed) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [sq]
          exact mul_le_mul_of_nonneg_left ((le_minEntropy_iff Y).mp hJ y) ENNReal.toReal_nonneg
      _ = (2 : ℝ) ^ (-kSeed) := by rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]
  have hBsq : ∑ y : BitString m, dist (B.map fun b => b (e y)) (PMF.uniformOfFintype Bool) ^ 2 ≤
      ((2 ^ m : ℕ) : ℝ) - kSrc := by
    rw [Fintype.sum_equiv e _ (fun i => dist (B.map fun b => b i) (PMF.uniformOfFintype Bool) ^ 2)
      (fun _ => rfl)]
    have hsupp : B.support ⊆ (pi fun _ : Fin (2 ^ m) => PMF.uniformOfFintype Bool).support := by
      rw [pi_uniformOfFintype]
      intro b _
      exact mem_support_uniformOfFintype b
    have hpinsker := sum_sq_dist_map_le B (fun _ => PMF.uniformOfFintype Bool) hsupp
    refine hpinsker.trans ?_
    rw [pi_uniformOfFintype]
    have hdiv : ∑ b : BitString (2 ^ m), (B b).toReal *
        Real.log ((B b).toReal / ((PMF.uniformOfFintype (BitString (2 ^ m))) b).toReal) ≤
        2 * (((2 ^ m : ℕ) : ℝ) - kSrc) := by
      calc ∑ b : BitString (2 ^ m), (B b).toReal *
            Real.log ((B b).toReal / ((PMF.uniformOfFintype (BitString (2 ^ m))) b).toReal)
          ≤ ∑ b : BitString (2 ^ m), (B b).toReal * (2 * (((2 ^ m : ℕ) : ℝ) - kSrc)) := by
            refine Finset.sum_le_sum fun b _ => ?_
            by_cases hBb : (B b).toReal = 0
            · simp [hBb]
            have hpos : 0 < (B b).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hBb)
            refine mul_le_mul_of_nonneg_left ?_ hpos.le
            have hunif : ((PMF.uniformOfFintype (BitString (2 ^ m))) b).toReal =
                (2 : ℝ) ^ (-((2 ^ m : ℕ) : ℝ)) := by
              rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
                Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Real.rpow_neg zero_le_two,
                Real.rpow_natCast]
              norm_cast
            have hratio : (B b).toReal /
                ((PMF.uniformOfFintype (BitString (2 ^ m))) b).toReal ≤
                (2 : ℝ) ^ (((2 ^ m : ℕ) : ℝ) - kSrc) := by
              rw [hunif, div_eq_mul_inv, ← Real.rpow_neg zero_le_two, neg_neg]
              calc (B b).toReal * (2 : ℝ) ^ ((2 ^ m : ℕ) : ℝ)
                  ≤ (2 : ℝ) ^ (-kSrc) * (2 : ℝ) ^ ((2 ^ m : ℕ) : ℝ) :=
                    mul_le_mul_of_nonneg_right ((le_minEntropy_iff B).mp hB b) (by positivity)
                _ = (2 : ℝ) ^ (((2 ^ m : ℕ) : ℝ) - kSrc) := by
                    rw [← Real.rpow_add two_pos]; ring_nf
            have hdiv_pos : 0 < (B b).toReal /
                ((PMF.uniformOfFintype (BitString (2 ^ m))) b).toReal :=
              div_pos hpos (by rw [hunif]; positivity)
            have hlog_le := (Real.log_le_log hdiv_pos hratio).trans_eq (Real.log_rpow two_pos _)
            have hln2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
            have hdiff_nn : 0 ≤ ((2 ^ m : ℕ) : ℝ) - kSrc := sub_nonneg.mpr hkSrc
            nlinarith
        _ = 2 * (((2 ^ m : ℕ) : ℝ) - kSrc) := by
            rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]
    linarith
  have hmul := mul_le_mul hYsq hBsq (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
  linarith

private theorem isSumsetExtractor_index_aux (m : ℕ) (hm8 : 8 ≤ m)
    (hbound : ((m : ℝ) + 6) / (2 : ℝ) ^ (m - 8) ≤ 1 / 9) :
    IsSumsetExtractor
      (fun x : BitString (2 ^ m) => fun _ : Fin 1 =>
        (fun f : Fin 1 → Bool => f 0) (sumsetTable (prefixExt m) (indexCB m) x))
      (2 ^ m) (2 ^ m) (19 / 48) := by
  have hlog64 : Real.logb 2 ((1 / 64 : ℝ)⁻¹) = 6 := by
    rw [show (1 / 64 : ℝ)⁻¹ = (2 : ℝ) ^ (6 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hlog63 : (-1 : ℝ) ≤ Real.logb 2 (1 - 1 / 64) := by
    have h1 : Real.logb 2 (2 : ℝ)⁻¹ = -1 := by
      rw [Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
    rw [← h1]
    exact Real.logb_le_logb_of_le one_lt_two (by norm_num) (by norm_num)
  have hCB_raw := isLinearWeakSeedCB_indexCB m
    (kSrc := ((2 ^ m : ℕ) : ℝ) - (m : ℝ) - 6) (kSeed := ((m - 8 : ℕ) : ℝ))
    (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hCB_err : Real.sqrt ((((2 ^ m : ℕ) : ℝ) - (((2 ^ m : ℕ) : ℝ) - (m : ℝ) - 6)) *
      (2 : ℝ) ^ (-((m - 8 : ℕ) : ℝ))) ≤ 1 / 3 := by
    rw [Real.sqrt_le_left (by norm_num), Real.rpow_neg zero_le_two, Real.rpow_natCast]
    have hsimp : (((2 ^ m : ℕ) : ℝ) - (((2 ^ m : ℕ) : ℝ) - (m : ℝ) - 6)) *
        ((2 : ℝ) ^ (m - 8))⁻¹ = ((m : ℝ) + 6) / (2 : ℝ) ^ (m - 8) := by
      rw [div_eq_mul_inv]; ring
    rw [hsimp]
    linarith
  have hCB : IsLinearWeakSeedCB (indexCB m) (((2 ^ m : ℕ) : ℝ) - (m : ℝ) - 6)
      ((m - 8 : ℕ) : ℝ) 0 (1 / 3) :=
    ⟨hCB_raw.1, fun r hr α α' hα' B J hB hJ => (hCB_raw.2 r hr α α' hα' B J hB hJ).trans hCB_err⟩
  have hcast : ((m - 8 : ℕ) : ℝ) = (m : ℝ) - 8 := by
    rw [Nat.cast_sub hm8]; norm_num
  have hres := isSumsetExtractor_of_linearStrongExtractor_weakSeedCB
    (LExt := prefixExt m) (LCB := indexCB m) (R := fun f : Fin 1 → Bool => f 0)
    (k₁ := 2 ^ m) (k₂ := 2 ^ m) (q := 0)
    (γ := 1 / 64) (δA := 1 / 64) (δB := 1 / 64) (εBias := 19 / 48) (εInf := 0)
    (isLinearStrongExtractor_prefixExt m) hCB
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [hlog64]; push_cast; linarith)
    (by rw [hlog64, hcast]; push_cast; linarith)
    (fun D hD => by
      have hb := hD {0} (Finset.singleton_nonempty 0) (by simp)
      have hbias_eq : bias D {0} = ∑ f : Fin 1 → Bool, (D f).toReal * signVal (f 0) := by
        simp only [bias, chi_eq_prod_signVal, Finset.prod_singleton]
      have hprob_eq : ((D.map fun f : Fin 1 → Bool => f 0) true).toReal - 1 / 2 =
          -(bias D {0}) / 2 := by
        rw [hbias_eq, map_apply_toReal]
        have hsum1 := PMF.sum_toReal D
        have hpt : ∀ f : Fin 1 → Bool,
            (if true = f 0 then (D f).toReal else 0) - (D f).toReal / 2 =
            -((D f).toReal * signVal (f 0)) / 2 := fun f => by
          cases f 0 <;> norm_num [signVal] <;> ring
        calc (∑ f : Fin 1 → Bool, if true = f 0 then (D f).toReal else 0) - 1 / 2
            = ∑ f : Fin 1 → Bool,
                ((if true = f 0 then (D f).toReal else 0) - (D f).toReal / 2) := by
              rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum1]
          _ = ∑ f : Fin 1 → Bool, -((D f).toReal * signVal (f 0)) / 2 :=
              Finset.sum_congr rfl fun f _ => hpt f
          _ = -(∑ f : Fin 1 → Bool, (D f).toReal * signVal (f 0)) / 2 := by
              rw [← Finset.sum_div, Finset.sum_neg_distrib]
      rw [hprob_eq, abs_div, abs_neg, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      linarith)
    (fun Q hQ D _ => by
      have hQ0 : Q = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hQ)
      subst hQ0
      rw [coalitionInfluence]
      refine le_of_eq (Finset.sum_eq_zero fun x _ => mul_eq_zero_of_right _ ?_)
      have hnot : ¬ IsUndetermined (∅ : Finset (Fin 1)) (fun f : Fin 1 → Bool => f 0) x := by
        rintro ⟨y, z, hy, hz, hne⟩
        exact hne (by
          dsimp only
          rw [hy 0 (Finset.notMem_empty 0), hz 0 (Finset.notMem_empty 0)])
      simp [hnot])
  rw [add_zero] at hres
  exact hres

/-- Non-vacuous end-to-end client of `isSumsetExtractor_of_linearStrongExtractor_weakSeedCB`:
instantiating with `prefixExt 16`, `indexCB 16`, and the 1-bit dictator on `Seed = Fin 1` yields
an unconditional `(2 ^ 16, 2 ^ 16, 19 / 48)` sumset extractor (`19 / 48 < 1 / 2`). -/
example :
    ∃ E : BitString (2 ^ 16) → BitString 1,
      IsSumsetExtractor E (2 ^ 16) (2 ^ 16) (19 / 48) :=
  ⟨_, isSumsetExtractor_index_aux 16 (by omega) (by norm_num)⟩

/-! ### 5. Standard-axiom verification -/

/--
info: 'Cslib.Probability.PMF.minEntropy_map_conditionalSnd_ge_of_apply_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.minEntropy_map_conditionalSnd_ge_of_apply_ge

/--
info: 'Cslib.Probability.PMF.exists_dist_le_and_le_minEntropy_map_of_dist_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Probability.PMF.exists_dist_le_and_le_minEntropy_map_of_dist_uniform

/-- info: 'Cslib.AffineDisperser.Li.isSumsetExtractor_splitDotProduct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.AffineDisperser.Li.isSumsetExtractor_splitDotProduct

/-- info: 'Cslib.AffineDisperser.Li.isLinearWeakSeedCB_blockDot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.AffineDisperser.Li.isLinearWeakSeedCB_blockDot

/--
info: 'Cslib.AffineDisperser.Li.isSumsetExtractor_of_linearStrongExtractor_weakSeedCB' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.AffineDisperser.Li.isSumsetExtractor_of_linearStrongExtractor_weakSeedCB

end CslibFrontierTests.LiSumsetExtractor
