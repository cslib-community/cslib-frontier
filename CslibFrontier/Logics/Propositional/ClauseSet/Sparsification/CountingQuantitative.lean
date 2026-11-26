/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.Propositional.ClauseSet.Sparsification.CountingTreeBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Input-dependent budgets for disjoint sparsification

For a fixed denominator `d ≥ 2`, use the dyadic approximation to `(n + 1) ^ (1/d)` as the
inverse error budget of the existing disjoint counting sparsifier. The budget is computable
in polynomial time from binary `n`. The same choice yields a power saving `1/d` in the
leaf-count exponent and at most a constant times `(n + 1) ^ (1 + 2*k/d)` clauses per leaf.

This proves the combinatorial bounds needed in [MITHardnessGroup2026SH, Lemma 2.2, §2.2,
printed pp. 6–7] for reciprocal integer savings, using the thresholds and disjoint branches
from [OpenAI2026ETH, Appendix A] already formalized in this library. The bound concerns the
leaf list and does not certify its generation time.
-/

public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Turing.MultiTapeTM
open Finset

/-- Dyadic inverse sparsification error budget for `n` declared variables and saving `1/d`. -/
@[expose] def countingPowerBudget (d n : ℕ) : ℕ :=
  2 ^ (Nat.clog 2 (n + 1) / d)

/-- Computing the inverse error budget is polynomial-time on binary naturals for fixed `d`. -/
theorem computableInPolyTime_countingPowerBudget (d : ℕ) :
    ComputableInPolyTime (countingPowerBudget d) encNat encNat := by
  open ComputableInPolyTime in
  exact binary_two_pow.comp ((unary_div_const d).comp
    (binary_clog_two.comp (binary_add' id' (const 1))))

/-- The selected inverse error budget is positive, including on zero variables. -/
theorem one_le_countingPowerBudget (d n : ℕ) : 1 ≤ countingPowerBudget d n :=
  Nat.one_le_pow _ _ (by decide)

private theorem countingPowerBudget_bounds {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    (n + 1 : ℝ) ^ (d : ℝ)⁻¹ ≤ 2 * countingPowerBudget d n ∧
      (countingPowerBudget d n : ℝ) ≤ 2 * (n + 1 : ℝ) ^ (d : ℝ)⁻¹ := by
  let q := Nat.clog 2 (n + 1) / d
  have hq₁ : q * d ≤ Nat.clog 2 (n + 1) := Nat.div_mul_le_self _ _
  have hq₂ : Nat.clog 2 (n + 1) ≤ (q + 1) * d := by
    have hmod := Nat.mod_lt (Nat.clog 2 (n + 1)) (by omega : 0 < d)
    have hsum := Nat.mod_add_div (Nat.clog 2 (n + 1)) d
    rw [Nat.add_mul, Nat.one_mul]
    rw [Nat.mul_comm d] at hsum
    change Nat.clog 2 (n + 1) % d + q * d = _ at hsum
    omega
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hupper : countingPowerBudget d n ^ d ≤ 2 * (n + 1) := by
    change (2 ^ q) ^ d ≤ _
    rw [← pow_mul]
    exact (Nat.pow_le_pow_right (by decide) hq₁).trans
      (Nat.pow_clog_le_mul (by decide) (Nat.succ_ne_zero _))
  have hlower : n + 1 ≤ (2 * countingPowerBudget d n) ^ d := by
    change n + 1 ≤ (2 * 2 ^ q) ^ d
    rw [← pow_succ', ← pow_mul]
    exact (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) hq₂)
  constructor
  · apply (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity) hd').mpr
    rw [Real.rpow_natCast]
    exact_mod_cast hlower
  · calc
      (countingPowerBudget d n : ℝ) ≤ (2 * (n + 1 : ℝ)) ^ (d : ℝ)⁻¹ := by
        apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) hd').mpr
        rw [Real.rpow_natCast]
        exact_mod_cast hupper
      _ ≤ 2 * (n + 1 : ℝ) ^ (d : ℝ)⁻¹ := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        gcongr
        exact (Real.rpow_le_rpow_of_exponent_le one_le_two
          (inv_le_one_of_one_le₀ (by exact_mod_cast hd))).trans_eq (Real.rpow_one _)

/-- The binary enumeration exponent saves a fixed power, uniformly in the variable count. -/
theorem countingPowerBudget_quotient_le {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    ((n / countingPowerBudget d n + 1 : ℕ) : ℝ) ≤
      3 * (n + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹) := by
  have hB : (0 : ℝ) < countingPowerBudget d n := by
    exact_mod_cast (one_le_countingPowerBudget d n)
  have hq : ((n / countingPowerBudget d n : ℕ) : ℝ) ≤ n / (countingPowerBudget d n : ℝ) := by
    apply (le_div_iff₀ hB).mpr
    exact_mod_cast Nat.div_mul_le_self n (countingPowerBudget d n)
  have hq' : n / (countingPowerBudget d n : ℝ) ≤
      2 * (n + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹) := by
    rw [Real.rpow_sub (by positivity), Real.rpow_one, ← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < (n + 1 : ℝ) ^ (d : ℝ)⁻¹)).mpr
    calc
      n / (countingPowerBudget d n : ℝ) * (n + 1 : ℝ) ^ (d : ℝ)⁻¹ ≤
          n / (countingPowerBudget d n : ℝ) * (2 * countingPowerBudget d n) :=
        mul_le_mul_of_nonneg_left (countingPowerBudget_bounds hd n).1 (by positivity)
      _ ≤ 2 * (n + 1 : ℝ) := by field_simp; linarith
  have hone : 1 ≤ (n + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹) :=
    Real.one_le_rpow (le_add_of_nonneg_left (Nat.cast_nonneg n))
      (sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast hd)))
  push_cast
  linarith

private theorem countingThresholdBase_powerBudget_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ A : ℕ, ∀ {d : ℕ}, 1 ≤ d → ∀ n : ℕ,
      (countingThresholdBase k (countingPowerBudget d n) : ℝ) ≤
        A * ((n + 1 : ℝ) ^ (d : ℝ)⁻¹) ^ 2 := by
  obtain ⟨C, hC⟩ := exists_countingThresholdBase_le_mul_clog hk
  refine ⟨4 * C, fun {d} hd n => ?_⟩
  let B := countingPowerBudget d n
  have hlog : Nat.clog 2 B + 1 ≤ B := by
    unfold B countingPowerBudget
    rw [Nat.clog_pow _ _ (by decide)]
    exact Nat.lt_two_pow_self
  calc
    (countingThresholdBase k B : ℝ) ≤ (C * B * B : ℕ) := by
      exact_mod_cast (hC B (one_le_countingPowerBudget d n)).trans
        (Nat.mul_le_mul_left _ hlog)
    _ ≤ (4 * C : ℕ) * ((n + 1 : ℝ) ^ (d : ℝ)⁻¹) ^ 2 := by
      have h := pow_le_pow_left₀ (Nat.cast_nonneg B) (countingPowerBudget_bounds hd n).2 2
      push_cast
      calc
        (C : ℝ) * B * B = C * (B : ℝ) ^ 2 := by ring
        _ ≤ C * (2 * (n + 1 : ℝ) ^ (d : ℝ)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left h (Nat.cast_nonneg C)
        _ = _ := by ring

/-- For fixed width, the selected density times the variable count bounds the leaf size
by a constant times `(n + 1) ^ (1 + 2*k/d)`, uniformly in `d`. -/
theorem exists_countingPowerBudget_clauseBound_le {k : ℕ} (hk : 2 ≤ k) :
    ∃ A : ℕ, ∀ {d : ℕ}, 1 ≤ d → ∀ n : ℕ,
      ((2 * (∑ j ∈ range k, countingThresholdBase k (countingPowerBudget d n) ^ j) * n + 1 :
          ℕ) : ℝ) ≤ A * (n + 1 : ℝ) ^ (1 + (2 * k : ℝ) / d) := by
  obtain ⟨C, hC⟩ := countingThresholdBase_powerBudget_le hk
  refine ⟨2 * k * C ^ k + 1, fun {d} hd n => ?_⟩
  let M := countingThresholdBase k (countingPowerBudget d n)
  let x : ℝ := n + 1
  have hx : 0 < x := by positivity
  have hs : ∑ j ∈ range k, M ^ j ≤ k * M ^ k := by
    simpa only [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul] using
      (sum_le_sum fun j hj => Nat.pow_le_pow_right
        ((by decide : 0 < 2).trans_le (two_le_countingThresholdBase k _))
        (Nat.le_of_lt (mem_range.mp hj)) :
        ∑ j ∈ range k, M ^ j ≤ ∑ _ ∈ range k, M ^ k)
  have hMpow : (M : ℝ) ^ k ≤ (C : ℝ) ^ k * x ^ ((2 * k : ℝ) / d) := by
    calc
      (M : ℝ) ^ k ≤ (C * (x ^ (d : ℝ)⁻¹) ^ 2) ^ k :=
        pow_le_pow_left₀ (by positivity) (hC hd n) k
      _ = _ := by
        have hexp : (d : ℝ)⁻¹ * ((2 * k : ℕ) : ℝ) = (2 * k : ℝ) / d := by
          push_cast
          rw [div_eq_mul_inv]
          ring
        rw [mul_pow, ← pow_mul, ← Real.rpow_natCast (x ^ (d : ℝ)⁻¹) (2 * k),
          ← Real.rpow_mul hx.le, hexp]
  have hxpow : 1 ≤ x ^ (1 + (2 * k : ℝ) / d) :=
    Real.one_le_rpow (show 1 ≤ x from le_add_of_nonneg_left (Nat.cast_nonneg n))
      (by positivity)
  change ((2 * (∑ j ∈ range k, M ^ j) * n + 1 : ℕ) : ℝ) ≤ _
  calc
    _ ≤ ((2 * (k * M ^ k) * n + 1 : ℕ) : ℝ) := by exact_mod_cast (by gcongr)
    _ ≤ (2 * k * C ^ k : ℝ) * (x * x ^ ((2 * k : ℝ) / d)) + 1 := by
      push_cast
      calc
        2 * (k * (M : ℝ) ^ k) * n + 1 ≤
            2 * (k * ((C : ℝ) ^ k * x ^ ((2 * k : ℝ) / d))) * x + 1 := by
          gcongr
          exact le_add_of_nonneg_right zero_le_one
        _ = _ := by ring
    _ ≤ _ := by
      rw [Real.rpow_add hx, Real.rpow_one]
      push_cast
      linarith [show 1 ≤ x * x ^ ((2 * k : ℝ) / d) from by
        simpa only [Real.rpow_add hx, Real.rpow_one] using hxpow]

/-- The normalized disjoint leaf list simultaneously has a power-saving count bound and a
polynomial clause bound. Exact model counts use the original declared variable set. -/
theorem countingLeaves_nontautological_powerBudget_spec {k d : ℕ} (hk : 2 ≤ k) (hd : 2 ≤ d) :
    ∃ A : ℕ, ∀ {V : Type*} [DecidableEq V] (φ : CNF V) (declared : Finset V),
      (∀ c ∈ φ, c.length ≤ k) → φ.vars.toFinset ⊆ declared →
      let n := declared.card
      let M := countingThresholdBase k (countingPowerBudget d n)
      let leaves := countingLeaves (M ^ ·) (reduce (nontautological φ.toClauseSet))
      (leaves.length : ℝ) ≤ 2 ^ (3 * (n + 1 : ℝ) ^ (1 - (d : ℝ)⁻¹)) ∧
        (leaves.map fun L => L.toCNF.modelCountOn declared).sum = φ.modelCountOn declared ∧
        (∀ x : V → Bool, (leaves.map ClauseSet.toCNF).countP (fun F => F.eval x) =
          if φ.eval x then 1 else 0) ∧
        ∀ L ∈ leaves, (L.card : ℝ) ≤ A * (n + 1 : ℝ) ^ (1 + (2 * k : ℝ) / d) := by
  obtain ⟨A, hA⟩ := exists_countingPowerBudget_clauseBound_le hk
  refine ⟨A, fun φ declared hwidth hvars => ?_⟩
  dsimp only
  obtain ⟨hcount, hpartition, hlength, hleaf⟩ :=
    countingLeaves_nontautological_thresholdBase_spec
      (one_le_countingPowerBudget d declared.card) φ hwidth declared hvars le_rfl
  refine ⟨?_, hcount, hpartition, fun L hL => ?_⟩
  · apply le_trans _ (Real.rpow_le_rpow_of_exponent_le one_le_two
      (countingPowerBudget_quotient_le (by omega) declared.card))
    rw [Real.rpow_natCast]
    exact_mod_cast hlength
  · have hsize := (hleaf L hL).2.2.2.2.2.2
    exact (Nat.cast_le.mpr hsize).trans (hA (by omega) declared.card)

end Cslib.Logic.PL.ClauseSet.Sparsification
