/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.GridSum
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Accel
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Contracting.Accelerator
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cutting.OneCut
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.NoAcc
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# The lower bound in the contracting case

Theorem K.7 of [AnthropicVPVNP2026] (p. 59): in the contracting case
(`TwoCases.ContractingCase`) and with `2 ≠ 0` in the field, there are `c > 0` and `m₀` such that
for `m ≥ m₀` every circuit for the permanent `PERM_m` has more than
`2 ^ (c (log m) ^ 2 / log log m)` nodes (`TwoCases.ContractingCase.perm_size_gt`).

The proof is the paper's calculation (p. 59). Theorem J.4 gives the ring `A`, its generators and
the cut hypothesis (`Cutting.exists_cutHyp`), so that by Theorem K.6 (`Interpreter.thm_noacc`)
there are no small accelerators. At the scale `v = ⌊M ^ (1 / B₀)⌋` a circuit with `M ^ a` nodes for
the member `G.poly M` of a family complete for grid sums would give one by Lemma K.3
(`Contracting.exists_hasAcc_of_computedWithin`). So `M ^ a` nodes do not suffice when
`(lg M) ^ (C a) ≤ M` (`TwoCases.ContractingCase.not_computedWithin_pow`), and the bound follows
for every monotone notion of size (`Contracting.exists_quasipoly_lt_of_not_pow`).

## Main results

* `Contracting.exists_quasipoly_lt_of_not_pow`: from exponents to the quasi-polynomial bound.
* `TwoCases.ContractingCase.not_computedWithin_pow`: the contracting case, for every family
  complete for grid sums.
* `TwoCases.ContractingCase.perm_size_gt`: Theorem K.7.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem K.6 (p. 58) and Theorem K.7 (p. 59) with its proof; module `Paper.Scales`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Contracting

open Interpreter

/-- **From exponents to a quasi-polynomial bound** (the calculation in the proof of Theorem K.7,
p. 59). Let `P M s` be monotone in `s`. If `P M (M ^ a)` fails for all `M ≥ M₁` and `a` with
`(lg M) ^ (C a) ≤ M`, then there are `c > 0` and `m₀` such that for `m ≥ m₀`, `P m s` implies
`2 ^ (c (log m) ^ 2 / log log m) < s`, with `c = 1 / (4 C + 4)`. -/
theorem exists_quasipoly_lt_of_not_pow {P : ℕ → ℕ → Prop}
    (hmono : ∀ M s t, s ≤ t → P M s → P M t) {C M₁ : ℕ}
    (h : ∀ M ≥ M₁, ∀ a : ℕ, lg M ^ (C * a) ≤ M → ¬ P M (M ^ a)) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, P m s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s := by
  set c : ℝ := 1 / (4 * C + 4) with hc
  refine ⟨c, by positivity, ?_⟩
  -- eventually `L = log m ≥ 2` and `l = log L ≤ c L`
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 2 ≤ x ∧ Real.logb 2 x ≤ c * x := by
    filter_upwards [(Real.isLittleO_logb_id_atTop (b := 2)).bound (by positivity : 0 < c),
      Filter.eventually_ge_atTop 2] with x hx h2
    rw [Real.norm_of_nonneg (Real.logb_nonneg one_lt_two (by linarith)), id,
      Real.norm_of_nonneg (by linarith)] at hx
    exact ⟨h2, hx⟩
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 (((Real.tendsto_logb_atTop one_lt_two).comp
    tendsto_natCast_atTop_atTop).eventually hev)
  refine ⟨m₀ + M₁ + 2, fun m hm s hs => ?_⟩
  obtain ⟨hL, hl⟩ := hm₀ m (by omega)
  simp only [Function.comp_apply] at hL hl
  set L := Real.logb 2 m
  set l := Real.logb 2 L
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hl1 : 1 ≤ l := (Real.le_logb_iff_rpow_le one_lt_two (by linarith)).2 (by simpa using hL)
  by_contra! hb
  have ha := Nat.ceil_lt_add_one (show 0 ≤ c * L / l by positivity)
  refine h m (by omega) ⌈c * L / l⌉₊ ?_ (hmono m s _ ?_ hs)
  · -- `(lg m) ^ (C a) ≤ m`, in logarithms
    have hlg : (0 : ℝ) < lg m := by exact_mod_cast Nat.succ_pos _
    have h2l : Real.logb 2 (lg m) ≤ 2 * l := by
      have : (lg m : ℝ) ≤ L ^ 2 := by
        have : (Nat.log 2 m : ℝ) ≤ L := by simpa using Real.natLog_le_logb m 2
        simp only [lg, Nat.cast_add, Nat.cast_one]
        nlinarith
      calc Real.logb 2 (lg m) ≤ Real.logb 2 (L ^ 2) := Real.logb_le_logb_of_le one_lt_two hlg this
        _ = 2 * l := by rw [Real.logb_pow]; push_cast; rfl
    have key : ((C * ⌈c * L / l⌉₊ : ℕ) : ℝ) * Real.logb 2 (lg m) ≤ L := by
      push_cast
      calc (C : ℝ) * ⌈c * L / l⌉₊ * Real.logb 2 (lg m) ≤ C * (c * L / l + 1) * (2 * l) := by
            gcongr
            exact Real.logb_nonneg one_lt_two (by exact_mod_cast Nat.succ_pos _)
        _ ≤ 4 * C * c * L := by
            have hmul : (C : ℝ) * (c * L / l + 1) * (2 * l) = 2 * C * c * L + 2 * C * l := by
              field_simp
            nlinarith
        _ ≤ L := by
            rw [hc]
            field_simp
            nlinarith
    have : (lg m : ℝ) ^ (C * ⌈c * L / l⌉₊) ≤ m :=
      (Real.logb_le_logb one_lt_two (by positivity) hmR).1 (by rwa [Real.logb_pow])
    exact_mod_cast this
  · have : (s : ℝ) ≤ (m : ℝ) ^ ⌈c * L / l⌉₊ :=
      calc (s : ℝ) ≤ 2 ^ (c * L ^ 2 / l) := hb
        _ ≤ 2 ^ (L * ⌈c * L / l⌉₊) := Real.rpow_le_rpow_of_exponent_le one_le_two (by
            rw [sq, mul_left_comm c L L, mul_div_assoc]
            exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by linarith))
        _ = (m : ℝ) ^ ⌈c * L / l⌉₊ := by
            rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hmR,
              Real.rpow_natCast]
    exact_mod_cast this

end Cslib.Circuits.Arithmetic.Separation.Contracting

namespace Cslib.Circuits.Arithmetic.Separation.TwoCases

open Interpreter Contracting

variable {K : Type} [Field K]

/-- **The contracting case for a family complete for grid sums** (proof of Theorem K.7, p. 59).
In the contracting case, for a family `G` complete for grid sums there are `C` and `M₁` such that
`G.poly M` is not computed within `M ^ a` nodes when `M ≥ M₁` and `(lg M) ^ (C a) ≤ M`. -/
theorem ContractingCase.not_computedWithin_pow (hK : ContractingCase K)
    {G : PolynomialFamily K} {κ : ℕ} (hG : GridComplete G κ) :
    ∃ C M₁ : ℕ, ∀ M ≥ M₁, ∀ a : ℕ, lg M ^ (C * a) ≤ M → ¬ ComputedWithin (G.poly M) (M ^ a) := by
  obtain ⟨A, hA, θ, h, C₀, v₀, hθ, -, hh, hcut⟩ := Cutting.exists_cutHyp hK
  obtain ⟨C₂, v₂, hno⟩ := thm_noacc hh hcut
  obtain ⟨B, C₁, v₁, hB, hacc⟩ := exists_hasAcc_of_computedWithin hθ (H := 16 * h) (by omega) κ
  obtain ⟨n₁, hn₁⟩ := poly_lg 1 (2 * ((C₂ + 1) * C₁))
  refine ⟨2 * (2 * B) * ((C₂ + 1) * C₁) * (2 * B), (v₁ + v₂ + n₁ + 4) ^ B,
    fun M hM a ha hcomp => ?_⟩
  -- the scale `v = ⌊M ^ (1 / B)⌋`, with `v ^ B ≤ M ≤ v ^ (2 B)`
  obtain ⟨v, hv⟩ : ∃ v, Nat.nthRoot B M = v := ⟨_, rfl⟩
  have hnv : v₁ + v₂ + n₁ + 4 ≤ v := hv ▸ (Nat.le_nthRoot_iff hB.ne').2 hM
  have hvM : v ^ B ≤ M := hv ▸ Nat.pow_nthRoot_le_iff.2 (.inl hB.ne')
  have hMv : M ≤ v ^ (2 * B) :=
    calc M ≤ (v + 1) ^ B := (hv ▸ Nat.lt_pow_nthRoot_add_one hB.ne' M).le
      _ ≤ (v ^ 2) ^ B := Nat.pow_le_pow_left (by nlinarith) _
      _ = v ^ (2 * B) := by rw [← pow_mul]
  have hlog : lg v ^ ((C₂ + 1) * C₁ * (2 * B * a + 1)) ≤ v :=
    Nat.pow_mul_add_one_le_of_pow_le (b := 2 * B) (by omega)
      (lg_mono ((Nat.le_self_pow hB.ne' v).trans hvM)) (le_trans (le_of_eq (by ring_nf))
        (ha.trans hMv)) (by simpa using hn₁ v (by omega))
  -- an accelerator of size `v ^ (C₁ (2 B a + 1))` at the scale `v`, which does not exist
  have hl1 : 1 ≤ lg v := Nat.succ_pos _
  refine hno v (by omega) (C₁ * (2 * B * a + 1)) (le_trans (Nat.pow_le_pow_right hl1 ?_) hlog) K
    (hacc K G hG v (by omega) (2 * B * a) (le_trans (Nat.pow_le_pow_right hl1 ?_) hlog) M hvM
      (hcomp.mono (by rw [pow_mul]; exact Nat.pow_le_pow_left hMv a)))
  · rw [← mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))
  · exact Nat.mul_le_mul (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) (Nat.le_succ _)

/-- **The lower bound in the contracting case** (Theorem K.7 of [AnthropicVPVNP2026], p. 59). In
the contracting case, if `2 ≠ 0` in `K`, there are `c > 0` and `m₀` such that for `m ≥ m₀` every
circuit over `K` for the permanent of the generic `m × m` matrix has more than
`2 ^ (c (log m) ^ 2 / log log m)` nodes. -/
theorem ContractingCase.perm_size_gt (hK : ContractingCase K) (h2 : (2 : K) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, ComputedWithin ((permFamily K).poly m) s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s := by
  obtain ⟨C, M₁, h⟩ := hK.not_computedWithin_pow (gridComplete_permFamily h2)
  exact exists_quasipoly_lt_of_not_pow (fun _ _ _ hst hs => hs.mono hst) h

end Cslib.Circuits.Arithmetic.Separation.TwoCases
