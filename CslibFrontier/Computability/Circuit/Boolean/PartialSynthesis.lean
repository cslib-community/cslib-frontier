/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Complexity
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Computability.Circuit.Boolean.LinearHash
import CslibFrontier.Computability.Circuit.Boolean.SparseSynthesis
import CslibFrontier.Computability.Circuit.Boolean.SparseSynthesisConstruction
import CslibFrontier.Probability.BitString.LinearHash.Collisions
import Cslib.Foundations.Data.Nat.Asymptotics
import Mathlib.Logic.Function.Basic

/-!
# General partial Boolean synthesis

For every positive `ε`, a constant `C` bounds the complexity of every Boolean function specified
on `D` inputs by `(1 + ε) |D| / log₂ |D| + C (n + 1)`. The leading term uses the actual support
size, uniformly in the input dimension and the support. This is the general partial-function
synthesis bound of [Andreev1989], extending the range established by [Sholomov1969]; see
[Jukna2012, Section 1.4.2]. The additive `1` includes empty input families.

An injective linear hash compresses the specified inputs to `2 p` bits, where
`p = ⌈log₂ |D|⌉`. The shared row-pattern implementation costs `24 n + o(2 ^ p / p)` gates.
Partial synthesis on the compressed domain retains `|D| / p` as its leading term. The finitely
many small support sizes are absorbed into the additive term. All circuits use the native
De Morgan basis, counting AND, OR, NOT and constant gates, with shared wires free.

## Main results

* `Cslib.Circuits.Boolean.PartialSynthesis.eventually_complexityOn_le`: the sharp leading
  coefficient with a fixed additive `24 n` overhead, once the support is large enough.
* `Cslib.Circuits.Boolean.PartialSynthesis.complexityOn_le`: the sharp leading coefficient
  for arbitrary support sizes, with an additive term linear in the input dimension.

## References

* [A. E. Andreev, *On the complexity of the realization of partial Boolean functions by circuits
  of functional elements*][Andreev1989], the asymptotic bound in the article's Math-Net abstract.
* [L. A. Sholomov, *On the realization of incompletely defined Boolean functions by circuits of
  functional elements*][Sholomov1969].
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012], Section 1.4.2,
  equation (1.7).
-/

public section

namespace Cslib.Circuits.Boolean.PartialSynthesis

open Finset Filter

private theorem linearHash_le_half_blocks {n p : ℕ} (hp : 2 ≤ p)
    (rows : Fin (2 * p) → BitString n) :
    complexity interpretation (BitString.LinearHash.hash rows) ≤
      24 * n + 16 * (p + 1) * 2 ^ (p / 2) := by
  have hs : 0 < p / 2 := by omega
  have hb : (2 * p) ⌈/⌉ (p / 2) ≤ 6 :=
    (ceilDiv_le_iff_le_mul hs).mpr (by omega)
  have h := complexity_linearHash_le_blocked rows hs
  have hbn := Nat.mul_le_mul_right n hb
  have hbg := Nat.mul_le_mul_right (2 ^ (p / 2)) hb
  have he := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le (p / 2) 1)
  have hpe := Nat.mul_le_mul_left (2 * p) he
  have hpG := Nat.mul_le_mul_left (2 * p) (Nat.one_le_two_pow (n := p / 2))
  have hmain : complexity interpretation (BitString.LinearHash.hash rows) ≤
      24 * n + (10 * p + 6) * 2 ^ (p / 2) := by
    nlinarith only [h, hbn, hbg, hpe, hpG]
  exact hmain.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)

private theorem eventually_linearHash_le (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ n w : ℕ, 2 ^ p ≤ 2 * w →
      ∀ rows : Fin (2 * p) → BitString n,
        (complexity interpretation (BitString.LinearHash.hash rows) : ℝ) ≤
          24 * n + ε * w / p := by
  obtain ⟨P, hP⟩ := exists_nat_gt (2 / ε)
  have hP0 : (0 : ℝ) < P := lt_trans (by positivity : 0 < 2 / ε) hP
  have hcoef : (2 : ℝ) ≤ ε * P := by
    have := (div_lt_iff₀ hε).mp hP
    linarith
  obtain ⟨H, hH⟩ := eventually_atTop.mp
    (Nat.eventually_mul_pow_le_pow (192 * P) 2 Nat.one_lt_two)
  refine ⟨2 * (H + 1), fun p hp n w hw rows => ?_⟩
  let h := p / 2
  have hh : H ≤ h := by omega
  have hh1 : 1 ≤ h := by omega
  have hp2 : 2 ≤ p := by omega
  have hp3 : p ≤ 3 * h := by omega
  have hp4 : p + 1 ≤ 4 * h := by omega
  have hpoly : P * p * (16 * (p + 1)) ≤ 192 * P * h ^ 2 := by
    calc
      _ ≤ P * (3 * h) * (16 * (4 * h)) := by gcongr
      _ = _ := by ring
  have herr : P * p * (16 * (p + 1) * 2 ^ (p / 2)) ≤ 2 ^ p := by
    calc
      _ = (P * p * (16 * (p + 1))) * 2 ^ h := by dsimp only [h]; ring
      _ ≤ 2 ^ h * 2 ^ h := Nat.mul_le_mul_right _ (hpoly.trans (hH h hh))
      _ = 2 ^ (2 * h) := by rw [← pow_add, two_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hscaled := Nat.mul_le_mul_left (P * p) (linearHash_le_half_blocks hp2 rows)
  have hnat : P * p * complexity interpretation (BitString.LinearHash.hash rows) ≤
      P * p * (24 * n) + 2 * w := by
    nlinarith only [hscaled, herr, hw]
  have hreal : (P : ℝ) * p * complexity interpretation (BitString.LinearHash.hash rows) ≤
      (P : ℝ) * p * (24 * n) + 2 * w := by exact_mod_cast hnat
  have hmain : (complexity interpretation (BitString.LinearHash.hash rows) : ℝ) * p ≤
      24 * n * p + ε * w := by
    apply (mul_le_mul_iff_left₀ hP0).mp
    have hcw := mul_le_mul_of_nonneg_right hcoef (by positivity : (0 : ℝ) ≤ w)
    nlinarith only [hreal, hcw]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  apply (mul_le_mul_iff_left₀ hp0).mp
  calc
    _ ≤ 24 * n * p + ε * w := hmain
    _ = (24 * n + ε * w / p) * p := by rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hp0)]

private theorem exists_injective_hash {n p : ℕ} (D : Finset (BitString n))
    (hD : #D ≤ 2 ^ p) :
    ∃ rows : Fin (2 * p) → BitString n, Set.InjOn (BitString.LinearHash.hash rows) D := by
  classical
  apply BitString.LinearHash.exists_injOn D
  calc
    (#D).choose 2 ≤ #D * #D / 2 := by
      rw [Nat.choose_two_right]
      exact Nat.div_le_div_right (Nat.mul_le_mul_left #D (Nat.sub_le #D 1))
    _ ≤ (2 ^ p * 2 ^ p) / 2 := Nat.div_le_div_right (Nat.mul_le_mul hD hD)
    _ < 2 ^ p * 2 ^ p := Nat.div_lt_self (by positivity) (by decide)
    _ = 2 ^ (2 * p) := by rw [← pow_add, two_mul]

private theorem complexityOn_le_small {n : ℕ} (D : Finset (BitString n))
    (u : BooleanFunction n) {W : ℕ} (hD : #D ≤ W) :
    complexityOn interpretation D (single u) ≤ (2 * W ^ 2 + W + 60) * (n + 1) := by
  have h := SparseSynthesis.complexityOn_le_partialBound 0 0 D u (J := 1) (by decide)
  norm_num [SparseSynthesis.partialBound, SparseSynthesis.partialTableBound] at h
  have hsq := Nat.mul_le_mul hD hD
  have hmul := Nat.mul_le_mul_right (2 * n + 2) hsq
  have hWn := Nat.le_mul_of_pos_right W (Nat.succ_pos n)
  nlinarith only [h, hmul, hD, hWn]

/-- The general partial-function bound has a fixed linear overhead: for every positive `ε`,
all sufficiently large supports admit `(1 + ε) |D| / log₂ |D| + 24 n` gates, uniformly in the
input dimension and the labels. This is the De Morgan-basis specialization of the arbitrary-
support upper bound of [Andreev1989], as stated in [Jukna2012, equation (1.7)]. -/
theorem eventually_complexityOn_le (ε : ℝ) (hε : 0 < ε) :
    ∃ w₀ : ℕ, ∀ (n : ℕ) (D : Finset (BitString n)), w₀ ≤ #D →
      ∀ u : BooleanFunction n,
        (complexityOn interpretation D (single u) : ℝ) ≤
          (1 + ε) * #D / Real.logb 2 #D + 24 * n := by
  classical
  obtain ⟨pS, hS⟩ := SparseSynthesis.complexityOn_le_card (ε / 2) (by positivity)
  obtain ⟨pH, hH⟩ := eventually_linearHash_le (ε / 2) (by positivity)
  let N := max (max pS pH) 2
  refine ⟨2 ^ N, fun n D hD u => ?_⟩
  let p := Nat.clog 2 #D
  have hp : N ≤ p := by
    simpa only [Nat.clog_pow 2 N (by decide)] using Nat.clog_mono_right 2 hD
  have hu : #D ≤ 2 ^ p := Nat.le_pow_clog (by decide) _
  have hp2 : 2 ≤ p := (le_max_right _ _).trans hp
  have hps : pS ≤ p := (le_max_left pS pH).trans ((le_max_left _ _).trans hp)
  have hph : pH ≤ p := (le_max_right pS pH).trans ((le_max_left _ _).trans hp)
  have hpow : 2 ^ (p - 1) < #D := Nat.pow_lt_of_lt_clog (by dsimp [p] at *; omega)
  have hlow : 2 ^ p ≤ 2 * #D := by
    have hp' : p = p - 1 + 1 := by omega
    rw [hp', pow_succ]
    omega
  obtain ⟨rows, hinj⟩ := exists_injective_hash D hu
  let H := BitString.LinearHash.hash rows
  let T := D.image H
  have hT : #T = #D := card_image_iff.mpr hinj
  let e : D → BitString (2 * p) := fun x => H x
  have he : Function.Injective e := fun x y hxy =>
    Subtype.ext (hinj x.property y.property hxy)
  let v : BooleanFunction (2 * p) := Function.extend e (fun x : D => u x) (fun _ => false)
  have hv : Set.EqOn (single u) ((single v) ∘ H) D := by
    intro x hx
    funext j
    exact (he.extend_apply (fun x : D => u x) (fun _ => false) ⟨x, hx⟩).symm
  have hcomp : complexityOn interpretation D (single u) ≤
      complexity interpretation H + complexityOn interpretation T (single v) := by
    rw [complexityOn_congr hv]
    have h := complexityOn_comp_le (I := interpretation) (S := (D : Set _)) H (single v)
    have ht : (T : Set _) = H '' (D : Set _) := coe_image
    rw [← ht] at h
    exact h.trans (Nat.add_le_add_right complexityOn_le_complexity _)
  have hs := hS p hps T (by simpa only [hT] using hlow) (by simpa only [hT] using hu) v
  rw [hT] at hs
  have hh := hH p hph n #D hlow rows
  have hr : (complexityOn interpretation D (single u) : ℝ) ≤
      (complexity interpretation H : ℝ) + complexityOn interpretation T (single v) := by
    exact_mod_cast hcomp
  have hbound : (complexityOn interpretation D (single u) : ℝ) ≤
      (1 + ε) * #D / p + 24 * n := by
    dsimp only [H] at hr
    calc
      _ ≤ (24 * n + ε / 2 * #D / p) + (1 + ε / 2) * #D / p :=
        hr.trans (add_le_add hh hs)
      _ = _ := by ring
  have hD1 : 1 < #D := by
    by_contra h
    have hz : p = 0 := Nat.clog_of_right_le_one (by omega) 2
    omega
  have hlog : 0 < Real.logb 2 (#D : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hD1)
  have hlogp : Real.logb 2 (#D : ℝ) ≤ (p : ℝ) := by
    calc
      _ ≤ (⌈Real.logb 2 (#D : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      _ = _ := by congr 1; exact Real.natCeil_logb_natCast 2 #D
  have hdiv : (1 + ε) * #D / (p : ℝ) ≤ (1 + ε) * #D / Real.logb 2 #D :=
    div_le_div_of_nonneg_left (by positivity) hlog hlogp
  exact hbound.trans (add_le_add hdiv le_rfl)

/-- General partial-function synthesis for every support, including the small boundary cases.
The constant is uniform in the input dimension, the specified input set, and its labels.
The denominator is the real logarithm of the actual support cardinality; the additive `1`
covers zero inputs and the conventions `log₂ 0 = log₂ 1 = 0`. -/
theorem complexityOn_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (D : Finset (BitString n)) (u : BooleanFunction n),
      (complexityOn interpretation D (single u) : ℝ) ≤
        (1 + ε) * #D / Real.logb 2 #D + C * (n + 1) := by
  obtain ⟨W, hW⟩ := eventually_complexityOn_le ε hε
  let C : ℝ := 2 * W ^ 2 + W + 84
  have hC : 24 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (W : ℝ)]
  refine ⟨C, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 24) hC, fun n D u => ?_⟩
  by_cases hD : W ≤ #D
  · have hn : (24 : ℝ) * n ≤ C * (n + 1) := by
      have := mul_le_mul_of_nonneg_right hC (by positivity : (0 : ℝ) ≤ n)
      nlinarith
    exact (hW n D hD u).trans (add_le_add le_rfl hn)
  · have h := complexityOn_le_small D u (le_of_lt (lt_of_not_ge hD))
    have hr : (complexityOn interpretation D (single u) : ℝ) ≤
        (2 * (W : ℝ) ^ 2 + W + 60) * (n + 1) := by exact_mod_cast h
    have hlog : 0 ≤ Real.logb 2 (#D : ℝ) := by
      by_cases hz : #D = 0
      · simp [hz]
      · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ #D by omega))
    have hlead : 0 ≤ (1 + ε) * #D / Real.logb 2 #D := div_nonneg (by positivity) hlog
    dsimp only [C]
    nlinarith

end Cslib.Circuits.Boolean.PartialSynthesis
