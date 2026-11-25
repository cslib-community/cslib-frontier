/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MarkovChain.Basic
public import Cslib.Probability.StatisticalDistance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.ENat.Lattice
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Probability.StatisticalDistance.OptimalCoupling

/-!
# Total-variation mixing of finite Markov chains

For a Markov chain `P` on a finite state space with a distribution `π`, define the worst-case
statistical distances after `t` steps

* `d(t) = max_x ‖Pᵗ(x, ·) - π‖_TV` (`Cslib.Probability.MarkovChain.distToStationary`,
  [LevinPeres2017], (4.22)), and
* `d̄(t) = max_{x,y} ‖Pᵗ(x, ·) - Pᵗ(y, ·)‖_TV` (`Cslib.Probability.MarkovChain.distPair`,
  [LevinPeres2017], (4.23)),

and the mixing time `t_mix(ε) = min {t | d(t) ≤ ε}` (`Cslib.Probability.MarkovChain.mixingTime`,
[LevinPeres2017], (4.30)). Here `‖μ - ν‖_TV` is cslib's statistical distance `dist μ ν`,
which is the total-variation distance `max_A |μ A - ν A|` (half of Mathlib's `tvDist`). The
mixing time takes values in `ℕ∞` and is `⊤` exactly when `d(t) > ε` for every `t`, so no
irreducibility or aperiodicity hypothesis is built in.

For stationary `π`: `d(t) ≤ d̄(t) ≤ 2 d(t)` (Lemma 4.10), `d̄` is submultiplicative (Lemma 4.11),
both are non-increasing (Exercise 4.2), `d(ℓ t) ≤ (2 d(t))^ℓ` ((4.32)) and
`t_mix(ε) ≤ ⌈log₂ ε⁻¹⌉ t_mix(1/4)` ((4.34)). The submultiplicativity proof runs a common kernel
from an optimal coupling (`Cslib.Probability.PMF.dist_bind_le_mul`).

## Main definitions

* `Cslib.Probability.MarkovChain.distToStationary`: `d(t)`.
* `Cslib.Probability.MarkovChain.distPair`: `d̄(t)`.
* `Cslib.Probability.MarkovChain.mixingTime`: `t_mix(ε) : ℕ∞`.

## Main results

* `Cslib.Probability.MarkovChain.IsStationary.dist_le_of_forall_mem_support`: if every start in
  the support of `π` is within `δ` of `x` after `t` steps, then so is `π`.
* `Cslib.Probability.MarkovChain.IsStationary.distToStationary_le_distPair`,
  `Cslib.Probability.MarkovChain.distPair_le_two_mul_distToStationary`: Lemma 4.10.
* `Cslib.Probability.MarkovChain.distPair_add_le`: Lemma 4.11, `d̄(s + t) ≤ d̄(s) d̄(t)`.
* `Cslib.Probability.MarkovChain.IsStationary.antitone_distToStationary`,
  `Cslib.Probability.MarkovChain.antitone_distPair`: Exercise 4.2.
* `Cslib.Probability.MarkovChain.IsStationary.distToStationary_mul_le`: (4.32).
* `Cslib.Probability.MarkovChain.IsStationary.dist_mul_le_mul`,
  `Cslib.Probability.MarkovChain.dist_prod_ofFn_le`,
  `Cslib.Probability.MarkovChain.IsStationary.distToStationary_le_half_mul_two_mul_pow`:
  two-step and `t`-step `(1 / 2) * (2 * δ) ^ t` contraction for `π`-stationary kernels
  ([ArbitmanNaorSegev2010], Theorem 5.6).
* `Cslib.Probability.MarkovChain.IsStationary.mixingTime_le_iff`: `t_mix(ε) ≤ t ↔ d(t) ≤ ε`.
* `Cslib.Probability.MarkovChain.IsStationary.mixingTime_le_ceil_logb_mul`: (4.34).

## References

* [LevinPeres2017], Sections 4.4 and 4.5.
* [Y. Arbitman, M. Naor and G. Segev, *Backyard Cuckoo Hashing: Constant Worst-Case Operations
  with a Succinct Representation*][ArbitmanNaorSegev2010], Section 5.3, Theorem 5.6.
-/

public section

open scoped ENNReal Cslib.Probability.PMF

namespace Cslib.Probability.MarkovChain

open Cslib.Probability.PMF

variable {S : Type*} [Fintype S]

/-- `d(t) = max_x ‖Pᵗ(x, ·) - π‖_TV`, the worst-case statistical distance to `π` after `t` steps
([LevinPeres2017], (4.22)). -/
noncomputable def distToStationary (P : MarkovChain S) (π : PMF S) (t : ℕ) : ℝ :=
  ⨆ x, dist ((P ^ t) x) π

/-- `d̄(t) = max_{x,y} ‖Pᵗ(x, ·) - Pᵗ(y, ·)‖_TV`, the worst-case statistical distance between two
copies of the chain after `t` steps ([LevinPeres2017], (4.23)). -/
noncomputable def distPair (P : MarkovChain S) (t : ℕ) : ℝ :=
  ⨆ x, ⨆ y, dist ((P ^ t) x) ((P ^ t) y)

/-- The mixing time `t_mix(ε) = min {t | d(t) ≤ ε}` ([LevinPeres2017], (4.30)), or `⊤` if
`d(t) > ε` for every `t`. -/
noncomputable def mixingTime (P : MarkovChain S) (π : PMF S) (ε : ℝ) : ℕ∞ :=
  open Classical in
  if h : ∃ t, P.distToStationary π t ≤ ε then (Nat.find h : ℕ∞) else ⊤

variable (P : MarkovChain S) (π : PMF S)

theorem dist_le_distToStationary (t : ℕ) (x : S) :
    dist ((P ^ t) x) π ≤ P.distToStationary π t :=
  le_ciSup (f := fun x => dist ((P ^ t) x) π) (Finite.bddAbove_range _) x

theorem distToStationary_le {t : ℕ} {ε : ℝ} (h : ∀ x, dist ((P ^ t) x) π ≤ ε) (hε : 0 ≤ ε) :
    P.distToStationary π t ≤ ε :=
  Real.iSup_le h hε

theorem distToStationary_nonneg (t : ℕ) : 0 ≤ P.distToStationary π t :=
  Real.iSup_nonneg fun _ => dist_nonneg

theorem distToStationary_le_one (t : ℕ) : P.distToStationary π t ≤ 1 :=
  P.distToStationary_le π (fun _ => dist_le_one _ _) zero_le_one

theorem dist_le_distPair (t : ℕ) (x y : S) :
    dist ((P ^ t) x) ((P ^ t) y) ≤ P.distPair t :=
  (le_ciSup (f := fun y => dist ((P ^ t) x) ((P ^ t) y)) (Finite.bddAbove_range _) y).trans <|
    le_ciSup (f := fun x => ⨆ y, dist ((P ^ t) x) ((P ^ t) y))
      ⟨1, by rintro _ ⟨_, rfl⟩; exact Real.iSup_le (fun _ => dist_le_one _ _) zero_le_one⟩ x

theorem distPair_le {t : ℕ} {ε : ℝ} (h : ∀ x y, dist ((P ^ t) x) ((P ^ t) y) ≤ ε)
    (hε : 0 ≤ ε) : P.distPair t ≤ ε :=
  Real.iSup_le (fun x => Real.iSup_le (h x) hε) hε

theorem distPair_nonneg (t : ℕ) : 0 ≤ P.distPair t :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => dist_nonneg

theorem distPair_le_one (t : ℕ) : P.distPair t ≤ 1 :=
  P.distPair_le (fun _ _ => dist_le_one _ _) zero_le_one

variable {P π}

/-- If after `t` steps the chain started at `x` is within `δ` of the chain started at every state
in the support of a stationary `π`, then it is within `δ` of `π`. -/
theorem IsStationary.dist_le_of_forall_mem_support (hπ : P.IsStationary π) {t : ℕ} {x : S}
    {δ : ℝ} (h : ∀ y ∈ π.support, dist ((P ^ t) y) ((P ^ t) x) ≤ δ) :
    dist ((P ^ t) x) π ≤ δ := by
  rw [← hπ.bind_pow t, dist_comm]
  exact dist_bind_left_le_of_le π (P ^ t) ((P ^ t) x) h

/-- `d(t) ≤ d̄(t)` for stationary `π` ([LevinPeres2017], Lemma 4.10). -/
theorem IsStationary.distToStationary_le_distPair (hπ : P.IsStationary π) (t : ℕ) :
    P.distToStationary π t ≤ P.distPair t :=
  P.distToStationary_le π
    (fun x => hπ.dist_le_of_forall_mem_support fun y _ => P.dist_le_distPair t y x)
    (P.distPair_nonneg t)

/-- `d̄(t) ≤ 2 d(t)` ([LevinPeres2017], Lemma 4.10); this holds for every `π`. -/
theorem distPair_le_two_mul_distToStationary (t : ℕ) :
    P.distPair t ≤ 2 * P.distToStationary π t := by
  refine P.distPair_le (fun x y => ?_) (by linarith [P.distToStationary_nonneg π t])
  have := dist_triangle ((P ^ t) x) π ((P ^ t) y)
  rw [dist_comm π] at this
  linarith [P.dist_le_distToStationary π t x, P.dist_le_distToStationary π t y]

theorem IsStationary.distToStationary_succ_le (hπ : P.IsStationary π) (t : ℕ) :
    P.distToStationary π (t + 1) ≤ P.distToStationary π t := by
  refine P.distToStationary_le π (fun x => ?_) (P.distToStationary_nonneg π t)
  rw [pow_succ_apply]; nth_rw 1 [← hπ]
  exact (dist_bind_le _ _ _).trans (P.dist_le_distToStationary π t x)

/-- `d(t)` is non-increasing for stationary `π` ([LevinPeres2017], Exercise 4.2). -/
theorem IsStationary.antitone_distToStationary (hπ : P.IsStationary π) :
    Antitone (P.distToStationary π) :=
  antitone_nat_of_succ_le hπ.distToStationary_succ_le

theorem distPair_succ_le (t : ℕ) : P.distPair (t + 1) ≤ P.distPair t := by
  refine P.distPair_le (fun x y => ?_) (P.distPair_nonneg t)
  rw [pow_succ_apply, pow_succ_apply]
  exact (dist_bind_le _ _ _).trans (P.dist_le_distPair t x y)

/-- `d̄(t)` is non-increasing ([LevinPeres2017], Exercise 4.2). -/
theorem antitone_distPair : Antitone P.distPair :=
  antitone_nat_of_succ_le distPair_succ_le

/-- **Submultiplicativity** `d̄(s + t) ≤ d̄(s) d̄(t)` ([LevinPeres2017], Lemma 4.11). -/
theorem distPair_add_le (s t : ℕ) : P.distPair (s + t) ≤ P.distPair s * P.distPair t := by
  refine P.distPair_le (fun x y => ?_)
    (mul_nonneg (P.distPair_nonneg s) (P.distPair_nonneg t))
  rw [pow_add_apply, pow_add_apply]
  exact (dist_bind_le_mul _ _ (P ^ t) (P.dist_le_distPair t)).trans
    (mul_le_mul_of_nonneg_right (P.dist_le_distPair s x y) (P.distPair_nonneg t))

/-- `d̄(ℓ t) ≤ d̄(t)^ℓ` ([LevinPeres2017], (4.29)). -/
theorem distPair_mul_le (ℓ t : ℕ) : P.distPair (ℓ * t) ≤ P.distPair t ^ ℓ := by
  induction ℓ with
  | zero => simpa using P.distPair_le_one 0
  | succ ℓ ih =>
    rw [Nat.succ_mul, pow_succ]
    exact (P.distPair_add_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (P.distPair_nonneg t))

/-- `d(ℓ t) ≤ (2 d(t))^ℓ` for stationary `π` ([LevinPeres2017], (4.32)). -/
theorem IsStationary.distToStationary_mul_le (hπ : P.IsStationary π) (ℓ t : ℕ) :
    P.distToStationary π (ℓ * t) ≤ (2 * P.distToStationary π t) ^ ℓ :=
  (hπ.distToStationary_le_distPair _).trans <| (P.distPair_mul_le ℓ t).trans <|
    pow_le_pow_left₀ (P.distPair_nonneg t) (P.distPair_le_two_mul_distToStationary t) ℓ

omit [Fintype S] in
private theorem isStationary_list_prod {l : List (MarkovChain S)}
    (hl : ∀ Q ∈ l, Q.IsStationary π) : l.prod.IsStationary π := by
  induction l with
  | nil => exact PMF.bind_pure π
  | cons Q rest ih =>
    rw [List.prod_cons]
    exact (hl Q List.mem_cons_self).mul (ih fun R hR => hl R (List.mem_cons_of_mem Q hR))

/-- Running a chain `P₁` within `δ₁` of `π` followed by a `π`-stationary chain `P₂` within `δ₂` of
`π` produces a chain within `δ₁ * (2 * δ₂)` of `π`. -/
theorem IsStationary.dist_mul_le_mul {P₁ P₂ : MarkovChain S} (hπ₂ : P₂.IsStationary π)
    {δ₁ δ₂ : ℝ} (hb₁ : ∀ x, dist (P₁ x) π ≤ δ₁) (hb₂ : ∀ y, dist (P₂ y) π ≤ δ₂) (x : S) :
    dist ((P₁ * P₂) x) π ≤ δ₁ * (2 * δ₂) := by
  have hpair (a b : S) : dist (P₂ a) (P₂ b) ≤ 2 * δ₂ := by
    have := dist_triangle (P₂ a) π (P₂ b)
    rw [dist_comm π] at this
    linarith [hb₂ a, hb₂ b]
  rw [mul_apply, ← hπ₂]
  exact (dist_bind_le_mul (P₁ x) π P₂ hpair).trans
    (mul_le_mul_of_nonneg_right (hb₁ x) (by linarith [dist_nonneg.trans (hb₂ x)]))

/-- Composing `t ≥ 1` `π`-stationary Markov chains `Ps 0, …, Ps (t - 1)`, each within statistical
distance `δ` of `π` from every start state, contracts statistical distance to at most
`(1 / 2) * (2 * δ) ^ t` ([ArbitmanNaorSegev2010], `arXiv:0912.5424v3`, Section 5.3, Theorem 5.6,
PDF p. 25 / printed p. 24). -/
theorem dist_prod_ofFn_le {t : ℕ} (ht : 1 ≤ t) (Ps : Fin t → MarkovChain S) {π : PMF S}
    (hstat : ∀ i, (Ps i).IsStationary π) {δ : ℝ} (hδ : ∀ i x, dist (Ps i x) π ≤ δ) (x : S) :
    dist (((List.ofFn Ps).prod) x) π ≤ (1 / 2 : ℝ) * (2 * δ) ^ t := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, (Nat.sub_add_cancel ht).symm⟩
  clear ht
  revert x
  induction m with
  | zero =>
    intro x
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    rw [pow_one]; linarith [hδ 0 x]
  | succ m ih =>
    intro x
    rw [List.ofFn_succ, List.prod_cons]
    have htail : ((List.ofFn fun i : Fin (m + 1) => Ps i.succ).prod).IsStationary π :=
      isStationary_list_prod fun _ hQ => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hQ; exact hstat i.succ
    exact (htail.dist_mul_le_mul (hδ 0) (ih (fun i => Ps i.succ) (fun i => hstat i.succ)
      fun i => hδ i.succ) x).trans_eq (by rw [pow_succ]; ring)

/-- Sharpened `t`-step stationary contraction `d(t) ≤ (1 / 2) * (2 d(1)) ^ t` for `1 ≤ t`. -/
theorem IsStationary.distToStationary_le_half_mul_two_mul_pow (hπ : P.IsStationary π)
    {t : ℕ} (ht : 1 ≤ t) :
    P.distToStationary π t ≤ (1 / 2 : ℝ) * (2 * P.distToStationary π 1) ^ t := by
  refine P.distToStationary_le π (fun x => ?_)
    (mul_nonneg (by positivity) (pow_nonneg (by linarith [P.distToStationary_nonneg π 1]) t))
  simpa using dist_prod_ofFn_le ht (fun _ => P) (fun _ => hπ)
    (fun _ y => by simpa using P.dist_le_distToStationary π 1 y) x

theorem mixingTime_eq_top_iff (ε : ℝ) :
    P.mixingTime π ε = ⊤ ↔ ∀ t, ε < P.distToStationary π t := by
  classical
  unfold mixingTime
  split_ifs with h
  · simpa [not_forall] using h
  · simpa using h

theorem mixingTime_le_of_distToStationary_le {ε : ℝ} {t : ℕ}
    (h : P.distToStationary π t ≤ ε) : P.mixingTime π ε ≤ t := by
  classical
  unfold mixingTime
  split_ifs with hex
  · exact ENat.natCast_le_natCast.mpr (Nat.find_min' _ h)
  · exact absurd ⟨t, h⟩ hex

theorem distToStationary_le_of_mixingTime_eq {ε : ℝ} {t : ℕ} (h : P.mixingTime π ε = t) :
    P.distToStationary π t ≤ ε := by
  classical
  unfold mixingTime at h
  split_ifs at h with hex
  · exact ENat.natCast_inj.mp h ▸ Nat.find_spec hex
  · exact absurd h (ENat.top_ne_natCast t)

/-- For stationary `π`, the chain is `ε`-mixed after `t` steps exactly when `t_mix(ε) ≤ t`. -/
theorem IsStationary.mixingTime_le_iff (hπ : P.IsStationary π) (ε : ℝ) (t : ℕ) :
    P.mixingTime π ε ≤ t ↔ P.distToStationary π t ≤ ε := by
  refine ⟨fun h => ?_, P.mixingTime_le_of_distToStationary_le⟩
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top t) h)
  exact (hπ.antitone_distToStationary (ENat.natCast_le_natCast.mp (hs ▸ h))).trans
    (P.distToStationary_le_of_mixingTime_eq hs.symm)

/-- `t_mix(ε) ≤ ⌈log₂ ε⁻¹⌉ t_mix(1/4)` for stationary `π` and `0 < ε`
([LevinPeres2017], (4.34)). -/
theorem IsStationary.mixingTime_le_ceil_logb_mul (hπ : P.IsStationary π) {ε : ℝ} (hε : 0 < ε) :
    P.mixingTime π ε ≤ (⌈Real.logb 2 ε⁻¹⌉₊ : ℕ∞) * P.mixingTime π (1 / 4) := by
  set ℓ := ⌈Real.logb 2 ε⁻¹⌉₊
  have hpow : ε⁻¹ ≤ (2 : ℝ) ^ ℓ := by
    rw [← Real.rpow_natCast]
    exact (Real.logb_le_iff_le_rpow one_lt_two (inv_pos.mpr hε)).mp (Nat.le_ceil _)
  cases h : P.mixingTime π (1 / 4) with
  | top =>
    rcases Nat.eq_zero_or_pos ℓ with h0 | h0
    · rw [h0, pow_zero, inv_le_one₀ hε] at hpow
      simpa [h0] using P.mixingTime_le_of_distToStationary_le
        ((P.distToStationary_le_one π 0).trans hpow)
    · simp [ENat.mul_top (Nat.cast_ne_zero.mpr h0.ne')]
  | coe t =>
    have ht := P.distToStationary_le_of_mixingTime_eq h
    refine mod_cast P.mixingTime_le_of_distToStationary_le
      ((hπ.distToStationary_mul_le ℓ t).trans ?_)
    refine (pow_le_pow_left₀ (by linarith [P.distToStationary_nonneg π t])
      (by linarith : 2 * P.distToStationary π t ≤ 2⁻¹) ℓ).trans ?_
    rwa [inv_pow, inv_le_comm₀ (by positivity) hε]

end Cslib.Probability.MarkovChain
