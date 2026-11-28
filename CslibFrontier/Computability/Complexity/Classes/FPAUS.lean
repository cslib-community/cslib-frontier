/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StatisticalDistance.CloseTo
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map

/-!
# Fully polynomial almost uniform samplers

Jerrum, Valiant and Vazirani's generator may return `none`. Every successful output belongs to
the witness set. Its individual probability approximates a common positive reference mass
`φ(x)` multiplicatively, and the probability of success is at least one half on nonempty
instances [JerrumValiantVazirani1986, §6, p. 181]. Time is polynomial in the instance length
and the unary precision `q`. The total-variation estimates below are used in the reductions
between this generator and approximate counting.

## Main definitions

* `Cslib.Complexity.uniformWitness`: the uniform law on a finite set of witnesses.
* `Cslib.Complexity.IsFPAUS`: a fully polynomial almost uniform sampler.
* `Cslib.Complexity.FPAUS`: the witness families admitting one.

## Main results

* `Cslib.Complexity.uniformWitness_toOuterMeasure_some`: the probability of an event of witnesses
  is its relative cardinality.
* `Cslib.Complexity.closeTo_uniformWitness_of_le`: pointwise lower bounds `(1 - ε) / |W|` on the
  witnesses give closeness to `uniformWitness W`.

## References

* [A. Sinclair, M. Jerrum, *Approximate counting, uniform generation and rapidly mixing Markov
  chains*][SinclairJerrum1989]
* [M. R. Jerrum, L. G. Valiant, V. V. Vazirani, *Random generation of combinatorial structures from
  a uniform distribution*][JerrumValiantVazirani1986]
* [A. Sinclair, *CS294 Partition Functions*, Lecture 4, Definition 4.3 and Section
  4.2][Sinclair2025]
-/

public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM

variable {α : Type}

/-- The uniform law on the witnesses `W`, as `some w`; the point mass at `none` when there are
none. -/
noncomputable def uniformWitness (W : Finset (List Bool)) : PMF (Option (List Bool)) :=
  if h : W.Nonempty then (PMF.uniformOfFinset W h).map some else PMF.pure none

/-- A fully polynomial almost uniform generator in the sense of Jerrum, Valiant and Vazirani
[JerrumValiantVazirani1986, §6, p. 181]. The unary input `q` asks for dyadic relative error
`ε = 2 ^ (-(q+1))`. Every positive tolerance below one admits a smaller such tolerance with
`q = O(log (1/ε))`. The common reference mass may depend on the instance. -/
structure IsFPAUS (enc : α ↪ List Bool) (W : α → Finset (List Bool))
    (S : α → ℕ → ProbComp (Option (List Bool))) : Prop where
  /-- The sampler runs in strict polynomial time on the encoded instance and unary precision. -/
  isPPTOn : IsPPTOn (encPair enc encUnary) (encOption encBits) (Function.uncurry S)
  /-- A successful run always outputs a witness. -/
  valid : ∀ x q w, w ∉ W x → ProbComp.eval (S x q) (some w) = 0
  /-- On a nonempty instance the probability of failure is at most one half. -/
  failure : ∀ x q, (W x).Nonempty → (ProbComp.eval (S x q) none).toReal ≤ 1 / 2
  /-- Every individual witness has the prescribed relative accuracy at every precision. -/
  pointwise : ∀ x, ∃ φ : ℝ, φ ∈ Set.Ioc 0 1 ∧ ∀ q w, w ∈ W x →
    φ / (1 + (1 / 2 : ℝ) ^ (q + 1)) ≤ (ProbComp.eval (S x q) (some w)).toReal ∧
    (ProbComp.eval (S x q) (some w)).toReal ≤ (1 + (1 / 2 : ℝ) ^ (q + 1)) * φ

/-- The witness families with a fully polynomial almost uniform sampler, on instances encoded by
`enc`. -/
@[expose]
def FPAUS (enc : α ↪ List Bool) : Set (α → Finset (List Bool)) :=
  {W | ∃ S, IsFPAUS enc W S}

theorem uniformWitness_of_nonempty {W : Finset (List Bool)} (h : W.Nonempty) :
    uniformWitness W = (PMF.uniformOfFinset W h).map some :=
  dite_eq_left h

@[simp]
theorem uniformWitness_empty : uniformWitness ∅ = PMF.pure none :=
  dite_eq_right Finset.not_nonempty_empty

/-- Point masses of the ideal law on successful outputs. -/
theorem uniformWitness_some_toReal (W : Finset (List Bool)) (w : List Bool) :
    (uniformWitness W (some w)).toReal = if w ∈ W then 1 / (W.card : ℝ) else 0 := by
  rcases W.eq_empty_or_nonempty with rfl | h
  · simp
  · rw [uniformWitness_of_nonempty h,
      Probability.PMF.map_apply_of_injective _ (Option.some_injective _)]
    by_cases hw : w ∈ W <;> simp [Probability.PMF.uniformOfFinset_apply, hw, one_div]

/-- Nonempty witness sets have no ideal failure mass. -/
theorem uniformWitness_none {W : Finset (List Bool)} (h : W.Nonempty) :
    uniformWitness W none = 0 := by
  rw [uniformWitness_of_nonempty h]
  simp [PMF.map_apply]

/-- The probability that the uniform witness lies in `E` is the relative number of witnesses
in `E`. -/
theorem uniformWitness_toOuterMeasure_some {W : Finset (List Bool)} (h : W.Nonempty)
    (E : Set (List Bool)) [DecidablePred (· ∈ E)] :
    ((uniformWitness W).toOuterMeasure (some '' E)).toReal =
      ((W.filter (· ∈ E)).card : ℝ) / W.card := by
  classical
  rw [uniformWitness_of_nonempty h, PMF.toOuterMeasure_map_apply,
    Set.preimage_image_eq _ (Option.some_injective _), PMF.toOuterMeasure_apply,
    tsum_eq_sum (s := W) (fun w hw => by simp [Set.indicator, hw]),
    Finset.sum_congr (g := fun w => if w ∈ E then ((W.card : ENNReal)⁻¹) else 0) rfl
      (fun w hw => by simp [Set.indicator, hw]),
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp [div_eq_mul_inv]

open Cslib.Probability

/-- **Closeness to the uniform witness law from pointwise lower bounds.** A law on optional
witnesses giving every witness of `W` probability at least `(1 - ε) / |W|`, and no witness at all
when `W` is empty, is within statistical distance `ε` of `uniformWitness W`. -/
theorem closeTo_uniformWitness_of_le {μ : PMF (Option (List Bool))} {W : Finset (List Bool)}
    {ε : ℝ} (hε : 0 ≤ ε)
    (hle : ∀ v ∈ W, ENNReal.ofReal ((1 - ε) / W.card) ≤ μ (some v))
    (hempty : W = ∅ → ∀ v, μ (some v) = 0) :
    CloseTo μ (uniformWitness W) (ENNReal.ofReal ε) := by
  rcases W.eq_empty_or_nonempty with hW | hW
  · have hμ : μ = PMF.pure none := by
      have hnone : μ none = 1 := by
        rw [PMF.apply_eq_one_iff]
        refine Set.eq_singleton_iff_nonempty_unique_mem.2 ⟨μ.support_nonempty, fun o ho => ?_⟩
        cases o with
        | none => rfl
        | some v => exact absurd (hempty hW v) ((PMF.mem_support_iff _ _).1 ho)
      ext o
      cases o with
      | none => simp [hnone]
      | some v => simp [hempty hW v]
    rw [hμ, hW, uniformWitness_empty]
    exact (CloseTo.refl _).mono zero_le
  · refine CloseTo.of_le_apply hε fun o => ?_
    cases o with
    | none => simp [uniformWitness_none hW]
    | some v =>
      rw [uniformWitness_of_nonempty hW,
        Probability.PMF.map_apply_of_injective _ (Option.some_injective _)]
      by_cases hv : v ∈ W
      · refine le_trans ?_ (hle v hv)
        simp only [Probability.PMF.uniformOfFinset_apply, hv, ↓reduceIte]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos
          (by exact_mod_cast Finset.card_pos.2 hW), ← ENNReal.ofReal_mul' (by positivity),
          div_eq_mul_inv]
      · simp only [Probability.PMF.uniformOfFinset_apply, hv, ↓reduceIte, mul_zero]
        exact zero_le

end Cslib.Complexity
