/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StatisticalDistance.CloseTo
public import CslibFrontier.Probability.StatisticalDistance.Coupling
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Map

/-!
# Sequential composition of couplings and the `CloseTo` bridge

Two approximate couplings compose sequentially across `PMF.bind` (`CoupledWithin.bind`): if `μ` and
`ν` are coupled within `ε` and, for every `a ∈ ν.support`, the continuations `f a` and `g a` are
coupled within `δ`, then `μ.bind f` and `ν.bind g` are coupled within `ε + δ`, with no finiteness
assumptions and across independent sample-space universes. On diagonal draws `p.1 = p.2` of the
first-stage coupling, the joint continuation uses the witness coupling of `(f p.2, g p.2)`; off the
diagonal it uses their independent product.

In addition, `CoupledWithin.closeTo` bridges any coupling within `ε` directly to statistical
closeness `CloseTo μ ν ε`.

## Main results

* `Cslib.Probability.PMF.CoupledWithin.closeTo`: every `ε`-coupling yields `CloseTo μ ν ε`.
* `Cslib.Probability.PMF.CoupledWithin.bind`: sequential composition of couplings across `PMF.bind`
  adds disagreement bounds.
* `Cslib.Probability.PMF.CoupledWithin.bind_left`,
  `Cslib.Probability.PMF.CoupledWithin.bind_right`: shared-continuation and pointwise-continuation
  specializations.
-/

public section

open scoped ENNReal

namespace Cslib.Probability.PMF.CoupledWithin

universe u v

/-- Every coupling of `μ` and `ν` within disagreement probability `ε` witnesses all-events
statistical closeness `CloseTo μ ν ε`. -/
theorem closeTo {α : Type} {μ ν : PMF α} {ε : ℝ≥0∞} (h : CoupledWithin μ ν ε) :
    CloseTo μ ν ε :=
  h.toOuterMeasure_le

/-- Sequential composition of couplings across `PMF.bind`: if `μ` and `ν` are coupled within `ε`
and `f a` and `g a` are coupled within `δ` for every `a ∈ ν.support`, then `μ.bind f` and
`ν.bind g` are coupled within `ε + δ`. -/
theorem bind {α : Type u} {β : Type v} {μ ν : PMF α} {f g : α → PMF β} {ε δ : ℝ≥0∞}
    (h₁ : CoupledWithin μ ν ε) (h₂ : ∀ a ∈ ν.support, CoupledWithin (f a) (g a) δ) :
    CoupledWithin (μ.bind f) (ν.bind g) (ε + δ) := by
  classical
  obtain ⟨ω, hfst, hsnd, hω⟩ := h₁
  let kernel (p : α × α) : PMF (β × β) :=
    if hp : p.1 = p.2 ∧ p.2 ∈ ν.support then
      (h₂ p.2 hp.2).choose
    else
      (f p.1).bind fun b₁ => (g p.2).map (b₁, ·)
  refine ⟨ω.bind kernel, ?_, ?_, ?_⟩
  · rw [← hfst, PMF.map_bind, PMF.bind_map]
    refine congrArg ω.bind (funext fun p => ?_)
    dsimp only [kernel, Function.comp_def]
    split_ifs with hp
    · exact (h₂ p.2 hp.2).choose_spec.1.trans (congrArg f hp.1.symm)
    · exact map_fst_bind_pair (f p.1) (fun _ => g p.2)
  · rw [← hsnd, PMF.map_bind, PMF.bind_map]
    refine congrArg ω.bind (funext fun p => ?_)
    dsimp only [kernel, Function.comp_def]
    split_ifs with hp
    · exact (h₂ p.2 hp.2).choose_spec.2.1
    · rw [PMF.map_bind]
      have hg : (fun b₁ : β => ((g p.2).map (b₁, ·)).map Prod.snd) = fun _ => g p.2 :=
        funext fun _ => (PMF.map_comp _ _ _).trans (PMF.map_id _)
      rw [hg, PMF.bind_const]
  · have hstep : ∀ p ∈ ω.support, p ∈ {p : α × α | p.1 = p.2} →
        (kernel p).toOuterMeasure {q : β × β | q.1 ≠ q.2} ≤ δ := by
      intro p hp_supp hp_eq
      have hp₂ : p.2 ∈ ν.support := by
        rw [← hsnd]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨p, hp_supp, rfl⟩
      have hp : p.1 = p.2 ∧ p.2 ∈ ν.support := ⟨hp_eq, hp₂⟩
      dsimp only [kernel]
      split_ifs
      exact (h₂ p.2 hp₂).choose_spec.2.2
    have hfail := toOuterMeasure_bind_failure_le ω kernel
      {p : α × α | p.1 = p.2} {q : β × β | q.1 ≠ q.2} δ hstep
    have hcompl : ({p : α × α | p.1 = p.2}ᶜ : Set (α × α)) = {p : α × α | p.1 ≠ p.2} := by
      ext p
      simp
    rw [hcompl] at hfail
    exact hfail.trans (add_le_add hω le_rfl)

/-- Postprocessing two coupled distributions by a shared randomized continuation `f` preserves
`CoupledWithin` with the same disagreement bound. -/
theorem bind_left {α : Type u} {β : Type v} {μ ν : PMF α} {ε : ℝ≥0∞}
    (h : CoupledWithin μ ν ε) (f : α → PMF β) :
    CoupledWithin (μ.bind f) (ν.bind f) ε := by
  simpa only [add_zero] using h.bind fun a _ => refl (f a)

/-- Pointwise `δ`-coupled continuations on `μ.support` lift across `PMF.bind` with disagreement
bound `δ`. -/
theorem bind_right {α : Type u} {β : Type v} (μ : PMF α) {f g : α → PMF β} {δ : ℝ≥0∞}
    (h : ∀ a ∈ μ.support, CoupledWithin (f a) (g a) δ) :
    CoupledWithin (μ.bind f) (μ.bind g) δ := by
  simpa only [zero_add] using (refl μ).bind h

end Cslib.Probability.PMF.CoupledWithin
