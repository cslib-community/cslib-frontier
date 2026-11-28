/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, polynomial root bounds)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice

/-!
# Sign separation on families of fixed-degree real polynomials

Continuous coefficients and a fixed degree give a locally uniform upper bound on all real
roots. If a jointly continuous test can only vanish at those roots, its eventual sign can
be read at a common point beyond the bound. The set where the sign is eventually positive
is clopen when the test is eventually strictly positive or strictly negative at each parameter.

Adapted from `LocalPolynomialRootBound` and `DegreePieceSeparation` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open Filter Set
open scoped Topology

variable {A : Type*} [TopologicalSpace A]

/-- Near any parameter point a fixed-degree family with continuous coefficients has a common
upper bound on its real roots. The space of parameters can itself be a subtype. -/
theorem exists_eventually_eval_ne_zero_of_fixed_degree (P : A → Polynomial ℝ) (d : ℕ)
    (hcoeff : ∀ i, Continuous (fun x => (P x).coeff i))
    (hdegree : ∀ x, (P x).natDegree ≤ d) (hlead : ∀ x, (P x).coeff d ≠ 0) (x₀ : A) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ x in 𝓝 x₀, ∀ v : ℝ, R ≤ v → (P x).eval v ≠ 0 := by
  have hd (x : A) : (P x).natDegree = d :=
    le_antisymm (hdegree x) (le_natDegree_of_ne_zero (hlead x))
  have hsup : Continuous (fun x => (Finset.range d).sup (fun i => ‖(P x).coeff i‖₊)) :=
    Continuous.finset_sup_apply fun i _ => (hcoeff i).nnNorm
  have hbound : Continuous (fun x => (P x).cauchyBound) := by
    simp only [cauchyBound, leadingCoeff, hd]
    exact (hsup.div (hcoeff d).nnNorm (fun x => nnNorm_ne_zero_iff.mpr (hlead x))).add
      continuous_const
  have hreal : Continuous (fun x => ((P x).cauchyBound : ℝ)) :=
    continuous_subtype_val.comp hbound
  let R := ((P x₀).cauchyBound : ℝ) + 1
  refine ⟨R, by dsimp only [R]; positivity, ?_⟩
  have hnear : ∀ᶠ x in 𝓝 x₀, ((P x).cauchyBound : ℝ) < R :=
    hreal.continuousAt.eventually (Iio_mem_nhds (lt_add_one _))
  filter_upwards [hnear] with x hx
  intro v hv hz
  have hne : P x ≠ 0 := by
    intro he
    exact hlead x (by rw [he, coeff_zero])
  have hroot := Polynomial.IsRoot.norm_lt_cauchyBound hne hz
  have habs : |v| < ((P x).cauchyBound : ℝ) := by exact_mod_cast hroot
  exact hv.not_gt ((le_abs_self v).trans_lt (habs.trans hx))

/-- A jointly continuous test with zeros confined to a fixed-degree polynomial family has
locally constant eventual sign. The parameter set with eventual positive sign is clopen
when its complement has eventual negative sign. -/
theorem eventualSign_isClopen_of_fixed_degree (P : A → Polynomial ℝ) (d : ℕ)
    (hcoeff : ∀ i, Continuous (fun x => (P x).coeff i))
    (hdegree : ∀ x, (P x).natDegree ≤ d) (hlead : ∀ x, (P x).coeff d ≠ 0)
    (f : A → ℝ → ℝ) (hf : Continuous (fun q : A × ℝ => f q.1 q.2)) (G : A → Prop)
    (hzero : ∀ x v, f x v = 0 → (P x).eval v = 0)
    (hpos : ∀ x, G x → ∀ᶠ v : ℝ in atTop, 0 < f x v)
    (hneg : ∀ x, ¬G x → ∀ᶠ v : ℝ in atTop, f x v < 0) :
    IsClopen {x | G x} := by
  have hclass (x : A) (R : ℝ) (havoid : ∀ v : ℝ, R ≤ v → f x v ≠ 0) :
      G x ↔ 0 < f x R := by
    have hc : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
    have hsign (v : ℝ) (hv : R ≤ v) : SignType.sign (f x R) = SignType.sign (f x v) :=
      isPreconnected_Ici.sign_eq_of_continuousOn hc.continuousOn havoid self_mem_Ici hv
    constructor
    · intro hx
      obtain ⟨v, hv, hfv⟩ := ((eventually_ge_atTop R).and (hpos x hx)).exists
      exact sign_eq_one_iff.mp ((hsign v hv).trans (sign_pos hfv))
    · intro hp
      by_contra hx
      obtain ⟨v, hv, hfv⟩ := ((eventually_ge_atTop R).and (hneg x hx)).exists
      exact (sign_eq_neg_one_iff.mp ((hsign v hv).trans (sign_neg hfv))).not_gt hp
  have hlocal (x : A) : ∀ᶠ y in 𝓝 x, G y ↔ G x := by
    obtain ⟨R, _, hR⟩ := exists_eventually_eval_ne_zero_of_fixed_degree P d hcoeff hdegree hlead x
    have havoid : ∀ᶠ y in 𝓝 x, ∀ v : ℝ, R ≤ v → f y v ≠ 0 :=
      hR.mono fun y hy v hv he => hy v hv (hzero y v he)
    have hxavoid : ∀ v : ℝ, R ≤ v → f x v ≠ 0 := havoid.self_of_nhds
    have hfx : Continuous (fun y => f y R) := hf.comp (continuous_id.prodMk continuous_const)
    by_cases hx : G x
    · have hp := (hclass x R hxavoid).mp hx
      have hnear : ∀ᶠ y in 𝓝 x, 0 < f y R := hfx.continuousAt.eventually (Ioi_mem_nhds hp)
      filter_upwards [havoid, hnear] with y hy hfy
      exact iff_of_true ((hclass y R hy).mpr hfy) hx
    · have hn : f x R < 0 := lt_of_le_of_ne
        (le_of_not_gt (hx ∘ (hclass x R hxavoid).mpr)) (hxavoid R le_rfl)
      have hnear : ∀ᶠ y in 𝓝 x, f y R < 0 := hfx.continuousAt.eventually (Iio_mem_nhds hn)
      filter_upwards [havoid, hnear] with y hy hfy
      exact iff_of_false (fun h => hfy.not_gt ((hclass y R hy).mp h)) hx
  have hopen : IsOpen {x | G x} :=
    isOpen_iff_mem_nhds.mpr fun x hx => (hlocal x).mono fun _ hy => hy.mpr hx
  have hcompl : IsOpen {x | ¬G x} :=
    isOpen_iff_mem_nhds.mpr fun x hx => (hlocal x).mono fun _ hy h => hx (hy.mp h)
  exact ⟨by simpa only [Set.compl_ofPred, not_not] using hcompl.isClosed_compl, hopen⟩

end Polynomial
