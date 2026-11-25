/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, compact minima)

public import CslibFrontier.Init
public import Mathlib.Topology.Order.Compact

/-!
# Continuity of coercive minima

A common lower bound with compact sublevels confines the minima of nearby objectives
to one compact set. Continuity follows by taking the infimum over this compact set.

Adapted from `ParameterizedCoerciveMinimum` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

open Filter Set
open scoped Topology

/-- If a jointly continuous objective has a common lower bound with compact sublevels,
its infimum over the nonempty decision space varies continuously with the parameter. -/
theorem continuous_sInf_range_of_compact_sublevels {A X R : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [Nonempty X]
    [ConditionallyCompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R] [NoMaxOrder R]
    {H : A → X → R} (hH : Continuous ↿H) {G : X → R} (hdom : ∀ p x, G x ≤ H p x)
    (hcompact : ∀ B : R, IsCompact {x | G x ≤ B}) :
    Continuous (fun p => sInf (range (H p))) := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  apply continuous_iff_continuousAt.mpr
  intro p₀
  obtain ⟨B, hB⟩ := exists_gt (H p₀ x₀)
  let K := {x | G x ≤ B}
  have hK : IsCompact K := hcompact B
  have hnear : ∀ᶠ p in 𝓝 p₀, H p x₀ < B :=
    (hH.comp (continuous_id.prodMk continuous_const)).continuousAt.eventually (Iio_mem_nhds hB)
  apply (hK.continuous_sInf hH).continuousAt.congr_of_eventuallyEq
  filter_upwards [hnear] with p hp
  have h₀ : x₀ ∈ K := (hdom p x₀).trans hp.le
  have hpcont : Continuous (H p) := hH.comp (continuous_const.prodMk continuous_id)
  obtain ⟨x, _, hx, hmin⟩ := hK.exists_sInf_image_eq_and_le ⟨x₀, h₀⟩ hpcont.continuousOn
  rw [hx]
  apply IsLeast.csInf_eq
  refine ⟨mem_range_self x, ?_⟩
  rintro _ ⟨y, rfl⟩
  by_cases hy : G y ≤ B
  · exact hmin y hy
  · calc
      H p x ≤ H p x₀ := hmin x₀ h₀
      _ ≤ B := hp.le
      _ ≤ G y := le_of_not_ge hy
      _ ≤ H p y := hdom p y
