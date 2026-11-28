/-
Copyright (c) 2026 Matthew Doty, Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Nick L. Leppelmeier
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Topology/Semicontinuity/Berge.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Berge's maximum theorem

This module proves **Berge's maximum theorem** ([Berge1963], Chapter VI; primary PDF unverified)
for a correspondence `Γ : X → Set Y` and an objective `u : X → Y → ℝ` between general
topological spaces `X` and `Y`. It reuses Mathlib's `UpperHemicontinuousOn`,
`LowerHemicontinuousOn`, `LowerSemicontinuousOn`, and `UpperSemicontinuousOn`
(`Mathlib.Topology.Semicontinuity.Hemicontinuity` and `Mathlib.Topology.Semicontinuity.Defs`).
Unlike `[Berge1963]`'s Hausdorff convention on compact sets, the theorems here hold for arbitrary
`[TopologicalSpace X]` and `[TopologicalSpace Y]` with `u` continuous on
`{p | p.1 ∈ s ∧ p.2 ∈ Γ p.1}`.

## Main definitions

* `Cslib.Berge.maxValue`: the value function `x ↦ sSup (u x '' Γ x)` (which agrees with the
  maximum on nonempty bounded-above fibers and evaluates to `0` if empty or unbounded above).
* `Cslib.Berge.argmaxSet`: the maximizer correspondence `x ↦ {y ∈ Γ x | ∀ z ∈ Γ x, u x z ≤ u x y}`.

## Main results

* `Cslib.Berge.continuousOn_maxValue`: continuity of `maxValue Γ u` on `s`.
* `Cslib.Berge.upperHemicontinuousOn_argmaxSet`: upper hemicontinuity of `argmaxSet Γ u` on `s`.
* `Cslib.Berge.continuousOn_of_argmaxSet_singleton`: continuity of any single-valued selection
  from `argmaxSet Γ u`.
* `Cslib.Berge.convex_argmaxSet`, `Cslib.Berge.subsingleton_argmaxSet_of_strictQuasiconcaveOn`,
  `Cslib.Berge.exists_unique_continuousOn_argmaxSet`: convexity under quasiconcavity and unique
  continuous selection under strict quasiconcavity on convex constraint sets.
* `Cslib.Berge.isClosed_graph_of_upperHemicontinuousOn`,
  `Cslib.Berge.upperHemicontinuousOn_of_isClosed_graph`: closed-graph and upper-hemicontinuity
  equivalences for correspondences.

## References

* [C. Berge, *Topological Spaces*][Berge1963] (primary PDF unverified)
-/

public section

namespace Cslib.Berge

open Set Filter Topology

section Definitions

variable {X Y : Type*}

/-- The optimal value `sup_{y ∈ Γ x} u x y` of `u` over `Γ x`. In `ℝ`, `sSup` agrees with the
supremum on nonempty bounded-above fibers and evaluates to `0` when empty or unbounded above. -/
@[expose] noncomputable def maxValue (Γ : X → Set Y) (u : X → Y → ℝ) (x : X) : ℝ :=
  sSup (u x '' Γ x)

/-- The set of maximizers `{y ∈ Γ x | ∀ z ∈ Γ x, u x z ≤ u x y}` of `u` over `Γ x`. -/
@[expose] def argmaxSet (Γ : X → Set Y) (u : X → Y → ℝ) (x : X) : Set Y :=
  {y ∈ Γ x | ∀ z ∈ Γ x, u x z ≤ u x y}

@[simp] theorem mem_argmaxSet {Γ : X → Set Y} {u : X → Y → ℝ} {x : X} {y : Y} :
    y ∈ argmaxSet Γ u x ↔ y ∈ Γ x ∧ ∀ z ∈ Γ x, u x z ≤ u x y :=
  Iff.rfl

theorem argmaxSet_subset {Γ : X → Set Y} {u : X → Y → ℝ} {x : X} :
    argmaxSet Γ u x ⊆ Γ x :=
  fun _ hy => hy.1

theorem maxValue_eq_of_mem_argmaxSet {Γ : X → Set Y} {u : X → Y → ℝ} {x : X} {y : Y}
    (hy : y ∈ argmaxSet Γ u x) : u x y = maxValue Γ u x := by
  have hne : (u x '' Γ x).Nonempty := ⟨u x y, y, hy.1, rfl⟩
  have hle : maxValue Γ u x ≤ u x y := csSup_le hne fun _ ⟨z, hz, hzx⟩ => hzx ▸ hy.2 z hz
  have hge : u x y ≤ maxValue Γ u x :=
    le_csSup ⟨u x y, fun _ ⟨z, hz, hzx⟩ => hzx ▸ hy.2 z hz⟩ ⟨y, hy.1, rfl⟩
  exact le_antisymm hge hle

end Definitions

section Fiber

variable {X Y : Type*} [TopologicalSpace Y] {Γ : X → Set Y} {u : X → Y → ℝ}

/-- Any feasible value `u x y` (`y ∈ Γ x`) is at most `maxValue Γ u x` when `Γ x` is compact and
`u x` is continuous on `Γ x`. -/
theorem le_maxValue_of_mem {x : X} (hcomp : IsCompact (Γ x))
    (hu : ContinuousOn (u x) (Γ x)) {y : Y} (hy : y ∈ Γ x) :
    u x y ≤ maxValue Γ u x :=
  le_csSup (hcomp.image_of_continuousOn hu).bddAbove ⟨y, hy, rfl⟩

/-- If `Γ x` is nonempty and compact and `u x` is continuous on `Γ x`, then `u x` attains its
maximum on `Γ x`. -/
theorem argmaxSet_nonempty {x : X} (hne : (Γ x).Nonempty) (hcomp : IsCompact (Γ x))
    (hu : ContinuousOn (u x) (Γ x)) : (argmaxSet Γ u x).Nonempty := by
  obtain ⟨y, hy, hmax⟩ := hcomp.exists_isMaxOn hne hu
  exact ⟨y, hy, fun z hz => hmax hz⟩

/-- Characterization of `argmaxSet` in terms of `maxValue` under compactness and continuity. -/
theorem mem_argmaxSet_iff {x : X} (hcomp : IsCompact (Γ x))
    (hu : ContinuousOn (u x) (Γ x)) {y : Y} (hy : y ∈ Γ x) :
    y ∈ argmaxSet Γ u x ↔ u x y = maxValue Γ u x :=
  ⟨maxValue_eq_of_mem_argmaxSet, fun heq => ⟨hy, fun _ hz =>
    heq ▸ le_maxValue_of_mem hcomp hu hz⟩⟩

private theorem lt_maxValue_of_notMem_argmaxSet {x : X} (hcomp : IsCompact (Γ x))
    (hu : ContinuousOn (u x) (Γ x)) {y : Y} (hyΓ : y ∈ Γ x) (hynot : y ∉ argmaxSet Γ u x) :
    u x y < maxValue Γ u x :=
  lt_of_le_of_ne (le_maxValue_of_mem hcomp hu hyΓ) fun heq =>
    hynot ((mem_argmaxSet_iff hcomp hu hyΓ).mpr heq)

/-- If `Γ x` is compact and `u x` is continuous on `Γ x`, then `argmaxSet Γ u x` is compact. -/
theorem argmaxSet_isCompact {x : X} (hcomp : IsCompact (Γ x)) (hu : ContinuousOn (u x) (Γ x)) :
    IsCompact (argmaxSet Γ u x) := by
  by_cases hne : (Γ x).Nonempty
  · have hEq : argmaxSet Γ u x =
        ((↑) : Γ x → Y) '' ((fun y : Γ x => u x y) ⁻¹' Ici (maxValue Γ u x)) := by
      ext y
      simp only [mem_image, mem_preimage, mem_Ici, Subtype.exists, exists_and_right,
        exists_eq_right]
      refine ⟨fun hy => ⟨hy.1, le_of_eq (maxValue_eq_of_mem_argmaxSet hy).symm⟩, ?_⟩
      rintro ⟨hy, hge⟩
      exact (mem_argmaxSet_iff hcomp hu hy).2
        (le_antisymm (le_maxValue_of_mem hcomp hu hy) hge)
    rw [hEq]
    have : CompactSpace (Γ x) := isCompact_iff_compactSpace.mp hcomp
    have hclosed : IsClosed ((fun y : Γ x => u x y) ⁻¹' Ici (maxValue Γ u x)) :=
      isClosed_Ici.preimage hu.domRestrict
    exact hclosed.isCompact.image continuous_subtypeVal
  · rw [not_nonempty_iff_eq_empty] at hne
    have hempty : argmaxSet Γ u x = ∅ := by
      ext y
      simp [argmaxSet, hne]
    rw [hempty]
    exact isCompact_empty

end Fiber

section Topological

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {Γ : X → Set Y} {u : X → Y → ℝ} {s : Set X}

private theorem nhds_prod_basis_of_continuousOn (x₀ : X) (y₀ : Y)
    (hx₀ : x₀ ∈ s) (hy₀ : y₀ ∈ Γ x₀)
    (hu : ContinuousOn (fun p : X × Y => u p.1 p.2) {p | p.1 ∈ s ∧ p.2 ∈ Γ p.1})
    {W : Set ℝ} (hW : W ∈ 𝓝 (u x₀ y₀)) :
    ∃ U V, IsOpen U ∧ IsOpen V ∧ x₀ ∈ U ∧ y₀ ∈ V ∧
      ∀ x ∈ U ∩ s, ∀ y ∈ V ∩ Γ x, u x y ∈ W := by
  have hcont : ContinuousWithinAt (fun p : X × Y => u p.1 p.2)
      {p | p.1 ∈ s ∧ p.2 ∈ Γ p.1} (x₀, y₀) := hu (x₀, y₀) ⟨hx₀, hy₀⟩
  obtain ⟨T, hT_open, hp₀T, hTW⟩ := mem_nhdsWithin.mp (hcont hW)
  obtain ⟨U, V, hU, hV, hpU, hpV, hUV⟩ := isOpen_prod_iff.mp hT_open x₀ y₀ hp₀T
  refine ⟨U, V, hU, hV, hpU, hpV, fun x hx y hy => ?_⟩
  have hmem : (x, y) ∈ T ∩ {p : X × Y | p.1 ∈ s ∧ p.2 ∈ Γ p.1} :=
    ⟨hUV ⟨hx.1, hy.1⟩, hx.2, hy.2⟩
  exact hTW hmem

/-- Lower semicontinuity of `maxValue` when `Γ` is lower hemicontinuous and `u` is continuous on
the graph of `Γ`. -/
theorem lowerSemicontinuousOn_maxValue
    (hne : ∀ x ∈ s, (Γ x).Nonempty) (hcomp : ∀ x ∈ s, IsCompact (Γ x))
    (hLHC : LowerHemicontinuousOn Γ s)
    (hu : ContinuousOn (fun p : X × Y => u p.1 p.2) {p | p.1 ∈ s ∧ p.2 ∈ Γ p.1}) :
    LowerSemicontinuousOn (maxValue Γ u) s := by
  intro x₀ hx₀ a ha
  have hu₀ : ContinuousOn (u x₀) (Γ x₀) :=
    hu.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hy => ⟨hx₀, hy⟩
  obtain ⟨y₀, hy₀⟩ := argmaxSet_nonempty (hne x₀ hx₀) (hcomp x₀ hx₀) hu₀
  have hlt : a < u x₀ y₀ := by rwa [maxValue_eq_of_mem_argmaxSet hy₀]
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ :=
    nhds_prod_basis_of_continuousOn x₀ y₀ hx₀ hy₀.1 hu (isOpen_Ioi.mem_nhds hlt)
  have hU_nhds : U ∈ 𝓝[s] x₀ := nhdsWithin_le_nhds (hU.mem_nhds hxU)
  have hLHC_ev : ∀ᶠ x in 𝓝[s] x₀, (Γ x ∩ V).Nonempty :=
    lowerHemicontinuousWithinAt_iff.mp (hLHC x₀ hx₀) V hV ⟨y₀, hy₀.1, hyV⟩
  have hmem_s : ∀ᶠ x in 𝓝[s] x₀, x ∈ s := self_mem_nhdsWithin
  filter_upwards [hU_nhds, hLHC_ev, hmem_s] with x hxU' ⟨y, hyΓ, hyV'⟩ hxs
  have hy_lt : a < u x y := hUV x ⟨hxU', hxs⟩ y ⟨hyV', hyΓ⟩
  have hu_x : ContinuousOn (u x) (Γ x) :=
    hu.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hy' => ⟨hxs, hy'⟩
  exact hy_lt.trans_le (le_maxValue_of_mem (hcomp x hxs) hu_x hyΓ)

/-- Upper semicontinuity of `maxValue` when `Γ` is compact-valued and upper hemicontinuous and `u`
is continuous on the graph of `Γ`. -/
theorem upperSemicontinuousOn_maxValue
    (hne : ∀ x ∈ s, (Γ x).Nonempty) (hcomp : ∀ x ∈ s, IsCompact (Γ x))
    (hUHC : UpperHemicontinuousOn Γ s)
    (hu : ContinuousOn (fun p : X × Y => u p.1 p.2) {p | p.1 ∈ s ∧ p.2 ∈ Γ p.1}) :
    UpperSemicontinuousOn (maxValue Γ u) s := by
  intro x₀ hx₀ b hb
  have hu₀ : ContinuousOn (u x₀) (Γ x₀) :=
    hu.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hy => ⟨hx₀, hy⟩
  have hcover : ∀ y : Γ x₀, ∃ U V, IsOpen U ∧ IsOpen V ∧ x₀ ∈ U ∧ (y : Y) ∈ V ∧
      ∀ x ∈ U ∩ s, ∀ z ∈ V ∩ Γ x, u x z < b := by
    intro y
    have hyb : u x₀ y < b := (le_maxValue_of_mem (hcomp x₀ hx₀) hu₀ y.property).trans_lt hb
    exact nhds_prod_basis_of_continuousOn x₀ (y : Y) hx₀ y.property hu (isOpen_Iio.mem_nhds hyb)
  choose U V hU hV hxU hyV hUV using hcover
  have hcov : Γ x₀ ⊆ ⋃ y : Γ x₀, V y := fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩
  obtain ⟨t, ht_cov⟩ := (hcomp x₀ hx₀).elim_finite_subcover V hV hcov
  let U₀ : Set X := ⋂ y ∈ t, U y
  let V₀ : Set Y := ⋃ y ∈ t, V y
  have hU₀_open : IsOpen U₀ := isOpen_biInter_finset fun y _ => hU y
  have hx₀U₀ : x₀ ∈ U₀ := mem_biInter fun y _ => hxU y
  have hV₀_open : IsOpen V₀ := isOpen_biUnion fun y _ => hV y
  have hU₀_nhds : U₀ ∈ 𝓝[s] x₀ := nhdsWithin_le_nhds (hU₀_open.mem_nhds hx₀U₀)
  have hUHC_ev : ∀ᶠ x in 𝓝[s] x₀, Γ x ⊆ V₀ :=
    (upperHemicontinuousOn_iff_forall_isOpen.mp hUHC) x₀ hx₀ V₀ hV₀_open ht_cov
  have hmem_s : ∀ᶠ x in 𝓝[s] x₀, x ∈ s := self_mem_nhdsWithin
  filter_upwards [hU₀_nhds, hUHC_ev, hmem_s] with x hxU₀' hΓV₀ hxs
  have hux : ContinuousOn (u x) (Γ x) :=
    hu.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hy' => ⟨hxs, hy'⟩
  obtain ⟨z, hz⟩ := argmaxSet_nonempty (hne x hxs) (hcomp x hxs) hux
  rw [← maxValue_eq_of_mem_argmaxSet hz]
  obtain ⟨y, hyt, hzVy⟩ := mem_iUnion₂.mp (hΓV₀ hz.1)
  exact hUV y x ⟨mem_iInter₂.mp hxU₀' y hyt, hxs⟩ z ⟨hzVy, hz.1⟩

/-- **Berge's maximum theorem (value continuity)** ([Berge1963], Chapter VI; primary PDF
unverified): under nonempty compact values, upper and lower hemicontinuity of `Γ`, and joint
continuity of `u` on the graph of `Γ`, the value function `maxValue Γ u` is continuous on `s`. -/
theorem continuousOn_maxValue
    (hne : ∀ x ∈ s, (Γ x).Nonempty) (hcomp : ∀ x ∈ s, IsCompact (Γ x))
    (hUHC : UpperHemicontinuousOn Γ s) (hLHC : LowerHemicontinuousOn Γ s)
    (hu : ContinuousOn (fun p : X × Y => u p.1 p.2) {p | p.1 ∈ s ∧ p.2 ∈ Γ p.1}) :
    ContinuousOn (maxValue Γ u) s :=
  continuousOn_iff_lower_upperSemicontinuousOn.mpr
    ⟨lowerSemicontinuousOn_maxValue hne hcomp hLHC hu,
      upperSemicontinuousOn_maxValue hne hcomp hUHC hu⟩

/-- **Berge's maximum theorem (correspondence upper hemicontinuity)** ([Berge1963], Chapter VI,
Section 3; primary PDF unverified): under the same hypotheses, the maximizer correspondence
`argmaxSet Γ u` is upper hemicontinuous on `s`. -/
theorem upperHemicontinuousOn_argmaxSet
    (hne : ∀ x ∈ s, (Γ x).Nonempty) (hcomp : ∀ x ∈ s, IsCompact (Γ x))
    (hUHC : UpperHemicontinuousOn Γ s) (hLHC : LowerHemicontinuousOn Γ s)
    (hu : ContinuousOn (fun p : X × Y => u p.1 p.2) {p | p.1 ∈ s ∧ p.2 ∈ Γ p.1}) :
    UpperHemicontinuousOn (argmaxSet Γ u) s := by
  rw [upperHemicontinuousOn_iff_forall_isOpen]
  intro x₀ hx₀ O hO hsub
  let K : Set Y := Γ x₀ \ O
  have hK_comp : IsCompact K := (hcomp x₀ hx₀).inter_right hO.isClosed_compl
  have hu₀ : ContinuousOn (u x₀) (Γ x₀) :=
    hu.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hy => ⟨hx₀, hy⟩
  have hsub_lt : ∀ y : K, u x₀ y < maxValue Γ u x₀ := fun y =>
    lt_maxValue_of_notMem_argmaxSet (hcomp x₀ hx₀) hu₀ y.property.1 fun hyarg =>
      y.property.2 (hsub hyarg)
  have hcover : ∀ y : K, ∃ U V, IsOpen U ∧ IsOpen V ∧ x₀ ∈ U ∧ (y : Y) ∈ V ∧
      ∀ x ∈ U ∩ s, ∀ z ∈ V ∩ Γ x, u x z < (u x₀ y + maxValue Γ u x₀) / 2 := by
    intro y
    have hlt : u x₀ y < (u x₀ y + maxValue Γ u x₀) / 2 := by linarith [hsub_lt y]
    exact nhds_prod_basis_of_continuousOn x₀ (y : Y) hx₀ y.property.1 hu (isOpen_Iio.mem_nhds hlt)
  choose U V hU hV hxU hyV hUV using hcover
  have hcov : K ⊆ ⋃ y : K, V y := fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩
  obtain ⟨t, ht_cov⟩ := hK_comp.elim_finite_subcover V hV hcov
  by_cases ht : t.Nonempty
  · let m : K → ℝ := fun y => (u x₀ y + maxValue Γ u x₀) / 2
    let m₀ : ℝ := t.sup' ht m
    have hm₀_lt : m₀ < maxValue Γ u x₀ := by
      rw [Finset.sup'_lt_iff]
      intro y _
      dsimp [m]
      linarith [hsub_lt y]
    let U₁ : Set X := ⋂ y ∈ t, U y
    let W : Set Y := ⋃ y ∈ t, V y
    have hU₁_open : IsOpen U₁ := isOpen_biInter_finset fun y _ => hU y
    have hx₀U₁ : x₀ ∈ U₁ := mem_biInter fun y _ => hxU y
    have hW_open : IsOpen W := isOpen_biUnion fun y _ => hV y
    have hΓ_sub : Γ x₀ ⊆ O ∪ W := fun y hy => by
      by_cases hyO : y ∈ O
      · exact Or.inl hyO
      · exact Or.inr (ht_cov ⟨hy, hyO⟩)
    have hU₁_nhds : U₁ ∈ 𝓝[s] x₀ := nhdsWithin_le_nhds (hU₁_open.mem_nhds hx₀U₁)
    have hLSC_ev : ∀ᶠ x in 𝓝[s] x₀, m₀ < maxValue Γ u x :=
      lowerSemicontinuousOn_maxValue hne hcomp hLHC hu x₀ hx₀ m₀ hm₀_lt
    have hUHC_ev : ∀ᶠ x in 𝓝[s] x₀, Γ x ⊆ O ∪ W :=
      (upperHemicontinuousOn_iff_forall_isOpen.mp hUHC) x₀ hx₀ (O ∪ W) (hO.union hW_open) hΓ_sub
    have hmem_s : ∀ᶠ x in 𝓝[s] x₀, x ∈ s := self_mem_nhdsWithin
    filter_upwards [hU₁_nhds, hLSC_ev, hUHC_ev, hmem_s] with x hxU₁' hm₀ hΓOW hxs
    intro z hz
    rcases hΓOW hz.1 with hzO | hzW
    · exact hzO
    · obtain ⟨y, hyt, hzVy⟩ := mem_iUnion₂.mp hzW
      have hzu : u x z < m y := hUV y x ⟨mem_iInter₂.mp hxU₁' y hyt, hxs⟩ z ⟨hzVy, hz.1⟩
      have hmax_eq : u x z = maxValue Γ u x := maxValue_eq_of_mem_argmaxSet hz
      have hmy_le : m y ≤ m₀ := Finset.le_sup' m hyt
      linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at ht
    have hK_empty : K = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro y hy
      simpa [ht] using ht_cov hy
    have hΓ_sub : Γ x₀ ⊆ O := fun y hy => by
      by_contra hynot
      exact (eq_empty_iff_forall_notMem.mp hK_empty y) ⟨hy, hynot⟩
    have hUHC_ev : ∀ᶠ x in 𝓝[s] x₀, Γ x ⊆ O :=
      (upperHemicontinuousOn_iff_forall_isOpen.mp hUHC) x₀ hx₀ O hO hΓ_sub
    filter_upwards [hUHC_ev] with x hx z hz
    exact hx hz.1

/-- If `argmaxSet Γ u x` is the singleton `{sel x}` on `s`, then `sel` is continuous on `s`. -/
theorem continuousOn_of_argmaxSet_singleton
    (hne : ∀ x ∈ s, (Γ x).Nonempty) (hcomp : ∀ x ∈ s, IsCompact (Γ x))
    (hUHC : UpperHemicontinuousOn Γ s) (hLHC : LowerHemicontinuousOn Γ s)
    (hu : ContinuousOn (fun p : X × Y => u p.1 p.2) {p | p.1 ∈ s ∧ p.2 ∈ Γ p.1})
    {sel : X → Y} (hsing : ∀ x ∈ s, argmaxSet Γ u x = {sel x}) :
    ContinuousOn sel s := by
  have huhc : UpperHemicontinuousOn (fun x => ({sel x} : Set Y)) s := by
    rw [upperHemicontinuousOn_iff_forall_isOpen]
    intro x₀ hx₀ O hO hsub
    have hsub' : argmaxSet Γ u x₀ ⊆ O := by rwa [hsing x₀ hx₀]
    have hev := (upperHemicontinuousOn_iff_forall_isOpen.mp
      (upperHemicontinuousOn_argmaxSet hne hcomp hUHC hLHC hu)) x₀ hx₀ O hO hsub'
    have hmem_s : ∀ᶠ x in 𝓝[s] x₀, x ∈ s := self_mem_nhdsWithin
    filter_upwards [hev, hmem_s] with x hx hxs
    rwa [← hsing x hxs]
  exact upperHemicontinuousOn_singleton_iff.mp huhc

end Topological

section ClosedGraph

open Set Filter Topology

/-- If `s` is closed, every value `F x` (`x ∈ s`) is closed, and `F` is upper hemicontinuous on
`s` into a regular space `Y`, then the restricted graph `{(x, y) | x ∈ s ∧ y ∈ F x}` is closed. -/
theorem isClosed_graph_of_upperHemicontinuousOn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [RegularSpace Y]
    {s : Set X} {F : X → Set Y}
    (hs : IsClosed s) (hF_closed : ∀ x ∈ s, IsClosed (F x))
    (hF_uhc : UpperHemicontinuousOn F s) :
    IsClosed {p : X × Y | p.1 ∈ s ∧ p.2 ∈ F p.1} := by
  let G : Set (X × Y) := {p | p.1 ∈ s ∧ p.2 ∈ F p.1}
  rw [isClosed_iff_clusterPt]
  intro ⟨x₀, y₀⟩ hcl
  let l : Filter G := Filter.comap Subtype.val (𝓝 (x₀, y₀))
  have : l.NeBot := Filter.comap_neBot fun {U} hU => by
    obtain ⟨p, hpU, hpG⟩ := clusterPt_principal_iff.mp hcl U hU
    exact ⟨⟨p, hpG⟩, hpU⟩
  have hx_lim : Tendsto (fun p : G => p.val.1) l (𝓝 x₀) :=
    continuous_fst.continuousAt.tendsto.comp tendsto_comap
  have hy_lim : Tendsto (fun p : G => p.val.2) l (𝓝 y₀) :=
    continuous_snd.continuousAt.tendsto.comp tendsto_comap
  have hx₀ : x₀ ∈ s := hs.mem_of_tendsto hx_lim (Eventually.of_forall fun p => p.property.1)
  have hsub_lim : Tendsto (fun p : G => (⟨p.val.1, p.property.1⟩ : s)) l (𝓝 (⟨x₀, hx₀⟩ : s)) :=
    tendsto_subtype_rng.mpr hx_lim
  have huhc : UpperHemicontinuousAt (s.domRestrict F) ⟨x₀, hx₀⟩ :=
    upperHemicontinuousOn_iff_restrict.mpr hF_uhc ⟨x₀, hx₀⟩
  have hy₀ : y₀ ∈ F x₀ := huhc.mem_of_tendsto (hF_closed x₀ hx₀) hsub_lim
    (Eventually.of_forall fun p : G => p.property.2).frequently hy_lim
  exact ⟨hx₀, hy₀⟩

/-- A correspondence with closed graph over `s` taking values in a sequentially compact set `K`
is upper hemicontinuous on `s`. -/
theorem upperHemicontinuousOn_of_isClosed_graph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [FirstCountableTopology X]
    {s : Set X} {K : Set Y} {F : X → Set Y}
    (hK : IsSeqCompact K) (hsub : ∀ x ∈ s, F x ⊆ K)
    (hgraph : IsClosed {p : X × Y | p.1 ∈ s ∧ p.2 ∈ F p.1}) :
    UpperHemicontinuousOn F s := by
  rw [← upperHemicontinuousOn_iff_restrict]
  intro ⟨x₀, hx₀⟩
  refine UpperHemicontinuousAt.of_sequences (K := K) hK
    (Eventually.of_forall fun x => hsub x.val x.property) ?_
  intro x hx y hy y₀ hy₀
  have hlim_prod : Tendsto (fun n => ((x n : X), y n)) atTop (𝓝 (x₀, y₀)) :=
    (continuousAt_subtypeVal.tendsto.comp hx).prodMk_nhds hy₀
  have hmem : ∀ n, ((x n : X), y n) ∈ {p : X × Y | p.1 ∈ s ∧ p.2 ∈ F p.1} :=
    fun n => ⟨(x n).property, hy n⟩
  exact (hgraph.mem_of_tendsto hlim_prod (Eventually.of_forall hmem)).2

end ClosedGraph

section Convex

/-- If `Γ x` is convex and `u x` is quasiconcave on `Γ x`, then `argmaxSet Γ u x` is convex. -/
theorem convex_argmaxSet {X Y : Type*} [AddCommMonoid Y] [Module ℝ Y]
    {Γ : X → Set Y} {u : X → Y → ℝ} {x : X}
    (hconv : Convex ℝ (Γ x)) (hqc : QuasiconcaveOn ℝ (Γ x) (u x)) :
    Convex ℝ (argmaxSet Γ u x) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  refine ⟨hconv hy₁.1 hy₂.1 ha hb hab, fun z hz => ?_⟩
  exact (hqc (u x z) ⟨hy₁.1, hy₁.2 z hz⟩ ⟨hy₂.1, hy₂.2 z hz⟩ ha hb hab).2

/-- If `Γ x` is convex and `u x` is strictly quasiconcave on `Γ x`, then `argmaxSet Γ u x`
contains at most one point. -/
theorem subsingleton_argmaxSet_of_strictQuasiconcaveOn
    {X Y : Type*} [AddCommMonoid Y] [Module ℝ Y]
    {Γ : X → Set Y} {u : X → Y → ℝ} {x : X}
    (hconv : Convex ℝ (Γ x))
    (hsqc : ∀ ⦃y₁ y₂ : Y⦄, y₁ ∈ Γ x → y₂ ∈ Γ x → y₁ ≠ y₂ →
      ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
        min (u x y₁) (u x y₂) < u x (a • y₁ + b • y₂)) :
    (argmaxSet Γ u x).Subsingleton := by
  intro y₁ hy₁ y₂ hy₂
  by_contra hne
  have hmid_mem : ((1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂) ∈ Γ x :=
    hconv hy₁.1 hy₂.1 (by norm_num) (by norm_num) (by norm_num)
  have hlt := hsqc hy₁.1 hy₂.1 hne (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hle₁ : u x ((1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂) ≤ u x y₁ := hy₁.2 _ hmid_mem
  have hle₂ : u x ((1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂) ≤ u x y₂ := hy₂.2 _ hmid_mem
  linarith [lt_min (hlt.trans_le hle₁) (hlt.trans_le hle₂)]

/-- Under Berge's hypotheses plus convex constraint sets and strict quasiconcavity of `u x` on
`Γ x`, `argmaxSet Γ u` admits a continuous unique maximizer selection on `s`. -/
theorem exists_unique_continuousOn_argmaxSet
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommMonoid Y] [Module ℝ Y]
    {Γ : X → Set Y} {u : X → Y → ℝ} {s : Set X}
    (hne : ∀ x ∈ s, (Γ x).Nonempty) (hcomp : ∀ x ∈ s, IsCompact (Γ x))
    (hconv : ∀ x ∈ s, Convex ℝ (Γ x))
    (hUHC : UpperHemicontinuousOn Γ s) (hLHC : LowerHemicontinuousOn Γ s)
    (hu : ContinuousOn (fun p : X × Y => u p.1 p.2) {p | p.1 ∈ s ∧ p.2 ∈ Γ p.1})
    (hsqc : ∀ x ∈ s, ∀ ⦃y₁ y₂ : Y⦄, y₁ ∈ Γ x → y₂ ∈ Γ x → y₁ ≠ y₂ →
      ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
        min (u x y₁) (u x y₂) < u x (a • y₁ + b • y₂)) :
    ∃ sel : X → Y, ContinuousOn sel s ∧ ∀ x ∈ s, argmaxSet Γ u x = {sel x} := by
  classical
  let harg_ne : ∀ x ∈ s, (argmaxSet Γ u x).Nonempty := fun x hx =>
    argmaxSet_nonempty (hne x hx) (hcomp x hx)
      (hu.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hy => ⟨hx, hy⟩)
  let sel : X → Y := fun x => if hx : x ∈ s then (harg_ne x hx).some else 0
  have hsing : ∀ x ∈ s, argmaxSet Γ u x = {sel x} := by
    intro x hx
    have hmem : sel x ∈ argmaxSet Γ u x := by
      simp only [sel, hx, ↓reduceDIte]
      exact (harg_ne x hx).some_mem
    exact (subsingleton_argmaxSet_of_strictQuasiconcaveOn (hconv x hx)
      (hsqc x hx)).eq_singleton_of_mem hmem
  exact ⟨sel, continuousOn_of_argmaxSet_singleton hne hcomp hUHC hLHC hu hsing, hsing⟩

end Convex

end Cslib.Berge
