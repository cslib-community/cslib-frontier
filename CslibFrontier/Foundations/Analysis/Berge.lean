/-
Copyright (c) 2026 Matthew Doty, Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Nick L. Leppelmeier
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Topology/Semicontinuity/Berge.lean`)

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Real

/-!
# Berge's maximum theorem

This module proves **Berge's maximum theorem** ([Berge1963], Chapter VI; primary PDF unverified)
for a correspondence `Γ : X → Set Y` and an objective `u : X → Y → ℝ` between general
topological spaces `X` and `Y`.

If `Γ` has nonempty compact values on `s : Set X`, is both upper and lower hemicontinuous on `s`,
and `u` is continuous on the graph `{(x, y) | x ∈ s ∧ y ∈ Γ x}`, then:

* `Cslib.Berge.maxValue Γ u` is continuous on `s` (`continuousOn_maxValue`);
* `Cslib.Berge.argmaxSet Γ u` has nonempty compact values and is upper hemicontinuous on `s`
  (`argmaxSet_nonempty`, `argmaxSet_isCompact`, `upperHemicontinuousOn_argmaxSet`);
* any single-valued selection from `argmaxSet Γ u` is continuous on `s`
  (`continuousOn_of_argmaxSet_singleton`).

## References

* [C. Berge, *Topological Spaces*][Berge1963] (primary PDF unverified)
-/

public section

namespace Cslib.Berge

open Set Filter Topology

section Definitions

variable {X Y : Type*}

/-- The optimal value `sup_{y ∈ Γ x} u x y` of `u` over `Γ x`. -/
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

theorem le_maxValue_of_mem {Γ : X → Set Y} {u : X → Y → ℝ} {x : X} {y z : Y}
    (hy : y ∈ argmaxSet Γ u x) (hz : z ∈ Γ x) : u x z ≤ maxValue Γ u x :=
  (hy.2 z hz).trans (le_of_eq (maxValue_eq_of_mem_argmaxSet hy))

end Definitions

section Fiber

variable {X Y : Type*} [TopologicalSpace Y] {Γ : X → Set Y} {u : X → Y → ℝ}

/-- If `Γ x` is nonempty and compact and `u x` is continuous on `Γ x`, then `u x` attains its
maximum on `Γ x`. -/
theorem argmaxSet_nonempty {x : X} (hne : (Γ x).Nonempty) (hcomp : IsCompact (Γ x))
    (hu : ContinuousOn (u x) (Γ x)) : (argmaxSet Γ u x).Nonempty := by
  obtain ⟨y, hy, hmax⟩ := hcomp.exists_isMaxOn hne hu
  exact ⟨y, hy, fun z hz => hmax hz⟩

/-- Characterization of `argmaxSet` in terms of `maxValue` under compactness and continuity. -/
theorem mem_argmaxSet_iff {x : X} (hcomp : IsCompact (Γ x))
    (hu : ContinuousOn (u x) (Γ x)) {y : Y} (hy : y ∈ Γ x) :
    y ∈ argmaxSet Γ u x ↔ u x y = maxValue Γ u x := by
  refine ⟨maxValue_eq_of_mem_argmaxSet, fun heq => ⟨hy, fun z hz => ?_⟩⟩
  have hbdd : BddAbove (u x '' Γ x) := (hcomp.image_of_continuousOn hu).bddAbove
  rw [heq]
  exact le_csSup hbdd ⟨z, hz, rfl⟩

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
      have hbdd : BddAbove (u x '' Γ x) := (hcomp.image_of_continuousOn hu).bddAbove
      exact (mem_argmaxSet_iff hcomp hu hy).2
        (le_antisymm (le_csSup hbdd ⟨y, hy, rfl⟩) hge)
    rw [hEq]
    have : CompactSpace (Γ x) := isCompact_iff_compactSpace.mp hcomp
    have hclosed : IsClosed ((fun y : Γ x => u x y) ⁻¹' Ici (maxValue Γ u x)) :=
      isClosed_Ici.preimage hu.domRestrict
    exact hclosed.isCompact.image continuous_subtype_val
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
    ∀ x₀ ∈ s, ∀ a < maxValue Γ u x₀, ∀ᶠ x in 𝓝[s] x₀, a < maxValue Γ u x := by
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
  have hbdd : BddAbove (u x '' Γ x) := ((hcomp x hxs).image_of_continuousOn hu_x).bddAbove
  exact hy_lt.trans_le (le_csSup hbdd ⟨y, hyΓ, rfl⟩)

/-- Upper semicontinuity of `maxValue` when `Γ` is compact-valued and upper hemicontinuous and `u`
is continuous on the graph of `Γ`. -/
theorem upperSemicontinuousOn_maxValue
    (hne : ∀ x ∈ s, (Γ x).Nonempty) (hcomp : ∀ x ∈ s, IsCompact (Γ x))
    (hUHC : UpperHemicontinuousOn Γ s)
    (hu : ContinuousOn (fun p : X × Y => u p.1 p.2) {p | p.1 ∈ s ∧ p.2 ∈ Γ p.1}) :
    ∀ x₀ ∈ s, ∀ b, maxValue Γ u x₀ < b → ∀ᶠ x in 𝓝[s] x₀, maxValue Γ u x < b := by
  intro x₀ hx₀ b hb
  have hu₀ : ContinuousOn (u x₀) (Γ x₀) :=
    hu.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hy => ⟨hx₀, hy⟩
  have hbdd₀ : BddAbove (u x₀ '' Γ x₀) := ((hcomp x₀ hx₀).image_of_continuousOn hu₀).bddAbove
  have hcover : ∀ y : Γ x₀, ∃ U V, IsOpen U ∧ IsOpen V ∧ x₀ ∈ U ∧ (y : Y) ∈ V ∧
      ∀ x ∈ U ∩ s, ∀ z ∈ V ∩ Γ x, u x z < b := by
    intro y
    have hyb : u x₀ y < b := (le_csSup hbdd₀ ⟨y, y.2, rfl⟩).trans_lt hb
    exact nhds_prod_basis_of_continuousOn x₀ (y : Y) hx₀ y.2 hu (isOpen_Iio.mem_nhds hyb)
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
    ContinuousOn (maxValue Γ u) s := by
  intro x₀ hx₀
  exact tendsto_order.mpr ⟨lowerSemicontinuousOn_maxValue hne hcomp hLHC hu x₀ hx₀,
    upperSemicontinuousOn_maxValue hne hcomp hUHC hu x₀ hx₀⟩

/-- **Berge's maximum theorem (correspondence upper hemicontinuity)** ([Berge1963], Chapter VI,
Section 3): under the same hypotheses, the maximizer correspondence `argmaxSet Γ u` is upper
hemicontinuous on `s`. -/
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
  have hcover : ∀ y : K, ∃ U V, IsOpen U ∧ IsOpen V ∧ x₀ ∈ U ∧ (y : Y) ∈ V ∧
      ∀ x ∈ U ∩ s, ∀ z ∈ V ∩ Γ x, u x z < (u x₀ y + maxValue Γ u x₀) / 2 := by
    intro y
    have hyΓ : (y : Y) ∈ Γ x₀ := y.2.1
    have hynot : (y : Y) ∉ argmaxSet Γ u x₀ := fun hyarg => y.2.2 (hsub hyarg)
    have hbdd₀ : BddAbove (u x₀ '' Γ x₀) := ((hcomp x₀ hx₀).image_of_continuousOn hu₀).bddAbove
    have hle : u x₀ y ≤ maxValue Γ u x₀ := le_csSup hbdd₀ ⟨y, hyΓ, rfl⟩
    have hne_val : u x₀ y ≠ maxValue Γ u x₀ := fun heq =>
      hynot ((mem_argmaxSet_iff (hcomp x₀ hx₀) hu₀ hyΓ).mpr heq)
    have hlt : u x₀ y < (u x₀ y + maxValue Γ u x₀) / 2 := by linarith [lt_of_le_of_ne hle hne_val]
    exact nhds_prod_basis_of_continuousOn x₀ (y : Y) hx₀ hyΓ hu (isOpen_Iio.mem_nhds hlt)
  choose U V hU hV hxU hyV hUV using hcover
  have hcov : K ⊆ ⋃ y : K, V y := fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hyV ⟨y, hy⟩⟩
  obtain ⟨t, ht_cov⟩ := hK_comp.elim_finite_subcover V hV hcov
  by_cases ht : t.Nonempty
  · let m : K → ℝ := fun y => (u x₀ y + maxValue Γ u x₀) / 2
    let m₀ : ℝ := t.sup' ht m
    have hm₀_lt : m₀ < maxValue Γ u x₀ := by
      rw [Finset.sup'_lt_iff]
      intro y _
      have hyΓ : (y : Y) ∈ Γ x₀ := y.2.1
      have hynot : (y : Y) ∉ argmaxSet Γ u x₀ := fun hyarg => y.2.2 (hsub hyarg)
      have hbdd₀ : BddAbove (u x₀ '' Γ x₀) := ((hcomp x₀ hx₀).image_of_continuousOn hu₀).bddAbove
      have hlt : u x₀ y < maxValue Γ u x₀ := lt_of_le_of_ne (le_csSup hbdd₀ ⟨y, hyΓ, rfl⟩)
        fun heq => hynot ((mem_argmaxSet_iff (hcomp x₀ hx₀) hu₀ hyΓ).mpr heq)
      dsimp [m]
      linarith
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

end Cslib.Berge
