/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.LinearValuation
import CslibFrontier.GameTheory.Mechanism.CriticalBid

/-!
# Single-parameter and feasible-set bridges on restricted valuation domains

`CslibFrontier.GameTheory.Mechanism.VCG` defines restricted-domain direct-revelation properties
(`Mechanism.IsDSICOn`, `Mechanism.IsIROn`, `Mechanism.NoPositiveTransfersOn`) and proves the
restricted-domain Groves/VCG theorems ([Nisan2007], Theorem 9.17 and Lemma 9.20), while
`CslibFrontier.GameTheory.Mechanism.LinearValuation` establishes the `IsDSIC` / `IsDSICOn`
equivalence between single-parameter mechanisms and general mechanisms on `Mechanism.linearDomain`.

This module completes the bridge between `SingleParameter.Mechanism` and general `Mechanism`:

* **Individual rationality equivalence**: `(M.toSingleParameter x).IsIR ↔ M.IsIROn (linearDomain x)`
  (`Mechanism.isIR_toSingleParameter_iff`) and `M.IsIR ↔ M.toMechanism.IsIROn (linearDomain id)`
  (`SingleParameter.Mechanism.isIR_iff_isIROn_toMechanism`).
* **Feasible-set subtype embedding (`SingleParameter.Mechanism.toMechanismOn`)**: any
  `M : SingleParameter.Mechanism ι` whose allocations on nonnegative bids belong to a feasible set
  `X : Set (ι → ℝ)` embeds directly into `Mechanism ι X` (with outcome type `X` rather than all of
  `ι → ℝ`). When every bidder has some outcome in `X` with nonzero allocation, `IsDSICOn` and
  `IsIROn` on `Mechanism.linearDomain Subtype.val` are equivalent to `M.IsDSIC` and `M.IsIR`
  (`SingleParameter.Mechanism.isDSIC_iff_isDSICOn_toMechanismOn`,
  `SingleParameter.Mechanism.isIR_iff_isIROn_toMechanismOn`).

For the specialization of `Mechanism.vcg` to `Vickrey.singleItemFeasible`, see
`CslibFrontier.GameTheory.Mechanism.VickreyVCG`.

## Main definitions

* `SingleParameter.extractBid`, `SingleParameter.Mechanism.toMechanismOn`: embedding a
  single-parameter mechanism with feasible set `X : Set (ι → ℝ)` into `Mechanism ι X`.

## Main results

* `Mechanism.isIR_toSingleParameter_iff`,
  `SingleParameter.Mechanism.isIR_iff_isIROn_toMechanism`: exact `IsIR` / `IsIROn` equivalences
  for `toSingleParameter` and `toMechanism`.
* `SingleParameter.Mechanism.isDSIC_iff_isDSICOn_toMechanismOn`,
  `SingleParameter.Mechanism.isIR_iff_isIROn_toMechanismOn`: exact `IsDSICOn` and `IsIROn`
  equivalences for feasible-set embedding into `Mechanism ι X`.

## References

* [N. Nisan, *Introduction to mechanism design (for computer scientists)*][Nisan2007]
-/

public section

namespace Cslib.GameTheory

namespace Mechanism

variable {ι Ω : Type*}

/-- **Single-parameter IR is IR on linear valuations**: `(M.toSingleParameter x).IsIR` holds
if and only if `M` is individually rational on `linearDomain x`. -/
theorem isIR_toSingleParameter_iff {M : Mechanism ι Ω} {x : Ω → ι → ℝ} :
    (M.toSingleParameter x).IsIR ↔ M.IsIROn (linearDomain x) := by
  constructor
  · intro h i B hB
    simp only [linearDomain, Set.mem_image, Set.mem_Ici] at hB
    choose c hc hcB using hB
    obtain rfl : linearProfile x c = B := funext hcB
    exact h i c hc
  · intro h i b hb
    exact h i (linearProfile x b) fun j => linearValuation_mem_linearDomain x j (hb j)

end Mechanism

/-! ### Feasible-set embedding `SingleParameter.Mechanism → Mechanism ι X` -/

namespace SingleParameter

variable {ι : Type*}

private theorem linearValuation_subtype_injective {X : Set (ι → ℝ)} {i : ι}
    (hX : ∃ ω ∈ X, ω i ≠ 0) :
    Function.Injective (GameTheory.Mechanism.linearValuation (Subtype.val : X → ι → ℝ) i) := by
  obtain ⟨ω, hω, hne⟩ := hX
  intro v₁ v₂ h
  exact mul_right_cancel₀ hne (congrFun h ⟨ω, hω⟩)

open Classical in
/-- Extract a nonnegative scalar bid from a valuation `u : X → ℝ` on a feasible set
`X : Set (ι → ℝ)`, returning `0` off `Mechanism.linearDomain Subtype.val i`. -/
noncomputable def extractBid (X : Set (ι → ℝ)) (i : ι) (u : X → ℝ) : ℝ :=
  if h : ∃ v, 0 ≤ v ∧ GameTheory.Mechanism.linearValuation Subtype.val i v = u then
    Classical.choose h
  else 0

theorem extractBid_nonneg (X : Set (ι → ℝ)) (i : ι) (u : X → ℝ) :
    0 ≤ extractBid X i u := by
  unfold extractBid
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact le_rfl

theorem extractBid_linearValuation {X : Set (ι → ℝ)} {i : ι} (hX : ∃ ω ∈ X, ω i ≠ 0)
    {v : ℝ} (hv : 0 ≤ v) :
    extractBid X i (GameTheory.Mechanism.linearValuation (Subtype.val : X → ι → ℝ) i v) = v := by
  have hex : ∃ w, 0 ≤ w ∧
      GameTheory.Mechanism.linearValuation (Subtype.val : X → ι → ℝ) i w =
        GameTheory.Mechanism.linearValuation (Subtype.val : X → ι → ℝ) i v := ⟨v, hv, rfl⟩
  unfold extractBid
  rw [dite_eq_left hex]
  exact linearValuation_subtype_injective hX (Classical.choose_spec hex).2

namespace Mechanism

/-- A single-parameter mechanism is individually rational iff its `toMechanism` embedding on
`ι → ℝ` is individually rational on `Mechanism.linearDomain id`. -/
theorem isIR_iff_isIROn_toMechanism [DecidableEq ι] {M : Mechanism ι} :
    M.IsIR ↔ M.toMechanism.IsIROn (GameTheory.Mechanism.linearDomain id) := by
  conv_lhs => rw [← toSingleParameter_toMechanism M]
  exact GameTheory.Mechanism.isIR_toSingleParameter_iff

/-- Embed a single-parameter mechanism `M` whose allocations on nonnegative bids belong to a
feasible set `X : Set (ι → ℝ)` directly into `Cslib.GameTheory.Mechanism ι X`. -/
noncomputable def toMechanismOn {X : Set (ι → ℝ)} (M : Mechanism ι)
    (hx : ∀ b, 0 ≤ b → M.allocation b ∈ X) : GameTheory.Mechanism ι X where
  outcome u := ⟨M.allocation (fun j => extractBid X j (u j)),
    hx _ fun j => extractBid_nonneg X j (u j)⟩
  payment u i := M.payment (fun j => extractBid X j (u j)) i

@[simp]
theorem toMechanismOn_outcome {X : Set (ι → ℝ)} (M : Mechanism ι)
    (hx : ∀ b, 0 ≤ b → M.allocation b ∈ X) (u : ι → X → ℝ) :
    ((M.toMechanismOn hx).outcome u : ι → ℝ) = M.allocation fun j => extractBid X j (u j) := by
  rfl

@[simp]
theorem toMechanismOn_payment {X : Set (ι → ℝ)} (M : Mechanism ι)
    (hx : ∀ b, 0 ≤ b → M.allocation b ∈ X) (u : ι → X → ℝ) (i : ι) :
    (M.toMechanismOn hx).payment u i = M.payment (fun j => extractBid X j (u j)) i := by
  rfl

theorem toMechanismOn_toSingleParameter_eq {X : Set (ι → ℝ)} (M : Mechanism ι)
    (hx : ∀ b, 0 ≤ b → M.allocation b ∈ X) (hX : ∀ i, ∃ ω ∈ X, ω i ≠ 0)
    {b : ι → ℝ} (hb : 0 ≤ b) :
    ((M.toMechanismOn hx).toSingleParameter Subtype.val).allocation b = M.allocation b ∧
      ((M.toMechanismOn hx).toSingleParameter Subtype.val).payment b = M.payment b := by
  have hext : (fun j => extractBid X j
      (GameTheory.Mechanism.linearProfile Subtype.val b j)) = b :=
    funext fun j => extractBid_linearValuation (hX j) (hb j)
  exact ⟨by simp only [GameTheory.Mechanism.toSingleParameter, toMechanismOn, hext],
    by simp only [GameTheory.Mechanism.toSingleParameter, toMechanismOn, hext]⟩

/-- **Feasible-set DSIC equivalence**: when every bidder can receive a nonzero allocation in `X`,
`M` is DSIC if and only if `M.toMechanismOn hx` is DSIC on
`Mechanism.linearDomain Subtype.val`. -/
theorem isDSIC_iff_isDSICOn_toMechanismOn [DecidableEq ι] {X : Set (ι → ℝ)} {M : Mechanism ι}
    (hx : ∀ b, 0 ≤ b → M.allocation b ∈ X) (hX : ∀ i, ∃ ω ∈ X, ω i ≠ 0) :
    M.IsDSIC ↔ (M.toMechanismOn hx).IsDSICOn (GameTheory.Mechanism.linearDomain Subtype.val) := by
  rw [← GameTheory.Mechanism.isDSIC_toSingleParameter_iff]
  exact ⟨fun h => h.congr fun b hb =>
      ⟨(toMechanismOn_toSingleParameter_eq M hx hX hb).1.symm,
        (toMechanismOn_toSingleParameter_eq M hx hX hb).2.symm⟩,
    fun h => h.congr fun b hb => toMechanismOn_toSingleParameter_eq M hx hX hb⟩

/-- **Feasible-set IR equivalence**: when every bidder can receive a nonzero allocation in `X`,
`M` is individually rational if and only if `M.toMechanismOn hx` is individually rational on
`Mechanism.linearDomain Subtype.val`. -/
theorem isIR_iff_isIROn_toMechanismOn {X : Set (ι → ℝ)} {M : Mechanism ι}
    (hx : ∀ b, 0 ≤ b → M.allocation b ∈ X) (hX : ∀ i, ∃ ω ∈ X, ω i ≠ 0) :
    M.IsIR ↔ (M.toMechanismOn hx).IsIROn (GameTheory.Mechanism.linearDomain Subtype.val) := by
  rw [← GameTheory.Mechanism.isIR_toSingleParameter_iff]
  exact ⟨fun h => h.congr fun b hb =>
      ⟨(toMechanismOn_toSingleParameter_eq M hx hX hb).1.symm,
        (toMechanismOn_toSingleParameter_eq M hx hX hb).2.symm⟩,
    fun h => h.congr fun b hb => toMechanismOn_toSingleParameter_eq M hx hX hb⟩

end Mechanism

end SingleParameter

end Cslib.GameTheory
