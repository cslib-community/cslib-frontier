/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.StableMatching.Incomplete.RuralHospitals
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.OrderDual
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic

/-!
# The lattice of stable matchings with incomplete preference lists

This module extends the Conway–Knuth distributive lattice theorem
(`CslibFrontier.Algorithms.Lean.StableMatching.Lattice`, [Knuth1976], [RothSotomayor1990]) to
two-sided matching markets with **strict, possibly incomplete preference lists and unequal sides**
(`IncompleteInstance m n`).

By the rural hospitals theorem (`IncompleteInstance.unmatched_eq_of_isStable`), every two stable
partial matchings `μ` and `ν` match the exact same set of proposers and the exact same set of
receivers. Letting each proposer choose the strictly better of `μ p` and `ν p` defines an injective
partial map `propBest` (matching the exact same set of proposers, and hence, by the finite
cardinality equality of `PartialMatching.card_matchedReceivers`, the exact same set of receivers).
The resulting matching `propJoin` is stable, gives every proposer the better of its two partners,
and gives every receiver the worse of its two partners (`recvRank_propJoin`). Dually, `propMeet`
(computed in `I.swap`) gives every proposer the worse and every receiver the better partner.

We package this as a `DistribLattice` and `BoundedOrder` on `IncompleteInstance.Stable I`, with
`⊤ = I.deferredAcceptance` and `⊥ = I.receiverDeferredAcceptance`.

## Main definitions

* `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.propBest`: proposer-wise best outcome of
  two partial matchings.
* `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.propJoin`,
  `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.propMeet`: join and meet of two stable
  partial matchings.
* `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.Stable`: subtype of stable partial
  matchings with `DistribLattice` and `BoundedOrder` instances.

## Main results

* `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.isStable_propJoin`,
  `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.propRank_propJoin`,
  `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.recvRank_propJoin`: `propJoin` is
  stable; proposers receive `min` and receivers receive `max` of their partner ranks.
* `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.isStable_propMeet`,
  `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.propRank_propMeet`,
  `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.recvRank_propMeet`: dual properties for
  `propMeet`.
* `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.Stable.le_iff`,
  `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.Stable.coe_top`,
  `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.Stable.coe_bot`.

## References

* [Knuth1976]
* [GusfieldIrving1989]
* [RothSotomayor1990]
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

namespace IncompleteInstance

open PartialMatching

variable {m n : ℕ} (I : IncompleteInstance m n)

/-- Each proposer selects the better of its outcomes in `μ` and `ν` (`min` rank). -/
@[expose] def propBest (μ ν : PartialMatching m n) (p : Fin m) : Option (Fin n) :=
  if I.propRank p (μ p) ≤ I.propRank p (ν p) then μ p else ν p

theorem propRank_propBest (μ ν : PartialMatching m n) (p : Fin m) :
    I.propRank p (I.propBest μ ν p) = min (I.propRank p (μ p)) (I.propRank p (ν p)) := by
  unfold propBest
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

theorem propBest_mem (μ ν : PartialMatching m n) (p : Fin m) :
    I.propBest μ ν p = μ p ∨ I.propBest μ ν p = ν p := by
  unfold propBest
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem propBest_cross {μ ν : PartialMatching m n} (hμ : I.IsStable μ) (hν : I.IsStable ν)
    {p q : Fin m} {r : Fin n} (hμp : μ p = some r) (hνq : ν q = some r)
    (hp : I.propRank p (μ p) ≤ I.propRank p (ν p))
    (hq : I.propRank q (ν q) ≤ I.propRank q (μ q)) : p = q := by
  by_contra hpq
  have hp_acc := (hμ.1 p r hμp).1
  have hq_acc := (hν.1 q r hνq).1
  have hp_r_acc := (hμ.1 p r hμp).2
  have hq_r_acc := (hν.1 q r hνq).2
  have hp_lt : I.propRank p (some r) < I.propRank p (ν p) := by
    refine lt_of_le_of_ne (hμp ▸ hp) fun heq => ?_
    have hνp : ν p = some r := I.eq_of_propRank_eq hp_acc heq
    exact hpq (ν.inj hνp hνq)
  have hq_lt : I.propRank q (some r) < I.propRank q (μ q) := by
    refine lt_of_le_of_ne (hνq ▸ hq) fun heq => ?_
    have hμq : μ q = some r := I.eq_of_propRank_eq hq_acc heq
    exact hpq (μ.inj hμp hμq)
  have hμs : μ.symm r = some p := μ.eq_some_iff.2 hμp
  have hνs : ν.symm r = some q := ν.eq_some_iff.2 hνq
  rcases lt_trichotomy (I.recvRank r (some p)) (I.recvRank r (some q)) with hr | hr | hr
  · exact hν.2 p r ⟨hp_lt, hνs ▸ hr⟩
  · exact hpq (Option.some_injective _ (I.eq_of_recvRank_eq hp_r_acc hr)).symm
  · exact hμ.2 q r ⟨hq_lt, hμs ▸ hr⟩

theorem propBest_injOn {μ ν : PartialMatching m n} (hμ : I.IsStable μ)
    (hν : I.IsStable ν) :
    ∀ p q r, I.propBest μ ν p = some r → I.propBest μ ν q = some r → p = q := by
  intro p q r hp hq
  unfold propBest at hp hq
  split_ifs at hp hq with h1 h2 h2
  · exact μ.inj hp hq
  · exact I.propBest_cross hμ hν hp hq h1 (le_of_not_ge h2)
  · exact (I.propBest_cross hμ hν hq hp h2 (le_of_not_ge h1)).symm
  · exact ν.inj hp hq

/-- Proposer-wise best (`join`) of two stable partial matchings. -/
@[expose] def propJoin {μ ν : PartialMatching m n} (hμ : I.IsStable μ) (hν : I.IsStable ν) :
    PartialMatching m n :=
  PartialMatching.ofInjOn (I.propBest μ ν) (I.propBest_injOn hμ hν)

variable {I}

/-- In `propJoin`, every proposer gets the better of its two outcomes. -/
theorem propRank_propJoin {μ ν : PartialMatching m n} (hμ : I.IsStable μ) (hν : I.IsStable ν)
    (p : Fin m) :
    I.propRank p (I.propJoin hμ hν p) = min (I.propRank p (μ p)) (I.propRank p (ν p)) :=
  I.propRank_propBest μ ν p

private theorem isIndividuallyRational_propJoin {μ ν : PartialMatching m n}
    (hμ : I.IsStable μ) (hν : I.IsStable ν) :
    I.IsIndividuallyRational (I.propJoin hμ hν) := by
  intro p r hr
  change I.propBest μ ν p = some r at hr
  rcases I.propBest_mem μ ν p with h | h
  · exact hμ.1 p r (h.symm.trans hr)
  · exact hν.1 p r (h.symm.trans hr)

private theorem matchedProposers_propJoin {μ ν : PartialMatching m n}
    (hμ : I.IsStable μ) (hν : I.IsStable ν) :
    matchedProposers (I.propJoin hμ hν) = matchedProposers μ := by
  have hsame := I.matchedProposers_eq_of_isStable hμ hν
  ext p
  simp only [mem_matchedProposers]
  change (I.propBest μ ν p).isSome ↔ (μ p).isSome
  rcases I.propBest_mem μ ν p with h | h
  · rw [h]
  · rw [h]
    have := congrArg (p ∈ ·) hsame
    simp only [mem_matchedProposers, eq_iff_iff] at this
    exact this.symm

private theorem matchedReceivers_propJoin {μ ν : PartialMatching m n}
    (hμ : I.IsStable μ) (hν : I.IsStable ν) :
    matchedReceivers (I.propJoin hμ hν) = matchedReceivers μ := by
  have hsameR := I.matchedReceivers_eq_of_isStable hμ hν
  have hsub : matchedReceivers (I.propJoin hμ hν) ⊆ matchedReceivers μ := by
    intro r hr
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (mem_matchedReceivers.1 hr)
    have hpr : I.propBest μ ν p = some r := (I.propJoin hμ hν).eq_some_iff.1 hp
    rcases I.propBest_mem μ ν p with h | h
    · exact mem_matchedReceivers.2 (by rw [μ.eq_some_iff.2 (h.symm.trans hpr)]; rfl)
    · rw [hsameR]
      exact mem_matchedReceivers.2 (by rw [ν.eq_some_iff.2 (h.symm.trans hpr)]; rfl)
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [card_matchedReceivers, card_matchedReceivers, matchedProposers_propJoin hμ hν]

private theorem symm_eq_none_of_propJoin {μ ν : PartialMatching m n} (hμ : I.IsStable μ)
    (hν : I.IsStable ν) {r : Fin n} (hj : (I.propJoin hμ hν).symm r = none) :
    μ.symm r = none := by
  have hnot : r ∉ matchedReceivers (I.propJoin hμ hν) := by simp [mem_matchedReceivers, hj]
  rw [matchedReceivers_propJoin hμ hν] at hnot
  cases h : μ.symm r with
  | none => rfl
  | some _ => exact absurd (mem_matchedReceivers.2 (by simp [h])) hnot

/-- The proposer-wise join of two stable partial matchings is stable. -/
theorem isStable_propJoin {μ ν : PartialMatching m n} (hμ : I.IsStable μ) (hν : I.IsStable ν) :
    I.IsStable (I.propJoin hμ hν) := by
  refine ⟨isIndividuallyRational_propJoin hμ hν, fun p r ⟨hp, hr⟩ => ?_⟩
  rw [propRank_propJoin, lt_min_iff] at hp
  cases hj : (I.propJoin hμ hν).symm r with
  | none =>
    exact hμ.2 p r ⟨hp.1, by rw [symm_eq_none_of_propJoin hμ hν hj]; rwa [hj] at hr⟩
  | some q =>
    have hqr : I.propBest μ ν q = some r := (I.propJoin hμ hν).eq_some_iff.1 hj
    rcases I.propBest_mem μ ν q with h | h
    · have hμq : μ q = some r := h.symm.trans hqr
      have hμr : μ.symm r = some q := μ.eq_some_iff.2 hμq
      exact hμ.2 p r ⟨hp.1, by rwa [hμr, ← hj]⟩
    · have hνq : ν q = some r := h.symm.trans hqr
      have hνr : ν.symm r = some q := ν.eq_some_iff.2 hνq
      exact hν.2 p r ⟨hp.2, by rwa [hνr, ← hj]⟩

/-- In `propJoin`, every receiver gets the worse of its two outcomes. -/
theorem recvRank_propJoin {μ ν : PartialMatching m n} (hμ : I.IsStable μ) (hν : I.IsStable ν)
    (r : Fin n) :
    I.recvRank r ((I.propJoin hμ hν).symm r) =
      max (I.recvRank r (μ.symm r)) (I.recvRank r (ν.symm r)) := by
  have hir := isIndividuallyRational_propJoin hμ hν
  have h1 : I.recvRank r (μ.symm r) ≤ I.recvRank r ((I.propJoin hμ hν).symm r) :=
    I.recvRank_le_of_propRank_le hir hμ
      (fun p => (propRank_propJoin hμ hν p).trans_le (min_le_left _ _)) r
  have h2 : I.recvRank r (ν.symm r) ≤ I.recvRank r ((I.propJoin hμ hν).symm r) :=
    I.recvRank_le_of_propRank_le hir hν
      (fun p => (propRank_propJoin hμ hν p).trans_le (min_le_right _ _)) r
  refine le_antisymm ?_ (max_le h1 h2)
  cases hj : (I.propJoin hμ hν).symm r with
  | none => rw [← symm_eq_none_of_propJoin hμ hν hj]; exact le_max_left _ _
  | some q =>
    have hqr : I.propBest μ ν q = some r := (I.propJoin hμ hν).eq_some_iff.1 hj
    rcases I.propBest_mem μ ν q with h | h
    · have hμr : μ.symm r = some q := μ.eq_some_iff.2 (h.symm.trans hqr)
      rw [← hμr]; exact le_max_left _ _
    · have hνr : ν.symm r = some q := ν.eq_some_iff.2 (h.symm.trans hqr)
      rw [← hνr]; exact le_max_right _ _

variable (I) in
/-- Proposer-wise worst (`meet`) of two stable partial matchings: computed as the receiver-wise
join in `I.swap`. -/
@[expose] def propMeet {μ ν : PartialMatching m n} (hμ : I.IsStable μ) (hν : I.IsStable ν) :
    PartialMatching m n :=
  (I.swap.propJoin ((I.isStable_swap_iff μ).2 hμ) ((I.isStable_swap_iff ν).2 hν)).symm

/-- The proposer-wise meet of two stable partial matchings is stable. -/
theorem isStable_propMeet {μ ν : PartialMatching m n} (hμ : I.IsStable μ) (hν : I.IsStable ν) :
    I.IsStable (I.propMeet hμ hν) :=
  (I.isStable_swap_iff (I.propMeet hμ hν)).1
    (isStable_propJoin ((I.isStable_swap_iff μ).2 hμ) ((I.isStable_swap_iff ν).2 hν))

/-- In `propMeet`, every proposer gets the worse of its two outcomes. -/
theorem propRank_propMeet {μ ν : PartialMatching m n} (hμ : I.IsStable μ) (hν : I.IsStable ν)
    (p : Fin m) :
    I.propRank p (I.propMeet hμ hν p) = max (I.propRank p (μ p)) (I.propRank p (ν p)) := by
  have h := recvRank_propJoin ((I.isStable_swap_iff μ).2 hμ) ((I.isStable_swap_iff ν).2 hν) p
  simp only [swap_recvRank, PEquiv.symm_symm] at h
  exact h

/-- In `propMeet`, every receiver gets the better of its two outcomes. -/
theorem recvRank_propMeet {μ ν : PartialMatching m n} (hμ : I.IsStable μ) (hν : I.IsStable ν)
    (r : Fin n) :
    I.recvRank r ((I.propMeet hμ hν).symm r) =
      min (I.recvRank r (μ.symm r)) (I.recvRank r (ν.symm r)) := by
  have h := propRank_propJoin ((I.isStable_swap_iff μ).2 hμ) ((I.isStable_swap_iff ν).2 hν) r
  simp only [swap_propRank] at h
  rw [propMeet, PEquiv.symm_symm]
  exact h

variable (I) in
/-- The type of stable partial matchings of `I`, carrying the Conway–Knuth distributive lattice
and bounded order with `μ ≤ ν` iff every proposer weakly prefers its outcome in `ν`. -/
@[expose] def Stable : Type := {μ : PartialMatching m n // I.IsStable μ}

namespace Stable

/-- The proposers' ranks of their outcomes, in the order dual to `ℕ` (so that a better partner is
larger). Pulls back a `DistribLattice` structure injectively via individual rationality. -/
@[expose] def propRanks (μ : I.Stable) : Fin m → ℕᵒᵈ :=
  fun p => OrderDual.toDual (I.propRank p (μ.1 p))

theorem propRanks_injective : Function.Injective (propRanks (I := I)) := by
  intro μ ν h
  refine Subtype.ext (PEquiv.ext fun p => ?_)
  exact I.eq_of_propRank_eq_of_isIndividuallyRational μ.2.1 ν.2.1
    (OrderDual.toDual.injective (congrFun h p))

instance : LE I.Stable := ⟨fun μ ν => μ.propRanks ≤ ν.propRanks⟩

instance : LT I.Stable := ⟨fun μ ν => μ.propRanks < ν.propRanks⟩

instance : Max I.Stable := ⟨fun μ ν => ⟨I.propJoin μ.2 ν.2, isStable_propJoin μ.2 ν.2⟩⟩

instance : Min I.Stable := ⟨fun μ ν => ⟨I.propMeet μ.2 ν.2, isStable_propMeet μ.2 ν.2⟩⟩

@[simp] theorem coe_sup (μ ν : I.Stable) : (μ ⊔ ν).1 = I.propJoin μ.2 ν.2 := rfl

@[simp] theorem coe_inf (μ ν : I.Stable) : (μ ⊓ ν).1 = I.propMeet μ.2 ν.2 := rfl

/-- `μ ≤ ν` exactly when every proposer weakly prefers its outcome in `ν`. -/
theorem le_iff {μ ν : I.Stable} :
    μ ≤ ν ↔ ∀ p, I.propRank p (ν.1 p) ≤ I.propRank p (μ.1 p) :=
  Pi.le_def

/-- **Conway–Knuth theorem for incomplete lists**: the set of stable partial matchings of
`IncompleteInstance m n` forms a distributive lattice ([Knuth1976]; [RothSotomayor1990]). -/
instance : DistribLattice I.Stable :=
  Function.Injective.distribLattice propRanks propRanks_injective Iff.rfl Iff.rfl
    (fun μ ν => funext fun p => by
      simp only [propRanks, coe_sup, propRank_propJoin]
      rfl)
    (fun μ ν => funext fun p => by
      simp only [propRanks, coe_inf, propRank_propMeet]
      rfl)

instance : BoundedOrder I.Stable where
  top := ⟨I.deferredAcceptance, I.isStable_deferredAcceptance⟩
  le_top μ := le_iff.2 fun p => I.propRank_deferredAcceptance_le_of_isStable μ.2 p
  bot := ⟨I.receiverDeferredAcceptance, I.isStable_receiverDeferredAcceptance⟩
  bot_le μ := le_iff.2 fun p => I.isProposerPessimal_receiverDeferredAcceptance.2 μ.1 μ.2 p

/-- The top stable matching is proposer-proposing deferred acceptance. -/
@[simp] theorem coe_top : (⊤ : I.Stable).1 = I.deferredAcceptance := rfl

/-- The bottom stable matching is receiver-proposing deferred acceptance. -/
@[simp] theorem coe_bot : (⊥ : I.Stable).1 = I.receiverDeferredAcceptance := rfl

end Stable

end IncompleteInstance

end Cslib.Algorithms.Lean.StableMatching
