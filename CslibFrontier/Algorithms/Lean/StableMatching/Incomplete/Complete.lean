/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.StableMatching.DeferredAcceptance
public import CslibFrontier.Algorithms.Lean.StableMatching.Incomplete.DeferredAcceptance
import CslibFrontier.Tactic.FinsetCard
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup

/-!
# Complete preference lists as a special case

A market `I : Instance n` with strict complete preferences is the market
`I.toIncompleteInstance : IncompleteInstance n n` in which every agent lists all agents of the
other side, in its order of preference. This module relates the two developments: ranks agree,
a perfect matching `μ` is stable for `I` exactly when the partial matching `μ.toPEquiv` is stable
for `I.toIncompleteInstance`, every stable matching of `I.toIncompleteInstance` is perfect, and
the two implementations of deferred acceptance produce the same matching.

## Main definitions

* `Instance.toIncompleteInstance`: a complete-list market as a market with incomplete lists.

## Main results

* `Instance.isStable_toIncompleteInstance_iff`: `μ.toPEquiv` is stable for
  `I.toIncompleteInstance` iff `μ` is stable for `I`.
* `Instance.isStable_toIncompleteInstance_iff_exists`: the stable matchings of
  `I.toIncompleteInstance` are exactly the `μ.toPEquiv` for stable perfect matchings `μ` of `I`;
  in particular they match every agent.
* `Instance.deferredAcceptance_toIncompleteInstance`: deferred acceptance for incomplete lists
  agrees with deferred acceptance for complete lists.
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- A complete-list market as a market with incomplete lists: every agent lists every agent of
the other side, from most to least preferred. -/
@[expose] def toIncompleteInstance : IncompleteInstance n n where
  propPref p := List.ofFn (I.propPref p)
  recvPref r := List.ofFn (I.recvPref r)

theorem mem_toIncompleteInstance_propPref (p r : Fin n) :
    r ∈ I.toIncompleteInstance.propPref p :=
  List.mem_ofFn.2 ⟨_, (I.propPref p).apply_symm_apply r⟩

theorem mem_toIncompleteInstance_recvPref (r p : Fin n) :
    p ∈ I.toIncompleteInstance.recvPref r :=
  List.mem_ofFn.2 ⟨_, (I.recvPref r).apply_symm_apply p⟩

/-- In the list of a permutation, an agent's position is its rank. -/
private theorem idxOf_ofFn_perm (σ : Equiv.Perm (Fin n)) (a : Fin n) :
    (List.ofFn σ).idxOf a = (σ.symm a).val := by
  simpa [σ.apply_symm_apply a] using
    (List.nodup_ofFn.2 σ.injective).idxOf_getElem (σ.symm a).val (by simp)

theorem toIncompleteInstance_propRank_some (p r : Fin n) :
    I.toIncompleteInstance.propRank p (some r) = (I.propRank p r).val :=
  idxOf_ofFn_perm _ r

theorem toIncompleteInstance_recvRank_some (r p : Fin n) :
    I.toIncompleteInstance.recvRank r (some p) = (I.recvRank r p).val :=
  idxOf_ofFn_perm _ p

theorem toIncompleteInstance_propRank_none (p : Fin n) :
    I.toIncompleteInstance.propRank p none = n :=
  List.length_ofFn

theorem toIncompleteInstance_recvRank_none (r : Fin n) :
    I.toIncompleteInstance.recvRank r none = n :=
  List.length_ofFn

/-- Exchanging the sides commutes with forgetting completeness. -/
theorem toIncompleteInstance_swap : I.swap.toIncompleteInstance = I.toIncompleteInstance.swap :=
  rfl

/-- A perfect matching is stable for the complete-list market exactly when it is stable as a
partial matching for the same market viewed with incomplete lists. -/
theorem isStable_toIncompleteInstance_iff (μ : Matching n) :
    I.toIncompleteInstance.IsStable μ.toPEquiv ↔ I.IsStable μ := by
  have hIR : I.toIncompleteInstance.IsIndividuallyRational μ.toPEquiv := fun p r _ =>
    ⟨I.mem_toIncompleteInstance_propPref p r, I.mem_toIncompleteInstance_recvPref r p⟩
  simp only [IncompleteInstance.IsStable, hIR, true_and, IncompleteInstance.IsBlockingPair,
    Equiv.toPEquiv_apply, ← Equiv.toPEquiv_symm, toIncompleteInstance_propRank_some,
    toIncompleteInstance_recvRank_some, IsStable, isBlockingPair_iff, Fin.lt_def]

/-- In the complete-list market every stable partial matching matches every proposer. -/
theorem isSome_of_isStable_toIncompleteInstance {ν : PartialMatching n n}
    (hν : I.toIncompleteInstance.IsStable ν) (p : Fin n) : (ν p).isSome := by
  by_contra hp
  rw [Option.not_isSome_iff_eq_none] at hp
  obtain ⟨r, hr⟩ : ∃ r, r ∉ PartialMatching.matchedReceivers ν := by
    finset_card [PartialMatching.card_matchedReceivers ν,
      show p ∉ PartialMatching.matchedProposers ν by
        simp [PartialMatching.mem_matchedProposers, hp]]
  rw [PartialMatching.mem_matchedReceivers, Option.not_isSome_iff_eq_none] at hr
  refine hν.2 p r ⟨?_, ?_⟩
  · rw [hp, toIncompleteInstance_propRank_some, toIncompleteInstance_propRank_none]
    exact (I.propRank p r).isLt
  · rw [hr, toIncompleteInstance_recvRank_some, toIncompleteInstance_recvRank_none]
    exact (I.recvRank r p).isLt

/-- The stable matchings of the complete-list market viewed with incomplete lists are exactly the
stable perfect matchings of the complete-list market. -/
theorem isStable_toIncompleteInstance_iff_exists (ν : PartialMatching n n) :
    I.toIncompleteInstance.IsStable ν ↔ ∃ μ : Matching n, I.IsStable μ ∧ μ.toPEquiv = ν := by
  constructor
  · intro hν
    have hsome := I.isSome_of_isStable_toIncompleteInstance hν
    let f : Fin n → Fin n := fun p => (ν p).get (hsome p)
    have hf : Function.Injective f := fun p q h =>
      ν.inj (b := f p) (Option.get_mem _) (h ▸ Option.get_mem _)
    have heq : (permOfInjective f hf).toPEquiv = ν :=
      PEquiv.ext fun p => Option.some_get (hsome p)
    exact ⟨permOfInjective f hf, (I.isStable_toIncompleteInstance_iff _).1 (heq.symm ▸ hν), heq⟩
  · rintro ⟨μ, hμ, rfl⟩
    exact (I.isStable_toIncompleteInstance_iff μ).2 hμ

/-- Deferred acceptance for incomplete lists, run on a complete-list market, computes the same
matching as deferred acceptance for complete lists. -/
theorem deferredAcceptance_toIncompleteInstance :
    I.toIncompleteInstance.deferredAcceptance = I.deferredAcceptance.toPEquiv := by
  refine ((I.toIncompleteInstance.isProposerOptimal_iff _).1 ⟨?_, fun ν hν p => ?_⟩).symm
  · exact (I.isStable_toIncompleteInstance_iff _).2 I.isStable_deferredAcceptance
  · obtain ⟨μ, hμ, rfl⟩ := (I.isStable_toIncompleteInstance_iff_exists ν).1 hν
    simp only [Equiv.toPEquiv_apply, toIncompleteInstance_propRank_some]
    exact I.propRank_deferredAcceptance_le hμ p

/-- Receiver-proposing deferred acceptance for incomplete lists agrees with the complete-list
version. -/
theorem receiverDeferredAcceptance_toIncompleteInstance :
    I.toIncompleteInstance.receiverDeferredAcceptance = I.receiverDeferredAcceptance.toPEquiv := by
  rw [IncompleteInstance.receiverDeferredAcceptance, ← toIncompleteInstance_swap,
    deferredAcceptance_toIncompleteInstance, receiverDeferredAcceptance, Equiv.toPEquiv_symm]

end Instance

end Cslib.Algorithms.Lean.StableMatching
