/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card

/-!
# Phase-specific Paxos quorums

`QuorumSystem` has separate prepare and accept families. Every prepare quorum intersects every
accept quorum; quorums in the same phase need not intersect. This is the quorum condition used by
Flexible Paxos [HowardMalkhiSpiegelman2017]. The operational safety proof in `Paxos.Basic` consumes
this interface directly.

`QuorumSystem.Supports` describes a live cohort containing a quorum for each phase, the condition
needed to start a ballot and complete it. `QuorumSystem.AvailableFor` instead allows different
failure families in the two phases, distinguishing leader-election availability from availability
after a leader has prepared its ballot.

The finite-set results in this module are original library formulations:

* `exists_thresholdQuorums_iff`: nonvacuous cardinality thresholds `qPrepare` and `qAccept` admit
  a quorum system exactly when their sum exceeds the number of acceptors.
* `thresholdQuorums_availableFor_iff`: exact phase-specific availability for each fault set.
* `exists_availableFor_iff`: two nonempty failure families admit available cross-intersecting
  quorum families exactly when no prepare failure set and accept failure set cover all acceptors.
* `exists_availableFor_card_iff`: the sharp asymmetric crash threshold
  `fPrepare + fAccept < Fintype.card P`.

These are quorum and availability statements, not assertions of unconditional asynchronous
protocol termination. Protocol liveness additionally needs its delivery and leader hypotheses.
-/

public section

namespace Cslib.Distributed.Paxos

/-- Two nonempty quorum families whose members intersect across phases. Same-phase intersection
is not required. Prepare quorums collect promises; accept quorums certify a chosen value. -/
structure QuorumSystem (P : Type*) [DecidableEq P] where
  /-- Quorums sufficient to finish the prepare phase. -/
  prepareQuorums : Finset (Finset P)
  /-- Quorums sufficient to finish the accept phase. -/
  acceptQuorums : Finset (Finset P)
  /-- At least one prepare quorum exists. -/
  prepare_nonempty : prepareQuorums.Nonempty
  /-- At least one accept quorum exists. -/
  accept_nonempty : acceptQuorums.Nonempty
  /-- Every prepare quorum intersects every accept quorum. -/
  inter_nonempty : ∀ Q₁ ∈ prepareQuorums, ∀ Q₂ ∈ acceptQuorums, (Q₁ ∩ Q₂).Nonempty

namespace QuorumSystem

variable {P : Type*} [DecidableEq P] (qs : QuorumSystem P)

/-- A prepare quorum is nonempty because it intersects an accept quorum. -/
theorem prepareQuorum_nonempty {Q : Finset P} (hQ : Q ∈ qs.prepareQuorums) : Q.Nonempty := by
  obtain ⟨A, hA⟩ := qs.accept_nonempty
  obtain ⟨p, hp⟩ := qs.inter_nonempty Q hQ A hA
  exact ⟨p, (Finset.mem_inter.mp hp).1⟩

/-- An accept quorum is nonempty because it intersects a prepare quorum. -/
theorem acceptQuorum_nonempty {Q : Finset P} (hQ : Q ∈ qs.acceptQuorums) : Q.Nonempty := by
  obtain ⟨A, hA⟩ := qs.prepare_nonempty
  obtain ⟨p, hp⟩ := qs.inter_nonempty A hA Q hQ
  exact ⟨p, (Finset.mem_inter.mp hp).2⟩

/-- A cohort supports both phases when it contains a prepare quorum and an accept quorum. -/
@[expose] def Supports (Q : Finset P) : Prop :=
  (∃ Q₁ ∈ qs.prepareQuorums, Q₁ ⊆ Q) ∧ (∃ Q₂ ∈ qs.acceptQuorums, Q₂ ⊆ Q)

/-- Supporting both phases is decidable by checking the two finite quorum families. -/
instance instDecidableSupports (Q : Finset P) : Decidable (qs.Supports Q) := by
  unfold Supports
  infer_instance

/-- A cohort supporting both phases contains at least one acceptor. -/
theorem Supports.nonempty {qs : QuorumSystem P} {Q : Finset P}
    (h : qs.Supports Q) : Q.Nonempty := by
  obtain ⟨Q₁, hQ₁, hsub⟩ := h.1
  exact (qs.prepareQuorum_nonempty hQ₁).mono hsub

/-- The union of a prepare quorum and an accept quorum supports both phases. -/
theorem supports_union {Q₁ Q₂ : Finset P}
    (h₁ : Q₁ ∈ qs.prepareQuorums) (h₂ : Q₂ ∈ qs.acceptQuorums) :
    qs.Supports (Q₁ ∪ Q₂) :=
  ⟨⟨Q₁, h₁, Finset.subset_union_left⟩, ⟨Q₂, h₂, Finset.subset_union_right⟩⟩

/-- Availability against possibly different failure families in the prepare and accept phases.
Each allowed fault set leaves some quorum of the corresponding phase entirely correct. -/
structure AvailableFor (prepareFaults acceptFaults : Set (Finset P)) : Prop where
  /-- Every prepare-phase fault set leaves a prepare quorum. -/
  prepare : ∀ F ∈ prepareFaults, ∃ Q ∈ qs.prepareQuorums, Disjoint Q F
  /-- Every accept-phase fault set leaves an accept quorum. -/
  accept : ∀ F ∈ acceptFaults, ∃ Q ∈ qs.acceptQuorums, Disjoint Q F

end QuorumSystem

section Thresholds

variable {P : Type*} [Fintype P] [DecidableEq P] {qPrepare qAccept : ℕ}

/-- All subsets meeting the respective cardinality thresholds form a phase-specific quorum
system when each threshold is feasible and their sum exceeds the number of acceptors. -/
@[expose] def thresholdQuorums (hPrepare : qPrepare ≤ Fintype.card P)
    (hAccept : qAccept ≤ Fintype.card P) (hInter : Fintype.card P < qPrepare + qAccept) :
    QuorumSystem P where
  prepareQuorums := Finset.univ.powerset.filter fun Q => qPrepare ≤ Q.card
  acceptQuorums := Finset.univ.powerset.filter fun Q => qAccept ≤ Q.card
  prepare_nonempty := ⟨Finset.univ, by simp [hPrepare]⟩
  accept_nonempty := ⟨Finset.univ, by simp [hAccept]⟩
  inter_nonempty := by
    intro Q₁ h₁ Q₂ h₂
    have h₁card := (Finset.mem_filter.mp h₁).2
    have h₂card := (Finset.mem_filter.mp h₂).2
    have hcard := Finset.card_inter_add_card_union Q₁ Q₂
    have hbound := Finset.card_le_univ (s := Q₁ ∪ Q₂)
    exact Finset.card_pos.mp (by omega)

/-- Membership in the prepare family is exactly the prepare cardinality threshold. -/
@[simp] theorem mem_thresholdQuorums_prepare_iff (hPrepare : qPrepare ≤ Fintype.card P)
    (hAccept : qAccept ≤ Fintype.card P) (hInter : Fintype.card P < qPrepare + qAccept)
    (Q : Finset P) :
    Q ∈ (thresholdQuorums hPrepare hAccept hInter).prepareQuorums ↔ qPrepare ≤ Q.card := by
  simp [thresholdQuorums]

/-- Membership in the accept family is exactly the accept cardinality threshold. -/
@[simp] theorem mem_thresholdQuorums_accept_iff (hPrepare : qPrepare ≤ Fintype.card P)
    (hAccept : qAccept ≤ Fintype.card P) (hInter : Fintype.card P < qPrepare + qAccept)
    (Q : Finset P) :
    Q ∈ (thresholdQuorums hPrepare hAccept hInter).acceptQuorums ↔ qAccept ≤ Q.card := by
  simp [thresholdQuorums]

/-- Exact cross-intersection criterion for feasible cardinality thresholds. Feasibility rules
out the vacuous case of an empty quorum family with a threshold larger than the universe. -/
theorem exists_thresholdQuorums_iff (hPrepare : qPrepare ≤ Fintype.card P)
    (hAccept : qAccept ≤ Fintype.card P) :
    (∃ qs : QuorumSystem P,
      (∀ Q, Q ∈ qs.prepareQuorums ↔ qPrepare ≤ Q.card) ∧
      (∀ Q, Q ∈ qs.acceptQuorums ↔ qAccept ≤ Q.card)) ↔
        Fintype.card P < qPrepare + qAccept := by
  constructor
  · rintro ⟨qs, hp, ha⟩
    by_contra! hle
    obtain ⟨Q, _, hcard⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset P)) (n := qPrepare) (by simpa using hPrepare)
    have hcomp : qAccept ≤ (Finset.univ \ Q).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcard]
      omega
    have hinter := qs.inter_nonempty Q ((hp Q).mpr (by omega))
      (Finset.univ \ Q) ((ha _).mpr hcomp)
    simp at hinter
  · intro hInter
    exact ⟨thresholdQuorums hPrepare hAccept hInter,
      mem_thresholdQuorums_prepare_iff hPrepare hAccept hInter,
      mem_thresholdQuorums_accept_iff hPrepare hAccept hInter⟩

omit [DecidableEq P] in
private theorem exists_disjoint_threshold_iff (q : ℕ) (F : Finset P) :
    (∃ Q : Finset P, q ≤ Q.card ∧ Disjoint Q F) ↔ q + F.card ≤ Fintype.card P := by
  classical
  constructor
  · rintro ⟨Q, hQ, hdisj⟩
    have hbound := Finset.card_le_univ (s := Q ∪ F)
    rw [Finset.card_union_of_disjoint hdisj] at hbound
    omega
  · intro h
    refine ⟨Finset.univ \ F, ?_, Finset.sdiff_disjoint⟩
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega

/-- A threshold family remains available precisely when each permitted fault set leaves enough
acceptors for that phase's threshold. The two phases may use different failure families. -/
theorem thresholdQuorums_availableFor_iff (hPrepare : qPrepare ≤ Fintype.card P)
    (hAccept : qAccept ≤ Fintype.card P) (hInter : Fintype.card P < qPrepare + qAccept)
    (prepareFaults acceptFaults : Set (Finset P)) :
    (thresholdQuorums hPrepare hAccept hInter).AvailableFor prepareFaults acceptFaults ↔
      (∀ F ∈ prepareFaults, qPrepare + F.card ≤ Fintype.card P) ∧
      (∀ F ∈ acceptFaults, qAccept + F.card ≤ Fintype.card P) := by
  have key {q : ℕ} {S : Finset (Finset P)} (hS : ∀ Q, Q ∈ S ↔ q ≤ Q.card) (B : Set (Finset P)) :
      (∀ F ∈ B, ∃ Q ∈ S, Disjoint Q F) ↔ ∀ F ∈ B, q + F.card ≤ Fintype.card P :=
    forall₂_congr fun F _ => by simp only [hS]; exact exists_disjoint_threshold_iff q F
  have kp := key (mem_thresholdQuorums_prepare_iff hPrepare hAccept hInter) prepareFaults
  have ka := key (mem_thresholdQuorums_accept_iff hPrepare hAccept hInter) acceptFaults
  exact ⟨fun h => ⟨kp.mp h.prepare, ka.mp h.accept⟩, fun h => ⟨kp.mpr h.1, ka.mpr h.2⟩⟩

/-- Equal strict-majority families recover classical Paxos: each quorum contains at least
`Fintype.card P - t` acceptors, with `2 * t < Fintype.card P`. -/
@[expose] def majorityQuorums {t : ℕ} (ht : 2 * t < Fintype.card P) : QuorumSystem P :=
  thresholdQuorums (qPrepare := Fintype.card P - t) (qAccept := Fintype.card P - t)
    (Nat.sub_le _ _) (Nat.sub_le _ _) (by omega)

/-- The classical prepare quorum cardinality test. -/
@[simp] theorem mem_majorityQuorums_prepare_iff {t : ℕ}
    (ht : 2 * t < Fintype.card P) (Q : Finset P) :
    Q ∈ (majorityQuorums ht).prepareQuorums ↔ Fintype.card P - t ≤ Q.card := by
  simp [majorityQuorums]

/-- The classical accept quorum cardinality test. -/
@[simp] theorem mem_majorityQuorums_accept_iff {t : ℕ}
    (ht : 2 * t < Fintype.card P) (Q : Finset P) :
    Q ∈ (majorityQuorums ht).acceptQuorums ↔ Fintype.card P - t ≤ Q.card := by
  simp [majorityQuorums]

end Thresholds

section Availability

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Two nonempty failure families admit an available phase-specific quorum system exactly when
no prepare fault set and accept fault set together cover the acceptor universe. Sufficiency uses
the complements of the respective fault sets as quorums. No closure assumption on either failure
family is needed. -/
theorem exists_availableFor_iff (prepareFaults acceptFaults : Set (Finset P))
    (hp : prepareFaults.Nonempty) (ha : acceptFaults.Nonempty) :
    (∃ qs : QuorumSystem P, qs.AvailableFor prepareFaults acceptFaults) ↔
      ∀ F₁ ∈ prepareFaults, ∀ F₂ ∈ acceptFaults, F₁ ∪ F₂ ≠ (Finset.univ : Finset P) := by
  classical
  constructor
  · rintro ⟨qs, hav⟩ F₁ hF₁ F₂ hF₂ hcover
    obtain ⟨Q₁, hQ₁, hd₁⟩ := hav.prepare F₁ hF₁
    obtain ⟨Q₂, hQ₂, hd₂⟩ := hav.accept F₂ hF₂
    obtain ⟨p, hp⟩ := qs.inter_nonempty Q₁ hQ₁ Q₂ hQ₂
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_inter.mp hp
    rcases Finset.mem_union.mp (hcover ▸ Finset.mem_univ p : p ∈ F₁ ∪ F₂) with hpF | hpF
    · exact Finset.disjoint_left.mp hd₁ hp₁ hpF
    · exact Finset.disjoint_left.mp hd₂ hp₂ hpF
  · intro hcover
    let complements (B : Set (Finset P)) : Finset (Finset P) :=
      (Finset.univ.powerset.filter (· ∈ B)).image (Finset.univ \ ·)
    have hmem (B : Set (Finset P)) (Q : Finset P) :
        Q ∈ complements B ↔ ∃ F ∈ B, Finset.univ \ F = Q := by
      simp [complements]
    let qs : QuorumSystem P :=
      { prepareQuorums := complements prepareFaults
        acceptQuorums := complements acceptFaults
        prepare_nonempty := by
          obtain ⟨F, hF⟩ := hp
          exact ⟨Finset.univ \ F, (hmem _ _).mpr ⟨F, hF, rfl⟩⟩
        accept_nonempty := by
          obtain ⟨F, hF⟩ := ha
          exact ⟨Finset.univ \ F, (hmem _ _).mpr ⟨F, hF, rfl⟩⟩
        inter_nonempty := by
          intro Q₁ hQ₁ Q₂ hQ₂
          obtain ⟨F₁, hF₁, rfl⟩ := (hmem _ _).mp hQ₁
          obtain ⟨F₂, hF₂, rfl⟩ := (hmem _ _).mp hQ₂
          have hnot : ¬ (Finset.univ : Finset P) ⊆ F₁ ∪ F₂ :=
            fun h => hcover F₁ hF₁ F₂ hF₂ (Finset.Subset.antisymm (Finset.subset_univ _) h)
          obtain ⟨p, hp⟩ := Finset.sdiff_nonempty.mpr hnot
          exact ⟨p, by simpa only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ,
            true_and, Finset.mem_union, not_or] using hp⟩ }
    refine ⟨qs, fun F hF => ?_, fun F hF => ?_⟩ <;>
      exact ⟨Finset.univ \ F, (hmem _ _).mpr ⟨F, hF, rfl⟩, Finset.sdiff_disjoint⟩

/-- Sharp asymmetric crash-availability threshold: prepare quorums can tolerate `fPrepare`
faults and accept quorums can tolerate `fAccept` faults exactly when their sum is below the
number of acceptors. In particular, requiring the same fault budget in both phases recovers
the strict-majority resilience bound. -/
theorem exists_availableFor_card_iff (fPrepare fAccept : ℕ) :
    (∃ qs : QuorumSystem P,
      qs.AvailableFor {F | F.card ≤ fPrepare} {F | F.card ≤ fAccept}) ↔
        fPrepare + fAccept < Fintype.card P := by
  rw [exists_availableFor_iff _ _ ⟨∅, by simp⟩ ⟨∅, by simp⟩]
  constructor
  · intro h
    by_contra! hle
    by_cases hp : Fintype.card P ≤ fPrepare
    · exact h Finset.univ (by simpa using hp) ∅ (by simp) (by simp)
    · obtain ⟨F, _, hF⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset P)) (n := fPrepare) (by simpa using le_of_not_ge hp)
      have hcomp : (Finset.univ \ F).card ≤ fAccept := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hF]
        omega
      exact h F (by simp [hF]) (Finset.univ \ F) hcomp (by simp)
  · intro h F₁ hF₁ F₂ hF₂ hcover
    have hcard := Finset.card_union_le F₁ F₂
    rw [hcover, Finset.card_univ] at hcard
    change F₁.card ≤ fPrepare at hF₁
    change F₂.card ≤ fAccept at hF₂
    omega

end Availability

end Cslib.Distributed.Paxos
