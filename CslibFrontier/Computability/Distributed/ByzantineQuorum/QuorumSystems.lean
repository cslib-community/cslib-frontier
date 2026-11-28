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
import CslibFrontier.Tactic.FinsetCard

/-!
# Threshold Byzantine Quorum Systems and Masking-Register Safety Step

This module formalizes uniform `b`-threshold Byzantine quorum systems and single-latest-write
unauthenticated masking-quorum register safety as a step toward `#7506` (`#3261`), after
[Malkhi and Reiter][MalkhiReiter1998] (*Distributed Computing* 11(4):203–213, 1998; preliminary
version in STOC 1997, pp. 569–578), rather than the general non-uniform fail-prone system
characterizations of that paper.

In [MalkhiReiter1998] §3.1 (p. 204), a quorum system over `U` is non-empty and pairwise
intersecting, while a fail-prone system `B ⊆ 2^U` is non-empty and subset-incomparable (`∀ B₁ B₂ ∈
B, B₁ ⊆ B₂ → B₁ = B₂`). Here `QuorumSystem P` carries an unbundled finite family
`quorums : Finset (Finset P)` (deriving nonemptiness and pairwise intersection from
`IsThresholdDisseminationQuorumSystem`), `IsAvailableFor qs B` requires every `F ∈ B` to miss some
quorum (`∃ Q ∈ qs.quorums, Disjoint Q F`), and `thresholdAdversary P b = {F | F.card ≤ b}`
downward-closes `{F | F.card = b}`:

* **Threshold dissemination quorum systems** (`IsThresholdDisseminationQuorumSystem b`, uniform
  `b`-threshold specialization of Definition 5.1, §5.1, p. 208): availability against `|F| ≤ b`
  together with `∀ Q₁ Q₂ ∈ quorums, ∀ F, |F| ≤ b → ((Q₁ ∩ Q₂) \ F).Nonempty` (equivalently
  `b + 1 ≤ (Q₁ ∩ Q₂).card`). Over `[Nonempty P]`, such a system exists if and only if
  `3 * b < Fintype.card P` (`exists_thresholdDisseminationQuorumSystem_iff`, threshold step after
  Corollary 5.5 and Example 5.6, p. 208).
* **Threshold masking quorum systems** (`IsThresholdMaskingQuorumSystem b`, uniform `b`-threshold
  specialization of Definition 4.1, §4, pp. 205–206): availability against `|F| ≤ b` together with
  `∀ Q₁ Q₂ ∈ quorums, ∀ F₁ F₂, |F₁| ≤ b → |F₂| ≤ b → (F₂ ∩ Q₂).card < ((Q₁ ∩ Q₂) \ F₁).card`
  (equivalently `2 * b + 1 ≤ (Q₁ ∩ Q₂).card`). Over `[Nonempty P]`, such a system exists if and
  only if `4 * b < Fintype.card P` (`exists_thresholdMaskingQuorumSystem_iff`, threshold step after
  Corollary 4.4 and Example 4.6, pp. 206–207).
* **Threshold strong-opaque quorum systems** (`IsThresholdStrongOpaqueQuorumSystem b`, formalizing
  the strict-inequality `>` variant of `O-Consistency1` noted in §5.2, p. 209 immediately below
  Definition 5.9, where correct up-to-date servers in `(Q₁ ∩ Q₂) \ F₁` strictly outnumber
  `((Q₂ \ Q₁) \ F₂).card + (Q₂ ∩ F₂).card` so timestamp-free majority voting suffices): over
  `[Nonempty P]`, such a system exists if and only if `5 * b < Fintype.card P`
  (`exists_thresholdStrongOpaqueQuorumSystem_iff`, contrasting with Definition 5.9, Example 5.11,
  and Theorem 5.12's weak-inequality `≥` opaque quorum systems, whose exact bound is `5 * b ≤ |P|`
  for `b > 0` and remains open under `#7506`).

Finally, we formalize a single-latest-write step for the unauthenticated timestamped register
protocol of §§3.2 and 4 (pp. 205–206): correct servers update their stored `TimestampedVal`
whenever a strictly newer timestamp arrives (`applyWrites`), faulty servers `u ∈ F` (`|F| ≤ b`)
return arbitrary forged `(ts, val)` pairs without cryptographic signatures, and a client reading
from any masking quorum `Q_r` filters to entries supported by at least `b + 1` servers in `Q_r`
(`maskingCandidates`) and selects the unique maximum surviving timestamp (`maskingRead`). General
fail-prone systems `B` (Theorems 4.3 and 5.4; Corollaries 4.4 and 5.5), weak-inequality opaque
quorums (Definition 5.9, Example 5.11, Theorem 5.12), load lower bounds (§3.3 Definition 3.1, §4
Theorem 4.5, §5.2 Theorem 5.14), and §6 faulty-client Echo/Ready updates remain open under `#7506`.

## Main definitions

* `Cslib.Distributed.ByzantineQuorum.QuorumSystem`: finite family of server subsets `quorums`.
* `Cslib.Distributed.ByzantineQuorum.QuorumSystem.IsAvailableFor`: availability against a
  fail-prone family `B : Set (Finset P)`.
* `Cslib.Distributed.ByzantineQuorum.thresholdAdversary`: uniform `b`-fault adversary
  `{F : Finset P | F.card ≤ b}`.
* `Cslib.Distributed.ByzantineQuorum.QuorumSystem.IsThresholdDisseminationQuorumSystem`: uniform
  `b`-threshold dissemination quorum system.
* `Cslib.Distributed.ByzantineQuorum.QuorumSystem.IsThresholdMaskingQuorumSystem`: uniform
  `b`-threshold masking quorum system.
* `Cslib.Distributed.ByzantineQuorum.QuorumSystem.IsThresholdStrongOpaqueQuorumSystem`: uniform
  `b`-threshold strong-inequality opaque quorum system.
* `Cslib.Distributed.ByzantineQuorum.thresholdQuorums`,
  `Cslib.Distributed.ByzantineQuorum.disseminationThresholdQuorums`,
  `Cslib.Distributed.ByzantineQuorum.maskingThresholdQuorums`,
  `Cslib.Distributed.ByzantineQuorum.strongOpaqueThresholdQuorums`: cardinality-threshold quorum
  constructions of sizes `⌈(|P| + b + 1)/2⌉`, `⌈(|P| + 2b + 1)/2⌉`, and `⌈(2|P| + 2b + 1)/3⌉`.
* `Cslib.Distributed.ByzantineQuorum.TimestampedVal`,
  `Cslib.Distributed.ByzantineQuorum.TimestampedVal.updateIfNewer`,
  `Cslib.Distributed.ByzantineQuorum.applyWrites`: server-side timestamped register storage and
  monotone-timestamp asynchronous write application.
* `Cslib.Distributed.ByzantineQuorum.maskingCandidates`,
  `Cslib.Distributed.ByzantineQuorum.maskingRead`: unauthenticated `(b + 1)`-multiplicity read
  filtering and maximum-timestamp value selection.

## Main results

* `QuorumSystem.IsThresholdStrongOpaqueQuorumSystem.toMasking`,
  `QuorumSystem.IsThresholdMaskingQuorumSystem.toDissemination`:
  containment hierarchy `StrongOpaque → Masking → Dissemination`.
* `QuorumSystem.isThresholdDisseminationQuorumSystem_iff_card_inter`,
  `QuorumSystem.isThresholdMaskingQuorumSystem_iff_card_inter`,
  `QuorumSystem.isThresholdStrongOpaqueQuorumSystem_iff_card`:
  exact quorum intersection and set-difference cardinality characterizations.
* `isThresholdDisseminationQuorumSystem_thresholdQuorums_sub`,
  `isThresholdDisseminationQuorumSystem_disseminationThresholdQuorums`,
  `isThresholdMaskingQuorumSystem_maskingThresholdQuorums`,
  `isThresholdStrongOpaqueQuorumSystem_strongOpaqueThresholdQuorums`:
  correctness of the `(|P| - b)` and minimal threshold quorum constructions when `3 * b < |P|`,
  `4 * b < |P|`, and `5 * b < |P|`.
* `Cslib.Distributed.ByzantineQuorum.exists_thresholdDisseminationQuorumSystem_iff`: over
  `[Nonempty P]`, a `b`-threshold dissemination quorum system exists iff `3 * b < Fintype.card P`.
* `Cslib.Distributed.ByzantineQuorum.exists_thresholdMaskingQuorumSystem_iff`: over `[Nonempty P]`,
  a `b`-threshold masking quorum system exists iff `4 * b < Fintype.card P`.
* `Cslib.Distributed.ByzantineQuorum.exists_thresholdStrongOpaqueQuorumSystem_iff`: over
  `[Nonempty P]`, a `b`-threshold strong-opaque quorum system exists iff `5 * b < Fintype.card P`.
* `Cslib.Distributed.ByzantineQuorum.maskingCandidates_sound`: every entry in
  `maskingCandidates b Q_r resp` was returned by at least one correct server `u ∈ Q_r \ F`.
* `Cslib.Distributed.ByzantineQuorum.threshold_masking_register_max_ts_eq`: `b`-threshold
  single-latest-write step showing any surviving candidate of maximum timestamp equals the latest
  completed write.
* `Cslib.Distributed.ByzantineQuorum.threshold_maskingRead_eq_some_latest_write`: `b`-threshold
  single-latest-write step showing `maskingRead` returns `some w.val` for the latest completed
  write `w` despite arbitrary unauthenticated Byzantine server responses on `F`.

## References

* [D. Malkhi, M. Reiter, *Byzantine quorum systems*][MalkhiReiter1998]
-/

public section

namespace Cslib.Distributed.ByzantineQuorum

open Finset

/-! ### Quorum systems and fail-prone availability -/

/-- A candidate quorum system over server universe `P`, represented by a finite family of server
subsets ([MalkhiReiter1998], §3.1, p. 204). -/
@[ext]
structure QuorumSystem (P : Type*) where
  /-- Finite family of quorum subsets of `P`. -/
  quorums : Finset (Finset P)
  deriving @[expose] DecidableEq

/-- Availability against a fail-prone adversary structure `B` ([MalkhiReiter1998], Definitions 4.1,
5.1, and 5.9, pp. 206–209): for every fault set `F ∈ B`, at least one quorum contains no faulty
server. -/
@[expose] def QuorumSystem.IsAvailableFor {P : Type*}
    (qs : QuorumSystem P) (B : Set (Finset P)) : Prop :=
  ∀ F ∈ B, ∃ Q ∈ qs.quorums, Disjoint Q F

/-- The uniform `b`-threshold adversary consisting of all subsets of `P` of size at most `b`. -/
@[expose] def thresholdAdversary (P : Type*) (b : ℕ) : Set (Finset P) :=
  {F : Finset P | F.card ≤ b}

@[simp]
theorem mem_thresholdAdversary_iff {P : Type*} {b : ℕ} {F : Finset P} :
    F ∈ thresholdAdversary P b ↔ F.card ≤ b := Iff.rfl

/-! ### Threshold dissemination, masking, and strong-opaque quorum systems -/

/-- Uniform `b`-threshold specialization of dissemination quorum systems (`#7506`; after
[MalkhiReiter1998], Definition 5.1, §5.1, p. 208, specialized to `thresholdAdversary P b`):
available against up to `b` faulty servers, and every pair of quorums intersects outside any faulty
set of size at most `b`. -/
@[expose] def QuorumSystem.IsThresholdDisseminationQuorumSystem {P : Type*} [DecidableEq P]
    (qs : QuorumSystem P) (b : ℕ) : Prop :=
  qs.IsAvailableFor (thresholdAdversary P b) ∧
    ∀ Q₁ ∈ qs.quorums, ∀ Q₂ ∈ qs.quorums, ∀ F : Finset P, F.card ≤ b → ((Q₁ ∩ Q₂) \ F).Nonempty

/-- Uniform `b`-threshold specialization of masking quorum systems (`#7506`; after
[MalkhiReiter1998], Definition 4.1, §4, pp. 205–206, specialized to `thresholdAdversary P b`):
available against up to `b` faulty servers, and for any two quorums `Q₁, Q₂` and fault sets
`F₁, F₂` of size at most `b`, `(Q₁ ∩ Q₂) \ F₁` strictly outnumbers `F₂ ∩ Q₂`. -/
@[expose] def QuorumSystem.IsThresholdMaskingQuorumSystem {P : Type*} [DecidableEq P]
    (qs : QuorumSystem P) (b : ℕ) : Prop :=
  qs.IsAvailableFor (thresholdAdversary P b) ∧
    ∀ Q₁ ∈ qs.quorums, ∀ Q₂ ∈ qs.quorums, ∀ F₁ F₂ : Finset P,
      F₁.card ≤ b → F₂.card ≤ b → (F₂ ∩ Q₂).card < ((Q₁ ∩ Q₂) \ F₁).card

/-- Uniform `b`-threshold strong-inequality opaque quorum system (`#7506`; formalizing the strict
`>` variant of `O-Consistency1` noted in [MalkhiReiter1998], §5.2, p. 209 immediately below
Definition 5.9, specialized to `thresholdAdversary P b`): available against up to `b` faulty
servers, and for any two quorums `Q₁, Q₂` and fault sets `F₁, F₂` of size at most `b`, correct
up-to-date servers `(Q₁ ∩ Q₂) \ F₁` strictly outnumber out-of-date correct servers `(Q₂ \ Q₁) \ F₂`
plus faulty servers `Q₂ ∩ F₂`. -/
@[expose] def QuorumSystem.IsThresholdStrongOpaqueQuorumSystem {P : Type*} [DecidableEq P]
    (qs : QuorumSystem P) (b : ℕ) : Prop :=
  qs.IsAvailableFor (thresholdAdversary P b) ∧
    ∀ Q₁ ∈ qs.quorums, ∀ Q₂ ∈ qs.quorums, ∀ F₁ F₂ : Finset P,
      F₁.card ≤ b → F₂.card ≤ b →
        ((Q₂ \ Q₁) \ F₂).card + (Q₂ ∩ F₂).card < ((Q₁ ∩ Q₂) \ F₁).card

namespace QuorumSystem

variable {P : Type*} [DecidableEq P] {qs : QuorumSystem P} {b : ℕ}

/-- Every `b`-threshold strong-opaque quorum system is a `b`-threshold masking quorum system. -/
theorem IsThresholdStrongOpaqueQuorumSystem.toMasking
    (h : qs.IsThresholdStrongOpaqueQuorumSystem b) :
    qs.IsThresholdMaskingQuorumSystem b := by
  refine ⟨h.1, fun Q₁ hQ₁ Q₂ hQ₂ F₁ F₂ hF₁ hF₂ => ?_⟩
  have := h.2 Q₁ hQ₁ Q₂ hQ₂ F₁ F₂ hF₁ hF₂
  finset_card

/-- Every `b`-threshold masking quorum system is a `b`-threshold dissemination quorum system. -/
theorem IsThresholdMaskingQuorumSystem.toDissemination
    (h : qs.IsThresholdMaskingQuorumSystem b) :
    qs.IsThresholdDisseminationQuorumSystem b := by
  refine ⟨h.1, fun Q₁ hQ₁ Q₂ hQ₂ F hF => ?_⟩
  have := h.2 Q₁ hQ₁ Q₂ hQ₂ F ∅ hF (Nat.zero_le b)
  finset_card

/-- Every `b`-threshold dissemination quorum system has at least one quorum. -/
theorem IsThresholdDisseminationQuorumSystem.quorums_nonempty
    (h : qs.IsThresholdDisseminationQuorumSystem b) :
    qs.quorums.Nonempty :=
  (h.1 ∅ (Nat.zero_le b)).imp fun _ h => h.1

/-- Any two quorums in a `b`-threshold dissemination quorum system intersect. -/
theorem IsThresholdDisseminationQuorumSystem.inter_nonempty
    (h : qs.IsThresholdDisseminationQuorumSystem b)
    {Q₁ Q₂ : Finset P} (hQ₁ : Q₁ ∈ qs.quorums) (hQ₂ : Q₂ ∈ qs.quorums) :
    (Q₁ ∩ Q₂).Nonempty := by
  simpa only [Finset.sdiff_empty] using h.2 Q₁ hQ₁ Q₂ hQ₂ ∅ (Nat.zero_le b)

/-- Exact cardinality characterization of `b`-threshold dissemination quorum systems: availability
against `|F| ≤ b` together with pairwise intersection of size at least `b + 1`. -/
theorem isThresholdDisseminationQuorumSystem_iff_card_inter :
    qs.IsThresholdDisseminationQuorumSystem b ↔
      qs.IsAvailableFor (thresholdAdversary P b) ∧
        ∀ Q₁ ∈ qs.quorums, ∀ Q₂ ∈ qs.quorums, b + 1 ≤ (Q₁ ∩ Q₂).card := by
  refine and_congr_right fun _ => ⟨fun h Q₁ hQ₁ Q₂ hQ₂ => ?_, fun h Q₁ hQ₁ Q₂ hQ₂ F hF => ?_⟩
  · by_contra! hlt
    have := h Q₁ hQ₁ Q₂ hQ₂ (Q₁ ∩ Q₂) (by omega)
    finset_card
  · have := h Q₁ hQ₁ Q₂ hQ₂
    finset_card

/-- Exact cardinality characterization of `b`-threshold masking quorum systems: availability
against `|F| ≤ b` together with pairwise intersection of size at least `2 * b + 1`. -/
theorem isThresholdMaskingQuorumSystem_iff_card_inter :
    qs.IsThresholdMaskingQuorumSystem b ↔
      qs.IsAvailableFor (thresholdAdversary P b) ∧
        ∀ Q₁ ∈ qs.quorums, ∀ Q₂ ∈ qs.quorums, 2 * b + 1 ≤ (Q₁ ∩ Q₂).card := by
  refine and_congr_right fun _ =>
    ⟨fun h Q₁ hQ₁ Q₂ hQ₂ => ?_, fun h Q₁ hQ₁ Q₂ hQ₂ F₁ F₂ hF₁ hF₂ => ?_⟩
  · by_contra! hlt
    by_cases hle : (Q₁ ∩ Q₂).card ≤ b
    · have := h Q₁ hQ₁ Q₂ hQ₂ (Q₁ ∩ Q₂) ∅ hle (Nat.zero_le b)
      finset_card
    · obtain ⟨F₁, hF₁sub, hF₁card⟩ :=
        Finset.exists_subset_card_eq (s := Q₁ ∩ Q₂) (n := b) (by omega)
      have := h Q₁ hQ₁ Q₂ hQ₂ F₁ ((Q₁ ∩ Q₂) \ F₁) (le_of_eq hF₁card) (by finset_card)
      finset_card
  · have := h Q₁ hQ₁ Q₂ hQ₂
    finset_card

/-- Exact cardinality characterization of `b`-threshold strong-opaque quorum systems: availability
against `|F| ≤ b` together with `(Q₂ \ Q₁).card + 2 * b < (Q₁ ∩ Q₂).card` for all pairs of
quorums. -/
theorem isThresholdStrongOpaqueQuorumSystem_iff_card :
    qs.IsThresholdStrongOpaqueQuorumSystem b ↔
      qs.IsAvailableFor (thresholdAdversary P b) ∧
        ∀ Q₁ ∈ qs.quorums, ∀ Q₂ ∈ qs.quorums, (Q₂ \ Q₁).card + 2 * b < (Q₁ ∩ Q₂).card := by
  refine and_congr_right fun _ =>
    ⟨fun h Q₁ hQ₁ Q₂ hQ₂ => ?_, fun h Q₁ hQ₁ Q₂ hQ₂ F₁ F₂ hF₁ hF₂ => ?_⟩
  · have hb_lt : b < (Q₁ ∩ Q₂).card := by
      by_contra! hle
      have := h Q₁ hQ₁ Q₂ hQ₂ (Q₁ ∩ Q₂) ∅ hle (Nat.zero_le b)
      finset_card
    obtain ⟨F, hFsub, hFcard⟩ := Finset.exists_subset_card_eq (n := b) (le_of_lt hb_lt)
    have := h Q₁ hQ₁ Q₂ hQ₂ F F (le_of_eq hFcard) (le_of_eq hFcard)
    finset_card
  · have := h Q₁ hQ₁ Q₂ hQ₂
    finset_card

end QuorumSystem

/-! ### Threshold quorum constructions and exact `iff` resilience characterizations -/

/-- Quorum system over a finite server set `P` consisting of all subsets of cardinality at least
`k`. -/
@[expose] def thresholdQuorums (P : Type*) [Fintype P] (k : ℕ) :
    QuorumSystem P where
  quorums := Finset.univ.powerset.filter fun Q => k ≤ Q.card

@[simp]
theorem mem_thresholdQuorums_iff {P : Type*} [Fintype P] {k : ℕ} {Q : Finset P} :
    Q ∈ (thresholdQuorums P k).quorums ↔ k ≤ Q.card := by
  simp only [thresholdQuorums, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]

/-- Canonical `b`-dissemination threshold quorum system of minimum quorum size
`⌈(|P| + b + 1) / 2⌉ = (|P| + b + 2) / 2` ([MalkhiReiter1998], Example 5.6, p. 208). -/
@[expose] def disseminationThresholdQuorums (P : Type*) [Fintype P] (b : ℕ) :
    QuorumSystem P :=
  thresholdQuorums P ((Fintype.card P + b + 2) / 2)

/-- Canonical `b`-masking threshold quorum system of minimum quorum size
`⌈(|P| + 2 * b + 1) / 2⌉ = (|P| + 2 * b + 2) / 2` ([MalkhiReiter1998], Example 4.6, p. 207). -/
@[expose] def maskingThresholdQuorums (P : Type*) [Fintype P] (b : ℕ) :
    QuorumSystem P :=
  thresholdQuorums P ((Fintype.card P + 2 * b + 2) / 2)

/-- Canonical `b`-threshold strong-opaque quorum system of minimum quorum size
`⌈(2 * |P| + 2 * b + 1) / 3⌉ = (2 * |P| + 2 * b + 3) / 3` (`#7506`; strict-inequality adaptation of
[MalkhiReiter1998], Example 5.11 and §5.2 p. 209). -/
@[expose] def strongOpaqueThresholdQuorums (P : Type*) [Fintype P] (b : ℕ) :
    QuorumSystem P :=
  thresholdQuorums P ((2 * Fintype.card P + 2 * b + 3) / 3)

private lemma thresholdQuorums_isAvailableFor {P : Type*} [Fintype P] {k b : ℕ}
    (hk : k + b ≤ Fintype.card P) :
    (thresholdQuorums P k).IsAvailableFor (thresholdAdversary P b) := by
  classical
  refine fun F hF => ⟨Finset.univ \ F, mem_thresholdQuorums_iff.mpr ?_, disjoint_sdiff_self_left⟩
  rw [mem_thresholdAdversary_iff] at hF
  finset_card

/-- Maximal-resilience `(|P| - b)`-cardinality threshold step toward `#7506`: when
`3 * b < Fintype.card P`, `thresholdQuorums P (Fintype.card P - b)` forms a `b`-threshold
dissemination quorum system (recovering `2 * b + 1` when `|P| = 3 * b + 1`). -/
theorem isThresholdDisseminationQuorumSystem_thresholdQuorums_sub {P : Type*} [Fintype P]
    [DecidableEq P] {b : ℕ} (hn : 3 * b < Fintype.card P) :
    (thresholdQuorums P (Fintype.card P - b)).IsThresholdDisseminationQuorumSystem b := by
  rw [QuorumSystem.isThresholdDisseminationQuorumSystem_iff_card_inter]
  refine ⟨thresholdQuorums_isAvailableFor (by omega), fun Q₁ hQ₁ Q₂ hQ₂ => ?_⟩
  rw [mem_thresholdQuorums_iff] at hQ₁ hQ₂
  finset_card

/-- Threshold construction step toward `#7506` (after [Malkhi and Reiter, Example 5.6, §5.1,
p. 208][MalkhiReiter1998]): when `3 * b < Fintype.card P`, `disseminationThresholdQuorums P b` is a
`b`-threshold dissemination quorum system. -/
theorem isThresholdDisseminationQuorumSystem_disseminationThresholdQuorums {P : Type*} [Fintype P]
    [DecidableEq P] {b : ℕ} (hn : 3 * b < Fintype.card P) :
    (disseminationThresholdQuorums P b).IsThresholdDisseminationQuorumSystem b := by
  rw [QuorumSystem.isThresholdDisseminationQuorumSystem_iff_card_inter]
  refine ⟨thresholdQuorums_isAvailableFor (by omega), fun Q₁ hQ₁ Q₂ hQ₂ => ?_⟩
  rw [disseminationThresholdQuorums, mem_thresholdQuorums_iff] at hQ₁ hQ₂
  finset_card

/-- Threshold construction step toward `#7506` (after [Malkhi and Reiter, Example 4.6, §4,
p. 207][MalkhiReiter1998]): when `4 * b < Fintype.card P`, `maskingThresholdQuorums P b` is a
`b`-threshold masking quorum system. -/
theorem isThresholdMaskingQuorumSystem_maskingThresholdQuorums {P : Type*} [Fintype P]
    [DecidableEq P] {b : ℕ} (hn : 4 * b < Fintype.card P) :
    (maskingThresholdQuorums P b).IsThresholdMaskingQuorumSystem b := by
  rw [QuorumSystem.isThresholdMaskingQuorumSystem_iff_card_inter]
  refine ⟨thresholdQuorums_isAvailableFor (by omega), fun Q₁ hQ₁ Q₂ hQ₂ => ?_⟩
  rw [maskingThresholdQuorums, mem_thresholdQuorums_iff] at hQ₁ hQ₂
  finset_card

/-- Strong-opaque threshold construction step toward `#7506` (strict-inequality adaptation after
[Malkhi and Reiter, §5.2, p. 209 and Example 5.11, p. 210][MalkhiReiter1998]): when
`5 * b < Fintype.card P`, `strongOpaqueThresholdQuorums P b` is a `b`-threshold strong-opaque quorum
system. -/
theorem isThresholdStrongOpaqueQuorumSystem_strongOpaqueThresholdQuorums {P : Type*} [Fintype P]
    [DecidableEq P] {b : ℕ} (hn : 5 * b < Fintype.card P) :
    (strongOpaqueThresholdQuorums P b).IsThresholdStrongOpaqueQuorumSystem b := by
  rw [QuorumSystem.isThresholdStrongOpaqueQuorumSystem_iff_card]
  refine ⟨thresholdQuorums_isAvailableFor (by omega), fun Q₁ hQ₁ Q₂ hQ₂ => ?_⟩
  rw [strongOpaqueThresholdQuorums, mem_thresholdQuorums_iff] at hQ₁ hQ₂
  finset_card

/-- Shared witness extraction for threshold-quorum lower bounds: given availability against
`thresholdAdversary P b` and every quorum having size `> b`, constructs two quorums `Q₁, Q₂` with
`(Q₁ ∩ Q₂).card ≤ |P| - 2 * b` and `b ≤ (Q₁ \ Q₂).card`. -/
private lemma exists_quorum_pair_bounds {P : Type*} [Fintype P] [DecidableEq P]
    {qs : QuorumSystem P} {b : ℕ}
    (havail : qs.IsAvailableFor (thresholdAdversary P b))
    (hgt : ∀ Q ∈ qs.quorums, b < Q.card) :
    ∃ Q₁ ∈ qs.quorums, ∃ Q₂ ∈ qs.quorums,
      (Q₁ ∩ Q₂).card ≤ Fintype.card P - 2 * b ∧ b ≤ (Q₁ \ Q₂).card := by
  have hbn : b < Fintype.card P := by
    by_contra hle
    obtain ⟨Q, hQ, hdisj⟩ := havail Finset.univ (mem_thresholdAdversary_iff.mpr (by finset_card))
    have := hgt Q hQ
    finset_card
  obtain ⟨F₁, -, hF₁⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset P)) hbn.le
  obtain ⟨Q₁, hQ₁, hdisj₁⟩ := havail F₁ (mem_thresholdAdversary_iff.mpr hF₁.le)
  obtain ⟨F₂, hF₂sub, hF₂⟩ := Finset.exists_subset_card_eq (hgt Q₁ hQ₁).le
  obtain ⟨Q₂, hQ₂, hdisj₂⟩ := havail F₂ (mem_thresholdAdversary_iff.mpr hF₂.le)
  exact ⟨Q₁, hQ₁, Q₂, hQ₂, by finset_card, by finset_card⟩

/-- Uniform `b`-threshold dissemination existence step toward `#7506` (specializing
[Malkhi and Reiter, Corollary 5.5, §5.1, p. 208][MalkhiReiter1998] to `thresholdAdversary P b`;
general fail-prone systems `B` of Theorem 5.4 and Corollary 5.5 remain open under `#7506`): over a
nonempty finite server universe `P`, a `b`-threshold dissemination quorum system exists if and only
if `3 * b < Fintype.card P`. -/
theorem exists_thresholdDisseminationQuorumSystem_iff {P : Type*} [Fintype P] [DecidableEq P]
    [Nonempty P] (b : ℕ) :
    (∃ qs : QuorumSystem P, qs.IsThresholdDisseminationQuorumSystem b) ↔
      3 * b < Fintype.card P := by
  refine ⟨fun ⟨qs, hqs⟩ => ?_,
    fun hn => ⟨disseminationThresholdQuorums P b,
      isThresholdDisseminationQuorumSystem_disseminationThresholdQuorums hn⟩⟩
  rw [QuorumSystem.isThresholdDisseminationQuorumSystem_iff_card_inter] at hqs
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hinter_ub, _⟩ :=
    exists_quorum_pair_bounds hqs.1 fun Q hQ => Finset.inter_self Q ▸ hqs.2 Q hQ Q hQ
  have := hqs.2 Q₁ hQ₁ Q₂ hQ₂
  have := Fintype.card_pos (α := P)
  omega

/-- Uniform `b`-threshold masking existence step toward `#7506` (specializing
[Malkhi and Reiter, Corollary 4.4, §4, p. 206][MalkhiReiter1998] to `thresholdAdversary P b`;
general fail-prone systems `B` of Theorem 4.3 and Corollary 4.4 remain open under `#7506`): over a
nonempty finite server universe `P`, a `b`-threshold masking quorum system exists if and only if
`4 * b < Fintype.card P`. -/
theorem exists_thresholdMaskingQuorumSystem_iff {P : Type*} [Fintype P] [DecidableEq P]
    [Nonempty P] (b : ℕ) :
    (∃ qs : QuorumSystem P, qs.IsThresholdMaskingQuorumSystem b) ↔ 4 * b < Fintype.card P := by
  refine ⟨fun ⟨qs, hqs⟩ => ?_,
    fun hn => ⟨maskingThresholdQuorums P b,
      isThresholdMaskingQuorumSystem_maskingThresholdQuorums hn⟩⟩
  rw [QuorumSystem.isThresholdMaskingQuorumSystem_iff_card_inter] at hqs
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hinter_ub, _⟩ := exists_quorum_pair_bounds hqs.1 fun Q hQ =>
    Nat.lt_of_le_of_lt (by omega) (Finset.inter_self Q ▸ hqs.2 Q hQ Q hQ)
  have := hqs.2 Q₁ hQ₁ Q₂ hQ₂
  have := Fintype.card_pos (α := P)
  omega

/-- Uniform `b`-threshold strong-opaque existence step toward `#7506` (formalizing the strict
`>` variant of `O-Consistency1` noted in [Malkhi and Reiter, §5.2, p. 209][MalkhiReiter1998];
contrasting with Definition 5.9, Example 5.11, and Theorem 5.12's weak-inequality `≥` opaque quorum
systems whose exact bound is `5 * b ≤ |P|` for `b > 0`, which remain open under `#7506`): over a
nonempty finite server universe `P`, a `b`-threshold strong-opaque quorum system exists if and only
if `5 * b < Fintype.card P`. -/
theorem exists_thresholdStrongOpaqueQuorumSystem_iff {P : Type*} [Fintype P] [DecidableEq P]
    [Nonempty P] (b : ℕ) :
    (∃ qs : QuorumSystem P, qs.IsThresholdStrongOpaqueQuorumSystem b) ↔
      5 * b < Fintype.card P := by
  refine ⟨fun ⟨qs, hqs⟩ => ?_,
    fun hn => ⟨strongOpaqueThresholdQuorums P b,
      isThresholdStrongOpaqueQuorumSystem_strongOpaqueThresholdQuorums hn⟩⟩
  rw [QuorumSystem.isThresholdStrongOpaqueQuorumSystem_iff_card] at hqs
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hinter_ub, hsdiff_lb⟩ := exists_quorum_pair_bounds hqs.1 fun Q hQ =>
    Nat.lt_of_le_of_lt (by omega) (Finset.inter_self Q ▸ hqs.2 Q hQ Q hQ)
  have := hqs.2 Q₂ hQ₂ Q₁ hQ₁
  have := Fintype.card_pos (α := P)
  finset_card

/-! ### Unauthenticated masking-quorum register read-after-write safety -/

/-- A timestamped register entry `(ts, val)` stored by a server or returned to a reader in the
unauthenticated masking-quorum register protocol ([MalkhiReiter1998], §3.2, p. 205). -/
@[ext]
structure TimestampedVal (T V : Type*) where
  /-- Write timestamp ordered in `T`. -/
  ts : T
  /-- Register value written at `ts`. -/
  val : V
  deriving @[expose] DecidableEq

/-- Server-side update rule of [MalkhiReiter1998] §3.2 (p. 205): replace the stored entry only when
the incoming write carries a strictly larger timestamp. -/
@[expose] def TimestampedVal.updateIfNewer {T V : Type*} [LinearOrder T]
    (cur incoming : TimestampedVal T V) : TimestampedVal T V :=
  if cur.ts < incoming.ts then incoming else cur

/-- Local register entry at a correct server after starting from `init` and applying `delivered`
writes in arbitrary asynchronous arrival order. -/
@[expose] def applyWrites {T V : Type*} [LinearOrder T]
    (init : TimestampedVal T V) (delivered : List (TimestampedVal T V)) : TimestampedVal T V :=
  delivered.foldl TimestampedVal.updateIfNewer init

private lemma applyWrites_mem_or_eq {T V : Type*} [LinearOrder T]
    (init : TimestampedVal T V) (delivered : List (TimestampedVal T V)) :
    applyWrites init delivered = init ∨ applyWrites init delivered ∈ delivered := by
  induction delivered generalizing init with
  | nil => exact Or.inl rfl
  | cons w ws ih =>
    refine (ih (init.updateIfNewer w)).elim (fun h => ?_) (Or.inr ∘ List.mem_cons_of_mem w)
    rw [applyWrites, List.foldl_cons, ← applyWrites, h]
    by_cases hlt : init.ts < w.ts <;> simp [TimestampedVal.updateIfNewer, hlt]

private lemma ts_le_applyWrites {T V : Type*} [LinearOrder T]
    (init : TimestampedVal T V) (delivered : List (TimestampedVal T V)) :
    init.ts ≤ (applyWrites init delivered).ts ∧
      ∀ e ∈ delivered, e.ts ≤ (applyWrites init delivered).ts := by
  induction delivered generalizing init with
  | nil => simp [applyWrites]
  | cons w ws ih =>
    simp only [applyWrites, List.foldl_cons]
    obtain ⟨hinit, hmem⟩ := ih (init.updateIfNewer w)
    have hcur : init.ts ≤ (init.updateIfNewer w).ts ∧ w.ts ≤ (init.updateIfNewer w).ts := by
      unfold TimestampedVal.updateIfNewer
      split_ifs with hlt
      exacts [⟨hlt.le, le_rfl⟩, ⟨le_rfl, not_lt.mp hlt⟩]
    exact ⟨hcur.1.trans hinit, List.forall_mem_cons.mpr ⟨hcur.2.trans hinit, hmem⟩⟩

/-- Candidate `(ts, val)` entries returned by at least `b + 1` servers in read quorum `Q_r`
([MalkhiReiter1998], §4, p. 206, specialized to `thresholdAdversary P b`). -/
@[expose] def maskingCandidates {P T V : Type*} [DecidableEq T] [DecidableEq V]
    (b : ℕ) (Q_r : Finset P) (resp : P → TimestampedVal T V) : Finset (TimestampedVal T V) :=
  (Q_r.image resp).filter fun e => b + 1 ≤ (Q_r.filter fun u => resp u = e).card

@[simp]
theorem mem_maskingCandidates_iff {P T V : Type*} [DecidableEq T] [DecidableEq V]
    {b : ℕ} {Q_r : Finset P} {resp : P → TimestampedVal T V} {e : TimestampedVal T V} :
    e ∈ maskingCandidates b Q_r resp ↔ b + 1 ≤ (Q_r.filter fun u => resp u = e).card := by
  simp only [maskingCandidates, Finset.mem_filter, Finset.mem_image, and_iff_right_iff_imp]
  intro hcard
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.zero_lt_succ b) hcard)
  exact ⟨u, (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩

/-- Soundness of `(b + 1)`-multiplicity filtering without signatures: when `F.card ≤ b`, every entry
in `maskingCandidates b Q_r resp` was returned by at least one correct server `u ∈ Q_r \ F`. -/
theorem maskingCandidates_sound {P T V : Type*} [DecidableEq T] [DecidableEq V]
    {b : ℕ} {F Q_r : Finset P} (hF : F.card ≤ b) {resp : P → TimestampedVal T V}
    {e : TimestampedVal T V} (he : e ∈ maskingCandidates b Q_r resp) :
    ∃ u ∈ Q_r, u ∉ F ∧ resp u = e := by
  rw [mem_maskingCandidates_iff] at he
  obtain ⟨u, hu, huF⟩ : ∃ u ∈ Q_r.filter (fun u => resp u = e), u ∉ F := by finset_card
  exact ⟨u, (Finset.mem_filter.mp hu).1, huF, (Finset.mem_filter.mp hu).2⟩

/-- Computable unauthenticated client read function ([MalkhiReiter1998], §4, p. 206): filter
responses on `Q_r` to `maskingCandidates b Q_r resp` and return `some e.val` when a unique
surviving candidate `e` attains the maximum timestamp across all surviving candidates. -/
@[expose] def maskingRead {P T V : Type*} [LinearOrder T] [DecidableEq V]
    (b : ℕ) (Q_r : Finset P) (resp : P → TimestampedVal T V) : Option V :=
  let cands := maskingCandidates b Q_r resp
  let top := cands.filter fun e => ∀ e' ∈ cands, e'.ts ≤ e.ts
  if h : top.card = 1 then
    some (top.choose (fun _ => True) (by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
      exact ⟨x, ⟨by rw [hx]; exact Finset.mem_singleton_self x, trivial⟩,
        fun y hy => by rw [hx, Finset.mem_singleton] at hy; exact hy.1⟩)).val
  else none

private lemma applyWrites_eq_latest {T V : Type*} [LinearOrder T]
    {init latest : TimestampedVal T V} {delivered : List (TimestampedVal T V)}
    (hinit : init.ts < latest.ts)
    (hbound : ∀ e ∈ delivered, e = latest ∨ e.ts < latest.ts) :
    (applyWrites init delivered).ts ≤ latest.ts ∧
      ((applyWrites init delivered).ts = latest.ts → applyWrites init delivered = latest) := by
  rcases (applyWrites_mem_or_eq init delivered).imp_right (hbound _) with heq | heq | hlt
  · exact ⟨(congrArg TimestampedVal.ts heq).trans_le hinit.le,
      fun hts => absurd ((congrArg TimestampedVal.ts heq).symm.trans hts) hinit.ne⟩
  · exact ⟨(congrArg TimestampedVal.ts heq).le, fun _ => heq⟩
  · exact ⟨hlt.le, fun hts => absurd hts hlt.ne⟩

/-- Unauthenticated `b`-threshold single-latest-write masking-register step toward `#7506` (after
[Malkhi and Reiter, §§3.2, 4, Lemma 4.2, pp. 205–206][MalkhiReiter1998]): suppose `qs` is a
`b`-threshold masking quorum system, `F.card ≤ b`, write `latest` (`init.ts < latest.ts`) has been
delivered to every correct server in write quorum `Q_w ∈ qs.quorums`, every other write delivered to
any correct server has timestamp `< latest.ts`, and `resp` agrees with each correct server's local
state `applyWrites init (delivered u)` outside `F` (while faulty servers in `F` return arbitrary
forged pairs). Then in any read quorum `Q_r ∈ qs.quorums`:

1. `latest ∈ maskingCandidates b Q_r resp`, and
2. any `e ∈ maskingCandidates b Q_r resp` whose timestamp is at least as large as every candidate in
   `maskingCandidates b Q_r resp` satisfies `e = latest` (hence `e.val = latest.val`). -/
theorem threshold_masking_register_max_ts_eq {P T V : Type*} [DecidableEq P] [LinearOrder T]
    [DecidableEq V] {qs : QuorumSystem P} {b : ℕ} (hqs : qs.IsThresholdMaskingQuorumSystem b)
    {F Q_w Q_r : Finset P} (hF : F.card ≤ b) (hQw : Q_w ∈ qs.quorums) (hQr : Q_r ∈ qs.quorums)
    {init latest : TimestampedVal T V} {delivered : P → List (TimestampedVal T V)}
    (hinit : init.ts < latest.ts)
    (hcompleted : ∀ u ∈ Q_w, u ∉ F → latest ∈ delivered u)
    (hbound : ∀ u, u ∉ F → ∀ e ∈ delivered u, e = latest ∨ e.ts < latest.ts)
    {resp : P → TimestampedVal T V}
    (hresp : ∀ u, u ∉ F → resp u = applyWrites init (delivered u)) :
    latest ∈ maskingCandidates b Q_r resp ∧
      ∀ e ∈ maskingCandidates b Q_r resp,
        (∀ e' ∈ maskingCandidates b Q_r resp, e'.ts ≤ e.ts) → e = latest := by
  have hlatest_mem : latest ∈ maskingCandidates b Q_r resp := by
    rw [mem_maskingCandidates_iff]
    have := (QuorumSystem.isThresholdMaskingQuorumSystem_iff_card_inter.mp hqs).2 Q_w hQw Q_r hQr
    refine le_trans (show b + 1 ≤ ((Q_w ∩ Q_r) \ F).card by finset_card)
      (Finset.card_le_card fun u hu => ?_)
    rw [Finset.mem_sdiff, Finset.mem_inter] at hu
    obtain ⟨hle, heq⟩ := applyWrites_eq_latest hinit (hbound u hu.2)
    refine Finset.mem_filter.mpr ⟨hu.1.2, (hresp u hu.2).trans (heq (le_antisymm hle ?_))⟩
    exact (ts_le_applyWrites init (delivered u)).2 latest (hcompleted u hu.1.1 hu.2)
  refine ⟨hlatest_mem, fun e he hmax => ?_⟩
  obtain ⟨u, _, huF, rfl⟩ := maskingCandidates_sound hF he
  obtain ⟨hle, heq⟩ := (hresp u huF).symm ▸ applyWrites_eq_latest hinit (hbound u huF)
  exact heq (le_antisymm hle (hmax latest hlatest_mem))

/-- Computable `b`-threshold single-latest-write masking-read step toward `#7506` (after
[Malkhi and Reiter, §§3.2, 4, Lemma 4.2, pp. 205–206][MalkhiReiter1998]): under the hypotheses of
`threshold_masking_register_max_ts_eq`, `maskingRead b Q_r resp = some latest.val` for every read
quorum `Q_r ∈ qs.quorums` and arbitrary Byzantine responses on `F`. -/
theorem threshold_maskingRead_eq_some_latest_write {P T V : Type*} [DecidableEq P] [LinearOrder T]
    [DecidableEq V] {qs : QuorumSystem P} {b : ℕ} (hqs : qs.IsThresholdMaskingQuorumSystem b)
    {F Q_w Q_r : Finset P} (hF : F.card ≤ b) (hQw : Q_w ∈ qs.quorums) (hQr : Q_r ∈ qs.quorums)
    {init latest : TimestampedVal T V} {delivered : P → List (TimestampedVal T V)}
    (hinit : init.ts < latest.ts)
    (hcompleted : ∀ u ∈ Q_w, u ∉ F → latest ∈ delivered u)
    (hbound : ∀ u, u ∉ F → ∀ e ∈ delivered u, e = latest ∨ e.ts < latest.ts)
    {resp : P → TimestampedVal T V}
    (hresp : ∀ u, u ∉ F → resp u = applyWrites init (delivered u)) :
    maskingRead b Q_r resp = some latest.val := by
  obtain ⟨hmem, huniq⟩ :=
    threshold_masking_register_max_ts_eq hqs hF hQw hQr hinit hcompleted hbound hresp
  let cands := maskingCandidates b Q_r resp
  have htop_eq : (cands.filter fun e => ∀ e' ∈ cands, e'.ts ≤ e.ts) = {latest} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_singleton]
    refine ⟨fun ⟨he, hm⟩ => huniq e he hm, fun h => h ▸ ⟨hmem, fun e' he' => ?_⟩⟩
    obtain ⟨u, _, huF, rfl⟩ := maskingCandidates_sound hF he'
    exact hresp u huF ▸ (applyWrites_eq_latest hinit (hbound u huF)).1
  simp only [maskingRead]
  split_ifs with hcard'
  · generalize_proofs hp
    exact congrArg (some ∘ TimestampedVal.val)
      (Finset.mem_singleton.mp (htop_eq ▸ (Finset.choose_spec (fun _ => True) _ hp).1))
  · exact absurd (htop_eq ▸ Finset.card_singleton latest) hcard'

end Cslib.Distributed.ByzantineQuorum
