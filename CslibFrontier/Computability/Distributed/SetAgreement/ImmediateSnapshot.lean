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
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Pairwise

/-!
# Immediate snapshot schedules, the Borowsky–Gafni characterization, and `IIS` views

As a step toward `#7504` (leaving the asynchronous read/write and atomic-snapshot to `IIS`
simulation open in `#7504`), this module formalizes one-shot Immediate Snapshot (`IS`) schedules and
`R`-round Iterated Immediate Snapshot (`IIS`) full-information executions over an active process set
`U : Finset V`, following [BorowskyGafni1997] (§§3.4–3.6, PS pp. 5–6; see also [BorowskyGafni1993]
and [HerlihyShavit1999], §5.2).

* **One-shot `IS` schedules (`ISSchedule U`):** ordered partitions `(B₁, …, Bₖ)` of a finite
  participating process set `U : Finset V` into nonempty pairwise-disjoint blocks. All processes
  in block `Bⱼ` concurrently write their values and immediately scan the shared memory, observing
  the prefix union `B₁ ∪ ⋯ ∪ Bⱼ` (`ISSchedule.snapshot`). We equip `ISSchedule U` with a computable
  `Fintype` instance enumerating all ordered partitions of `U`.
* **Borowsky–Gafni immediate-snapshot characterization (`IsImmediateSnapshotOn`,
  `IsImmediateSnapshot`):** a set assignment `S : V → Finset V` arises as `π.snapshot` for a
  (unique) ordered partition `π : ISSchedule U` if and only if it satisfies self-inclusion
  (`p ∈ S p`), containment (`S p ⊆ S q ∨ S q ⊆ S p`), and immediacy (`p ∈ S q → S p ⊆ S q`) on `U`
  ([BorowskyGafni1997], §3.5, conditions 1–3, p. 5), packaged as explicit equivalences
  `ISSchedule.equivImmediateSnapshotOn` and `ISSchedule.equivImmediateSnapshot`.
* **`R`-round `IIS` full-information views (`IISView`, `iisRun`):** inductively, round-`0` views
  are `InitView V Input` (`⟨p, inp p⟩`) and round-`(r + 1)` views are `StepView V` pairing process
  identity `p` with the `Finset` image of round-`r` views across `(E (Fin.last r)).snapshot p`
  ([BorowskyGafni1997], §3.5, p. 5). We track the participating process carrier (`IISView.carrier`)
  and observed input set (`IISView.carrierInputs`), prove view locality (`iisRun_congr_carrier`:
  `p`'s view depends only on `inp` restricted to `(iisRun inp E p).carrier`), solo-execution
  singleton carriers (`carrier_iisRun_eq_singleton_of_solo`), and derive carrier-input validity
  from plain global input validity (`IISProtocol.isCarrierValid_of_isValid`, following
  the input-simplex extension step of [HerlihyShavit1999], Proof of Theorem 3.3, p. 881).

## Main definitions

* `Cslib.Distributed.SetAgreement.unionBlocks`, `Cslib.Distributed.SetAgreement.blocksSnapshot`:
  block-list union and prefix-union snapshot evaluation.
* `Cslib.Distributed.SetAgreement.ISSchedule`, `Cslib.Distributed.SetAgreement.ISSchedule.snapshot`:
  one-shot immediate-snapshot schedule (ordered partition of `U : Finset V`) and its induced
  per-process snapshot map.
* `Cslib.Distributed.SetAgreement.IsImmediateSnapshotOn`,
  `Cslib.Distributed.SetAgreement.IsImmediateSnapshot`: Borowsky–Gafni immediate-snapshot axioms
  (self-inclusion, containment, immediacy) on a participating set `U` and on `Finset.univ`.
* `Cslib.Distributed.SetAgreement.InitView`, `Cslib.Distributed.SetAgreement.StepView`,
  `Cslib.Distributed.SetAgreement.IISView`: round-`0`, step, and `R`-round `IIS` views.
* `Cslib.Distributed.SetAgreement.IISView.proc`, `Cslib.Distributed.SetAgreement.IISView.carrier`,
  `Cslib.Distributed.SetAgreement.IISView.carrierInputs`: owner process, participating process
  carrier, and observed input set of an `IIS` view.
* `Cslib.Distributed.SetAgreement.iisRun`: `R`-round full-information `IIS` view execution.
* `Cslib.Distributed.SetAgreement.IISProtocol`,
  `Cslib.Distributed.SetAgreement.IISProtocol.IsValid`,
  `Cslib.Distributed.SetAgreement.IISProtocol.IsCarrierValid`: `R`-round `IIS` decision protocols
  and global vs carrier-restricted input validity.

## Main results

* `Cslib.Distributed.SetAgreement.ISSchedule.isImmediateSnapshotOn`,
  `Cslib.Distributed.SetAgreement.ISSchedule.isImmediateSnapshot`: every `IS` schedule satisfies
  self-inclusion, containment, and immediacy.
* `Cslib.Distributed.SetAgreement.ISSchedule.equivImmediateSnapshotOn`,
  `Cslib.Distributed.SetAgreement.ISSchedule.equivImmediateSnapshot`,
  `Cslib.Distributed.SetAgreement.isImmediateSnapshot_iff_existsUnique_schedule`: exact bijection
  and unique-existence characterization between ordered partitions and set assignments satisfying
  the Borowsky–Gafni axioms.
* `Cslib.Distributed.SetAgreement.self_mem_carrier_iisRun`,
  `Cslib.Distributed.SetAgreement.carrier_iisRun_subset`,
  `Cslib.Distributed.SetAgreement.carrierInputs_iisRun`: carrier bounds and input-image identity
  for `R`-round `IIS` views.
* `Cslib.Distributed.SetAgreement.iisRun_congr_carrier`: `p`'s `R`-round `IIS` view depends only on
  inputs of processes in `(iisRun inp E p).carrier`.
* `Cslib.Distributed.SetAgreement.carrier_iisRun_eq_singleton_of_solo`: a process running first
  alone in every round observes carrier `{p}` and input set `{inp p}`.
* `Cslib.Distributed.SetAgreement.IISProtocol.isCarrierValid_of_isValid`: every globally input-valid
  `IIS` protocol automatically satisfies carrier-input validity.

## References

* [E. Borowsky, E. Gafni, *Generalized FLP Impossibility Result for t-Resilient Asynchronous
  Computations*][BorowskyGafni1993]
* [E. Borowsky, E. Gafni, *A Simple Algorithmically Reasoned Characterization of Wait-Free
  Computations*][BorowskyGafni1997]
* [M. Herlihy, N. Shavit, *The Topological Structure of Asynchronous
  Computability*][HerlihyShavit1999]
-/

public section

namespace Cslib.Distributed.SetAgreement

open Finset

section OrderedPartitions

variable {V : Type*} [DecidableEq V]

/-- Union of a list of process blocks `B₁, …, Bₖ`. -/
@[expose]
def unionBlocks (bs : List (Finset V)) : Finset V :=
  bs.foldr (· ∪ ·) ∅

@[simp]
theorem unionBlocks_nil : unionBlocks ([] : List (Finset V)) = ∅ := rfl

@[simp]
theorem unionBlocks_cons (B : Finset V) (bs : List (Finset V)) :
    unionBlocks (B :: bs) = B ∪ unionBlocks bs := rfl

@[simp]
theorem unionBlocks_append (bs₁ bs₂ : List (Finset V)) :
    unionBlocks (bs₁ ++ bs₂) = unionBlocks bs₁ ∪ unionBlocks bs₂ := by
  induction bs₁ with
  | nil => simp only [List.nil_append, unionBlocks_nil, empty_union]
  | cons B bs₁ ih => simp only [List.cons_append, unionBlocks_cons, ih, union_assoc]

theorem mem_unionBlocks {bs : List (Finset V)} {p : V} :
    p ∈ unionBlocks bs ↔ ∃ B ∈ bs, p ∈ B := by
  induction bs with
  | nil => simp only [unionBlocks_nil, notMem_empty, List.not_mem_nil, false_and, exists_false]
  | cons B bs ih =>
    simp only [unionBlocks_cons, mem_union, ih, List.mem_cons, exists_eq_or_imp]

theorem disjoint_unionBlocks_right {B : Finset V} {bs : List (Finset V)} :
    Disjoint B (unionBlocks bs) ↔ ∀ C ∈ bs, Disjoint B C := by
  induction bs with
  | nil => simp
  | cons C bs ih =>
    simp only [unionBlocks_cons, disjoint_union_right, ih, List.mem_cons, forall_eq_or_imp]

theorem card_unionBlocks_of_pairwise_disjoint {bs : List (Finset V)}
    (hdisj : bs.Pairwise Disjoint) :
    #(unionBlocks bs) = (bs.map Finset.card).sum := by
  induction bs with
  | nil => rfl
  | cons B bs ih =>
    rw [List.pairwise_cons] at hdisj
    rw [unionBlocks_cons, card_union_of_disjoint (disjoint_unionBlocks_right.mpr hdisj.1),
      List.map_cons, List.sum_cons, ih hdisj.2]

theorem length_le_card_unionBlocks {bs : List (Finset V)}
    (hne : ∀ B ∈ bs, B.Nonempty) (hdisj : bs.Pairwise Disjoint) :
    bs.length ≤ #(unionBlocks bs) := by
  rw [card_unionBlocks_of_pairwise_disjoint hdisj]
  induction bs with
  | nil => simp only [List.length_nil, List.map_nil, List.sum_nil, le_refl]
  | cons B bs ih =>
    rw [List.pairwise_cons] at hdisj
    have hB : 1 ≤ #B := (hne B List.mem_cons_self).card_pos
    have htl := ih (fun C hC => hne C (List.mem_cons_of_mem B hC)) hdisj.2
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- Prefix-union snapshot returned to process `p` by executing ordered concurrent blocks `bs`:
if `p` appears in block `Bⱼ`, `p` observes `B₁ ∪ ⋯ ∪ Bⱼ`; if `p ∉ unionBlocks bs`, `∅`. -/
@[expose]
def blocksSnapshot : List (Finset V) → V → Finset V
  | [], _ => ∅
  | B :: bs, p =>
    if p ∈ B then B
    else if p ∈ unionBlocks bs then B ∪ blocksSnapshot bs p
    else ∅

@[simp]
theorem blocksSnapshot_nil (p : V) : blocksSnapshot ([] : List (Finset V)) p = ∅ := rfl

theorem blocksSnapshot_of_notMem {bs : List (Finset V)} {p : V} (hp : p ∉ unionBlocks bs) :
    blocksSnapshot bs p = ∅ := by
  cases bs with
  | nil => rfl
  | cons B bs =>
    simp only [unionBlocks_cons, mem_union, not_or] at hp
    simp only [blocksSnapshot, hp.1, hp.2, ↓reduceIte]

theorem blocksSnapshot_cons_of_mem {B : Finset V} {bs : List (Finset V)} {p : V} (hp : p ∈ B) :
    blocksSnapshot (B :: bs) p = B := by
  simp only [blocksSnapshot, hp, ↓reduceIte]

theorem blocksSnapshot_cons_of_notMem {B : Finset V} {bs : List (Finset V)} {p : V}
    (hpB : p ∉ B) (hp : p ∈ unionBlocks bs) :
    blocksSnapshot (B :: bs) p = B ∪ blocksSnapshot bs p := by
  simp only [blocksSnapshot, hpB, hp, ↓reduceIte]

theorem blocksSnapshot_append_of_mem_left {bs₁ bs₂ : List (Finset V)} {p : V}
    (hp : p ∈ unionBlocks bs₁) :
    blocksSnapshot (bs₁ ++ bs₂) p = blocksSnapshot bs₁ p := by
  induction bs₁ with
  | nil => simp only [unionBlocks_nil, notMem_empty] at hp
  | cons B bs₁ ih =>
    by_cases hpB : p ∈ B
    · simp only [List.cons_append, blocksSnapshot_cons_of_mem hpB]
    · have hp₁ : p ∈ unionBlocks bs₁ := by
        simp only [unionBlocks_cons, mem_union, hpB, false_or] at hp
        exact hp
      have hp₁₂ : p ∈ unionBlocks (bs₁ ++ bs₂) := by
        simp only [unionBlocks_append, mem_union, hp₁, true_or]
      rw [List.cons_append, blocksSnapshot_cons_of_notMem hpB hp₁₂,
        blocksSnapshot_cons_of_notMem hpB hp₁, ih hp₁]

theorem self_mem_blocksSnapshot {bs : List (Finset V)} {p : V} (hp : p ∈ unionBlocks bs) :
    p ∈ blocksSnapshot bs p := by
  induction bs with
  | nil => simp only [unionBlocks_nil, notMem_empty] at hp
  | cons B bs ih =>
    by_cases hpB : p ∈ B
    · rw [blocksSnapshot_cons_of_mem hpB]
      exact hpB
    · have hp' : p ∈ unionBlocks bs := by
        simp only [unionBlocks_cons, mem_union, hpB, false_or] at hp
        exact hp
      rw [blocksSnapshot_cons_of_notMem hpB hp']
      exact mem_union_right B (ih hp')

theorem blocksSnapshot_subset_unionBlocks (bs : List (Finset V)) (p : V) :
    blocksSnapshot bs p ⊆ unionBlocks bs := by
  induction bs with
  | nil => simp only [blocksSnapshot_nil, unionBlocks_nil, Subset.refl]
  | cons B bs ih =>
    by_cases hpB : p ∈ B
    · rw [blocksSnapshot_cons_of_mem hpB, unionBlocks_cons]
      exact subset_union_left
    · by_cases hp : p ∈ unionBlocks bs
      · rw [blocksSnapshot_cons_of_notMem hpB hp, unionBlocks_cons]
        exact union_subset_union_right ih
      · rw [blocksSnapshot_of_notMem (by simp only [unionBlocks_cons, mem_union, hpB, hp, or_self,
          not_false_eq_true])]
        exact empty_subset _

theorem blocksSnapshot_containment {bs : List (Finset V)} {p q : V}
    (hp : p ∈ unionBlocks bs) (hq : q ∈ unionBlocks bs) :
    blocksSnapshot bs p ⊆ blocksSnapshot bs q ∨ blocksSnapshot bs q ⊆ blocksSnapshot bs p := by
  induction bs with
  | nil => simp only [unionBlocks_nil, notMem_empty] at hp
  | cons B bs ih =>
    by_cases hpB : p ∈ B
    · left
      rw [blocksSnapshot_cons_of_mem hpB]
      by_cases hqB : q ∈ B
      · rw [blocksSnapshot_cons_of_mem hqB]
      · have hq' : q ∈ unionBlocks bs := by
          simp only [unionBlocks_cons, mem_union, hqB, false_or] at hq
          exact hq
        rw [blocksSnapshot_cons_of_notMem hqB hq']
        exact subset_union_left
    · by_cases hqB : q ∈ B
      · right
        have hp' : p ∈ unionBlocks bs := by
          simp only [unionBlocks_cons, mem_union, hpB, false_or] at hp
          exact hp
        rw [blocksSnapshot_cons_of_mem hqB, blocksSnapshot_cons_of_notMem hpB hp']
        exact subset_union_left
      · have hp' : p ∈ unionBlocks bs := by
          simp only [unionBlocks_cons, mem_union, hpB, false_or] at hp
          exact hp
        have hq' : q ∈ unionBlocks bs := by
          simp only [unionBlocks_cons, mem_union, hqB, false_or] at hq
          exact hq
        rw [blocksSnapshot_cons_of_notMem hpB hp', blocksSnapshot_cons_of_notMem hqB hq']
        rcases ih hp' hq' with h | h
        · exact Or.inl (union_subset_union_right h)
        · exact Or.inr (union_subset_union_right h)

theorem blocksSnapshot_immediacy {bs : List (Finset V)} (hdisj : bs.Pairwise Disjoint) {p q : V}
    (hq : q ∈ unionBlocks bs) (hpq : p ∈ blocksSnapshot bs q) :
    blocksSnapshot bs p ⊆ blocksSnapshot bs q := by
  induction bs with
  | nil => simp only [unionBlocks_nil, notMem_empty] at hq
  | cons B bs ih =>
    rw [List.pairwise_cons] at hdisj
    by_cases hqB : q ∈ B
    · rw [blocksSnapshot_cons_of_mem hqB] at hpq ⊢
      rw [blocksSnapshot_cons_of_mem hpq]
    · have hq' : q ∈ unionBlocks bs := by
        simp only [unionBlocks_cons, mem_union, hqB, false_or] at hq
        exact hq
      rw [blocksSnapshot_cons_of_notMem hqB hq'] at hpq ⊢
      by_cases hpB : p ∈ B
      · rw [blocksSnapshot_cons_of_mem hpB]
        exact subset_union_left
      · have hp_mem : p ∈ blocksSnapshot bs q := (mem_union.mp hpq).resolve_left hpB
        have hp' : p ∈ unionBlocks bs := blocksSnapshot_subset_unionBlocks bs q hp_mem
        rw [blocksSnapshot_cons_of_notMem hpB hp']
        exact union_subset_union_right (ih hdisj.2 hq' hp_mem)

/-- A one-shot Immediate Snapshot (`IS`) schedule over active processes `U : Finset V`: an ordered
partition `(B₁, …, Bₖ)` of `U` into nonempty pairwise-disjoint concurrent write-scan blocks
([BorowskyGafni1997], §§3.4–3.5, p. 5). -/
@[ext]
structure ISSchedule (U : Finset V) where
  /-- Ordered list of concurrent write-then-snapshot blocks. -/
  blocks : List (Finset V)
  /-- Every block in the schedule is nonempty. -/
  blocks_nonempty : ∀ B ∈ blocks, B.Nonempty
  /-- Distinct blocks in the schedule are pairwise disjoint. -/
  blocks_pairwise_disjoint : blocks.Pairwise Disjoint
  /-- The union of all blocks equals the active process set `U`. -/
  union_blocks : unionBlocks blocks = U

instance instDecidableEqISSchedule (U : Finset V) : DecidableEq (ISSchedule U) :=
  fun π₁ π₂ => decidable_of_iff (π₁.blocks = π₂.blocks) ISSchedule.ext_iff.symm

/-- Auxiliary enumeration of ordered partitions of `rem` of length at most `k`. -/
@[expose]
def orderedPartitionsAux : ℕ → Finset V → Finset (List (Finset V))
  | 0, rem => if rem = ∅ then {[]} else ∅
  | k + 1, rem =>
    (if rem = ∅ then {[]} else ∅) ∪
      (rem.powerset.filter Finset.Nonempty).biUnion fun B =>
        (orderedPartitionsAux k (rem \ B)).image (B :: ·)

theorem mem_orderedPartitionsAux {k : ℕ} {rem : Finset V} {bs : List (Finset V)} :
    bs ∈ orderedPartitionsAux k rem ↔
      bs.length ≤ k ∧ (∀ B ∈ bs, B.Nonempty) ∧ bs.Pairwise Disjoint ∧ unionBlocks bs = rem := by
  induction k generalizing rem bs with
  | zero =>
    simp only [orderedPartitionsAux, Nat.le_zero, List.length_eq_zero_iff]
    split_ifs with hrem
    · subst hrem
      constructor
      · intro h
        rw [mem_singleton.mp h]
        exact ⟨rfl, by simp, List.Pairwise.nil, rfl⟩
      · rintro ⟨rfl, -, -, -⟩
        exact mem_singleton_self []
    · simp only [notMem_empty, false_iff, not_and]
      rintro rfl _ _ hu
      exact hrem hu.symm
  | succ k ih =>
    simp only [orderedPartitionsAux, mem_union, mem_biUnion, mem_filter, mem_powerset, mem_image]
    cases bs with
    | nil =>
      constructor
      · rintro (h | ⟨B, -, tl, -, hcons⟩)
        · split_ifs at h with hrem
          · exact ⟨Nat.zero_le _, by simp, List.Pairwise.nil, hrem.symm⟩
          · exact absurd h (notMem_empty _)
        · cases hcons
      · rintro ⟨-, -, -, hu⟩
        left
        have hrem : rem = ∅ := hu.symm
        simp only [hrem, ↓reduceIte, mem_singleton]
    | cons B tl =>
      constructor
      · rintro (h | ⟨B', ⟨hB'sub, hB'ne⟩, tl', htl', hcons⟩)
        · split_ifs at h <;> simp at h
        · obtain ⟨rfl, rfl⟩ := List.cons.inj hcons
          obtain ⟨hlen, hne, hdisj, hu⟩ := ih.mp htl'
          have hdisjB : Disjoint B' (unionBlocks tl') := by
            rw [hu]
            exact disjoint_sdiff_self_right
          exact ⟨Nat.succ_le_succ hlen, List.forall_mem_cons.mpr ⟨hB'ne, hne⟩,
            List.pairwise_cons.mpr ⟨disjoint_unionBlocks_right.mp hdisjB, hdisj⟩,
            by rw [unionBlocks_cons, hu, union_sdiff_of_subset hB'sub]⟩
      · rintro ⟨hlen, hne, hdisj, hu⟩
        right
        rw [List.pairwise_cons] at hdisj
        have hBne : B.Nonempty := hne B List.mem_cons_self
        have hBsub : B ⊆ rem := by
          rw [← hu, unionBlocks_cons]
          exact subset_union_left
        have hdisjB : Disjoint B (unionBlocks tl) := disjoint_unionBlocks_right.mpr hdisj.1
        have hu_tl : unionBlocks tl = rem \ B := by
          rw [← hu, unionBlocks_cons, union_sdiff_cancel_left hdisjB]
        exact ⟨B, ⟨hBsub, hBne⟩, tl, ih.mpr ⟨Nat.le_of_succ_le_succ hlen,
          (List.forall_mem_cons.mp hne).2, hdisj.2, hu_tl⟩, rfl⟩

/-- Computable `Finset` of all one-shot `IS` schedules on `U`. -/
@[expose]
def allISchedules (U : Finset V) : Finset (ISSchedule U) :=
  (orderedPartitionsAux #U U).attach.map
    ⟨fun (x : {bs // bs ∈ orderedPartitionsAux #U U}) =>
      ({ blocks := x.1
         blocks_nonempty := by
           obtain ⟨-, hne, -, -⟩ := mem_orderedPartitionsAux.mp x.2
           exact hne
         blocks_pairwise_disjoint := by
           obtain ⟨-, -, hdisj, -⟩ := mem_orderedPartitionsAux.mp x.2
           exact hdisj
         union_blocks := by
           obtain ⟨-, -, -, hu⟩ := mem_orderedPartitionsAux.mp x.2
           exact hu } : ISSchedule U),
     fun _ _ h => Subtype.ext (congrArg ISSchedule.blocks h)⟩

theorem mem_allISchedules {U : Finset V} (π : ISSchedule U) : π ∈ allISchedules U := by
  unfold allISchedules
  rw [mem_map]
  have hlen : π.blocks.length ≤ #U := by
    have h := length_le_card_unionBlocks π.blocks_nonempty π.blocks_pairwise_disjoint
    rwa [π.union_blocks] at h
  have hbs : π.blocks ∈ orderedPartitionsAux #U U :=
    mem_orderedPartitionsAux.mpr ⟨hlen, π.blocks_nonempty, π.blocks_pairwise_disjoint,
      π.union_blocks⟩
  exact ⟨⟨π.blocks, hbs⟩, mem_attach _ _, rfl⟩

instance instFintypeISSchedule (U : Finset V) : Fintype (ISSchedule U) where
  elems := allISchedules U
  complete := mem_allISchedules

/-- The unique one-shot `IS` schedule on the empty process set `∅`. -/
@[expose]
def ISSchedule.empty : ISSchedule (∅ : Finset V) where
  blocks := []
  blocks_nonempty _ h := nomatch h
  blocks_pairwise_disjoint := List.Pairwise.nil
  union_blocks := rfl

@[simp]
theorem ISSchedule.blocks_eq_nil_of_empty (π : ISSchedule (∅ : Finset V)) : π.blocks = [] := by
  cases h : π.blocks with
  | nil => rfl
  | cons B bs =>
    have hne := π.blocks_nonempty B (h ▸ List.mem_cons_self)
    have hu := π.union_blocks
    rw [h, unionBlocks_cons, union_eq_empty] at hu
    exact absurd hu.1 hne.ne_empty

/-- Snapshot set observed by process `p` in one-shot `IS` schedule `π : ISSchedule U`. -/
@[expose]
def ISSchedule.snapshot {U : Finset V} (π : ISSchedule U) (p : V) : Finset V :=
  blocksSnapshot π.blocks p

theorem ISSchedule.snapshot_of_notMem {U : Finset V} (π : ISSchedule U) {p : V} (hp : p ∉ U) :
    π.snapshot p = ∅ :=
  blocksSnapshot_of_notMem fun h => hp (π.union_blocks ▸ h)

theorem ISSchedule.self_mem_snapshot {U : Finset V} (π : ISSchedule U) {p : V} (hp : p ∈ U) :
    p ∈ π.snapshot p :=
  self_mem_blocksSnapshot (π.union_blocks.symm ▸ hp)

theorem ISSchedule.snapshot_subset {U : Finset V} (π : ISSchedule U) (p : V) :
    π.snapshot p ⊆ U := by
  have h := blocksSnapshot_subset_unionBlocks π.blocks p
  rwa [π.union_blocks] at h

theorem ISSchedule.snapshot_containment {U : Finset V} (π : ISSchedule U) {p q : V}
    (hp : p ∈ U) (hq : q ∈ U) :
    π.snapshot p ⊆ π.snapshot q ∨ π.snapshot q ⊆ π.snapshot p :=
  blocksSnapshot_containment (π.union_blocks.symm ▸ hp) (π.union_blocks.symm ▸ hq)

theorem ISSchedule.snapshot_immediacy {U : Finset V} (π : ISSchedule U) {p q : V}
    (hq : q ∈ U) (hpq : p ∈ π.snapshot q) :
    π.snapshot p ⊆ π.snapshot q :=
  blocksSnapshot_immediacy π.blocks_pairwise_disjoint (π.union_blocks.symm ▸ hq) hpq

/-! ### Borowsky–Gafni immediate-snapshot characterization -/

/-- Borowsky–Gafni immediate-snapshot axioms for a set assignment `S : V → Finset V` over active
processes `U : Finset V` ([BorowskyGafni1997], §3.5, conditions 1–3, p. 5): inactive processes
observe `∅`, active snapshots lie in `U`, and active processes satisfy self-inclusion, containment,
and immediacy. -/
structure IsImmediateSnapshotOn (U : Finset V) (S : V → Finset V) : Prop where
  /-- Non-participating processes have empty snapshot. -/
  outside : ∀ p ∉ U, S p = ∅
  /-- Every active process's snapshot is a subset of `U`. -/
  subset : ∀ p ∈ U, S p ⊆ U
  /-- **Self-inclusion:** every active process observes itself (`p ∈ S p`). -/
  self_mem : ∀ p ∈ U, p ∈ S p
  /-- **Containment:** any two active processes' snapshots are comparable under `⊆`. -/
  containment : ∀ p ∈ U, ∀ q ∈ U, S p ⊆ S q ∨ S q ⊆ S p
  /-- **Immediacy:** if `q` observes `p`, then `q` observes everything `p` observed. -/
  immediacy : ∀ p ∈ U, ∀ q ∈ U, p ∈ S q → S p ⊆ S q

/-- Global Borowsky–Gafni immediate-snapshot axioms on all processes `V`
([BorowskyGafni1997], §3.5, conditions 1–3, p. 5). -/
structure IsImmediateSnapshot (S : V → Finset V) : Prop where
  /-- **Self-inclusion:** `∀ p, p ∈ S p`. -/
  self_mem : ∀ p : V, p ∈ S p
  /-- **Containment:** `∀ p q, S p ⊆ S q ∨ S q ⊆ S p`. -/
  containment : ∀ p q : V, S p ⊆ S q ∨ S q ⊆ S p
  /-- **Immediacy:** `∀ p q, p ∈ S q → S p ⊆ S q`. -/
  immediacy : ∀ p q : V, p ∈ S q → S p ⊆ S q

omit [DecidableEq V] in
theorem isImmediateSnapshotOn_univ_iff [Fintype V] {S : V → Finset V} :
    IsImmediateSnapshotOn (univ : Finset V) S ↔ IsImmediateSnapshot S := by
  constructor
  · intro h
    exact ⟨fun p => h.self_mem p (mem_univ p),
      fun p q => h.containment p (mem_univ p) q (mem_univ q),
      fun p q hpq => h.immediacy p (mem_univ p) q (mem_univ q) hpq⟩
  · intro h
    exact ⟨fun p hp => absurd (mem_univ p) hp,
      fun _ _ => subset_univ _,
      fun p _ => h.self_mem p,
      fun p _ q _ => h.containment p q,
      fun p _ q _ => h.immediacy p q⟩

/-- Every one-shot `IS` schedule on `U` satisfies `IsImmediateSnapshotOn U`. -/
theorem ISSchedule.isImmediateSnapshotOn {U : Finset V} (π : ISSchedule U) :
    IsImmediateSnapshotOn U π.snapshot where
  outside _ hp := π.snapshot_of_notMem hp
  subset p _ := π.snapshot_subset p
  self_mem _ hp := π.self_mem_snapshot hp
  containment _ hp _ hq := π.snapshot_containment hp hq
  immediacy _ _ _ hq hpq := π.snapshot_immediacy hq hpq

/-- Every full-system one-shot `IS` schedule satisfies `IsImmediateSnapshot`. -/
theorem ISSchedule.isImmediateSnapshot [Fintype V] (π : ISSchedule (univ : Finset V)) :
    IsImmediateSnapshot π.snapshot :=
  isImmediateSnapshotOn_univ_iff.mp π.isImmediateSnapshotOn

/-- Minimal block of an immediate-snapshot map `S` on a nonempty active set `U`: the processes in
`U` whose snapshot is contained in every active process's snapshot. -/
private def minBlock (U : Finset V) (S : V → Finset V) : Finset V :=
  U.filter fun p => ∀ q ∈ U, S p ⊆ S q

private theorem minBlock_spec {U : Finset V} (hne : U.Nonempty) {S : V → Finset V}
    (hS : IsImmediateSnapshotOn U S) :
    (minBlock U S).Nonempty ∧ minBlock U S ⊆ U ∧
      (∀ p ∈ minBlock U S, S p = minBlock U S) ∧
      (∀ q ∈ U, minBlock U S ⊆ S q) := by
  have himg : (U.image fun p => #(S p)).Nonempty := hne.image _
  obtain ⟨p₀, hp₀U, hcMin⟩ := mem_image.mp ((U.image fun p => #(S p)).min'_mem himg)
  have hp₀_sub : ∀ q ∈ U, S p₀ ⊆ S q := by
    intro q hqU
    rcases hS.containment p₀ hp₀U q hqU with h | h
    · exact h
    · have hle : #(S p₀) ≤ #(S q) := by
        rw [hcMin]
        exact (U.image fun p => #(S p)).min'_le #(S q) (mem_image_of_mem _ hqU)
      exact (eq_of_subset_of_card_le h hle).symm.subset
  have hSp : ∀ p ∈ S p₀, S p = S p₀ := fun p hp =>
    Subset.antisymm (hS.immediacy p (hS.subset p₀ hp₀U hp) p₀ hp₀U hp)
      (hp₀_sub p (hS.subset p₀ hp₀U hp))
  have hB_eq : minBlock U S = S p₀ := by
    ext p
    simp only [minBlock, mem_filter]
    constructor
    · rintro ⟨hpU, hpMin⟩
      exact Subset.antisymm (hpMin p₀ hp₀U) (hp₀_sub p hpU) ▸ hS.self_mem p hpU
    · intro hp
      exact ⟨hS.subset p₀ hp₀U hp, fun q hqU => hSp p hp ▸ hp₀_sub q hqU⟩
  rw [hB_eq]
  exact ⟨⟨p₀, hS.self_mem p₀ hp₀U⟩, hS.subset p₀ hp₀U, hSp, hp₀_sub⟩

private theorem isImmediateSnapshotOn_sdiff_minBlock {U : Finset V}
    {S : V → Finset V} (hS : IsImmediateSnapshotOn U S) :
    IsImmediateSnapshotOn (U \ minBlock U S)
      (fun p => if p ∈ U \ minBlock U S then S p \ minBlock U S else ∅) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [hp, ↓reduceIte]
  · intro p hp
    simp only [hp, ↓reduceIte]
    exact sdiff_subset_sdiff (hS.subset p (sdiff_subset hp)) Subset.rfl
  · intro p hp
    simp only [hp, ↓reduceIte]
    rw [mem_sdiff] at hp ⊢
    exact ⟨hS.self_mem p hp.1, hp.2⟩
  · intro p hp q hq
    simp only [hp, hq, ↓reduceIte]
    rcases hS.containment p (sdiff_subset hp) q (sdiff_subset hq) with h | h
    · exact Or.inl (sdiff_subset_sdiff h Subset.rfl)
    · exact Or.inr (sdiff_subset_sdiff h Subset.rfl)
  · intro p hp q hq hpq
    simp only [hp, hq, ↓reduceIte] at hpq ⊢
    exact sdiff_subset_sdiff
      (hS.immediacy p (sdiff_subset hp) q (sdiff_subset hq) (sdiff_subset hpq)) Subset.rfl

/-- Fuel-bounded structural recursion reconstructing the ordered-partition blocks of `S` on `U`. -/
private def reconstructBlocksAux :
    ℕ → (U : Finset V) → (S : V → Finset V) → IsImmediateSnapshotOn U S → List (Finset V)
  | 0, _, _, _ => []
  | fuel + 1, U, S, hS =>
    if U.Nonempty then
      let B := minBlock U S
      B :: reconstructBlocksAux fuel (U \ B)
        (fun p => if p ∈ U \ B then S p \ B else ∅)
        (isImmediateSnapshotOn_sdiff_minBlock hS)
    else
      []

private theorem reconstructBlocksAux_spec :
    ∀ (fuel : ℕ) (U : Finset V) (S : V → Finset V) (hS : IsImmediateSnapshotOn U S),
      #U ≤ fuel →
      (∀ B ∈ reconstructBlocksAux fuel U S hS, B.Nonempty) ∧
        (reconstructBlocksAux fuel U S hS).Pairwise Disjoint ∧
        unionBlocks (reconstructBlocksAux fuel U S hS) = U ∧
        blocksSnapshot (reconstructBlocksAux fuel U S hS) = S
  | 0, U, S, hS, hfuel => by
    have hU : U = ∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero hfuel)
    subst hU
    refine ⟨by simp [reconstructBlocksAux], List.Pairwise.nil, rfl, ?_⟩
    funext p
    rw [reconstructBlocksAux, blocksSnapshot_nil, hS.outside p (notMem_empty p)]
  | fuel + 1, U, S, hS, hfuel => by
    simp only [reconstructBlocksAux]
    split_ifs with hne
    · set B := minBlock U S
      obtain ⟨hBne, hBsub, hBeq, hBmin⟩ := minBlock_spec hne hS
      set S' : V → Finset V := fun p => if p ∈ U \ B then S p \ B else ∅
      have hS' : IsImmediateSnapshotOn (U \ B) S' := isImmediateSnapshotOn_sdiff_minBlock hS
      have hlt : #(U \ B) < #U := card_lt_card (sdiff_lt hBsub hBne.ne_empty)
      obtain ⟨hne', hdisj', hu', hsnap'⟩ :=
        reconstructBlocksAux_spec fuel (U \ B) S' hS' (Nat.le_of_lt_succ (lt_of_lt_of_le hlt hfuel))
      have hdisjB : Disjoint B (unionBlocks (reconstructBlocksAux fuel (U \ B) S' hS')) := by
        rw [hu']
        exact disjoint_sdiff_self_right
      have hu : unionBlocks (B :: reconstructBlocksAux fuel (U \ B) S' hS') = U := by
        rw [unionBlocks_cons, hu', union_sdiff_of_subset hBsub]
      refine ⟨List.forall_mem_cons.mpr ⟨hBne, hne'⟩,
        List.pairwise_cons.mpr ⟨disjoint_unionBlocks_right.mp hdisjB, hdisj'⟩, hu,
        funext fun p => ?_⟩
      by_cases hpB : p ∈ B
      · rw [blocksSnapshot_cons_of_mem hpB, hBeq p hpB]
      · by_cases hpU : p ∈ U
        · have hpU' : p ∈ U \ B := mem_sdiff.mpr ⟨hpU, hpB⟩
          rw [blocksSnapshot_cons_of_notMem hpB (by rwa [hu']), hsnap']
          simp only [S', hpU', ↓reduceIte]
          exact union_sdiff_of_subset (hBmin p hpU)
        · rw [blocksSnapshot_of_notMem (by rwa [hu]), hS.outside p hpU]
    · rw [not_nonempty_iff_eq_empty] at hne
      subst hne
      refine ⟨by simp, List.Pairwise.nil, rfl, ?_⟩
      funext p
      rw [blocksSnapshot_nil, hS.outside p (notMem_empty p)]

/-- Reconstruct the one-shot `IS` schedule on `U` corresponding to a set assignment `S` satisfying
`IsImmediateSnapshotOn U S`. -/
def ISSchedule.ofImmediateSnapshotOn {U : Finset V} (S : V → Finset V)
    (hS : IsImmediateSnapshotOn U S) : ISSchedule U where
  blocks := reconstructBlocksAux #U U S hS
  blocks_nonempty := by
    obtain ⟨hne, -, -, -⟩ := reconstructBlocksAux_spec #U U S hS le_rfl
    exact hne
  blocks_pairwise_disjoint := by
    obtain ⟨-, hdisj, -, -⟩ := reconstructBlocksAux_spec #U U S hS le_rfl
    exact hdisj
  union_blocks := by
    obtain ⟨-, -, hu, -⟩ := reconstructBlocksAux_spec #U U S hS le_rfl
    exact hu

@[simp]
theorem ISSchedule.snapshot_ofImmediateSnapshotOn {U : Finset V} (S : V → Finset V)
    (hS : IsImmediateSnapshotOn U S) :
    (ISSchedule.ofImmediateSnapshotOn S hS).snapshot = S := by
  obtain ⟨-, -, -, hsnap⟩ := reconstructBlocksAux_spec #U U S hS le_rfl
  exact hsnap

/-- The first block lies in the snapshot of every process of the block list. -/
private theorem subset_blocksSnapshot_cons {B : Finset V} {bs : List (Finset V)} {p : V}
    (hp : p ∈ unionBlocks (B :: bs)) : B ⊆ blocksSnapshot (B :: bs) p := by
  by_cases hpB : p ∈ B
  · rw [blocksSnapshot_cons_of_mem hpB]
  · rw [blocksSnapshot_cons_of_notMem hpB ((mem_union.mp hp).resolve_left hpB)]
    exact subset_union_left

/-- Two one-shot `IS` schedules on `U` with identical snapshot maps are equal. -/
theorem ISSchedule.snapshot_injective {U : Finset V} :
    Function.Injective (ISSchedule.snapshot (U := U)) := by
  suffices ∀ (bs₁ bs₂ : List (Finset V)),
      (∀ B ∈ bs₁, B.Nonempty) → bs₁.Pairwise Disjoint →
      (∀ B ∈ bs₂, B.Nonempty) → bs₂.Pairwise Disjoint →
      unionBlocks bs₁ = unionBlocks bs₂ →
      blocksSnapshot bs₁ = blocksSnapshot bs₂ → bs₁ = bs₂ by
    intro π₁ π₂ h
    ext1
    exact this π₁.blocks π₂.blocks π₁.blocks_nonempty π₁.blocks_pairwise_disjoint
      π₂.blocks_nonempty π₂.blocks_pairwise_disjoint
      (π₁.union_blocks.trans π₂.union_blocks.symm) h
  intro bs₁
  induction bs₁ with
  | nil =>
    intro bs₂ _ _ hne₂ _ hu _
    cases bs₂ with
    | nil => rfl
    | cons B₂ tl₂ =>
      rw [unionBlocks_nil, eq_comm, unionBlocks_cons, union_eq_empty] at hu
      exact absurd hu.1 (hne₂ B₂ List.mem_cons_self).ne_empty
  | cons B₁ tl₁ ih =>
    intro bs₂ hne₁ hdisj₁ hne₂ hdisj₂ hu hsnap
    cases bs₂ with
    | nil =>
      rw [unionBlocks_cons, unionBlocks_nil, union_eq_empty] at hu
      exact absurd hu.1 (hne₁ B₁ List.mem_cons_self).ne_empty
    | cons B₂ tl₂ =>
      obtain ⟨p₁, hp₁⟩ := hne₁ B₁ List.mem_cons_self
      obtain ⟨p₂, hp₂⟩ := hne₂ B₂ List.mem_cons_self
      have hp₁_u₂ : p₁ ∈ unionBlocks (B₂ :: tl₂) := hu ▸ mem_union_left _ hp₁
      have hp₂_u₁ : p₂ ∈ unionBlocks (B₁ :: tl₁) := hu.symm ▸ mem_union_left _ hp₂
      have hB₁_sub : B₁ ⊆ B₂ := by
        have h := subset_blocksSnapshot_cons hp₂_u₁
        rwa [congrFun hsnap p₂, blocksSnapshot_cons_of_mem hp₂] at h
      have hB₂_sub : B₂ ⊆ B₁ := by
        have h := subset_blocksSnapshot_cons hp₁_u₂
        rwa [← congrFun hsnap p₁, blocksSnapshot_cons_of_mem hp₁] at h
      obtain rfl : B₁ = B₂ := Subset.antisymm hB₁_sub hB₂_sub
      rw [List.pairwise_cons] at hdisj₁ hdisj₂
      have hdisj_tl₁ := disjoint_unionBlocks_right.mpr hdisj₁.1
      have hdisj_tl₂ := disjoint_unionBlocks_right.mpr hdisj₂.1
      have hu_tl : unionBlocks tl₁ = unionBlocks tl₂ := by
        rw [← union_sdiff_cancel_left hdisj_tl₁, ← union_sdiff_cancel_left hdisj_tl₂]
        exact congrArg (· \ B₁) hu
      congr 1
      refine ih tl₂ (fun C hC => hne₁ C (List.mem_cons_of_mem B₁ hC)) hdisj₁.2
        (fun C hC => hne₂ C (List.mem_cons_of_mem B₁ hC)) hdisj₂.2 hu_tl (funext fun p => ?_)
      by_cases hp_tl₁ : p ∈ unionBlocks tl₁
      · have hpB : p ∉ B₁ := disjoint_right.mp hdisj_tl₁ hp_tl₁
        have hp_eq := congrFun hsnap p
        rw [blocksSnapshot_cons_of_notMem hpB hp_tl₁,
          blocksSnapshot_cons_of_notMem hpB (hu_tl ▸ hp_tl₁)] at hp_eq
        rw [← union_sdiff_cancel_left
            (hdisj_tl₁.mono_right (blocksSnapshot_subset_unionBlocks tl₁ p)), hp_eq,
          union_sdiff_cancel_left (hdisj_tl₂.mono_right (blocksSnapshot_subset_unionBlocks tl₂ p))]
      · rw [blocksSnapshot_of_notMem hp_tl₁, blocksSnapshot_of_notMem (hu_tl ▸ hp_tl₁)]

@[simp]
theorem ISSchedule.ofImmediateSnapshotOn_snapshot {U : Finset V} (π : ISSchedule U) :
    ISSchedule.ofImmediateSnapshotOn π.snapshot π.isImmediateSnapshotOn = π :=
  ISSchedule.snapshot_injective (ISSchedule.snapshot_ofImmediateSnapshotOn _ _)

/-- One-shot immediate-snapshot characterization step for #7504 (after
[Borowsky and Gafni, §3.5, conditions 1–3, p. 5][BorowskyGafni1997]): ordered partitions of `U`
into nonempty disjoint blocks correspond bijectively to set assignments satisfying
`IsImmediateSnapshotOn U`. -/
def ISSchedule.equivImmediateSnapshotOn (U : Finset V) :
    ISSchedule U ≃ {S : V → Finset V // IsImmediateSnapshotOn U S} where
  toFun π := ⟨π.snapshot, π.isImmediateSnapshotOn⟩
  invFun S := ISSchedule.ofImmediateSnapshotOn S.1 S.2
  left_inv := ISSchedule.ofImmediateSnapshotOn_snapshot
  right_inv S := Subtype.ext (ISSchedule.snapshot_ofImmediateSnapshotOn S.1 S.2)

/-- One-shot immediate-snapshot characterization step for #7504 (after
[Borowsky and Gafni, §3.5, conditions 1–3, p. 5][BorowskyGafni1997]): full-system ordered
partitions correspond bijectively to set assignments satisfying self-inclusion, containment, and
immediacy. -/
def ISSchedule.equivImmediateSnapshot [Fintype V] :
    ISSchedule (univ : Finset V) ≃ {S : V → Finset V // IsImmediateSnapshot S} :=
  (ISSchedule.equivImmediateSnapshotOn (univ : Finset V)).trans
    (Equiv.subtypeEquivRight fun _ => isImmediateSnapshotOn_univ_iff)

@[simp]
theorem ISSchedule.snapshot_equivImmediateSnapshot_symm [Fintype V]
    (S : {S : V → Finset V // IsImmediateSnapshot S}) :
    (ISSchedule.equivImmediateSnapshot.symm S).snapshot = S.1 :=
  ISSchedule.snapshot_ofImmediateSnapshotOn S.1 (isImmediateSnapshotOn_univ_iff.mpr S.2)

/-- One-shot immediate-snapshot unique-schedule characterization step for #7504 (after
[Borowsky and Gafni, §3.5, conditions 1–3, p. 5][BorowskyGafni1997]): a map `S : V → Finset V`
satisfies self-inclusion, containment, and immediacy if and only if there exists a unique one-shot
`IS` schedule `π` on `V` with `π.snapshot = S`. -/
theorem isImmediateSnapshot_iff_existsUnique_schedule [Fintype V] (S : V → Finset V) :
    IsImmediateSnapshot S ↔ ∃! π : ISSchedule (univ : Finset V), π.snapshot = S := by
  constructor
  · intro hS
    refine ⟨ISSchedule.ofImmediateSnapshotOn S (isImmediateSnapshotOn_univ_iff.mpr hS),
      ISSchedule.snapshot_ofImmediateSnapshotOn S _, fun π hπ => ?_⟩
    exact ISSchedule.snapshot_injective
      (hπ.trans (ISSchedule.snapshot_ofImmediateSnapshotOn S _).symm)
  · rintro ⟨π, rfl, -⟩
    exact π.isImmediateSnapshot

end OrderedPartitions

/-! ### `R`-round Iterated Immediate Snapshot (`IIS`) full-information views -/

section IISViews

/-- Initial (`0`-round) `IIS` view of a process: its identity `proc` paired with its initial input
`input` ([BorowskyGafni1997], §3.5, p. 5). -/
@[ext]
structure InitView (V Input : Type*) where
  /-- Participating process identity. -/
  proc : V
  /-- Initial input value of `proc`. -/
  input : Input
  deriving @[expose] DecidableEq

/-- Single-step (`(r + 1)`-round) `IIS` view of a process: its identity `proc` paired with the
`Finset` of round-`r` views observed in round `r + 1` ([BorowskyGafni1997], §3.5, p. 5). -/
@[ext]
structure StepView (V View : Type*) where
  /-- Participating process identity. -/
  proc : V
  /-- Immediate snapshot of prior-round views observed by `proc`. -/
  seen : Finset View
  deriving @[expose] DecidableEq

/-- Full-information `IIS` local view after `R` rounds over processes `V` and inputs `Input`. -/
@[expose]
def IISView (V Input : Type*) : ℕ → Type _
  | 0 => InitView V Input
  | r + 1 => StepView V (IISView V Input r)

/-- Explicit decidable equality on `IISView V Input R`. -/
@[expose]
def decEqIISView {V Input : Type*} [DecidableEq V] [DecidableEq Input] :
    (R : ℕ) → DecidableEq (IISView V Input R)
  | 0 => inferInstanceAs (DecidableEq (InitView V Input))
  | R + 1 =>
    letI : DecidableEq (IISView V Input R) := decEqIISView R
    inferInstanceAs (DecidableEq (StepView V (IISView V Input R)))

instance instDecidableEqIISView {V Input : Type*} [DecidableEq V] [DecidableEq Input]
    {R : ℕ} : DecidableEq (IISView V Input R) :=
  decEqIISView R

/-- Owner process identity of an `R`-round `IIS` view. -/
@[expose]
def IISView.proc {V Input : Type*} : {R : ℕ} → IISView V Input R → V
  | 0 => InitView.proc
  | _ + 1 => StepView.proc

/-- Participating process carrier of an `R`-round `IIS` view: all processes whose initial inputs
causally contributed to the view. -/
@[expose]
def IISView.carrier {V Input : Type*} [DecidableEq V] :
    {R : ℕ} → IISView V Input R → Finset V
  | 0 => fun v => {InitView.proc v}
  | R + 1 =>
    let prev := IISView.carrier (R := R)
    fun v => insert (StepView.proc v) ((StepView.seen v).biUnion prev)

/-- Set of initial input values causally observed in an `R`-round `IIS` view. -/
@[expose]
def IISView.carrierInputs {V Input : Type*} [DecidableEq Input] :
    {R : ℕ} → IISView V Input R → Finset Input
  | 0 => fun v => {InitView.input v}
  | R + 1 =>
    let prev := IISView.carrierInputs (R := R)
    fun v => (StepView.seen v).biUnion prev

theorem IISView.proc_mem_carrier {V Input : Type*} [DecidableEq V] {R : ℕ}
    (v : IISView V Input R) : v.proc ∈ v.carrier := by
  cases R with
  | zero => exact mem_singleton_self _
  | succ R => exact mem_insert_self _ _

theorem IISView.carrier_nonempty {V Input : Type*} [DecidableEq V] {R : ℕ}
    (v : IISView V Input R) : v.carrier.Nonempty :=
  ⟨v.proc, v.proc_mem_carrier⟩

/-- Execute `R` rounds of the full-information Iterated Immediate Snapshot (`IIS`) protocol on
active process set `U : Finset V` from input assignment `inp : V → Input` along schedule sequence
`E : Fin R → ISSchedule U` ([BorowskyGafni1997], §3.5, p. 5). -/
@[expose]
def iisRun {V Input : Type*} [DecidableEq V] [DecidableEq Input] {U : Finset V}
    (inp : V → Input) : {R : ℕ} → (Fin R → ISSchedule U) → V → IISView V Input R
  | 0, _, p => ⟨p, inp p⟩
  | R + 1, E, p => ⟨p, ((E (Fin.last R)).snapshot p).image (iisRun inp (Fin.init E))⟩

@[simp]
theorem iisRun_zero {V Input : Type*} [DecidableEq V] [DecidableEq Input] {U : Finset V}
    (inp : V → Input) (E : Fin 0 → ISSchedule U) (p : V) :
    iisRun inp E p = (⟨p, inp p⟩ : InitView V Input) := rfl

theorem iisRun_succ {V Input : Type*} [DecidableEq V] [DecidableEq Input] {U : Finset V}
    (inp : V → Input) {R : ℕ} (E : Fin (R + 1) → ISSchedule U) (p : V) :
    iisRun inp E p =
      (⟨p, ((E (Fin.last R)).snapshot p).image (iisRun inp (Fin.init E))⟩ :
        StepView V (IISView V Input R)) := rfl

@[simp]
theorem iisRun_proc {V Input : Type*} [DecidableEq V] [DecidableEq Input] {U : Finset V}
    (inp : V → Input) {R : ℕ} (E : Fin R → ISSchedule U) (p : V) :
    (iisRun inp E p).proc = p := by
  cases R <;> rfl

theorem self_mem_carrier_iisRun {V Input : Type*} [DecidableEq V] [DecidableEq Input]
    {U : Finset V} (inp : V → Input) {R : ℕ} (E : Fin R → ISSchedule U) (p : V) :
    p ∈ (iisRun inp E p).carrier := by
  have h := (iisRun inp E p).proc_mem_carrier
  rwa [iisRun_proc] at h

theorem carrier_iisRun_subset {V Input : Type*} [DecidableEq V] [DecidableEq Input]
    {U : Finset V} (inp : V → Input) {R : ℕ} (E : Fin R → ISSchedule U) {p : V} (hp : p ∈ U) :
    (iisRun inp E p).carrier ⊆ U := by
  induction R generalizing p with
  | zero =>
    change ({p} : Finset V) ⊆ U
    exact singleton_subset_iff.mpr hp
  | succ R ih =>
    rw [iisRun_succ]
    change insert p
      ((((E (Fin.last R)).snapshot p).image (iisRun inp (Fin.init E))).biUnion
        (IISView.carrier (R := R))) ⊆ U
    refine insert_subset hp (biUnion_subset.mpr fun v hv => ?_)
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hv
    exact ih (Fin.init E) ((E (Fin.last R)).snapshot_subset p hq)

theorem carrierInputs_iisRun {V Input : Type*} [DecidableEq V] [DecidableEq Input]
    {U : Finset V} (inp : V → Input) {R : ℕ} (E : Fin R → ISSchedule U) {p : V} (hp : p ∈ U) :
    (iisRun inp E p).carrierInputs = (iisRun inp E p).carrier.image inp := by
  induction R generalizing p with
  | zero =>
    change ({inp p} : Finset Input) = ({p} : Finset V).image inp
    simp only [image_singleton]
  | succ R ih =>
    rw [iisRun_succ]
    change (((E (Fin.last R)).snapshot p).image (iisRun inp (Fin.init E))).biUnion
        (IISView.carrierInputs (R := R)) =
      (insert p
        ((((E (Fin.last R)).snapshot p).image (iisRun inp (Fin.init E))).biUnion
          (IISView.carrier (R := R)))).image inp
    have hself : p ∈ (((E (Fin.last R)).snapshot p).image (iisRun inp (Fin.init E))).biUnion
        (IISView.carrier (R := R)) := by
      rw [mem_biUnion]
      exact ⟨iisRun inp (Fin.init E) p,
        mem_image_of_mem _ ((E (Fin.last R)).self_mem_snapshot hp),
        self_mem_carrier_iisRun inp (Fin.init E) p⟩
    rw [insert_eq_of_mem hself]
    ext x
    simp only [mem_biUnion, mem_image]
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, hx⟩
      rw [ih (Fin.init E) ((E (Fin.last R)).snapshot_subset p hq)] at hx
      obtain ⟨r, hr, rfl⟩ := mem_image.mp hx
      exact ⟨r, ⟨_, ⟨q, hq, rfl⟩, hr⟩, rfl⟩
    · rintro ⟨r, ⟨_, ⟨q, hq, rfl⟩, hr⟩, rfl⟩
      refine ⟨iisRun inp (Fin.init E) q, ⟨q, hq, rfl⟩, ?_⟩
      rw [ih (Fin.init E) ((E (Fin.last R)).snapshot_subset p hq)]
      exact mem_image_of_mem inp hr

/-- View locality of `R`-round `IIS` runs: process `p`'s view depends only on the initial inputs of
processes in `(iisRun inp₁ E p).carrier`. -/
theorem iisRun_congr_carrier {V Input : Type*} [DecidableEq V] [DecidableEq Input]
    {U : Finset V} {inp₁ inp₂ : V → Input} {R : ℕ} (E : Fin R → ISSchedule U) (p : V)
    (heq : ∀ q ∈ (iisRun inp₁ E p).carrier, inp₁ q = inp₂ q) :
    iisRun inp₁ E p = iisRun inp₂ E p := by
  induction R generalizing p with
  | zero =>
    have hp : inp₁ p = inp₂ p := heq p (mem_singleton_self p)
    exact congrArg (InitView.mk p) hp
  | succ R ih =>
    rw [iisRun_succ, iisRun_succ]
    congr 1
    refine image_congr fun q hq => ih (Fin.init E) q fun r hr => heq r ?_
    rw [iisRun_succ]
    exact mem_insert_of_mem (mem_biUnion.mpr ⟨iisRun inp₁ (Fin.init E) q,
      mem_image_of_mem _ hq, hr⟩)

/-- Solo-execution carrier property: if process `p` runs first alone (`{p} :: tail`) in every round
of `E`, then `(iisRun inp E p).carrier = {p}`. -/
theorem carrier_iisRun_eq_singleton_of_solo {V Input : Type*} [DecidableEq V] [DecidableEq Input]
    {U : Finset V} (inp : V → Input) {R : ℕ} (E : Fin R → ISSchedule U) {p : V}
    (hsolo : ∀ r : Fin R, ∃ tail, (E r).blocks = {p} :: tail) :
    (iisRun inp E p).carrier = {p} := by
  induction R with
  | zero => rfl
  | succ R ih =>
    obtain ⟨tail, hlast⟩ := hsolo (Fin.last R)
    have hsnap : (E (Fin.last R)).snapshot p = {p} := by
      unfold ISSchedule.snapshot
      rw [hlast, blocksSnapshot_cons_of_mem (mem_singleton_self p)]
    rw [iisRun_succ]
    change insert p
      ((((E (Fin.last R)).snapshot p).image (iisRun inp (Fin.init E))).biUnion
        (IISView.carrier (R := R))) = {p}
    rw [hsnap, image_singleton, singleton_biUnion,
      ih (Fin.init E) (fun r => hsolo r.castSucc), insert_eq_of_mem (mem_singleton_self p)]

/-- Extend an `IS` schedule on `U` to all of `Finset.univ` by scheduling all remaining processes
`univ \ U` concurrently in a single trailing block (when `(univ \ U).Nonempty`). -/
def ISSchedule.extendToUniv {V : Type*} [Fintype V] [DecidableEq V] {U : Finset V}
    (π : ISSchedule U) : ISSchedule (univ : Finset V) :=
  if hrem : (univ \ U).Nonempty then
    { blocks := π.blocks ++ [univ \ U]
      blocks_nonempty := fun B hB => by
        rcases List.mem_append.mp hB with hB | hB
        · exact π.blocks_nonempty B hB
        · rw [List.mem_singleton.mp hB]
          exact hrem
      blocks_pairwise_disjoint := by
        rw [List.pairwise_append]
        refine ⟨π.blocks_pairwise_disjoint, List.pairwise_singleton _ _, fun A hA C hC => ?_⟩
        rw [List.mem_singleton.mp hC]
        have hAU : A ⊆ U := by
          rw [← π.union_blocks]
          intro x hx
          exact mem_unionBlocks.mpr ⟨A, hA, hx⟩
        exact Disjoint.mono_left hAU disjoint_sdiff_self_right
      union_blocks := by
        rw [unionBlocks_append, π.union_blocks, unionBlocks_cons, unionBlocks_nil, union_empty,
          union_sdiff_of_subset (subset_univ U)] }
  else
    have hU : U = univ := by
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at hrem
      exact Subset.antisymm (subset_univ U) hrem
    hU ▸ π

theorem ISSchedule.snapshot_extendToUniv_of_mem {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} (π : ISSchedule U) {p : V} (hp : p ∈ U) :
    π.extendToUniv.snapshot p = π.snapshot p := by
  unfold ISSchedule.extendToUniv
  split_ifs with hrem
  · exact blocksSnapshot_append_of_mem_left (π.union_blocks.symm ▸ hp)
  · have hU : U = univ := by
      rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at hrem
      exact Subset.antisymm (subset_univ U) hrem
    subst hU
    rfl

theorem iisRun_extendToUniv_of_mem {V Input : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq Input] {U : Finset V} (inp : V → Input) {R : ℕ}
    (E : Fin R → ISSchedule U) {p : V} (hp : p ∈ U) :
    iisRun inp (fun r => (E r).extendToUniv) p = iisRun inp E p := by
  induction R generalizing p with
  | zero => rfl
  | succ R ih =>
    rw [iisRun_succ, iisRun_succ]
    congr 1
    have hsnap : ((E (Fin.last R)).extendToUniv).snapshot p = (E (Fin.last R)).snapshot p :=
      ISSchedule.snapshot_extendToUniv_of_mem (E (Fin.last R)) hp
    rw [hsnap]
    refine image_congr fun q hq => ih (Fin.init E) ((E (Fin.last R)).snapshot_subset p hq)

/-! ### `IIS` decision protocols and carrier-input validity -/

/-- An `R`-round deterministic decision protocol in the Iterated Immediate Snapshot (`IIS`) model:
each process `p : V` maps its `R`-round `IIS` view to an output decision in `Val`. -/
structure IISProtocol (V Val : Type*) (R : ℕ) where
  /-- Per-process decision rule applied after `R` rounds of `IIS`. -/
  decide : V → IISView V Val R → Val

/-- Global input validity of an `R`-round `IIS` protocol: in every full-system execution, every
decided value is the initial input of some process in `V`. -/
@[expose]
def IISProtocol.IsValid {V Val : Type*} [Fintype V] [DecidableEq V] [DecidableEq Val] {R : ℕ}
    (P : IISProtocol V Val R) : Prop :=
  ∀ (inp : V → Val) (E : Fin R → ISSchedule (univ : Finset V)) (p : V),
    P.decide p (iisRun inp E p) ∈ (univ : Finset V).image inp

/-- Carrier-input validity of an `R`-round `IIS` protocol: in every full-system execution, every
process `p` decides an input belonging to a process in `(iisRun inp E p).carrier` (equivalently, in
`(iisRun inp E p).carrierInputs`). -/
@[expose]
def IISProtocol.IsCarrierValid {V Val : Type*} [Fintype V] [DecidableEq V] [DecidableEq Val]
    {R : ℕ} (P : IISProtocol V Val R) : Prop :=
  ∀ (inp : V → Val) (E : Fin R → ISSchedule (univ : Finset V)) (p : V),
    P.decide p (iisRun inp E p) ∈ (iisRun inp E p).carrier.image inp

/-- Iterated immediate snapshot (`IIS`) carrier-validity step for #7504 (after the input-simplex
extension argument of [Herlihy and Shavit, Proof of Theorem 3.3, p. 881][HerlihyShavit1999]):
because `iisRun inp E p` depends only on `inp` restricted to `C = (iisRun inp E p).carrier`,
replacing all inputs outside `C` with `inp p` leaves `p`'s `R`-round view unchanged while
restricting all global inputs to `C.image inp`. -/
theorem IISProtocol.isCarrierValid_of_isValid {V Val : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq Val] {R : ℕ} {P : IISProtocol V Val R} (hval : P.IsValid) :
    P.IsCarrierValid := by
  intro inp E p
  let inp' : V → Val := fun q => if q ∈ (iisRun inp E p).carrier then inp q else inp p
  have hview : iisRun inp E p = iisRun inp' E p :=
    iisRun_congr_carrier E p fun q hq => by
      dsimp only [inp']
      split_ifs
      rfl
  obtain ⟨q, -, hdec⟩ := mem_image.mp (hval inp' E p)
  have hdec' : P.decide p (iisRun inp E p) = inp' q := by
    rw [hview, ← hdec]
  rw [hdec']
  dsimp only [inp']
  split_ifs with hqC
  · exact mem_image_of_mem inp hqC
  · exact mem_image_of_mem inp (self_mem_carrier_iisRun inp E p)

end IISViews

end Cslib.Distributed.SetAgreement
