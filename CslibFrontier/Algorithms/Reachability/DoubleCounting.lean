/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Relation.InductiveCounting
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Equiv.List

/-!
# Double-counting certificates for bounded reachability

This is the branch semantics of Figure 1 in the March 31, 1999 version of
[Reinhardt and Allender, *Making Nondeterminism Unambiguous*][ReinhardtAllender2000],
Section 2, proof of Theorem 2.2. The edges are unweighted, and a scan in a fixed order
makes one choice per vertex: skip it or supply an actual walk of at most `k` edges.
The transcript is indexed by vertex so that permuting scan order cannot introduce spurious
ambiguity. Walks are vertex lists in a directed relation, with no padding steps.

The supplied count must equal the size of the breadth-first round, and the supplied sum
must equal the sum of its shortest distances. The count forces the scan to cover the
round, and the sum forces each supplied walk to be shortest. Thus a successful
transcript determines membership even for a vertex outside the round. Its uniqueness is
equivalent to uniqueness of the shortest walk at every vertex of the round.

## Main results

* `Cslib.DoubleCounting.passes_iff`: exact characterization of successful transcripts.
* `Cslib.DoubleCounting.existsUnique_passes_iff`: exact ambiguity criterion for Figure 1.

This certificate model does not encode machine choice bits or certify the resources of a
machine generating the transcript.
-/

public section

namespace Cslib.DoubleCounting

open Relation Finset

variable {α : Type*} {r : α → α → Prop} {s v : α} {k : ℕ}

/-- The least number of edges in a walk from `s` to `v`, with zero used outside the reachable set.
Only distances of vertices in the current round enter the sum. -/
noncomputable def distance (r : α → α → Prop) (s v : α) : ℕ := by
  classical
  exact if h : ∃ n, RelatesInSteps r s v n then Nat.find h else 0

/-- A reached vertex has a walk whose length is its distance, bounded by the round index. -/
theorem distance_spec (h : v ∈ reachableWithin r s k) :
    RelatesInSteps r s v (distance r s v) ∧ distance r s v ≤ k := by
  classical
  obtain ⟨n, hn, hp⟩ := h
  have hex : ∃ n, RelatesInSteps r s v n := ⟨n, hp⟩
  rw [distance, dite_eq_left hex]
  exact ⟨Nat.find_spec hex, (Nat.find_min' hex hp).trans hn⟩

private theorem distance_le {n : ℕ} (h : RelatesInSteps r s v n) : distance r s v ≤ n := by
  classical
  have hex : ∃ n, RelatesInSteps r s v n := ⟨n, h⟩
  rw [distance, dite_eq_left hex]
  exact Nat.find_min' hex h

variable [Fintype α]

/-- The breadth-first round as a finite set of vertices. -/
noncomputable def round (r : α → α → Prop) (s : α) (k : ℕ) : Finset α :=
  (Set.toFinite (reachableWithin r s k)).toFinset

/-- The finite round contains exactly the vertices reachable within the given number of steps. -/
@[simp] theorem mem_round : v ∈ round r s k ↔ v ∈ reachableWithin r s k :=
  Set.Finite.mem_toFinset _

/-- A scan transcript chooses either no walk or a list of vertices for each vertex. -/
abbrev Transcript (α : Type*) := α → Option (List α)

/-- Vertices for which the scan guessed a walk. -/
noncomputable def selected (w : Transcript α) : Finset α := by
  classical
  exact Finset.univ.filter fun v => (w v).isSome

/-- The scan selected a vertex precisely when its transcript includes a walk for it. -/
@[simp] theorem mem_selected {w : Transcript α} :
    v ∈ selected w ↔ ∃ p, w v = some p := by
  cases h : w v <;> simp [selected, h]

/-- Number of edges guessed for a vertex. A skipped vertex contributes zero. -/
@[expose] def guessedLength (w : Transcript α) (v : α) : ℕ :=
  ((w v).getD []).length - 1

/-- The two registers checked at the end of a scan. -/
structure Tally where
  /-- Number of selected vertices. -/
  count : ℕ
  /-- Sum of the lengths of the chosen walks. -/
  lengthSum : ℕ

/-- Expected count and distance sum, supplied to the scan. -/
@[expose] noncomputable def expected (r : α → α → Prop) (s : α) (k : ℕ) : Tally :=
  ⟨(round r s k).card, ∑ v ∈ round r s k, distance r s v⟩

/-- The exact tally uses at most one count and at most `k` edges per vertex. -/
theorem expected_bounds :
    (expected r s k).count ≤ Fintype.card α ∧
      (expected r s k).lengthSum ≤ Fintype.card α * k := by
  have hc : (round r s k).card ≤ Fintype.card α := Finset.card_le_univ _
  refine ⟨hc, ?_⟩
  dsimp only [expected]
  calc
    ∑ v ∈ round r s k, distance r s v ≤ ∑ _ ∈ round r s k, k :=
      sum_le_sum fun _ hv => (distance_spec (mem_round.mp hv)).2
    _ = (round r s k).card * k := by rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ ≤ _ := Nat.mul_le_mul_right k hc

/-- Terminal count and length sum of the chosen walks. -/
@[expose] noncomputable def observed (w : Transcript α) : Tally :=
  ⟨(selected w).card, ∑ v ∈ selected w, guessedLength w v⟩

/-- The final test compares the two registers with their expected values. -/
@[expose] def Tally.matches (actual expected : Tally) : Bool :=
  (actual.count == expected.count) && (actual.lengthSum == expected.lengthSum)

/-- The Boolean test checks both equalities. -/
theorem Tally.matches_iff (actual expected : Tally) :
    actual.matches expected ↔
      actual.count = expected.count ∧ actual.lengthSum = expected.lengthSum := by
  simp [Tally.matches]

/-- The scan's terminal checks, using the correct count and distance sum as inputs.
The chain condition also checks the initial and final vertices of each guess. -/
@[expose] def Passes (r : α → α → Prop) (s : α) (k : ℕ) (w : Transcript α) : Prop :=
  (∀ v p, w v = some p → p.IsChainFromTo r s v ∧ guessedLength w v ≤ k) ∧
  (observed w).matches (expected r s k)

omit [Fintype α] in
private theorem guessedLength_spec {w : Transcript α} {p : List α}
    (hw : w v = some p) (hp : p.IsChainFromTo r s v) :
    p.length = guessedLength w v + 1 := by
  have hpos := hp.length_pos
  simp only [guessedLength, hw, Option.getD_some]
  omega

/-- Exactly the successful transcripts choose a shortest walk at every vertex of the round
and skip every other vertex. This also determines the Boolean answer for any queried vertex. -/
theorem passes_iff {w : Transcript α} :
    Passes r s k w ↔
      (∀ v ∈ round r s k, ∃ p, w v = some p ∧ p.IsChainFromTo r s v ∧
        p.length = distance r s v + 1) ∧
      (∀ v ∉ round r s k, w v = none) := by
  classical
  rw [Passes, Tally.matches_iff]
  change (_ ∧ (selected w).card = (round r s k).card ∧
    (∑ v ∈ selected w, guessedLength w v) = ∑ v ∈ round r s k, distance r s v) ↔ _
  constructor
  · rintro ⟨hwalk, hcount, hsum⟩
    have hsteps (v : α) (p : List α) (hp : w v = some p) :
        RelatesInSteps r s v (guessedLength w v) :=
      (hwalk v p hp).1.relatesInSteps (guessedLength_spec hp (hwalk v p hp).1)
    have hselected : selected w = round r s k :=
      Finset.eq_of_subset_of_card_le
        (fun v hv => let ⟨p, hp⟩ := mem_selected.mp hv
          mem_round.mpr ⟨_, (hwalk v p hp).2, hsteps v p hp⟩) hcount.ge
    have hle (v : α) (hv : v ∈ selected w) : distance r s v ≤ guessedLength w v := by
      obtain ⟨p, hp⟩ := mem_selected.mp hv
      exact distance_le (hsteps v p hp)
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hmem : v ∈ selected w := hselected ▸ hv
      obtain ⟨p, hp⟩ := mem_selected.mp hmem
      have heq : guessedLength w v = distance r s v := by
        apply (hle v hmem).antisymm'
        by_contra! hlt
        rw [← hselected] at hsum
        exact not_lt_of_ge hsum.le (Finset.sum_lt_sum hle ⟨v, hmem, hlt⟩)
      exact ⟨p, hp, (hwalk v p hp).1, heq ▸ guessedLength_spec hp (hwalk v p hp).1⟩
    · cases hw : w v with
      | none => rfl
      | some p => exact (hv (hselected ▸ mem_selected.mpr ⟨p, hw⟩)).elim
  · rintro ⟨hin, hout⟩
    have hselected : selected w = round r s k := by
      ext v
      rw [mem_selected]
      by_cases hv : v ∈ round r s k
      · obtain ⟨p, hp, _, _⟩ := hin v hv
        simp [hv, hp]
      · simp [hv, hout v hv]
    have hspec (v : α) (p : List α) (hp : w v = some p) :
        p.IsChainFromTo r s v ∧ guessedLength w v = distance r s v := by
      obtain ⟨q, hq, hchain, hlen⟩ := hin v (hselected ▸ mem_selected.mpr ⟨p, hp⟩)
      obtain rfl := Option.some.inj (hp.symm.trans hq)
      exact ⟨hchain, Nat.add_right_cancel ((guessedLength_spec hp hchain).symm.trans hlen)⟩
    refine ⟨fun v p hp => ?_, by rw [hselected], ?_⟩
    · obtain ⟨hc, hl⟩ := hspec v p hp
      exact ⟨hc, hl.symm ▸ (distance_spec (mem_round.mp (hselected ▸ mem_selected.mpr ⟨p, hp⟩))).2⟩
    · refine Finset.sum_congr hselected fun v hv => ?_
      obtain ⟨p, hp, _, _⟩ := hin v hv
      exact (hspec v p hp).2

/-- A successful scan returns true exactly for vertices in the breadth-first round. -/
theorem isSome_iff {w : Transcript α} (hw : Passes r s k w) :
    (w v).isSome ↔ v ∈ reachableWithin r s k := by
  obtain ⟨hin, hout⟩ := passes_iff.mp hw
  rw [← mem_round]
  constructor
  · intro h
    by_contra hnot
    simp [hout v hnot] at h
  · intro hv
    obtain ⟨p, hp, _, _⟩ := hin v hv
    simp [hp]

/-- The correct count and sum always admit a successful scan, even when shortest walks tie. -/
theorem exists_passes : ∃ w, Passes r s k w := by
  classical
  have hex (v : α) (hv : v ∈ round r s k) :
      ∃ p : List α, p.IsChainFromTo r s v ∧ p.length = distance r s v + 1 :=
    (distance_spec (mem_round.mp hv)).1.exists_isChainFromTo
  let w : Transcript α := fun v => if hv : v ∈ round r s k then some (hex v hv).choose else none
  refine ⟨w, passes_iff.mpr ⟨fun v hv => ?_, fun v hv => dite_eq_right hv⟩⟩
  exact ⟨(hex v hv).choose, dite_eq_left hv, (hex v hv).choose_spec.1, (hex v hv).choose_spec.2⟩

/-- With exact counts, Figure 1 has exactly one successful transcript if and only if
each round vertex has exactly one shortest walk from the source. -/
theorem existsUnique_passes_iff :
    (∃! w, Passes r s k w) ↔
      ∀ v ∈ round r s k, ∃! p : List α,
        p.IsChainFromTo r s v ∧ p.length = distance r s v + 1 := by
  classical
  constructor
  · rintro ⟨w, hw, huniq⟩ v hv
    obtain ⟨hin, hout⟩ := passes_iff.mp hw
    obtain ⟨p, hp, hchain, hlen⟩ := hin v hv
    refine ⟨p, ⟨hchain, hlen⟩, fun q hq => ?_⟩
    let w' := Function.update w v (some q)
    have hw' : Passes r s k w' := by
      refine passes_iff.mpr ⟨fun u hu => ?_, fun u hu => ?_⟩
      · rcases eq_or_ne u v with rfl | heq
        · exact ⟨q, Function.update_self _ _ _, hq.1, hq.2⟩
        · simpa only [w', Function.update_of_ne heq] using hin u hu
      · simpa only [w', Function.update_of_ne (fun heq : u = v => hu (heq.symm ▸ hv))] using
          hout u hu
    exact Option.some.inj (by simpa [w', hp] using congrFun (huniq w' hw') v)
  · intro h
    obtain ⟨w, hw⟩ := exists_passes (r := r) (s := s) (k := k)
    obtain ⟨hin, hout⟩ := passes_iff.mp hw
    refine ⟨w, hw, fun w' hw' => funext fun v => ?_⟩
    obtain ⟨hin', hout'⟩ := passes_iff.mp hw'
    by_cases hv : v ∈ round r s k
    · obtain ⟨p, hp, hpchain, hplen⟩ := hin v hv
      obtain ⟨q, hq, hqchain, hqlen⟩ := hin' v hv
      obtain ⟨_, _, huniq⟩ := h v hv
      rw [hq, hp, huniq q ⟨hqchain, hqlen⟩, huniq p ⟨hpchain, hplen⟩]
    · rw [hout' v hv, hout v hv]

/-- At radius zero, only the source is reachable. -/
theorem round_zero {α : Type*} [Fintype α] (r : α → α → Prop) (s : α) :
    round r s 0 = {s} := by
  classical
  ext v
  simp only [mem_round, reachableWithin_zero, Set.mem_singleton_iff, mem_singleton]

/-- The initial tally counts the source, at distance zero. -/
theorem expected_zero {α : Type*} [Fintype α] (r : α → α → Prop) (s : α) :
    expected r s 0 = ⟨1, 0⟩ := by
  have hmem : s ∈ round r s 0 := by simp [round_zero]
  have hd := (distance_spec (mem_round.mp hmem)).2
  simp [expected, round_zero, Nat.eq_zero_of_le_zero hd]

/-- The only successful radius-zero transcript selects the singleton walk at the source. -/
theorem existsUnique_passes_zero {α : Type*} [Fintype α] (r : α → α → Prop) (s : α) :
    ∃! w, Passes r s 0 w := by
  classical
  rw [existsUnique_passes_iff, round_zero]
  intro v hv
  obtain rfl := mem_singleton.mp hv
  have hd := Nat.eq_zero_of_le_zero
    (distance_spec (mem_round.mp (by simp [round_zero] : v ∈ round r v 0))).2
  refine ⟨[v], ⟨List.isChainFromTo_singleton, by simp [hd]⟩, fun p hp => ?_⟩
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (by simpa [hd] using hp.2)
  simpa using hp.1.getLast_eq

private theorem chainMap {γ δ : Type*} {R : γ → γ → Prop} {S : δ → δ → Prop}
    (f : γ → δ) (hf : ∀ u v, R u v → S (f u) (f v)) {u v : γ} {xs : List γ}
    (h : xs.IsChainFromTo R u v) : (xs.map f).IsChainFromTo S (f u) (f v) := by
  induction h using List.IsChainFromTo.head_induction_on with
  | h_refl => exact List.isChainFromTo_singleton
  | h_head hab _ ih => exact ih.cons (hf _ _ hab)

/-- Relabeling the graph preserves the existence of a unique passing transcript.
In particular, a finite carrier can be indexed by consecutive vertex IDs. -/
theorem existsUnique_passes_reindex {α β : Type*} [Fintype α] [Fintype β] (index : α ≃ β)
    (r : α → α → Prop) (s : α) (k : ℕ) :
    (∃! t, Passes r s k t) ↔
      ∃! t, Passes (fun u v => r (index.symm u) (index.symm v)) (index s) k t := by
  let r' (u v : β) := r (index.symm u) (index.symm v)
  have toIndex (u v : α) (h : r u v) : r' (index u) (index v) := by simpa [r'] using h
  have fromIndex (u v : β) : r' u v → r (index.symm u) (index.symm v) := id
  have steps (v : α) (d : ℕ) :
      RelatesInSteps r s v d ↔ RelatesInSteps r' (index s) (index v) d := by
    refine ⟨RelatesInSteps.map index toIndex, fun h => ?_⟩
    simpa only [Equiv.symm_apply_apply] using h.map index.symm fromIndex
  have memRound (v : α) : v ∈ round r s k ↔ index v ∈ round r' (index s) k := by
    simp only [mem_round]
    exact exists_congr fun d => and_congr_right fun _ => steps v d
  have dist (v : α) (hv : v ∈ round r s k) :
      distance r s v = distance r' (index s) (index v) := by
    have ha := (distance_spec (mem_round.mp hv)).1
    have hb := (distance_spec (mem_round.mp ((memRound v).mp hv))).1
    exact le_antisymm (distance_le ((steps v _).mpr hb)) (distance_le ((steps v _).mp ha))
  have shortest (v : α) (hv : v ∈ round r s k) :
      (∃! p : List α, p.IsChainFromTo r s v ∧ p.length = distance r s v + 1) ↔
        ∃! p : List β, p.IsChainFromTo r' (index s) (index v) ∧
          p.length = distance r' (index s) (index v) + 1 := by
    apply index.listEquivOfEquiv.existsUnique_congr
    intro xs
    change (_ ∧ _) ↔ (xs.map index).IsChainFromTo r' (index s) (index v) ∧
      (xs.map index).length = distance r' (index s) (index v) + 1
    rw [List.length_map, ← dist v hv]
    refine and_congr_left fun _ => ⟨chainMap index toIndex, fun h => ?_⟩
    simpa [List.map_map, Function.comp_def] using chainMap index.symm fromIndex h
  rw [existsUnique_passes_iff, existsUnique_passes_iff]
  change (∀ v ∈ round r s k, _) ↔ ∀ v ∈ round r' (index s) k, _
  constructor
  · intro h v hv
    have hm := (memRound (index.symm v)).mpr (by simpa using hv)
    simpa using (shortest (index.symm v) hm).mp (h _ hm)
  · intro h v hv
    exact (shortest v hv).mpr (h _ ((memRound v).mp hv))

end Cslib.DoubleCounting
