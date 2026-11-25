/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Nodup

/-!
# Adjacent deduplication with full multiplicities

The output is a list of key/count pairs with positive counts and strictly increasing keys.
Expanding those runs recovers the sorted input exactly. This specifies the whole finite set and
all multiplicities, rather than a one-way membership condition. These proofs are original.

## Main definitions

* `expand`: expand key/count pairs into their repeated keys.
* `RunEncoding`: positive, strictly ordered runs reconstructing the input.

## Main results

* `RunEncoding.keys_nodup`: each key occurs once.
* `RunEncoding.mem_iff`: the keys enumerate exactly the input set.
* `RunEncoding.multiplicity`: each count is the full input multiplicity.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Deduplicate

/-- Expand a list of key/count pairs into repeated keys. -/
def expand (rs : List (ℕ × ℕ)) : List ℕ := rs.flatMap (fun p => List.replicate p.2 p.1)

/-- Runs with positive counts and strictly increasing keys reconstruct exactly `xs`. -/
structure RunEncoding (xs : List ℕ) (rs : List (ℕ × ℕ)) : Prop where
  /-- Each emitted run is nonempty. -/
  positive : ∀ p ∈ rs, 0 < p.2
  /-- A key never reappears after a different key. -/
  ordered : rs.Pairwise (fun p q => p.1 < q.1)
  /-- All input positions are accounted for, with their exact order and multiplicity. -/
  reconstruct : expand rs = xs

/-- Expansion distributes over concatenation. -/
theorem expand_append (rs ss : List (ℕ × ℕ)) : expand (rs ++ ss) = expand rs ++ expand ss := by
  simp [expand]

/-- Expansion of one run. -/
theorem expand_singleton (k c : ℕ) : expand [(k, c)] = List.replicate c k := by
  simp [expand]

/-- Every key in an expansion occurs in some nonempty run. -/
theorem mem_expand {rs : List (ℕ × ℕ)} {k : ℕ} :
    k ∈ expand rs ↔ ∃ p ∈ rs, p.1 = k ∧ 0 < p.2 := by
  simp only [expand, List.mem_flatMap, List.mem_replicate]
  exact ⟨fun ⟨p, hp, hc, hk⟩ => ⟨p, hp, hk.symm, by omega⟩,
    fun ⟨p, hp, hk, hc⟩ => ⟨p, hp, by omega, hk.symm⟩⟩

/-- Positive runs contain at least one element each. -/
theorem length_le_expand {rs : List (ℕ × ℕ)} (hp : ∀ p ∈ rs, 0 < p.2) :
    rs.length ≤ (expand rs).length := by
  induction rs with
  | nil => simp [expand]
  | cons p rs ih =>
    have hc := hp p (by simp)
    have ht := ih fun q hq => hp q (by simp [hq])
    simp only [expand, List.flatMap_cons, List.length_append, List.length_replicate,
      List.length_cons] at *
    omega

private theorem count_expand {rs : List (ℕ × ℕ)}
    (ho : rs.Pairwise (fun p q => p.1 < q.1)) {p : ℕ × ℕ} (hp : p ∈ rs) :
    (expand rs).count p.1 = p.2 := by
  induction rs with
  | nil => simp at hp
  | cons q rs ih =>
    obtain ⟨hq, ht⟩ := List.pairwise_cons.mp ho
    rcases List.mem_cons.mp hp with rfl | hp
    · have hnot : p.1 ∉ expand rs := fun hk => by
        obtain ⟨r, hr, hpr, _⟩ := mem_expand.mp hk
        exact (hq r hr).ne hpr.symm
      change (List.replicate p.2 p.1 ++ expand rs).count p.1 = p.2
      rw [List.count_append, List.count_replicate_self, List.count_eq_zero_of_not_mem hnot,
        Nat.add_zero]
    · simp only [expand, List.flatMap_cons, List.count_append]
      have hrep : (List.replicate q.2 q.1).count p.1 = 0 := by
        simp [List.count_replicate, (hq p hp).ne]
      rw [hrep]
      simpa only [Nat.zero_add, expand] using ih ht hp

/-- The key array contains no repeated key. -/
theorem RunEncoding.keys_nodup {xs : List ℕ} {rs : List (ℕ × ℕ)}
    (h : RunEncoding xs rs) : (rs.map Prod.fst).Nodup :=
  List.nodup_iff_pairwise_ne.mpr (List.pairwise_map.mpr (h.ordered.imp Nat.ne_of_lt))

/-- The key array enumerates precisely the input set. -/
theorem RunEncoding.mem_iff {xs : List ℕ} {rs : List (ℕ × ℕ)}
    (h : RunEncoding xs rs) (k : ℕ) : k ∈ rs.map Prod.fst ↔ k ∈ xs := by
  rw [← h.reconstruct, mem_expand, List.mem_map]
  exact ⟨fun ⟨p, hp, hk⟩ => ⟨p, hp, hk, h.positive p hp⟩, fun ⟨p, hp, hk, _⟩ => ⟨p, hp, hk⟩⟩

/-- Each emitted count equals the full multiplicity in the input list. -/
theorem RunEncoding.multiplicity {xs : List ℕ} {rs : List (ℕ × ℕ)}
    (h : RunEncoding xs rs) {p : ℕ × ℕ} (hp : p ∈ rs) : xs.count p.1 = p.2 :=
  h.reconstruct ▸ count_expand h.ordered hp

/-- A nonempty sorted list starts with a positive run of its head, followed only by larger
keys. This is a mathematical decomposition used to verify the adjacent scan, not an oracle
operation of the program. -/
theorem first_run (k : ℕ) (xs : List ℕ) (hs : (k :: xs).Pairwise (· ≤ ·)) :
    ∃ c rest, 0 < c ∧ k :: xs = List.replicate c k ++ rest ∧ ∀ v ∈ rest, k < v := by
  induction xs generalizing k with
  | nil => exact ⟨1, [], by decide, rfl, by simp⟩
  | cons j xs ih =>
    obtain ⟨hk, ht⟩ := List.pairwise_cons.mp hs
    rcases eq_or_ne k j with rfl | heq
    · obtain ⟨c, rest, hc, he, hr⟩ := ih k ht
      exact ⟨c + 1, rest, by omega,
        by simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons k) he, hr⟩
    · have hkj : k < j := lt_of_le_of_ne (hk j (by simp)) heq
      refine ⟨1, j :: xs, by decide, rfl, fun v hv => ?_⟩
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hkj
      · exact hkj.trans_le ((List.pairwise_cons.mp ht).1 v hv)

end Cslib.Algorithms.WordRAM.Deduplicate
