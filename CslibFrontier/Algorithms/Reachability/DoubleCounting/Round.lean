/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting

/-!
# Updating the double-counting round

A successful transcript answers membership in the current round. Scan successors of
that round to obtain its next frontier. Each new vertex contributes once to the
count, and its distance is the next round index. Figure 2 of [ReinhardtAllender2000]
increments once per qualifying predecessor and flags ties. Its accumulator agrees
with the set-based update here when the next-round predecessor test succeeds.
On a tied round the set-based tally still counts each newly reached vertex once.
Under uniqueness in the current round, a new vertex has a unique shortest walk
exactly when it has a unique predecessor in that round.

The checked diamond in `CslibFrontierTests.LayeredDigraph` uses `isSome_iff`
to query a vertex outside the first round, then uses the predecessor criterion
to show that uniqueness fails in the second. `Scan` provides a streaming
replay of the bounded scan, and the native `LogSpace.DoubleCounting` module
certifies the terminal comparison of binary tallies.

## Main results

* `Cslib.DoubleCounting.nextTally_eq_expected`: the scan computes the exact next tally.
* `Cslib.DoubleCounting.existsUnique_shortest_iff_predecessor`: correctness of the
  tie check at a new vertex.
-/

public section

namespace Cslib.DoubleCounting

open Finset Relation

variable {α : Type*} [Fintype α] {r : α → α → Prop} {s v : α} {k : ℕ}
  {w : Transcript α}

/-- The vertices outside the current round that have a predecessor selected in its scan. -/
noncomputable def frontier (r : α → α → Prop) (w : Transcript α) : Finset α := by
  classical
  exact univ.filter fun v => ¬(w v).isSome ∧ ∃ u, (w u).isSome ∧ r u v

/-- A valid scan identifies exactly the vertices added by the next round. -/
theorem mem_frontier_iff (hw : Passes r s k w) :
    v ∈ frontier r w ↔ v ∈ round r s (k + 1) ∧ v ∉ round r s k := by
  classical
  simp only [frontier, mem_filter, mem_univ, true_and, isSome_iff hw, mem_round,
    reachableWithin_succ, Set.mem_union, Set.mem_ofPred_eq]
  tauto

/-- A vertex first reached in the next round has distance exactly its index. -/
theorem distance_eq_succ_of_mem_frontier (hw : Passes r s k w) (hv : v ∈ frontier r w) :
    distance r s v = k + 1 := by
  obtain ⟨hnext, hold⟩ := (mem_frontier_iff hw).mp hv
  obtain ⟨hp, hle⟩ := distance_spec (mem_round.mp hnext)
  by_contra hne
  exact hold (mem_round.mpr ⟨_, by omega, hp⟩)

/-- Add one count and the new distance for each vertex in the next frontier. -/
@[expose] noncomputable def nextTally (r : α → α → Prop) (k : ℕ) (w : Transcript α)
    (t : Tally) : Tally :=
  ⟨t.count + (frontier r w).card, t.lengthSum + (frontier r w).card * (k + 1)⟩

/-- From the exact previous tally and a successful scan, the update computes the exact tally. -/
theorem nextTally_eq_expected (hw : Passes r s k w) :
    nextTally r k w (expected r s k) = expected r s (k + 1) := by
  classical
  have hdisjoint : Disjoint (round r s k) (frontier r w) :=
    disjoint_left.mpr fun _ hu hf => ((mem_frontier_iff hw).mp hf).2 hu
  have hunion : round r s (k + 1) = round r s k ∪ frontier r w := by
    ext u
    rw [mem_union, mem_frontier_iff hw]
    exact ⟨fun h => by by_cases hu : u ∈ round r s k <;> tauto,
      fun h => h.elim
        (fun hu => mem_round.mpr (reachableWithin_mono (Nat.le_succ k) (mem_round.mp hu)))
        And.left⟩
  unfold nextTally expected
  congr 1
  · rw [hunion, card_union_of_disjoint hdisjoint]
  · rw [hunion, sum_union hdisjoint]
    congr 1
    calc
      (frontier r w).card * (k + 1) = ∑ _ ∈ frontier r w, (k + 1) := by simp
      _ = _ := sum_congr rfl fun _ hv => (distance_eq_succ_of_mem_frontier hw hv).symm

private theorem predecessor_distance (hv : v ∉ round r s k) {u : α}
    (hu : u ∈ round r s k) (he : r u v) : distance r s u = k := by
  obtain ⟨hp, hle⟩ := distance_spec (mem_round.mp hu)
  by_contra hne
  have hstep : RelatesInSteps r s v (distance r s u + 1) := hp.trans (.single he)
  exact hv (mem_round.mpr ⟨_, by omega, hstep⟩)

private theorem shortest_snoc (hv : v ∉ round r s k) {u : α}
    (hu : u ∈ round r s k) (he : r u v) {p : List α}
    (hp : p.IsChainFromTo r s u ∧ p.length = distance r s u + 1) :
    (p ++ [v]).IsChainFromTo r s v ∧ (p ++ [v]).length = k + 2 := by
  refine ⟨hp.1.snoc he, ?_⟩
  rw [List.length_append, List.length_singleton, hp.2, predecessor_distance hv hu he]

private theorem exists_shortest_prefix {p : List α}
    (hp : p.IsChainFromTo r s v ∧ p.length = k + 2) (hv : v ∉ round r s k) :
    ∃ u ∈ round r s k, r u v ∧ p.dropLast.IsChainFromTo r s u ∧
      p.dropLast.length = distance r s u + 1 := by
  have hi : k < p.length := by omega
  have hlast : k + 1 < p.length := by omega
  let u := p[k]
  have hlast_eq : p[k + 1] = v := by
    have heq : p.length - 1 = k + 1 := by omega
    simpa only [heq] using hp.1.getElem_length_sub_one
  have he : r u v := hlast_eq ▸ hp.1.isChain.getElem k hlast
  have htake := hp.1.take hi
  have hlen : (p.take (k + 1)).length = k + 1 := by simp [hp.2]
  have hu : u ∈ round r s k := mem_round.mpr ⟨k, le_rfl, htake.relatesInSteps hlen⟩
  have hdrop : p.dropLast = p.take (k + 1) := by simp [List.dropLast_eq_take, hp.2]
  refine ⟨u, hu, he, hdrop.symm ▸ htake, ?_⟩
  rw [hdrop, hlen, predecessor_distance hv hu he]

/-- Assuming uniqueness in the current round, a newly reached vertex has one shortest walk
exactly when it has one predecessor in the current round. -/
theorem existsUnique_shortest_iff_predecessor (hw : Passes r s k w) (hv : v ∈ frontier r w)
    (hprev : ∃! t, Passes r s k t) :
    (∃! p : List α, p.IsChainFromTo r s v ∧ p.length = distance r s v + 1) ↔
      ∃! u, u ∈ round r s k ∧ r u v := by
  have huniq := (existsUnique_passes_iff.mp hprev)
  have hold := ((mem_frontier_iff hw).mp hv).2
  rw [distance_eq_succ_of_mem_frontier hw hv]
  change (∃! p : List α, p.IsChainFromTo r s v ∧ p.length = k + 2) ↔ _
  constructor
  · rintro ⟨p, hp, hpu⟩
    obtain ⟨u, hu, he, hchain, hlen⟩ := exists_shortest_prefix hp hold
    refine ⟨u, ⟨hu, he⟩, fun y hy => ?_⟩
    obtain ⟨q, hq, _⟩ := huniq y hy.1
    have hq' := hpu (q ++ [v]) (shortest_snoc hold hy.1 hy.2 hq)
    have hdrop : q = p.dropLast := by
      simpa using congrArg List.dropLast hq'
    cases hdrop
    exact hq.1.getLast_eq.symm.trans hchain.getLast_eq
  · rintro ⟨u, ⟨hu, he⟩, huu⟩
    obtain ⟨p, hp, hpu⟩ := huniq u hu
    refine ⟨p ++ [v], shortest_snoc hold hu he hp, fun q hq => ?_⟩
    obtain ⟨y, hy, hye, hqchain, hqlen⟩ := exists_shortest_prefix hq hold
    obtain rfl : y = u := huu y ⟨hy, hye⟩
    have hd := hpu q.dropLast ⟨hqchain, hqlen⟩
    rw [← hd, ← hq.1.getLast_eq]
    exact (List.dropLast_append_getLast hq.1.ne_nil).symm

/-- A unique current transcript extends to a unique next-round transcript exactly when all
newly reached vertices pass the predecessor check. -/
theorem existsUnique_passes_succ_iff (hw : Passes r s k w) (hprev : ∃! t, Passes r s k t) :
    (∃! t, Passes r s (k + 1) t) ↔
      ∀ v ∈ frontier r w, ∃! u, u ∈ round r s k ∧ r u v := by
  rw [existsUnique_passes_iff]
  constructor
  · intro h v hv
    exact (existsUnique_shortest_iff_predecessor hw hv hprev).mp
      (h v ((mem_frontier_iff hw).mp hv).1)
  · intro h v hv
    by_cases hcur : v ∈ round r s k
    · exact (existsUnique_passes_iff.mp hprev) v hcur
    · have hnew := (mem_frontier_iff hw).mpr ⟨hv, hcur⟩
      exact (existsUnique_shortest_iff_predecessor hw hnew hprev).mpr (h v hnew)

end Cslib.DoubleCounting
