/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.ChildEndpointWitness
public import CslibFrontier.Computability.PolyTime.SeededPacketPlacement
import Mathlib.Data.List.GetD

/-!
# Iterating endpoint witnesses with actual packet numbering

A split is given the vertex label codes and its coordinate. Each parent edge's packet number is
computed from the two endpoint codes and a count of earlier edges with the same two codes.
The summands query endpoints of the parent through its witness relation. This gives the actual
packet numbering and native edge list at each level without assuming a table of packet numbers
as part of the query.
-/

public section

namespace Cslib.Circuits.Frontier.NativeChild.EndpointQuery

open PacketPacking ChildNumbering

/-- Parameters of one split, with a common radix-64 label code at every parent vertex. -/
structure Labels where
  vertices : ℕ
  coordinates : ℕ
  coordinate : Fin coordinates
  group : ℕ
  code : ℕ → Fin (2 ^ (6 * coordinates))

/-- A single represented seed supplies the vertex codes at a split. Out-of-range vertex
keys have code zero. -/
@[expose] noncomputable def Labels.ofSeed (U a : ℕ)
    (seed : BalancedSchedules.SeededLabels.Seed U (6 * a)) (i : Fin a) (g : ℕ) : Labels where
  vertices := U
  coordinates := a
  coordinate := i
  group := g
  code v := if h : v < U then BalancedSchedules.SeededLabels.label U (6 * a) seed ⟨v, h⟩ else 0

/-- The group of a vertex in the split coordinate. -/
@[expose] def Labels.symbol (l : Labels) (v : ℕ) : ℕ :=
  ((Seeded.wordEquiv l.coordinates (l.code v)) l.coordinate).val

/-- Native group table used only to state the edge-list semantics. -/
@[expose] def Labels.groups (l : Labels) : List ℕ := (List.range l.vertices).map l.symbol

/-- Native packing on the ordered parent edges, using the very same vertex codes. -/
@[expose] noncomputable def Labels.packing (l : Labels) (es : List (ℕ × ℕ)) :=
  let row := fun i : Fin es.length => (es.getD i.val (0, 0)).1
  let col := fun i : Fin es.length => (es.getD i.val (0, 0)).2
  let label := fun v => Seeded.wordEquiv l.coordinates (l.code v)
  Packing.ofLabels row col label label

/-- The genuine child edge table of a split of this parent. -/
@[expose] noncomputable def Labels.edges (l : Labels) (es : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  childEdgeList l.groups l.group es (List.ofFn fun i => ((l.packing es).packet i).val)

/-- Every child endpoint fits the exact vertex universe: retained vertices followed by all
packet vertices. In particular this is the universe used by the seed of a subsequent split. -/
theorem Labels.edges_keys (l : Labels) (es : List (ℕ × ℕ)) :
    ∀ p ∈ l.edges es,
      p.1 < l.groups.count l.group + (l.packing es).numPackets ∧
        p.2 < l.groups.count l.group + (l.packing es).numPackets := by
  have half (sel : ℕ × ℕ → ℕ) :
      ∀ p ∈ ((es.zip (List.ofFn fun i => ((l.packing es).packet i).val)).filter
          (fun q => l.groups.getD (sel q.1) 0 = l.group)).map
          (fun q => ((l.groups.take (sel q.1)).count l.group,
            l.groups.count l.group + q.2)),
        p.1 < l.groups.count l.group + (l.packing es).numPackets ∧
          p.2 < l.groups.count l.group + (l.packing es).numPackets := by
    intro p hp
    simp only [List.mem_map, List.mem_filter] at hp
    obtain ⟨⟨ends, packet⟩, ⟨hz, _⟩, rfl⟩ := hp
    obtain ⟨e, he⟩ := List.mem_ofFn.mp (List.of_mem_zip hz).2
    have hpacket : packet < (l.packing es).numPackets := by
      rw [← he]
      exact Fin.isLt _
    have hcount := (List.take_sublist (sel ends) l.groups).count_le l.group
    constructor <;> dsimp only <;> omega
  intro p hp
  simp only [Labels.edges, childEdgeList, List.mem_append] at hp
  exact hp.elim (half Prod.fst p) (half Prod.snd p)

/-- Rank of the proposed pair of labels among the preceding edge numbers. Each summand
refers only to the parent endpoint verifier on its candidate. -/
@[expose] noncomputable def classCount (q : EndpointQuery) (l : Labels) (e : ℕ)
    (p : ℕ × ℕ) : ℕ := by
  classical
  exact ∑ i ∈ Finset.range q.size, (decide (i < e ∧ ∃ x, q.accepts i x ∧
    l.code x.1 = l.code p.1 ∧ l.code x.2 = l.code p.2)).toNat

private theorem classCount_eq {q : EndpointQuery} {es} (hq : q.Represents es) (l : Labels)
    (e : Fin es.length) :
    q.classCount l e.val (es.getD e.val (0, 0)) =
      classIndex (fun i : Fin es.length => (es.getD i.val (0, 0)).1)
        (fun i : Fin es.length => (es.getD i.val (0, 0)).2)
        (fun v => Seeded.wordEquiv l.coordinates (l.code v))
        (fun v => Seeded.wordEquiv l.coordinates (l.code v)) e := by
  classical
  rw [classCount, hq.1, ← Fin.sum_univ_eq_sum_range, classIndex, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hq.2, i.isLt, true_and, exists_eq_left', pairLabel, Prod.mk.injEq,
    Equiv.apply_eq_iff_eq, Fin.lt_def]
  split_ifs with h
  · rw [decide_eq_true h]
    rfl
  · rw [decide_eq_false h]
    rfl

/-- Split relation using the binary packet computation and the recursively verified class rank. -/
@[expose] noncomputable def Labels.split (l : Labels) (q : EndpointQuery) : Split where
  vertices := l.vertices
  group := l.group
  label v := if v < l.vertices then l.symbol v else 0
  packet e p u := (SeededPacketLocation.run ⟨l.coordinates, (l.code p.1).val, (l.code p.2).val,
    q.classCount l e p⟩).1 = u

/-- On genuine vertex keys, the packet test uses exactly the polynomial-time native arithmetic
of the supplied seed, with the common class rank of this pair of endpoints. -/
theorem packet_ofSeed {U a : ℕ} (seed : BalancedSchedules.SeededLabels.Seed U (6 * a))
    (i : Fin a) (g : ℕ) (q : EndpointQuery) (e packet : ℕ) (r c : Fin U) :
    let l := Labels.ofSeed U a seed i g
    (l.split q).packet e (r.val, c.val) packet ↔
      (SeededPacketPlacement.run
        ⟨⟨U, a, seed 0, seed 1, seed 2, seed 3, 0, 0⟩, r.val, c.val,
          q.classCount l e (r.val, c.val)⟩).1 = packet := by
  simp only [SeededPacketPlacement.run, SeededPacketPlacement.code_eq, Labels.split,
    Labels.ofSeed, r.isLt, c.isLt, dite_true]

/-- One recursive call gives the correct endpoints of the actual packed child. -/
theorem Represents.seededChild {q : EndpointQuery} {es} (hq : q.Represents es) (l : Labels) :
    (q.child (l.split q)).Represents (l.edges es) := by
  apply hq.child
  refine ⟨by simp [Labels.split, Labels.groups], ?_, by simp, ?_⟩
  · intro v
    by_cases hv : v < l.vertices
    · rw [List.getD_eq_getElem _ _ (by simpa [Labels.groups] using hv)]
      simp [Labels.groups, Labels.split, hv]
    · rw [List.getD_eq_default _ _ (by simpa [Labels.groups] using Nat.le_of_not_gt hv)]
      simp [Labels.split, hv]
  · intro e he packet
    let i : Fin es.length := ⟨e, he⟩
    let row := fun j : Fin es.length => (es.getD j.val (0, 0)).1
    let col := fun j : Fin es.length => (es.getD j.val (0, 0)).2
    have h := congrArg Prod.fst (SeededPacketLocation.run_of_codes l.coordinates row col
      l.code l.code i)
    change (SeededPacketLocation.run ⟨_, _, _, _⟩).1 = packet ↔ _
    rw [show q.classCount l e (es.getD e (0, 0)) = _ from classCount_eq hq l i, h]
    simp [Labels.packing, row, col, i, he]

/-- Recursion through an arbitrary list of split coordinates preserves acceptance for every
index, including indices outside the last descendant's edge list. -/
theorem Represents.descend {q : EndpointQuery} {es} (hq : q.Represents es) (levels : List Labels) :
    (levels.foldl (fun parent l => parent.child (l.split parent)) q).Represents
      (levels.foldl (fun parent l => l.edges parent) es) := by
  induction levels generalizing q es with
  | nil => exact hq
  | cons l ls ih => exact ih (hq.seededChild l)

end Cslib.Circuits.Frontier.NativeChild.EndpointQuery
