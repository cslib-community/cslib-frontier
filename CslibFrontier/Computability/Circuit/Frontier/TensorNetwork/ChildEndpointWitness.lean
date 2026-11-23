/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.ParentEdgeWitness
import Mathlib.Data.List.GetD

/-!
# Recursive endpoint witnesses for native children

The row and column halves of the child edge list both preserve parent edge order. Each child
endpoint claim therefore reduces to one proposed parent edge with its endpoints, the rank of
the selected port, and the packet number of that same edge. Prefix counts use the parent
endpoint relation on each queried index, so the same witness applies again at the next level.
-/

public section

namespace Cslib.Circuits.Frontier.NativeChild

open ChildNumbering

variable (groups : List ℕ) (g : ℕ) (ends : List (ℕ × ℕ)) (packets : List ℕ)

/-- Endpoints attached to the retained side of an edge and its packet. -/
private def attached (sel : ℕ × ℕ → ℕ) (e : ℕ) : ℕ × ℕ :=
  ((groups.take (sel (ends.getD e (0, 0)))).count g, groups.count g + packets.getD e 0)

/-- The child list, written as two maps over the corresponding parent edge numbers. -/
private theorem childEdgeList_eq_map_ports (hp : ends.length ≤ packets.length) :
    childEdgeList groups g ends packets =
      (portEdges groups g ends Prod.fst).map (attached groups g ends packets Prod.fst) ++
      (portEdges groups g ends Prod.snd).map (attached groups g ends packets Prod.snd) := by
  have hz : ends.zip packets = (List.range ends.length).map
      (fun e => (ends.getD e (0, 0), packets.getD e 0)) := by
    apply List.ext_getElem (by simp [Nat.min_eq_left hp])
    intro i h₁ h₂
    have hi : i < ends.length := by simpa using h₂
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ (hi.trans_le hp)]
  simp only [childEdgeList, hz, List.filter_map, List.map_map, portEdges, Function.comp_def]
  rfl

/-- The bound on a child index in the parent witness is its actual edge count. -/
theorem length_childEdgeList_eq_ports (hp : ends.length ≤ packets.length) :
    (childEdgeList groups g ends packets).length =
      (portEdges groups g ends Prod.fst).length + (portEdges groups g ends Prod.snd).length := by
  simp [childEdgeList_eq_map_ports groups g ends packets hp]

/-- On every genuine child edge, reading its endpoints needs only its parent edge, the
rank of the retained endpoint among its group and the packet number of that parent edge. -/
theorem get_childEdgeList (hp : ends.length ≤ packets.length) (j : ℕ)
    (hj : j < (childEdgeList groups g ends packets).length) :
    let e := parentEdge groups g ends j
    let p := ends.getD e (0, 0)
    let v := if j < (portEdges groups g ends Prod.fst).length then p.1 else p.2
    (childEdgeList groups g ends packets)[j] =
      ((groups.take v).count g, groups.count g + packets.getD e 0) := by
  dsimp only
  rw [length_childEdgeList_eq_ports groups g ends packets hp] at hj
  have h := childEdgeList_eq_map_ports groups g ends packets hp
  by_cases hrow : j < (portEdges groups g ends Prod.fst).length
  · simp [h, hrow, parentEdge, List.getElem_append_left, attached]
  · have hcol : j - (portEdges groups g ends Prod.fst).length <
        (portEdges groups g ends Prod.snd).length := by omega
    simp only [h, parentEdge, ite_eq_right hrow, List.getD_eq_getElem _ _ hcol]
    rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hrow)]
    simp [attached]


/-- A membership test for an endpoint pair, with the exact number of available edges. -/
structure EndpointQuery where
  size : ℕ
  accepts : ℕ → ℕ × ℕ → Prop

namespace EndpointQuery

/-- Invalid indices have no accepted endpoint pair, including when the default pair is genuine. -/
@[expose] def Represents (q : EndpointQuery) (es : List (ℕ × ℕ)) : Prop :=
  q.size = es.length ∧ ∀ e p, q.accepts e p ↔ e < es.length ∧ es.getD e (0, 0) = p

/-- The fields required at one split. Labels and packet membership can themselves be verified
on a succinct representation. The rank of a vertex is counted only up to the vertex universe. -/
structure Split where
  vertices : ℕ
  group : ℕ
  label : ℕ → ℕ
  packet : ℕ → ℕ × ℕ → ℕ → Prop

/-- Prefix size of the retained vertex group. The full prefix gives the packet offset. -/
@[expose] def Split.vertexRank (s : Split) (v : ℕ) : ℕ :=
  (List.range (min v s.vertices)).countP fun u => decide (s.label u = s.group)

/-- Count prefix edges whose selected endpoint belongs to the chosen group. -/
@[expose] noncomputable def portCount (q : EndpointQuery) (s : Split) (sel : ℕ × ℕ → ℕ)
    (bound : ℕ) : ℕ := by
  classical
  exact (List.range bound).countP fun e => decide (∃ p, q.accepts e p ∧ s.label (sel p) = s.group)

/-- An endpoint witness guesses one parent edge, both its endpoints, and one packet. The
order test selects a predecessor count on the row or column side. -/
@[expose] noncomputable def child (q : EndpointQuery) (s : Split) : EndpointQuery where
  size := q.portCount s Prod.fst q.size + q.portCount s Prod.snd q.size
  accepts j answer := ∃ e p packet, q.accepts e p ∧ s.packet e p packet ∧
    ((s.label p.1 = s.group ∧ q.portCount s Prod.fst e = j) ∨
      (s.label p.2 = s.group ∧ q.portCount s Prod.fst q.size + q.portCount s Prod.snd e = j)) ∧
    answer = (s.vertexRank (if j < q.portCount s Prod.fst q.size then p.1 else p.2),
      s.vertexRank s.vertices + packet)

/-- A split's label and packet operations agree with the numbered native packing. The packet
test is needed only at a real parent edge and its actual endpoints. -/
@[expose] def Split.Represents (s : Split) (labels : List ℕ) (es : List (ℕ × ℕ))
    (ps : List ℕ) : Prop :=
  s.vertices = labels.length ∧ (∀ v, s.label v = labels.getD v 0) ∧ es.length ≤ ps.length ∧
    ∀ e, e < es.length → ∀ packet, s.packet e (es.getD e (0, 0)) packet ↔ ps.getD e 0 = packet

/-- Counting a split's genuine parent keys agrees with counting the matching labels in the
same prefix of its group table. No agreement outside the vertex universe is required. -/
theorem Split.vertexRank_eq {s : Split} {gs : List ℕ} (hsize : s.vertices = gs.length)
    (hlabels : ∀ v, v < s.vertices → s.label v = gs.getD v 0) (v : ℕ) :
    s.vertexRank v = (gs.take v).count s.group := by
  have h : (List.range (min v s.vertices)).map s.label = gs.take v := by
    apply List.ext_getElem (by simp [hsize])
    intro i h₁ h₂
    have hi : i < gs.length := by simp [hsize] at h₁; omega
    simp only [List.getElem_map, List.getElem_range,
      hlabels i (by simpa only [hsize] using hi), List.getD_eq_getElem _ _ hi, List.getElem_take]
  rw [← h, List.count, List.countP_map, Split.vertexRank]
  rfl

private theorem prefix_eq {q : EndpointQuery} {s : Split} {gs es ps}
    (hq : q.Represents es) (hs : s.Represents gs es ps) (sel : ℕ × ℕ → ℕ)
    {bound : ℕ} (hb : bound ≤ es.length) :
    q.portCount s sel bound = portRank gs s.group es sel bound := by
  classical
  unfold portCount portRank
  apply List.countP_congr
  intro e hem
  have he := (List.mem_range.mp hem).trans_le hb
  simp only [hq.2, he, true_and, exists_eq_left', hs.2.1]

/-- The same endpoint relation is sound and complete after one split. It uses the actual
native child's edge ordering, including both row and column ports of the same parent edge. -/
theorem Represents.child {q : EndpointQuery} {s : Split} {gs es ps} (hq : q.Represents es)
    (hs : s.Represents gs es ps) :
    (q.child s).Represents (childEdgeList gs s.group es ps) := by
  have hfull (sel : ℕ × ℕ → ℕ) :
      q.portCount s sel q.size = (portEdges gs s.group es sel).length := by
    rw [hq.1, prefix_eq hq hs sel le_rfl, length_portEdges_eq_portRank]
  have hn := length_childEdgeList_eq_ports gs s.group es ps hs.2.2.1
  refine ⟨by simp only [EndpointQuery.child, hfull, hn], ?_⟩
  intro j answer
  constructor
  · rintro ⟨e, p, packet, hread, hpacket, hbranch, rfl⟩
    obtain ⟨he, rfl⟩ := (hq.2 e p).mp hread
    obtain rfl := (hs.2.2.2 e he packet).mp hpacket
    rw [prefix_eq hq hs _ he.le, prefix_eq hq hs _ he.le, hfull, hs.2.1, hs.2.1] at hbranch
    obtain ⟨hj, hpar⟩ := (parentEdge_witness_iff gs s.group es j e).mpr ⟨he, hbranch⟩
    have hvalid := hn ▸ hj
    refine ⟨hvalid, ?_⟩
    rw [List.getD_eq_getElem _ _ hvalid, get_childEdgeList _ _ _ _ hs.2.2.1 j hvalid]
    simp only [hpar, hfull, Split.vertexRank_eq hs.1 (fun v _ => hs.2.1 v), hs.1,
      List.take_length]
  · rintro ⟨hj, rfl⟩
    let e := parentEdge gs s.group es j
    obtain ⟨he, hbranch⟩ :=
      (parentEdge_witness_iff gs s.group es j e).mp ⟨hn ▸ hj, rfl⟩
    refine ⟨e, es.getD e (0, 0), ps.getD e 0, (hq.2 _ _).mpr ⟨he, rfl⟩,
      (hs.2.2.2 e he _).mpr rfl, ?_, ?_⟩
    · rwa [prefix_eq hq hs _ he.le, prefix_eq hq hs _ he.le, hfull, hs.2.1, hs.2.1]
    · rw [List.getD_eq_getElem _ _ hj, get_childEdgeList _ _ _ _ hs.2.2.1 j hj]
      simp only [e, hfull, Split.vertexRank_eq hs.1 (fun v _ => hs.2.1 v), hs.1,
        List.take_length]

end EndpointQuery

end Cslib.Circuits.Frontier.NativeChild
