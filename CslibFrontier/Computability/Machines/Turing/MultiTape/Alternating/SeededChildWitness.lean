/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.SeededChildWitness.Fields
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildCounts

/-!
# Local arithmetic and count obligations for a recursive child witness

The six proposed counts refer to the same parent edge, endpoints, seed and split coordinate.
Checking those counts, the parent edge, and one native short arithmetic predicate characterizes
both endpoints of the selected child edge.
-/

public section

namespace Turing.MultiTapeATM.SeededChildCounts

open Cslib BalancedSchedules MultiTapeTM Circuits.Frontier.NativeChild EndpointQuery

/-- Count values a correct proposal must supply. The vertex prefix selects the side using the
row-port total, including when the queried child edge is the first column port. -/
@[expose] noncomputable def actualCounts (q : EndpointQuery) (l : Labels) (e j : ℕ)
    (p : ℕ × ℕ) : SeededChildWitness.Counts :=
  let total := (Request.port false q.size).value q l
  let v := if j < total then p.1 else p.2
  ⟨(Request.port false e).value q l, (Request.port true e).value q l, total,
    (Request.vertex v).value q l, (Request.vertex l.vertices).value q l,
    (Request.pack e p).value q l⟩

private theorem request_value_le (r : Request) (q : EndpointQuery) (l : Labels) :
    r.value q l ≤ r.size q l := by
  rw [Request.value_eq]
  calc
    _ ≤ ∑ _j ∈ Finset.range (r.size q l), 1 := Finset.sum_le_sum fun j _ => by
      cases r.test q l j <;> decide
    _ = _ := by simp

/-- On a genuine parent edge the six counts fit the common binary width of the parent
vertex and edge universes. This controls the length of the existential witness tape. -/
theorem actualCounts_fit (q : EndpointQuery) (l : Labels) {e : ℕ} (he : e ≤ q.size)
    (j : ℕ) (p : ℕ × ℕ) :
    let c := actualCounts q l e j p
    let n := max q.size l.vertices
    ∀ z ∈ [c.rowPrefix, c.colPrefix, c.rowTotal, c.vertexPrefix, c.vertexTotal, c.classRank],
      z < 2 ^ n.size := by
  let total := (Request.port false q.size).value q l
  let v := if j < total then p.1 else p.2
  have h₁ := request_value_le (.port false e) q l
  have h₂ := request_value_le (.port true e) q l
  have h₃ := request_value_le (.port false q.size) q l
  have h₄ := request_value_le (.vertex v) q l
  have h₅ := request_value_le (.vertex l.vertices) q l
  have h₆ := request_value_le (.pack e p) q l
  change _ ≤ e at h₁ h₂
  change _ ≤ q.size at h₃ h₆
  change _ ≤ min v l.vertices at h₄
  change _ ≤ min l.vertices l.vertices at h₅
  have hsize := Nat.lt_size_self (max q.size l.vertices)
  have hq := (Nat.le_max_left q.size l.vertices).trans_lt hsize
  have hv := (Nat.le_max_right q.size l.vertices).trans_lt hsize
  change ∀ z ∈ [(Request.port false e).value q l, (Request.port true e).value q l,
    (Request.port false q.size).value q l, (Request.vertex v).value q l,
    (Request.vertex l.vertices).value q l, (Request.pack e p).value q l], _
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, forall_const, and_true]
  exact ⟨(h₁.trans he).trans_lt hq, (h₂.trans he).trans_lt hq, h₃.trans_lt hq,
    (h₄.trans (Nat.min_le_right _ _)).trans_lt hv, (h₅.trans (Nat.min_le_right _ _)).trans_lt hv,
    h₆.trans_lt hq⟩

/-- The represented four-coefficient seed computes the selected native group. -/
theorem symbol_of_seed {U a : ℕ} (seed : SeededLabels.Seed U (6 * a))
    (i : Fin a) (g e : ℕ) (v : Fin U) (q : EndpointQuery) :
    RootPortFinish.symbol ⟨U, a, seed 0, seed 1, seed 2, seed 3, e, 0⟩ i.val v.val =
      ((Labels.ofSeed U a seed i g).split q).label v.val := by
  simp only [RootPortFinish.symbol, TrinomialArithmetic.runSelected_eq, Labels.split,
    Labels.ofSeed, Labels.symbol, v.isLt, ite_true, dite_true, PacketPacking.Seeded.wordEquiv,
    SeededLabels.label]
  rfl

/-- A child endpoint query is exactly a single parent witness, six count claims, and the
native short arithmetic test. The vertex bound is required for the supplied seed's tagged keys. -/
theorem child_iff_exists_witness {U a : ℕ} (seed : SeededLabels.Seed U (6 * a))
    (i : Fin a) (g : ℕ) (q : EndpointQuery)
    (hkeys : ∀ e p, q.accepts e p → p.1 < U ∧ p.2 < U) (j : ℕ) (answer : ℕ × ℕ) :
    let l := Labels.ofSeed U a seed i g
    (q.child (l.split q)).accepts j answer ↔
      ∃ (e : ℕ) (p : ℕ × ℕ) (c : SeededChildWitness.Counts), q.accepts e p ∧
        c = actualCounts q l e j p ∧
        SeededChildWitness.run ⟨⟨U, a, seed 0, seed 1, seed 2, seed 3, e, 0⟩,
          i.val, g, j, p, answer, c⟩ = true := by
  let l := Labels.ofSeed U a seed i g
  change (∃ e p u, q.accepts e p ∧ (l.split q).packet e p u ∧ _ ∧ _) ↔ _
  constructor
  · rintro ⟨e, p, u, hp, hpack, hport, hans⟩
    obtain ⟨hr, hc⟩ := hkeys e p hp
    have hu : (SeededPacketPlacement.run
        ⟨⟨U, a, seed 0, seed 1, seed 2, seed 3, e, 0⟩, p.1, p.2, q.classCount l e p⟩).1 = u :=
      (packet_ofSeed seed i g q e u ⟨p.1, hr⟩ ⟨p.2, hc⟩).mp hpack
    refine ⟨e, p, _, hp, rfl, ?_⟩
    simp only [SeededChildWitness.run, decide_eq_true_eq, actualCounts, Request.value,
      Bool.false_eq_true, ↓reduceIte]
    rw [symbol_of_seed seed i g e ⟨p.1, hr⟩ q, symbol_of_seed seed i g e ⟨p.2, hc⟩ q, hu]
    exact ⟨hport, hans⟩
  · rintro ⟨e, p, c, hp, rfl, hrun⟩
    obtain ⟨hr, hc⟩ := hkeys e p hp
    simp only [SeededChildWitness.run, decide_eq_true_eq, actualCounts, Request.value,
      Bool.false_eq_true, ↓reduceIte] at hrun
    rw [symbol_of_seed seed i g e ⟨p.1, hr⟩ q, symbol_of_seed seed i g e ⟨p.2, hc⟩ q] at hrun
    exact ⟨e, p, _, hp, (packet_ofSeed seed i g q e _ ⟨p.1, hr⟩ ⟨p.2, hc⟩).mpr rfl,
      hrun.1, hrun.2⟩

/-- Nine equal-width existential fields commit to a single bounded proposal before any
individual count can be challenged. -/
theorem plays_proposal (w : ℕ) (P : SeededChildWitness.Proposal → Prop) :
    QuantifiedWord.plays (fun xs => P (SeededChildWitness.parse w xs)) []
        (List.replicate (9 * w) false) ↔
      ∃ p, (∀ z ∈ p.fields, z < 2 ^ w) ∧ P p := by
  open QuantifiedWord BitString SeededChildWitness in
    have h := plays_exists_field (fun xs => P (parse w xs)) [] [] (9 * w)
    simp only [List.append_nil, List.nil_append, plays] at h
    rw [h]
    constructor
    · rintro ⟨index, hp⟩
      exact ⟨_, parse_fields_lt _ _, hp⟩
    · rintro ⟨p, hw, hp⟩
      let bits := word w p
      have hlen : bits.length = 9 * w := length_word w p
      have hi : lsbValue bits < 2 ^ (9 * w) := hlen ▸ lsbValue_lt bits
      refine ⟨⟨lsbValue bits, hi⟩, ?_⟩
      change P (parse w (lowBits (9 * w) (lsbValue bits)))
      rw [← hlen, lowBits_lsbValue]
      have he := parse_word w p hw []
      rw [List.append_nil] at he
      simpa only [bits, he] using hp

/-- The nine-field physical choice prefix covers every genuine parent witness on a bounded
parent graph. All subsequent endpoint and count tests use this same fixed proposal. -/
theorem child_iff_plays {U a : ℕ} (seed : SeededLabels.Seed U (6 * a)) (i : Fin a) (g : ℕ)
    {q : EndpointQuery} {es : List (ℕ × ℕ)} (hq : q.Represents es)
    (hkeys : ∀ e p, q.accepts e p → p.1 < U ∧ p.2 < U) (j : ℕ) (answer : ℕ × ℕ) :
    let l := Labels.ofSeed U a seed i g
    let w := (max q.size U).size
    (q.child (l.split q)).accepts j answer ↔
      QuantifiedWord.plays (fun xs =>
        let p := SeededChildWitness.parse w xs
        q.accepts p.edge p.ends ∧ p.counts = actualCounts q l p.edge j p.ends ∧
          SeededChildWitness.run
            ⟨⟨U, a, seed 0, seed 1, seed 2, seed 3, p.edge, 0⟩, i.val, g, j,
              p.ends, answer, p.counts⟩ = true) [] (List.replicate (9 * w) false) := by
  let l := Labels.ofSeed U a seed i g
  let w := (max q.size U).size
  dsimp only
  have hchild := child_iff_exists_witness seed i g q hkeys j answer
  dsimp only at hchild
  rw [hchild]
  let P (p : SeededChildWitness.Proposal) := q.accepts p.edge p.ends ∧
    p.counts = actualCounts q l p.edge j p.ends ∧ SeededChildWitness.run
      ⟨⟨U, a, seed 0, seed 1, seed 2, seed 3, p.edge, 0⟩, i.val, g, j,
        p.ends, answer, p.counts⟩ = true
  rw [plays_proposal w P]
  constructor
  · rintro ⟨e, p, c, hp, rfl, hr⟩
    have he : e < q.size := hq.1 ▸ ((hq.2 e p).mp hp).1
    obtain ⟨h₁, h₂⟩ := hkeys e p hp
    refine ⟨⟨e, p, _⟩, ?_, hp, rfl, hr⟩
    have ht := Nat.lt_size_self (max q.size U)
    have hq' := Nat.le_max_left q.size U
    have hU := Nat.le_max_right q.size U
    have hc := actualCounts_fit q l he.le j p
    dsimp only [SeededChildWitness.Proposal.fields]
    exact List.forall_mem_cons.mpr ⟨by dsimp [w]; omega, List.forall_mem_cons.mpr
      ⟨by dsimp [w]; omega, List.forall_mem_cons.mpr ⟨by dsimp [w]; omega, hc⟩⟩⟩
  · rintro ⟨p, _, hp, hc, hr⟩
    exact ⟨p.edge, p.ends, p.counts, hp, hc, hr⟩

end Turing.MultiTapeATM.SeededChildCounts
