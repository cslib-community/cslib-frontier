/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildWitness.Instruction
import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits

/-!
# Compiling the entire endpoint word to a Boolean or one recursive call

The terminal parses the parent proposal and count selector once. On a count branch it
reconstructs the sole signed singleton along the selected path and checks the two final
guessed keys. The dispatcher and flag initializer have uniform short polynomial running time.
-/

public section
namespace Turing.MultiTapeATM.SeededChildCounts.Joined

open Cslib BalancedSchedules Circuits.Frontier.NativeChild EndpointQuery SeededChildWitness Dispatch
open MultiTapeTM ComputableInPolyTime

private abbrev wordCut (h : Header) := (witnessFlags (width h.graph)).length
private abbrev common (h : Header) := max h.graph.edges h.graph.vertices
private abbrev countCut (h : Header) := (IntervalCountGame.flags (common h)).length

private def localCheck (h : Header) (p : Proposal) : Bool :=
  SeededChildWitness.run ⟨h.seed, h.coordinate, h.group, h.graph.child, p.ends, h.answer, p.counts⟩

private def countTask (h : Header) (part : List Bool) (r : BitQuery) : Instruction :=
  let v := h.graph.vertices.size
  let w := width h.graph
  let ys := part.drop (countCut h)
  let rest := ys.drop v
  let ends := (ofBits (ys.take v), ofBits (rest.take v))
  let challenge := (rest.drop v).headD false
  let result := IntervalCountGame.route (common h) (min w r.2.1) r.2.2 (part.take (countCut h))
  result.elim (.inl false) (fun kv => singleton ⟨h, kv.1, kv.2, ends, challenge⟩ r.1)

/-- The complete deterministic instruction produced by the quantified choice word. -/
def program (p : Header × List Bool) : Instruction :=
  let h := p.1
  let xs := p.2
  let data := Dispatch.run (h.graph, xs.take (wordCut h))
  data.2.elim (fun parent => if parent then .inr (data.1.edge, data.1.ends)
      else .inl (localCheck h data.1))
    (fun r => r.elim (.inl true) (countTask h (xs.drop (wordCut h))))

private theorem common_polyTime {α : Type} {enc : α ↪ List Bool} {h : α → Header}
    (hh : ComputableInPolyTime h enc encHeader) :
    ComputableInPolyTime (fun x => common (h x)) enc encNat := by
  have hg := encHeader_graph_polyTime hh
  have he := encPublic_edges_polyTime hg
  have hv := encPublic_vertices_polyTime hg
  exact (ite_decide (binary_lt' he hv) hv he).of_enc_eq fun x => by
    by_cases hn : (h x).graph.edges < (h x).graph.vertices
    · simp [common, hn, Nat.max_eq_right hn.le]
    · simp [common, hn, Nat.max_eq_left (Nat.le_of_not_gt hn)]

private theorem cut_polyTime {α : Type} {enc : α ↪ List Bool} {h : α → Header}
    (hh : ComputableInPolyTime h enc encHeader) :
    ComputableInPolyTime (fun x => wordCut (h x)) enc encUnary :=
  length_bits_comp (computableInPolyTime_witnessFlags.comp (encHeader_graph_polyTime hh))

private theorem local_polyTime {α : Type} {enc : α ↪ List Bool} {h : α → Header}
    {p : α → Proposal} (hh : ComputableInPolyTime h enc encHeader)
    (hp : ComputableInPolyTime p enc encProposal) :
    ComputableInPolyTime (fun x => localCheck (h x) (p x)) enc encBool :=
  SeededChildWitness.computableInPolyTime_run.comp
    (SeededChildWitness.encInput_mk_polyTime (encHeader_seed_polyTime hh)
      (encHeader_coordinate_polyTime hh) (encHeader_group_polyTime hh)
      (encPublic_child_polyTime (encHeader_graph_polyTime hh)) (encProposal_ends_polyTime hp)
      (encHeader_answer_polyTime hh) (encProposal_counts_polyTime hp))

private theorem countTask_polyTime {α : Type} {enc : α ↪ List Bool} {h : α → Header}
    {part : α → List Bool} {r : α → BitQuery} (hh : ComputableInPolyTime h enc encHeader)
    (hp : ComputableInPolyTime part enc encBits) (hr : ComputableInPolyTime r enc encBitQuery) :
    ComputableInPolyTime (fun x => countTask (h x) (part x) (r x)) enc encInstruction := by
  have hg := encHeader_graph_polyTime hh
  have hv := binary_size.comp (encPublic_vertices_polyTime hg)
  have hw := computableInPolyTime_width.comp hg
  have hN := common_polyTime hh
  have hk := length_bits_comp (IntervalCountGame.computableInPolyTime_flags.comp hN)
  have hy := bitsDropWithInput hp hk
  have hrest := bitsDropWithInput hy hv
  have hend := (bitsToNat.comp (bitsTakeWithInput hy hv)).prod
    (bitsToNat.comp (bitsTakeWithInput hrest hv))
  have hb := (ListEncoding.headD (enc₁ := encBool) (enc := encBits) false).computableInPolyTime.comp
    (bitsDropWithInput hrest hv)
  have hresult := IntervalCountGame.computableInPolyTime_route.comp
    (IntervalCountGame.encInput_mk_polyTime hN (binary_min_unary' hw hr.snd'.fst')
      hr.snd'.snd' (bitsTakeWithInput hp hk))
  let e := encPair encNat encNat
  have ha := fst enc e
  have kv := snd enc e
  exact optionElimWithInput (body := fun x (kv : ℕ × ℕ) => singleton ⟨h x, kv.1, kv.2,
      (ofBits (((part x).drop (countCut (h x))).take (h x).graph.vertices.size),
       ofBits ((((part x).drop (countCut (h x))).drop (h x).graph.vertices.size).take
         (h x).graph.vertices.size)),
       ((((part x).drop (countCut (h x))).drop (h x).graph.vertices.size).drop
         (h x).graph.vertices.size).headD false⟩ (r x).1) hresult
    (const (encOut := encInstruction) (Sum.inl false))
    (computableInPolyTime_singleton.comp
      ((encSingleton_mk_polyTime (hh.comp ha) kv.fst' kv.snd' (hend.comp ha) (hb.comp ha)).prod
        (hr.fst'.comp ha)))

/-- The flag tape is prepared from public graph sizes only. -/
theorem computableInPolyTime_flags : ComputableInPolyTime flags encPublic encBits := by
  have he := encPublic_edges_deg.computableInPolyTime
  have hu := encPublic_vertices_deg.computableInPolyTime
  have hN : ComputableInPolyTime (fun b : Public => max b.edges b.vertices) encPublic encNat :=
    (ite_decide (binary_lt' he hu) hu he).of_enc_eq fun b => by
      by_cases hb : b.edges < b.vertices
      · simp [hb, Nat.max_eq_right hb.le]
      · simp [hb, Nat.max_eq_left (Nat.le_of_not_gt hb)]
  have hf := (bitsReplicate false).comp (binary_size.comp hu)
  exact computableInPolyTime_witnessFlags.bitsAppend
    ((IntervalCountGame.computableInPolyTime_flags.comp hN).bitsAppend
      (hf.bitsAppend (hf.bitsAppend (const [true]))))

set_option maxHeartbeats 1200000 in
-- Elaborating the nested branch machines requires the encodings of each intermediate record.
/-- The complete runtime terminal requires polynomial time only in its short header and
choice word. It produces at most one positive endpoint request on every branch. -/
theorem computableInPolyTime_program : ComputableInPolyTime program (encPair encHeader encBits)
    encInstruction := by
  let enc := encPair encHeader encBits
  have hh := fst encHeader encBits
  have hx := snd encHeader encBits
  have hk := cut_polyTime hh
  have hd := Dispatch.computableInPolyTime_run.comp
    ((encHeader_graph_polyTime hh).prod (bitsTakeWithInput hx hk))
  have ha := fst enc encBool
  have hb := snd enc encBool
  have hp := hd.fst'.comp ha
  let rec' := sumInr encBool (encPair encNat (encPair encNat encNat))
  let halt := sumInl encBool (encPair encNat (encPair encNat encNat))
  have hl := ite hb (rec'.comp ((encProposal_edge_polyTime hp).prod (encProposal_ends_polyTime hp)))
    (halt.comp (local_polyTime (hh.comp ha) hp))
  have ho := fst enc (encOption encBitQuery)
  let z := encPair enc (encOption encBitQuery)
  have hz := fst z encBitQuery
  have htail := (bitsDropWithInput hx hk).comp (ho.comp hz)
  have hr := optionElimWithInput (body := fun (x : (Header × List Bool) × Option BitQuery) r =>
      countTask x.1.1 (x.1.2.drop (wordCut x.1.1)) r) (snd enc (encOption encBitQuery))
    (const (encOut := encInstruction) (Sum.inl true))
    (countTask_polyTime (hh.comp (ho.comp hz)) htail (snd z encBitQuery))
  exact Complexity.CSP.EdgeSolver.NativeCases.sumElimWithInput
    (left := fun x parent => let p := (Dispatch.run (x.1.graph, x.2.take (wordCut x.1))).1
      if parent then Sum.inr (p.edge, p.ends) else Sum.inl (localCheck x.1 p))
    (right := fun x r =>
    r.elim (.inl true) (countTask x.1 (x.2.drop (wordCut x.1)))) (.inl false) hd.snd' hl hr

/-- The native terminal computes exactly the leaf proposition of the complete shared game. -/
theorem program_spec {U a : ℕ} (seed : SeededLabels.Seed U (6 * a)) (i : Fin a)
    (g : ℕ) (q : EndpointQuery) (j : ℕ) (ans : ℕ × ℕ) (xs : List Bool) :
    let h := headerOf seed i g q.size j ans
    let l := Labels.ofSeed U a seed i g
    let check (p : Proposal) := SeededChildWitness.run
      ⟨⟨U, a, seed 0, seed 1, seed 2, seed 3, p.edge, 0⟩, i.val, g, j, p.ends, ans,
        p.counts⟩ = true
    holds q (program (h, xs)) ↔ Joined.value q l h.graph check xs := by
  intro h l check
  generalize hd : Dispatch.run (h.graph, xs.take (wordCut h)) = o
  rcases o with ⟨p, side⟩
  unfold program value
  dsimp only
  rw [hd]
  rcases side with (_ | _) | (_ | ⟨r, bit, claim⟩)
  · rfl
  · rfl
  · simp only [Sum.elim_inr, Option.elim, holds]
  · have hv := Dispatch.params_valid (b := h.graph) (xs := xs.take (wordCut h)) (by rw [hd])
    change bit < width h.graph at hv
    simp only [Sum.elim_inr, Option.elim, countTask, Nat.min_eq_right hv.le, countLeaf]
    let part := xs.drop (wordCut h)
    let ys := part.drop (countCut h)
    let result := IntervalCountGame.route (common h) bit claim (part.take (countCut h))
    let V := leaf q l (request r)
    change holds q (result.elim _ _) ↔ pairTest h.graph.vertices.size (V result) ys
    cases hv' : result with
    | none => simp [holds, pairTest, V, leaf]
    | some kv =>
      rcases kv with ⟨k,v⟩
      apply (singleton_spec seed i g q j ans r k v _ _).trans
      simp only [V, pairTest, ofBits_eq_lsbValue]
      rfl

end Turing.MultiTapeATM.SeededChildCounts.Joined
