/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantPortsInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DescendantEndpoint
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Native
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuardedWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Native verification of compressed ordered ports

One fixed finite alternating machine verifies a proposed increasing port list. It prepares the
universal edge challenge and shared endpoint guesses, then runs either the local membership test
or the complete native descendant endpoint controller. The original schedule is copied only a
fixed number of times; every polynomial operates on the short candidate and ancestry.

The compiler starts from one encoded request on a work tape. Its construction supplies the
endpoint machine internally, including the root lookup, and preserves the ambient source input.
-/

public section

namespace Turing.MultiTapeATM.DescendantPorts

open MultiTapeTM MultiTapePTM MultiTapeTM.DescendantPorts QuantifiedWord SeededChildCounts
open Cslib.Circuits.Frontier.NativeChild
open Cslib.Circuits.Frontier (DescribedNetwork)

private def predicate (k : ℕ) (x : Input × List Bool) : Prop :=
  Joined.holds ⟨x.1.context.query.edges,
    MultiTapeTM.DescendantEndpoint.accepts
      (RootEndpointQuery.endpointQuery k x.1.context.copies x.1.raw) x.1.context.frames⟩
    (outcome (data x))

private theorem endpoint_size : PolyBounded challengeSize
    (fun x : Input × List Bool => (MultiTapeTM.DescendantEndpoint.encPosition
      (endpoint (data x))).length) :=
  endpoint_polyTime.polyBounded_length.comp (PolyBounded.self.mono (fun x => by
    simp only [challengeSize]; omega))

private theorem exists_endpoint (k : ℕ) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C D : ℕ),
      ∀ (host : List Bool) (x : Input × List Bool),
        let p := endpoint (data x)
        let start := SharedWordFork.start src atm host (encChallenge x) 0
        let time := C * (x.1.raw.length + challengeSize x ^ D + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          MultiTapeTM.DescendantEndpoint.accepts
            (RootEndpointQuery.endpointQuery k x.1.context.copies x.1.raw)
            x.1.context.frames p.edge (p.row, p.column)) := by
  obtain ⟨K, schedule, query, S, hS, leaf, A, E, hne, hleaf⟩ :=
    DescendantEndpoint.exists_evaluator k
  obtain ⟨d, hd⟩ := exists_endpoint_inO
  let T := fun x : Input × List Bool =>
    (encChallenge x).length + x.1.raw.length + challengeSize x ^ d
  have hp : ComputableInO (fun x => endpoint (data x)) encChallenge
      MultiTapeTM.DescendantEndpoint.encPosition T T :=
    hd.mono_le (fun _ => by dsimp [T]; omega) (fun _ => by dsimp [T]; omega)
  have hraw := (encInput_raw_deg.comp (ComputableInDegree.fst encInput encBits)).inO_one
  have hr : ComputableInO (fun x : Input × List Bool => x.1.raw) encChallenge encBits T T :=
    hraw.mono_le (fun _ => by dsimp [T]; omega) (fun _ => by dsimp [T]; omega)
  obtain ⟨U, src, Q, hQ, atm, c, hload⟩ := TwoWordLoad.exists_load_from hr hp
    schedule query hne leaf
  let small := fun x : Input × List Bool =>
    c * (2 * challengeSize x + 3 + challengeSize x ^ d + 1) + 8 +
      A * (((MultiTapeTM.DescendantEndpoint.encPosition (endpoint (data x))).length +
        challengeSize x + 1) ^ E + 1)
  have hsmall : PolyBounded challengeSize small := by
    have hs : PolyBounded challengeSize challengeSize := .self
    exact ((((PolyBounded.const c).mul
      (((((PolyBounded.const 2).mul hs).add (.const 3)).add (hs.pow d)).add (.const 1))).add
        (.const 8)).add ((PolyBounded.const A).mul
          ((((endpoint_size.add hs).add (.const 1)).pow E).add (.const 1))))
  obtain ⟨C, D, hbound⟩ := hsmall.exists_le_linear_add_pow (fun x => x.1.raw.length)
    (5 * c + A) (fun x => by simp [challengeSize])
  refine ⟨U, src, Q, hQ, atm, C, D, ?_⟩
  intro host x p start time
  let args := (outcome (data x)).getRight?.getD (0, (0, 0))
  have he := hleaf host x.1.raw x.1.context.copies x.1.context.frames args.1 args.2
  have heq : endpoint (data x) = MultiTapeTM.DescendantEndpoint.root
      x.1.context.copies x.1.context.frames args.1 args.2 := by
    rfl
  have ht : leaf.HaltsWithin
      (A * (x.1.raw.length + ((MultiTapeTM.DescendantEndpoint.encPosition p).length +
        x.1.raw.length.size + 1) ^ E + 1))
      ((TwoWordInput.ready schedule query host x.1.raw
        (MultiTapeTM.DescendantEndpoint.encPosition p)).withState (some leaf.toPTM.initial)) := by
    simpa only [p, heq] using he.1
  have h := hload host x 0 (Nat.zero_le _) _ ht
  have hclock : c * (T x + 1) + 8 +
      A * (x.1.raw.length + ((MultiTapeTM.DescendantEndpoint.encPosition p).length +
        x.1.raw.length.size + 1) ^ E + 1) ≤ time := by
    refine le_trans ?_ (hbound x)
    have hl := length_encChallenge x
    have hs : x.1.raw.length.size ≤ challengeSize x := by simp only [challengeSize]; omega
    have hz := Nat.pow_le_pow_left (show
      (MultiTapeTM.DescendantEndpoint.encPosition p).length + x.1.raw.length.size + 1 ≤
      (MultiTapeTM.DescendantEndpoint.encPosition p).length + challengeSize x + 1 by omega) E
    have hprep := Nat.mul_le_mul_left c (show T x + 1 ≤
        5 * x.1.raw.length + (2 * challengeSize x + 3 + challengeSize x ^ d + 1) by
      dsimp only [T]
      omega)
    have hterm := Nat.mul_le_mul_left A
      (Nat.add_le_add_right (Nat.add_le_add_left hz x.1.raw.length) 1)
    calc
      _ ≤ c * (5 * x.1.raw.length + (2 * challengeSize x + 3 + challengeSize x ^ d + 1)) +
          8 + A * (x.1.raw.length + ((MultiTapeTM.DescendantEndpoint.encPosition p).length +
            challengeSize x + 1) ^ E + 1) :=
        Nat.add_le_add (Nat.add_le_add_right hprep 8) hterm
      _ = (5 * c + A) * x.1.raw.length + small x := by dsimp only [small, p]; ring
  simp only [Nat.zero_add] at h
  have hv : leaf.AcceptsWithin
      (A * (x.1.raw.length + ((MultiTapeTM.DescendantEndpoint.encPosition p).length +
        x.1.raw.length.size + 1) ^ E + 1))
      ((TwoWordInput.ready schedule query host x.1.raw
        (MultiTapeTM.DescendantEndpoint.encPosition p)).withState (some leaf.toPTM.initial)) ↔
      MultiTapeTM.DescendantEndpoint.accepts
        (RootEndpointQuery.endpointQuery k x.1.context.copies x.1.raw)
        x.1.context.frames p.edge (p.row, p.column) := by
    simpa only [p, heq, MultiTapeTM.DescendantEndpoint.root] using he.2
  exact ⟨h.1.mono hclock, ⟨fun acc => hv.mp (h.2.mp (acc.of_halted_stepCoins h.1)),
    fun v => (h.2.mpr (hv.mpr v)).mono hclock⟩⟩

private theorem exists_terminal (k : ℕ) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C D : ℕ),
      ∀ (host : List Bool) (x : Input × List Bool),
        let start := SharedWordFork.start src atm host (encChallenge x) (encChallenge x).length
        let time := C * (x.1.raw.length + challengeSize x ^ D + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔ predicate k x) := by
  obtain ⟨K, childSource, S, hS, child, A, E, hchild⟩ := exists_endpoint k
  obtain ⟨d, hd⟩ := exists_instruction_inO
  obtain ⟨u, Q, hQ, guard, c, hguard⟩ := GuardedWord.exists_guarded_runner childSource child
    (fun x => active (data x)) (fun x => answer (data x)) encChallenge
    (fun x => x.1.raw.length + challengeSize x ^ d) hd
  let src : Fin (u + 2) := Fin.natAdd u 0
  let atm := prependTM (TwoWordLoad.rewind src) guard
  let small := fun x : Input × List Bool =>
    6 * challengeSize x + 27 + c * (challengeSize x ^ d + 1) +
      A * (challengeSize x ^ E + 1)
  have hsmall : PolyBounded challengeSize small := by growth_poly
  obtain ⟨C, D, hbound⟩ := hsmall.exists_le_linear_add_pow (fun x => x.1.raw.length)
    (12 + c + A) (fun x => by simp [challengeSize])
  refine ⟨u + 2, src, _, inferInstance, atm, C, D, ?_⟩
  intro host x start time
  have hc := hchild host x
  have hg := hguard host x _ (fun _ => hc.1)
  rw [← SharedWordFork.start_eq_workTape guard host (encChallenge x)] at hg
  have hh := SharedWordFork.rewind_spec src guard host (encChallenge x)
    (encChallenge x).length _ le_rfl hg.1
  have htime : (encChallenge x).length + 2 +
      (c * (x.1.raw.length + challengeSize x ^ d + 1) +
        (2 * (encChallenge x).length + 16) +
        A * (x.1.raw.length + challengeSize x ^ E + 1)) ≤ time := by
    refine le_trans ?_ (hbound x)
    have hl := length_encChallenge x
    dsimp only [small]
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at *
    omega
  have hv : (if active (data x) then child.AcceptsWithin
      (A * (x.1.raw.length + challengeSize x ^ E + 1))
      (SharedWordFork.start childSource child host (encChallenge x) 0)
      else answer (data x) = true) ↔ predicate k x := by
    rw [hc.2]
    unfold predicate active answer endpoint
    cases outcome (data x) <;> rfl
  refine ⟨hh.1.mono htime, ?_⟩
  exact ⟨fun acc => hv.mp (hg.2.mp (hh.2.mp (acc.of_halted_stepCoins hh.1))),
    fun v => (hh.2.mpr (hg.2.mpr (hv.mpr v))).mono htime⟩

/-- One fixed finite machine verifies every compressed port request. All quantifier choices,
native preparation and the internally constructed descendant endpoint computation are charged.
The long root schedule occurs only linearly in the complete branch bound. -/
theorem exists_evaluator (k : ℕ) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C D : ℕ),
      ∀ (host : List Bool) (a : Input),
        let start := SharedWordFork.start src atm host (encInput a) 0
        let time := C * (a.raw.length + shortSize a ^ D + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          plays (fun xs => Joined.holds ⟨a.context.query.edges,
            MultiTapeTM.DescendantEndpoint.accepts
              (RootEndpointQuery.endpointQuery k a.context.copies a.raw) a.context.frames⟩
            (program (a.context.query, xs))) [] (flags a.context.query)) := by
  obtain ⟨K, source, S, hS, terminal, A, E, hterminal⟩ := exists_terminal k
  obtain ⟨d, hd⟩ := exists_flags_inO
  obtain ⟨U, src, Q, hQ, atm, c, hprepare⟩ :=
    QuantifiedWord.exists_of_terminal hd source terminal
  let choiceSize := fun a : Input =>
    2 * (encContext a.context).length + (flags a.context.query).length + a.raw.length.size + 2
  have hctx : PolyBounded shortSize (fun a : Input => (encContext a.context).length) :=
    PolyBounded.self.mono (fun a => by simp only [shortSize]; omega)
  have hflags : PolyBounded shortSize (fun a : Input => (flags a.context.query).length) :=
    (flags_polyTime.comp encContext_query_deg.computableInPolyTime).polyBounded_length.comp hctx
  have hsize : PolyBounded shortSize choiceSize := by
    have hraw : PolyBounded shortSize (fun a : Input => a.raw.length.size) :=
      PolyBounded.self.mono (fun a => by simp only [shortSize]; omega)
    exact ((((PolyBounded.const 2).mul hctx).add hflags).add hraw).add (.const 2)
  let small := fun a : Input =>
    c * (shortSize a ^ d + 1) + 12 + 2 * shortSize a +
      A * (choiceSize a ^ E + 1) + 2 * (flags a.context.query).length
  have hsmall : PolyBounded shortSize small :=
    ((((((PolyBounded.const c).mul ((PolyBounded.self.pow d).add (.const 1))).add
      (.const 12)).add ((PolyBounded.const 2).mul PolyBounded.self)).add
        ((PolyBounded.const A).mul ((hsize.pow E).add (.const 1)))).add
          ((PolyBounded.const 2).mul hflags))
  obtain ⟨C, D, hbound⟩ := hsmall.exists_le_linear_add_pow (fun a => a.raw.length)
    (c + 4 + A) (fun a => by simp [shortSize])
  refine ⟨U, src, Q, hQ, atm, C, D, ?_⟩
  intro host a start time
  let pre := frame (encInput a)
  let players := flags a.context.query
  let terminalTime := A * (a.raw.length + choiceSize a ^ E + 1)
  have hp := hprepare host a 0 (Nat.zero_le _) terminalTime (fun xs => predicate k (a, xs)) (by
    intro xs hxs
    have ht := hterminal host (a, xs)
    have hsize' : challengeSize (a, xs) = choiceSize a := by
      simp only [challengeSize, encData, data, choiceSize, length_encPair, encBits_apply,
        hxs]
      omega
    simpa only [hsize', terminalTime] using ht)
  simp only [Nat.zero_add] at hp
  have htime : c * (a.raw.length + shortSize a ^ d + 1) + 8 +
      (pre.length + (terminalTime + 2 * players.length + 1)) ≤ time := by
    refine le_trans ?_ (hbound a)
    have hctxlen : (encContext a.context).length + 1 ≤ shortSize a := by
      simp only [shortSize]; omega
    simp only [pre, terminalTime, players, small, length_frame, encInput_apply,
      encInputFields, length_encPair, encBits_apply, Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  exact ⟨hp.1.mono htime, ⟨fun acc => hp.2.mp (acc.of_halted_stepCoins hp.1),
    fun v => (hp.2.mpr v).mono htime⟩⟩

/-- The fixed verifier accepts precisely the stored ordered ports of an actual descendant of
the block network. The mathematical network is used only to specify correctness; the machine
receives its raw root schedule, short seed frames, graph sizes and candidate port list. -/
theorem exists_actual_evaluator (k : ℕ) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C d : ℕ),
      ∀ {R T : Type} (source : MultiTapePTM k Bool R) (word : List Bool)
        (b q copies σ : ℕ) (code : BlockLetter k R b → Fin copies → Bool)
        (frames : List MultiTapeTM.DescendantEndpoint.Frame) (network : DescribedNetwork T)
        (rows : ℕ),
        MultiTapeTM.DescendantEndpoint.Represents (RootPredecessorGraph.vertexCount k q copies)
          (RootPortGraph.ends (q := q) source word b σ code) frames
          network.vertices.length network.edgeEnds →
        network.IsRowsFirstBipartite rows →
        (∀ v ∈ network.vertices, v.1.Pairwise (· < ·)) →
        ∀ (host : List Bool) (vertex : ℕ) (ports : List ℕ),
          let raw := ScheduleBits.rows (List.ofFn (scheduleOfNat k q σ))
          let a : Input := ⟨raw, ⟨copies, frames,
            ⟨network.numEdges, network.vertices.length, vertex, ports⟩⟩⟩
          let start := SharedWordFork.start src atm host (encInput a) 0
          let time := C * (raw.length + shortSize a ^ d + 1)
          atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
            ∃ hv : vertex < network.vertices.length, ports = network.vertices[vertex].1) := by
  obtain ⟨U, src, Q, hQ, atm, C, d, hrun⟩ := exists_evaluator k
  refine ⟨U, src, Q, hQ, atm, C, d, ?_⟩
  intro R T source word b q copies σ code frames network rows hframes hnetwork hports
    host vertex ports raw a start time
  let endpoint : EndpointQuery := ⟨network.numEdges,
    MultiTapeTM.DescendantEndpoint.accepts (RootEndpointQuery.endpointQuery k copies raw) frames⟩
  have hbase := RootEndpointQuery.represents_descendant (q := q) source word b σ code []
  have hendpoint : endpoint.Represents network.edgeEnds := by
    refine ⟨?_, fun edge answer =>
      MultiTapeTM.DescendantEndpoint.accepts_iff_of_represents _ hbase hframes edge answer⟩
    simp [endpoint, DescribedNetwork.edgeEnds]
  have hs := hrun host a
  exact ⟨hs.1, hs.2.trans (plays_program_network network hnetwork hports
    endpoint hendpoint vertex ports)⟩

end Turing.MultiTapeATM.DescendantPorts
