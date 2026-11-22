/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.IntervalCount
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.TablePolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuardedWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalCount.InputWindow
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# Native alternating access to a block-network table entry

One request names a vertex and a binary assignment to its Boolean ports. The compiler computes
that vertex's actual port list, validates its incident letter codes, and decodes the interval
record when needed. It invokes the native interval counter for an interval and handles sinks,
subdivision vertices and invalid codes by their exact Boolean values. No tensor table or list of
coin strings is constructed.

`exists_evaluator` gives one fixed finite machine for every positive unary block width, unary
interval count and vertex number, binary schedule and assignment, and count-bit claim. Its clock
is linear in the source input length and polynomial in the remaining serialized request. The
compiler first plans on the empty source, then attaches the source with a linear native operation.
Composition through the recursive contraction remains part of #4728.
-/

public section

namespace Turing.MultiTapeATM.BlockTableEntry

open MultiTapeTM MultiTapePTM ComputableInPolyTime Cslib

/-- A local Boolean assignment and one bit of the corresponding block-network tensor entry. -/
structure Request where
  /-- The original machine's input. -/
  input : List Bool
  /-- Positive block width, represented in unary. -/
  width : ℕ
  /-- Number of intervals, represented in unary. -/
  intervals : ℕ
  /-- The base-three schedule number, represented in binary. -/
  schedule : ℕ
  /-- Existing explicit vertex number, represented in unary. -/
  vertex : ℕ
  /-- Binary assignment in the order of the vertex's actual Boolean ports. -/
  assignment : ℕ
  /-- Binary index of the requested count bit. -/
  bit : ℕ
  /-- The requested bit value. -/
  claim : Bool

/-- The input and numeric fields are framed, with the claim bit last. Width, interval count and
vertex number are unary; schedule, local assignment and bit index are binary. -/
enc_structure encRequest : Request where
  input : encBits, width : encUnary, intervals : encUnary, schedule : encNat,
  vertex : encUnary, assignment : encNat, bit : encNat, claim : encBool

variable {k s : ℕ} {State : Type} [Finite State] [DecidableEq State]
  (e : State ≃ Fin s) (machine : MultiTapePTM k Bool State)

private def plan (a : Request) : IntervalData k State ⊕ Bool :=
  tableEntryPlan e machine (max a.width 1) a.input a.intervals a.schedule a.vertex
    (explicitPortsNum k a.intervals (letterBits k s (max a.width 1)) a.schedule a.vertex)
    a.assignment

private def active (a : Request) : Bool := (plan e machine a).isLeft

private def answer (a : Request) : Bool :=
  (((plan e machine a).getRight?.getD false && decide (a.bit = 0)) == a.claim)

private noncomputable def word (a : Request) : List Bool :=
  (plan e machine a).getLeft?.elim [] fun d => IntervalCount.encRequest ⟨d, a.bit, a.claim⟩

private def strip (a : Request) : Request := { a with input := [] }

private noncomputable def shortSize (a : Request) : ℕ := (encRequest (strip a)).length + 1

private theorem strip_deg : ComputableInDegree strip encRequest encRequest 1 1 :=
  encRequest_mk_deg.comp
    (((ComputableInDegree.const (encMid := encBits) []).mono (d' := 1) (e' := 1)).prod
      (encRequest_width_deg.prod (encRequest_intervals_deg.prod (encRequest_schedule_deg.prod
        (encRequest_vertex_deg.prod (encRequest_assignment_deg.prod
          (encRequest_bit_deg.prod encRequest_claim_deg)))))))

private theorem request_length_eq (a : Request) :
    (encRequest a).length + 1 = 2 * a.input.length + shortSize a := by
  simp only [encRequest_apply, encRequestFields, shortSize, strip, length_encPair,
    encBits_apply, List.length_nil]
  omega

omit [Finite State] [DecidableEq State] in
private theorem plan_input (a : Request) (input : List Bool) :
    plan e machine { a with input := input } =
      (plan e machine a).map (fun d => { d with input := input }) id :=
  tableEntryPlan_input e machine _ _ _ _ _ _ _ _

omit [Finite State] [DecidableEq State] in
private theorem plan_input_field {a : Request} {d : IntervalData k State}
    (hp : plan e machine a = .inl d) : d.input = a.input := by
  have h := plan_input e machine a a.input
  change plan e machine a = _ at h
  rw [hp] at h
  exact congrArg IntervalData.input (Sum.inl.inj h)

omit [Finite State] [DecidableEq State] in
private theorem flags_strip (a : Request) :
    [active e machine (strip a), false, answer e machine (strip a)] =
      [active e machine a, false, answer e machine a] := by
  simp only [active, answer, strip, plan_input]
  cases plan e machine a <;> rfl

omit [DecidableEq State] in
private theorem word_strip {a : Request} {d : IntervalData k State}
    (hp : plan e machine a = .inl d) :
    word e machine (strip a) =
      IntervalCount.encRequest ⟨{ d with input := [] }, a.bit, a.claim⟩ := by
  simp only [word, strip, plan_input, hp, Sum.map_inl, Sum.getLeft?_inl, Option.elim_some]

omit [DecidableEq State] in
private theorem word_length_le (a : Request) :
    (word e machine a).length ≤ 4 * a.input.length + (word e machine (strip a)).length := by
  cases hp : plan e machine a with
  | inl d =>
    rw [word_strip e machine hp]
    have hn := plan_input_field e machine hp
    simp only [word, hp, Sum.getLeft?_inl, Option.elim_some,
      IntervalCount.encRequest_apply, IntervalCount.encRequestFields, encIntervalData_apply,
      IntervalData.equivProd, Equiv.coe_fn_mk, length_encPair, encBits_apply, List.length_nil, hn]
    omega
  | inr value => simp [word, hp]

omit [DecidableEq State] in
private theorem plan_polyTime : ComputableInPolyTime (plan e machine) encRequest
    encTableEntryPlan := by
  have hb := unary_max.comp (encRequest_width_deg.computableInPolyTime.prod (const 1))
  have hq := encRequest_intervals_deg.computableInPolyTime
  have hσ := encRequest_schedule_deg.computableInPolyTime
  have hv := encRequest_vertex_deg.computableInPolyTime
  have hm : ComputableInPolyTime (fun a : Request => letterBits k s (max a.width 1))
      encRequest encUnary := unary_mul' (const _) hb
  exact computableInPolyTime_tableEntryPlan e machine
    encRequest_input_deg.computableInPolyTime hb (fun _ => by omega) hq hσ hv
    (computableInPolyTime_explicitPortsNum hq hm hσ hv)
    encRequest_assignment_deg.computableInPolyTime

omit [DecidableEq State] in
private theorem word_polyTime : ComputableInPolyTime (word e machine) encRequest encBits := by
  have hp := plan_polyTime e machine
  have hl := (ComputableInO.getLeft?_deg encIntervalData encBool).computableInPolyTime.comp hp
  apply optionElimWithInput hl (const [])
  have hd := snd encRequest (encIntervalData (k := k) (State := State))
  have ha := fst encRequest (encIntervalData (k := k) (State := State))
  have hreq := IntervalCount.encRequest_mk_polyTime hd
    (encRequest_bit_deg.computableInPolyTime.comp ha)
    (encRequest_claim_deg.computableInPolyTime.comp ha)
  exact (of_eq (encIn := IntervalCount.encRequest) (encOut := encBits)
    (f := IntervalCount.encRequest) fun _ => rfl).comp hreq

omit [DecidableEq State] in
private theorem flags_polyTime : ComputableInPolyTime
    (fun a => [active e machine a, false, answer e machine a]) encRequest encBits := by
  have hp := plan_polyTime e machine
  have hc := (ComputableInO.isLeft_deg encIntervalData encBool).computableInPolyTime.comp hp
  have hv := optionGetDWithInput
    ((ComputableInO.getRight?_deg encIntervalData encBool).computableInPolyTime.comp hp)
    (const false)
  have hbit := bool_and' hv
    (decide_eq' encRequest_bit_deg.computableInPolyTime (const 0))
  have ha := decide_eq' hbit encRequest_claim_deg.computableInPolyTime
  exact (of_finite (encIn := encPair encBool encBool) (encOut := encBits)
    (fun p : Bool × Bool => [p.1, false, p.2])).comp (hc.prod ha)

omit [DecidableEq State] in
private theorem attach_inO :
    let enc := encPair encRequest (encTableEntryPlan (k := k) (State := State))
    ComputableInO
      (fun p : Request × (IntervalData k State ⊕ Bool) => p.2.elim
        (fun d => IntervalCount.encRequest ⟨{ d with input := p.1.input }, p.1.bit, p.1.claim⟩)
        (fun _ => [])) enc encBits (fun p => (enc p).length) (fun p => (enc p).length) := by
  have ha := ComputableInDegree.fst encRequest (encIntervalData (k := k) (State := State))
  have hd := ComputableInDegree.snd encRequest (encIntervalData (k := k) (State := State))
  have hdata := IntervalData.replaceInput_deg.comp (hd.prod (encRequest_input_deg.comp ha))
  have hreq := IntervalCount.encRequest_mk_deg.comp
    (hdata.prod ((encRequest_bit_deg.comp ha).prod (encRequest_claim_deg.comp ha)))
  have hl : ComputableInDegree
      (fun p : Request × IntervalData k State =>
        IntervalCount.encRequest ⟨{ p.2 with input := p.1.input }, p.1.bit, p.1.claim⟩)
      (encPair encRequest encIntervalData) encBits 1 1 :=
    (ComputableInDegree.of_eq (f := IntervalCount.encRequest) fun _ => rfl).comp hreq
  have hr : ComputableInO (fun _ : Request × Bool => []) (encPair encRequest encBool)
      encBits (fun p => (encPair encRequest encBool p).length)
        (fun p => (encPair encRequest encBool p).length) := .const []
  refine (hl.inO_one.sumElimSnd hr).mono 2 (fun p => ?_) (fun p => ?_) <;>
    cases p with
    | mk a value => cases value <;> simp [encTableEntryPlan] <;> omega

omit [DecidableEq State] in
private theorem exists_instruction_inO : ∃ d,
    let T := fun a => a.input.length + shortSize a ^ d
    ComputableInO
      (fun a => [active e machine a, false, answer e machine a] ++ word e machine a)
      encRequest encBits T T := by
  obtain ⟨dp, _, hp⟩ := (plan_polyTime e machine).exists_degree
  obtain ⟨df, _, hf⟩ := (flags_polyTime e machine).exists_degree
  let d := dp + df + 1
  have hbase (a : Request) : 1 ≤ shortSize a := by dsimp [shortSize]; omega
  have hpow (a : Request) (j : ℕ) (hj : j ≤ d) : shortSize a ^ j ≤ shortSize a ^ d :=
    Nat.pow_le_pow_right (hbase a) hj
  have hshort (a : Request) : shortSize a ≤ shortSize a ^ d := by
    simpa only [pow_one] using hpow a 1 (by dsimp [d]; omega)
  have hflags := hf.inO.comp strip_deg.inO_one
  have hplan := hp.inO.comp strip_deg.inO_one
  have hword := (attach_inO (k := k) (State := State)).comp_linear
    ((ComputableInDegree.id' (enc := encRequest)).inO_one.prod hplan)
  have hw : ComputableInO (word e machine) encRequest encBits
      (fun a => (encRequest a).length + ((encRequest a).length + shortSize a ^ dp))
      (fun a => (encRequest a).length + ((encRequest a).length + shortSize a ^ dp)) := by
    refine hword.of_enc_eq fun a => ?_
    have hfull := plan_input e machine (strip a) a.input
    change plan e machine a = _ at hfull
    simp only [encBits_apply, Function.comp_apply, word, hfull]
    cases plan e machine (strip a) <;> rfl
  have h := hflags.append hw (encOut := encBits) (g := fun a =>
      [active e machine a, false, answer e machine a] ++ word e machine a) fun a => by
    simp only [encBits_apply, Function.comp_apply, flags_strip]
  refine ⟨d, h.mono 9 (fun a => ?_) (fun a => ?_)⟩ <;>
    · have hn := request_length_eq a
      have hp := hpow a dp (by dsimp [d]; omega)
      have hf := hpow a df (by dsimp [d]; omega)
      have hs := hshort a
      dsimp only [shortSize] at hn hp hf hs ⊢
      omega

/-- A finite native machine checks one bit of the actual table entry, computing the port list
from the supplied schedule and vertex. All positive widths and all vertex numbers are admitted;
the complete branch clock is linear in the source length and polynomial in the remaining request
word, including its unary interval count and vertex number. -/
theorem exists_evaluator :
    ∃ (u : ℕ) (src : Fin u) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C E : ℕ),
      ∀ (host : List Bool) (a : Request), 0 < a.width → a.bit < a.width + 1 →
        let start := SharedWordFork.start src atm host (encRequest a) 0
        let time := C * (a.input.length + ((encRequest { a with input := [] }).length + 1) ^ E + 1)
        let ports := explicitPortsNum k a.intervals (letterBits k s a.width) a.schedule a.vertex
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (tableEntryNum e a.width machine a.input a.intervals a.schedule a.vertex ports
            a.assignment).testBit a.bit = a.claim) := by
  obtain ⟨v, src, S, hS, child, A, D, he⟩ := IntervalCount.exists_evaluator machine
  let := hS
  obtain ⟨d, hd⟩ := exists_instruction_inO e machine
  obtain ⟨u, Q, hQ, atm, c, hr⟩ := GuardedWord.exists_guarded_runner src child
    (active e machine) (answer e machine) (word e machine)
    (fun a => a.input.length + shortSize a ^ d) hd
  let leafTime (a : Request) :=
    A * (a.input.length + ((word e machine (strip a)).length + 1) ^ D + 1)
  have hw : PolyBounded shortSize (fun a => (word e machine (strip a)).length) :=
    (word_polyTime e machine).polyBounded_length.comp
      (PolyBounded.self.mono fun a => by dsimp [shortSize]; omega)
  let extra (a : Request) := c * (shortSize a ^ d + 1) +
    (2 * (word e machine (strip a)).length + 16) +
      A * (((word e machine (strip a)).length + 1) ^ D + 1)
  have ht : PolyBounded shortSize extra :=
    (((PolyBounded.const c).mul (PolyBounded.self.pow d |>.add (.const 1))).add
      (((PolyBounded.const 2).mul hw).add (.const 16))).add
        ((PolyBounded.const A).mul (hw.add (.const 1) |>.pow D |>.add (.const 1)))
  obtain ⟨C, E, hclock⟩ := ht.exists_le_linear_add_pow (fun a => a.input.length) (c + 8 + A)
    (fun a => by dsimp [shortSize]; omega)
  refine ⟨u + 2, Fin.natAdd u 0, Q, hQ, atm, C, E, ?_⟩
  intro host a hb hbit start time ports
  have hb' : max a.width 1 = a.width := max_eq_left (by omega)
  have hs := tableEntryPlan_spec e machine (max a.width 1) a.input a.intervals a.schedule
    a.vertex (explicitPortsNum k a.intervals (letterBits k s (max a.width 1)) a.schedule a.vertex)
    a.assignment
  change match plan e machine a with
    | .inl d => d.b = max a.width 1 ∧ d.count machine = _
    | .inr value => value.toNat = _ at hs
  rw [hb'] at hs
  have hchild : active e machine a = true → child.HaltsWithin (leafTime a)
      (SharedWordFork.start src child host (word e machine a) 0) := by
    intro ha
    cases hp : plan e machine a with
    | inl data =>
      simp only [hp] at hs
      have hh := (he host ⟨data, a.bit, a.claim⟩ (by rw [hs.1]; exact hbit)).1
      dsimp only [leafTime]
      rw [word_strip e machine hp, ← plan_input_field e machine hp]
      simpa only [word, hp, Sum.getLeft?_inl, Option.elim_some] using hh
    | inr value => simp [active, hp] at ha
  obtain ⟨hh, ha⟩ := hr host a (leafTime a) hchild
  have hmeaning : (if active e machine a then child.AcceptsWithin (leafTime a)
      (SharedWordFork.start src child host (word e machine a) 0) else answer e machine a = true) ↔
      (tableEntryNum e a.width machine a.input a.intervals a.schedule a.vertex ports
        a.assignment).testBit a.bit = a.claim := by
    cases hp : plan e machine a with
    | inl data =>
      simp only [hp] at hs
      have h := (he host ⟨data, a.bit, a.claim⟩ (by rw [hs.1]; exact hbit)).2
      dsimp only [leafTime]
      rw [word_strip e machine hp, ← plan_input_field e machine hp]
      simpa only [active, word, hp, Sum.isLeft_inl, Sum.getLeft?_inl,
        Option.elim_some, ↓reduceIte, hs.2, plan_input_field e machine hp] using h
    | inr value =>
      simp only [hp] at hs
      rw [← hs]
      cases value <;> cases hi : a.bit <;> simp [active, answer, hp, hi, Nat.testBit_add_one]
  have hstart : start = (WorkTapePredicate.config host (encRequest a)).withState
      (some atm.toPTM.initial) := SharedWordFork.start_eq_workTape atm host (encRequest a)
  rw [hstart]
  have hc : c * (a.input.length + shortSize a ^ d + 1) +
      (2 * (word e machine a).length + 16) + leafTime a ≤ time := by
    calc
      _ ≤ c * (a.input.length + shortSize a ^ d + 1) +
          (2 * (4 * a.input.length + (word e machine (strip a)).length) + 16) + leafTime a := by
        gcongr
        exact word_length_le e machine a
      _ = (c + 8 + A) * a.input.length + extra a := by dsimp [extra, leafTime]; ring
      _ ≤ time := hclock a
  exact ⟨hh.mono hc, ⟨fun h => hmeaning.mp (ha.mp (h.of_halted_stepCoins hh)),
    fun h => (ha.mpr (hmeaning.mpr h)).mono hc⟩⟩

end Turing.MultiTapeATM.BlockTableEntry
