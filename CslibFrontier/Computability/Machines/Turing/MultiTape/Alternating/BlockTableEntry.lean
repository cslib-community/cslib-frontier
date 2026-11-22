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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
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
is polynomial in the full serialized request, including the source input. The sharper source
charge and composition through the recursive contraction remain part of #4728.
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
private theorem instruction_polyTime : ComputableInPolyTime
    (fun a => [active e machine a, false, answer e machine a] ++ word e machine a)
      encRequest encBits := by
  have hp := plan_polyTime e machine
  have hc := (ComputableInO.isLeft_deg encIntervalData encBool).computableInPolyTime.comp hp
  have hv := optionGetDWithInput
    ((ComputableInO.getRight?_deg encIntervalData encBool).computableInPolyTime.comp hp)
    (const false)
  have hbit := bool_and' hv
    (decide_eq' encRequest_bit_deg.computableInPolyTime (const 0))
  have ha := decide_eq' hbit encRequest_claim_deg.computableInPolyTime
  have hflags := (of_finite (encIn := encPair encBool encBool) (encOut := encBits)
    (fun p : Bool × Bool => [p.1, false, p.2])).comp (hc.prod ha)
  exact hflags.bitsAppend (word_polyTime e machine)

omit [DecidableEq State] in
private theorem interval_clock_le (a : IntervalCount.Request k State) (A D : ℕ) :
    A * (a.interval.input.length +
      ((IntervalCount.encRequest { a with interval := { a.interval with input := [] } }).length +
        1) ^ D + 1) ≤
      (2 * A) * ((IntervalCount.encRequest a).length + 1) ^ (D + 1) := by
  have hn : a.interval.input.length ≤ (IntervalCount.encRequest a).length := by
    simp only [IntervalCount.encRequest_apply, IntervalCount.encRequestFields,
      encIntervalData_apply, IntervalData.equivProd, Equiv.coe_fn_mk, length_encPair, encBits_apply]
    omega
  have hs :
      (IntervalCount.encRequest { a with interval := { a.interval with input := [] } }).length ≤
        (IntervalCount.encRequest a).length := by
    simp only [IntervalCount.encRequest_apply, IntervalCount.encRequestFields,
      encIntervalData_apply, IntervalData.equivProd, Equiv.coe_fn_mk, length_encPair, encBits_apply,
      List.length_nil]
    omega
  have hp := (Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) D).trans
    (Nat.pow_le_pow_right (by omega) (show D ≤ D + 1 by omega))
  have hl : (IntervalCount.encRequest a).length + 1 ≤
      ((IntervalCount.encRequest a).length + 1) ^ (D + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (show 1 ≤ (IntervalCount.encRequest a).length + 1 by omega) (show 1 ≤ D + 1 by omega)
  have hsum : a.interval.input.length +
      ((IntervalCount.encRequest { a with interval := { a.interval with input := [] } }).length +
        1) ^ D + 1 ≤ 2 * ((IntervalCount.encRequest a).length + 1) ^ (D + 1) := by omega
  exact (Nat.mul_le_mul_left A hsum).trans_eq (by ring)

/-- A finite native machine checks one bit of the actual table entry, computing the port list
from the supplied schedule and vertex. All positive widths and all vertex numbers are admitted;
the complete branch clock is polynomial in the full request word. -/
theorem exists_evaluator :
    ∃ (u : ℕ) (src : Fin u) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C E : ℕ),
      ∀ (host : List Bool) (a : Request), 0 < a.width → a.bit < a.width + 1 →
        let start := SharedWordFork.start src atm host (encRequest a) 0
        let time := C * ((encRequest a).length + 1) ^ E
        let ports := explicitPortsNum k a.intervals (letterBits k s a.width) a.schedule a.vertex
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (tableEntryNum e a.width machine a.input a.intervals a.schedule a.vertex ports
            a.assignment).testBit a.bit = a.claim) := by
  obtain ⟨v, src, S, hS, child, A₀, D₀, he₀⟩ := IntervalCount.exists_evaluator machine
  let := hS
  let A := 2 * A₀
  let D := D₀ + 1
  have he (host : List Bool) (a : IntervalCount.Request k State) (hb : a.bit < a.interval.b + 1) :
      let start := SharedWordFork.start src child host (IntervalCount.encRequest a) 0
      let time := A * ((IntervalCount.encRequest a).length + 1) ^ D
      child.HaltsWithin time start ∧ (child.AcceptsWithin time start ↔
        (a.interval.count machine).testBit a.bit = a.claim) := by
    obtain ⟨hh, ha⟩ := he₀ host a hb
    have hc := interval_clock_le a A₀ D₀
    exact ⟨hh.mono hc, ⟨fun h => ha.mp (h.of_halted_stepCoins hh),
      fun h => (ha.mpr h).mono hc⟩⟩
  obtain ⟨d, _, hd⟩ := (instruction_polyTime e machine).exists_degree
  obtain ⟨u, Q, hQ, atm, c, hr⟩ := GuardedWord.exists_guarded_runner src child
    (active e machine) (answer e machine) (word e machine)
    (fun a => ((encRequest a).length + 1) ^ d) hd.inO
  let leafTime (a : Request) := A * ((word e machine a).length + 1) ^ D
  have hw := (word_polyTime e machine).polyBounded_length
  have ht : PolyBounded (fun a : Request => (encRequest a).length)
      (fun a => c * (((encRequest a).length + 1) ^ d + 1) +
        (2 * (word e machine a).length + 16) + leafTime a) :=
    (((PolyBounded.const c).mul ((PolyBounded.self.add (.const 1)).pow d |>.add (.const 1))).add
      (((PolyBounded.const 2).mul hw).add (.const 16))).add
        ((PolyBounded.const A).mul (hw.add (.const 1) |>.pow D))
  obtain ⟨C, E, hclock⟩ := ht.exists_le
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
      simpa only [leafTime, word, hp, Sum.getLeft?_inl, Option.elim_some] using hh
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
      simpa only [active, word, leafTime, hp, Sum.isLeft_inl, Sum.getLeft?_inl,
        Option.elim_some, ↓reduceIte, hs.2] using h
    | inr value =>
      simp only [hp] at hs
      rw [← hs]
      cases value <;> cases hi : a.bit <;> simp [active, answer, hp, hi, Nat.testBit_add_one]
  have hstart : start = (WorkTapePredicate.config host (encRequest a)).withState
      (some atm.toPTM.initial) := SharedWordFork.start_eq_workTape atm host (encRequest a)
  rw [hstart]
  have hc := hclock a
  exact ⟨hh.mono hc, ⟨fun h => hmeaning.mp (ha.mp (h.of_halted_stepCoins hh)),
    fun h => (ha.mpr (hmeaning.mpr h)).mono hc⟩⟩

end Turing.MultiTapeATM.BlockTableEntry
