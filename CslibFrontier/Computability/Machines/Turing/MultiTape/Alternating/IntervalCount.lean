/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalCount.Decode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingContext
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.TerminalLayout
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedWordFork
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Foundations.Data.BitString.Weight

/-!
# Native alternating bits of an interval count

`exists_evaluator` compiles a fixed finite probabilistic machine into a finite alternating
machine that checks bits of its actual `IntervalData.count`. The supplied work word contains
the interval data, a binary bit index and a claim. The machine constructs the count limit
`2 ^ b`, the precision `b + 1`, and all counting fields on its tapes. A branch selects one
coin string, replays it, and checks the resulting control, coordinates and work windows.

The branch bound is polynomial in the full existing request encoding, including the source
word and unary block width. It does not enumerate `2 ^ b` strings. The sharper charge for the
original input and composition through recursive contraction remain part of #4728.
-/

public section

namespace Turing.MultiTapeATM.IntervalCount

open MultiTapeTM MultiTapePTM ComputableInPolyTime Cslib
open Cslib.Circuits.Boolean.CarryLookahead.Query

variable {k : ℕ} {State : Type}

/-- Actual interval data and a claimed bit of its coin-string count. -/
structure Request (k : ℕ) (State : Type) where
  /-- The existing general interval record, including its source input word. -/
  interval : IntervalData k State
  /-- Binary index into the count, below the block width plus one. -/
  bit : ℕ
  /-- Requested value of that bit. -/
  claim : Bool

variable [Finite State]

noncomputable section

/-- The full interval record and binary bit index are framed, followed by the claim bit. -/
enc_structure encRequest : Request k State where
  interval : (encIntervalData (k := k) (State := State)), bit : encNat, claim : encBool

end

variable [DecidableEq State]

private noncomputable def predicate (machine : MultiTapePTM k Bool State)
    (p : List Bool × ℕ) : Bool :=
  let d := IntervalData.decoder.decode p.1
  decide (machine.LocalIntervalStepData d.b d.input d.J d.δ d.cIn d.wIn d.cOut d.wOut
    (BitString.lowBits d.b p.2))

private theorem predicate_encoded (machine : MultiTapePTM k Bool State)
    (d : IntervalData k State) (j : ℕ) : predicate machine (encIntervalData d, j) =
      decide (machine.LocalIntervalStepData d.b d.input d.J d.δ d.cIn d.wIn d.cOut d.wOut
        (BitString.lowBits d.b j)) := by
  simp only [predicate, IntervalData.decoder.decode_enc]

private theorem predicate_polyTime (machine : MultiTapePTM k Bool State) :
    ComputableInPolyTime (predicate machine) (encPair encBits encNat) encBool := by
  have hd : ComputableInPolyTime (fun p : List Bool × ℕ => IntervalData.decoder.decode p.1)
      (encPair encBits encNat) (encIntervalData (k := k) (State := State)) :=
    IntervalData.decoder.computableInPolyTime.comp (fst encBits encNat)
  have hc := bitsLow (IntervalData.computableInPolyTime_b.comp hd) (snd encBits encNat)
  exact computableInPolyTime_localIntervalStepData machine hd hc

private theorem count_eq_sum (machine : MultiTapePTM k Bool State) (d : IntervalData k State) :
    d.count machine =
      ∑ j ∈ Finset.range (2 ^ d.b), (predicate machine (encIntervalData d, j)).toNat := by
  rw [IntervalData.count, localIntervalCount, BitString.enumList_eq_ofFn, List.countP_ofFn,
    ← Fin.sum_univ_eq_sum_range]
  change BitString.weight _ = _
  rw [BitString.weight_eq_sum_toNat]
  apply Finset.sum_congr rfl
  intro j _
  rw [predicate_encoded, BitString.lowBits_eq_ofFn_equivFin_symm]

private def parameters (a : Request k State) : CountingInput.Input :=
  ⟨2 ^ a.interval.b, ⟨a.interval.b + 1, a.bit, a.claim⟩⟩

omit [DecidableEq State] in
private theorem parameters_polyTime : ComputableInPolyTime
    (parameters (k := k) (State := State)) encRequest CountingInput.encInput := by
  have hi := encRequest_interval_polyTime (id' (encIn := encRequest (k := k) (State := State)))
  have hb := IntervalData.computableInPolyTime_b.comp hi
  apply CountingInput.encInput_mk_polyTime
  · exact binary_two_pow.comp hb
  · apply Initial.encInput_mk_polyTime
    · exact unary_to_binary.comp (unary_add' hb (const 1))
    · fun_prop
    · fun_prop

omit [DecidableEq State] in
private theorem width_le_length (d : IntervalData k State) : d.b ≤ (encIntervalData d).length := by
  rw [encIntervalData_apply, length_encPair, length_encPair]
  simp only [encBits_apply, encUnary_apply, List.length_replicate]
  change d.b ≤ 2 * d.input.length + 1 + (2 * d.b + 1 + _)
  omega

/-- One finite native machine checks every interval count bit. Its entire branch time is
polynomial in the actual full request word; no enumerated table or caller-supplied leaf
implementation is used. Every source-input word is admitted in the original interval encoding. -/
theorem exists_evaluator (machine : MultiTapePTM k Bool State) :
    ∃ (u : ℕ) (src : Fin u) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C E : ℕ),
      ∀ (host : List Bool) (a : Request k State), a.bit < a.interval.b + 1 →
        let start := SharedWordFork.start src atm host (encRequest a) 0
        let time := C * ((encRequest a).length + 1) ^ E
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (a.interval.count machine).testBit a.bit = a.claim) := by
  obtain ⟨d, _, hp⟩ := (predicate_polyTime machine).exists_degree
  obtain ⟨scratch, u, r, q, S, hS, eval, A, D, he⟩ :=
    CarryLookaheadCountingFromParametersCost.exists_evaluator_on_context
      (encIntervalData (k := k) (State := State)) (fun _ => 0)
      (fun x => 2 * (encIntervalData x).length + 2) (predicate machine) hp.inO d
      (fun _ => by omega) (by
        intro x j
        rw [length_encPair]
        simp only [encBits_apply, encNat_apply, ← Nat.size_eq_bits_len]
        exact (Nat.pow_le_pow_left (by omega) d).trans (Nat.le_add_left _ _))
  let := hS
  have hi : ComputableInPolyTime (Request.interval (k := k) (State := State))
      encRequest encIntervalData := by fun_prop
  obtain ⟨di, _, hdi⟩ := hi.exists_degree
  obtain ⟨dp, _, hdp⟩ := parameters_polyTime (k := k) (State := State) |>.exists_degree
  let deg := di + dp
  let T (a : Request k State) := ((encRequest a).length + 1) ^ deg
  have hf : ComputableInO Request.interval encRequest encIntervalData T T :=
    hdi.inO.mono_le (fun _ => Nat.pow_le_pow_right (by omega) (by omega))
      (fun _ => Nat.pow_le_pow_right (by omega) (by omega))
  have hg : ComputableInO parameters encRequest CountingInput.encInput T T :=
    hdp.inO.mono_le (fun _ => Nat.pow_le_pow_right (by omega) (by omega))
      (fun _ => Nat.pow_le_pow_right (by omega) (by omega))
  obtain ⟨v, src, Q, hQ, atm, c, hs⟩ := RootPackingBalance.TerminalLayout.exists_load_from hf hg
    _ _ (CarryLookaheadCountingPrepare.context_ne_request scratch u r q) eval
  let leafTime (a : Request k State) := A *
    ((2 * (encIntervalData a.interval).length + 2 + (2 ^ a.interval.b).size +
      (a.interval.b + 1).size + 1) ^ D + 1)
  have hlen : PolyBounded (fun a : Request k State => (encRequest a).length)
      (fun a => (encIntervalData a.interval).length) :=
    PolyBounded.self.mono (fun a => encRequest_interval_length_le a)
  have hb := hlen.mono (fun a => width_le_length a.interval)
  have hn : PolyBounded (fun a : Request k State => (encRequest a).length)
      (fun a => (2 ^ a.interval.b).size) := by simpa only [Nat.size_pow] using hb.add (.const 1)
  have hw := (hb.add (.const 1)).mono (fun _ => Nat.size_le_self _)
  have ht : PolyBounded (fun a : Request k State => (encRequest a).length)
      (fun a => c * (T a + 1) + 8 + leafTime a) :=
    (((PolyBounded.const c).mul ((PolyBounded.self.add (.const 1)).pow deg |>.add (.const 1))).add
      (.const 8)).add ((PolyBounded.const A).mul
        ((((((PolyBounded.const 2).mul hlen).add (.const 2)).add hn).add hw).add (.const 1)
          |>.pow D |>.add (.const 1)))
  obtain ⟨C, E, hclock⟩ := ht.exists_le
  refine ⟨v, src, Q, hQ, atm, C, E, ?_⟩
  intro host a hbit start time
  obtain ⟨hh, ha⟩ := he host a.interval (2 ^ a.interval.b) (a.interval.b + 1)
    ⟨a.bit, hbit⟩ a.claim
  simp only [Nat.zero_add] at hh ha
  change eval.HaltsWithin (leafTime a) _ at hh
  change eval.AcceptsWithin (leafTime a) _ ↔ _ at ha
  rw [← count_eq_sum machine a.interval] at ha
  have hstart := hs host a 0 (Nat.zero_le _) (leafTime a)
  dsimp only at hstart
  rw [CarryLookaheadCountingPrepare.ready_eq_initial] at hstart
  obtain ⟨hh', ha'⟩ := hstart hh
  have hc : 0 + c * (T a + 1) + 8 + leafTime a ≤ time := by
    simpa only [Nat.zero_add] using hclock a
  exact ⟨hh'.mono hc, ⟨fun h => ha.mp (ha'.mp (h.of_halted_stepCoins hh')),
    fun h => (ha'.mpr (ha.mpr h)).mono hc⟩⟩

end Turing.MultiTapeATM.IntervalCount
