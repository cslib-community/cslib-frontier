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
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalCount.InputWindow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import Mathlib.Algebra.Order.Ring.Basic
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

The native preparation extracts a substring of at most `2 * b + 1` symbols in linear source
time. Every selected coin string is replayed on that same short record, with a binary origin
restoring absolute input coordinates. The branch bound is linear in the original source length
plus a fixed polynomial in the remaining request encoding, including unary block width. No
`2 ^ b` coin strings are enumerated. Composition through recursive contraction remains part
of #4728.
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
  let d := IntervalData.InputWindow.decoder.decode p.1
  d.test machine (BitString.lowBits d.interval.b p.2)

private theorem predicate_encoded (machine : MultiTapePTM k Bool State)
    (d : IntervalData k State) (j : ℕ) :
    predicate machine (encInputWindow (IntervalData.InputWindow.prepare d), j) =
      decide (machine.LocalIntervalStepData d.b d.input d.J d.δ d.cIn d.wIn d.cOut d.wOut
        (BitString.lowBits d.b j)) := by
  simp only [predicate, IntervalData.InputWindow.decoder.decode_enc]
  exact IntervalData.InputWindow.test_prepare machine d _ (by
    simp [IntervalData.InputWindow.prepare])

private theorem predicate_polyTime (machine : MultiTapePTM k Bool State) :
    ComputableInPolyTime (predicate machine) (encPair encBits encNat) encBool := by
  have hd : ComputableInPolyTime
      (fun p : List Bool × ℕ => IntervalData.InputWindow.decoder.decode p.1)
      (encPair encBits encNat) (encInputWindow (k := k) (State := State)) :=
    IntervalData.InputWindow.decoder.computableInPolyTime.comp (fst encBits encNat)
  have hb := IntervalData.computableInPolyTime_b.comp (encInputWindow_interval_polyTime hd)
  have hc := bitsLow hb (snd encBits encNat)
  exact IntervalData.InputWindow.computableInPolyTime_test machine hd hc

private theorem count_eq_sum (machine : MultiTapePTM k Bool State) (d : IntervalData k State) :
    d.count machine = ∑ j ∈ Finset.range (2 ^ d.b),
      (predicate machine (encInputWindow (IntervalData.InputWindow.prepare d), j)).toNat := by
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

private def strip (a : Request k State) : Request k State :=
  { a with interval := { a.interval with input := [] } }

private noncomputable def shortSize (a : Request k State) : ℕ := (encRequest (strip a)).length

private noncomputable def localSize (a : Request k State) : ℕ :=
  shortSize a + a.interval.input.length.size + 1

omit [DecidableEq State] in
private theorem strip_deg : ComputableInDegree (strip (k := k) (State := State))
    encRequest encRequest 1 1 :=
  encRequest_mk_deg.comp
    ((IntervalData.InputWindow.stripInput_deg.comp encRequest_interval_deg).prod
      (encRequest_bit_deg.prod encRequest_claim_deg))

omit [DecidableEq State] in
private theorem request_length_eq (a : Request k State) :
    (encRequest a).length = 4 * a.interval.input.length + shortSize a := by
  simp only [encRequest_apply, encRequestFields, shortSize, strip, encIntervalData_apply,
    IntervalData.equivProd, Equiv.coe_fn_mk, length_encPair, encBits_apply, List.length_nil]
  omega

omit [DecidableEq State] in
private theorem metadata_length_le (a : Request k State) :
    (encIntervalData { a.interval with input := [] }).length ≤ shortSize a :=
  encRequest_interval_length_le (strip a)

omit [DecidableEq State] in
private theorem metadata_local_le (a : Request k State) :
    (encIntervalData { a.interval with input := [] }).length + a.interval.input.length.size + 1 ≤
      localSize a :=
  Nat.add_le_add_right (Nat.add_le_add_right (metadata_length_le a) _) _

omit [DecidableEq State] in
private theorem exists_setup : ∃ d, let T := fun a : Request k State =>
    a.interval.input.length + localSize a ^ d
    ComputableInO (fun a => IntervalData.InputWindow.prepare a.interval)
        encRequest encInputWindow T T ∧
      ComputableInO parameters encRequest CountingInput.encInput T T := by
  obtain ⟨df, hf⟩ := IntervalData.InputWindow.exists_prepare_inO (k := k) (State := State)
  obtain ⟨dp, _, hp⟩ := parameters_polyTime (k := k) (State := State) |>.exists_degree
  let d := df + dp + 1
  have hbase (a : Request k State) : 1 ≤ localSize a := by dsimp [localSize]; omega
  have hshort (a : Request k State) : shortSize a ≤ localSize a ^ d := by
    have hpow : localSize a ≤ localSize a ^ d := by
      simpa only [pow_one] using Nat.pow_le_pow_right (hbase a) (show 1 ≤ d by omega)
    exact (show shortSize a ≤ localSize a by dsimp [localSize]; omega).trans hpow
  have hprep (a : Request k State) :
      ((encIntervalData { a.interval with input := [] }).length + a.interval.input.length.size +
        1) ^ df ≤ localSize a ^ d :=
    (Nat.pow_le_pow_left (metadata_local_le a) df).trans
        (Nat.pow_le_pow_right (hbase a) (by dsimp [d]; omega))
  have hparam (a : Request k State) : (shortSize a + 1) ^ dp ≤ localSize a ^ d :=
    (Nat.pow_le_pow_left (show shortSize a + 1 ≤ localSize a by dsimp [localSize]; omega) dp).trans
      (Nat.pow_le_pow_right (hbase a) (by dsimp [d]; omega))
  refine ⟨d, ?_, ?_⟩
  · apply (hf.comp encRequest_interval_deg.inO_one).mono 6
    all_goals intro a; have hl := request_length_eq a; have hs := hshort a
    all_goals have hp := hprep a; dsimp only at hp; omega
  · have h := hp.inO.comp strip_deg.inO_one
    have h' := h.of_enc_eq (g := parameters) (encC := CountingInput.encInput) (fun _ => rfl)
    apply h'.mono 6
    all_goals intro a; have hl := request_length_eq a; have hs := hshort a
    all_goals have hp := hparam a; change _ + (shortSize a + 1) ^ dp ≤ _; omega

private theorem absorb_source_log (d : ℕ) : ∃ C, ∀ n m : ℕ,
    (m + n.size + 1) ^ d ≤ C * (n + (m + 1) ^ d + 1) := by
  obtain ⟨c, hc⟩ := exists_pow_length_encNat_le d
  refine ⟨2 ^ (d - 1) * (c + 1), fun n m => ?_⟩
  have hn : (n.size + 1) ^ d ≤ c * (n + 1) := by
    simpa only [encNat_apply, Nat.size_eq_bits_len] using hc n
  calc
    _ ≤ ((m + 1) + (n.size + 1)) ^ d := Nat.pow_le_pow_left (by omega) d
    _ ≤ 2 ^ (d - 1) * ((m + 1) ^ d + (n.size + 1) ^ d) :=
      add_pow_le (Nat.zero_le _) (Nat.zero_le _) d
    _ ≤ 2 ^ (d - 1) * ((m + 1) ^ d + c * (n + 1)) := by gcongr
    _ ≤ _ := by
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      calc
        (m + 1) ^ d + c * (n + 1) ≤
            (n + (m + 1) ^ d + 1) + c * (n + (m + 1) ^ d + 1) :=
          Nat.add_le_add (by omega) (Nat.mul_le_mul_left c (by omega))
        _ = _ := by ring

/-- One finite native machine checks every interval count bit. Its branch clock is linear in the
original source length and polynomial in the remaining request encoding. The machine extracts
its own source window and implements every leaf; all original interval records are admitted. -/
theorem exists_evaluator (machine : MultiTapePTM k Bool State) :
    ∃ (u : ℕ) (src : Fin u) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C E : ℕ),
      ∀ (host : List Bool) (a : Request k State), a.bit < a.interval.b + 1 →
        let start := SharedWordFork.start src atm host (encRequest a) 0
        let time := C * (a.interval.input.length +
          ((encRequest { a with interval := { a.interval with input := [] } }).length + 1) ^ E + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (a.interval.count machine).testBit a.bit = a.claim) := by
  obtain ⟨d, _, hp⟩ := (predicate_polyTime machine).exists_degree
  obtain ⟨scratch, u, r, q, S, hS, eval, A, D, he⟩ :=
    CarryLookaheadCountingFromParametersCost.exists_evaluator_on_context
      (encInputWindow (k := k) (State := State)) (fun _ => 0)
      (fun x => 2 * (encInputWindow x).length + 2) (predicate machine) hp.inO d
      (fun _ => by omega) (by
        intro x j
        rw [length_encPair]
        simp only [encBits_apply, encNat_apply, ← Nat.size_eq_bits_len]
        exact (Nat.pow_le_pow_left (by omega) d).trans (Nat.le_add_left _ _))
  let := hS
  obtain ⟨deg, hf, hg⟩ := exists_setup (k := k) (State := State)
  let T (a : Request k State) := a.interval.input.length + localSize a ^ deg
  obtain ⟨v, src, Q, hQ, atm, c, hs⟩ := RootPackingBalance.TerminalLayout.exists_load_from hf hg
    _ _ (CarryLookaheadCountingPrepare.context_ne_request scratch u r q) eval
  let leafTime (a : Request k State) := A *
    ((2 * (encInputWindow (IntervalData.InputWindow.prepare a.interval)).length + 2 +
      (2 ^ a.interval.b).size + (a.interval.b + 1).size + 1) ^ D + 1)
  have hmeta : PolyBounded (localSize (k := k) (State := State))
      (fun a => (encIntervalData { a.interval with input := [] }).length) :=
    PolyBounded.self.mono (fun a => (metadata_length_le a).trans (by dsimp [localSize]; omega))
  have hlen : PolyBounded (localSize (k := k) (State := State))
      (fun a => (encInputWindow (IntervalData.InputWindow.prepare a.interval)).length) :=
    ((PolyBounded.const 20).mul PolyBounded.self).mono fun a =>
      (IntervalData.InputWindow.prepare_length_le a.interval).trans
        (Nat.mul_le_mul_left _ (metadata_local_le a))
  have hb := hmeta.mono (fun a => width_le_length { a.interval with input := [] })
  have hn : PolyBounded (localSize (k := k) (State := State))
      (fun a => (2 ^ a.interval.b).size) := by simpa only [Nat.size_pow] using hb.add (.const 1)
  have hw := (hb.add (.const 1)).mono (fun _ => Nat.size_le_self _)
  let extra (a : Request k State) := c * (localSize a ^ deg + 1) + 8 + leafTime a
  have ht : PolyBounded (localSize (k := k) (State := State)) extra :=
    (((PolyBounded.const c).mul (PolyBounded.self.pow deg |>.add (.const 1))).add
      (.const 8)).add ((PolyBounded.const A).mul
        ((((((PolyBounded.const 2).mul hlen).add (.const 2)).add hn).add hw).add (.const 1)
          |>.pow D |>.add (.const 1)))
  obtain ⟨C, E, hclock⟩ := ht.exists_le_linear_add_pow (fun a => a.interval.input.length) c
    (fun a => by dsimp [localSize]; omega)
  obtain ⟨B, hlog⟩ := absorb_source_log E
  refine ⟨v, src, Q, hQ, atm, C * (B + 1), E, ?_⟩
  intro host a hbit start time
  obtain ⟨hh, ha⟩ := he host (IntervalData.InputWindow.prepare a.interval)
    (2 ^ a.interval.b) (a.interval.b + 1) ⟨a.bit, hbit⟩ a.claim
  simp only [Nat.zero_add] at hh ha
  change eval.HaltsWithin (leafTime a) _ at hh
  change eval.AcceptsWithin (leafTime a) _ ↔ _ at ha
  rw [← count_eq_sum machine a.interval] at ha
  have hstart := hs host a 0 (Nat.zero_le _) (leafTime a)
  dsimp only at hstart
  rw [CarryLookaheadCountingPrepare.ready_eq_initial] at hstart
  obtain ⟨hh', ha'⟩ := hstart hh
  have hc : 0 + c * (T a + 1) + 8 + leafTime a ≤ time := by
    have h₁ := hlog a.interval.input.length (shortSize a)
    have h₂ : a.interval.input.length + localSize a ^ E + 1 ≤
        (B + 1) * (a.interval.input.length + (shortSize a + 1) ^ E + 1) := by
      calc
        _ = (a.interval.input.length + 1) + localSize a ^ E := by omega
        _ ≤ (a.interval.input.length + (shortSize a + 1) ^ E + 1) +
            B * (a.interval.input.length + (shortSize a + 1) ^ E + 1) :=
          Nat.add_le_add (by omega) h₁
        _ = _ := by ring
    calc
      _ = c * a.interval.input.length + extra a := by dsimp [T, extra]; ring
      _ ≤ C * (a.interval.input.length + localSize a ^ E + 1) := hclock a
      _ ≤ C * ((B + 1) * (a.interval.input.length + (shortSize a + 1) ^ E + 1)) :=
        Nat.mul_le_mul_left C h₂
      _ = time := by dsimp [time, shortSize, strip]; ring
  exact ⟨hh'.mono hc, ⟨fun h => ha.mp (ha'.mp (h.of_halted_stepCoins hh')),
    fun h => (ha'.mpr (ha.mpr h)).mono hc⟩⟩

end Turing.MultiTapeATM.IntervalCount
