/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# A query-machine reader for one fixed-width vertex ID

This query routine reads `Nat.size N` consecutive positions from zero.
It consumes only one ID prefix, not a scan branch. Missing bits set a sticky truncation flag;
the routine still makes exactly `Nat.size N` attempted reads and then halts. Later input bits
are left unread. The returned optional binary rank agrees with `Scan.Binary.decodeVertex`
on that prefix, including rejection of truncated words and out-of-range ranks.

## Main results

* `run_eq_prefix`, `halted_iff`, `query_run`: exact prefix registers and attempted-read count.
* `prefix_value_lt`: accumulator below `2 ^ min t N.size`, even on invalid choices.
* `length_run_le`: all-clock binary-state bound, charging the retained dimension and width.
* `result_eq_decodeVertex`: agreement with the existing codec, without a second encoding.
* `native_decoder`: native space certificate for reading an already supplied ID prefix.

The state bound is `4 * (Nat.log2 N.size + 1) + 4 * N.size + 5` bits. The native certificate
also charges the simulation's input-position counter, giving space
`O(N.size + Nat.log2 input.length + 1)` for each fixed `N`. Native certificates for all five
query-machine components and the final range check are supplied. The ordinary-import client
is `CslibFrontierTests.DoubleCountingVertexReader`.

The entry certificate `init_budget` loads a supplied binary dimension and computes its width
in the same space budget.

This is original infrastructure for [#6747](https://github.com/cslib-community/cslib-frontier/issues/6747).
The input is a read-only word supplying the choices. Generating nondeterministic bits, composing
the reader into the scanner, and the first-halting native scan correspondence remain open there.
-/

public section

namespace Turing.DoubleCounting.VertexReader

open MultiTapeTM ComputableInSpace Cslib.BitString

/-- Live ID registers. No list of bits or destination vertices is retained. -/
structure State where
  /-- Number of permitted vertex IDs, retained for the final range check. -/
  limit : ℕ
  /-- Number of bits to consume, loaded as `Nat.size limit`. -/
  width : ℕ
  /-- Number of positions queried. -/
  cursor : ℕ
  /-- Most-significant-first value of the present prefix. -/
  value : ℕ
  /-- Whether a missing bit has occurred. -/
  truncated : Bool

/-- Binary dimension, width, cursor and accumulator, each framed, then the truncation flag. -/
enc_structure encState : State where
  limit : encNat, width : encNat, cursor : encNat, value : encNat, truncated : encBool

/-- Read one bit. Absent bits set the flag and leave the accumulator unchanged. -/
@[expose] def advance (s : State) (bit : Option Bool) : State :=
  ⟨s.limit, s.width, s.cursor + 1,
    if bit.isSome then 2 * s.value + (bit.getD false).toNat else s.value,
    s.truncated || !bit.isSome⟩

/-- Return the binary rank only if all bits were present and the ID is in range. -/
@[expose] def result (s : State) : Option ℕ :=
  if !s.truncated && decide (s.value < s.limit) then some s.value else none

/-- Read one ID prefix and output its optional binary rank after the fixed number of reads. -/
@[expose] def machine (N : ℕ) : QueryMachine State where
  init := ⟨N, N.size, 0, 0, false⟩
  query := State.cursor
  next := fun (s, bit) => advance s bit
  emit _ := []
  halted s := decide (s.width ≤ s.cursor)
  finish s := encOption encNat (result s)

/-- Every live state contains precisely the numeric value of the prefix already read. -/
private theorem run_prefix (N : ℕ) (w : List Bool) (t : ℕ) (ht : t ≤ N.size) :
    (machine N).run w t = ⟨N, N.size, t, binaryValue (w.take t), decide (w.length < t)⟩ := by
  induction t with
  | zero => simp [QueryMachine.run_zero, machine, binaryValue]
  | succ t ih =>
    rw [QueryMachine.run_succ, ih (by omega)]
    have hl : ¬ N.size ≤ t := by omega
    by_cases hw : t < w.length
    · have hg := List.getElem?_eq_getElem hw
      have he := List.take_succ_eq_append_getElem hw
      simp only [QueryMachine.step, QueryMachine.read, machine, hl, decide_false,
        Bool.false_eq_true,
        ite_false, advance, hg, Option.isSome_some, Option.getD_some, ite_true,
        Bool.not_true, Bool.or_false, he, binaryValue_snoc,
        show ¬w.length < t by omega, show ¬w.length < t + 1 by omega]
    · have hg : w[t]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      have he : w.take (t + 1) = w.take t := by simp [List.take_add_one, hg]
      simp [QueryMachine.step, QueryMachine.read, machine, hl, advance, hg, he,
        show w.length < t + 1 by omega]

/-- Exactly the declared width of attempted reads occurs before the first halt, even when
some of those reads return `none`. -/
theorem halted_iff (N : ℕ) (w : List Bool) (t : ℕ) :
    (machine N).halted ((machine N).run w t) = true ↔ N.size ≤ t := by
  apply QueryMachine.halted_run_iff
  · rw [run_prefix N w _ le_rfl]
    simp [machine]
  · intro t ht
    rw [run_prefix N w t (by omega)]
    simp [machine, show ¬N.size ≤ t by omega]

/-- The live query index is exactly the number of bits already attempted. -/
theorem query_run (N : ℕ) (w : List Bool) (t : ℕ) (ht : t < N.size) :
    (machine N).query ((machine N).run w t) = t := by
  rw [run_prefix N w t (by omega)]
  rfl

/-- After halting, the state remains the completed-width state. -/
theorem run_eq_prefix (N : ℕ) (w : List Bool) (t : ℕ) :
    (machine N).run w t =
      ⟨N, N.size, min t N.size, binaryValue (w.take (min t N.size)),
        decide (w.length < min t N.size)⟩ := by
  by_cases ht : t ≤ N.size
  · simpa [Nat.min_eq_left ht] using run_prefix N w t ht
  · rw [(machine N).run_eq_of_le w ((halted_iff N w N.size).mpr le_rfl) (by omega)]
    simpa [Nat.min_eq_right (by omega : N.size ≤ t)] using run_prefix N w N.size le_rfl

/-- Even an invalid rank uses only as many numeric bits as have been read. -/
theorem prefix_value_lt (N : ℕ) (w : List Bool) (t : ℕ) :
    ((machine N).run w t).value < 2 ^ min t N.size := by
  rw [run_eq_prefix]
  exact (binaryValue_lt_two_pow _).trans_le
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

/-- Every query-machine state has a bounded binary encoding, including truncated and
out-of-range branches and clocks after halting. -/
theorem length_run_le (N : ℕ) (w : List Bool) (t : ℕ) :
    (encState ((machine N).run w t)).length ≤
      4 * (Nat.log2 N.size + 1) + 4 * N.size + 5 := by
  have hc : ((machine N).run w t).cursor ≤ N.size := by
    rw [run_eq_prefix]
    exact Nat.min_le_right _ _
  have hv : ((machine N).run w t).value < 2 ^ N.size :=
    (prefix_value_lt N w t).trans_le (Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _))
  have hcursor := length_encNat_le_log2 hc
  have hvalue := length_encNat_le_of_lt_two_pow hv
  have hlimit : ((machine N).run w t).limit = N := by rw [run_eq_prefix]
  have hwidth : ((machine N).run w t).width = N.size := by rw [run_eq_prefix]
  have hwsize := length_encNat_le_log2 (le_refl N.size)
  have hnsize : (encNat N).length = N.size := by rw [encNat_apply, Nat.size_eq_bits_len]
  simp only [encState_apply, encStateFields, length_encPair, encBool_apply,
    List.length_singleton, hlimit, hwidth, hnsize]
  omega

/-- Exact agreement with the existing codec on the consumed prefix. -/
theorem result_eq_decodeVertex (N : ℕ) (w : List Bool) :
    result ((machine N).run w N.size) =
      (Cslib.DoubleCounting.Scan.Binary.decodeVertex (N := N) (w.take N.size)).map Fin.val := by
  rw [run_prefix N w N.size le_rfl]
  unfold result Cslib.DoubleCounting.Scan.Binary.decodeVertex
  by_cases hw : N.size ≤ w.length
  · have hl : (w.take N.size).length = N.size := by simp [List.length_take, Nat.min_eq_left hw]
    simp [show ¬w.length < N.size by omega, hl]
  · have hl : (w.take N.size).length ≠ N.size := by simp [List.length_take]; omega
    simp [show w.length < N.size by omega]

/-- Initialize the vertex reader from a binary dimension computed within the input budget. -/
theorem init_budget {α : Type} {encIn : α ↪ List Bool} {budget : α → ℕ}
    {dimension : α → ℕ} (hdim : ComputableInSpace dimension encIn encNat budget) :
    ComputableInSpace (fun a => (machine (dimension a)).init) encIn encState budget :=
  encState_mk_budget hdim (budget_comp_linear natSize hdim)
    ((constZero 0).mono_le fun _ => Nat.zero_le _)
    ((constZero 0).mono_le fun _ => Nat.zero_le _)
    ((constZero false).mono_le fun _ => Nat.zero_le _)

/-- The actual input query is a native binary-register projection. -/
theorem query_inSpace (N : ℕ) :
    ComputableInSpace (machine N).query encState encNat (fun s => (encState s).length) :=
  encState_cursor_budget (of_inO (ComputableInO.of_eq fun _ => rfl))

/-- The halt comparison uses the retained width, with no dimension-dependent constant. -/
theorem halted_inSpace (N : ℕ) :
    ComputableInSpace (machine N).halted encState encBool (fun s => (encState s).length) := by
  have hid := of_inO (ComputableInO.of_eq (encIn := encState) (encMid := encState) fun _ => rfl)
  exact (budget_finite (encC := encBool) Bool.not
    (budget_natLt (encState_cursor_budget hid) (encState_width_budget hid))).of_enc_eq
      fun s => by
        by_cases h : s.cursor < s.width
        · simp [machine, h, show ¬s.width ≤ s.cursor by omega]
        · simp [machine, h, show s.width ≤ s.cursor by omega]

/-- Native transition computation uses only binary addition and finite option/flag operations. -/
theorem next_inSpace (N : ℕ) :
    ComputableInSpace (machine N).next (QueryMachine.encStateRead encState) encState
      (fun p => (QueryMachine.encStateRead encState p).length) := by
  have hs := fst encState (encOption encBool)
  have hb := snd encState (encOption encBool)
  have hc := encState_cursor_budget hs
  have hv := encState_value_budget hs
  have hf := encState_truncated_budget hs
  have hsome := budget_optionIsSome hb
  have hval := budget_ite hsome
    (budget_natAdd (budget_natAdd hv hv)
      (budget_finite (encC := encNat) Bool.toNat (budget_optionGetD false hb))) hv
  have hflag := budget_finite (encC := encBool)
    (fun ((f, present) : Bool × Bool) => f || !present) (budget_prod hf hsome)
  exact (encState_mk_budget (encState_limit_budget hs) (encState_width_budget hs)
    (budget_natSucc hc) hval hflag).of_enc_eq
    fun p => by simp [machine, advance, two_mul]

/-- The rank check and optional binary result are native scalar operations. -/
theorem result_inSpace :
    ComputableInSpace result encState (encOption encNat) (fun s => (encState s).length) := by
  have hv := encState_value_budget (of_inO (ComputableInO.of_eq fun _ => rfl))
  have hf := encState_truncated_budget (of_inO (ComputableInO.of_eq fun _ => rfl))
  have hlt := budget_natLt hv
    (encState_limit_budget (of_inO (ComputableInO.of_eq fun _ => rfl)))
  have hok := budget_finite (encC := encBool)
    (fun ((failed, lt) : Bool × Bool) => !failed && lt) (budget_prod hf hlt)
  exact budget_ite hok (budget_optionSome hv) (budget_const none (.refl _))

/-- No intermediate output is materialized. -/
theorem emit_inSpace (N : ℕ) :
    ComputableInSpace (machine N).emit (QueryMachine.encStateRead encState) encBits
      (fun p => (QueryMachine.encStateRead encState p).length) := budget_const [] (.refl _)

/-- Native finalization encodes the range-checked optional rank. -/
theorem finish_inSpace (N : ℕ) :
    ComputableInSpace (machine N).finish encState encBits
      (fun s => (encState s).length) := result_inSpace.of_enc_eq fun _ => rfl

/-- Only the final optional rank is emitted. -/
theorem output_eq (N : ℕ) (w : List Bool) (t : ℕ) :
    (machine N).output w t = encOption encNat (result ((machine N).run w t)) := by
  simp [QueryMachine.output, machine]

/-- For each fixed dimension, the existing query-machine simulation certifies actual native
reading and decoding of one ID prefix. The bound also charges the input-position machinery. -/
theorem native_decoder (N : ℕ) :
    ∃ time c, ComputableInTimeAndSpace
      (fun w : List Bool =>
        (Cslib.DoubleCounting.Scan.Binary.decodeVertex (N := N) (w.take N.size)).map Fin.val)
      encBits (encOption encNat) time
      (fun w => c * (N.size + Nat.log2 w.length + 1)) := by
  apply (machine N).computableInSpace (query_inSpace N) (next_inSpace N)
    (emit_inSpace N) (halted_inSpace N) (finish_inSpace N) (fun _ => N.size)
  · intro w
    exact (halted_iff N w N.size).mpr le_rfl
  · intro w t ht
    have h := (halted_iff N w t).not
    simpa using h.mpr (by omega : ¬N.size ≤ t)
  · intro w
    rw [output_eq, result_eq_decodeVertex]
    simp only [encBits_apply]
  · intro w
    simp only [encBits_apply]
    omega
  · refine ⟨13, fun w t _ => ?_⟩
    simp only [encBits_apply]
    have h := length_run_le N w t
    have hw : Nat.log2 N.size ≤ N.size := Nat.log2_le_self _
    omega

end Turing.DoubleCounting.VertexReader
