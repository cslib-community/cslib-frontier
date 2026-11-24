/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import Mathlib.Data.Nat.Bitwise
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import Mathlib.Data.List.GetD

/-!
# Binary digit access and fixed-width words in native space

A bit of a binary natural is obtained by iterating the tail of its binary encoding and reading
its head, with a missing bit read as false. Every intermediate word is a suffix of the input
word. The iteration count is binary, so digit access only charges the length of the count.
The fixed-width word loop adds one digit per step and also charges the requested output width.

This proof was extracted unchanged from Christian Reitwiessner's tree-evaluation reader so that
numeric algorithms can reuse it without depending on tree evaluation.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.natTestBit`: binary digit access in work space
  linear in the binary encodings of both the value and the index.
* `Turing.MultiTapeTM.ComputableInSpace.lowBits_inSpace`: a fixed-width word in space linear in the
  width and the encoded input.

## References

* [N. Immerman, *Descriptive Complexity*, proof of Theorem 3.1][Immerman1999].
-/

public section

namespace Turing.MultiTapeTM

namespace ComputableInSpace

/-- **A bit of a binary natural**, `k.testBit j` from `(k, j)`. -/
theorem natTestBit :
    ComputableInSpace (fun q : ℕ × ℕ => q.1.testBit q.2) (encPair encNat encNat) encBool
      fun q => 32 * ((encPair encNat encNat q).length + 1) := by
  have hl : (fun q => (encPair encNat encNat q).length) ≼
      fun q => 8 * ((encPair encNat encNat q).length + 1) := .of_le fun _ => by omega
  have hbits : ComputableInSpace (fun q : ℕ × ℕ => q.1.bits) (encPair encNat encNat) encBits
      fun q => 8 * ((encPair encNat encNat q).length + 1) :=
    ((fst encNat encNat).weaken hl).of_enc_eq fun _ => rfl
  have htail : ComputableInSpace List.tail encBits encBits fun l => (encBits l).length :=
    of_inO (.of_linear (ListEncoding.tail encBool))
  have hlen (q : ℕ × ℕ) (i : ℕ) :
      (encBits (List.tail^[i] q.1.bits)).length ≤ (encNat q.1).length := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      simp only [encBits_apply, List.length_tail] at ih ⊢
      omega
  have h := iterate (n := fun q : ℕ × ℕ => q.2) ((snd encNat encNat).weaken hl) hbits htail
    (Q := fun q => (encNat q.1).length) (B := fun q => (encNat q.1).length)
    (fun q k _ => hlen q k) (fun q k _ => hlen q k)
  have hhead : ComputableInSpace (fun l : List Bool => l.headD false) encBits encBool
      fun l => (encBits l).length :=
    of_inO (.of_linear (ListEncoding.headD false))
  refine (budget_comp_linear hhead h).mono_le (fun q => ?_) |>.of_enc_eq fun q => ?_
  · simp only [length_encPair]; omega
  · rw [List.tail_iterate, Nat.testBit_eq_inth]
    congr 1
    rw [List.headD_eq_head?_getD, List.head?_drop, List.getI_eq_getElem?_getD]
    rfl

private structure LowBitsState where
  value : ℕ
  cursor : ℕ
  output : List Bool

private enc_structure encLowBitsState : LowBitsState where
  value : encNat, cursor : encNat, output : (encList encBool)

private def lowBitsStep (s : LowBitsState) : LowBitsState :=
  ⟨s.value, s.cursor + 1, s.output ++ [s.value.testBit s.cursor]⟩

private theorem iterate_lowBitsStep (value t : ℕ) :
    lowBitsStep^[t] ⟨value, 0, []⟩ = ⟨value, t, Cslib.BitString.lowBits t value⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [lowBitsStep, Cslib.BitString.lowBits, List.range_succ, List.map_append,
      List.map_singleton]

private theorem lowBitsStep_inSpace :
    ComputableInSpace lowBitsStep encLowBitsState encLowBitsState
      (fun s => (encLowBitsState s).length) := by
  have h := budget_id (BigOLe.refl fun s => (encLowBitsState s).length)
  have hv := encLowBitsState_value_budget h
  have hc := encLowBitsState_cursor_budget h
  have ho := encLowBitsState_output_budget h
  have hbit := budget_comp_lin natTestBit (linear_mul 32) (budget_prod hv hc)
  exact encLowBitsState_mk_budget hv (budget_natSucc hc) (budget_snoc ho hbit)

/-- Write the requested number of little-endian digits. The full live state is linear in
the requested width and the binary input length, including zero padding. -/
theorem lowBits_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ => Cslib.BitString.lowBits p.1 p.2)
      (encPair encNat encNat) (encList encBool)
      (fun p => p.1 + (encPair encNat encNat p).length) := by
  let B (p : ℕ × ℕ) := p.1 + (encPair encNat encNat p).length
  have hin : (fun p : ℕ × ℕ => (encPair encNat encNat p).length) ≼ B :=
    .of_le fun _ => by dsimp only [B]; omega
  have hwidth := (fst encNat encNat).weaken hin
  have hvalue := (snd encNat encNat).weaken hin
  have hinit := encLowBitsState_mk_budget hvalue (budget_const (encB := encNat) 0)
    (budget_const (encB := encList encBool) [])
  let : Inhabited LowBitsState := ⟨⟨0, 0, []⟩⟩
  have hstate (p : ℕ × ℕ) (i : ℕ) (hi : i ≤ p.1) :
      (encLowBitsState (lowBitsStep^[i] ⟨p.2, 0, []⟩)).length ≤ 8 * B p := by
    rw [iterate_lowBitsStep]
    have hcursor := length_encNat_le_self i
    have hout : (encList encBool (Cslib.BitString.lowBits i p.2)).length = 3 * i := by
      simp [length_encList, encBool_apply, Nat.mul_comm]
    change
      (encPair encNat (encPair encNat (encList encBool))
        (p.2, i, Cslib.BitString.lowBits i p.2)).length ≤ 8 * B p
    simp only [B, length_encPair, hout]
    omega
  have h := budget_iterate hwidth hinit lowBitsStep_inSpace hstate
    (.of_le_linear 8 0 fun _ => le_rfl)
  exact (encLowBitsState_output_budget h).of_enc_eq fun p => by rw [iterate_lowBitsStep]

end ComputableInSpace

end Turing.MultiTapeTM
