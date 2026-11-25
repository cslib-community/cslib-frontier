/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Decode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OPrimitives

/-!
# Decoding finite configurations within quadratic time

The decoders of `CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.Decode`
run within quadratic time. The cells of a stack tape are read by a finite transducer in linear
time, and folded into the tape by `Turing.MultiTapeTM.stackStep`, each step taking time linear in
the encoded state, which grows by at most four bits per step; the other fields are read off the
frames of the encoding in linear time, and clamping a count into range is quadratic.

## Main results

* `Turing.MultiTapeTM.ComputableInO.decodeStackTape`, `.decodeBiTape`, `.decodeTapes`: decoding
  tapes within quadratic time and linear space.
* `Turing.MultiTapeTM.ComputableInO.decodeFiniteCfg`: decoding a finite configuration within
  quadratic time and space.
* `Turing.MultiTapeTM.ComputableInO.length_encFiniteCfg_decodeFiniteCfg_le`: a decoded
  configuration is encoded by a word of linear length.
* `Turing.MultiTapeTM.ComputableInO.decodeView`: reading the view of a code
  (`Turing.MultiTapeNTM.decodeView`) within quadratic time and space.
-/

public section

namespace Turing.MultiTapeTM.ComputableInO

open Cslib.Turing

/-- Dropping `n` frames does not lengthen a word. -/
private theorem length_dropFrame_iterate_le (n : ℕ) (w : List Bool) :
    (dropFrame^[n] w).length ≤ w.length := by
  induction n generalizing w with
  | zero => exact le_rfl
  | succ n ih => exact (ih _).trans (length_dropFrame_le w)

/-- Dropping a fixed number of frames is linear. -/
private theorem dropFrame_iterate (n : ℕ) :
    ComputableInO (dropFrame^[n]) encBits encBits (fun w => (encBits w).length)
      fun w => (encBits w).length := by
  induction n with
  | zero => exact id'
  | succ n ih => rw [Function.iterate_succ']; exact dropFrame' ih

/-- A quadratic-time, linear-space computation after a linear computation that does not lengthen
its input. -/
private theorem comp_shrink {β : Type} {enc : β ↪ List Bool} {f : List Bool → β}
    {g : List Bool → List Bool}
    (hf : ComputableInO f encBits enc (fun w => (w.length + 1) ^ 2) fun w => w.length)
    (hg : ComputableInO g encBits encBits (fun w => (encBits w).length)
      fun w => (encBits w).length)
    (hle : ∀ w, (g w).length ≤ w.length) :
    ComputableInO (fun w => f (g w)) encBits enc (fun w => (w.length + 1) ^ 2)
      fun w => w.length :=
  (hf.comp hg).mono 2 (fun w => by
      have h := Nat.pow_le_pow_left (Nat.succ_le_succ (hle w)) 2
      simp only [encBits_apply] at *; nlinarith)
    fun w => by
      have := hle w
      simp only [encBits_apply]; omega

/-- The minimum of two linear unary counts, within quadratic time and space. -/
private theorem unaryMin {a b : List Bool → ℕ}
    (ha : ComputableInO a encBits encUnary (fun w => (encBits w).length)
      fun w => (encBits w).length)
    (hb : ComputableInO b encBits encUnary (fun w => (encBits w).length)
      fun w => (encBits w).length) :
    ComputableInO (fun w => min (a w) (b w)) encBits encUnary (fun w => (w.length + 1) ^ 2)
      fun w => (w.length + 1) ^ 2 := by
  obtain ⟨c, hc⟩ := (ha.prod hb).length_le
  refine (ComputableInDegree.unary_min.inO.comp (ha.prod hb)).mono ((2 * c + 1) ^ 2 + 2)
    (fun w => ?_) fun w => ?_ <;>
  · have h := hc w
    simp only [encBits_apply] at h ⊢
    have := Nat.pow_le_pow_left (show (encPair encUnary encUnary (a w, b w)).length + 1 ≤
      (2 * c + 1) * (w.length + 1) by nlinarith) 2
    rw [mul_pow] at this; nlinarith

/-! ### Stack tapes -/

/-- The fold over the cells lengthens its encoded state by at most four bits per bit read. -/
private theorem length_foldl_stackStep_le (bits : List Bool)
    (state : Option Bool × StackTape Bool) :
    (encPair (encOption encBool) (encStackTape encBool) (bits.foldl stackStep state)).length ≤
      (encPair (encOption encBool) (encStackTape encBool) state).length + 4 * bits.length := by
  induction bits generalizing state with
  | nil => simp
  | cons bit bits ih =>
    rw [List.foldl_cons, List.length_cons]
    have := length_stackStep_le state bit
    have := ih (stackStep state bit)
    omega

/-- Emitting the bits of the framed cells, reversed, is linear. -/
private theorem cellsReversed : ComputableInO
    (fun w => (cellsTransducer.run cellsTransducer.q₀ w).reverse) encBits encBits
    (fun w => (encBits w).length) fun w => (encBits w).length :=
  (of_linear ComputableInDegree.bitsReverse).comp_linear
    (of_linear (ComputableInDegree.of_transducer (f := cellsTransducer.run cellsTransducer.q₀)
      (encIn := encBits) (encMid := encBits) cellsTransducer fun _ => rfl))

private theorem stackStep_eq (cell : Option Bool) (tape : StackTape Bool) (bit : Bool) :
    stackStep (cell, tape) bit = if cell.isSome then
      (none, StackTape.cons (if bit then cell else none) tape) else (some bit, tape) := by
  rcases cell with _ | _ <;> rcases bit with _ | _ <;> rfl

/-- A step of the stack-tape fold is linear: it branches on its finite part. -/
private theorem stackStepO : ComputableInO
    (fun p : (Option Bool × StackTape Bool) × Bool => stackStep p.1 p.2)
    (encPair (encPair (encOption encBool) (encStackTape encBool)) encBool)
    (encPair (encOption encBool) (encStackTape encBool))
    (fun p => (encPair (encPair (encOption encBool) (encStackTape encBool)) encBool p).length)
    fun p => (encPair (encPair (encOption encBool) (encStackTape encBool)) encBool p).length := by
  have hid := id' (encMid := encPair (encPair (encOption encBool) (encStackTape encBool)) encBool)
  have hcell := fst' (fst' hid)
  have htape := snd' (fst' hid)
  have hbit := snd' hid
  have hlist : ComputableInO (fun p : (Option Bool × StackTape Bool) × Bool => p.1.2.toList)
      (encPair (encPair (encOption encBool) (encStackTape encBool)) encBool)
      (encList (encOption encBool)) _ _ := htape.of_enc_eq fun _ => rfl
  have hnew := hbit.ite hcell (const none)
  have hcons := cons'.comp_linear (hnew.prod hlist)
  have hstack := ((hnew.optionIsSome.or' (isEmpty' hlist).not').ite hcons (const [])).of_enc_eq
    (encC := encStackTape encBool)
    (g := fun p : (Option Bool × StackTape Bool) × Bool =>
      StackTape.cons (if p.2 then p.1.1 else none) p.1.2)
    fun p => by simp only [encStackTape_apply, StackTape.cons_toList]; rfl
  have h := (hcell.optionIsSome.ite ((const none).prod hstack)
    ((some'.comp_linear hbit).prod htape)).of_enc_eq
    (g := fun p : (Option Bool × StackTape Bool) × Bool => stackStep p.1 p.2)
    fun ⟨⟨cell, tape⟩, bit⟩ => by rw [stackStep_eq]; rfl
  refine h.mono 12 (fun p => ?_) fun p => ?_ <;>
  · have : (encList (encOption encBool) p.1.2.toList).length ≤
        (encPair (encPair (encOption encBool) (encStackTape encBool)) encBool p).length := by
      rcases p with ⟨⟨c, t⟩, b⟩
      simp only [length_encPair, encStackTape_apply]
      omega
    split_ifs <;> omega

/-- **Decoding a stack tape within quadratic time and linear space.** -/
theorem decodeStackTape : ComputableInO MultiTapeTM.decodeStackTape encBits
    (encStackTape encBool) (fun w => (w.length + 1) ^ 2) fun w => w.length := by
  obtain ⟨c, hc⟩ := cellsReversed.length_le
  set L := (encPair (encOption encBool) (encStackTape encBool) (none, .nil)).length with hL
  have hlen (w : List Bool) :
      (cellsTransducer.run cellsTransducer.q₀ w).reverse.length ≤ c * (w.length + 1) := by
    simpa only [encBits_apply] using hc w
  have hstate (w : List Bool) (i : ℕ) : (encPair (encOption encBool) (encStackTape encBool)
      (((cellsTransducer.run cellsTransducer.q₀ w).reverse.take i).foldl stackStep
        (none, .nil))).length ≤ L + 4 * (c * (w.length + 1)) := by
    have := length_foldl_stackStep_le
      ((cellsTransducer.run cellsTransducer.q₀ w).reverse.take i) (none, .nil)
    have := List.length_take_le' i (cellsTransducer.run cellsTransducer.q₀ w).reverse
    have := hlen w
    omega
  have hfold := foldl (encA := encBool) (encL := encBits) cellsReversed
    (const (none, StackTape.nil)) stackStepO
    (R := fun w => 2 * (L + 4 * (c * (w.length + 1))) + 3)
    (Q := fun w => 2 * (L + 4 * (c * (w.length + 1))) + 3)
    (B := fun w => L + 4 * (c * (w.length + 1)))
    (fun w i _ => by
      have := hstate w i
      simp only [length_encPair, encBool_apply, List.length_singleton] at this ⊢; omega)
    (fun w i _ => by
      have := hstate w i
      simp only [length_encPair, encBool_apply, List.length_singleton] at this ⊢; omega)
    (fun w i _ => hstate w i)
  refine (snd' hfold).mono ((c + 1) * (3 * L + 3 + 13 * c) + 2) (fun w => ?_) fun w => ?_
  · have hm := hlen w
    simp only [encBits_apply]
    have := Nat.mul_le_mul
      (show (cellsTransducer.run cellsTransducer.q₀ w).reverse.length + 1 ≤
        (c + 1) * (w.length + 1) by nlinarith)
      (show 2 * (L + 4 * (c * (w.length + 1))) + 3 + (L + 4 * (c * (w.length + 1))) +
        (cellsTransducer.run cellsTransducer.q₀ w).reverse.length ≤
        (3 * L + 3 + 13 * c) * (w.length + 1) by nlinarith)
    nlinarith
  · have hm := hlen w
    simp only [encBits_apply]; nlinarith

/-- Decoding a cell is linear. -/
private theorem decodeCellO : ComputableInO MultiTapeTM.decodeCell encBits (encOption encBool)
    (fun w => (encBits w).length) fun w => (encBits w).length := by
  have hc := (ComputableInDegree.isEmpty (enc₁ := encBool) (enc := encBits)).inO_one
  have hg := (ComputableInDegree.optionSome (enc₁ := encBool)
    (enc := encOption encBool)).inO_one.comp_linear
    ((ComputableInDegree.headD (enc₁ := encBool) (enc := encBits) false).inO_one.comp_linear
      (ComputableInDegree.tail (enc₁ := encBool) (enc := encBits)).inO_one)
  unfold Turing.MultiTapeTM.decodeCell
  exact (hc.ite (const none) hg).mono 2 (fun _ => by split_ifs <;> omega)
    fun _ => by split_ifs <;> omega

/-- **Decoding a two-sided tape within quadratic time and linear space.** -/
theorem decodeBiTape : ComputableInO MultiTapeTM.decodeBiTape encBits (encBiTape encBool)
    (fun w => (w.length + 1) ^ 2) fun w => w.length := by
  have hcell : ComputableInO (fun w => MultiTapeTM.decodeCell (unframe w)) encBits
      (encOption encBool) (fun w => (w.length + 1) ^ 2) fun w => w.length :=
    (decodeCellO.comp_linear (unframe' id')).mono_le
      (fun w => by simp only [encBits_apply]; nlinarith)
      fun w => by simp only [encBits_apply, le_refl]
  have hleft := comp_shrink decodeStackTape (unframe' (dropFrame' id'))
    fun w => (length_unframe_le _).trans (length_dropFrame_le _)
  have hright := comp_shrink decodeStackTape (dropFrame' (dropFrame' id'))
    fun w => (length_dropFrame_le _).trans (length_dropFrame_le _)
  exact ((hcell.prod (hleft.prod hright)).of_enc_eq (encC := encBiTape encBool)
    (g := MultiTapeTM.decodeBiTape) fun _ => rfl).mono 3 (fun _ => by nlinarith)
    fun _ => by omega

/-- **Decoding a fixed finite family of tapes within quadratic time and linear space.** -/
theorem decodeTapes (k : ℕ) : ComputableInO (MultiTapeTM.decodeTapes k) encBits
    (encPi (encBiTape encBool)) (fun w => (w.length + 1) ^ 2) fun w => w.length := by
  have h := pi (Index := Fin k) (values := MultiTapeTM.decodeTapes k) fun i =>
    comp_shrink (f := MultiTapeTM.decodeBiTape)
      (g := fun w => unframe (dropFrame^[(Fintype.equivFin (Fin k) i).val] w)) decodeBiTape
      (unframe' (dropFrame_iterate _))
      fun w => (length_unframe_le _).trans (length_dropFrame_iterate_le _ w)
  refine h.mono (k + 1) (fun w => ?_) fun w => ?_ <;>
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, encBits_apply]
    nlinarith

/-! ### Configurations -/

variable {k : ℕ} {State : Type} [Finite State]

/-- **Decoding a finite configuration within quadratic time and space.** -/
theorem decodeFiniteCfg :
    ComputableInO (MultiTapeTM.decodeFiniteCfg (k := k) (State := State)) encBits encFiniteCfg
      (fun w => (w.length + 1) ^ 2) fun w => (w.length + 1) ^ 2 := by
  have hstate := (unaryMin (bitsLengthUnary' (unframe' (dropFrame' id')))
    (const (Nat.card (Option State) - 1))).of_enc_eq (encC := encFinite (Option State))
    (g := fun w => decodeState (State := State) (unframe (dropFrame w)).length)
    fun _ => encFinite_decodeState _
  have hpos := unaryMin (bitsLengthUnary' (unframe' (dropFrame' (dropFrame' id'))))
    (unarySucc'.comp_linear (bitsLengthUnary' (unframe' id')))
  have htapes := comp_shrink (decodeTapes k) (unframe' (dropFrame' (dropFrame' (dropFrame' id'))))
    fun w => (length_unframe_le _).trans (length_dropFrame_iterate_le 3 w)
  have hout := dropFrame' (dropFrame' (dropFrame' (dropFrame' id')))
  exact (((unframe' id').prod (hstate.prod (hpos.prod (htapes.prod hout)))).of_enc_eq
    (encC := encFiniteCfg) (g := MultiTapeTM.decodeFiniteCfg) fun _ => rfl).mono 5
    (fun _ => by simp only [encBits_apply]; nlinarith)
    fun _ => by simp only [encBits_apply]; nlinarith

/-- **A decoded configuration has a linear encoding.** -/
theorem length_encFiniteCfg_decodeFiniteCfg_le : ∃ c, ∀ w : List Bool,
    (encFiniteCfg (MultiTapeTM.decodeFiniteCfg (k := k) (State := State) w)).length ≤
      c * (w.length + 1) := by
  obtain ⟨c, hc⟩ := (decodeTapes k).length_le
  refine ⟨2 * c + 2 * Nat.card (Option State) + 12, fun w => ?_⟩
  have h1 := length_unframe_le w
  have h2 := hc (unframe (dropFrame (dropFrame (dropFrame w))))
  have h3 : (unframe (dropFrame (dropFrame (dropFrame w)))).length ≤ w.length :=
    (length_unframe_le _).trans (length_dropFrame_iterate_le 3 w)
  have h4 : (dropFrame (dropFrame (dropFrame (dropFrame w)))).length ≤ w.length :=
    length_dropFrame_iterate_le 4 w
  have h5 := Nat.min_le_right (unframe (dropFrame w)).length (Nat.card (Option State) - 1)
  have h6 := Nat.min_le_right (unframe (dropFrame (dropFrame w))).length
    ((unframe w).length + 1)
  have h7 := Nat.mul_le_mul_left c (Nat.add_le_add_right h3 1)
  have h8 := Nat.sub_le (Nat.card (Option State)) 1
  simp only [encFiniteCfg_apply, length_encPair, encBits_apply, encUnary_apply,
    List.length_replicate, MultiTapeTM.decodeFiniteCfg, encFinite_decodeState] at h2 ⊢
  nlinarith

private theorem length_unframe_tail_le (code : List Bool) :
    (unframe code.tail).length ≤ code.length :=
  (length_unframe_le _).trans (by simp only [List.length_tail]; omega)

/-- **Reading the view of a code within quadratic time and space.** -/
theorem decodeView : ComputableInO (MultiTapeNTM.decodeView (k := k) (State := State)) encBits
    (encOption encFiniteCfg) (fun code => (code.length + 1) ^ 2)
    fun code => (code.length + 1) ^ 2 := by
  have hc := (ComputableInDegree.headD (enc₁ := encBool) (enc := encBits) true).inO_one
  have htail := (ComputableInDegree.tail (enc₁ := encBool) (enc := encBits)).inO_one
  have hcfg : ComputableInO
      (fun code => MultiTapeTM.decodeFiniteCfg (k := k) (State := State) (unframe code.tail))
      encBits encFiniteCfg (fun code => (code.length + 1) ^ 2)
      fun code => (code.length + 1) ^ 2 :=
    ((decodeFiniteCfg (k := k) (State := State)).comp (unframe' htail)).mono 2
      (fun code => by
        have := Nat.pow_le_pow_left (Nat.add_le_add_right (length_unframe_tail_le code) 1) 2
        simp only [encBits_apply] at *; nlinarith)
      fun code => by
        have := Nat.pow_le_pow_left (Nat.add_le_add_right (length_unframe_tail_le code) 1) 2
        simp only [encBits_apply] at *; nlinarith
  refine ((hc.ite (const none) (some'.comp_linear hcfg)).mono 3
    (fun _ => by simp only [encBits_apply]; split_ifs <;> nlinarith)
    fun _ => by simp only [encBits_apply]; split_ifs <;> nlinarith).of_enc_eq
    fun code => by rw [MultiTapeNTM.decodeView_eq]; rfl

/-- **The view read from a code has a linear encoding.** -/
theorem length_encOption_decodeView_le : ∃ c, ∀ code : List Bool,
    (encOption encFiniteCfg (MultiTapeNTM.decodeView (k := k) (State := State) code)).length ≤
      c * (code.length + 1) := by
  obtain ⟨c, hc⟩ := length_encFiniteCfg_decodeFiniteCfg_le (k := k) (State := State)
  refine ⟨c + 1, fun code => ?_⟩
  rw [MultiTapeNTM.decodeView_eq]
  split_ifs
  · simp
  · have h := hc (unframe code.tail)
    have hle := Nat.mul_le_mul_left c (Nat.add_le_add_right (length_unframe_tail_le code) 1)
    simp only [encOption_some, List.length_cons]; nlinarith

end Turing.MultiTapeTM.ComputableInO
