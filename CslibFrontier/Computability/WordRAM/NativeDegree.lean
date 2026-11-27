/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Native
public import CslibFrontier.Computability.GenericRAM.Native.Degree
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi

/-!
# Word-RAM primitives with explicit degrees

`WordRAM.Native` certifies each primitive of a word-RAM basis in polynomial time of unnamed degree.
Here the primitives get explicit degrees: on a unary word size and binary operands, the literal
check, the `eq`/`lt` tests, address extraction and the move and label checks all run in quadratic
time and space with output of linear length, and so do checked addition and truncated subtraction.
The fits test `v < 2 ^ w` compares the bit length of `v` with `w` in unary, without forming `2 ^ w`.

`Basis.nativePrimitivesOfDegree` assembles a primitive bundle of degree `d ≥ 2` from degree-`d`
certificates for the operations of a basis; `Basis.additive.quadraticPrimitives` is the instance
with `d = 2`. The other bases need degree certificates for multiplication, division,
remainder, the bitwise operations and the shifts, which the machine library does not yet supply
except for multiplication.

## Main definitions

* `Cslib.WordRAM.Basis.nativePrimitivesOfDegree`: the primitive bundle of a basis from degree-`d`
  certificates for its operations.
* `Cslib.WordRAM.Basis.additive.quadraticPrimitives`: the quadratic bundle of the additive basis.

## Main results

* `Cslib.WordRAM.fits_degree`: the fits test is quadratic.
* `Cslib.WordRAM.checkedAdd_degree`, `Cslib.WordRAM.checkedSub_degree`: checked addition and
  subtraction are quadratic.
* `Cslib.WordRAM.Basis.nativePrimitivesOfDegree_hasDegree`,
  `Cslib.WordRAM.Basis.additive.quadraticPrimitives_hasDegree`: the bundles have the stated
  degree.
-/

@[expose] public section

namespace Cslib.WordRAM

open Cslib.GenericRAM Turing.MultiTapeTM ComputableInDegree

/-- A linear-time, linear-space computation has cost and output degree one. -/
private theorem degree_of_linear {α β : Type} {ei : α ↪ List Bool} {eo : β ↪ List Bool}
    {f : α → β} (h : ComputableInO f ei eo (fun a => (ei a).length) (fun a => (ei a).length)) :
    ComputableInDegree f ei eo 1 1 :=
  h.computableInDegree ⟨1, fun a => by simp⟩ ⟨1, fun a => by simp⟩ le_rfl

/-- A computation in quadratic time and linear space has cost degree two and output degree one. -/
private theorem degree_of_quadratic {α β : Type} {ei : α ↪ List Bool} {eo : β ↪ List Bool}
    {f : α → β}
    (h : ComputableInO f ei eo (fun a => ((ei a).length + 1) ^ 2) (fun a => (ei a).length + 1)) :
    ComputableInDegree f ei eo 2 1 :=
  h.computableInDegree ⟨1, fun a => by simp⟩ ⟨1, fun a => by simp⟩ (by omega)

/-- **The fits test `v < 2 ^ w` is quadratic** on a unary width and a binary value. It compares the
bit length of `v` with `w`. -/
theorem fits_degree :
    ComputableInDegree (fun p : ℕ × ℕ => decide (Fits p.1 p.2)) (encPair encUnary encNat)
      encBool 2 1 := by
  have hsize := ((degree_of_linear (ComputableInO.lengthUnary.comp_enc encNat)).comp
    (snd encUnary encNat)).mono (d' := 1) (e' := 1)
  have hsub := (unary_sub.comp (hsize.prod (fst encUnary encNat))).mono (d' := 2) (e' := 1)
  convert ((eq encUnary).comp (hsub.prod (const 0))).mono (d' := 2) (e' := 1) using 1
  funext p
  dsimp only [Function.comp_def]
  refine decide_eq_decide.mpr ?_
  rw [fits_iff, encNat_apply, Nat.size_eq_bits_len, ← Nat.size_le]; omega

/-- Checking that a quadratic word value fits the unary width is quadratic. -/
private theorem checkFits_degree {k : ℕ} {val : ℕ × (Fin k → ℕ) → ℕ}
    (hval : ComputableInDegree val encWidthOperands encNat 2 1) :
    ComputableInDegree
      (fun p : ℕ × (Fin k → ℕ) => if decide (Fits p.1 (val p)) then some (val p) else none)
      encWidthOperands (encOption encNat) 2 1 :=
  ite_le
    ((fits_degree.comp ((fst encUnary (encPi encNat (Index := Fin k))).prod hval)).mono
      (d' := 2) (e' := 1))
    (((optionSome (enc₁ := encNat) (enc := encOption encNat)).comp hval).mono
      (d' := 2) (e' := 1))
    (const none) (by omega) (by omega)

/-- An operand register of a binary operation, read in linear time. -/
private theorem operand_degree (i : Fin 2) :
    ComputableInDegree (fun p : ℕ × (Fin 2 → ℕ) => p.2 i) encWidthOperands
      encNat 1 1 :=
  ((degree_of_linear (ComputableInO.pi_apply encNat i)).comp
    (snd encUnary (encPi encNat))).mono

/-- **Checked addition is quadratic** on a unary width and binary operands. -/
theorem checkedAdd_degree :
    ComputableInDegree (Basis.standard.genericModel.checkedOp (.bin .add))
      encWidthOperands (encOption encNat) 2 1 :=
  checkFits_degree (k := 2) (val := fun p : ℕ × (Fin 2 → ℕ) => p.2 0 + p.2 1)
    (computableInDegree_add.comp ((operand_degree 0).prod (operand_degree 1))).mono

/-- **Checked truncated subtraction is quadratic** on a unary width and binary operands. -/
theorem checkedSub_degree :
    ComputableInDegree (Basis.standard.genericModel.checkedOp (.bin .sub))
      encWidthOperands (encOption encNat) 2 1 :=
  checkFits_degree (k := 2) (val := fun p : ℕ × (Fin 2 → ℕ) => p.2 0 - p.2 1)
    ((degree_of_quadratic ComputableInO.natSub).comp
      ((operand_degree 1).prod (operand_degree 0))).mono

/-- A literal is checked against the unary width in quadratic time. -/
theorem checkedConstant_degree (B : Basis) (c : ℕ) :
    ComputableInDegree (B.genericModel.checkedConstant c) encUnary (encOption encNat) 2 1 :=
  ite_le ((fits_degree.comp ((of_eq (f := fun w : ℕ => w) (encIn := encUnary) (encMid := encUnary)
      fun _ => rfl).prod (const c))).mono (d' := 2) (e' := 1))
    (const (some c)) (const none) (by omega) (by omega)

/-- The word-RAM tests (`eq`, `lt` and the faulting test) are quadratic. -/
theorem evalTest_degree (B : Basis) (t : Option Bool) :
    ComputableInDegree (fun p => B.genericModel.evalTest p.1 t p.2)
      encWidthOperands (encOption encBool) 2 1 := by
  cases t with
  | none => exact (const (α := ℕ × (Fin 0 → ℕ)) (none : Option Bool)).mono
  | some b =>
    have hxy := (operand_degree 0).prod (operand_degree 1)
    cases b
    · exact ((optionSome (enc₁ := encBool) (enc := encOption encBool)).comp
        (ComputableInDegree.natEq.comp hxy)).mono
    · exact ((optionSome (enc₁ := encBool) (enc := encOption encBool)).comp
        ((degree_of_quadratic ComputableInO.natLt).comp hxy)).mono

/-- Word-RAM address extraction is linear. -/
theorem address_degree (B : Basis) :
    ComputableInDegree (fun p => B.genericModel.address p.1 p.2)
      (encPair encUnary encNat) (encOption encNat) 1 1 :=
  ((optionSome (enc₁ := encNat) (enc := encOption encNat)).comp (snd encUnary encNat)).mono

/-- The primitive bundle of a basis from degree-`d` certificates for its checked operations,
`d ≥ 2`; the literal, test, address, move and label primitives are quadratic. -/
noncomputable def Basis.nativePrimitivesOfDegree (B : Basis) {d : ℕ} (hd : 2 ≤ d)
    (hop : ∀ op : B.Op, ComputableInDegree (B.genericModel.checkedOp op)
      encWidthOperands (encOption encNat) d 1) :
    B.genericModel.NativePrimitives B.encoding where
  constant c := .ofDegree ((checkedConstant_degree B c).mono hd le_rfl)
  operation op := .ofDegree (hop op)
  test t := .ofDegree ((evalTest_degree B t).mono hd le_rfl)
  address := .ofDegree ((address_degree B).mono (d' := d) (by omega) le_rfl)
  validMove := .ofDegree ((const true).mono (d' := d) (e' := 1) (by omega) zero_le_one)
  validPC := .ofDegree ((const true).mono (d' := d) (e' := 1) (by omega) zero_le_one)

/-- `Basis.nativePrimitivesOfDegree` has degree `d`. -/
theorem Basis.nativePrimitivesOfDegree_hasDegree (B : Basis) {d : ℕ} (hd : 2 ≤ d)
    (hop : ∀ op : B.Op, ComputableInDegree (B.genericModel.checkedOp op)
      encWidthOperands (encOption encNat) d 1) :
    (B.nativePrimitivesOfDegree hd hop).HasDegree d :=
  ⟨fun c => NativeCertificate.ofDegree_hasDegree ((checkedConstant_degree B c).mono hd le_rfl),
    fun op => NativeCertificate.ofDegree_hasDegree (hop op),
    fun t => NativeCertificate.ofDegree_hasDegree ((evalTest_degree B t).mono hd le_rfl),
    NativeCertificate.ofDegree_hasDegree ((address_degree B).mono (d' := d) (by omega) le_rfl),
    NativeCertificate.ofDegree_hasDegree
      ((const true).mono (d' := d) (e' := 1) (by omega) zero_le_one),
    NativeCertificate.ofDegree_hasDegree
      ((const true).mono (d' := d) (e' := 1) (by omega) zero_le_one)⟩

/-- Every checked operation of the additive basis is quadratic. -/
theorem Basis.additive.checkedOp_degree (op : Basis.additive.Op) :
    ComputableInDegree (Basis.additive.genericModel.checkedOp op)
      encWidthOperands (encOption encNat) 2 1 := by
  rcases op with ⟨f, hf⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  exacts [checkedAdd_degree, checkedSub_degree]

/-- The quadratic primitive bundle of the additive basis. -/
noncomputable def Basis.additive.quadraticPrimitives :
    Basis.additive.genericModel.NativePrimitives Basis.additive.encoding :=
  Basis.nativePrimitivesOfDegree Basis.additive le_rfl Basis.additive.checkedOp_degree

/-- **Every primitive of the additive basis is quadratic.** -/
theorem Basis.additive.quadraticPrimitives_hasDegree :
    Basis.additive.quadraticPrimitives.HasDegree 2 :=
  Basis.nativePrimitivesOfDegree_hasDegree _ le_rfl Basis.additive.checkedOp_degree

end Cslib.WordRAM
