/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryFieldArithmetic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.ZipFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Linear workspace for table-free binary-polynomial operations

This is a scalar kernel for the generator, not its native logspace certificate (#6747).
`fieldMulMod_inSpace` concerns the existing total evaluator, including padding and truncation,
with no irreducibility or nonempty-word assumptions. Coefficients are little-endian Boolean
lists. Each bit uses the existing framed-list encoding; its length is three times the word
length. The modulus and operands are retained while the multiplication fold executes. Remainder uses
the same fold and native step, initialized with the coefficient word for one instead of an
operand. The fold rule charges the callee as well as both live coefficient words at every prefix.

This is an original resource analysis of the existing executable algorithm. Modulus search,
binary dimension processing, Horner composition and seed-tape queries remain under #6747.

## Main results

* `Turing.BinaryField.fieldMulMod_inSpace`: native linear workspace for the supplied modulus
  and two coefficient words, including their normalization.
* `Turing.BinaryField.xor_inSpace`: coefficient-wise XOR in linear workspace.
* `Turing.BinaryField.modBits_inSpace`: native linear workspace for the existing total
  supplied-modulus remainder scan.
-/

public section
namespace Turing.BinaryField

open MultiTapeTM MultiTapeTM.ComputableInSpace
open Cslib Cslib.BinaryField

/-- Framed little-endian coefficient bits, three encoded symbols per coefficient. -/
abbrev encCoefficients := encList encBool

/-- Inputs to the supplied-modulus multiplication kernel. -/
structure MulInput where
  /-- Little-endian modulus coefficients. -/
  modulus : List Bool
  /-- Left coefficient word, padded or truncated by the evaluator. -/
  left : List Bool
  /-- Right coefficient word, padded or truncated by the evaluator. -/
  right : List Bool

/-- Modulus, left operand and right operand in order; each is a framed Boolean list and
all record fields except the last are framed again by `enc_structure`. -/
enc_structure encMulInput : MulInput where
  modulus : encCoefficients, left : encCoefficients, right : encCoefficients

private theorem coefficients_length (a : List Bool) :
    (encCoefficients a).length = 3 * a.length := by
  simp [encCoefficients, length_encList, encBool_apply, Nat.mul_comm]

private theorem zipFold_length (f : Bool → Option Bool → Option Bool) (p : Bool)
    (a b : List Bool) :
    (MultiTapeTM.zipFold (fun (_ : Bool) => f) p a b).length ≤ a.length := by
  induction a generalizing b with
  | nil => simp [MultiTapeTM.zipFold]
  | cons bit a ih =>
    have := ih b.tail
    cases h : f bit b.head? <;> simp [MultiTapeTM.zipFold, h] <;> omega

private theorem zip_inSpace (f : Bool → Option Bool → Option Bool) :
    ComputableInSpace (fun p : List Bool × List Bool =>
      MultiTapeTM.zipFold (fun (_ : Bool) => f) false p.1 p.2)
      (encPair encCoefficients encCoefficients) encCoefficients
      (fun p => (encPair encCoefficients encCoefficients p).length) := by
  have hf := ComputableInSpace.of_finite
    (encIn := encPair encBool (encPair encBool (encOption encBool)))
    (encB := encOption encBool) (fun q : Bool × Bool × Option Bool => f q.2.1 q.2.2)
  obtain ⟨K, h⟩ := ComputableInSpace.zipFold hf
    (B := fun q : Bool × List Bool × List Bool => 3 * q.2.1.length) (fun q i => by
      rw [coefficients_length]
      exact Nat.mul_le_mul_left 3 ((zipFold_length f q.1 (q.2.1.take i) q.2.2).trans
        (by simp only [List.length_take]; exact Nat.min_le_right _ _)))
  have hlin := h.weaken (show
      (fun q : Bool × List Bool × List Bool => K *
        ((encPair encBool (encPair encCoefficients encCoefficients) q).length +
          3 * q.2.1.length + 1)) ≼
      (fun q => (encPair encBool (encPair encCoefficients encCoefficients) q).length) from
    .of_le_linear (4 * K + 1) (4 * K + 1) fun q => by
      rw [length_encPair, length_encPair, coefficients_length, coefficients_length]
      cases q.1 <;> simp [encBool_apply] <;> nlinarith)
  have hp : ComputableInSpace (fun p : List Bool × List Bool => (false, p))
      (encPair encCoefficients encCoefficients)
      (encPair encBool (encPair encCoefficients encCoefficients))
      (fun p => (encPair encCoefficients encCoefficients p).length) := budget_prod
    (budget_const (encB := encBool) false (.refl _))
    (ComputableInSpace.of_inO ComputableInO.id')
  exact budget_comp_linear hlin hp

private theorem zip_xor (a b : List Bool) :
    MultiTapeTM.zipFold (fun (_ : Bool) bit other => other.map (xor bit)) false a b =
      a.zipWith xor b := by
  induction a generalizing b with
  | nil => rfl
  | cons bit a ih => cases b <;> simp [MultiTapeTM.zipFold, ih]

/-- Coefficient-wise XOR uses linear workspace in the encoded pair of coefficient words.
The output ends at the shorter word. -/
theorem xor_inSpace :
    ComputableInSpace (fun p : List Bool × List Bool => p.1.zipWith xor p.2)
      (encPair encCoefficients encCoefficients) encCoefficients
      (fun p => (encPair encCoefficients encCoefficients p).length) := by
  simpa only [zip_xor] using zip_inSpace (fun bit other => other.map (xor bit))

private def pad (template word : List Bool) : List Bool :=
  MultiTapeTM.zipFold (fun (_ : Bool) _ bit => some (bit.getD false)) false template word

private theorem pad_eq (template word : List Bool) :
    pad template word = List.ofFn (fun i : Fin template.length => word.getD i false) := by
  induction template generalizing word with
  | nil => simp [pad, MultiTapeTM.zipFold]
  | cons bit template ih =>
    cases word with
    | nil =>
      simpa [pad, MultiTapeTM.zipFold, List.ofFn_succ, List.getD] using
        congrArg (false :: ·) (ih [])
    | cons head tail =>
      simpa [pad, MultiTapeTM.zipFold, List.ofFn_succ, List.getD] using
        congrArg (head :: ·) (ih tail)

private theorem pad_inSpace :
    ComputableInSpace (fun p : List Bool × List Bool => pad p.1 p.2)
      (encPair encCoefficients encCoefficients) encCoefficients
      (fun p => (encPair encCoefficients encCoefficients p).length) :=
  zip_inSpace (fun _ bit => some (bit.getD false))

private theorem pad_length (template word : List Bool) :
    (pad template word).length = template.length := by rw [pad_eq, List.length_ofFn]

private theorem pad_nil (template : List Bool) :
    pad template [] = List.replicate template.length false := by
  induction template with
  | nil => rfl
  | cons bit template ih =>
    simp only [pad, MultiTapeTM.zipFold, List.head?_nil, Option.getD_none, Option.toList_some,
      List.singleton_append, List.tail_nil, List.length_cons, List.replicate_succ]
    exact congrArg (false :: ·) ih

private theorem mulXMod_inSpace :
    ComputableInSpace (fun p : List Bool × List Bool => mulXMod p.1 p.2)
      (encPair encCoefficients encCoefficients) encCoefficients
      (fun p => (encPair encCoefficients encCoefficients p).length) := by
  have hg := fst encCoefficients encCoefficients
  have hr := snd encCoefficients encCoefficients
  have hn := budget_natPred (budget_length hg)
  have hs := budget_cons (budget_const (encB := encBool) false (.refl _)) hr
  have ht := budget_headD false (budget_comp_linear (listDrop encBool) (budget_prod hs hn))
  have hx := budget_comp_linear xor_inSpace (budget_prod hs hg)
  exact (budget_comp_linear (listTake encBool)
    (budget_prod (budget_ite ht hx hs) hn)).of_enc_eq fun p => by
      simp only [mulXMod, List.getD_eq_getElem?_getD, List.headD_eq_head?_getD,
        List.head?_drop]

/-- The two coefficient registers carried by multiplication. -/
private structure Registers where
  shift : List Bool
  product : List Bool

private enc_structure encRegisters : Registers where
  shift : encCoefficients, product : encCoefficients

private def advance (g : List Bool) (s : Registers) (bit : Bool) : Registers :=
  ⟨mulXMod g s.shift, if bit then s.product.zipWith xor s.shift else s.product⟩

private theorem advance_inSpace :
    ComputableInSpace (fun p : (List Bool × Registers) × Bool =>
      advance p.1.1 p.1.2 p.2)
      (encPair (encPair encCoefficients encRegisters) encBool) encRegisters
      (fun p => (encPair (encPair encCoefficients encRegisters) encBool p).length) := by
  have hp := fst (encPair encCoefficients encRegisters) encBool
  have hb := snd (encPair encCoefficients encRegisters) encBool
  have hg := hp.fst'
  have hs := encRegisters_shift_budget hp.snd'
  have ha := encRegisters_product_budget hp.snd'
  exact encRegisters_mk_budget
    (budget_comp_linear mulXMod_inSpace (budget_prod hg hs))
    (budget_ite hb (budget_comp_linear xor_inSpace (budget_prod ha hs)) ha)

private theorem advance_lengths (g : List Bool) (s : Registers) (bit : Bool) (d : ℕ)
    (hs : s.shift.length ≤ d) (ha : s.product.length ≤ d) (hg : g.length - 1 ≤ d) :
    (advance g s bit).shift.length ≤ d ∧ (advance g s bit).product.length ≤ d := by
  constructor
  · change (mulXMod g s.shift).length ≤ d
    unfold mulXMod
    exact Nat.le_trans (List.length_take_le _ _) hg
  · simp only [advance]
    split <;> simp_all only [List.length_zipWith]; omega

private theorem fold_lengths (g bits : List Bool) (s : Registers) (d : ℕ)
    (hs : s.shift.length ≤ d) (ha : s.product.length ≤ d) (hg : g.length - 1 ≤ d) :
    (bits.foldl (advance g) s).shift.length ≤ d ∧
      (bits.foldl (advance g) s).product.length ≤ d := by
  induction bits generalizing s with
  | nil => exact ⟨hs, ha⟩
  | cons bit bits ih =>
    have h := advance_lengths g s bit d hs ha hg
    exact ih _ h.1 h.2

private theorem fold_agrees (g bits : List Bool) (s : Registers) :
    (bits.foldl (advance g) s).product =
      (bits.foldl (modStep g) (s.shift, s.product)).2 := by
  induction bits generalizing s with
  | nil => rfl
  | cons bit bits ih => exact ih (advance g s bit)

-- Shared by multiplication and remainder: the original modStep fold, with both live words
-- bounded at every prefix and the retained modulus charged in each scalar invocation.
private theorem fold_inSpace {α : Type} {encIn : α ↪ List Bool}
    {g bits : α → List Bool} {initial : α → Registers}
    (hg : ComputableInSpace g encIn encCoefficients (fun p => (encIn p).length))
    (hbits : ComputableInSpace bits encIn encCoefficients (fun p => (encIn p).length))
    (hinit : ComputableInSpace initial encIn encRegisters (fun p => (encIn p).length))
    (hwords : ∀ p, (initial p).shift.length ≤ (g p).length - 1 ∧
      (initial p).product.length ≤ (g p).length - 1)
    (hmodulus : ∀ p, 3 * (g p).length ≤ (encIn p).length)
    (hmultiplier : ∀ p, (encCoefficients (bits p)).length ≤ (encIn p).length) :
    ComputableInSpace (fun p => ((bits p).foldl (advance (g p)) (initial p)).product)
      encIn encCoefficients (fun p => (encIn p).length) := by
  have hstates (p : α) (i : ℕ) :
      (encRegisters (((bits p).take i).foldl (advance (g p)) (initial p))).length ≤
          9 * (g p).length + 1 := by
    have h := fold_lengths (g p) ((bits p).take i) (initial p) ((g p).length - 1)
      (hwords p).1 (hwords p).2 le_rfl
    simp only [encRegisters_apply, encRegistersFields, length_encPair, coefficients_length]
    omega
  have hfold := foldlWith hg hbits hinit advance_inSpace
    (Q := fun p => 24 * ((encIn p).length + 1))
    (B := fun p => 9 * (g p).length + 1)
    (fun p i _ => by
      have h := hstates p i
      have hm := hmodulus p
      simp only [length_encPair, coefficients_length, encBool_apply, List.length_singleton]
      omega)
    (fun p i _ => hstates p i)
  exact (encRegisters_product_budget hfold).weaken
    (.of_le_linear 100 100 fun p => by
      have hm := hmodulus p
      have hb := hmultiplier p
      rw [coefficients_length] at hb
      simp only [coefficients_length]
      omega)

/-- The existing table-free evaluator is computable by a native machine in workspace linear
in its three framed coefficient words. This includes all intermediate fold states and scalar
callees, with no assumptions about the supplied modulus. -/
theorem fieldMulMod_inSpace :
    ComputableInSpace (fun p : MulInput => fieldMulMod p.modulus p.left p.right)
      encMulInput encCoefficients (fun p => (encMulInput p).length) := by
  have hid : ComputableInSpace (fun p : MulInput => p) encMulInput encMulInput
      (fun p => (encMulInput p).length) := of_inO ComputableInO.id'
  have hg := encMulInput_modulus_budget hid
  have hl := encMulInput_left_budget hid
  have hr := encMulInput_right_budget hid
  have ht := budget_tail hg
  have hleft := budget_comp_linear pad_inSpace (budget_prod ht hl)
  have hright := budget_comp_linear pad_inSpace (budget_prod ht hr)
  have hzero := budget_comp_linear pad_inSpace
    (budget_prod ht (budget_const (encB := encCoefficients) [] (.refl _)))
  have hinit := encRegisters_mk_budget hleft hzero
  have hout := fold_inSpace hg hright hinit
    (fun p => by simp [pad_length])
    (fun p => by
      simp only [encMulInput_apply, encMulInputFields, length_encPair, coefficients_length]
      omega)
    (fun p => by
      simp only [coefficients_length, pad_length, List.length_tail,
        encMulInput_apply, encMulInputFields, length_encPair]
      omega)
  refine hout.of_enc_eq fun p => ?_
  rw [fold_agrees, fieldMulMod, modMulBits, pad_nil]
  simp only [pad_eq, List.length_tail, Fin.val_cast]

/-- Arguments to the supplied-modulus polynomial-remainder evaluator. -/
structure RemainderInput where
  /-- Little-endian modulus coefficients, with no monicity assumption. -/
  modulus : List Bool
  /-- Little-endian coefficients to scan. -/
  dividend : List Bool

/-- Modulus followed by dividend, both framed Boolean lists; the modulus field is additionally
framed by the record encoding. Each coefficient contributes three symbols before record framing. -/
enc_structure encRemainderInput : RemainderInput where
  modulus : encCoefficients, dividend : encCoefficients

private theorem pad_one (template : List Bool) :
    pad template [true] =
      (true :: List.replicate (template.length - 1) false).take template.length := by
  cases template with
  | nil => rfl
  | cons bit tail =>
    change true :: pad tail [] = (true :: List.replicate tail.length false).take (tail.length + 1)
    rw [pad_nil]
    simp

/-- Native linear workspace for the existing total supplied-modulus `modBits` evaluator.
The modulus is retained throughout the scan; at every prefix both registers have at most
`modulus.length - 1` coefficients. The native fold also charges each shift/XOR callee.
For monic moduli, algebraic remainder agreement is supplied by `Cslib.mk_polyOfBits_modBits`;
no algebraic meaning is asserted here for malformed modulus words. -/
theorem modBits_inSpace :
    ComputableInSpace (fun p : RemainderInput => modBits p.modulus p.dividend)
      encRemainderInput encCoefficients (fun p => (encRemainderInput p).length) := by
  have hid : ComputableInSpace (fun p : RemainderInput => p)
      encRemainderInput encRemainderInput (fun p => (encRemainderInput p).length) :=
    of_inO ComputableInO.id'
  have hg := encRemainderInput_modulus_budget hid
  have hf := encRemainderInput_dividend_budget hid
  have ht := budget_tail hg
  have hone := budget_comp_linear pad_inSpace
    (budget_prod ht (budget_const (encB := encCoefficients) [true] (.refl _)))
  have hzero := budget_comp_linear pad_inSpace
    (budget_prod ht (budget_const (encB := encCoefficients) [] (.refl _)))
  have hinit := encRegisters_mk_budget hone hzero
  have hout := fold_inSpace hg hf hinit
    (fun p => by simp [pad_length])
    (fun p => by
      simp only [encRemainderInput_apply, encRemainderInputFields,
        length_encPair, coefficients_length]
      omega)
    (fun p => by
      simp only [encRemainderInput_apply, encRemainderInputFields, length_encPair]
      omega)
  refine hout.of_enc_eq fun p => ?_
  rw [fold_agrees, modBits, pad_one, pad_nil]
  simp only [List.length_tail, Nat.sub_sub]

end Turing.BinaryField
