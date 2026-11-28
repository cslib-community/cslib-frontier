/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
public import Mathlib.Tactic.FunProp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreePrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer.Copy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryAddition
import CslibFrontier.Foundations.Data.Nat.Doubling
import CslibFrontier.Tactic.EncLen
import Mathlib.Tactic.TypeStar

/-!
# Quantitative computability rules

`fun_prop (disch := lia)` composes degree certificates (`ComputableInDegree`) without replacing
output-size bounds by runtime bounds. Computation premises determine the intermediate encodings
and degrees before the arithmetic obligations compare the resulting degrees with the requested ones.
The same `fun_prop` interface recognizes ordinary finite-state bit folds with linear time and
constant work space.
For nested projections with inferred degrees, `disch := first | apply le_refl | lia` first
instantiates a missing degree with the derived bound, then checks arithmetic inequalities.
Framed-list and option rules infer the payload encoding from the representation explicitly.

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.foldl'`,
  `Turing.MultiTapeTM.ComputableInDegree.foldlWith`: plain left folds with degree bounds.
* `Turing.MultiTapeTM.ComputableInDegree.natSucc`: binary successor with degrees one.
* `Turing.MultiTapeTM.computableInDegree_add`, `Turing.MultiTapeTM.computableInDegree_mul`:
  plain binary addition (quadratic) and multiplication (cubic).
* `Turing.MultiTapeTM.ComputableInO.comp_enc`: reuse a bit-word computation on encoded
  instances, with bounds evaluated on their encodings.
* `Turing.MultiTapeTM.ComputableInO.lengthUnary`: compute bit-word length in unary within
  linear time and space.
* `Turing.MultiTapeTM.ComputableInO.unary_two_pow`: compute `2 ^ n` from unary `n` within
  time `O((n + 1) * 2 ^ n)` and space `O(2 ^ n)`.
* `Turing.MultiTapeTM.ComputableInDegree.comp_le`, `.prod_le`, `.ite_le`: plain composition,
  pairing, and branching at requested degrees, retaining output-size bounds.
* `Turing.MultiTapeTM.ComputableInDegree.bitsReverse`,
  `Turing.MultiTapeTM.ComputableInDegree.bitsDropLast`,
  `Turing.MultiTapeTM.ComputableInDegree.bitsGetLast?ToList`,
  `Turing.MultiTapeTM.ComputableInDegree.bitsGetLast?`,
  `Turing.MultiTapeTM.ComputableInDegree.optionBoolToList`,
  `Turing.MultiTapeTM.ComputableInDegree.bitsAppend`,
  `Turing.MultiTapeTM.ComputableInDegree.unaryAdd`: plain degree rules for raw bit-list reversal,
  prefix, last-bit extraction, concatenation, and unary addition.

## References

Uses Christian Reitwiessner's degree calculus and streaming backend; see the source markers in
`Degree.lean` and `CslibFrontier/Computability/Machines/Turing/MultiTape/Encodings/StreamFold.lean`.
-/

public section

namespace Turing.MultiTapeTM

universe u

namespace ComputableInDegree

/-- Equality of bit words in quadratic time/space and constant output length. -/
theorem eqWords :
    ComputableInDegree (fun p : List Bool × List Bool => decide (p.1 = p.2))
      (encPair encBits encBits) encBool 2 0 := by
  have hfold := foldl' (encA := encBool) (encL := encBits)
    (encB := encPair encBits encBool) (fst encBits encBits)
    ((snd encBits encBits).prod (const true)) eqWordsStep
    (B := fun p => 2 * (encPair encBits encBits p).length + 2)
    ((DegreeBounded.self.smul 2).add_const 2)
    (fun p i _ => by
      rw [show ((p.1.take i).foldl EqWords.step (p.2, true)) =
        ((p.2.drop (p.1.take i).length), ((p.1.take i).foldl EqWords.step (p.2, true)).2) from
          Prod.ext (EqWords.foldl_fst _ _ _) rfl]
      simp only [encPair_apply, encBits_apply, encBool_apply, List.length_append, length_frame,
        List.length_drop, List.length_singleton]
      omega)
  have h : ComputableInDegree (_ ∘ _) _ encBool 2 0 := (eqWordsResult.comp hfold).mono
  convert h using 1
  funext p
  simpa using (EqWords.foldl_result p.1 p.2 true).symm

/-- Equality for any encoding in quadratic time/space and constant output length. -/
theorem eq {α : Type} [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : α × α => decide (p.1 = p.2)) (encPair enc enc) encBool 2 0 := by
  have h : ComputableInDegree (_ ∘ _) _ encBool 2 0 := (eqWords.comp (of_eq
    (f := fun p : α × α => (enc p.1, enc p.2)) (encIn := encPair enc enc)
    (encMid := encPair encBits encBits) fun _ => rfl)).mono
  convert h using 1
  funext p
  simp [enc.injective.eq_iff]

end ComputableInDegree

/-- **Addition is computable in quadratic time and space**, with linear output length, in the
binary encoding. -/
theorem computableInDegree_add :
    ComputableInDegree (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat 2 1 :=
  ComputableInO.natAdd.computableInDegree
    ⟨1, fun _ => by simp⟩ ⟨1, fun _ => by simp⟩ (by decide)

/-- **Multiplication is computable in cubic time and space**, with linear output length, in the
binary encoding. -/
theorem computableInDegree_mul :
    ComputableInDegree (fun p : ℕ × ℕ => p.1 * p.2) (encPair encNat encNat) encNat 3 1 :=
  ComputableInO.natMul.computableInDegree ⟨1, fun _ => by simp⟩ ⟨1, fun _ => by simp⟩ (by decide)

attribute [fun_prop] ComputableInDegree.const ComputableInDegree.fst
  ComputableInDegree.snd ComputableInDegree.comp ComputableInDegree.prod
  ComputableInDegree.fst' ComputableInDegree.snd'
  ComputableInDegree.cons ComputableInDegree.snoc
  ComputableInDegree.listAppend ComputableInDegree.isSome
  ComputableInDegree.unary_succ ComputableInDegree.unary_pred
  ComputableInDegree.unary_sub ComputableInDegree.unary_min
  ComputableInDegree.int_succ ComputableInDegree.int_pred

namespace ComputableInDegree

/-- Testing a framed list for emptiness. -/
@[fun_prop]
theorem listIsEmpty {α : Type*} (enc : α ↪ List Bool) :
    ComputableInDegree List.isEmpty (encList enc) encBool 1 1 :=
  isEmpty (enc₁ := enc)

/-- Reverse a raw bit list in linear time and linear output size. -/
@[fun_prop]
theorem bitsReverse :
    ComputableInDegree List.reverse encBits encBits 1 1 :=
  of_bounds ⟨2, fun _ => by simp; omega⟩ ⟨0, fun _ => by simp⟩
    ComputableInTimeAndSpace.reverse_bits

/-- Drop the last bit of a raw bit list in linear time and linear output size. -/
@[fun_prop]
theorem bitsDropLast :
    ComputableInDegree List.dropLast encBits encBits 1 1 :=
  of_bounds ⟨8, fun _ => by simp; omega⟩ ⟨0, fun _ => by simp⟩
    ComputableInTimeAndSpace.dropLast_bits

/-- Extract the last bit of a raw bit list as a 0-or-1-element list in linear time and constant
output size. -/
@[fun_prop]
theorem bitsGetLast?ToList :
    ComputableInDegree (fun l : List Bool => l.getLast?.toList) encBits encBits 1 0 :=
  ⟨⟨_, _, ⟨8, fun _ => by simp; omega⟩, ⟨0, fun _ => by simp⟩,
    ComputableInTimeAndSpace.getLast?_toList_bits⟩,
    ⟨1, fun l => by simp [Option.length_toList_le]⟩⟩

/-- Extract the last bit of a raw bit list as an `Option Bool` in linear time and constant output
size. -/
@[fun_prop]
theorem bitsGetLast? :
    ComputableInDegree (List.getLast? (α := Bool)) encBits (encOption encBool) 1 0 :=
  ⟨⟨_, _, ⟨8, fun _ => by simp; omega⟩, ⟨0, fun _ => by simp⟩,
    ComputableInTimeAndSpace.getLast?_bits⟩,
    ⟨2, fun l => by cases h : l.getLast? <;> simp [h]⟩⟩

/-- Convert an `Option Bool` to a 0-or-1-element bit list in linear time and linear output size. -/
@[fun_prop]
theorem optionBoolToList :
    ComputableInDegree (Option.toList (α := Bool)) (encOption encBool) encBits 1 1 :=
  (Internal.DecoderWords.tail_degree.comp
    (of_eq (f := encOption encBool) (encIn := encOption encBool) (encMid := encBits)
      fun _ => rfl)).of_enc_eq fun o => by cases o <;> rfl

/-- Concatenate two raw bit lists while preserving their time and output degrees independently. -/
@[fun_prop]
theorem bitsAppend {α : Type*} {encIn : α ↪ List Bool} {f g : α → List Bool}
    {df ef dg eg d e : ℕ}
    (hf : ComputableInDegree f encIn encBits df ef)
    (hg : ComputableInDegree g encIn encBits dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableInDegree (fun x => f x ++ g x) encIn encBits d e :=
  (hf.append hg fun _ => rfl).mono hd he

/-- Add two unary natural numbers while preserving their time and output degrees independently. -/
@[fun_prop]
theorem unaryAdd {α : Type*} {encIn : α ↪ List Bool} {f g : α → ℕ}
    {df ef dg eg d e : ℕ}
    (hf : ComputableInDegree f encIn encUnary df ef)
    (hg : ComputableInDegree g encIn encUnary dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableInDegree (fun x => f x + g x) encIn encUnary d e :=
  (hf.append hg fun _ => List.replicate_add _ _ true).mono hd he

/-- Compose using the intermediate output size. The computation premises determine the degrees
before arithmetic compares them with the requested bound. -/
@[fun_prop]
theorem comp_le {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : β → γ} {g : α → β} {df ef dg eg d e : ℕ}
    (hg : ComputableInDegree g encIn encMid dg eg)
    (hf : ComputableInDegree f encMid encOut df ef)
    (hd : max dg (eg * df) ≤ d) (he : eg * ef ≤ e) :
    ComputableInDegree (fun x => f (g x)) encIn encOut d e :=
  (hf.comp hg).mono hd he

/-- Pair two results while preserving their output degrees independently of computation time. -/
@[fun_prop]
theorem prod_le {α β γ : Type u} {encIn : α ↪ List Bool} {encF : β ↪ List Bool}
    {encG : γ ↪ List Bool} {f : α → β} {g : α → γ} {df ef dg eg d e : ℕ}
    (hf : ComputableInDegree f encIn encF df ef)
    (hg : ComputableInDegree g encIn encG dg eg)
    (hd : max df dg ≤ d) (he : max ef eg ≤ e) :
    ComputableInDegree (fun x => (f x, g x)) encIn (encPair encF encG) d e :=
  (hf.prod hg).mono hd he

/-- Branching on a computed Boolean, retaining each branch's output degree. -/
@[fun_prop]
theorem ite_le {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {condition : α → Bool} {f g : α → β} {dc ec df ef dg eg d e : ℕ}
    (hc : ComputableInDegree condition encIn encBool dc ec)
    (hf : ComputableInDegree f encIn encOut df ef)
    (hg : ComputableInDegree g encIn encOut dg eg)
    (hd : max dc (max df dg) ≤ d) (he : max ef eg ≤ e) :
    ComputableInDegree (fun x => if condition x then f x else g x) encIn encOut d e :=
  (hc.ite (hf.restrict _) (hg.restrict _)).mono hd he

end ComputableInDegree

namespace ComputableInO

variable {α β : Type} {encOut : β ↪ List Bool}

/-- A function of bit words computed within given bounds is computed by the same machine on encoded
instances. -/
theorem comp_enc {f : List Bool → β} {T S : List Bool → ℕ}
    (h : ComputableInO f encBits encOut T S) (enc : α ↪ List Bool) :
    ComputableInO (fun a => f (enc a)) enc encOut (fun a => T (enc a)) fun a => S (enc a) :=
  h.of_encIn_eq enc fun _ => rfl

/-- The length of a bit word in unary, within linear time and space, by the streaming machine of
`Turing.MultiTapeTM.ComputableInTimeAndSpace.length_bits`. -/
theorem lengthUnary : ComputableInO (fun l : List Bool => l.length) encBits encUnary
    (fun l => l.length) fun l => l.length :=
  .of_bounds ComputableInTimeAndSpace.length_bits 8
    (fun l => by omega) (fun _ => Nat.zero_le _)
    fun l => by simp only [encUnary_apply, List.length_replicate]; omega

/-- Doubling `m` once for each element of a list of length `n` multiplies it by `2 ^ n`. -/
private theorem foldl_double (n m : ℕ) :
    (List.replicate n true).foldl (fun m _ => m + m) m = m * 2 ^ n := by
  rw [List.foldl_add_self_eq_mul_two_pow, List.length_replicate]

/-- **`2 ^ n` in unary**, by doubling `n` times, within time `O((n + 1) * 2 ^ n)` and space
`O(2 ^ n)`. -/
theorem unary_two_pow : ComputableInO (fun n : ℕ => 2 ^ n) encUnary encUnary
    (fun n => (n + 1) * 2 ^ n) fun n => 2 ^ n := by
  have hstep : ComputableInO (fun p : ℕ × Bool => p.1 + p.1) (encPair encUnary encBool)
      encUnary (fun p => (encPair encUnary encBool p).length)
      fun p => (encPair encUnary encBool p).length :=
    (ComputableInDegree.unaryAdd (ComputableInDegree.fst encUnary encBool)
      (ComputableInDegree.fst encUnary encBool) le_rfl le_rfl).inO_one
  have hstate (n i : ℕ) : (encUnary (((List.replicate n true).take i).foldl
      (fun m _ => m + m) 1)).length ≤ 2 ^ n := by
    rw [List.take_replicate, foldl_double, encUnary_apply, List.length_replicate, one_mul]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.min_le_right _ _)
  have h := foldl (encA := encBool) (encL := encBits) (encB := encUnary)
    (list := fun n : ℕ => List.replicate n true) (init := fun _ => 1)
    (step := fun m _ => m + m)
    (of_linear (.of_eq (f := fun n : ℕ => List.replicate n true) (encIn := encUnary)
      (encMid := encBits) fun _ => rfl)) (const 1) hstep
    (R := fun n => 2 * 2 ^ n + 2) (Q := fun n => 2 * 2 ^ n + 2) (B := fun n => 2 ^ n)
    (fun n i _ => by
      have := hstate n i
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega)
    (fun n i _ => by
      have := hstate n i
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega)
    fun n i _ => hstate n i
  refine (h.mono 8 (fun n => ?_) fun n => ?_).of_enc_eq fun n => ?_
  · have h₁ : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    have h₂ := Nat.mul_le_mul_left (n + 1) h₁
    simp only [encUnary_apply, encBits_apply, List.length_replicate]
    nlinarith
  · have h₁ : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
    enc_len
  · rw [foldl_double, one_mul]

end ComputableInO

end Turing.MultiTapeTM
