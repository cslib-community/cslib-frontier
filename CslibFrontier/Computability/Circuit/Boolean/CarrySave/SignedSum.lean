/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.ConvolutionPath
public import CslibFrontier.Computability.Circuit.Boolean.Modular.Subtract
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Combining signed convolution terms in a carry-save tree

A partial product has zero in its carry word. Its modular negative is the complement of its
sum word together with one. Two leading path bits choose a positive term, a negative term,
an optional third positive term, or zero. At every real leaf only the original bit and a
constant are required.
-/

@[expose] public section
namespace Cslib.Circuits.Boolean.CarrySaveQuery.SignedSum

open BitString

variable {w : ℕ}

/-- Read a finished word in the coefficient ring. -/
def residue (a : BitString w) : ZMod (2 ^ w) := ((equivFin w a : ℕ) : ZMod (2 ^ w))

/-- The two's-complement negative of a sum word, kept as a carry-save pair. -/
def negative (a : BitString w) : BitString (w + w) :=
  Fin.append (fun i => !a i) ((equivFin w).symm ⟨1 % 2 ^ w, Nat.mod_lt _ (by positivity)⟩)

theorem residue_negative (a : BitString w) :
    (pairVal (negative a) : ZMod (2 ^ w)) = -residue a := by
  have h := (equivFin w a).isLt
  have hn : (2 ^ w - 1 - (equivFin w a : ℕ)) + (equivFin w a : ℕ) + 1 = 2 ^ w := by omega
  have hz := congrArg (fun n : ℕ => (n : ZMod (2 ^ w))) hn
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at hz
  rw [negative, pairVal_append, Equiv.apply_symm_apply, Modular.val_not]
  simp only [Nat.cast_add, ZMod.natCast_mod, Nat.cast_one, residue]
  linear_combination hz

/-- The two-bit selector adds the first term, subtracts the second term and optionally
adds the third. Its fourth branch is zero. -/
def leaves (extra : Bool) (a b c : List Bool → BitString (w + w)) :
    List Bool → BitString (w + w)
  | false :: false :: t => a t
  | false :: true :: t => negative (fstBits (b t))
  | true :: false :: t => if extra then c t else Fin.append (fun _ => false) (fun _ => false)
  | _ => Fin.append (fun _ => false) (fun _ => false)

/-- The additive contribution of a complete subtree. -/
def sum (a : List Bool → BitString (w + w)) (n : ℕ) : ZMod (2 ^ w) :=
  (leafSum a n [] : ZMod (2 ^ w))

private theorem leafSum_prefix (a : List Bool → BitString (w + w)) (n : ℕ) (p q : List Bool) :
    leafSum a n (p ++ q) = leafSum (fun t => a (p ++ t)) n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => simp only [leafSum, List.append_assoc, ih]

private theorem leafSum_negative (a : List Bool → BitString (w + w)) (n : ℕ) (p : List Bool)
    (hz : ∀ t, sndBits (a t) = fun _ => false) :
    (leafSum (fun t => negative (fstBits (a t))) n p : ZMod (2 ^ w)) =
      -(leafSum a n p : ZMod (2 ^ w)) := by
  induction n generalizing p with
  | zero =>
    rw [leafSum, leafSum, residue_negative]
    simp [residue, pairVal, hz]
  | succ n ih => simp only [leafSum, Nat.cast_add, ih, neg_add]

private theorem leafSum_zero (n : ℕ) (p : List Bool) :
    leafSum (fun _ => Fin.append (fun _ : Fin w => false) (fun _ : Fin w => false)) n p = 0 := by
  induction n generalizing p with
  | zero => simp [leafSum]
  | succ n ih => simp [leafSum, ih]

/-- The value of one tree with two extra compressor layers includes the required signed terms. -/
theorem eval (extra : Bool) (a b c : List Bool → BitString (w + w)) (n : ℕ)
    (hz : ∀ t, sndBits (b t) = fun _ => false) :
    residue ((carryLookaheadAdd w).eval interpretation (tree (leaves extra a b c) (n + 2) [])) =
      sum a n - sum b n + (if extra then sum c n else 0) := by
  rw [residue, val_eval_carryLookaheadAdd_pair, pairVal_tree_mod, ZMod.natCast_mod,
    leafSum, leafSum, leafSum]
  simp only [List.nil_append, List.cons_append]
  have h (p : List Bool) := leafSum_prefix (leaves extra a b c) n p []
  simp only [List.append_nil] at h
  rw [h [false, false], h [false, true], h [true, false], h [true, true]]
  cases extra <;> simp [leaves, leafSum_negative _ _ _ hz, leafSum_zero, sum, sub_eq_add_neg]

end Cslib.Circuits.Boolean.CarrySaveQuery.SignedSum
