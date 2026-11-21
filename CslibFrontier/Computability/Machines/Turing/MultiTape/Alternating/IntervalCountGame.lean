/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Segment
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Counting an implicit interval with one endpoint query per branch

The existential player supplies a total, then the left subtotal of the current dyadic interval.
A universal bit chooses the half that must justify its total. A single physical word stores all
choices. Its terminal rejects an inconsistent subtraction and otherwise checks one padded leaf.
-/

public section

namespace Turing.MultiTapeATM.IntervalCountGame

open Cslib.BitString QuantifiedWord

/-- Flags until the interval is a singleton. Each left subtotal precedes the choice of side. -/
@[expose] def rounds (w : ℕ) : ℕ → List Bool
  | 0 => []
  | h + 1 => List.replicate w false ++ true :: rounds w h

/-- The total is one existential field preceding all bisection rounds. -/
@[expose] def flags (n : ℕ) : List Bool :=
  List.replicate (n.size + 1) false ++ rounds (n.size + 1) n.size

@[simp] theorem length_rounds (w h : ℕ) : (rounds w h).length = h * (w + 1) := by
  induction h with
  | zero => simp [rounds]
  | succ h ih => simp [rounds, ih, Nat.succ_mul]; omega

/-- The number of physical choices is quadratic in the bit length of the endpoint count. -/
theorem length_flags (n : ℕ) : (flags n).length = n.size + 1 + n.size * (n.size + 2) := by
  simp [flags]

/-- Reconstruct the selected index and its claimed Boolean value. A subtotal larger than its
parent fails immediately, even on the branch selecting the left side. -/
@[expose] def walk (w : ℕ) : ℕ → ℕ → ℕ → List Bool → Option (ℕ × ℕ)
  | 0, base, value, _ => some (base, value)
  | h + 1, base, value, xs =>
    let left := lsbValue (xs.take w)
    let rest := xs.drop w
    if left ≤ value then
      if rest.headD false then walk w h (base + 2 ^ h) (value - left) rest.tail
      else walk w h base left rest.tail
    else none

/-- Read the claimed total and its challenged bit before extracting the single obligation. -/
@[expose] def route (n bit : ℕ) (claim : Bool) (xs : List Bool) : Option (ℕ × ℕ) :=
  let w := n.size + 1
  let value := lsbValue (xs.take w)
  if value.testBit bit = claim then walk w n.size 0 value (xs.drop w) else none

/-- Invalid routes reject. Successful routes compare their one integer to a single bit. -/
@[expose] def verdict (f : ℕ → Bool) : Option (ℕ × ℕ) → Prop
  | none => False
  | some (i, value) => value = (f i).toNat

/-- Sum on the dyadic interval starting at the given index. -/
def total (f : ℕ → Bool) (base h : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (2 ^ h), (f (base + j)).toNat

private theorem total_le (f : ℕ → Bool) (base h : ℕ) : total f base h ≤ 2 ^ h := by
  calc
    _ ≤ ∑ _j ∈ Finset.range (2 ^ h), 1 :=
      Finset.sum_le_sum fun j _ => by cases f (base + j) <;> decide
    _ = _ := by simp

private theorem total_succ (f : ℕ → Bool) (base h : ℕ) :
    total f base (h + 1) = total f base h + total f (base + 2 ^ h) h := by
  simp only [total, Nat.pow_succ, Nat.mul_two, Finset.sum_range_add, Nat.add_assoc]

private theorem plays_const (P : Prop) (pre players : List Bool) :
    plays (fun _ => P) pre players ↔ P := by
  induction players generalizing pre with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [plays, ih]

private theorem plays_field (V : List Bool → Prop) (w : ℕ) (tail : List Bool) :
    plays V [] (List.replicate w false ++ tail) ↔
      ∃ x : Fin (2 ^ w), plays (fun ys => V (lowBits w x.val ++ ys)) [] tail := by
  rw [plays_exists_field]
  apply exists_congr
  intro x
  simpa only [List.nil_append, List.append_nil] using
    plays_append_prefix V (lowBits w x.val) [] tail

private theorem plays_side (V : List Bool → Prop) (tail : List Bool) :
    plays V [] (true :: tail) ↔ ∀ b, plays (fun ys => V (b :: ys)) [] tail := by
  simp only [plays, ↓reduceIte, List.nil_append]
  apply forall_congr'
  intro b
  simpa only [List.append_nil, List.singleton_append] using plays_append_prefix V [b] [] tail

private theorem walk_field (w h base value : ℕ) (x : Fin (2 ^ w)) (b : Bool) (ys : List Bool) :
    walk w (h + 1) base value (lowBits w x.val ++ b :: ys) =
      if x.val ≤ value then
        if b then walk w h (base + 2 ^ h) (value - x.val) ys else walk w h base x.val ys
      else none := by
  have ht : (lowBits w x.val ++ b :: ys).take w = lowBits w x.val := by
    simpa only [length_lowBits] using List.take_left (l₁ := lowBits w x.val) (l₂ := _)
  have hd : (lowBits w x.val ++ b :: ys).drop w = b :: ys := by
    simpa only [length_lowBits] using List.drop_left (l₁ := lowBits w x.val) (l₂ := _)
  simp only [walk, ht, hd, lsbValue_lowBits x.isLt, List.headD_cons, List.tail_cons]

/-- All paths agree on precisely the actual sum. False total guesses cannot survive the
universal choice of a half, including when every leaf in that half is zero. -/
theorem plays_rounds (f : ℕ → Bool) (w h base value : ℕ) (hw : h < w) :
    plays (fun xs => verdict f (walk w h base value xs)) [] (rounds w h) ↔
      value = total f base h := by
  induction h generalizing base value with
  | zero => simp [rounds, plays, walk, verdict, total]
  | succ h ih =>
    rw [rounds, plays_field]
    have he (x : Fin (2 ^ w)) :
        plays (fun ys => verdict f (walk w (h + 1) base value (lowBits w x.val ++ ys)))
            [] (true :: rounds w h) ↔
          x.val ≤ value ∧ x.val = total f base h ∧ value - x.val = total f (base + 2 ^ h) h := by
      rw [plays_side]
      by_cases hx : x.val ≤ value
      · simp only [walk_field, hx, ↓reduceIte, true_and, Bool.forall_bool, Bool.false_eq_true]
        rw [ih _ _ (by omega), ih _ _ (by omega)]
      · simp only [walk_field, hx, ↓reduceIte, false_and, verdict, plays_const, forall_const]
    simp_rw [he]
    rw [total_succ]
    constructor
    · rintro ⟨x, hx, h₁, h₂⟩
      omega
    · intro hv
      have hb := (total_le f base h).trans_lt (Nat.pow_lt_pow_right (by decide) (by omega : h < w))
      exact ⟨⟨_, hb⟩, (by change total f base h ≤ value; omega), rfl,
        (by change value - total f base h = _; omega)⟩

/-- The ordinary finite sum on the original edge range, including the empty interval. -/
theorem plays_flags (f : ℕ → Bool) (n bit : ℕ) (claim : Bool) :
    let padded := fun i => decide (i < n) && f i
    plays (fun xs => verdict padded (route n bit claim xs)) [] (flags n) ↔
      (∑ j ∈ Finset.range n, (f j).toNat).testBit bit = claim := by
  intro padded
  let w := n.size + 1
  rw [flags, plays_field]
  have hroute (x : Fin (2 ^ w)) (ys : List Bool) :
      route n bit claim (lowBits w x.val ++ ys) =
        if x.val.testBit bit = claim then walk w n.size 0 x.val ys else none := by
    have ht : (lowBits w x.val ++ ys).take w = lowBits w x.val := by
      simpa only [length_lowBits] using List.take_left (l₁ := lowBits w x.val) (l₂ := _)
    have hd : (lowBits w x.val ++ ys).drop w = ys := by
      simpa only [length_lowBits] using List.drop_left (l₁ := lowBits w x.val) (l₂ := _)
    dsimp only [w] at ht hd ⊢
    simp only [route, ht, hd, lsbValue_lowBits (n := n.size + 1) x.isLt]
  have he (x : Fin (2 ^ w)) :
      plays (fun ys => verdict padded (route n bit claim (lowBits w x.val ++ ys))) []
        (rounds w n.size) ↔ x.val.testBit bit = claim ∧ x.val = total padded 0 n.size := by
    by_cases hx : x.val.testBit bit = claim
    · simp only [hroute, hx, ↓reduceIte, true_and]
      exact plays_rounds _ _ _ _ _ (by omega)
    · simp only [hroute, hx, ↓reduceIte, false_and, verdict, plays_const]
  change (∃ x : Fin (2 ^ w), plays (fun ys => verdict padded
    (route n bit claim (lowBits w x.val ++ ys))) [] (rounds w n.size)) ↔ _
  rw [exists_congr he]
  have hb := Nat.lt_size_self n
  have hsum : total padded 0 n.size = ∑ j ∈ Finset.range n, (f j).toNat := by
    unfold total
    rw [show 2 ^ n.size = n + (2 ^ n.size - n) by omega, Finset.sum_range_add]
    simp only [Nat.zero_add]
    have h₀ : ∑ j ∈ Finset.range (2 ^ n.size - n), (padded (n + j)).toNat = 0 :=
      Finset.sum_eq_zero fun j _ => by simp [padded]
    rw [h₀, Nat.add_zero]
    exact Finset.sum_congr rfl fun j hj => by simp [padded, Finset.mem_range.mp hj]
  rw [← hsum]
  constructor
  · rintro ⟨x, hbit, hx⟩
    rwa [← hx]
  · intro hbit
    have hv := (total_le padded 0 n.size).trans_lt
      (Nat.pow_lt_pow_right (by decide) (by omega : n.size < w))
    exact ⟨⟨_, hv⟩, hbit, rfl⟩

end Turing.MultiTapeATM.IntervalCountGame
