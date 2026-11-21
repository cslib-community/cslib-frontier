/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SparseModeTuple
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Length of the sparse mode encoding

For `m` colours and total weighted multiplicity at most `p`, the sparse tuple occupies
`O(√(mp) + 1)` bits. The position gaps are charged in reverse rank order and the multiplicities
in forward rank order. Cauchy–Schwarz then combines the row lengths.
-/

public section

namespace Cslib.SparseModeTuple

open BitString Finset

/-- Weighted multiplicity of the remaining entries after `offset` weight positions. -/
@[expose] def entryMass (offset : ℕ) : List Entry → ℕ
  | [] => 0
  | e :: es =>
    let weight := offset + (e.skip + 1)
    weight * (e.extra + 1) + entryMass weight es

/-- The sum of the positive weights times their exponents across all occupied rows. -/
@[expose] def mass (rows : List Row) : ℕ :=
  (rows.map fun r => entryMass 0 (r.first :: r.rest)).sum

/-- The number of colours up through the last occupied colour. -/
@[expose] def colours (rows : List Row) : ℕ := (rows.map fun r => r.skip + 1).sum

/-- Dense weighted mass for entries with successive weights starting at `start + 1`. -/
@[expose] def rankMass (start : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => (start + 1) * x + rankMass (start + 1) xs

private theorem sum_getD {α : Type} (d : α) (f : α → ℕ) (l : List α) :
    ∑ i ∈ range l.length, f (l.getD i d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons, sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]

/-- The dense mass is the finite sum of each exponent times its positive weight. -/
theorem rankMass_eq (l : List ℕ) (start : ℕ) : rankMass start l =
    ∑ i ∈ range l.length, (start + i + 1) * l.getD i 0 := by
  induction l generalizing start with
  | nil => simp [rankMass]
  | cons x xs ih =>
    rw [rankMass, ih, List.length_cons, sum_range_succ', add_comm]
    simp only [Nat.add_zero, List.getD_cons_succ, List.getD_cons_zero]
    congr 1
    apply sum_congr rfl
    intro i _
    congr 1
    omega

private def gammaCost (l : List ℕ) : ℕ := (l.map fun n => (eliasGamma n).length).sum

private theorem gammaCost_le (l : List ℕ) (hl : ∀ x ∈ l, 0 < x) :
    gammaCost l ≤ 8 * Nat.sqrt (2 * rankMass 0 l) := by
  have hpos (i) (hi : i ∈ range l.length) : 0 < l.getD i 0 := by
    have hi' := mem_range.mp hi
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
      using hl _ (List.getElem_mem hi')
  have h := sum_length_eliasGamma_le (range l.length) (fun i => l.getD i 0) hpos
  rw [sum_getD 0 (fun n => (eliasGamma n).length) l] at h
  simpa only [gammaCost, rankMass_eq, Nat.zero_add] using h

private theorem rankMass_concat (l : List ℕ) (x start : ℕ) :
    rankMass start (l ++ [x]) = rankMass start l + (start + l.length + 1) * x := by
  induction l generalizing start with
  | nil => simp [rankMass]
  | cons y ys ih =>
    simp only [List.cons_append, rankMass, ih, List.length_cons]
    ring

private theorem rankMass_mult_le (es : List Entry) {start offset : ℕ} (h : start ≤ offset) :
    rankMass start (es.map fun e => e.extra + 1) ≤ entryMass offset es := by
  induction es generalizing start offset with
  | nil => simp [entryMass, rankMass]
  | cons e es ih =>
    simp only [entryMass, List.map_cons, rankMass]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (ih (by omega))

private theorem rankMass_gaps_le (es : List Entry) (offset : ℕ) :
    es.length * offset + rankMass 0 (es.map fun e => e.skip + 1).reverse ≤
      entryMass offset es := by
  induction es generalizing offset with
  | nil => simp [entryMass, rankMass]
  | cons e es ih =>
    have h := ih (offset + (e.skip + 1))
    simp only [entryMass, List.length_cons, List.map_cons, List.reverse_cons, rankMass_concat,
      Nat.zero_add, List.length_reverse, List.length_map]
    nlinarith

private theorem length_le_gammaCost (l : List ℕ) : l.length ≤ gammaCost l := by
  induction l with
  | nil => simp [gammaCost]
  | cons n ns ih => simp [gammaCost] at ih ⊢; omega

private theorem sum_entry_lengths (es : List Entry) :
    (es.flatMap encodeEntry).length =
      gammaCost (es.map fun e => e.skip + 1) + gammaCost (es.map fun e => e.extra + 1) := by
  induction es with
  | nil => simp [gammaCost]
  | cons e es ih => simp [encodeEntry, gammaCost] at ih ⊢; omega

private theorem row_length_le (r : Row) :
    (encodeRow r).length ≤ (eliasGamma (r.skip + 1)).length +
      40 * Nat.sqrt (2 * entryMass 0 (r.first :: r.rest)) := by
  let es := r.first :: r.rest
  let gs := es.map fun e => e.skip + 1
  let ms := es.map fun e => e.extra + 1
  have hm : gammaCost ms ≤ 8 * Nat.sqrt (2 * entryMass 0 es) :=
    (gammaCost_le ms (by simp [ms])).trans (Nat.mul_le_mul_left _ (Nat.sqrt_le_sqrt
      (Nat.mul_le_mul_left _ (rankMass_mult_le es le_rfl))))
  have hg' := gammaCost_le gs.reverse (by simp [gs])
  have hg : gammaCost gs ≤ 8 * Nat.sqrt (2 * entryMass 0 es) := by
    have hg0 : gammaCost gs.reverse = gammaCost gs := by simp [gammaCost]
    rw [hg0] at hg'
    exact hg'.trans (Nat.mul_le_mul_left _ (Nat.sqrt_le_sqrt (Nat.mul_le_mul_left _
      (by simpa [gs] using rankMass_gaps_le es 0))))
  have hr : es.length ≤ gammaCost ms := by simpa [ms] using length_le_gammaCost ms
  have hlog := Nat.log_le_self 2 es.length
  have hn : es.length = r.rest.length + 1 := rfl
  have hd : (encodeRow r).length = (eliasGamma (r.skip + 1)).length +
      (2 * Nat.log 2 es.length + 1) + gammaCost gs + gammaCost ms := by
    simp only [encodeRow, List.length_append, sum_entry_lengths, length_eliasGamma]
    dsimp [es, gs, ms]
    omega
  rw [hd]
  change _ ≤ _ + 40 * Nat.sqrt (2 * entryMass 0 es)
  omega

private theorem sum_sqrt_le (l : List ℕ) :
    (l.map fun n => Nat.sqrt (2 * n)).sum ≤ Nat.sqrt (2 * l.length * l.sum) := by
  apply Nat.le_sqrt'.mpr
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul (range l.length)
    (f := fun _ => 1) (g := fun i => 2 * l.getD i 0) (r := fun i => Nat.sqrt (2 * l.getD i 0))
    (by intros; omega) (by intros; omega) (fun i _ => by simpa using Nat.sqrt_le' (2 * l.getD i 0))
  rw [sum_getD 0 (fun n => Nat.sqrt (2 * n)) l, ← mul_sum] at h
  have hl : ∑ i ∈ range l.length, l.getD i 0 = l.sum := by simpa using sum_getD 0 id l
  rw [hl] at h
  simpa only [sum_const, card_range, nsmul_eq_mul, Nat.cast_id, mul_one, mul_left_comm,
    mul_assoc] using h

private theorem gammaCost_le_sum_sqrt (l : List ℕ) (hl : ∀ x ∈ l, 0 < x) :
    gammaCost l ≤ 8 * (l.map fun n => Nat.sqrt (2 * n)).sum := by
  induction l with
  | nil => simp [gammaCost]
  | cons x xs ih =>
    have hx : 0 < x := hl x (by simp)
    have hsingle := sum_length_eliasGamma_le ({0} : Finset ℕ) (fun _ => x) (by simp [hx])
    simp only [sum_singleton, Nat.zero_add, one_mul] at hsingle
    have hxs := ih (fun y hy => hl y (by simp [hy]))
    change (eliasGamma x).length + gammaCost xs ≤
      8 * (Nat.sqrt (2 * x) + (xs.map fun n => Nat.sqrt (2 * n)).sum)
    omega

private theorem flat_length_le (rows : List Row) :
    (rows.flatMap encodeRow).length ≤ gammaCost (rows.map fun r => r.skip + 1) +
      40 * (rows.map fun r => Nat.sqrt (2 * entryMass 0 (r.first :: r.rest))).sum := by
  induction rows with
  | nil => simp [gammaCost]
  | cons r rs ih =>
    have hr := row_length_le r
    change (List.length (encodeRow r ++ rs.flatMap encodeRow)) ≤
      ((eliasGamma (r.skip + 1)).length + gammaCost (rs.map fun r => r.skip + 1)) +
        40 * (Nat.sqrt (2 * entryMass 0 (r.first :: r.rest)) +
          (rs.map fun r => Nat.sqrt (2 * entryMass 0 (r.first :: r.rest))).sum)
    rw [List.length_append]
    omega

/-- Every fixed-width guess of this length suffices for a sparse exponent tuple with
`m` available colours and total weight at most `p`. -/
theorem length_encode_le (rows : List Row) {m p : ℕ}
    (hc : colours rows ≤ m) (hp : mass rows ≤ p) :
    (encode rows).length ≤ 64 * Nat.sqrt (2 * m * p) + 3 := by
  let gs := rows.map fun r => r.skip + 1
  let ws := rows.map fun r => entryMass 0 (r.first :: r.rest)
  have hrows : rows.length ≤ colours rows ∧ rows.length ≤ mass rows := by
    clear hc hp gs ws
    induction rows with
    | nil => simp [mass, colours]
    | cons r rs ih =>
      have hr : 0 < entryMass 0 (r.first :: r.rest) := by
        simp only [entryMass, Nat.zero_add]; positivity
      simp only [colours, mass, List.map_cons, List.length_cons, List.sum_cons] at ih ⊢
      omega
  have hw : (ws.map fun n => Nat.sqrt (2 * n)).sum ≤ Nat.sqrt (2 * m * p) := by
    refine (sum_sqrt_le ws).trans (Nat.sqrt_le_sqrt ?_)
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by simpa [ws] using hrows.1.trans hc)) hp
  have hg : gammaCost gs ≤ 8 * Nat.sqrt (2 * m * p) := by
    refine (gammaCost_le_sum_sqrt gs (by simp [gs])).trans (Nat.mul_le_mul_left _
      ((sum_sqrt_le gs).trans (Nat.sqrt_le_sqrt ?_)))
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hrows.2.trans hp)) hc
    calc
      2 * gs.length * gs.sum ≤ 2 * p * m := by simpa only [gs, List.length_map, colours] using h
      _ = 2 * m * p := by ac_rfl
  have hl : rows.length ≤ gammaCost gs := by simpa [gs] using length_le_gammaCost gs
  have hf := flat_length_le rows
  change (rows.flatMap encodeRow).length ≤ gammaCost gs +
    40 * (rows.map fun r => Nat.sqrt (2 * entryMass 0 (r.first :: r.rest))).sum at hf
  simp only [ws, List.map_map, Function.comp_def] at hw
  have hlog := Nat.log_le_self 2 (rows.length + 1)
  simp only [encode, List.length_append, length_eliasGamma]
  omega

end Cslib.SparseModeTuple
