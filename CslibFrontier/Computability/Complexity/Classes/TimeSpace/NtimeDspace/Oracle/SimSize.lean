/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.Basic
public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bound
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.InPlace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Space

/-!
# The size of the universal configurations of the simulation

A zipper of the universal machine holds only cells at positions its head has visited
(`TapeCovered`), so its encoding is linear in the number of visited positions; for binary machines
its cells are blanks, `0` and `1` (`TapeBits`). Universal steps of descriptions of binary machines
keep both properties (`stepWith_desc_tapes`). A head moving by at most one cell per step from `0`
visits every position between `0` and its current position (`natAbs_lt_card_visited`).

## References

`TapeCovered` and its lemmas restate private lemmas of
`Complexity.Computability.Machines.Turing.MultiTape.Universal.Space` (Christian Reitwiessner),
for arbitrary sequences of tape actions.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Oracle

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.Universal

/-! ### Zippers within visited positions -/

/-- The cells of the zipper `t` are at positions in `V`. -/
structure TapeCovered (t : Tape) (V : Set ℤ) : Prop where
  left : ∀ k < t.left.length, t.head - 1 - k ∈ V
  right : ∀ k < t.right.length, t.head + k ∈ V

lemma TapeCovered.mono {t : Tape} {V W : Set ℤ} (h : TapeCovered t V) (hVW : V ⊆ W) :
    TapeCovered t W :=
  ⟨fun k hk => hVW (h.left k hk), fun k hk => hVW (h.right k hk)⟩

lemma TapeCovered.blank (V : Set ℤ) : TapeCovered Universal.Tape.blank V :=
  ⟨fun k
      hk => by simp [Universal.Tape.blank] at hk, fun k hk => by simp [Universal.Tape.blank] at hk⟩

/-- An action keeps a zipper covered, if the heads before and after are covered. -/
lemma TapeCovered.apply {t : Tape} {V : Set ℤ} (h : TapeCovered t V) (hh : t.head ∈ V)
    (a : Option (Option ℕ) × SignType) (ha : (t.apply a).head ∈ V) :
    TapeCovered (t.apply a) V := by
  obtain ⟨hl, hr⟩ := h
  obtain ⟨w, m⟩ := a
  have hw : TapeCovered (w.elim t t.write) V ∧ (w.elim t t.write).head = t.head := by
    rcases w with _ | o
    · exact ⟨⟨hl, hr⟩, rfl⟩
    · refine ⟨⟨hl, fun k hk => ?_⟩, rfl⟩
      simp only [Option.elim, Universal.Tape.write, List.length_cons, List.length_tail] at hk ⊢
      rcases k with _ | k
      · simpa using hh
      · exact hr (k + 1) (by omega)
  obtain ⟨⟨hl', hr'⟩, hhd⟩ := hw
  simp only [Universal.Tape.apply] at ha ⊢
  generalize w.elim t t.write = u at *
  rcases m with _ | _ | _
  · exact ⟨hl', hr'⟩
  · have ha' : u.head - 1 ∈ V := by simpa [Universal.Tape.move] using ha
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · simp only [Universal.Tape.move, List.length_tail] at hk ⊢
      rw [show u.head - 1 - 1 - (k : ℤ) = u.head - 1 - ((k + 1 : ℕ) : ℤ) by push_cast; omega]
      exact hl' (k + 1) (by omega)
    · simp only [Universal.Tape.move, List.length_cons] at hk ⊢
      rcases k with _ | k
      · simpa using ha'
      · rw [show u.head - 1 + ((k + 1 : ℕ) : ℤ) = u.head + k by push_cast; omega]
        exact hr' k (by omega)
  · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · simp only [Universal.Tape.move, List.length_cons] at hk ⊢
      rcases k with _ | k
      · simpa [hhd] using hh
      · rw [show u.head + 1 - 1 - ((k + 1 : ℕ) : ℤ) = u.head - 1 - k by push_cast; omega]
        exact hl' k (by omega)
    · simp only [Universal.Tape.move, List.length_tail] at hk ⊢
      rw [show u.head + 1 + (k : ℤ) = u.head + ((k + 1 : ℕ) : ℤ) by push_cast; omega]
      exact hr' (k + 1) (by omega)

/-- A covered zipper holds at most as many cells as there are positions in `V`. -/
lemma TapeCovered.length_le {t : Tape} {V : Finset ℤ} (h : TapeCovered t V) :
    t.left.length + t.right.length ≤ V.card := by
  let f : ℕ → ℤ := fun k => if k < t.left.length then t.head - 1 - k
    else t.head + (k - t.left.length : ℕ)
  have := Finset.card_le_card_of_injOn f (s := Finset.range (t.left.length + t.right.length))
    (t := V) (fun k hk => by
      simp only [Finset.coe_range, Set.mem_Iio] at hk
      simp only [Finset.mem_coe, f]
      split_ifs with h'
      · exact h.left k h'
      · exact h.right _ (by omega))
    (fun a ha b hb hab => by
      simp only [Finset.coe_range, Set.mem_Iio, f] at ha hb hab
      split_ifs at hab <;> omega)
  simpa using this

/-! ### Binary cells -/

/-- The cells of the zipper `t` are blanks, `0` or `1`. -/
def TapeBits (t : Tape) : Prop := ∀ o ∈ t.left ++ t.right, o.getD 0 ≤ 1

lemma tapeBits_blank : TapeBits Universal.Tape.blank := by simp [TapeBits, Universal.Tape.blank]

lemma TapeBits.write {t : Tape} (h : TapeBits t) {o : Option ℕ} (ho : o.getD 0 ≤ 1) :
    TapeBits (t.write o) := by
  intro c hc
  simp only [Universal.Tape.write, List.mem_append, List.mem_cons] at hc
  rcases hc with hc | rfl | hc
  · exact h c (List.mem_append_left _ hc)
  · exact ho
  · exact h c (List.mem_append_right _ (List.mem_of_mem_tail hc))

lemma TapeBits.move {t : Tape} (h : TapeBits t) (m : SignType) : TapeBits (t.move m) := by
  rcases m with _ | _ | _
  · exact h
  · intro c hc
    simp only [Universal.Tape.move, List.mem_append, List.mem_cons] at hc
    rcases hc with hc | rfl | hc
    · exact h c (List.mem_append_left _ (List.mem_of_mem_tail hc))
    · cases hl : t.left with
      | nil => simp
      | cons a l => simpa using h a (by simp [hl])
    · exact h c (List.mem_append_right _ hc)
  · intro c hc
    simp only [Universal.Tape.move, Universal.Tape.read, List.mem_append, List.mem_cons] at hc
    rcases hc with (rfl | hc) | hc
    · cases hr : t.right with
      | nil => simp
      | cons a l => simpa using h a (by simp [hr])
    · exact h c (List.mem_append_left _ hc)
    · exact h c (List.mem_append_right _ (List.mem_of_mem_tail hc))

lemma TapeBits.apply {t : Tape} (h : TapeBits t) (a : TapeAct)
    (ha : ∀ o, a.1 = some o → o.getD 0 ≤ 1) : TapeBits (t.apply a) := by
  obtain ⟨w, m⟩ := a
  simp only [Universal.Tape.apply]
  refine TapeBits.move ?_ m
  rcases w with _ | o
  · exact h
  · exact h.write (ha o rfl)

/-! ### Universal steps of binary machines -/

lemma applyTapes_nil' (ts : List Tape) : applyTapes ts [] = ts := by
  cases ts <;> rfl

lemma getD_applyTapes' (ts : List Tape) (as : List TapeAct) {i : ℕ} (hi : i < ts.length) :
    (applyTapes ts as).getD i .blank = (ts.getD i .blank).apply (as.getD i (none, 0)) := by
  induction ts generalizing as i with
  | nil => simp at hi
  | cons t ts ih =>
    rcases as with _ | ⟨a, as⟩
    · rcases i with _ | i <;> simp [applyTapes, List.getD_eq_getElem?_getD] <;> rfl
    · rcases i with _ | i
      · simp [applyTapes]
      · simpa [applyTapes] using ih as (by simpa using hi)

lemma length_applyTapes' (ts : List Tape) (as : List TapeAct) :
    (applyTapes ts as).length = ts.length := by
  induction ts generalizing as with
  | nil => rfl
  | cons t ts ih => cases as <;> simp [applyTapes, ih]

section Desc

variable {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ)

/-- The transitions of the description of a binary machine write only blanks, `0` and `1`. -/
lemma desc_table_bits (tm : MultiTapeTM k Bool State) {e : Key × Act}
    (he : e ∈ (desc eS eBit tm).table) : ∀ a ∈ e.2.workTapes, ∀ o, a.1 = some o → o.getD 0 ≤ 1 := by
  obtain ⟨⟨q, i, w⟩, -, rfl⟩ := List.mem_map.mp he
  intro a ha o hao
  simp only [Act.ofAction, List.mem_ofFn] at ha
  obtain ⟨j, rfl⟩ := ha
  simp only [Action.map_workTapes, Option.map_eq_some_iff] at hao
  obtain ⟨o', -, rfl⟩ := hao
  cases o' with
  | none => simp
  | some b =>
    cases b
    · exact (by decide : Bool.toNat false ≤ 1)
    · exact (by decide : Bool.toNat true ≤ 1)

/-- **A universal step of the description of a binary machine** applies to the work tapes actions
writing only blanks, `0` and `1`. -/
lemma stepWith_desc_tapes (tm : MultiTapeTM k Bool State) (s : SCfg) (sym : Option ℕ) :
    ∃ as : List TapeAct, (∀ a ∈ as, ∀ o, a.1 = some o → o.getD 0 ≤ 1) ∧
      (stepWith (desc eS eBit tm) s sym).1.workTapes = applyTapes s.workTapes as := by
  obtain ⟨_ | q, ip, ts⟩ := s
  · exact ⟨[], by simp, (applyTapes_nil' ts).symm⟩
  · simp only [stepWith]
    split
    · exact ⟨[], by simp, (applyTapes_nil' ts).symm⟩
    · next e he =>
      exact ⟨e.2.workTapes, desc_table_bits eS tm (List.mem_of_find?_eq_some he), rfl⟩

end Desc

/-! ### Visited positions -/

/-- A sequence of positions from `0`, moving by at most one per step, visits every position between
`0` and its current position. -/
lemma natAbs_lt_card_visited (f : ℕ → ℤ) (h0 : f 0 = 0) (hstep : ∀ j, |f (j + 1) - f j| ≤ 1)
    (t : ℕ) : (f t).natAbs < (Finset.univ.image fun n : Fin (t + 1) => f n).card := by
  have hmem : ∀ t z, min 0 (f t) ≤ z ∧ z ≤ max 0 (f t) →
      z ∈ Finset.univ.image fun n : Fin (t + 1) => f n := by
    intro t
    induction t with
    | zero =>
      intro z hz
      rw [h0] at hz
      exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp [h0]; omega⟩
    | succ t ih =>
      intro z hz
      have hs := hstep t
      rw [abs_le] at hs
      by_cases hzt : z = f (t + 1)
      · exact Finset.mem_image.mpr ⟨Fin.last _, Finset.mem_univ _, by simp [hzt]⟩
      · obtain ⟨n, -, hn⟩ := Finset.mem_image.mp (ih z (by omega))
        exact Finset.mem_image.mpr ⟨n.castSucc, Finset.mem_univ _, by simpa using hn⟩
  have := Finset.card_le_card (s := Finset.Icc (min 0 (f t)) (max 0 (f t)))
    (t := Finset.univ.image fun n : Fin (t + 1) => f n) fun z hz =>
      hmem t z (Finset.mem_Icc.mp hz)
  rw [Int.card_Icc] at this
  omega

/-! ### The size of a configuration -/

lemma length_eTape_le_card {t : Tape} {V : Finset ℤ} (hc : TapeCovered t V)
    (hh : t.head.natAbs < V.card) (hv : TapeBits t) : (eTape t).length ≤ 21 * V.card := by
  have h₁ := length_encIntUnary_le t.head
  have h₂ := length_cells_le (D := 1) fun o ho => hv o (List.mem_append_left t.right ho)
  have h₃ := length_cells_le (D := 1) fun o ho => hv o (List.mem_append_right t.left ho)
  have h₄ := hc.length_le
  simp only [eTape_apply, length_encPair]
  omega

lemma length_encList_eTape (l : List Tape) :
    (encList eTape l).length = ∑ i ∈ Finset.range l.length,
      (2 * (eTape (l.getD i Universal.Tape.blank)).length + 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [encList_cons, List.length_append, length_frame, ih, List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega

/-- **The size of a universal configuration** whose `k` zippers are covered by visited positions
`V i` and hold bits. -/
theorem length_eCfg_le {k : ℕ} (s : SCfg) (V : Fin k → Finset ℤ) (hk : s.workTapes.length = k)
    (hc : ∀ i : Fin k, TapeCovered (s.workTapes.getD i Universal.Tape.blank) (V i))
    (hh : ∀ i : Fin k, (s.workTapes.getD i Universal.Tape.blank).head.natAbs < (V i).card)
    (hb : ∀ i : Fin k, TapeBits (s.workTapes.getD i Universal.Tape.blank)) :
    (eCfg s).length ≤ 2 * (eSym s.state).length + 2 * (encNat s.inputPos).length + 2 +
      (k + 42 * ∑ i, (V i).card) := by
  have ht : (encList eTape s.workTapes).length ≤ k + 42 * ∑ i, (V i).card := by
    rw [length_encList_eTape, hk, Finset.sum_range (fun i => 2 * (eTape (s.workTapes.getD i
      Universal.Tape.blank)).length + 1), Finset.mul_sum]
    calc ∑ i : Fin k, (2 * (eTape (s.workTapes.getD i Universal.Tape.blank)).length + 1)
        ≤ ∑ i : Fin k, (1 + 42 * (V i).card) := Finset.sum_le_sum fun i _ => by
          have := length_eTape_le_card (hc i) (hh i) (hb i)
          omega
      _ = k + ∑ i : Fin k, 42 * (V i).card := by
          rw [Finset.sum_add_distrib]; simp
  simp only [eCfg_apply, length_encPair]
  omega

end Cslib.Complexity.NtimeDspace.Oracle
