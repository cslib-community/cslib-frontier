/-
Copyright (c) 2026 Stefan Langerman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Langerman
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Quicksort.LocalStack

/-!
# Representation invariant for the local quicksort stack

Frame slots increase by two from the prepared stack base. The list is in bottom-to-top order
and contains only the numeric boundaries, which are used to state the correctness invariant.
-/

public section

namespace Cslib.Algorithms.WordRAM.Quicksort

open Cslib.WordRAM Reg

/-- The live frames and the next free slot encode the pending ranges. -/
structure StackRealizes {n : ℕ} (x : Local.Data localModel n 16 16) (base : ℕ)
    (pending : List (ℕ × ℕ)) : Prop where
  top : ∃ slot : Fin n, x.addr sp = some slot ∧ slot.val = base + 2 * pending.length
  frames : ∀ i : Fin pending.length, ∃ (slot start stop : Fin n) (h : slot.val + 1 < n),
    slot.val = base + 2 * i.val ∧
    start.val = pending[i.val].1 ∧ stop.val = pending[i.val].2 ∧
    x.refs slot = some start ∧ x.refs ⟨slot.val + 1, h⟩ = some stop ∧
    x.values slot = stop.val - start.val

variable {n base : ℕ} {x y : Local.Data localModel n 16 16}
variable {S : List (ℕ × ℕ)}

/-- The backing cells below the stack top determine the frame contents. -/
theorem StackRealizes.frames_congr (h : StackRealizes x base S)
    (hsp : y.addr sp = x.addr sp)
    (hvalues : ∀ a : Fin n, base ≤ a.val → a.val < base + 2 * S.length →
      y.values a = x.values a)
    (hrefs : ∀ a : Fin n, base ≤ a.val → a.val < base + 2 * S.length →
      y.refs a = x.refs a) : StackRealizes y base S := by
  refine ⟨hsp ▸ h.top, ?_⟩
  intro i
  obtain ⟨slot, start, stop, hb, hs, ha, hz, hf, hl, hv⟩ := h.frames i
  have hi := i.isLt
  exact ⟨slot, start, stop, hb, hs, ha, hz, (hrefs slot (by omega) (by omega)).trans hf,
    (hrefs _ (by dsimp; omega) (by dsimp; omega)).trans hl,
    (hvalues slot (by omega) (by omega)).trans hv⟩

/-- Expose the top frame of a nonempty stack in the format needed by the iteration theorem. -/
theorem StackRealizes.last {a b : ℕ} (h : StackRealizes x base (S ++ [(a, b)])) :
    ∃ (slot start stop : Fin n) (hb : slot.val + 2 < n),
      slot.val = base + 2 * S.length ∧ start.val = a ∧ stop.val = b ∧
      x.addr sp = some ⟨slot.val + 2, hb⟩ ∧ x.refs slot = some start ∧
      x.refs ⟨slot.val + 1, by omega⟩ = some stop ∧ x.values slot = stop.val - start.val := by
  obtain ⟨top, ht, htop⟩ := h.top
  obtain ⟨slot, start, stop, hb, hs, ha, hz, hf, hl, hv⟩ :=
    h.frames ⟨S.length, by simp⟩
  have hlen : (S ++ [(a,b)]).length = S.length + 1 := by simp
  change slot.val = base + 2 * S.length at hs
  have he : top.val = slot.val + 2 := by omega
  have hb' : slot.val + 2 < n := he ▸ top.isLt
  have ht' : top = (⟨slot.val + 2, hb'⟩ : Fin n) := Fin.ext he
  refine ⟨slot, start, stop, hb', hs, ?_, ?_, ht.trans (congrArg some ht'), hf, hl, hv⟩
  · simpa using ha
  · simpa using hz

/-- Replacing the cursor by the first slot of the top frame drops that frame from the live stack. -/
theorem StackRealizes.pop {range : ℕ × ℕ} (h : StackRealizes x base (S ++ [range]))
    (slot : Fin n) (hslot : slot.val = base + 2 * S.length)
    (hsp : y.addr sp = some slot) (hv : y.values = x.values) (hr : y.refs = x.refs) :
    StackRealizes y base S := by
  refine ⟨⟨slot, hsp, hslot⟩, ?_⟩
  intro i
  have hi : i.val < (S ++ [range]).length := by
    have := i.isLt
    simp only [List.length_append, List.length_singleton]
    omega
  obtain ⟨a, l, r, hb, ha, hl, hright, hf, hlast, hval⟩ := h.frames ⟨i.val, hi⟩
  refine ⟨a, l, r, hb, ha, ?_, ?_, hr ▸ hf, hr ▸ hlast, hv ▸ hval⟩
  · simpa only [List.getElem_append_left i.isLt] using hl
  · simpa only [List.getElem_append_left i.isLt] using hright

/-- The conditional enqueue extends precisely the live frame sequence. -/
private theorem StackRealizes.enqueue (h : StackRealizes x base S) (start stop slot : Fin n)
    (hroom : slot.val + 2 < n) (hslot : x.addr sp = some slot) :
    StackRealizes (enqueueState x start stop slot hroom) base
      (if 1 < stop.val - start.val then S ++ [(start.val, stop.val)] else S) := by
  obtain ⟨top, htop, hv⟩ := h.top
  have hts : top = slot := Option.some.inj (htop.symm.trans hslot)
  subst top
  have hslotAdd := enqueueState_top x start stop slot hroom hslot
  by_cases hn : 1 < stop.val - start.val
  · rw [ite_eq_left hn]
    refine ⟨⟨⟨slot.val + 2, hroom⟩, by simpa only [ite_eq_left hn] using hslotAdd, ?_⟩, ?_⟩
    · simp only [List.length_append, List.length_singleton]
      omega
    · intro i
      by_cases hi : i.val < S.length
      · obtain ⟨old, a, b, hb, hOld, ha, hB, hFirst, hLast, hLen⟩ := h.frames ⟨i.val, hi⟩
        change old.val = base + 2 * i.val at hOld
        have hOldLt : old.val + 1 < slot.val := by omega
        have hne : old ≠ slot := Fin.ne_of_lt (by omega)
        have hne₂ : (⟨old.val + 1, hb⟩ : Fin n) ≠ slot := Fin.ne_of_lt hOldLt
        have hne₃ : old ≠ (⟨slot.val + 1, by omega⟩ : Fin n) :=
          Fin.ne_of_lt (show old.val < slot.val + 1 by omega)
        have hne₄ : (⟨old.val + 1, hb⟩ : Fin n) ≠ (⟨slot.val + 1, by omega⟩ : Fin n) :=
          Fin.ne_of_lt (show old.val + 1 < slot.val + 1 by omega)
        exact ⟨old, a, b, hb, hOld, by simpa only [List.getElem_append_left hi] using ha,
          by simpa only [List.getElem_append_left hi] using hB,
          by simpa [enqueueState, hn, hne, hne₃] using hFirst,
          by simpa [enqueueState, hn, hne₂, hne₄] using hLast,
          by simpa [enqueueState, hn, hne] using hLen⟩
      · have his : i.val = S.length := by
          have hh := i.isLt
          simp only [List.length_append, List.length_singleton] at hh
          omega
        have he : slot ≠ (⟨slot.val + 1, by omega⟩ : Fin n) :=
          Fin.ne_of_lt (Nat.lt_succ_self _)
        exact ⟨slot, start, stop, by omega, by simpa only [his] using hv,
          by simp [his], by simp [his], by simp [enqueueState, hn, he],
          by simp [enqueueState, hn], by simp [enqueueState, hn]⟩
  · simpa only [enqueueState, ite_eq_right hn] using h

/-- A stack enqueue preserves all payload cells below the first free frame. -/
private theorem enqueueState_values_below (x : Local.Data localModel n 16 16)
    (start stop slot a : Fin n) (hroom : slot.val + 2 < n) (ha : a.val < slot.val) :
    (enqueueState x start stop slot hroom).values a = x.values a := by
  have hne : a ≠ slot := Fin.ne_of_lt ha
  by_cases hn : 1 < stop.val - start.val <;> simp [enqueueState, hn, hne]

/-- The live stack has a unique list of ranges. -/
theorem StackRealizes.unique {T : List (ℕ × ℕ)} (hS : StackRealizes x base S)
    (hT : StackRealizes x base T) : S = T := by
  obtain ⟨topS, hspS, htS⟩ := hS.top
  obtain ⟨topT, hspT, htT⟩ := hT.top
  have he : topS = topT := Option.some.inj (hspS.symm.trans hspT)
  have hlen : S.length = T.length := by
    have he' := congrArg Fin.val he
    omega
  refine List.ext_getElem hlen fun i hi hj => ?_
  obtain ⟨s, a, b, hs, hpos, ha, hb, hfirst, hlast, _⟩ := hS.frames ⟨i, hi⟩
  obtain ⟨t, c, d, ht, hpos', hc, hd, hfirst', hlast', _⟩ := hT.frames ⟨i, hj⟩
  have hst : s = t := Fin.ext (hpos.trans hpos'.symm)
  subst t
  have hac := Option.some.inj (hfirst.symm.trans hfirst')
  have hbd := Option.some.inj (hlast.symm.trans hlast')
  exact Prod.ext (ha.symm.trans (hac ▸ hc)) (hb.symm.trans (hbd ▸ hd))

/-- The list effect of a conditional enqueue. -/
@[expose] def queueRange (S : List (ℕ × ℕ)) (start stop : ℕ) : List (ℕ × ℕ) :=
  if start + 2 ≤ stop then S ++ [(start, stop)] else S

/-- The new live stack and the data preserved by a pair of conditional pushes. -/
structure StackExtension (x out : Local.Data localModel n 16 16) (base : ℕ)
    (pending : List (ℕ × ℕ)) (slot : Fin n) : Prop where
  /-- The extended sequence of pending ranges. -/
  stack : StackRealizes out base pending
  /-- Payloads below the first free slot are untouched. -/
  valuesBelow : ∀ j : Fin n, j.val < slot.val → out.values j = x.values j
  /-- The stack base register is unchanged. -/
  stackBase_eq : out.addr stackHi = x.addr stackHi
  /-- The measured lengths and other scalar registers are unchanged. -/
  scalars_eq : out.scalars = x.scalars

/-- Two enqueues change only the stack and its cursor. -/
theorem StackRealizes.enqueuePair (h : StackRealizes x base S) (a b c d slot : Fin n)
    (hroom : slot.val + 4 < n) (hslot : x.addr sp = some slot) :
    StackExtension x (enqueuePairState x a b c d slot hroom) base
      (queueRange (queueRange S a.val b.val) c.val d.val) slot := by
  have hroom₁ : slot.val + 2 < n := by omega
  let u := enqueueState x a b slot hroom₁
  let next := afterEnqueue a b slot hroom₁
  have hroom₂ : next.val + 2 < n := by unfold next afterEnqueue; split <;> omega
  have h₁ := h.enqueue a b slot hroom₁ hslot
  have htop : u.addr sp = some next := enqueueState_top x a b slot hroom₁ hslot
  have h₂ := h₁.enqueue c d next hroom₂ htop
  have h₁c : (1 < b.val - a.val) ↔ a.val + 2 ≤ b.val := by omega
  have h₂c : (1 < d.val - c.val) ↔ c.val + 2 ≤ d.val := by omega
  have f₁ := enqueueState_frame x a b slot hroom₁
  have f₂ := enqueueState_frame u c d next hroom₂
  refine ⟨?_, ?_, (f₂.1 _ (by decide)).trans (f₁.1 _ (by decide)), f₂.2.trans f₁.2⟩
  · change StackRealizes (enqueueState u c d next hroom₂) base _
    simpa only [queueRange, h₁c, h₂c] using h₂
  · intro j hj
    exact (enqueueState_values_below u c d next j hroom₂
      (hj.trans_le (le_afterEnqueue a b slot hroom₁))).trans
      (enqueueState_values_below x a b slot j hroom₁ hj)

end Cslib.Algorithms.WordRAM.Quicksort
