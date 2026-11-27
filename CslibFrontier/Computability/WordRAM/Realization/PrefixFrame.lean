/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.ListArray
public import CslibFrontier.DataStructure.Memory.Spec
import Mathlib.Data.List.GetD

/-!
# Framing allocated Word-RAM memory

`PreservesBelow` and `FrameOutsideRange` describe the cells retained across memory states with
nondecreasing allocation frontiers. `HoldsIn` combines a contiguous list representation with
its allocation bound, so the same assertion supplies both safe addresses and their contents.

Allocation and update rules propagate these predicates through individual memory operations.
-/

public section

namespace Cslib.WordRAM.Realization

open Cslib.WordRAM Cslib.DataStructure

/-! ### Monotone memory preservation and materialized list blocks -/

/-- `s₁` extends `s₀`'s frontier monotonically while keeping every cell below `F` unchanged. -/
@[expose] def PreservesBelow (F : ℕ) (s₀ s₁ : Memory.State) : Prop :=
  F ≤ s₀.frontier ∧ s₀.frontier ≤ s₁.frontier ∧ ∀ a < F, s₁.mem a = s₀.mem a

theorem PreservesBelow.refl {F : ℕ} {s : Memory.State} (hF : F ≤ s.frontier) :
    PreservesBelow F s s :=
  ⟨hF, le_rfl, fun _ _ => rfl⟩

theorem PreservesBelow.mono_bound {F₁ F₂ : ℕ} {s₀ s₁ : Memory.State}
    (h : PreservesBelow F₂ s₀ s₁) (hle : F₁ ≤ F₂) : PreservesBelow F₁ s₀ s₁ :=
  ⟨hle.trans h.1, h.2.1, fun a ha => h.2.2 a (lt_of_lt_of_le ha hle)⟩

theorem PreservesBelow.trans {F : ℕ} {s₀ s₁ s₂ : Memory.State}
    (h₁ : PreservesBelow F s₀ s₁) (h₂ : PreservesBelow F s₁ s₂) :
    PreservesBelow F s₀ s₂ :=
  ⟨h₁.1, h₁.2.1.trans h₂.2.1, fun a ha => (h₂.2.2 a ha).trans (h₁.2.2 a ha)⟩

theorem preservesBelow_write {F a v : ℕ} {s : Memory.State}
    (hF : F ≤ a) (ha : a < s.frontier) :
    PreservesBelow F s ⟨Function.update s.mem a v, s.frontier⟩ :=
  ⟨by omega, le_rfl, fun x hx => Function.update_of_ne (by omega) v s.mem⟩

theorem preservesBelow_alloc (s : Memory.State) (k : ℕ) :
    PreservesBelow s.frontier s ((Memory.spec 0).clientState s (Memory.alloc k)) := by
  refine ⟨le_rfl, Nat.le_add_right _ _, fun a ha => ?_⟩
  change clear s.mem s.frontier k a = s.mem a
  exact clear_of_not_owns (by dsimp only [Block.Owns]; omega)

theorem preservesBelow_allocDirty (s : Memory.State) (k : ℕ) :
    PreservesBelow s.frontier s ((Memory.spec 0).clientState s (Memory.allocDirty k)) :=
  ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩

/-- A step preserving all allocated cells of the intermediate state composes with a
prefix frame from the original state. -/
theorem PreservesBelow.trans_frontier {F : ℕ} {s₀ s₁ s₂ : Memory.State}
    (h₁ : PreservesBelow F s₀ s₁) (h₂ : PreservesBelow s₁.frontier s₁ s₂) :
    PreservesBelow F s₀ s₂ :=
  h₁.trans (h₂.mono_bound (h₁.1.trans h₁.2.1))

/-- `xs` is stored contiguously starting at `base` within `s`'s allocated frontier. -/
@[expose] def HoldsIn (base : ℕ) (xs : List ℕ) (s : Memory.State) : Prop :=
  base + xs.length ≤ s.frontier ∧ Block.HoldsList base xs s.mem

theorem HoldsIn.mono {base : ℕ} {xs : List ℕ} {F : ℕ} {s₀ s₁ : Memory.State}
    (h : HoldsIn base xs s₀) (hF : base + xs.length ≤ F) (hp : PreservesBelow F s₀ s₁) :
    HoldsIn base xs s₁ :=
  ⟨h.1.trans hp.2.1, h.2.frame (fun a _ ha => hp.2.2 a (lt_of_lt_of_le ha hF))⟩

theorem HoldsIn.mono_frontier {base : ℕ} {xs : List ℕ} {s₀ s₁ : Memory.State}
    (h : HoldsIn base xs s₀) (hp : PreservesBelow s₀.frontier s₀ s₁) :
    HoldsIn base xs s₁ :=
  h.mono h.1 hp

theorem HoldsIn.get {base : ℕ} {xs : List ℕ} {s : Memory.State}
    (h : HoldsIn base xs s) (i : ℕ) (hi : i < xs.length) :
    s.mem (base + i) = xs[i] :=
  h.2.get i hi

theorem HoldsIn.nil {base : ℕ} {s : Memory.State} (h : base ≤ s.frontier) :
    HoldsIn base [] s :=
  ⟨by simpa only [List.length_nil, Nat.add_zero] using h, Block.holdsList_nil base s.mem⟩

theorem HoldsIn.cons_iff {base a : ℕ} {xs : List ℕ} {s : Memory.State} :
    HoldsIn base (a :: xs) s ↔
      base + 1 + xs.length ≤ s.frontier ∧ s.mem base = a ∧ HoldsIn (base + 1) xs s := by
  simp only [HoldsIn, List.length_cons, Block.holdsList_cons_iff]
  exact ⟨fun ⟨hb, hm, hr⟩ => ⟨by omega, hm, ⟨by omega, hr⟩⟩,
    fun ⟨hb, hm, ⟨_, hr⟩⟩ => ⟨by omega, hm, hr⟩⟩

/-- A nonempty represented list has a readable head cell and a represented tail. -/
theorem HoldsIn.cons {base x : ℕ} {xs : List ℕ} {s : Memory.State}
    (h : HoldsIn base (x :: xs) s) :
    base < s.frontier ∧ s.mem base = x ∧ HoldsIn (base + 1) xs s := by
  obtain ⟨hbound, hhead, htail⟩ := HoldsIn.cons_iff.mp h
  exact ⟨(Nat.lt_succ_self base).trans_le ((Nat.le_add_right _ _).trans hbound), hhead, htail⟩

theorem HoldsIn.append_iff {base : ℕ} {xs ys : List ℕ} {s : Memory.State} :
    HoldsIn base (xs ++ ys) s ↔
      HoldsIn base xs s ∧ HoldsIn (base + xs.length) ys s := by
  simp only [HoldsIn, List.length_append, Block.holdsList_append_iff]
  exact ⟨fun ⟨hb, hx, hy⟩ => ⟨⟨by omega, hx⟩, ⟨by omega, hy⟩⟩,
    fun ⟨⟨_, hx⟩, ⟨hby, hy⟩⟩ => ⟨by omega, hx, hy⟩⟩

theorem HoldsIn.drop {base : ℕ} {xs : List ℕ} {s : Memory.State}
    (h : HoldsIn base xs s) (k : ℕ) (hk : k ≤ xs.length) :
    HoldsIn (base + k) (xs.drop k) s := by
  rw [← List.take_append_drop k xs, HoldsIn.append_iff, List.length_take_of_le hk] at h
  exact h.2

theorem holdsIn_init (words : List ℕ) : HoldsIn 1 words (Memory.State.init words) := by
  refine ⟨le_of_eq (Nat.add_comm 1 words.length), fun i => ?_⟩
  change (Data.init (r := 0) words).mem (1 + i.val) = words[i.val]
  rw [Nat.add_comm 1, Data.init_mem_succ, List.getD_eq_getElem _ 0 i.isLt]

theorem holdsIn_alloc_zero (s : Memory.State) (k : ℕ) :
    HoldsIn s.frontier (List.replicate k 0) ((Memory.spec 0).clientState s (Memory.alloc k)) := by
  change HoldsIn s.frontier (List.replicate k 0) ⟨clear s.mem s.frontier k, s.frontier + k⟩
  refine ⟨by simp, fun i => ?_⟩
  have hi : i.val < k := by simpa only [List.length_replicate] using i.isLt
  change clear s.mem s.frontier k (s.frontier + i.val) = (List.replicate k 0)[i.val]
  rw [List.getElem_replicate]
  exact Block.realizes_clear s.mem s.frontier k ⟨i.val, hi⟩

theorem holdsIn_set {base idx v : ℕ} {xs : List ℕ} {s : Memory.State}
    (h : HoldsIn base xs s) :
    HoldsIn base (xs.set idx v) ⟨Function.update s.mem (base + idx) v, s.frontier⟩ := by
  refine ⟨by simpa only [List.length_set] using h.1, fun i => ?_⟩
  have hi : i.val < xs.length := by simpa only [List.length_set] using i.isLt
  change Function.update s.mem (base + idx) v (base + i.val) = (xs.set idx v)[i.val]
  by_cases heq : i.val = idx
  · simp only [heq, Function.update_self, List.getElem_set_self]
  · rw [Function.update_of_ne (by omega), List.getElem_set_ne (Ne.symm heq)]
    exact h.get i.val hi

theorem holdsIn_write_outside {base a v : ℕ} {xs : List ℕ} {s : Memory.State}
    (h : HoldsIn base xs s) (hout : a < base ∨ base + xs.length ≤ a) :
    HoldsIn base xs ⟨Function.update s.mem a v, s.frontier⟩ :=
  ⟨h.1, h.2.frame (fun _ _ _ => Function.update_of_ne (by omega) v s.mem)⟩

theorem holdsIn_append_one {base v : ℕ} {xs : List ℕ} {s : Memory.State}
    (h : HoldsIn base xs s) (hbound : base + xs.length + 1 ≤ s.frontier) :
    HoldsIn base (xs ++ [v]) ⟨Function.update s.mem (base + xs.length) v, s.frontier⟩ :=
  ⟨by simp only [List.length_append, List.length_singleton]; omega, h.2.append_one v⟩

/-! ### Frames around a writable interval -/

/-- Memory framing invariant: `s₁` extends `s₀`'s frontier and preserves every previously
allocated address outside `[lo, hi)`. -/
@[expose] def FrameOutsideRange (lo hi : ℕ) (s₀ s₁ : Memory.State) : Prop :=
  s₀.frontier ≤ s₁.frontier ∧
  ∀ x < s₀.frontier, (x < lo ∨ hi ≤ x) → s₁.mem x = s₀.mem x

theorem FrameOutsideRange.refl (lo hi : ℕ) (s : Memory.State) :
    FrameOutsideRange lo hi s s :=
  ⟨le_rfl, fun _ _ _ => rfl⟩

theorem FrameOutsideRange.of_preservesBelow (lo hi : ℕ) {s₀ s₁ : Memory.State}
    (hp : PreservesBelow s₀.frontier s₀ s₁) :
    FrameOutsideRange lo hi s₀ s₁ :=
  ⟨hp.2.1, fun x hx _ => hp.2.2 x hx⟩

theorem FrameOutsideRange.mono_range {lo₁ hi₁ lo₂ hi₂ : ℕ} {s₀ s₁ : Memory.State}
    (h : FrameOutsideRange lo₁ hi₁ s₀ s₁) (hlo : lo₂ ≤ lo₁) (hhi : hi₁ ≤ hi₂) :
    FrameOutsideRange lo₂ hi₂ s₀ s₁ :=
  ⟨h.1, fun x hx hout => h.2 x hx (hout.imp (fun hlt => lt_of_lt_of_le hlt hlo)
    (fun hge => le_trans hhi hge))⟩

theorem FrameOutsideRange.trans {lo hi : ℕ} {s₀ s₁ s₂ : Memory.State}
    (h₁ : FrameOutsideRange lo hi s₀ s₁) (h₂ : FrameOutsideRange lo hi s₁ s₂) :
    FrameOutsideRange lo hi s₀ s₂ :=
  ⟨h₁.1.trans h₂.1, fun x hx hout =>
    (h₂.2 x (lt_of_lt_of_le hx h₁.1) hout).trans (h₁.2 x hx hout)⟩

theorem HoldsIn.frame_outsideRange {base lo hi : ℕ} {xs : List ℕ} {s₀ s₁ : Memory.State}
    (h : HoldsIn base xs s₀)
    (hdisj : base + xs.length ≤ lo ∨ hi ≤ base)
    (hf : FrameOutsideRange lo hi s₀ s₁) :
    HoldsIn base xs s₁ := by
  refine ⟨h.1.trans hf.1, h.2.frame fun x hlo hhi => ?_⟩
  exact hf.2 x (by have := h.1; omega) (by omega)

end Cslib.WordRAM.Realization
