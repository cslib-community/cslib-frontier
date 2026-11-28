/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Memory.Field
public import CslibFrontier.DataStructure.StateTransition.CostHoare

/-!
# Correctness-and-cost triples for memory programs

`Memory.Triple w s p c Q` says that the memory program `p`, run from the state `s` at word size
`w`, issues only admissible operations, costs at most `c` memory units (`Memory.charge`), and
ends with an answer and a state satisfying `Q`. It is `StateTransitionSpec.CostHoare` at the
single initial state `s`; `Memory.triple_iff` unfolds it along the run of `p`.

The rules evaluate a program from its first operation on. `Triple.read_bind` and
`Triple.write_bind` discharge one operation's admissibility and charge, and leave the
continuation at the next state; `Triple.bind` splits a program at a subprogram with its own
triple; `Triple.pure` ends the run. Each rule peels one unit off a cost written `c + 1`, so a
straight-line program is checked by applying the rules in order. A recursive program is checked
by induction on its recursion measure, with the induction hypothesis applied at the recursive
call.

The word RAM's initial memory is zero past the input (`zeroAbove_init`), so a structure that
needs zeroed storage can take it there with a dirty allocation, at the cost of one unit, instead
of a zeroed one, whose charge grows with its size.

## Main definitions

* `Cslib.DataStructure.Memory.Triple`: admissibility, cost and postcondition of one run.
* `Cslib.DataStructure.Memory.ZeroAbove`: every cell at or above the frontier holds `0`.

## Main results

* `Cslib.DataStructure.Memory.triple_iff`: the triple along the run of the program.
* `Cslib.DataStructure.Memory.Triple.pure`, `Cslib.DataStructure.Memory.Triple.read_bind`,
  `Cslib.DataStructure.Memory.Triple.read`, `Cslib.DataStructure.Memory.Triple.write_bind`,
  `Cslib.DataStructure.Memory.Triple.write`, `Cslib.DataStructure.Memory.Triple.alloc_bind`,
  `Cslib.DataStructure.Memory.Triple.alloc`, `Cslib.DataStructure.Memory.Triple.allocDirty_bind`,
  `Cslib.DataStructure.Memory.Triple.allocDirty`,
  `Cslib.DataStructure.Memory.Triple.allocBlock_bind`,
  `Cslib.DataStructure.Memory.Triple.allocBlock`,
  `Cslib.DataStructure.Memory.Triple.allocBlockDirty_bind`,
  `Cslib.DataStructure.Memory.Triple.allocBlockDirty`,
  `Cslib.DataStructure.Memory.Triple.get_bind`, `Cslib.DataStructure.Memory.Triple.get`,
  `Cslib.DataStructure.Memory.Triple.set_bind`, `Cslib.DataStructure.Memory.Triple.set`:
  primitive step and block rules.
* `Cslib.DataStructure.Memory.Triple.bind`, `Cslib.DataStructure.Memory.Triple.ite`,
  `Cslib.DataStructure.Memory.Triple.dite`, `Cslib.DataStructure.Memory.Triple.map`: sequential
  composition, branching, and functorial mapping.
* `Cslib.DataStructure.Memory.Triple.mono`, `Cslib.DataStructure.Memory.Triple.wellFormed`,
  `Cslib.DataStructure.Memory.Triple.zeroAbove`: cost/postcondition weakening and invariant
  preservation.
* `Cslib.DataStructure.Memory.zeroAbove_init`, `Cslib.DataStructure.Memory.ZeroAbove.write`,
  `Cslib.DataStructure.Memory.ZeroAbove.alloc`,
  `Cslib.DataStructure.Memory.ZeroAbove.allocDirty`, `Cslib.DataStructure.Memory.ZeroAbove.step`,
  `Cslib.DataStructure.Memory.ZeroAbove.run`: `ZeroAbove` initialization and preservation.
-/

@[expose] public section

namespace Cslib.DataStructure.Memory

open Cslib.WordRAM

variable {w : ℕ} {α β : Type}

/-- Run from `s` at word size `w`, the program `p` issues only admissible operations, costs at
most `c` memory units, and ends with an answer and a state satisfying `Q`. -/
abbrev Triple (w : ℕ) (s : State) (p : Prog α) (c : ℕ) (Q : α → State → Prop) : Prop :=
  (spec w).CostHoare charge (· = s) p Q fun _ => c

/-- A triple is a statement about the one run of the program. -/
theorem triple_iff {s : State} {p : Prog α} {c : ℕ} {Q : α → State → Prop} :
    Triple w s p c Q ↔ (spec w).ValidHistory s ((spec w).clientHistory s p) ∧
      (spec w).totalCost charge s ((spec w).clientHistory s p) ≤ c ∧
      Q ((spec w).clientResult s p) ((spec w).clientState s p) := by
  rw [Triple, StateTransitionSpec.costHoare_iff_ofFn, StateTransitionSpec.hoare_iff_ofFn]
  exact ⟨fun ⟨h, hc⟩ => ⟨(h s rfl).1, hc s rfl, (h s rfl).2⟩,
    fun ⟨hv, hc, hq⟩ => ⟨fun _ h => h ▸ ⟨hv, hq⟩, fun _ h => h ▸ hc⟩⟩

namespace Triple

variable {s : State} {c c' : ℕ} {Q Q' : α → State → Prop}

/-- Weaken the cost and the postcondition. -/
theorem mono {p : Prog α} (h : Triple w s p c Q) (hc : c ≤ c') (hQ : ∀ a s', Q a s' → Q' a s') :
    Triple w s p c' Q' := by
  rw [triple_iff] at h ⊢
  exact ⟨h.1, h.2.1.trans hc, hQ _ _ h.2.2⟩

/-- Returning a value costs nothing. -/
theorem pure {a : α} (h : Q a s) : Triple w s (Pure.pure a) c Q :=
  triple_iff.mpr ⟨trivial, Nat.zero_le c, h⟩

/-- Read an allocated cell, then continue with its contents. -/
theorem read_bind {a : ℕ} {k : ℕ → Prog α} (ha : a < s.frontier)
    (h : Triple w s (k (s.mem a)) c Q) : Triple w s (read a >>= k) (c + 1) Q := by
  obtain ⟨hv, hc, hq⟩ := triple_iff.mp h
  exact triple_iff.mpr ⟨⟨ha, hv⟩, (Nat.add_le_add_left hc 1).trans_eq (Nat.add_comm 1 c), hq⟩

/-- Read an allocated cell as a standalone program. -/
theorem read {Q : ℕ → State → Prop} {a : ℕ} (ha : a < s.frontier) (h : Q (s.mem a) s) :
    Triple w s (Memory.read a) 1 Q :=
  read_bind ha (pure h)

/-- Write a word to an allocated cell, then continue. -/
theorem write_bind {a v : ℕ} {k : Unit → Prog α} (ha : a < s.frontier) (hv : Fits w v)
    (h : Triple w ⟨Function.update s.mem a v, s.frontier⟩ (k ()) c Q) :
    Triple w s (write a v >>= k) (c + 1) Q := by
  obtain ⟨hvh, hc, hq⟩ := triple_iff.mp h
  exact triple_iff.mpr ⟨⟨⟨ha, hv⟩, hvh⟩, (Nat.add_le_add_left hc 1).trans_eq (Nat.add_comm 1 c), hq⟩

/-- Write a word to an allocated cell as a standalone program. -/
theorem write {Q : Unit → State → Prop} {a v : ℕ} (ha : a < s.frontier) (hv : Fits w v)
    (h : Q () ⟨Function.update s.mem a v, s.frontier⟩) :
    Triple w s (Memory.write a v) 1 Q :=
  write_bind ha hv (pure h)

/-- Allocate `k` zeroed cells at the frontier, then continue with the base address. -/
theorem alloc_bind {k : ℕ} {next : ℕ → Prog α} (hk : Fits w (s.frontier + k))
    (h : Triple w ⟨clear s.mem s.frontier k, s.frontier + k⟩ (next s.frontier) c Q) :
    Triple w s (Memory.alloc k >>= next) (c + (k + 1)) Q := by
  obtain ⟨hv, hc, hq⟩ := triple_iff.mp h
  refine triple_iff.mpr ⟨⟨hk, hv⟩, ?_, hq⟩
  change charge s (.alloc k) + (spec w).totalCost charge
    ⟨clear s.mem s.frontier k, s.frontier + k⟩
    ((spec w).clientHistory ⟨clear s.mem s.frontier k, s.frontier + k⟩ (next s.frontier)) ≤
    c + (k + 1)
  rw [charge_alloc]
  omega

/-- Allocate `k` zeroed cells as a standalone program. -/
theorem alloc {Q : ℕ → State → Prop} {k : ℕ} (hk : Fits w (s.frontier + k))
    (h : Q s.frontier ⟨clear s.mem s.frontier k, s.frontier + k⟩) :
    Triple w s (Memory.alloc k) (k + 1) Q :=
  mono (alloc_bind (c := 0) hk (pure h)) (Nat.zero_add _).le fun _ _ hq => hq

/-- Allocate `k` dirty cells at the frontier, then continue with the base address. -/
theorem allocDirty_bind {k : ℕ} {next : ℕ → Prog α} (hk : Fits w (s.frontier + k))
    (h : Triple w ⟨s.mem, s.frontier + k⟩ (next s.frontier) c Q) :
    Triple w s (Memory.allocDirty k >>= next) (c + 1) Q := by
  obtain ⟨hv, hc, hq⟩ := triple_iff.mp h
  refine triple_iff.mpr ⟨⟨hk, hv⟩, ?_, hq⟩
  change charge s (.allocDirty k) + (spec w).totalCost charge ⟨s.mem, s.frontier + k⟩
    ((spec w).clientHistory ⟨s.mem, s.frontier + k⟩ (next s.frontier)) ≤ c + 1
  rw [charge_allocDirty]
  omega

/-- Allocate `k` dirty cells as a standalone program. -/
theorem allocDirty {Q : ℕ → State → Prop} {k : ℕ} (hk : Fits w (s.frontier + k))
    (h : Q s.frontier ⟨s.mem, s.frontier + k⟩) :
    Triple w s (Memory.allocDirty k) 1 Q :=
  allocDirty_bind hk (pure h)

/-- Allocate a zeroed block of `k` cells, then continue with the block handle. -/
theorem allocBlock_bind {k : ℕ} {next : Block → Prog α} (hk : Fits w (s.frontier + k))
    (h : Triple w ⟨clear s.mem s.frontier k, s.frontier + k⟩ (next ⟨s.frontier, k⟩) c Q) :
    Triple w s (Memory.allocBlock k >>= next) (c + (k + 1)) Q := by
  obtain ⟨hv, hc, hq⟩ := triple_iff.mp h
  refine triple_iff.mpr ⟨⟨hk, hv⟩, ?_, hq⟩
  change charge s (.alloc k) + (spec w).totalCost charge
    ⟨clear s.mem s.frontier k, s.frontier + k⟩
    ((spec w).clientHistory ⟨clear s.mem s.frontier k, s.frontier + k⟩
      (next ⟨s.frontier, k⟩)) ≤ c + (k + 1)
  rw [charge_alloc]
  omega

/-- Allocate a zeroed block of `k` cells as a standalone program. -/
theorem allocBlock {Q : Block → State → Prop} {k : ℕ} (hk : Fits w (s.frontier + k))
    (h : Q ⟨s.frontier, k⟩ ⟨clear s.mem s.frontier k, s.frontier + k⟩) :
    Triple w s (Memory.allocBlock k) (k + 1) Q :=
  mono (allocBlock_bind (c := 0) hk (pure h)) (Nat.zero_add _).le fun _ _ hq => hq

/-- Allocate a field of `k` cells without clearing it, then continue with the field at the
frontier. -/
theorem allocBlockDirty_bind {k : ℕ} {next : Block → Prog α} (hk : Fits w (s.frontier + k))
    (h : Triple w ⟨s.mem, s.frontier + k⟩ (next ⟨s.frontier, k⟩) c Q) :
    Triple w s (allocBlockDirty k >>= next) (c + 1) Q := by
  obtain ⟨hv, hc, hq⟩ := triple_iff.mp h
  exact triple_iff.mpr ⟨⟨hk, hv⟩, (Nat.add_le_add_left hc 1).trans_eq (Nat.add_comm 1 c), hq⟩

/-- Allocate a dirty block of `k` cells as a standalone program. -/
theorem allocBlockDirty {Q : Block → State → Prop} {k : ℕ} (hk : Fits w (s.frontier + k))
    (h : Q ⟨s.frontier, k⟩ ⟨s.mem, s.frontier + k⟩) :
    Triple w s (Memory.allocBlockDirty k) 1 Q :=
  allocBlockDirty_bind hk (pure h)

/-- Read entry `i` of an allocated block, then continue with its contents. -/
theorem get_bind {b : Block} {i : ℕ} {k : ℕ → Prog α} (hb : b.Allocated s) (hi : i < b.length)
    (h : Triple w s (k (s.mem (b.base + i))) c Q) :
    Triple w s (b.get i >>= k) (c + 1) Q :=
  read_bind (hb.lt_frontier hi) h

/-- Read entry `i` of an allocated block as a standalone program. -/
theorem get {Q : ℕ → State → Prop} {b : Block} {i : ℕ} (hb : b.Allocated s) (hi : i < b.length)
    (h : Q (s.mem (b.base + i)) s) : Triple w s (b.get i) 1 Q :=
  get_bind hb hi (pure h)

/-- Write `v` to entry `i` of an allocated block, then continue. -/
theorem set_bind {b : Block} {i v : ℕ} {k : Unit → Prog α} (hb : b.Allocated s)
    (hi : i < b.length) (hv : Fits w v)
    (h : Triple w ⟨Function.update s.mem (b.base + i) v, s.frontier⟩ (k ()) c Q) :
    Triple w s (b.set i v >>= k) (c + 1) Q :=
  write_bind (hb.lt_frontier hi) hv h

/-- Write `v` to entry `i` of an allocated block as a standalone program. -/
theorem set {Q : Unit → State → Prop} {b : Block} {i v : ℕ} (hb : b.Allocated s)
    (hi : i < b.length) (hv : Fits w v)
    (h : Q () ⟨Function.update s.mem (b.base + i) v, s.frontier⟩) :
    Triple w s (b.set i v) 1 Q :=
  set_bind hb hi hv (pure h)

/-- **Sequential composition.** Run `p` within `c₁`, and from each of its outcomes run the
continuation within `c₂`. -/
theorem bind {p : Prog α} {k : α → Prog β} {c₁ c₂ : ℕ} {Q : β → State → Prop}
    (h : Triple w s p c₁ fun a s' => Triple w s' (k a) c₂ Q) :
    Triple w s (p >>= k) (c₁ + c₂) Q := by
  obtain ⟨hv₁, hc₁, h₂⟩ := triple_iff.mp h
  obtain ⟨hv₂, hc₂, hq⟩ := triple_iff.mp h₂
  have hrun := (spec w).runClient_bind p k s
  have hhist : (spec w).clientHistory s (p >>= k) = (spec w).clientHistory s p ++
      (spec w).clientHistory ((spec w).clientState s p) (k ((spec w).clientResult s p)) :=
    congrArg (·.2.2) hrun
  have hmid := (spec w).run_runClient p s
  refine triple_iff.mpr ⟨?_, ?_, ?_⟩
  · rw [hhist, StateTransitionSpec.validHistory_append, hmid]
    exact ⟨hv₁, hv₂⟩
  · rw [hhist, StateTransitionSpec.totalCost_append, hmid]
    exact Nat.add_le_add hc₁ hc₂
  · rw [show (spec w).clientResult s (p >>= k) = _ from congrArg (·.1) hrun,
      show (spec w).clientState s (p >>= k) = _ from congrArg (·.2.1) hrun]
    exact hq

/-- Branching rule for `if cond then p₁ else p₂`. -/
theorem ite {cond : Prop} [Decidable cond] {p₁ p₂ : Prog α}
    (h₁ : cond → Triple w s p₁ c Q) (h₂ : ¬cond → Triple w s p₂ c Q) :
    Triple w s (if cond then p₁ else p₂) c Q := by
  split_ifs with h
  · exact h₁ h
  · exact h₂ h

/-- Dependent branching rule for `if h : cond then p₁ h else p₂ h`. -/
theorem dite {cond : Prop} [Decidable cond] {p₁ : cond → Prog α} {p₂ : ¬cond → Prog α}
    (h₁ : ∀ h : cond, Triple w s (p₁ h) c Q) (h₂ : ∀ h : ¬cond, Triple w s (p₂ h) c Q) :
    Triple w s (if h : cond then p₁ h else p₂ h) c Q := by
  split_ifs with h
  · exact h₁ h
  · exact h₂ h

/-- Map the result of a memory program without additional cost. -/
theorem map (f : α → β) {p : Prog α} {Q : β → State → Prop}
    (h : Triple w s p c fun a s' => Q (f a) s') : Triple w s (f <$> p) c Q := by
  rw [← bind_pure_comp]
  exact (bind (c₁ := c) (c₂ := 0) (h.mono le_rfl fun _ _ ha => pure ha)).mono
    (Nat.add_zero c).le fun _ _ hq => hq

/-- Any admissible `Triple` run preserves `WellFormed w`. -/
theorem wellFormed {p : Prog α} (hwf : WellFormed w s) (h : Triple w s p c Q) :
    Triple w s p c fun a s' => Q a s' ∧ WellFormed w s' := by
  obtain ⟨hv, hc, hq⟩ := triple_iff.mp h
  refine triple_iff.mpr ⟨hv, hc, hq, ?_⟩
  have hrun := hwf.run hv
  rwa [StateTransitionSpec.run_runClient] at hrun

end Triple

/-! ## Memory that is zero above the frontier -/

/-- Every cell at or above the frontier holds `0`, as in the word RAM's initial memory past the
input. A dirty allocation from such a state hands out a zeroed block at the cost of one unit. -/
def ZeroAbove (s : State) : Prop := ∀ a, s.frontier ≤ a → s.mem a = 0

/-- The input convention is zero above the frontier. -/
theorem zeroAbove_init (input : List ℕ) : ZeroAbove (State.init input) := by
  intro a (ha : input.length + 1 ≤ a)
  change (if a = 0 then input.length else input.getD (a - 1) 0) = 0
  rw [ite_eq_right (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

/-- A dirty allocation keeps memory zero above the new frontier. -/
theorem ZeroAbove.allocDirty {s : State} (h : ZeroAbove s) (k : ℕ) :
    ZeroAbove ⟨s.mem, s.frontier + k⟩ := fun a ha => h a (by simp only at ha; omega)

namespace ZeroAbove

/-- Writing below the frontier preserves `ZeroAbove`. -/
theorem write {s : State} (h : ZeroAbove s) {a v : ℕ} (ha : a < s.frontier) :
    ZeroAbove ⟨Function.update s.mem a v, s.frontier⟩ := by
  intro b hb
  change Function.update s.mem a v b = 0
  rw [Function.update_of_ne (by simp only at hb; omega)]
  exact h b hb

/-- A zeroed allocation preserves `ZeroAbove`. -/
theorem alloc {s : State} (h : ZeroAbove s) (k : ℕ) :
    ZeroAbove ⟨clear s.mem s.frontier k, s.frontier + k⟩ := by
  intro a ha
  change clear s.mem s.frontier k a = 0
  rw [clear_of_not_owns (fun howns => by simp only [Block.Owns] at howns; simp only at ha; omega)]
  exact h a (by simp only at ha; omega)

/-- Every admissible single operation preserves `ZeroAbove`. -/
theorem step {s : State} (h : ZeroAbove s) {o : Op} (hv : valid w s o) :
    ZeroAbove (Memory.step s o).1 := by
  cases o with
  | read => exact h
  | write a v => exact h.write hv.1
  | alloc k => exact h.alloc k
  | allocDirty k => exact h.allocDirty k

/-- Every admissible history preserves `ZeroAbove`. -/
theorem run {s : State} (h : ZeroAbove s) {os : List Op} (hv : (spec w).ValidHistory s os) :
    ZeroAbove ((spec w).run s os).1 := by
  induction os generalizing s with
  | nil => exact h
  | cons o os ih => exact ih (h.step hv.1) hv.2

end ZeroAbove

/-- Any `Triple` run preserves `ZeroAbove`. -/
theorem Triple.zeroAbove {s : State} {p : Prog α} {c : ℕ} {Q : α → State → Prop}
    (hz : ZeroAbove s) (h : Triple w s p c Q) :
    Triple w s p c fun a s' => Q a s' ∧ ZeroAbove s' := by
  obtain ⟨hv, hc, hq⟩ := triple_iff.mp h
  refine triple_iff.mpr ⟨hv, hc, hq, ?_⟩
  have hrun := hz.run hv
  rwa [StateTransitionSpec.run_runClient] at hrun

end Cslib.DataStructure.Memory
