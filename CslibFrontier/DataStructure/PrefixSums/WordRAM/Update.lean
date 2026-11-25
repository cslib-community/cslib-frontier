/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PrefixSums.WordRAM.Tree
public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec.MemFrame

/-!
# Fixed Word-RAM point updates for aggregation trees

The program walks from the root to the updated leaf. Every visited node is incremented,
and the next subtree is selected by the position relative to half the current length.
The same code handles every height, position and increment. Its arithmetic and all its
loads, stores, tests and jumps are actual bounded-word instructions.

## Main definitions

* `Reg.zero`, `Reg.one`, `Reg.two`, `Reg.ptr`, `Reg.len`, `Reg.idx`, `Reg.delta`, `Reg.val`,
  `Reg.tmp`, `Reg.ans`, `Reg.tag`, `Reg.root`, `Reg.capacity`, `Reg.position`: register
  assignments for aggregation-tree updates and queries.
* `Entry`: the register calling convention.
* `updateBody`, `updateLoop`, `updateNext`: the single-iteration body, fixed update loop, and
  single-iteration state transition.

## Main results

* `updateLoop_spec`: logarithmic instruction bound, restored tree representation and a
  frame theorem for every memory word outside the tree.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.DataStructure.PrefixSums.WordRAM

open Cslib.WordRAM

namespace Reg
/-- Constant zero. -/
abbrev zero : Fin 14 := 0
/-- Constant one. -/
abbrev one : Fin 14 := 1
/-- Constant two. -/
abbrev two : Fin 14 := 2
/-- Current subtree pointer. -/
abbrev ptr : Fin 14 := 3
/-- Current subtree length. -/
abbrev len : Fin 14 := 4
/-- Position relative to the current subtree. -/
abbrev idx : Fin 14 := 5
/-- Increment supplied to an update. -/
abbrev delta : Fin 14 := 6
/-- Loaded value and arithmetic scratch. -/
abbrev val : Fin 14 := 7
/-- Address scratch. -/
abbrev tmp : Fin 14 := 8
/-- Query answer. -/
abbrev ans : Fin 14 := 9
/-- Operation tag, zero for update and nonzero for query. -/
abbrev tag : Fin 14 := 10
/-- Persistent root pointer. -/
abbrev root : Fin 14 := 11
/-- Persistent array capacity. -/
abbrev capacity : Fin 14 := 12
/-- External operation position. -/
abbrev position : Fin 14 := 13
end Reg

open Reg

/-- Registers used by both tree traversals. -/
structure Entry (b n i δ : ℕ) (x : Data 14) : Prop where
  zero_eq : x.regs zero = 0
  one_eq : x.regs one = 1
  two_eq : x.regs two = 2
  ptr_eq : x.regs ptr = b
  len_eq : x.regs len = n
  idx_eq : x.regs idx = i
  delta_eq : x.regs delta = δ

/-- Increment one node and move to the selected child. A leaf has half-length zero;
the resulting length stops the loop before another access. -/
def updateBody : Code .standard 14 := ram[
  val ← *ptr; val ← val + delta; *ptr ← val;
  len ← len / two;
  if idx < len then [ptr ← ptr + one]
  else [ptr ← ptr + len; ptr ← ptr + len; idx ← idx - len] ]

/-- Fixed update code, independent of array size, position and increment. -/
def updateLoop : Code .standard 14 := ram[while zero < len do [⟪updateBody⟫]]

/-- The data after one update iteration; this is a mathematical description, not an
additional instruction in the machine. -/
def updateNext (x : Data 14) (b n i δ : ℕ) : Data 14 :=
  let y := ((x.set val (x.mem b)).set val (x.mem b + δ)).write b (x.mem b + δ)
    |>.set len (n / 2)
  if i < n / 2 then y.set ptr (b + 1)
  else ((y.set ptr (b + n / 2)).set ptr (b + n / 2 + n / 2)).set idx (i - n / 2)

variable {w h b n i δ : ℕ} {x : Data 14}

private theorem updateBody_exec (hx : Entry b n i δ x) (hi : i < n)
    (ha : Fits w (b + 2 * n)) (hv : Fits w (x.mem b + δ)) :
    ExecWithin w updateBody x (updateNext x b n i δ) 9 := by
  obtain ⟨hz, ho, ht, hp, hl, hi', hd⟩ := hx
  refine WP.execWithin ?_
  unfold updateBody updateNext
  wram_exec [hp, hl, hi', hd, ho, ht, hv] <;> simp only [hc, ↓reduceIte]

private theorem updateNext_entry (hx : Entry b n i δ x) :
    Entry (if i < n / 2 then b + 1 else b + n / 2 + n / 2) (n / 2)
      (if i < n / 2 then i else i - n / 2) δ (updateNext x b n i δ) := by
  rcases hx with ⟨hz, ho, ht, hp, hl, hi, hd⟩
  by_cases hc : i < n / 2 <;>
    simp +decide [updateNext, hc, Entry.mk, hz, ho, ht, hi, hd]

/-- One update iteration increments the memory word at the current node pointer `b` by `δ` and
leaves all other addresses unchanged. -/
@[simp]
theorem updateNext_mem (a : ℕ) :
    (updateNext x b n i δ).mem a = Function.update x.mem b (x.mem b + δ) a := by
  simp only [updateNext]
  split <;> rfl

/-- The fixed update loop runs in at most `11 (h + 1) + 2` instructions. It restores the
complete aggregation invariant and preserves every word outside the original footprint.
The bound assumes the existing tree is supplied in memory; it does not include construction. -/
theorem updateLoop_spec (t : Tree h) (hx : Entry b (2 ^ h) i δ x) (hi : i < 2 ^ h)
    (hr : t.Rep b x.mem) (ha : Fits w (b + 2 * 2 ^ h)) (hv : Fits w (t.total + δ)) :
    ∃ y, ExecWithin w updateLoop x y (11 * (h + 1) + 2) ∧ (t.add i δ).Rep b y.mem ∧
      (∀ a, a < b ∨ b + Tree.words h ≤ a → y.mem a = x.mem a) := by
  induction t generalizing b i x with
  | leaf v =>
    obtain rfl : i = 0 := by simpa using hi
    let y := updateNext x b (2 ^ 0) 0 δ
    have he := updateBody_exec hx (by decide) ha (by simpa [Tree.total, hr.root] using hv)
    have hy := updateNext_entry hx
    have hym : y.mem = Function.update x.mem b (x.mem b + δ) := funext updateNext_mem
    refine ⟨y, (he.loop_once (cond := .lt zero len)
      (by simp [Cond.holds_lt, hx.zero_eq, hx.len_eq]) ?_).mono (by omega),
      by simp [Tree.add, Tree.Rep, hym, hr.root, Tree.total], by mem_frame⟩
    simp only [Cond.holds_lt, hy.zero_eq, hy.len_eq]
    decide
  | @node h l r ihl ihr =>
    have hsize : 2 ^ (h + 1) = 2 * 2 ^ h := by simp [pow_succ, Nat.mul_comm]
    have hhalf : 2 ^ (h + 1) / 2 = 2 ^ h := by omega
    let y := updateNext x b (2 ^ (h + 1)) i δ
    have he := updateBody_exec hx hi ha (by simpa [hr.root] using hv)
    have hy := updateNext_entry hx
    have hym : y.mem = Function.update x.mem b (x.mem b + δ) := funext updateNext_mem
    have hroot := hr.1
    have hl : l.Rep (b + 1) y.mem := hym ▸ hr.2.1.update_of_outside (Or.inl (by omega)) _
    have hright : r.Rep (b + 2 * 2 ^ h) y.mem :=
      hym ▸ hr.2.2.update_of_outside (Or.inl (by omega)) _
    have hcond : (Cond.lt zero len).Holds x := by
      simp only [Cond.holds_lt, hx.zero_eq, hx.len_eq]; exact Nat.two_pow_pos _
    by_cases hleft : i < 2 ^ h
    · obtain ⟨z, hz, hzrep, hzframe⟩ := ihl (by simpa [y, hhalf, hleft] using hy) hleft hl
        (by fits [hsize]) (by simp only [Tree.total] at hv; fits)
      refine ⟨z, (he.loop_iter hcond hz).mono (by omega), ?_, by mem_frame⟩
      simp only [Tree.add, hleft, ↓reduceIte, Tree.Rep, Tree.total_add]
      exact ⟨by rw [show z.mem b = x.mem b + δ by mem_frame, hroot]; omega,
        hzrep, hright.congr fun _ _ _ => by mem_frame⟩
    · obtain ⟨z, hz, hzrep, hzframe⟩ := ihr
        (by simpa [y, hhalf, hleft, Nat.two_mul, Nat.add_assoc] using hy)
        (by omega) hright (by fits [hsize]) (by simp only [Tree.total] at hv; fits)
      refine ⟨z, (he.loop_iter hcond hz).mono (by omega), ?_, by mem_frame⟩
      simp only [Tree.add, hleft, ↓reduceIte, Tree.Rep, Tree.total_add]
      exact ⟨by rw [show z.mem b = x.mem b + δ by mem_frame, hroot]; omega,
        hl.congr fun _ _ _ => by mem_frame, hzrep⟩

end Cslib.DataStructure.PrefixSums.WordRAM

end
