/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Heap
public import CslibFrontier.DataStructure.BTree.WordRAM.Arena
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Word-RAM B-Tree Interface Registers, `Rep` Invariant, and Arena Initialization

Caller-visible register bank (`Reg.rBase..rFound`), Word-RAM representation invariant `Rep`
coupling a `20`-register machine state `x : Data 20` to a well-formed `BTree ℕ ℕ` in
`[base, base + arenaWords t capNodes)`, allocated-node counter `allocCount`, and `O(1)` empty-arena
initializer `initCode` (`initCode_spec`).

## Main definitions

* `Cslib.DataStructure.BTree.WordRAM.Reg.rBase`,
  `Cslib.DataStructure.BTree.WordRAM.Reg.rDeg`,
  `Cslib.DataStructure.BTree.WordRAM.Reg.rKey`,
  `Cslib.DataStructure.BTree.WordRAM.Reg.rVal`,
  `Cslib.DataStructure.BTree.WordRAM.Reg.rFound`: caller-visible Word-RAM interface registers.
* `Cslib.DataStructure.BTree.WordRAM.Rep` and `Cslib.DataStructure.BTree.WordRAM.allocCount`:
  coupling invariant and allocated-node count (`x.mem (base + 1)`).
* `Cslib.DataStructure.BTree.WordRAM.initCode`: `O(1)` empty-arena initializer over
  `Basis.standard`.

## Main results

* `Cslib.DataStructure.BTree.WordRAM.Rep.isWF`,
  `Cslib.DataStructure.BTree.WordRAM.Rep.isSortedAssoc`,
  `Cslib.DataStructure.BTree.WordRAM.Rep.height_le_log`: well-formedness, sortedness, and
  logarithmic height bound from `Rep`.
* `Cslib.DataStructure.BTree.WordRAM.Rep.allocCount_le_cap`,
  `Cslib.DataStructure.BTree.WordRAM.Rep.set_of_ne`,
  `Cslib.DataStructure.BTree.WordRAM.Rep.setKey`,
  `Cslib.DataStructure.BTree.WordRAM.Rep.setKeyVal`: node-count bound and register framing for
  `Rep`.
* `Cslib.DataStructure.BTree.WordRAM.initCode_spec`: `O(1)` Word-RAM initialization of `.leaf`.
-/

public section

namespace Cslib.DataStructure.BTree.WordRAM

open Cslib.WordRAM Cslib.DataStructure

namespace Reg
/-- Persistent base address of the B-tree arena `[base, base + arenaWords t capNodes)`. -/
@[expose] def rBase : Fin 20 := 0
/-- Persistent minimum degree `t` (`2 ≤ t`). -/
@[expose] def rDeg : Fin 20 := 1
/-- Search or insertion key `k`. -/
@[expose] def rKey : Fin 20 := 2
/-- Insertion value `v` (input to `insertCode`) / lookup value (output of `lookupCode`). -/
@[expose] def rVal : Fin 20 := 3
/-- Lookup hit flag (`1` when `k` is present, `0` when absent). -/
@[expose] def rFound : Fin 20 := 4
end Reg

open Reg

private abbrev rZero : Fin 20 := 5
private abbrev rOne : Fin 20 := 6
private abbrev rTmp1 : Fin 20 := 18

/-- Word-RAM representation of a classic minimum-degree-`t` `BTree ℕ ℕ` in the memory block
`[base, base + arenaWords t capNodes)` at word width `w`. -/
structure Rep (base capNodes t w : ℕ) (tr : BTree ℕ ℕ) (x : Data 20) : Prop where
  /-- All registers and memory cells fit in `w`-bit words. -/
  bounded : x.Bounded w
  /-- Minimum degree is at least `2`. -/
  two_le : 2 ≤ t
  /-- `rBase` holds `base`. -/
  base_eq : x.regs rBase = base
  /-- `rDeg` holds `t`. -/
  deg_eq : x.regs rDeg = t
  /-- Every address up to `base + arenaWords t capNodes` fits in a `w`-bit word. -/
  fits_arena : Fits w (base + arenaWords t capNodes)
  /-- Allocated node count `x.mem (base + 1)` does not exceed `capNodes`. -/
  cnt_le_cap : x.mem (base + 1) ≤ capNodes
  /-- Either `cnt = 0` (`tr = .leaf`), or `0 < cnt` and `x.mem base` roots a valid, sorted B-tree
  whose node indices lie in `Finset.range (x.mem (base + 1))`. -/
  tree_spec :
    (x.mem (base + 1) = 0 ∧ tr = .leaf) ∨
      (0 < x.mem (base + 1) ∧
        ∃ l : ℕ,
          tr = readTree l base t x.mem (x.mem base) ∧
          ValidNode l base t x.mem (x.mem base) ∧
          SortedNode l base t x.mem (x.mem base) ∧
          readNodeSet l base t x.mem (x.mem base) ⊆ Finset.range (x.mem (base + 1)))

/-- Number of arena nodes currently allocated in `x` (`x.mem (base + 1)`). -/
@[expose] def allocCount (base : ℕ) (x : Data 20) : ℕ := x.mem (base + 1)

@[simp] theorem allocCount_set (base : ℕ) (x : Data 20) (r : Fin 20) (v : ℕ) :
    allocCount base (x.set r v) = allocCount base x := rfl

/-- Allocated node count never exceeds `capNodes` under `Rep`. -/
theorem Rep.allocCount_le_cap {base capNodes t w : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x) : allocCount base x ≤ capNodes :=
  hr.cnt_le_cap

/-- Setting any register other than `rBase` and `rDeg` to a `w`-bit word preserves `Rep`. -/
theorem Rep.set_of_ne {base capNodes t w : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x) {r : Fin 20} (hb : r ≠ rBase) (hd : r ≠ rDeg)
    {v : ℕ} (hv : Fits w v) :
    Rep base capNodes t w tr (x.set r v) where
  bounded := hr.bounded.set hv
  two_le := hr.two_le
  base_eq := (Data.set_regs_of_ne hb.symm v).trans hr.base_eq
  deg_eq := (Data.set_regs_of_ne hd.symm v).trans hr.deg_eq
  fits_arena := hr.fits_arena
  cnt_le_cap := hr.cnt_le_cap
  tree_spec := hr.tree_spec

/-- Setting `rKey` to a `w`-bit word preserves `Rep`. -/
theorem Rep.setKey {base capNodes t w : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x) {k : ℕ} (hk : Fits w k) :
    Rep base capNodes t w tr (x.set rKey k) :=
  hr.set_of_ne (by decide) (by decide) hk

/-- Setting `rKey` and `rVal` to `w`-bit words preserves `Rep`. -/
theorem Rep.setKeyVal {base capNodes t w : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x) {k v : ℕ} (hk : Fits w k) (hv : Fits w v) :
    Rep base capNodes t w tr ((x.set rKey k).set rVal v) :=
  (hr.setKey hk).set_of_ne (by decide) (by decide) hv

/-- Every represented B-tree satisfies `BTree.IsWF t tr`. -/
theorem Rep.isWF {base capNodes t w : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x) : BTree.IsWF t tr := by
  rcases hr.tree_spec with ⟨_, rfl⟩ | ⟨_, _, rfl, hv, hs, _⟩
  · exact { two_le := hr.two_le, rootKeys_le := Nat.zero_le _,
            rootKeys_pos := fun h => (h rfl).elim,
            occupied_of_mem_children := (fun _ hc => nomatch hc),
            balanced := .leaf, sorted := List.isSortedAssoc_nil }
  · exact hv.isWF hr.two_le hs

/-- Every represented B-tree has sorted key-value inorder traversal `tr.toList`. -/
theorem Rep.isSortedAssoc {base capNodes t w : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x) : tr.toList.IsSortedAssoc :=
  hr.isWF.sorted

/-- Every represented B-tree has height at most `Nat.log t ((tr.size + 1) / 2) + 1`. -/
theorem Rep.height_le_log {base capNodes t w : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x) :
    tr.height ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  hr.isWF.height_le_log

/-- Initialize `[base, base + 2)` to `(root = 0, cnt = 0)`. -/
def initCode : Code .standard 20 := ram[
  rZero ← #0;
  rOne ← #1;
  *rBase ← rZero;
  rTmp1 ← rBase + rOne;
  *rTmp1 ← rZero ]

/-- `initCode` initializes an empty B-tree `.leaf` (`allocCount base y = 0`) in at most `5`
standard Word-RAM instructions, modifying only `[base, base + arenaWords t capNodes)`. -/
theorem initCode_spec {w base capNodes t : ℕ} {x : Data 20}
    (ht : 2 ≤ t)
    (hbdd : x.Bounded w)
    (hbase : x.regs rBase = base)
    (hdeg : x.regs rDeg = t)
    (hfit : Fits w (base + arenaWords t capNodes)) :
    ∃ y, ExecWithin w initCode x y 5 ∧
      Rep base capNodes t w .leaf y ∧
      allocCount base y = 0 ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
  have hf1 : Fits w 1 := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_b1 : Fits w (base + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  let y : Data 20 :=
    ((((x.set rZero 0).set rOne 1).write base 0).set rTmp1 (base + 1)).write (base + 1) 0
  have hexec : ExecWithin w initCode x y 5 := by
    unfold initCode
    dsimp only [y]
    wram_exec [hbase, hf1, hf_b1]
  have hymem : y.mem = Function.update (Function.update x.mem base 0) (base + 1) 0 := by
    dsimp only [y]
    wram_simp
  have hcnt0 : allocCount base y = 0 := by simp only [allocCount, hymem, Function.update_self]
  refine ⟨y, hexec, ⟨hexec.bounded hbdd, ht, ?_, ?_, hfit, ?_, Or.inl ⟨hcnt0, rfl⟩⟩, hcnt0, ?_⟩
  · dsimp only [y]
    wram_simp
    exact hbase
  · dsimp only [y]
    wram_simp
    exact hdeg
  · change allocCount base y ≤ capNodes
    omega
  · rw [hymem]
    simpa only [Finset.union_idempotent] using
      (Modifies.write_of_owns (base := base) (n := arenaWords t capNodes)
        ⟨le_rfl, by simp only [arenaWords]; omega⟩ 0).trans
        (Modifies.write_of_owns (base := base) (n := arenaWords t capNodes)
          ⟨by omega, by simp only [arenaWords]; omega⟩ 0)

end Cslib.DataStructure.BTree.WordRAM
