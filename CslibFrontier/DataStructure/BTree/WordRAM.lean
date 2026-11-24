/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.Computability.WordRAM.Heap
public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.DataStructure.BTree.WordRAM.Arena
import CslibFrontier.Computability.WordRAM.Call
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Array-Allocated Word-RAM B-Tree (`O(t log_t n)` Lookup and Insertion)

Concrete in-memory Word-RAM implementation of classic minimum-degree-`t` B-trees (`t ≥ 2`) over
`Cslib.WordRAM.Basis.standard` (`20` registers), backed by the flat arena representation of
`CslibFrontier.DataStructure.BTree.WordRAM.Arena` and following [CLRS2009], Section 18.2:

* **Initialization (`initCode`):** writes the empty header `(root = 0, cnt = 0)` at
  `[base, base + 2)` in `O(1)` Word-RAM instructions, establishing `Rep base capNodes t w .leaf y`.
* **Lookup (`lookupCode`, `lookupProgram`):** walks a single root-to-leaf path, scanning at most
  `2 * t - 1` keys per visited node (`slotScanLoop`) without modifying memory, returning
  `(found, val)` matching `BTree.lookup k tr` in at most `(16 * t + 21) * tr.height + 16`
  (`O(t log_t n)`) Word-RAM instructions.
* **Proactive top-down insertion (`insertCode`, `insertProgram`):** splits a full `(2 * t - 1)`-key
  root via `splitRootCode` (`O(t)` instructions) and descends through non-full nodes (`insertLoop`),
  proactively splitting any full child via `splitChildCode` (`O(t)` instructions) before descending
  and either overwriting an existing key's value or shifting-inserting into a leaf in a single
  downward pass without parent pointers, realizing `Cslib.SortedAssoc.insert k v tr.toList` in
  `O(t log_t n)` Word-RAM instructions while preserving `BTree.IsWF t` and outside memory.

## Main definitions

* `Cslib.DataStructure.BTree.WordRAM.Reg.rBase`,
  `Cslib.DataStructure.BTree.WordRAM.Reg.rDeg`,
  `Cslib.DataStructure.BTree.WordRAM.Reg.rKey`,
  `Cslib.DataStructure.BTree.WordRAM.Reg.rVal`,
  `Cslib.DataStructure.BTree.WordRAM.Reg.rFound`: caller-visible Word-RAM interface registers.
* `Cslib.DataStructure.BTree.WordRAM.Rep` and `Cslib.DataStructure.BTree.WordRAM.allocCount`:
  coupling invariant and allocated-node count (`x.mem (base + 1)`) for a `20`-register Word-RAM
  state `x : Data 20` representing a well-formed `BTree ℕ ℕ` in
  `[base, base + arenaWords t capNodes)`.
* `Cslib.DataStructure.BTree.WordRAM.initCode`: `O(1)` empty-arena initializer over
  `Basis.standard`.
* `Cslib.DataStructure.BTree.WordRAM.lookupCode`,
  `Cslib.DataStructure.BTree.WordRAM.lookupProgram`: `O(t log_t n)` B-tree lookup code and
  compiled flat program over `Basis.standard`.
* `Cslib.DataStructure.BTree.WordRAM.insertCode`,
  `Cslib.DataStructure.BTree.WordRAM.insertProgram`: `O(t log_t n)` proactive top-down B-tree
  insertion code and compiled flat program over `Basis.standard`.

## Main results

* `Cslib.DataStructure.BTree.WordRAM.Rep.isWF`,
  `Cslib.DataStructure.BTree.WordRAM.Rep.height_le_log`,
  `Cslib.DataStructure.BTree.WordRAM.Rep.setKey`, and
  `Cslib.DataStructure.BTree.WordRAM.Rep.setKeyVal`: well-formedness, logarithmic height bound,
  and argument-register framing for `Rep`.
* `Cslib.DataStructure.BTree.WordRAM.initCode_spec`: `O(1)` Word-RAM initialization of `.leaf`.
* `Cslib.DataStructure.BTree.WordRAM.lookupCode_spec`,
  `Cslib.DataStructure.BTree.WordRAM.lookupCode_log_spec`, and
  `Cslib.DataStructure.BTree.WordRAM.lookupProgram_spec`: `O(t * tr.height)` and `O(t log_t n)`
  Word-RAM instruction bounds for `lookupCode` and halting flat `lookupProgram` (retaining both
  `rFound` and `rVal`, unchanged memory, and `Rep`).
* `Cslib.DataStructure.BTree.WordRAM.insertCode_spec`,
  `Cslib.DataStructure.BTree.WordRAM.insertCode_log_spec`, and
  `Cslib.DataStructure.BTree.WordRAM.insertProgram_spec`: `O(t * (tr.height + 1))` and
  `O(t log_t n)` Word-RAM instruction bounds, `Rep` preservation, `SortedAssoc.insert` correctness,
  node-allocation bound, and memory framing for `insertCode` and halting flat `insertProgram`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 18.2][CLRS2009]
-/

public section

namespace Cslib.DataStructure.BTree.WordRAM

open Cslib.WordRAM Cslib.DataStructure

/-! ## 1. Caller-visible register bank and private scratch registers -/

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
private abbrev rStride : Fin 20 := 7
private abbrev rCur : Fin 20 := 8
private abbrev rChild : Fin 20 := 9
private abbrev rCnt : Fin 20 := 10
private abbrev rSlot : Fin 20 := 11
private abbrev rNumK : Fin 20 := 12
private abbrev rSrc : Fin 20 := 13
private abbrev rDst : Fin 20 := 14
private abbrev rLim : Fin 20 := 15
private abbrev rIdx : Fin 20 := 16
private abbrev rActive : Fin 20 := 17
private abbrev rTmp1 : Fin 20 := 18
private abbrev rTmp2 : Fin 20 := 19

/-! ## 2. Representation invariant `Rep` -/

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
  · exact {
      two_le := hr.two_le
      rootKeys_le := Nat.zero_le _
      rootKeys_pos := fun h => (h rfl).elim
      occupied_of_mem_children := fun _ hc => nomatch hc
      balanced := .leaf
      sorted := List.isSortedAssoc_nil }
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

private theorem stride_le_arena {base capNodes t : ℕ} (hcap : 1 ≤ capNodes) :
    6 * t ≤ base + arenaWords t capNodes := by
  have hmul : 1 * nodeStride t ≤ capNodes * nodeStride t := Nat.mul_le_mul_right _ hcap
  simp only [arenaWords, nodeStride, Nat.one_mul] at hmul ⊢
  omega

private theorem nodeAddr_add_le_arena {base capNodes t u o : ℕ}
    (hu : u < capNodes) (ho : o ≤ 6 * t) :
    nodeAddr base t u + o ≤ base + arenaWords t capNodes := by
  have hmul : (u + 1) * nodeStride t ≤ capNodes * nodeStride t :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [nodeAddr, arenaWords, nodeStride, Nat.add_mul, Nat.one_mul] at hmul ⊢
  omega

/-! ## 3. Initialization (`initCode`) -/

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
  have hcnt0 : allocCount base y = 0 := by
    simp only [allocCount, hymem, Function.update_self]
  have hrep : Rep base capNodes t w .leaf y := by
    refine ⟨hexec.bounded hbdd, ht, ?_, ?_, hfit, ?_, Or.inl ⟨hcnt0, rfl⟩⟩
    · dsimp only [y]; wram_simp; exact hbase
    · dsimp only [y]; wram_simp; exact hdeg
    · change allocCount base y ≤ capNodes; rw [hcnt0]; omega
  refine ⟨y, hexec, hrep, hcnt0, ?_⟩
  rw [hymem]
  simpa only [Finset.union_idempotent] using
    (Modifies.write_of_owns (base := base) (n := arenaWords t capNodes)
      ⟨le_rfl, by simp only [arenaWords]; omega⟩ 0).trans
      (Modifies.write_of_owns (base := base) (n := arenaWords t capNodes)
        ⟨by omega, by simp only [arenaWords]; omega⟩ 0)

/-! ## 4. Reusable inner loops: `copyArrayCode`, `shiftLoop`, `slotScanLoop` -/

private abbrev copyRegMap : Fin 7 → Fin 20 :=
  ![rSrc, rDst, rLim, rIdx, rTmp1, rTmp2, rOne]

private theorem copyRegMap_injective : Function.Injective copyRegMap := by decide

private def copyArrayCode : Code .standard 20 := ram[
  ⟪ArrayCopy.program.rename copyRegMap⟫;
  rOne ← #1 ]

private theorem copyArrayCode_spec {w srcBase dstBase N : ℕ} {x : Data 20}
    (hbdd : x.Bounded w)
    (ho : x.regs rOne = 1) (hsrc : x.regs rSrc = srcBase)
    (hdst : x.regs rDst = dstBase) (hlim : x.regs rLim = N)
    (hf_src : Fits w (srcBase + N)) (hf_dst : Fits w (dstBase + N))
    (hdisj : srcBase + N ≤ dstBase ∨ dstBase + N ≤ srcBase ∨ srcBase = dstBase) :
    ∃ y, ExecWithin w copyArrayCode x y (7 * N + 5) ∧
      y.Bounded w ∧
      y.mem = ArrayCopy.copyPrefix x.mem srcBase dstBase N ∧
      ∀ reg : Fin 20, reg ≠ rIdx → reg ≠ rTmp1 → reg ≠ rTmp2 → y.regs reg = x.regs reg := by
  have h1 : Fits w 1 := by rw [← ho]; exact hbdd.1 rOne
  have hcs : (x.comap copyRegMap).regs ArrayCopy.src = srcBase := hsrc
  have hcd : (x.comap copyRegMap).regs ArrayCopy.dst = dstBase := hdst
  have hcl : (x.comap copyRegMap).regs ArrayCopy.len = N := hlim
  obtain ⟨z, hz_exec, ⟨hzm, hzs, hzd, hzl⟩, hframe⟩ :=
    ExecWithin.rename_post copyRegMap_injective
      (ArrayCopy.exec_of_separated_or_eq (x.comap copyRegMap) h1
        (by rw [hcs, hcl]; exact hf_src)
        (by rw [hcd, hcl]; exact hf_dst)
        (by rw [hcs, hcd, hcl]; exact hdisj))
  rw [hcl] at hz_exec hzm hzl
  rw [hcs] at hzm hzs
  rw [hcd] at hzm hzd
  let y := z.set rOne 1
  have hy_exec : ExecWithin w copyArrayCode x y (7 * N + 5) :=
    hz_exec.seq (ExecWithin.const h1)
  refine ⟨y, hy_exec, hy_exec.bounded hbdd, hzm, fun reg hi ht1 ht2 => ?_⟩
  by_cases hor : reg = rOne
  · subst hor; exact ho.symm
  · dsimp only [y]
    rw [Data.set_regs_of_ne hor]
    by_cases hs : reg = rSrc
    · subst hs; exact hzs.trans hsrc.symm
    · by_cases hd : reg = rDst
      · subst hd; exact hzd.trans hdst.symm
      · by_cases hl : reg = rLim
        · subst hl; exact hzl.trans hlim.symm
        · refine hframe reg (fun j => ?_)
          rcases j with ⟨_ | _ | _ | _ | _ | _ | _ | j, hj⟩
          · exact Ne.symm hs
          · exact Ne.symm hd
          · exact Ne.symm hl
          · exact hi.symm
          · exact ht1.symm
          · exact ht2.symm
          · exact Ne.symm hor
          · omega

private def shiftBody : Code .standard 20 := ram[
  rTmp1 ← rDst - rIdx;
  rTmp2 ← rTmp1 - rOne;
  rTmp2 ← rSrc + rTmp2;
  rTmp2 ← *rTmp2;
  rTmp1 ← rSrc + rTmp1;
  *rTmp1 ← rTmp2;
  rIdx ← rIdx + rOne ]

private def shiftLoop : Code .standard 20 := ram[
  rIdx ← #0;
  while rIdx < rLim do [⟪shiftBody⟫] ]

private theorem shiftLoop_spec {w arrBase upper count : ℕ} {x : Data 20}
    (hbdd : x.Bounded w)
    (ho : x.regs rOne = 1) (hsrc : x.regs rSrc = arrBase)
    (hdst : x.regs rDst = upper) (hlim : x.regs rLim = count)
    (hcount : count ≤ upper)
    (hf_arr : Fits w (arrBase + upper)) :
    ∃ y, ExecWithin w shiftLoop x y (9 * count + 3) ∧
      y.Bounded w ∧
      y.mem = shiftArrRight arrBase upper count x.mem ∧
      ∀ reg : Fin 20, reg ≠ rIdx → reg ≠ rTmp1 → reg ≠ rTmp2 → y.regs reg = x.regs reg := by
  let x₀ := x.set rIdx 0
  have h0 : ExecWithin w (ram[ rIdx ← #0 ] : Code .standard 20) x x₀ 1 :=
    ExecWithin.const (hf_arr.of_le (Nat.zero_le _))
  let P (j : ℕ) (z : Data 20) : Prop :=
    z.Bounded w ∧
      z.mem = shiftArrRight arrBase upper j x.mem ∧
      ∀ reg : Fin 20, reg ≠ rIdx → reg ≠ rTmp1 → reg ≠ rTmp2 → z.regs reg = x.regs reg
  have hP0 : P (x₀.regs rIdx) x₀ := by
    have hidx0 : x₀.regs rIdx = 0 := rfl
    rw [hidx0]
    refine ⟨hbdd.set (hf_arr.of_le (Nat.zero_le _)), rfl, fun reg h1 _ _ => ?_⟩
    dsimp only [x₀]
    exact Data.set_regs_of_ne h1 _
  obtain ⟨y, hy_loop, hPN, _⟩ := ExecWithin.loop_count (w := w) (N := count) (T := 7)
    (index := rIdx) (limit := rLim) (body := shiftBody) P
    (fun z hz => (hz.2.2 rLim (by decide) (by decide) (by decide)).trans hlim)
    (fun z ⟨hb_z, hmem_z, hreg_z⟩ hj_lt => by
      set j := z.regs rIdx
      have ho_z : z.regs rOne = 1 := (hreg_z rOne (by decide) (by decide) (by decide)).trans ho
      have hsrc_z : z.regs rSrc = arrBase :=
        (hreg_z rSrc (by decide) (by decide) (by decide)).trans hsrc
      have hdst_z : z.regs rDst = upper :=
        (hreg_z rDst (by decide) (by decide) (by decide)).trans hdst
      have hf_d1 : Fits w (upper - j) := hf_arr.of_le (by omega)
      have hf_d2 : Fits w (upper - j - 1) := hf_arr.of_le (by omega)
      have hf_a2 : Fits w (arrBase + (upper - j - 1)) := hf_arr.of_le (by omega)
      have hf_a1 : Fits w (arrBase + (upper - j)) := hf_arr.of_le (by omega)
      have hf_j1 : Fits w (j + 1) := hf_arr.of_le (by omega)
      let z' : Data 20 :=
        ((((((z.set rTmp1 (upper - j)).set rTmp2 (upper - j - 1)).set rTmp2
          (arrBase + (upper - j - 1))).set rTmp2 (z.mem (arrBase + (upper - j - 1)))).set rTmp1
          (arrBase + (upper - j))).write (arrBase + (upper - j))
          (z.mem (arrBase + (upper - j - 1)))).set rIdx (j + 1)
      have he_b : ExecWithin w shiftBody z z' 7 := by
        unfold shiftBody
        dsimp only [z']
        wram_exec [ho_z, hsrc_z, hdst_z, hf_d1, hf_d2, hf_a2, hf_a1, hf_j1]
      have hz'_mem : z'.mem = shiftArrRight arrBase upper (j + 1) x.mem := by
        have hsub : upper - j - 1 = upper - 1 - j := by omega
        dsimp only [z', shiftArrRight]
        rw [hsub, ← hmem_z]
        wram_simp
      refine ⟨z', he_b, ⟨he_b.bounded hb_z, hz'_mem, fun reg h1 h2 h3 => ?_⟩, rfl⟩
      dsimp only [z']
      simp only [Data.set_regs_of_ne h1 _, Data.write_regs, Data.set_regs_of_ne h2 _,
        Data.set_regs_of_ne h3 _]
      exact hreg_z reg h1 h2 h3)
    (Nat.zero_le count) hP0
  have hfull : ExecWithin w shiftLoop x y (9 * count + 3) :=
    (h0.seq hy_loop).mono (by have : x₀.regs rIdx = 0 := rfl; rw [this]; omega)
  exact ⟨y, hfull, hPN.1, hPN.2.1, hPN.2.2⟩

private def slotScanBody : Code .standard 20 := ram[
  rTmp1 ← rSrc + rIdx;
  rTmp2 ← *rTmp1;
  if rTmp2 < rKey then [
    rSlot ← rSlot + rOne
  ] else [
    rZero ← #0
  ];
  rIdx ← rIdx + rOne ]

private def slotScanLoop : Code .standard 20 := ram[
  rSlot ← #0;
  rIdx ← #0;
  while rIdx < rLim do [⟪slotScanBody⟫] ]

private theorem slotScanLoop_spec {w base t u k m : ℕ} {x : Data 20}
    (hbdd : x.Bounded w)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hkey : x.regs rKey = k)
    (hsrc : x.regs rSrc = nodeAddr base t u + 2)
    (hlim : x.regs rLim = m)
    (hf_keys : Fits w (nodeAddr base t u + 2 + m)) :
    ∃ y, ExecWithin w slotScanLoop x y (8 * m + 4) ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs rSlot = slotCount base t x.mem u k m ∧
      y.regs rZero = 0 ∧
      ∀ reg : Fin 20,
        reg ≠ rSlot → reg ≠ rIdx → reg ≠ rTmp1 → reg ≠ rTmp2 → reg ≠ rZero →
          y.regs reg = x.regs reg := by
  have hf0 : Fits w 0 := hf_keys.of_le (Nat.zero_le _)
  let x₀ := (x.set rSlot 0).set rIdx 0
  let P (j : ℕ) (z : Data 20) : Prop :=
    z.Bounded w ∧
      z.mem = x.mem ∧
      z.regs rSlot = slotCount base t x.mem u k j ∧
      z.regs rZero = 0 ∧
      ∀ reg : Fin 20,
        reg ≠ rSlot → reg ≠ rIdx → reg ≠ rTmp1 → reg ≠ rTmp2 → reg ≠ rZero →
          z.regs reg = x.regs reg
  have hP0 : P (x₀.regs rIdx) x₀ := by
    have hidx0 : x₀.regs rIdx = 0 := rfl
    rw [hidx0]
    refine ⟨(hbdd.set hf0).set hf0, rfl, rfl, hz, fun reg h1 h2 _ _ _ => ?_⟩
    dsimp only [x₀]
    simp only [Data.set_regs_of_ne h2 _, Data.set_regs_of_ne h1 _]
  obtain ⟨y, hy_loop, hPN, _⟩ := ExecWithin.loop_count (w := w) (N := m) (T := 6)
    (index := rIdx) (limit := rLim) (body := slotScanBody) P
    (fun z hz => (hz.2.2.2.2 rLim (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hlim)
    (fun z ⟨hb_z, hmem_z, hslot_z, hz_z, hreg_z⟩ hj_lt => by
      set j := z.regs rIdx
      have hj_eq : z.regs rIdx = j := rfl
      have ho_z : z.regs rOne = 1 :=
        (hreg_z rOne (by decide) (by decide) (by decide) (by decide) (by decide)).trans ho
      have hk_z : z.regs rKey = k :=
        (hreg_z rKey (by decide) (by decide) (by decide) (by decide) (by decide)).trans hkey
      have hsrc_z : z.regs rSrc = nodeAddr base t u + 2 :=
        (hreg_z rSrc (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsrc
      have hslot_le : slotCount base t x.mem u k j ≤ j := by
        clear hslot_z
        induction j with
        | zero => simp [slotCount]
        | succ n ihn => rw [slotCount]; split_ifs <;> omega
      have hf_aj : Fits w (nodeAddr base t u + 2 + j) := hf_keys.of_le (by omega)
      have hf_j1 : Fits w (j + 1) := hf_keys.of_le (by omega)
      have hf_s1 : Fits w (slotCount base t x.mem u k j + 1) := hf_keys.of_le (by omega)
      have hkj_eq : z.mem (nodeAddr base t u + 2 + j) = keyAt base t x.mem u j := by
        rw [hmem_z]; rfl
      by_cases hlt : keyAt base t x.mem u j < k
      · let z' : Data 20 :=
          ((((z.set rTmp1 (nodeAddr base t u + 2 + j)).set rTmp2
            (keyAt base t x.mem u j)).set rSlot (slotCount base t x.mem u k j + 1)).set rIdx
            (j + 1))
        have he_b : ExecWithin w slotScanBody z z' 6 := by
          unfold slotScanBody
          dsimp only [z']
          wram_exec [hj_eq, ho_z, hk_z, hsrc_z, hslot_z, hkj_eq, hlt, hf_aj, hf_j1, hf_s1]
        refine ⟨z', he_b, ⟨he_b.bounded hb_z, hmem_z, ?_, hz_z, fun reg h1 h2 h3 h4 h5 => ?_⟩,
          rfl⟩
        · simp only [z', slotCount, hlt, ↓reduceIte]
          wram_simp
        · dsimp only [z']
          simp only [Data.set_regs_of_ne h2 _, Data.set_regs_of_ne h1 _,
            Data.set_regs_of_ne h4 _, Data.set_regs_of_ne h3 _]
          exact hreg_z reg h1 h2 h3 h4 h5
      · let z' : Data 20 :=
          ((((z.set rTmp1 (nodeAddr base t u + 2 + j)).set rTmp2
            (keyAt base t x.mem u j)).set rZero 0).set rIdx (j + 1))
        have he_b : ExecWithin w slotScanBody z z' 6 := by
          unfold slotScanBody
          dsimp only [z']
          wram_exec [hj_eq, ho_z, hk_z, hsrc_z, hslot_z, hkj_eq, hlt, hf_aj, hf_j1, hf0]
        refine ⟨z', he_b, ⟨he_b.bounded hb_z, hmem_z, ?_, ?_, fun reg h1 h2 h3 h4 h5 => ?_⟩, rfl⟩
        · simp only [z', slotCount, hlt, ↓reduceIte, Nat.add_zero]
          wram_simp
          exact hslot_z
        · dsimp only [z']; wram_simp
        · dsimp only [z']
          simp only [Data.set_regs_of_ne h2 _, Data.set_regs_of_ne h5 _,
            Data.set_regs_of_ne h4 _, Data.set_regs_of_ne h3 _]
          exact hreg_z reg h1 h2 h3 h4 h5)
    (Nat.zero_le m) hP0
  have hfull : ExecWithin w slotScanLoop x y (8 * m + 4) :=
    ((ExecWithin.const hf0).seq ((ExecWithin.const hf0).seq hy_loop)).mono
      (by have : x₀.regs rIdx = 0 := rfl; rw [this]; omega)
  exact ⟨y, hfull, hPN.1, hPN.2.1, hPN.2.2.1, hPN.2.2.2.1, hPN.2.2.2.2⟩

/-! ## 5. Shared node-header loader -/

private def loadNodeHeader : Code .standard 20 := ram[
  rSrc ← rCur * rStride;
  rSrc ← rBase + rSrc;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rTmp1 ← rSrc + rOne;
  rNumK ← *rTmp1;
  rSrc ← rTmp1 + rOne;
  rLim ← rNumK ]

private theorem loadNodeHeader_spec {w base capNodes t u : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes)
    (hbdd : x.Bounded w)
    (hfit : Fits w (base + arenaWords t capNodes))
    (ho : x.regs rOne = 1) (hbase : x.regs rBase = base)
    (hstride : x.regs rStride = 6 * t) (hcur : x.regs rCur = u) :
    ∃ y, ExecWithin w loadNodeHeader x y 8 ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs rSrc = nodeAddr base t u + 2 ∧
      y.regs rNumK = numKeys base t x.mem u ∧
      y.regs rLim = numKeys base t x.mem u ∧
      ∀ reg : Fin 20,
        reg ≠ rSrc → reg ≠ rTmp1 → reg ≠ rNumK → reg ≠ rLim → y.regs reg = x.regs reg := by
  have ha_le : nodeAddr base t u + 6 * t ≤ base + arenaWords t capNodes :=
    nodeAddr_add_le_arena hu_cap le_rfl
  have hf_mul : Fits w (u * (6 * t)) := hfit.of_le (by
    simp only [nodeAddr, nodeStride] at ha_le; omega)
  have hf_b0 : Fits w (base + u * (6 * t)) := hfit.of_le (by
    simp only [nodeAddr, nodeStride] at ha_le; omega)
  have hf_b1 : Fits w (base + u * (6 * t) + 1) := hfit.of_le (by
    simp only [nodeAddr, nodeStride] at ha_le; omega)
  have hf_au : Fits w (nodeAddr base t u) := hfit.of_le (by omega)
  have hf_au1 : Fits w (nodeAddr base t u + 1) := hfit.of_le (by omega)
  have hf_au2 : Fits w (nodeAddr base t u + 2) := hfit.of_le (by omega)
  have hna_eq : base + u * (6 * t) + 1 + 1 = nodeAddr base t u := by
    simp only [nodeAddr, nodeStride]; omega
  let m := numKeys base t x.mem u
  let y : Data 20 :=
    (((((((x.set rSrc (u * (6 * t))).set rSrc (base + u * (6 * t))).set rSrc
      (base + u * (6 * t) + 1)).set rSrc (nodeAddr base t u)).set rTmp1
      (nodeAddr base t u + 1)).set rNumK m).set rSrc (nodeAddr base t u + 2)).set rLim m
  have he : ExecWithin w loadNodeHeader x y 8 := by
    unfold loadNodeHeader
    dsimp only [y, m, numKeys]
    wram_exec [ho, hbase, hstride, hcur, hna_eq, hf_mul, hf_b0, hf_b1, hf_au, hf_au1, hf_au2]
  refine ⟨y, he, he.bounded hbdd, rfl, rfl, ?_, rfl, fun reg h1 h2 h3 h4 => ?_⟩
  · dsimp only [y, m]; wram_simp
  · dsimp only [y]
    simp only [Data.set_regs_of_ne h4 _, Data.set_regs_of_ne h1 _, Data.set_regs_of_ne h3 _,
      Data.set_regs_of_ne h2 _]

private def loadAndScan : Code .standard 20 := ram[
  ⟪loadNodeHeader⟫;
  ⟪slotScanLoop⟫ ]

private theorem loadAndScan_spec {w base capNodes t u k : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hm_le : numKeys base t x.mem u ≤ 2 * t - 1)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t) (hkey : x.regs rKey = k) (hcur : x.regs rCur = u) :
    let m := numKeys base t x.mem u
    ∃ y, ExecWithin w loadAndScan x y (8 * m + 12) ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧
      y.regs rStride = 6 * t ∧ y.regs rKey = k ∧ y.regs rCur = u ∧
      y.regs rSrc = nodeAddr base t u + 2 ∧
      y.regs rNumK = m ∧
      y.regs rSlot = slotCount base t x.mem u k m ∧
      ∀ reg : Fin 20,
        reg ≠ rSrc → reg ≠ rNumK → reg ≠ rLim → reg ≠ rSlot →
          reg ≠ rIdx → reg ≠ rTmp1 → reg ≠ rTmp2 → reg ≠ rZero → y.regs reg = x.regs reg := by
  set m := numKeys base t x.mem u
  have ha_le : nodeAddr base t u + 6 * t ≤ base + arenaWords t capNodes :=
    nodeAddr_add_le_arena hu_cap le_rfl
  have hf_keys : Fits w (nodeAddr base t u + 2 + m) := hfit.of_le (by omega)
  obtain ⟨x₁, h1, hb₁, hmem₁, hsrc₁, hnk₁, hlim₁, hreg₁⟩ :=
    loadNodeHeader_spec ht hu_cap hbdd hfit ho hbase hstride hcur
  have hz₁ : x₁.regs rZero = 0 :=
    (hreg₁ rZero (by decide) (by decide) (by decide) (by decide)).trans hz
  have ho₁ : x₁.regs rOne = 1 :=
    (hreg₁ rOne (by decide) (by decide) (by decide) (by decide)).trans ho
  have hk₁ : x₁.regs rKey = k :=
    (hreg₁ rKey (by decide) (by decide) (by decide) (by decide)).trans hkey
  obtain ⟨x₂, h2, hb₂, hmem₂, hslot₂, hz₂, hreg₂⟩ :=
    slotScanLoop_spec hb₁ hz₁ ho₁ hk₁ hsrc₁ hlim₁ hf_keys
  rw [hmem₁] at hslot₂ hmem₂
  have hkeep : ∀ reg : Fin 20,
      reg ≠ rSrc → reg ≠ rNumK → reg ≠ rLim → reg ≠ rSlot →
        reg ≠ rIdx → reg ≠ rTmp1 → reg ≠ rTmp2 → reg ≠ rZero → x₂.regs reg = x.regs reg :=
    fun reg hs hn hl hsl hi ht1 ht2 hzr =>
      (hreg₂ reg hsl hi ht1 ht2 hzr).trans (hreg₁ reg hs ht1 hn hl)
  refine ⟨x₂, (h1.seq h2).mono (by omega), hb₂, hmem₂, hz₂,
    (hkeep rOne (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ho,
    (hkeep rBase (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hbase,
    (hkeep rDeg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hdeg,
    (hkeep rStride (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hstride,
    (hkeep rKey (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hkey,
    (hkeep rCur (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hcur,
    (hreg₂ rSrc (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsrc₁,
    (hreg₂ rNumK (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnk₁,
    hslot₂, hkeep⟩

/-! ## 6. Lookup (`lookupCode`, `O(t log_t n)`) -/

private def lookupDescendOrStop : Code .standard 20 := ram[
  rTmp1 ← rSrc - rOne;
  rTmp1 ← rTmp1 - rOne;
  rTmp2 ← *rTmp1;
  if rTmp2 = rZero then [
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rSlot;
    rCur ← *rTmp1
  ] else [
    rActive ← #0
  ] ]

private def lookupBranch : Code .standard 20 := ram[
  if rSlot < rNumK then [
    rTmp1 ← rSrc + rSlot;
    rTmp2 ← *rTmp1;
    if rTmp2 = rKey then [
      rFound ← #1;
      rTmp1 ← rSrc + rDeg;
      rTmp1 ← rTmp1 + rDeg;
      rTmp1 ← rTmp1 - rOne;
      rTmp1 ← rTmp1 + rSlot;
      rVal ← *rTmp1;
      rActive ← #0
    ] else [
      ⟪lookupDescendOrStop⟫
    ]
  ] else [
    ⟪lookupDescendOrStop⟫
  ] ]

private def lookupStep : Code .standard 20 := ram[
  ⟪loadAndScan⟫;
  ⟪lookupBranch⟫ ]

private def lookupLoop : Code .standard 20 := ram[
  while rZero < rActive do [⟪lookupStep⟫] ]

/-- Look up key `rKey` in the arena at `rBase` of minimum degree `rDeg`, setting `rFound` (`1` or
`0`) and `rVal` (found value or `0`) without modifying memory. -/
def lookupCode : Code .standard 20 := ram[
  rZero ← #0;
  rOne ← #1;
  rFound ← #0;
  rVal ← #0;
  rTmp1 ← rBase + rOne;
  rCnt ← *rTmp1;
  if rCnt = rZero then [
    rZero ← #0
  ] else [
    rStride ← rDeg + rDeg;
    rTmp1 ← rStride + rStride;
    rStride ← rStride + rTmp1;
    rCur ← *rBase;
    rActive ← #1;
    ⟪lookupLoop⟫
  ] ]

private theorem lookupDescendOrStop_spec {w base capNodes t u slot : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hslot : slot ≤ 2 * t - 1)
    (hfit : Fits w (base + arenaWords t capNodes))
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hdeg : x.regs rDeg = t)
    (hsrc : x.regs rSrc = nodeAddr base t u + 2) (hslot_reg : x.regs rSlot = slot) :
    ∃ y, ExecWithin w lookupDescendOrStop x y 10 ∧
      y.mem = x.mem ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = x.regs rBase ∧ y.regs rDeg = t ∧
      y.regs rStride = x.regs rStride ∧ y.regs rKey = x.regs rKey ∧
      y.regs rFound = x.regs rFound ∧ y.regs rVal = x.regs rVal ∧
      (if leafFlag base t x.mem u = 0 then
        y.regs rCur = childAt base t x.mem u slot ∧ y.regs rActive = x.regs rActive
      else
        y.regs rActive = 0) := by
  have ha_le : nodeAddr base t u + 6 * t ≤ base + arenaWords t capNodes :=
    nodeAddr_add_le_arena hu_cap le_rfl
  have hf_au1 : Fits w (nodeAddr base t u + 2 - 1) := hfit.of_le (by omega)
  have hf_au : Fits w (nodeAddr base t u) := hfit.of_le (by omega)
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  have hsub2 : nodeAddr base t u + 2 - 1 - 1 = nodeAddr base t u := by omega
  have hlf_eq : x.mem (nodeAddr base t u) = leafFlag base t x.mem u := rfl
  by_cases hlf0 : leafFlag base t x.mem u = 0
  · have hf_t1 : Fits w (nodeAddr base t u + t) := hfit.of_le (by omega)
    have hf_t2 : Fits w (nodeAddr base t u + t + t) := hfit.of_le (by omega)
    have hf_t3 : Fits w (nodeAddr base t u + t + t + t) := hfit.of_le (by omega)
    have hf_t4 : Fits w (nodeAddr base t u + 4 * t) := hfit.of_le (by omega)
    have hf_cs : Fits w (nodeAddr base t u + 4 * t + slot) := hfit.of_le (by omega)
    have hadd4 : nodeAddr base t u + t + t + t + t = nodeAddr base t u + 4 * t := by omega
    let y : Data 20 :=
      ((((((((x.set rTmp1 (nodeAddr base t u + 2 - 1)).set rTmp1 (nodeAddr base t u)).set rTmp2
        0).set rTmp1 (nodeAddr base t u + t)).set rTmp1 (nodeAddr base t u + t + t)).set rTmp1
        (nodeAddr base t u + t + t + t)).set rTmp1 (nodeAddr base t u + 4 * t)).set rTmp1
        (nodeAddr base t u + 4 * t + slot)).set rCur (childAt base t x.mem u slot)
    have he : ExecWithin w lookupDescendOrStop x y 10 := by
      unfold lookupDescendOrStop
      dsimp only [y, childAt]
      wram_exec [hz, ho, hdeg, hsrc, hslot_reg, hsub2, hlf_eq, hlf0, hadd4,
        hf_au1, hf_au, hf_t1, hf_t2, hf_t3, hf_t4, hf_cs]
    refine ⟨y, he, rfl,
      by dsimp only [y]; wram_simp; exact hz,
      by dsimp only [y]; wram_simp; exact ho,
      by dsimp only [y]; wram_simp,
      by dsimp only [y]; wram_simp; exact hdeg,
      by dsimp only [y]; wram_simp,
      by dsimp only [y]; wram_simp,
      by dsimp only [y]; wram_simp,
      by dsimp only [y]; wram_simp,
      ?_⟩
    simp only [hlf0, ↓reduceIte]
    exact ⟨rfl, by dsimp only [y]; wram_simp⟩
  · let y : Data 20 :=
      (((x.set rTmp1 (nodeAddr base t u + 2 - 1)).set rTmp1 (nodeAddr base t u)).set rTmp2
        (leafFlag base t x.mem u)).set rActive 0
    have he : ExecWithin w lookupDescendOrStop x y 10 := by
      unfold lookupDescendOrStop
      dsimp only [y]
      wram_exec [hz, ho, hsrc, hsub2, hlf_eq, hlf0, hf_au1, hf_au, hf0]
    refine ⟨y, he, rfl,
      by dsimp only [y]; wram_simp; exact hz,
      by dsimp only [y]; wram_simp; exact ho,
      by dsimp only [y]; wram_simp,
      by dsimp only [y]; wram_simp; exact hdeg,
      by dsimp only [y]; wram_simp,
      by dsimp only [y]; wram_simp,
      by dsimp only [y]; wram_simp,
      by dsimp only [y]; wram_simp,
      ?_⟩
    simp only [hlf0, ↓reduceIte]
    rfl

private theorem lookupBranch_spec {w base capNodes t u k m slot : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hm_le : m ≤ 2 * t - 1) (hslot : slot ≤ m)
    (hfit : Fits w (base + arenaWords t capNodes))
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hdeg : x.regs rDeg = t)
    (hkey : x.regs rKey = k) (hnk : x.regs rNumK = m)
    (hsrc : x.regs rSrc = nodeAddr base t u + 2) (hslot_reg : x.regs rSlot = slot) :
    ∃ y, ExecWithin w lookupBranch x y 15 ∧
      y.mem = x.mem ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = x.regs rBase ∧ y.regs rDeg = t ∧
      y.regs rStride = x.regs rStride ∧ y.regs rKey = k ∧
      (if slot < m ∧ keyAt base t x.mem u slot = k then
        y.regs rFound = 1 ∧ y.regs rVal = valAt base t x.mem u slot ∧ y.regs rActive = 0
      else if leafFlag base t x.mem u = 0 then
        y.regs rCur = childAt base t x.mem u slot ∧ y.regs rActive = x.regs rActive ∧
          y.regs rFound = x.regs rFound ∧ y.regs rVal = x.regs rVal
      else
        y.regs rActive = 0 ∧ y.regs rFound = x.regs rFound ∧ y.regs rVal = x.regs rVal) := by
  have ha_le : nodeAddr base t u + 6 * t ≤ base + arenaWords t capNodes :=
    nodeAddr_add_le_arena hu_cap le_rfl
  by_cases hlt_m : slot < m
  · have hf_ks : Fits w (nodeAddr base t u + 2 + slot) := hfit.of_le (by omega)
    have hks_eq : x.mem (nodeAddr base t u + 2 + slot) = keyAt base t x.mem u slot := rfl
    by_cases heq_k : keyAt base t x.mem u slot = k
    · have hf1 : Fits w 1 := hfit.of_le (by omega)
      have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
      have hf_v1 : Fits w (nodeAddr base t u + 2 + t) := hfit.of_le (by omega)
      have hf_v2 : Fits w (nodeAddr base t u + 2 + t + t) := hfit.of_le (by omega)
      have hf_v3 : Fits w (nodeAddr base t u + (2 * t + 1)) := hfit.of_le (by omega)
      have hf_vs : Fits w (nodeAddr base t u + (2 * t + 1) + slot) := hfit.of_le (by omega)
      have hv_arith : nodeAddr base t u + 2 + t + t - 1 = nodeAddr base t u + (2 * t + 1) := by
        omega
      have hvs_eq : x.mem (nodeAddr base t u + (2 * t + 1) + slot) = valAt base t x.mem u slot :=
        rfl
      let y : Data 20 :=
        ((((((((x.set rTmp1 (nodeAddr base t u + 2 + slot)).set rTmp2 k).set rFound 1).set
          rTmp1 (nodeAddr base t u + 2 + t)).set rTmp1
          (nodeAddr base t u + 2 + t + t)).set rTmp1
          (nodeAddr base t u + (2 * t + 1))).set rTmp1
          (nodeAddr base t u + (2 * t + 1) + slot)).set rVal
          (valAt base t x.mem u slot)).set rActive 0
      have he : ExecWithin w lookupBranch x y 15 := by
        unfold lookupBranch
        dsimp only [y]
        wram_exec [ho, hdeg, hkey, hnk, hsrc, hslot_reg, hlt_m, hks_eq, heq_k, hv_arith, hvs_eq,
          hf_ks, hf1, hf0, hf_v1, hf_v2, hf_v3, hf_vs]
      refine ⟨y, he, rfl,
        by dsimp only [y]; wram_simp; exact hz,
        by dsimp only [y]; wram_simp; exact ho,
        by dsimp only [y]; wram_simp,
        by dsimp only [y]; wram_simp; exact hdeg,
        by dsimp only [y]; wram_simp,
        by dsimp only [y]; wram_simp; exact hkey,
        ?_⟩
      simp only [hlt_m, heq_k, and_self, ↓reduceIte]
      exact ⟨by dsimp only [y]; wram_simp, by dsimp only [y]; wram_simp, rfl⟩
    · let x' := (x.set rTmp1 (nodeAddr base t u + 2 + slot)).set rTmp2 (keyAt base t x.mem u slot)
      obtain ⟨y, hdesc, hmem_y, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hfnd_y, hval_y, hbr⟩ :=
        lookupDescendOrStop_spec (x := x') ht hu_cap (by omega) hfit hz ho hdeg hsrc hslot_reg
      have he : ExecWithin w lookupBranch x y 15 := by
        unfold lookupBranch
        apply WP.execWithin
        wram_exec [hnk, hsrc, hslot_reg, hkey, hlt_m, hks_eq, heq_k, hf_ks]
        exact WP.of_execWithin hdesc ⟨by omega, rfl⟩
      refine ⟨y, he, hmem_y, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y.trans hkey, ?_⟩
      simp only [hlt_m, heq_k, and_false, ↓reduceIte]
      change (if leafFlag base t x'.mem u = 0 then _ else _) at hbr
      dsimp only [x'] at hbr hb_y hst_y hfnd_y hval_y
      wram_simp at hbr hb_y hst_y hfnd_y hval_y
      split_ifs at hbr ⊢
      · exact ⟨hbr.1, hbr.2, hfnd_y, hval_y⟩
      · exact ⟨hbr, hfnd_y, hval_y⟩
  · obtain ⟨y, hdesc, hmem_y, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hfnd_y, hval_y, hbr⟩ :=
      lookupDescendOrStop_spec (x := x) ht hu_cap (by omega) hfit hz ho hdeg hsrc hslot_reg
    have he : ExecWithin w lookupBranch x y 15 := by
      unfold lookupBranch
      apply WP.execWithin
      wram_exec [hnk, hslot_reg, hlt_m]
      exact WP.of_execWithin hdesc ⟨by omega, rfl⟩
    refine ⟨y, he, hmem_y, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y.trans hkey, ?_⟩
    simp only [hlt_m, false_and, ↓reduceIte]
    split_ifs at hbr ⊢
    · exact ⟨hbr.1, hbr.2, hfnd_y, hval_y⟩
    · exact ⟨hbr, hfnd_y, hval_y⟩

private theorem lookupStep_spec {w base capNodes t u k : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hm_le : numKeys base t x.mem u ≤ 2 * t - 1)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t) (hkey : x.regs rKey = k) (hcur : x.regs rCur = u) :
    let m := numKeys base t x.mem u
    let slot := slotCount base t x.mem u k m
    ∃ y, ExecWithin w lookupStep x y (16 * t + 19) ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧
      y.regs rStride = 6 * t ∧ y.regs rKey = k ∧
      (if slot < m ∧ keyAt base t x.mem u slot = k then
        y.regs rFound = 1 ∧ y.regs rVal = valAt base t x.mem u slot ∧ y.regs rActive = 0
      else if leafFlag base t x.mem u = 0 then
        y.regs rCur = childAt base t x.mem u slot ∧ y.regs rActive = x.regs rActive ∧
          y.regs rFound = x.regs rFound ∧ y.regs rVal = x.regs rVal
      else
        y.regs rActive = 0 ∧ y.regs rFound = x.regs rFound ∧ y.regs rVal = x.regs rVal) := by
  set m := numKeys base t x.mem u
  set slot := slotCount base t x.mem u k m
  have hslot_le : slot ≤ m := by
    dsimp only [slot]
    induction m with
    | zero => simp [slotCount]
    | succ n ihn => rw [slotCount]; split_ifs <;> omega
  obtain ⟨x₂, h12, _, hmem₂, hz₂, ho₂, hb₂_reg, hd₂, hst₂, hk₂, _, hsrc₂, hnk₂, hslot₂, hreg₂⟩ :=
    loadAndScan_spec ht hu_cap hm_le hbdd hfit hz ho hbase hdeg hstride hkey hcur
  have hact₂ : x₂.regs rActive = x.regs rActive :=
    hreg₂ rActive (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have hfnd₂ : x₂.regs rFound = x.regs rFound :=
    hreg₂ rFound (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have hval₂ : x₂.regs rVal = x.regs rVal :=
    hreg₂ rVal (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  obtain ⟨y, h3, hmem₃, hz₃, ho₃, hb₃, hd₃, hst₃, hk₃, hbr₃⟩ :=
    lookupBranch_spec ht hu_cap hm_le hslot_le hfit hz₂ ho₂ hd₂ hk₂ hnk₂ hsrc₂ hslot₂
  have hfull : ExecWithin w lookupStep x y (16 * t + 19) :=
    (h12.seq h3).mono (by omega)
  rw [hmem₂] at hbr₃
  rw [hact₂, hfnd₂, hval₂] at hbr₃
  exact ⟨y, hfull, hfull.bounded hbdd, hmem₃.trans hmem₂, hz₃, ho₃, hb₃.trans hb₂_reg, hd₃,
    hst₃.trans hst₂, hk₃, hbr₃⟩

private theorem lookupLoop_spec {l w base capNodes t u k : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hv : ValidNode l base t x.mem u) (hs : SortedNode l base t x.mem u)
    (hcap : readNodeSet l base t x.mem u ⊆ Finset.range capNodes)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t) (hkey : x.regs rKey = k)
    (hcur : x.regs rCur = u) (hact : x.regs rActive = 1)
    (hfound0 : x.regs rFound = 0) (hval0 : x.regs rVal = 0) :
    ∃ y, ExecWithin w lookupLoop x y ((16 * t + 21) * (l + 1) + 2) ∧
      y.mem = x.mem ∧
      y.regs rBase = base ∧
      y.regs rDeg = t ∧
      y.regs rFound = (if (BTree.lookup k (readTree l base t x.mem u)).isSome then 1 else 0) ∧
      y.regs rVal = (BTree.lookup k (readTree l base t x.mem u)).getD 0 := by
  induction l generalizing u x with
  | zero =>
    have hu_cap : u < capNodes :=
      Finset.mem_range.mp (hcap (self_mem_readNodeSet 0 base t x.mem u))
    obtain ⟨y, hstep, _, hmem_y, hz_y, _, hb_y, hd_y, _, _, hbr⟩ :=
      lookupStep_spec ht hu_cap hv.numKeys_le hbdd hfit hz ho hbase hdeg hstride hkey hcur
    set m := numKeys base t x.mem u
    set slot := slotCount base t x.mem u k m
    have hsc := slotCount_spec (k := k) (fun _ _ => hs.keys_strict) m le_rfl
    have hcond_in : (Cond.lt rZero rActive).Holds x := by
      simp only [Cond.holds_lt, hz, hact, Nat.zero_lt_one]
    by_cases hhit : slot < m ∧ keyAt base t x.mem u slot = k
    · simp only [hhit] at hbr
      have hexit : ExecWithin w lookupLoop y y 2 :=
        ExecWithin.loop_exit (by simp only [Cond.holds_lt, hz_y, hbr.2.2, Nat.lt_irrefl,
          not_false_eq_true])
      have hlk := lookup_readTree_eq_some hs hhit.1 hhit.2
      refine ⟨y, (hstep.loop_iter hcond_in hexit).mono (by omega), hmem_y, hb_y, hd_y, ?_, ?_⟩
      · rw [hlk, hbr.1]; rfl
      · rw [hlk, hbr.2.1]; rfl
    · have hlf_ne : leafFlag base t x.mem u ≠ 0 := by simp [hv.leafFlag_eq]
      simp only [hhit, hlf_ne, ↓reduceIte] at hbr
      have hexit : ExecWithin w lookupLoop y y 2 :=
        ExecWithin.loop_exit (by simp only [Cond.holds_lt, hz_y, hbr.1, Nat.lt_irrefl,
          not_false_eq_true])
      have hne_all : ∀ i < m, keyAt base t x.mem u i ≠ k := by
        intro i hi
        rcases lt_or_ge i slot with hlt | hge
        · exact (hsc.2.1 i hlt).ne
        · have hle_k := hsc.2.2 i hge hi
          rcases eq_or_lt_of_le hge with rfl | hgt
          · exact fun heq => hhit ⟨hi, heq⟩
          · have hlt_slot : slot < m := by omega
            have hk_lt : k < keyAt base t x.mem u slot := by
              have hle_s := hsc.2.2 slot le_rfl hlt_slot
              have hne_s : keyAt base t x.mem u slot ≠ k := fun heq => hhit ⟨hlt_slot, heq⟩
              omega
            exact (hk_lt.trans (hs.keys_strict hgt hi)).ne'
      have hlk := lookup_readTree_leaf_none hs hne_all
      refine ⟨y, (hstep.loop_iter hcond_in hexit).mono (by omega), hmem_y, hb_y, hd_y, ?_, ?_⟩
      · rw [hlk, hbr.2.1, hfound0]; rfl
      · rw [hlk, hbr.2.2, hval0]; rfl
  | succ l ih =>
    have hu_cap : u < capNodes :=
      Finset.mem_range.mp (hcap (self_mem_readNodeSet (l + 1) base t x.mem u))
    obtain ⟨x₁, hstep, hb₁, hmem₁, hz₁, ho₁, hb₁_reg, hd₁, hst₁, hk₁, hbr⟩ :=
      lookupStep_spec ht hu_cap hv.numKeys_le hbdd hfit hz ho hbase hdeg hstride hkey hcur
    set m := numKeys base t x.mem u
    set slot := slotCount base t x.mem u k m
    have hsc := slotCount_spec (k := k) (fun _ _ => hs.keys_strict) m le_rfl
    have hcond_in : (Cond.lt rZero rActive).Holds x := by
      simp only [Cond.holds_lt, hz, hact, Nat.zero_lt_one]
    have hmul_step : (16 * t + 21) * (l + 1 + 1) = (16 * t + 21) * (l + 1) + (16 * t + 21) :=
      Nat.mul_succ _ _
    by_cases hhit : slot < m ∧ keyAt base t x.mem u slot = k
    · simp only [hhit] at hbr
      have hexit : ExecWithin w lookupLoop x₁ x₁ 2 :=
        ExecWithin.loop_exit (by simp only [Cond.holds_lt, hz₁, hbr.2.2, Nat.lt_irrefl,
          not_false_eq_true])
      have hlk := lookup_readTree_eq_some hs hhit.1 hhit.2
      refine ⟨x₁, (hstep.loop_iter hcond_in hexit).mono (by omega), hmem₁, hb₁_reg, hd₁, ?_, ?_⟩
      · rw [hlk, hbr.1]; rfl
      · rw [hlk, hbr.2.1]; rfl
    · simp only [hhit, hv.leafFlag_eq, Nat.succ_ne_zero, ↓reduceIte] at hbr
      have hslot_le : slot ≤ m := hsc.1
      have hgt_all : ∀ i, slot ≤ i → i < m → k < keyAt base t x.mem u i := by
        intro i hge hi
        have hle_i := hsc.2.2 i hge hi
        rcases eq_or_lt_of_le hge with rfl | hgt
        · have hne_s : keyAt base t x.mem u slot ≠ k := fun heq => hhit ⟨hi, heq⟩
          omega
        · have hle_s := hsc.2.2 slot le_rfl (by omega)
          have hne_s : keyAt base t x.mem u slot ≠ k := fun heq => hhit ⟨by omega, heq⟩
          have hk_lt : k < keyAt base t x.mem u slot := by omega
          exact hk_lt.trans (hs.keys_strict hgt hi)
      have hslot_lt1 : slot < m + 1 := by omega
      have hv_c : ValidNode l base t x₁.mem (childAt base t x.mem u slot) :=
        hmem₁ ▸ hv.child_valid hslot_lt1
      have hs_c : SortedNode l base t x₁.mem (childAt base t x.mem u slot) :=
        hmem₁ ▸ hs.child_sorted hslot_lt1
      have hcap_c : readNodeSet l base t x₁.mem (childAt base t x.mem u slot) ⊆
          Finset.range capNodes := by
        rw [hmem₁]
        exact (child_subset_readNodeSet l base t x.mem u slot hslot_lt1).trans hcap
      obtain ⟨y, hy_rec, hmem_y, hb_y, hd_y, hfnd_y, hval_y⟩ :=
        ih hb₁ hv_c hs_c hcap_c hz₁ ho₁ hb₁_reg hd₁ hst₁ hk₁ hbr.1 (hbr.2.1.trans hact)
          (hbr.2.2.1.trans hfound0) (hbr.2.2.2.trans hval0)
      have hlk := lookup_readTree_succ_eq_child hs hslot_le hsc.2.1 hgt_all
      rw [hmem₁] at hfnd_y hval_y
      refine ⟨y, (hstep.loop_iter hcond_in hy_rec).mono (by omega), hmem_y.trans hmem₁,
        hb_y, hd_y, ?_, ?_⟩
      · rwa [hlk]
      · rwa [hlk]

/-- `lookupCode` evaluates `BTree.lookup k tr` in at most `(16 * t + 21) * tr.height + 16`
standard Word-RAM instructions without modifying memory, preserving `Rep`. -/
theorem lookupCode_spec {w base capNodes t k : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x)
    (hkey : x.regs rKey = k) :
    ∃ y, ExecWithin w lookupCode x y ((16 * t + 21) * tr.height + 16) ∧
      Rep base capNodes t w tr y ∧
      y.mem = x.mem ∧
      y.regs rFound = (if (BTree.lookup k tr).isSome then 1 else 0) ∧
      y.regs rVal = (BTree.lookup k tr).getD 0 := by
  have hfit := hr.fits_arena
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  have hf1 : Fits w 1 := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_b1 : Fits w (base + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  rcases hr.tree_spec with ⟨hcnt0, rfl⟩ | ⟨hcnt_pos, l, rfl, hv, hs, hrange⟩
  · -- Empty tree (`cnt = 0`, `tr = .leaf`):
    let y : Data 20 :=
      ((((((x.set rZero 0).set rOne 1).set rFound 0).set rVal 0).set rTmp1
        (base + 1)).set rCnt 0).set rZero 0
    have he : ExecWithin w lookupCode x y 9 := by
      unfold lookupCode
      dsimp only [y]
      wram_exec [hr.base_eq, hcnt0, hf0, hf1, hf_b1]
    have hrep : Rep base capNodes t w .leaf y := by
      refine ⟨he.bounded hr.bounded, hr.two_le, ?_, ?_, hfit, hr.cnt_le_cap, Or.inl ⟨hcnt0, rfl⟩⟩
      · dsimp only [y]; wram_simp; exact hr.base_eq
      · dsimp only [y]; wram_simp; exact hr.deg_eq
    refine ⟨y, he.mono (by omega), hrep, rfl, ?_, ?_⟩
    · simp only [BTree.lookup_leaf, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      dsimp only [y]; wram_simp
    · simp only [BTree.lookup_leaf, Option.getD_none]
      dsimp only [y]; wram_simp
  · -- Non-empty tree (`0 < cnt`, `tr = readTree l base t x.mem (x.mem base)`):
    have hcap1 : 1 ≤ capNodes := by have := hr.cnt_le_cap; omega
    have hst_le := stride_le_arena (base := base) (t := t) hcap1
    have hf_2t : Fits w (t + t) := hfit.of_le (by omega)
    have hf_4t : Fits w ((t + t) + (t + t)) := hfit.of_le (by omega)
    have hf_6t : Fits w (6 * t) := hfit.of_le hst_le
    have h6t : (t + t) + ((t + t) + (t + t)) = 6 * t := by omega
    have hcnt_ne : x.mem (base + 1) ≠ 0 := by omega
    let x₀ : Data 20 :=
      ((((((((((x.set rZero 0).set rOne 1).set rFound 0).set rVal 0).set rTmp1
        (base + 1)).set rCnt (x.mem (base + 1))).set rStride (t + t)).set rTmp1
        ((t + t) + (t + t))).set rStride (6 * t)).set rCur (x.mem base)).set rActive 1
    have hcap_sub : readNodeSet l base t x₀.mem (x.mem base) ⊆ Finset.range capNodes :=
      hrange.trans (Finset.range_mono hr.cnt_le_cap)
    obtain ⟨y, hloop, hmem_y, hb_y, hd_y, hfnd_y, hval_y⟩ :=
      lookupLoop_spec (x := x₀) (k := k) hr.two_le
        (((((((((((hr.bounded.set hf0).set hf1).set hf0).set hf0).set hf_b1).set
          (hr.bounded.2 _)).set hf_2t).set hf_4t).set hf_6t).set (hr.bounded.2 _)).set hf1)
        hfit hv hs hcap_sub rfl rfl
        (by dsimp only [x₀]; wram_simp; exact hr.base_eq)
        (by dsimp only [x₀]; wram_simp; exact hr.deg_eq)
        rfl
        (by dsimp only [x₀]; wram_simp; exact hkey)
        rfl rfl rfl rfl
    have he : ExecWithin w lookupCode x y ((16 * t + 21) * (l + 1) + 16) := by
      unfold lookupCode
      apply WP.execWithin
      wram_exec [hr.base_eq, hr.deg_eq, hcnt_ne, h6t, hf0, hf1, hf_b1, hf_2t, hf_4t, hf_6t]
      exact WP.of_execWithin hloop ⟨by omega, rfl⟩
    have hh_eq : (readTree l base t x.mem (x.mem base)).height = l + 1 :=
      hv.balanced_and_height.2
    have hrep : Rep base capNodes t w (readTree l base t x.mem (x.mem base)) y :=
      ⟨he.bounded hr.bounded, hr.two_le, hb_y, hd_y, hfit,
        by rw [hmem_y]; exact hr.cnt_le_cap,
        by rw [hmem_y]; exact Or.inr ⟨hcnt_pos, l, rfl, hv, hs, hrange⟩⟩
    exact ⟨y, hh_eq ▸ he, hrep, hmem_y, hfnd_y, hval_y⟩

/-- Logarithmic `O(t log_t n)` Word-RAM instruction bound for `lookupCode`. -/
theorem lookupCode_log_spec {w base capNodes t k : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x)
    (hkey : x.regs rKey = k) :
    ∃ y, ExecWithin w lookupCode x y
        ((16 * t + 21) * (Nat.log t ((tr.size + 1) / 2) + 1) + 16) ∧
      Rep base capNodes t w tr y ∧
      y.mem = x.mem ∧
      y.regs rFound = (if (BTree.lookup k tr).isSome then 1 else 0) ∧
      y.regs rVal = (BTree.lookup k tr).getD 0 := by
  obtain ⟨y, he, hrep, hmem, hfnd, hval⟩ := lookupCode_spec hr hkey
  have hle := Nat.mul_le_mul_left (16 * t + 21) hr.height_le_log
  exact ⟨y, he.mono (by omega), hrep, hmem, hfnd, hval⟩

/-- Complete flat Word-RAM lookup program (`lookupCode` followed by `halt rVal`). -/
def lookupProgram : Program .standard 20 := lookupCode.program rVal

/-- `lookupCode` does not read the runtime word width `w`. -/
theorem not_readsWidth_lookupCode : ¬lookupCode.ReadsWidth := by decide

/-- `lookupCode` is deterministic (`rand`-free). -/
theorem isRandFree_lookupCode : lookupCode.IsRandFree := by decide

/-- `lookupProgram` does not read the runtime word width `w`. -/
theorem not_readsWidth_lookupProgram : ¬lookupProgram.ReadsWidth :=
  Code.not_readsWidth_program not_readsWidth_lookupCode rVal

/-- `lookupProgram` is deterministic (`rand`-free). -/
theorem isRandFree_lookupProgram : lookupProgram.IsRandFree :=
  Code.isRandFree_program.mpr isRandFree_lookupCode

/-- Complete halting flat-program specification of `lookupProgram`: runs in at most
`(16 * t + 21) * (Nat.log t ((tr.size + 1) / 2) + 1) + 17` Word-RAM instructions (charging the
final `halt`), halting with `(BTree.lookup k tr).getD 0` in `rVal`, the hit/miss bit in `rFound`
(distinguishing `some 0` from `none`), unchanged memory `y.mem = x.mem`, and preserved `Rep`. -/
theorem lookupProgram_spec {w base capNodes t k : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x)
    (hkey : x.regs rKey = k) :
    ∃ y steps,
      Runs w lookupProgram ⟨0, x⟩ ⟨lookupCode.size, y⟩ steps ∧
      step w lookupProgram ⟨lookupCode.size, y⟩ = .halt ((BTree.lookup k tr).getD 0) ∧
      steps + 1 ≤ (16 * t + 21) * (Nat.log t ((tr.size + 1) / 2) + 1) + 17 ∧
      Rep base capNodes t w tr y ∧
      y.mem = x.mem ∧
      y.regs rFound = (if (BTree.lookup k tr).isSome then 1 else 0) ∧
      y.regs rVal = (BTree.lookup k tr).getD 0 := by
  obtain ⟨y, ⟨steps, hle, hexec⟩, hrep, hmem, hfnd, hval⟩ := lookupCode_log_spec hr hkey
  have hruns : Runs w lookupProgram ⟨0, x⟩ ⟨lookupCode.size, y⟩ steps := by
    simpa only [Nat.zero_add] using
      hexec.runs (pc := 0) (p := lookupProgram) (Program.Contains.self _).append_left
  have hhalt : step w lookupProgram ⟨0 + lookupCode.size, y⟩ = .halt (y.regs rVal) :=
    step_halt (by simp [lookupProgram, Code.program])
  rw [Nat.zero_add, hval] at hhalt
  exact ⟨y, steps, hruns, hhalt, by omega, hrep, hmem, hfnd, hval⟩

/-! ## 7. Split and leaf-insert subprograms (`copyUpperCode`, `splitRootCode`, `splitChildCode`,
`leafInsertCode`) -/

private def copyUpperPre1 : Code .standard 20 := ram[
  rSrc ← rChild * rStride;
  rSrc ← rBase + rSrc;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rDeg;
  rDst ← rCnt * rStride;
  rDst ← rBase + rDst;
  rDst ← rDst + rOne;
  rDst ← rDst + rOne;
  rDst ← rDst + rOne;
  rDst ← rDst + rOne;
  rLim ← rDeg - rOne ]

private def copyUpperPre2 : Code .standard 20 := ram[
  rSrc ← rSrc + rLim;
  rSrc ← rSrc + rDeg;
  rDst ← rDst + rLim;
  rDst ← rDst + rDeg ]

private def copyUpperBranch : Code .standard 20 := ram[
  rTmp1 ← rChild * rStride;
  rTmp1 ← rBase + rTmp1;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp2 ← *rTmp1;
  if rTmp2 = rZero then [
    rSrc ← rSrc + rLim;
    rSrc ← rSrc + rDeg;
    rDst ← rDst + rLim;
    rDst ← rDst + rDeg;
    rLim ← rDeg;
    ⟪copyArrayCode⟫
  ] else [
    rZero ← #0
  ] ]

private def copyUpperPost : Code .standard 20 := ram[
  rSrc ← rChild * rStride;
  rSrc ← rBase + rSrc;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rTmp2 ← *rSrc;
  rDst ← rCnt * rStride;
  rDst ← rBase + rDst;
  rDst ← rDst + rOne;
  rDst ← rDst + rOne;
  *rDst ← rTmp2;
  rLim ← rDeg - rOne;
  rTmp1 ← rDst + rOne;
  *rTmp1 ← rLim;
  rTmp1 ← rSrc + rOne;
  *rTmp1 ← rLim ]

private def copyUpperCode : Code .standard 20 := ram[
  ⟪copyUpperPre1⟫;
  ⟪copyArrayCode⟫;
  ⟪copyUpperPre2⟫;
  ⟪copyArrayCode⟫;
  ⟪copyUpperBranch⟫;
  ⟪copyUpperPost⟫ ]

private theorem copyUpperCode_spec {w base capNodes t c z : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hc_cap : c < capNodes) (hz_cap : z < capNodes) (hcz : c ≠ z)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hz0 : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t)
    (hchild : x.regs rChild = c) (hcnt : x.regs rCnt = z) :
    ∃ y, ExecWithin w copyUpperCode x y (21 * t + 48) ∧
      y.Bounded w ∧
      y.mem = memCopyUpper base t c z x.mem ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rZero = 0 ∧
      ∀ reg : Fin 20,
        reg ≠ rSrc → reg ≠ rDst → reg ≠ rLim → reg ≠ rIdx →
          reg ≠ rTmp1 → reg ≠ rTmp2 → reg ≠ rZero → y.regs reg = x.regs reg := by
  have hac_le := nodeAddr_add_le_arena (base := base) hc_cap (o := 6 * t) le_rfl
  have haz_le := nodeAddr_add_le_arena (base := base) hz_cap (o := 6 * t) le_rfl
  have hsep : nodeAddr base t c + 6 * t ≤ nodeAddr base t z ∨
      nodeAddr base t z + 6 * t ≤ nodeAddr base t c := by
    rcases lt_or_gt_of_ne hcz with hlt | hgt
    · left
      have hmul : (c + 1) * nodeStride t ≤ z * nodeStride t := Nat.mul_le_mul_right _ hlt
      simp only [nodeAddr, nodeStride, Nat.add_mul, Nat.one_mul] at hmul ⊢; omega
    · right
      have hmul : (z + 1) * nodeStride t ≤ c * nodeStride t := Nat.mul_le_mul_right _ hgt
      simp only [nodeAddr, nodeStride, Nat.add_mul, Nat.one_mul] at hmul ⊢; omega
  have hf_cmul : Fits w (c * (6 * t)) := hfit.of_le (by
    simp only [nodeAddr, nodeStride] at hac_le; omega)
  have hf_cb0 : Fits w (base + c * (6 * t)) := hfit.of_le (by
    simp only [nodeAddr, nodeStride] at hac_le; omega)
  have hf_cb1 : Fits w (base + c * (6 * t) + 1) := hfit.of_le (by
    simp only [nodeAddr, nodeStride] at hac_le; omega)
  have hf_ac : Fits w (nodeAddr base t c) := hfit.of_le (by omega)
  have hf_ac1 : Fits w (nodeAddr base t c + 1) := hfit.of_le (by omega)
  have hf_ac2 : Fits w (nodeAddr base t c + 2) := hfit.of_le (by omega)
  have hf_ac2t : Fits w (nodeAddr base t c + 2 + t) := hfit.of_le (by omega)
  have hf_zmul : Fits w (z * (6 * t)) := hfit.of_le (by
    simp only [nodeAddr, nodeStride] at haz_le; omega)
  have hf_zb0 : Fits w (base + z * (6 * t)) := hfit.of_le (by
    simp only [nodeAddr, nodeStride] at haz_le; omega)
  have hf_zb1 : Fits w (base + z * (6 * t) + 1) := hfit.of_le (by
    simp only [nodeAddr, nodeStride] at haz_le; omega)
  have hf_az : Fits w (nodeAddr base t z) := hfit.of_le (by omega)
  have hf_az1 : Fits w (nodeAddr base t z + 1) := hfit.of_le (by omega)
  have hf_az2 : Fits w (nodeAddr base t z + 2) := hfit.of_le (by omega)
  have hf_tm1 : Fits w (t - 1) := hfit.of_le (by omega)
  have hna_c : base + c * (6 * t) + 1 + 1 = nodeAddr base t c := by
    simp only [nodeAddr, nodeStride]; omega
  have hna_z : base + z * (6 * t) + 1 + 1 = nodeAddr base t z := by
    simp only [nodeAddr, nodeStride]; omega
  -- Step 1: `copyUpperPre1` + `copyLoop` (keys)
  let x₁ : Data 20 :=
    (((((((((((((x.set rSrc (c * (6 * t))).set rSrc (base + c * (6 * t))).set rSrc
      (base + c * (6 * t) + 1)).set rSrc (nodeAddr base t c)).set rSrc
      (nodeAddr base t c + 1)).set rSrc (nodeAddr base t c + 2)).set rSrc
      (nodeAddr base t c + 2 + t)).set rDst (z * (6 * t))).set rDst
      (base + z * (6 * t))).set rDst (base + z * (6 * t) + 1)).set rDst
      (nodeAddr base t z)).set rDst (nodeAddr base t z + 1)).set rDst
      (nodeAddr base t z + 2)).set rLim (t - 1)
  have he1 : ExecWithin w copyUpperPre1 x x₁ 14 := by
    unfold copyUpperPre1
    dsimp only [x₁]
    wram_exec [ho, hbase, hdeg, hstride, hchild, hcnt, hna_c, hna_z,
      hf_cmul, hf_cb0, hf_cb1, hf_ac, hf_ac1, hf_ac2, hf_ac2t,
      hf_zmul, hf_zb0, hf_zb1, hf_az, hf_az1, hf_az2, hf_tm1]
  obtain ⟨x₂, hc1, hb₂, hmem₂, hreg₂⟩ :=
    copyArrayCode_spec (srcBase := nodeAddr base t c + 2 + t)
      (dstBase := nodeAddr base t z + 2) (N := t - 1)
      (he1.bounded hbdd) ho rfl rfl rfl
      (hfit.of_le (by omega)) (hfit.of_le (by omega)) (by omega)
  -- Step 2: `copyUpperPre2` + `copyArrayCode` (values)
  have hsrc₂ : x₂.regs rSrc = nodeAddr base t c + 2 + t :=
    hreg₂ rSrc (by decide) (by decide) (by decide)
  have hdst₂ : x₂.regs rDst = nodeAddr base t z + 2 :=
    hreg₂ rDst (by decide) (by decide) (by decide)
  have hlim₂ : x₂.regs rLim = t - 1 :=
    hreg₂ rLim (by decide) (by decide) (by decide)
  have ho₂ : x₂.regs rOne = 1 :=
    (hreg₂ rOne (by decide) (by decide) (by decide)).trans ho
  have hd₂ : x₂.regs rDeg = t :=
    (hreg₂ rDeg (by decide) (by decide) (by decide)).trans hdeg
  have hv_c_eq : nodeAddr base t c + 2 + t + (t - 1) + t =
      nodeAddr base t c + (2 * t + 1) + t := by omega
  have hv_z_eq : nodeAddr base t z + 2 + (t - 1) + t =
      nodeAddr base t z + (2 * t + 1) := by omega
  let x₃ : Data 20 :=
    (((x₂.set rSrc (nodeAddr base t c + 2 + t + (t - 1))).set rSrc
      (nodeAddr base t c + (2 * t + 1) + t)).set rDst
      (nodeAddr base t z + 2 + (t - 1))).set rDst (nodeAddr base t z + (2 * t + 1))
  have he2 : ExecWithin w copyUpperPre2 x₂ x₃ 4 := by
    unfold copyUpperPre2
    dsimp only [x₃]
    have hf_s1 : Fits w (nodeAddr base t c + 2 + t + (t - 1)) := hfit.of_le (by omega)
    have hf_s2 : Fits w (nodeAddr base t c + (2 * t + 1) + t) := hfit.of_le (by omega)
    have hf_d1 : Fits w (nodeAddr base t z + 2 + (t - 1)) := hfit.of_le (by omega)
    have hf_d2 : Fits w (nodeAddr base t z + (2 * t + 1)) := hfit.of_le (by omega)
    wram_exec [hsrc₂, hdst₂, hlim₂, hd₂, hv_c_eq, hv_z_eq, hf_s1, hf_s2, hf_d1, hf_d2]
  obtain ⟨x₄, hc2, hb₄, hmem₄, hreg₄⟩ :=
    copyArrayCode_spec (srcBase := nodeAddr base t c + (2 * t + 1) + t)
      (dstBase := nodeAddr base t z + (2 * t + 1)) (N := t - 1)
      (he2.bounded hb₂) ho₂ rfl rfl hlim₂
      (hfit.of_le (by omega)) (hfit.of_le (by omega)) (by omega)
  -- Helper tracking unaffected registers up to `x₄`:
  have hkeep₄ : ∀ reg : Fin 20, reg ≠ rSrc → reg ≠ rDst → reg ≠ rLim → reg ≠ rIdx →
      reg ≠ rTmp1 → reg ≠ rTmp2 → x₄.regs reg = x.regs reg := fun reg hs1 hd1 hl1 hi1 ht1 ht2 => by
    rw [hreg₄ reg hi1 ht1 ht2]
    dsimp only [x₃]
    simp only [Data.set_regs_of_ne hd1 _, Data.set_regs_of_ne hs1 _]
    rw [hreg₂ reg hi1 ht1 ht2]
    dsimp only [x₁]
    simp only [Data.set_regs_of_ne hl1 _, Data.set_regs_of_ne hd1 _,
      Data.set_regs_of_ne hs1 _]
  have hlf₄ : x₄.mem (nodeAddr base t c) = x.mem (nodeAddr base t c) := by
    rw [hmem₄]; simp only [x₃, Data.set_mem]
    rw [ArrayCopy.copyPrefix_outside (by omega), hmem₂]; simp only [x₁, Data.set_mem]
    exact ArrayCopy.copyPrefix_outside (by omega)
  have hz₄ : x₄.regs rZero = 0 :=
    (hkeep₄ rZero (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hz0
  have ho₄ : x₄.regs rOne = 1 :=
    (hkeep₄ rOne (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ho
  have hb₄_reg : x₄.regs rBase = base :=
    (hkeep₄ rBase (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hbase
  have hd₄ : x₄.regs rDeg = t :=
    (hkeep₄ rDeg (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hdeg
  have hst₄ : x₄.regs rStride = 6 * t :=
    (hkeep₄ rStride (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hstride
  have hch₄ : x₄.regs rChild = c :=
    (hkeep₄ rChild (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hchild
  have hcnt₄ : x₄.regs rCnt = z :=
    (hkeep₄ rCnt (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hcnt
  have hsrc₄ : x₄.regs rSrc = nodeAddr base t c + (2 * t + 1) + t :=
    hreg₄ rSrc (by decide) (by decide) (by decide)
  have hdst₄ : x₄.regs rDst = nodeAddr base t z + (2 * t + 1) :=
    hreg₄ rDst (by decide) (by decide) (by decide)
  have hlim₄ : x₄.regs rLim = t - 1 :=
    (hreg₄ rLim (by decide) (by decide) (by decide)).trans hlim₂
  -- Step 3: `copyUpperBranch` (`m3`)
  have hmem₃_step : ∃ x₅, ExecWithin w copyUpperBranch x₄ x₅ (7 * t + 16) ∧
      x₅.Bounded w ∧
      x₅.mem = (if x.mem (nodeAddr base t c) = 0 then
        ArrayCopy.copyPrefix x₄.mem (nodeAddr base t c + 4 * t + t) (nodeAddr base t z + 4 * t) t
      else x₄.mem) ∧
      x₅.regs rZero = 0 ∧
      ∀ reg : Fin 20, reg ≠ rSrc → reg ≠ rDst → reg ≠ rLim → reg ≠ rIdx →
        reg ≠ rTmp1 → reg ≠ rTmp2 → reg ≠ rZero → x₅.regs reg = x.regs reg := by
    by_cases hlf0 : x.mem (nodeAddr base t c) = 0
    · have hc_c_eq : nodeAddr base t c + (2 * t + 1) + t + (t - 1) + t =
          nodeAddr base t c + 4 * t + t := by omega
      have hc_z_eq : nodeAddr base t z + (2 * t + 1) + (t - 1) + t =
          nodeAddr base t z + 4 * t := by omega
      have hf_s1 : Fits w (nodeAddr base t c + (2 * t + 1) + t + (t - 1)) := hfit.of_le (by omega)
      have hf_s2 : Fits w (nodeAddr base t c + 4 * t + t) := hfit.of_le (by omega)
      have hf_d1 : Fits w (nodeAddr base t z + (2 * t + 1) + (t - 1)) := hfit.of_le (by omega)
      have hf_d2 : Fits w (nodeAddr base t z + 4 * t) := hfit.of_le (by omega)
      have hf_t : Fits w t := hfit.of_le (by omega)
      let x₄' : Data 20 :=
        (((((((((x₄.set rTmp1 (c * (6 * t))).set rTmp1 (base + c * (6 * t))).set rTmp1
          (base + c * (6 * t) + 1)).set rTmp1 (nodeAddr base t c)).set rTmp2 0).set rSrc
          (nodeAddr base t c + (2 * t + 1) + t + (t - 1))).set rSrc
          (nodeAddr base t c + 4 * t + t)).set rDst
          (nodeAddr base t z + (2 * t + 1) + (t - 1))).set rDst
          (nodeAddr base t z + 4 * t)).set rLim t
      obtain ⟨x₅, hc3, hb₅, hmem₅, hreg₅⟩ :=
        copyArrayCode_spec (x := x₄') (srcBase := nodeAddr base t c + 4 * t + t)
          (dstBase := nodeAddr base t z + 4 * t) (N := t)
          ((((((((((hb₄.set hf_cmul).set hf_cb0).set hf_cb1).set hf_ac).set
            (hfit.of_le (Nat.zero_le _))).set hf_s1).set hf_s2).set hf_d1).set hf_d2).set hf_t)
          ho₄ rfl rfl rfl (hfit.of_le (by omega)) (hfit.of_le (by omega)) (by omega)
      have he3 : ExecWithin w copyUpperBranch x₄ x₅ (7 * t + 16) := by
        unfold copyUpperBranch
        apply WP.execWithin
        wram_exec [hz₄, ho₄, hb₄_reg, hd₄, hst₄, hch₄, hsrc₄, hdst₄, hlim₄,
          hna_c, hlf₄, hlf0, hc_c_eq, hc_z_eq,
          hf_cmul, hf_cb0, hf_cb1, hf_ac, hf_s1, hf_s2, hf_d1, hf_d2, hf_t]
        exact WP.of_execWithin hc3 ⟨by omega, rfl⟩
      refine ⟨x₅, he3, hb₅, ?_, ?_, fun reg hs1 hd1 hl1 hi1 ht1 ht2 hzr => ?_⟩
      · simp only [hlf0, ↓reduceIte]; exact hmem₅
      · rw [hreg₅ rZero (by decide) (by decide) (by decide)]; exact hz₄
      · rw [hreg₅ reg hi1 ht1 ht2]
        dsimp only [x₄']
        simp only [Data.set_regs_of_ne hl1 _, Data.set_regs_of_ne hd1 _,
          Data.set_regs_of_ne hs1 _, Data.set_regs_of_ne ht2 _, Data.set_regs_of_ne ht1 _]
        exact hkeep₄ reg hs1 hd1 hl1 hi1 ht1 ht2
    · have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
      let x₅ : Data 20 :=
        (((((x₄.set rTmp1 (c * (6 * t))).set rTmp1 (base + c * (6 * t))).set rTmp1
          (base + c * (6 * t) + 1)).set rTmp1 (nodeAddr base t c)).set rTmp2
          (x.mem (nodeAddr base t c))).set rZero 0
      have he3 : ExecWithin w copyUpperBranch x₄ x₅ (7 * t + 16) := by
        unfold copyUpperBranch
        dsimp only [x₅]
        wram_exec [hz₄, ho₄, hb₄_reg, hst₄, hch₄, hna_c, hlf₄, hlf0,
          hf_cmul, hf_cb0, hf_cb1, hf_ac, hf0]
      refine ⟨x₅, he3, he3.bounded hb₄, ?_, rfl, fun reg hs1 hd1 hl1 hi1 ht1 ht2 hzr => ?_⟩
      · simp only [hlf0, ↓reduceIte]; rfl
      · dsimp only [x₅]
        simp only [Data.set_regs_of_ne hzr _, Data.set_regs_of_ne ht2 _,
          Data.set_regs_of_ne ht1 _]
        exact hkeep₄ reg hs1 hd1 hl1 hi1 ht1 ht2
  obtain ⟨x₅, he3, hb₅, hmem₅, hz₅, hkeep₅⟩ := hmem₃_step
  -- Step 4: `copyUpperPost`
  have hlf₅ : x₅.mem (nodeAddr base t c) = x.mem (nodeAddr base t c) := by
    rw [hmem₅]
    split_ifs
    · rw [ArrayCopy.copyPrefix_outside (by omega)]; exact hlf₄
    · exact hlf₄
  have ho₅ : x₅.regs rOne = 1 :=
    (hkeep₅ rOne (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ho
  have hb₅_reg : x₅.regs rBase = base :=
    (hkeep₅ rBase (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hbase
  have hd₅ : x₅.regs rDeg = t :=
    (hkeep₅ rDeg (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hdeg
  have hst₅ : x₅.regs rStride = 6 * t :=
    (hkeep₅ rStride (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hstride
  have hch₅ : x₅.regs rChild = c :=
    (hkeep₅ rChild (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hchild
  have hcnt₅ : x₅.regs rCnt = z :=
    (hkeep₅ rCnt (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hcnt
  let y : Data 20 :=
    ((((((((((((((x₅.set rSrc (c * (6 * t))).set rSrc (base + c * (6 * t))).set rSrc
      (base + c * (6 * t) + 1)).set rSrc (nodeAddr base t c)).set rTmp2
      (x.mem (nodeAddr base t c))).set rDst (z * (6 * t))).set rDst
      (base + z * (6 * t))).set rDst (base + z * (6 * t) + 1)).set rDst
      (nodeAddr base t z)).write (nodeAddr base t z) (x.mem (nodeAddr base t c))).set rLim
      (t - 1)).set rTmp1 (nodeAddr base t z + 1)).write (nodeAddr base t z + 1) (t - 1)).set rTmp1
      (nodeAddr base t c + 1)).write (nodeAddr base t c + 1) (t - 1)
  have he4 : ExecWithin w copyUpperPost x₅ y 15 := by
    unfold copyUpperPost
    dsimp only [y]
    wram_exec [ho₅, hb₅_reg, hd₅, hst₅, hch₅, hcnt₅, hna_c, hna_z, hlf₅,
      hf_cmul, hf_cb0, hf_cb1, hf_ac, hf_ac1, hf_zmul, hf_zb0, hf_zb1, hf_az, hf_az1, hf_tm1]
  have hfull : ExecWithin w copyUpperCode x y (21 * t + 48) :=
    (he1.seq (hc1.seq (he2.seq (hc2.seq (he3.seq he4))))).mono (by omega)
  have hymem : y.mem = memCopyUpper base t c z x.mem := by
    simp only [x₁, Data.set_mem] at hmem₂
    simp only [x₃, Data.set_mem] at hmem₄
    dsimp only [y, memCopyUpper]
    wram_simp
    simp only [hmem₅, hmem₄, hmem₂]
  have hmod : Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
    intro addr hnot
    rw [hymem]
    apply memCopyUpper_outside ht
    · by_contra hc_in
      apply hnot
      simp only [Block.mem_footprint, Block.Owns, nodeStride] at hc_in ⊢
      have := base_lt_nodeAddr base t c 0
      omega
    · by_contra hz_in
      apply hnot
      simp only [Block.mem_footprint, Block.Owns, nodeStride] at hz_in ⊢
      have := base_lt_nodeAddr base t z 0
      omega
  refine ⟨y, hfull, hfull.bounded hbdd, hymem, hmod, ?_, fun reg hs1 hd1 hl1 hi1 ht1 ht2 hzr => ?_⟩
  · dsimp only [y]; wram_simp; exact hz₅
  · dsimp only [y]
    simp only [Data.write_regs, Data.set_regs_of_ne ht1 _, Data.set_regs_of_ne hl1 _,
      Data.set_regs_of_ne hd1 _, Data.set_regs_of_ne ht2 _, Data.set_regs_of_ne hs1 _]
    exact hkeep₅ reg hs1 hd1 hl1 hi1 ht1 ht2 hzr

private theorem memCopyUpper_at_c {base t c cnt : ℕ}
    (hsep : nodeAddr base t c + 6 * t ≤ nodeAddr base t cnt)
    (o : ℕ) (ho_lo : 2 ≤ o) (ho_hi : o < 6 * t) (mem : ℕ → ℕ) :
    memCopyUpper base t c cnt mem (nodeAddr base t c + o) = mem (nodeAddr base t c + o) := by
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t c = ac := ⟨_, rfl⟩
  obtain ⟨az, haz_def⟩ : ∃ az, nodeAddr base t cnt = az := ⟨_, rfl⟩
  rw [hac_def, haz_def] at hsep
  dsimp only [memCopyUpper]
  simp only [hac_def, haz_def]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega)]
  split_ifs
  · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega),
      ArrayCopy.copyPrefix_outside (by omega)]
  · rw [ArrayCopy.copyPrefix_outside (by omega), ArrayCopy.copyPrefix_outside (by omega)]

private def splitRootPost : Code .standard 20 := ram[
  rCur ← rCnt + rOne;
  rDst ← rCur * rStride;
  rDst ← rBase + rDst;
  rDst ← rDst + rOne;
  rDst ← rDst + rOne;
  *rDst ← rZero;
  rTmp1 ← rDst + rOne;
  *rTmp1 ← rOne;
  rSrc ← rChild * rStride;
  rSrc ← rBase + rSrc;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rLim ← rDeg - rOne;
  rTmp1 ← rSrc + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rLim;
  rTmp2 ← *rTmp1;
  rTmp1 ← rDst + rOne;
  rTmp1 ← rTmp1 + rOne;
  *rTmp1 ← rTmp2;
  rTmp1 ← rSrc + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rLim;
  rTmp2 ← *rTmp1;
  rTmp1 ← rDst + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rOne;
  *rTmp1 ← rTmp2;
  rTmp1 ← rDst + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  *rTmp1 ← rChild;
  rTmp1 ← rTmp1 + rOne;
  *rTmp1 ← rCnt;
  *rBase ← rCur;
  rCnt ← rCur + rOne;
  rTmp1 ← rBase + rOne;
  *rTmp1 ← rCnt ]

private def splitRootCode : Code .standard 20 := ram[
  ⟪copyUpperCode⟫;
  ⟪splitRootPost⟫ ]

private theorem splitRootCode_spec {w base capNodes t oldRoot cnt : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hr_lt : oldRoot < cnt) (hcap : cnt + 2 ≤ capNodes)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hz0 : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t)
    (hchild : x.regs rChild = oldRoot) (hcnt : x.regs rCnt = cnt) :
    ∃ y, ExecWithin w splitRootCode x y (21 * t + 88) ∧
      y.Bounded w ∧
      y.mem = memSplitRoot base t oldRoot cnt x.mem ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
      y.regs rKey = x.regs rKey ∧ y.regs rVal = x.regs rVal ∧
      y.regs rCur = cnt + 1 ∧ y.regs rCnt = cnt + 2 := by
  obtain ⟨x₁, he1, hb₁, hmem₁, hmod₁, hz₁, hkeep₁⟩ :=
    copyUpperCode_spec ht (by omega) (by omega) (by omega) hbdd hfit hz0 ho hbase hdeg hstride
      hchild hcnt
  have ho₁ : x₁.regs rOne = 1 :=
    (hkeep₁ rOne (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans ho
  have hb₁_reg : x₁.regs rBase = base :=
    (hkeep₁ rBase (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hbase
  have hd₁ : x₁.regs rDeg = t :=
    (hkeep₁ rDeg (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hdeg
  have hst₁ : x₁.regs rStride = 6 * t :=
    (hkeep₁ rStride (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hstride
  have hch₁ : x₁.regs rChild = oldRoot :=
    (hkeep₁ rChild (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hchild
  have hcnt₁ : x₁.regs rCnt = cnt :=
    (hkeep₁ rCnt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans hcnt
  have hk₁ : x₁.regs rKey = x.regs rKey :=
    hkeep₁ rKey (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hv₁ : x₁.regs rVal = x.regs rVal :=
    hkeep₁ rVal (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- Median key/val of `oldRoot` are untouched by `memCopyUpper` (`oldRoot ≠ cnt`):
  have hsep_rc : nodeAddr base t oldRoot + 6 * t ≤ nodeAddr base t cnt := by
    have hmul : (oldRoot + 1) * nodeStride t ≤ cnt * nodeStride t := Nat.mul_le_mul_right _ hr_lt
    simp only [nodeAddr, nodeStride, Nat.add_mul, Nat.one_mul] at hmul ⊢; omega
  have hsep_rn : nodeAddr base t oldRoot + 6 * t ≤ nodeAddr base t (cnt + 1) := by
    have hmul : (oldRoot + 1) * nodeStride t ≤ (cnt + 1) * nodeStride t :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [nodeAddr, nodeStride, Nat.add_mul, Nat.one_mul] at hmul ⊢; omega
  have hk_med_m1 : x₁.mem (nodeAddr base t oldRoot + 2 + (t - 1)) =
      keyAt base t x.mem oldRoot (t - 1) := by
    dsimp only [keyAt]; rw [hmem₁]; simp only [Nat.add_assoc]
    exact memCopyUpper_at_c hsep_rc (2 + (t - 1)) (by omega) (by omega) x.mem
  have hv_med_m1 : x₁.mem (nodeAddr base t oldRoot + (2 * t + 1) + (t - 1)) =
      valAt base t x.mem oldRoot (t - 1) := by
    dsimp only [valAt]; rw [hmem₁]; simp only [Nat.add_assoc]
    exact memCopyUpper_at_c hsep_rc (2 * t + (1 + (t - 1))) (by omega) (by omega) x.mem
  obtain ⟨ar, har_def⟩ : ∃ ar, nodeAddr base t (cnt + 1) = ar := ⟨_, rfl⟩
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t oldRoot = ac := ⟨_, rfl⟩
  have har_le : ar + 6 * t ≤ base + arenaWords t capNodes :=
    har_def ▸ nodeAddr_add_le_arena (base := base) (u := cnt + 1)
      (by omega : cnt + 1 < capNodes) (o := 6 * t) le_rfl
  have hac_le : ac + 6 * t ≤ base + arenaWords t capNodes :=
    hac_def ▸ nodeAddr_add_le_arena (base := base) (u := oldRoot)
      (by omega : oldRoot < capNodes) (o := 6 * t) le_rfl
  rw [hac_def] at hk_med_m1 hv_med_m1 hsep_rc
  rw [hac_def, har_def] at hsep_rn
  have hna_r : base + (cnt + 1) * (6 * t) + 1 + 1 = ar := by
    rw [← har_def]; simp only [nodeAddr, nodeStride]; omega
  have hna_c : base + oldRoot * (6 * t) + 1 + 1 = ac := by
    rw [← hac_def]; simp only [nodeAddr, nodeStride]; omega
  have h2t_c : ac + t + t + 1 = ac + (2 * t + 1) := by omega
  have h2t_r : ar + t + t + 1 = ar + (2 * t + 1) := by omega
  have h4t_r : ar + t + t + t + t = ar + 4 * t := by omega
  have hcap_le : capNodes ≤ capNodes * nodeStride t :=
    Nat.le_mul_of_pos_right _ (by simp only [nodeStride]; omega)
  -- Fit facts:
  have hf_c1 : Fits w (cnt + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_c2 : Fits w (cnt + 1 + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_b1 : Fits w (base + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_tm1 : Fits w (t - 1) := hfit.of_le (by omega)
  have hf_rmul : Fits w ((cnt + 1) * (6 * t)) := hfit.of_le (by omega)
  have hf_rb0 : Fits w (base + (cnt + 1) * (6 * t)) := hfit.of_le (by omega)
  have hf_rb1 : Fits w (base + (cnt + 1) * (6 * t) + 1) := hfit.of_le (by omega)
  have hf_rb2 : Fits w (base + (cnt + 1) * (6 * t) + 1 + 1) := hfit.of_le (by omega)
  have hf_ar : Fits w ar := hfit.of_le (by omega)
  have hf_ar1 : Fits w (ar + 1) := hfit.of_le (by omega)
  have hf_ar2 : Fits w (ar + 1 + 1) := hfit.of_le (by omega)
  have hf_ar2' : Fits w (ar + 2) := hfit.of_le (by omega)
  have hf_art1 : Fits w (ar + t) := hfit.of_le (by omega)
  have hf_art2 : Fits w (ar + t + t) := hfit.of_le (by omega)
  have hf_art21 : Fits w (ar + t + t + 1) := hfit.of_le (by omega)
  have hf_ar2t1 : Fits w (ar + (2 * t + 1)) := hfit.of_le (by omega)
  have hf_art3 : Fits w (ar + t + t + t) := hfit.of_le (by omega)
  have hf_art4 : Fits w (ar + t + t + t + t) := hfit.of_le (by omega)
  have hf_ar4t : Fits w (ar + 4 * t) := hfit.of_le (by omega)
  have hf_ar4t1 : Fits w (ar + 4 * t + 1) := hfit.of_le (by omega)
  have hf_cmul : Fits w (oldRoot * (6 * t)) := hfit.of_le (by omega)
  have hf_cb0 : Fits w (base + oldRoot * (6 * t)) := hfit.of_le (by omega)
  have hf_cb1 : Fits w (base + oldRoot * (6 * t) + 1) := hfit.of_le (by omega)
  have hf_cb2 : Fits w (base + oldRoot * (6 * t) + 1 + 1) := hfit.of_le (by omega)
  have hf_ac : Fits w ac := hfit.of_le (by omega)
  have hf_ac1 : Fits w (ac + 1) := hfit.of_le (by omega)
  have hf_ac2 : Fits w (ac + 1 + 1) := hfit.of_le (by omega)
  have hf_ack : Fits w (ac + 1 + 1 + (t - 1)) := hfit.of_le (by omega)
  have hf_ack' : Fits w (ac + 2 + (t - 1)) := hfit.of_le (by omega)
  have hf_act1 : Fits w (ac + t) := hfit.of_le (by omega)
  have hf_act2 : Fits w (ac + t + t) := hfit.of_le (by omega)
  have hf_act21 : Fits w (ac + t + t + 1) := hfit.of_le (by omega)
  have hf_ac2t1 : Fits w (ac + (2 * t + 1)) := hfit.of_le (by omega)
  have hf_acv : Fits w (ac + (2 * t + 1) + (t - 1)) := hfit.of_le (by omega)
  have hack_eq : ac + 1 + 1 + (t - 1) = ac + 2 + (t - 1) := by omega
  have har2_eq : ar + 1 + 1 = ar + 2 := by omega
  have hc2_eq : cnt + 1 + 1 = cnt + 2 := by omega
  have hk_ne1 : ac + 2 + (t - 1) ≠ ar := by omega
  have hk_ne2 : ac + 2 + (t - 1) ≠ ar + 1 := by omega
  have hv_ne1 : ac + (2 * t + 1) + (t - 1) ≠ ar := by omega
  have hv_ne2 : ac + (2 * t + 1) + (t - 1) ≠ ar + 1 := by omega
  have hv_ne3 : ac + (2 * t + 1) + (t - 1) ≠ ar + 2 := by omega
  obtain ⟨y, he2, hymem, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hv_y, hcur_y, hcnt_y⟩ :
      ∃ y, ExecWithin w splitRootPost x₁ y 40 ∧
        y.mem = memSplitRoot base t oldRoot cnt x.mem ∧
        y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
        y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
        y.regs rKey = x.regs rKey ∧ y.regs rVal = x.regs rVal ∧
        y.regs rCur = cnt + 1 ∧ y.regs rCnt = cnt + 2 := by
    unfold splitRootPost
    apply WP.exists_execWithin
    wram_exec [hz₁, ho₁, hb₁_reg, hd₁, hst₁, hch₁, hcnt₁,
      hna_r, hna_c, h2t_c, h2t_r, h4t_r, hack_eq, har2_eq, hc2_eq,
      hk_ne1, hk_ne2, hv_ne1, hv_ne2, hv_ne3, hk_med_m1, hv_med_m1,
      hf_c1, hf_c2, hf_b1, hf_tm1, hf_rmul, hf_rb0, hf_rb1, hf_rb2,
      hf_ar, hf_ar1, hf_ar2, hf_ar2', hf_art1, hf_art2, hf_art21, hf_ar2t1, hf_art3, hf_art4,
      hf_ar4t, hf_ar4t1,
      hf_cmul, hf_cb0, hf_cb1, hf_cb2, hf_ac, hf_ac1, hf_ac2, hf_ack, hf_ack',
      hf_act1, hf_act2, hf_act21, hf_ac2t1, hf_acv]
    wram_simp [hz₁, ho₁, hb₁_reg, hd₁, hst₁, hk₁, hv₁]
    simp only [memSplitRoot, har_def, ← hmem₁]
  have hmod₂ : Modifies (Block.mk base (arenaWords t capNodes)).footprint x₁.mem y.mem := by
    intro addr hnot
    rw [hymem]
    dsimp only [memSplitRoot]
    have hb_lo : base + 1 < ar := har_def ▸ base_lt_nodeAddr base t (cnt + 1) 0
    rw [har_def]
    repeat rw [Function.update_of_ne (by
      intro heq; apply hnot
      simp only [Block.mem_footprint, Block.Owns] at heq har_le ⊢
      omega)]
    rw [← hmem₁]
  have hfull : ExecWithin w splitRootCode x y (21 * t + 88) :=
    (he1.seq he2).mono (by omega)
  exact ⟨y, hfull, hfull.bounded hbdd, hymem,
    by simpa only [Finset.union_idempotent] using hmod₁.trans hmod₂,
    hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hv_y, hcur_y, hcnt_y⟩

private def splitChildPre1 : Code .standard 20 := ram[
  rSrc ← rCur * rStride;
  rSrc ← rBase + rSrc;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rDst ← rNumK;
  rLim ← rNumK - rSlot ]

private def splitChildPre2 : Code .standard 20 := ram[
  rSrc ← rSrc + rDeg;
  rSrc ← rSrc + rDeg;
  rSrc ← rSrc - rOne ]

private def splitChildPre3 : Code .standard 20 := ram[
  rSrc ← rSrc + rDeg;
  rSrc ← rSrc + rDeg;
  rSrc ← rSrc - rOne;
  rDst ← rNumK + rOne ]

private def splitChildPost : Code .standard 20 := ram[
  rSrc ← rChild * rStride;
  rSrc ← rBase + rSrc;
  rSrc ← rSrc + rOne;
  rSrc ← rSrc + rOne;
  rDst ← rCur * rStride;
  rDst ← rBase + rDst;
  rDst ← rDst + rOne;
  rDst ← rDst + rOne;
  rLim ← rDeg - rOne;
  rTmp1 ← rSrc + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rLim;
  rTmp2 ← *rTmp1;
  rTmp1 ← rDst + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rSlot;
  *rTmp1 ← rTmp2;
  rTmp1 ← rSrc + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rLim;
  rTmp2 ← *rTmp1;
  rTmp1 ← rDst + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rSlot;
  *rTmp1 ← rTmp2;
  rTmp1 ← rDst + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rSlot;
  rTmp1 ← rTmp1 + rOne;
  *rTmp1 ← rCnt;
  rNumK ← rNumK + rOne;
  rTmp1 ← rDst + rOne;
  *rTmp1 ← rNumK;
  rCnt ← rCnt + rOne;
  rTmp1 ← rBase + rOne;
  *rTmp1 ← rCnt ]

private def splitChildShifts : Code .standard 20 := ram[
  ⟪splitChildPre1⟫;
  ⟪shiftLoop⟫;
  ⟪splitChildPre2⟫;
  ⟪shiftLoop⟫;
  ⟪splitChildPre3⟫;
  ⟪shiftLoop⟫ ]

private def splitChildCode : Code .standard 20 := ram[
  ⟪copyUpperCode⟫;
  ⟪splitChildShifts⟫;
  ⟪splitChildPost⟫ ]

private theorem splitChildPost_spec {w base capNodes t u m slot c cnt : ℕ}
    {mem₀ : ℕ → ℕ} {x₇ : Data 20}
    (ht : 2 ≤ t) (hu_lt : u < cnt) (hc_lt : c < cnt) (hcap : cnt + 1 ≤ capNodes)
    (hm_le : m ≤ 2 * t - 2) (hslot : slot ≤ m)
    (hfit : Fits w (base + arenaWords t capNodes))
    (hz₇ : x₇.regs rZero = 0) (ho₇ : x₇.regs rOne = 1)
    (hb₇_reg : x₇.regs rBase = base) (hd₇ : x₇.regs rDeg = t)
    (hst₇ : x₇.regs rStride = 6 * t)
    (hcur₇ : x₇.regs rCur = u) (hnk₇ : x₇.regs rNumK = m)
    (hsl₇ : x₇.regs rSlot = slot) (hch₇ : x₇.regs rChild = c) (hcnt₇ : x₇.regs rCnt = cnt)
    (hk_med : x₇.mem (nodeAddr base t c + 2 + (t - 1)) = keyAt base t mem₀ c (t - 1))
    (hv_med : x₇.mem (nodeAddr base t c + (2 * t + 1) + (t - 1)) = valAt base t mem₀ c (t - 1))
    (hsep_uc : nodeAddr base t u + 6 * t ≤ nodeAddr base t c ∨
      nodeAddr base t c + 6 * t ≤ nodeAddr base t u)
    (hmem₇_eq : x₇.mem =
      let au := nodeAddr base t u
      let m1 := memCopyUpper base t c cnt mem₀
      let m2 := shiftArrRight (au + 2) m (m - slot) m1
      let m3 := shiftArrRight (au + (2 * t + 1)) m (m - slot) m2
      shiftArrRight (au + 4 * t) (m + 1) (m - slot) m3) :
    ∃ y, ExecWithin w splitChildPost x₇ y 40 ∧
      y.mem = memSplitChild base t u m slot c cnt mem₀ ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
      y.regs rKey = x₇.regs rKey ∧ y.regs rVal = x₇.regs rVal ∧
      y.regs rActive = x₇.regs rActive ∧
      y.regs rCur = u ∧ y.regs rSlot = slot ∧ y.regs rChild = c ∧
      y.regs rNumK = m + 1 ∧ y.regs rCnt = cnt + 1 := by
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t c = ac := ⟨_, rfl⟩
  have hau_le : au + 6 * t ≤ base + arenaWords t capNodes :=
    hau_def ▸ nodeAddr_add_le_arena (base := base) (u := u) (by omega : u < capNodes)
      (o := 6 * t) le_rfl
  have hac_le : ac + 6 * t ≤ base + arenaWords t capNodes :=
    hac_def ▸ nodeAddr_add_le_arena (base := base) (u := c) (by omega : c < capNodes)
      (o := 6 * t) le_rfl
  rw [hau_def, hac_def] at hsep_uc
  rw [hac_def] at hk_med hv_med
  have hna_u : base + u * (6 * t) + 1 + 1 = au := by
    rw [← hau_def]; simp only [nodeAddr, nodeStride]; omega
  have hna_c : base + c * (6 * t) + 1 + 1 = ac := by
    rw [← hac_def]; simp only [nodeAddr, nodeStride]; omega
  have hcap_le : capNodes ≤ capNodes * nodeStride t :=
    Nat.le_mul_of_pos_right _ (by simp only [nodeStride]; omega)
  have hf_umul : Fits w (u * (6 * t)) := hfit.of_le (by omega)
  have hf_ub0 : Fits w (base + u * (6 * t)) := hfit.of_le (by omega)
  have hf_ub1 : Fits w (base + u * (6 * t) + 1) := hfit.of_le (by omega)
  have hf_ub2 : Fits w (base + u * (6 * t) + 1 + 1) := hfit.of_le (by omega)
  have hf_au : Fits w au := hfit.of_le (by omega)
  have hf_au1 : Fits w (au + 1) := hfit.of_le (by omega)
  have hf_au2 : Fits w (au + 2) := hfit.of_le (by omega)
  have hf_au2' : Fits w (au + 1 + 1) := hfit.of_le (by omega)
  have hf_auks : Fits w (au + 2 + slot) := hfit.of_le (by omega)
  have hf_aut1 : Fits w (au + t) := hfit.of_le (by omega)
  have hf_aut2 : Fits w (au + t + t) := hfit.of_le (by omega)
  have hf_aut21 : Fits w (au + t + t + 1) := hfit.of_le (by omega)
  have hf_au2t1 : Fits w (au + (2 * t + 1)) := hfit.of_le (by omega)
  have hf_auvs : Fits w (au + (2 * t + 1) + slot) := hfit.of_le (by omega)
  have hf_aut3 : Fits w (au + t + t + t) := hfit.of_le (by omega)
  have hf_aut4 : Fits w (au + t + t + t + t) := hfit.of_le (by omega)
  have hf_au4t : Fits w (au + 4 * t) := hfit.of_le (by omega)
  have hf_aucs : Fits w (au + 4 * t + slot) := hfit.of_le (by omega)
  have hf_aucs10 : Fits w (au + 4 * t + slot + 1) := hfit.of_le (by omega)
  have hf_aucs1 : Fits w (au + 4 * t + (slot + 1)) := hfit.of_le (by omega)
  have hf_cmul : Fits w (c * (6 * t)) := hfit.of_le (by omega)
  have hf_cb0 : Fits w (base + c * (6 * t)) := hfit.of_le (by omega)
  have hf_cb1 : Fits w (base + c * (6 * t) + 1) := hfit.of_le (by omega)
  have hf_cb2 : Fits w (base + c * (6 * t) + 1 + 1) := hfit.of_le (by omega)
  have hf_ac : Fits w ac := hfit.of_le (by omega)
  have hf_ac1 : Fits w (ac + 1) := hfit.of_le (by omega)
  have hf_ac2 : Fits w (ac + 1 + 1) := hfit.of_le (by omega)
  have hf_ack0 : Fits w (ac + 1 + 1 + (t - 1)) := hfit.of_le (by omega)
  have hf_ack : Fits w (ac + 2 + (t - 1)) := hfit.of_le (by omega)
  have hf_act1 : Fits w (ac + t) := hfit.of_le (by omega)
  have hf_act2 : Fits w (ac + t + t) := hfit.of_le (by omega)
  have hf_act21 : Fits w (ac + t + t + 1) := hfit.of_le (by omega)
  have hf_ac2t1 : Fits w (ac + (2 * t + 1)) := hfit.of_le (by omega)
  have hf_acv : Fits w (ac + (2 * t + 1) + (t - 1)) := hfit.of_le (by omega)
  have hf_tm1 : Fits w (t - 1) := hfit.of_le (by omega)
  have hf_m1 : Fits w (m + 1) := hfit.of_le (by omega)
  have hf_cnt1 : Fits w (cnt + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_b1 : Fits w (base + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  have hack_eq : ac + 1 + 1 + (t - 1) = ac + 2 + (t - 1) := by omega
  have hau2_eq : au + 1 + 1 = au + 2 := by omega
  have h2tc_eq : ac + t + t + 1 = ac + (2 * t + 1) := by omega
  have h2tu_eq : au + t + t + 1 = au + (2 * t + 1) := by omega
  have h4tu_eq : au + t + t + t + t = au + 4 * t := by omega
  have hcs1_eq : au + 4 * t + slot + 1 = au + 4 * t + (slot + 1) := by omega
  have hv_ne_ks : ac + (2 * t + 1) + (t - 1) ≠ au + 2 + slot := by omega
  unfold splitChildPost
  apply WP.exists_execWithin
  wram_exec [ho₇, hb₇_reg, hd₇, hst₇, hcur₇, hnk₇, hsl₇, hch₇, hcnt₇,
    hna_c, hna_u, hack_eq, hau2_eq, h2tc_eq, h2tu_eq, h4tu_eq, hcs1_eq,
    hv_ne_ks, hk_med, hv_med,
    hf_cmul, hf_cb0, hf_cb1, hf_cb2, hf_ac, hf_ac1, hf_ac2, hf_ack0, hf_ack,
    hf_act1, hf_act2, hf_act21, hf_ac2t1, hf_acv,
    hf_umul, hf_ub0, hf_ub1, hf_ub2, hf_au, hf_au1, hf_au2, hf_au2', hf_auks,
    hf_aut1, hf_aut2, hf_aut21, hf_au2t1, hf_auvs, hf_aut3, hf_aut4, hf_au4t,
    hf_aucs, hf_aucs10, hf_aucs1, hf_tm1, hf_m1, hf_cnt1, hf_b1]
  wram_simp [hz₇, ho₇, hb₇_reg, hd₇, hst₇, hcur₇, hsl₇, hch₇]
  simp only [memSplitChild, hau_def, hmem₇_eq]

private theorem splitChildShifts_spec {w base capNodes t u m slot : ℕ} {x₁ : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hm_le : m ≤ 2 * t - 2) (hslot : slot ≤ m)
    (hb₁ : x₁.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (ho₁ : x₁.regs rOne = 1) (hb₁_reg : x₁.regs rBase = base) (hd₁ : x₁.regs rDeg = t)
    (hst₁ : x₁.regs rStride = 6 * t) (hcur₁ : x₁.regs rCur = u)
    (hnk₁ : x₁.regs rNumK = m) (hsl₁ : x₁.regs rSlot = slot) :
    ∃ x₇, ExecWithin w splitChildShifts x₁ x₇ (54 * t + 24) ∧
      x₇.Bounded w ∧
      x₇.mem =
        (let au := nodeAddr base t u
         let m2 := shiftArrRight (au + 2) m (m - slot) x₁.mem
         let m3 := shiftArrRight (au + (2 * t + 1)) m (m - slot) m2
         shiftArrRight (au + 4 * t) (m + 1) (m - slot) m3) ∧
      ∀ reg : Fin 20, reg ≠ rSrc → reg ≠ rDst → reg ≠ rLim → reg ≠ rIdx →
        reg ≠ rTmp1 → reg ≠ rTmp2 → x₇.regs reg = x₁.regs reg := by
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  have hau_le : au + 6 * t ≤ base + arenaWords t capNodes :=
    hau_def ▸ nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
  have hna_u : base + u * (6 * t) + 1 + 1 = au := by
    rw [← hau_def]; simp only [nodeAddr, nodeStride]; omega
  have hf_umul : Fits w (u * (6 * t)) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_ub0 : Fits w (base + u * (6 * t)) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_ub1 : Fits w (base + u * (6 * t) + 1) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_au : Fits w au := hfit.of_le (by omega)
  have hf_au1 : Fits w (au + 1) := hfit.of_le (by omega)
  have hf_au2 : Fits w (au + 2) := hfit.of_le (by omega)
  have hf_ms : Fits w (m - slot) := hfit.of_le (by omega)
  let x₂ : Data 20 :=
    (((((((x₁.set rSrc (u * (6 * t))).set rSrc (base + u * (6 * t))).set rSrc
      (base + u * (6 * t) + 1)).set rSrc au).set rSrc (au + 1)).set rSrc
      (au + 2)).set rDst m).set rLim (m - slot)
  have hp1 : ExecWithin w splitChildPre1 x₁ x₂ 8 := by
    unfold splitChildPre1; dsimp only [x₂]
    wram_exec [ho₁, hb₁_reg, hst₁, hcur₁, hnk₁, hsl₁, hna_u,
      hf_umul, hf_ub0, hf_ub1, hf_au, hf_au1, hf_au2, hf_ms]
  obtain ⟨x₃, hs1, hb₃, hmem₃, hreg₃⟩ :=
    shiftLoop_spec (arrBase := au + 2) (upper := m) (count := m - slot)
      (hp1.bounded hb₁) ho₁ rfl rfl rfl (by omega) (hfit.of_le (by omega))
  have hsrc₃ : x₃.regs rSrc = au + 2 := hreg₃ rSrc (by decide) (by decide) (by decide)
  have hdst₃ : x₃.regs rDst = m := hreg₃ rDst (by decide) (by decide) (by decide)
  have hlim₃ : x₃.regs rLim = m - slot := hreg₃ rLim (by decide) (by decide) (by decide)
  have ho₃ : x₃.regs rOne = 1 := (hreg₃ rOne (by decide) (by decide) (by decide)).trans ho₁
  have hd₃ : x₃.regs rDeg = t := (hreg₃ rDeg (by decide) (by decide) (by decide)).trans hd₁
  have hav_eq : au + 2 + t + t - 1 = au + (2 * t + 1) := by omega
  let x₄ : Data 20 :=
    ((x₃.set rSrc (au + 2 + t)).set rSrc (au + 2 + t + t)).set rSrc (au + (2 * t + 1))
  have hp2 : ExecWithin w splitChildPre2 x₃ x₄ 3 := by
    unfold splitChildPre2; dsimp only [x₄]
    have hf1 : Fits w (au + 2 + t) := hfit.of_le (by omega)
    have hf2 : Fits w (au + 2 + t + t) := hfit.of_le (by omega)
    have hf3 : Fits w (au + (2 * t + 1)) := hfit.of_le (by omega)
    wram_exec [ho₃, hd₃, hsrc₃, hav_eq, hf1, hf2, hf3]
  obtain ⟨x₅, hs2, hb₅, hmem₅, hreg₅⟩ :=
    shiftLoop_spec (arrBase := au + (2 * t + 1)) (upper := m) (count := m - slot)
      (hp2.bounded hb₃) ho₃ rfl hdst₃ hlim₃ (by omega) (hfit.of_le (by omega))
  have hsrc₅ : x₅.regs rSrc = au + (2 * t + 1) := hreg₅ rSrc (by decide) (by decide) (by decide)
  have hlim₅ : x₅.regs rLim = m - slot :=
    (hreg₅ rLim (by decide) (by decide) (by decide)).trans hlim₃
  have ho₅ : x₅.regs rOne = 1 := (hreg₅ rOne (by decide) (by decide) (by decide)).trans ho₃
  have hd₅ : x₅.regs rDeg = t := (hreg₅ rDeg (by decide) (by decide) (by decide)).trans hd₃
  have hnk₅ : x₅.regs rNumK = m :=
    (hreg₅ rNumK (by decide) (by decide) (by decide)).trans
      ((hreg₃ rNumK (by decide) (by decide) (by decide)).trans hnk₁)
  have hac4_eq : au + (2 * t + 1) + t + t - 1 = au + 4 * t := by omega
  let x₆ : Data 20 :=
    (((x₅.set rSrc (au + (2 * t + 1) + t)).set rSrc (au + (2 * t + 1) + t + t)).set rSrc
      (au + 4 * t)).set rDst (m + 1)
  have hp3 : ExecWithin w splitChildPre3 x₅ x₆ 4 := by
    unfold splitChildPre3; dsimp only [x₆]
    have hf1 : Fits w (au + (2 * t + 1) + t) := hfit.of_le (by omega)
    have hf2 : Fits w (au + (2 * t + 1) + t + t) := hfit.of_le (by omega)
    have hf3 : Fits w (au + 4 * t) := hfit.of_le (by omega)
    have hf4 : Fits w (m + 1) := hfit.of_le (by omega)
    wram_exec [ho₅, hd₅, hsrc₅, hnk₅, hac4_eq, hf1, hf2, hf3, hf4]
  obtain ⟨x₇, hs3, hb₇, hmem₇, hreg₇⟩ :=
    shiftLoop_spec (arrBase := au + 4 * t) (upper := m + 1) (count := m - slot)
      (hp3.bounded hb₅) ho₅ rfl rfl hlim₅ (by omega) (hfit.of_le (by omega))
  simp only [x₂, Data.set_mem] at hmem₃
  simp only [x₄, Data.set_mem] at hmem₅
  simp only [x₆, Data.set_mem] at hmem₇
  have he : ExecWithin w splitChildShifts x₁ x₇ (54 * t + 24) :=
    (hp1.seq (hs1.seq (hp2.seq (hs2.seq (hp3.seq hs3))))).mono (by omega)
  refine ⟨x₇, he, hb₇, by simp only [hau_def, ← hmem₃, ← hmem₅, ← hmem₇], ?_⟩
  intro reg h1 h2 h3 h4 h5 h6
  rw [hreg₇ reg h4 h5 h6]
  dsimp only [x₆]; simp only [Data.set_regs_of_ne h2 _, Data.set_regs_of_ne h1 _]
  rw [hreg₅ reg h4 h5 h6]
  dsimp only [x₄]; simp only [Data.set_regs_of_ne h1 _]
  rw [hreg₃ reg h4 h5 h6]
  dsimp only [x₂]; simp only [Data.set_regs_of_ne h3 _, Data.set_regs_of_ne h2 _,
    Data.set_regs_of_ne h1 _]

private theorem splitChildCode_spec {w base capNodes t u m slot c cnt : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_lt : u < cnt) (hc_lt : c < cnt) (huc : u ≠ c) (hcap : cnt + 1 ≤ capNodes)
    (hm_le : m ≤ 2 * t - 2) (hslot : slot ≤ m)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hz0 : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t)
    (hcur : x.regs rCur = u) (hnk : x.regs rNumK = m)
    (hslot_reg : x.regs rSlot = slot) (hchild : x.regs rChild = c) (hcnt : x.regs rCnt = cnt) :
    ∃ y, ExecWithin w splitChildCode x y (75 * t + 115) ∧
      y.Bounded w ∧
      y.mem = memSplitChild base t u m slot c cnt x.mem ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rZero = 0 ∧ y.regs rOne = 1 ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
      y.regs rKey = x.regs rKey ∧ y.regs rVal = x.regs rVal ∧
      y.regs rActive = x.regs rActive ∧
      y.regs rCur = u ∧ y.regs rSlot = slot ∧ y.regs rChild = c ∧
      y.regs rNumK = m + 1 ∧ y.regs rCnt = cnt + 1 := by
  have hsep_raw : nodeAddr base t u + 6 * t ≤ nodeAddr base t c ∨
      nodeAddr base t c + 6 * t ≤ nodeAddr base t u := nodeAddr_sep base t huc
  have hsep_cz : nodeAddr base t c + 6 * t ≤ nodeAddr base t cnt := by
    have hmul : (c + 1) * nodeStride t ≤ cnt * nodeStride t := Nat.mul_le_mul_right _ hc_lt
    simp only [nodeAddr, nodeStride, Nat.add_mul, Nat.one_mul] at hmul ⊢; omega
  obtain ⟨x₁, he1, hb₁, hmem₁, _, hz₁, hkeep₁⟩ :=
    copyUpperCode_spec ht (by omega) (by omega) (by omega) hbdd hfit hz0 ho hbase hdeg hstride
      hchild hcnt
  have hkeep₁' : ∀ reg : Fin 20,
      (reg.val < 13 ∧ reg.val ≠ 5) ∨ reg.val = 17 → x₁.regs reg = x.regs reg :=
    fun reg h => hkeep₁ reg
      (fun heq => by have := congrArg Fin.val heq; dsimp [rSrc] at this; omega)
      (fun heq => by have := congrArg Fin.val heq; dsimp [rDst] at this; omega)
      (fun heq => by have := congrArg Fin.val heq; dsimp [rLim] at this; omega)
      (fun heq => by have := congrArg Fin.val heq; dsimp [rIdx] at this; omega)
      (fun heq => by have := congrArg Fin.val heq; dsimp [rTmp1] at this; omega)
      (fun heq => by have := congrArg Fin.val heq; dsimp [rTmp2] at this; omega)
      (fun heq => by have := congrArg Fin.val heq; dsimp [rZero] at this; omega)
  obtain ⟨x₇, hshifts, _, hmem₇, hreg₇⟩ :=
    splitChildShifts_spec ht (by omega : u < capNodes) hm_le hslot hb₁ hfit
      ((hkeep₁' rOne (by decide)).trans ho)
      ((hkeep₁' rBase (by decide)).trans hbase)
      ((hkeep₁' rDeg (by decide)).trans hdeg)
      ((hkeep₁' rStride (by decide)).trans hstride)
      ((hkeep₁' rCur (by decide)).trans hcur)
      ((hkeep₁' rNumK (by decide)).trans hnk)
      ((hkeep₁' rSlot (by decide)).trans hslot_reg)
  have hreg₇' : ∀ reg : Fin 20, reg.val < 13 ∨ reg.val = 17 → x₇.regs reg = x₁.regs reg :=
    fun reg h => hreg₇ reg
      (fun heq => by have := congrArg Fin.val heq; dsimp [rSrc] at this; omega)
      (fun heq => by have := congrArg Fin.val heq; dsimp [rDst] at this; omega)
      (fun heq => by have := congrArg Fin.val heq; dsimp [rLim] at this; omega)
      (fun heq => by have := congrArg Fin.val heq; dsimp [rIdx] at this; omega)
      (fun heq => by have := congrArg Fin.val heq; dsimp [rTmp1] at this; omega)
      (fun heq => by have := congrArg Fin.val heq; dsimp [rTmp2] at this; omega)
  have hmem₇_eq : x₇.mem =
      let au' := nodeAddr base t u
      let m1 := memCopyUpper base t c cnt x.mem
      let m2 := shiftArrRight (au' + 2) m (m - slot) m1
      let m3 := shiftArrRight (au' + (2 * t + 1)) m (m - slot) m2
      shiftArrRight (au' + 4 * t) (m + 1) (m - slot) m3 := by
    rw [hmem₇, hmem₁]
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t c = ac := ⟨_, rfl⟩
  have hsep_uc : au + 6 * t ≤ ac ∨ ac + 6 * t ≤ au := by
    rw [← hau_def, ← hac_def]; exact hsep_raw
  have hk_med : x₇.mem (nodeAddr base t c + 2 + (t - 1)) = keyAt base t x.mem c (t - 1) := by
    rw [hmem₇_eq]; dsimp only
    rw [hau_def, hac_def,
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
    dsimp only [keyAt]; rw [← hac_def]; simp only [Nat.add_assoc]
    exact memCopyUpper_at_c hsep_cz (2 + (t - 1)) (by omega) (by omega) x.mem
  have hv_med :
      x₇.mem (nodeAddr base t c + (2 * t + 1) + (t - 1)) = valAt base t x.mem c (t - 1) := by
    rw [hmem₇_eq]; dsimp only
    rw [hau_def, hac_def,
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
      shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
    dsimp only [valAt]; rw [← hac_def]; simp only [Nat.add_assoc]
    exact memCopyUpper_at_c hsep_cz (2 * t + (1 + (t - 1))) (by omega) (by omega) x.mem
  obtain ⟨y, hp4, hymem, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hv_y, hact_y, hcur_y, hsl_y,
      hch_y, hnk_y, hcnt_y⟩ :=
    splitChildPost_spec ht hu_lt hc_lt hcap hm_le hslot hfit
      ((hreg₇' rZero (by decide)).trans hz₁)
      ((hreg₇' rOne (by decide)).trans ((hkeep₁' rOne (by decide)).trans ho))
      ((hreg₇' rBase (by decide)).trans ((hkeep₁' rBase (by decide)).trans hbase))
      ((hreg₇' rDeg (by decide)).trans ((hkeep₁' rDeg (by decide)).trans hdeg))
      ((hreg₇' rStride (by decide)).trans ((hkeep₁' rStride (by decide)).trans hstride))
      ((hreg₇' rCur (by decide)).trans ((hkeep₁' rCur (by decide)).trans hcur))
      ((hreg₇' rNumK (by decide)).trans ((hkeep₁' rNumK (by decide)).trans hnk))
      ((hreg₇' rSlot (by decide)).trans ((hkeep₁' rSlot (by decide)).trans hslot_reg))
      ((hreg₇' rChild (by decide)).trans ((hkeep₁' rChild (by decide)).trans hchild))
      ((hreg₇' rCnt (by decide)).trans ((hkeep₁' rCnt (by decide)).trans hcnt))
      hk_med hv_med hsep_raw hmem₇_eq
  have hfull : ExecWithin w splitChildCode x y (75 * t + 115) :=
    (he1.seq (hshifts.seq hp4)).mono (by omega)
  have hmod : Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
    intro addr hnot
    rw [hymem]
    have hb_lo_u := base_lt_nodeAddr base t u 0
    have hb_lo_c := base_lt_nodeAddr base t c 0
    have hb_lo_z := base_lt_nodeAddr base t cnt 0
    have hau_le := nodeAddr_add_le_arena (base := base) (u := u) (by omega : u < capNodes)
      (o := 6 * t) le_rfl
    have hac_le := nodeAddr_add_le_arena (base := base) (u := c) (by omega : c < capNodes)
      (o := 6 * t) le_rfl
    have haz_le := nodeAddr_add_le_arena (base := base) (u := cnt) (by omega : cnt < capNodes)
      (o := 6 * t) le_rfl
    apply memSplitChild_outside ht hm_le hslot
    · intro heq; apply hnot
      simp only [Block.mem_footprint, Block.Owns, arenaWords]; omega
    · by_contra h_in; apply hnot
      simp only [Block.mem_footprint, Block.Owns, nodeStride] at h_in hau_le ⊢; omega
    · by_contra h_in; apply hnot
      simp only [Block.mem_footprint, Block.Owns, nodeStride] at h_in hac_le ⊢; omega
    · by_contra h_in; apply hnot
      simp only [Block.mem_footprint, Block.Owns, nodeStride] at h_in haz_le ⊢; omega
  exact ⟨y, hfull, hfull.bounded hbdd, hymem, hmod, hz_y, ho_y, hb_y, hd_y, hst_y,
    hk_y.trans ((hreg₇' rKey (by decide)).trans (hkeep₁' rKey (by decide))),
    hv_y.trans ((hreg₇' rVal (by decide)).trans (hkeep₁' rVal (by decide))),
    hact_y.trans ((hreg₇' rActive (by decide)).trans (hkeep₁' rActive (by decide))),
    hcur_y, hsl_y, hch_y, hnk_y, hcnt_y⟩

private def leafInsertPre1 : Code .standard 20 := ram[
  rDst ← rNumK;
  rLim ← rNumK - rSlot ]

private def leafInsertPre2 : Code .standard 20 := ram[
  rSrc ← rSrc + rDeg;
  rSrc ← rSrc + rDeg;
  rSrc ← rSrc - rOne ]

private def leafInsertPost : Code .standard 20 := ram[
  rTmp1 ← rSrc + rSlot;
  *rTmp1 ← rVal;
  rSrc ← rSrc - rDeg;
  rSrc ← rSrc - rDeg;
  rSrc ← rSrc + rOne;
  rTmp1 ← rSrc + rSlot;
  *rTmp1 ← rKey;
  rSrc ← rSrc - rOne;
  rTmp1 ← rNumK + rOne;
  *rSrc ← rTmp1;
  rActive ← #0 ]

private def leafInsertCode : Code .standard 20 := ram[
  ⟪leafInsertPre1⟫;
  ⟪shiftLoop⟫;
  ⟪leafInsertPre2⟫;
  ⟪shiftLoop⟫;
  ⟪leafInsertPost⟫ ]

private theorem leafInsertCode_spec {w base capNodes t u m slot k v : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hm_le : m ≤ 2 * t - 2) (hslot : slot ≤ m)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (ho : x.regs rOne = 1) (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hkey : x.regs rKey = k) (hval : x.regs rVal = v)
    (hnk : x.regs rNumK = m) (hslot_reg : x.regs rSlot = slot)
    (hsrc : x.regs rSrc = nodeAddr base t u + 2) :
    ∃ y, ExecWithin w leafInsertCode x y (36 * t + 22) ∧
      y.Bounded w ∧
      y.mem = memInsertLeaf base t u m slot k v x.mem ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rZero = x.regs rZero ∧
      y.regs rActive = 0 := by
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  have hsrc_au : x.regs rSrc = au + 2 := hau_def ▸ hsrc
  have hau_le : au + 6 * t ≤ base + arenaWords t capNodes :=
    hau_def ▸ nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
  have hf_ms : Fits w (m - slot) := hfit.of_le (by omega)
  let x₁ := (x.set rDst m).set rLim (m - slot)
  have hp1 : ExecWithin w leafInsertPre1 x x₁ 2 := by
    unfold leafInsertPre1; dsimp only [x₁]; wram_exec [hnk, hslot_reg, hf_ms]
  obtain ⟨x₂, hs1, hb₂, hmem₂, hreg₂⟩ :=
    shiftLoop_spec (arrBase := au + 2) (upper := m) (count := m - slot)
      (hp1.bounded hbdd) ho hsrc_au rfl rfl (by omega) (hfit.of_le (by omega))
  have hsrc₂ : x₂.regs rSrc = au + 2 :=
    (hreg₂ rSrc (by decide) (by decide) (by decide)).trans hsrc_au
  have hdst₂ : x₂.regs rDst = m := hreg₂ rDst (by decide) (by decide) (by decide)
  have hlim₂ : x₂.regs rLim = m - slot := hreg₂ rLim (by decide) (by decide) (by decide)
  have ho₂ : x₂.regs rOne = 1 := (hreg₂ rOne (by decide) (by decide) (by decide)).trans ho
  have hd₂ : x₂.regs rDeg = t := (hreg₂ rDeg (by decide) (by decide) (by decide)).trans hdeg
  have hav_eq : au + 2 + t + t - 1 = au + (2 * t + 1) := by omega
  let x₃ := ((x₂.set rSrc (au + 2 + t)).set rSrc (au + 2 + t + t)).set rSrc (au + (2 * t + 1))
  have hp2 : ExecWithin w leafInsertPre2 x₂ x₃ 3 := by
    unfold leafInsertPre2; dsimp only [x₃]
    have hf1 : Fits w (au + 2 + t) := hfit.of_le (by omega)
    have hf2 : Fits w (au + 2 + t + t) := hfit.of_le (by omega)
    have hf3 : Fits w (au + (2 * t + 1)) := hfit.of_le (by omega)
    wram_exec [ho₂, hd₂, hsrc₂, hav_eq, hf1, hf2, hf3]
  obtain ⟨x₄, hs2, hb₄, hmem₄, hreg₄⟩ :=
    shiftLoop_spec (arrBase := au + (2 * t + 1)) (upper := m) (count := m - slot)
      (hp2.bounded hb₂) ho₂ rfl hdst₂ hlim₂ (by omega) (hfit.of_le (by omega))
  have hsrc₄ : x₄.regs rSrc = au + (2 * t + 1) := hreg₄ rSrc (by decide) (by decide) (by decide)
  have ho₄ : x₄.regs rOne = 1 := (hreg₄ rOne (by decide) (by decide) (by decide)).trans ho₂
  have hd₄ : x₄.regs rDeg = t := (hreg₄ rDeg (by decide) (by decide) (by decide)).trans hd₂
  have hb₄_reg : x₄.regs rBase = base :=
    (hreg₄ rBase (by decide) (by decide) (by decide)).trans
      ((hreg₂ rBase (by decide) (by decide) (by decide)).trans hbase)
  have hz₄ : x₄.regs rZero = x.regs rZero :=
    (hreg₄ rZero (by decide) (by decide) (by decide)).trans
      (hreg₂ rZero (by decide) (by decide) (by decide))
  have hk₄ : x₄.regs rKey = k :=
    (hreg₄ rKey (by decide) (by decide) (by decide)).trans
      ((hreg₂ rKey (by decide) (by decide) (by decide)).trans hkey)
  have hv₄ : x₄.regs rVal = v :=
    (hreg₄ rVal (by decide) (by decide) (by decide)).trans
      ((hreg₂ rVal (by decide) (by decide) (by decide)).trans hval)
  have hnk₄ : x₄.regs rNumK = m :=
    (hreg₄ rNumK (by decide) (by decide) (by decide)).trans
      ((hreg₂ rNumK (by decide) (by decide) (by decide)).trans hnk)
  have hsl₄ : x₄.regs rSlot = slot :=
    (hreg₄ rSlot (by decide) (by decide) (by decide)).trans
      ((hreg₂ rSlot (by decide) (by decide) (by decide)).trans hslot_reg)
  have hak_back : au + (2 * t + 1) - t - t + 1 = au + 2 := by omega
  have hau1_back : au + 2 - 1 = au + 1 := by omega
  have hf_vs : Fits w (au + (2 * t + 1) + slot) := hfit.of_le (by omega)
  have hf_sub1 : Fits w (au + (2 * t + 1) - t) := hfit.of_le (by omega)
  have hf_sub2 : Fits w (au + (2 * t + 1) - t - t) := hfit.of_le (by omega)
  have hf_sub21 : Fits w (au + (2 * t + 1) - t - t + 1) := hfit.of_le (by omega)
  have hf_au2 : Fits w (au + 2) := hfit.of_le (by omega)
  have hf_ks : Fits w (au + 2 + slot) := hfit.of_le (by omega)
  have hf_au2m1 : Fits w (au + 2 - 1) := hfit.of_le (by omega)
  have hf_au1 : Fits w (au + 1) := hfit.of_le (by omega)
  have hf_m1 : Fits w (m + 1) := hfit.of_le (by omega)
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  simp only [x₁, Data.set_mem] at hmem₂
  simp only [x₃, Data.set_mem] at hmem₄
  obtain ⟨y, hp3, hymem, hb_y, hd_y, hz_y, hact_y⟩ :
      ∃ y, ExecWithin w leafInsertPost x₄ y 11 ∧
        y.mem = memInsertLeaf base t u m slot k v x.mem ∧
        y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rZero = x.regs rZero ∧
        y.regs rActive = 0 := by
    unfold leafInsertPost
    apply WP.exists_execWithin
    wram_exec [ho₄, hd₄, hsrc₄, hk₄, hv₄, hnk₄, hsl₄, hak_back, hau1_back,
      hf_vs, hf_sub1, hf_sub2, hf_sub21, hf_au2, hf_ks, hf_au2m1, hf_au1, hf_m1, hf0]
    wram_simp [hb₄_reg, hd₄, hz₄]
    simp only [memInsertLeaf, hau_def, ← hmem₂, ← hmem₄]
    funext a
    by_cases h1 : a = au + 1
    · subst h1; simp only [Function.update_self]
    · rw [Function.update_of_ne h1, Function.update_of_ne h1]
      by_cases h2 : a = au + (2 * t + 1) + slot
      · subst h2
        rw [Function.update_self, Function.update_of_ne (by omega), Function.update_self]
      · rw [Function.update_of_ne h2]
        by_cases h3 : a = au + 2 + slot
        · subst h3; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h3]
  have hfull : ExecWithin w leafInsertCode x y (36 * t + 22) :=
    (hp1.seq (hs1.seq (hp2.seq (hs2.seq hp3)))).mono (by omega)
  have hmod : Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
    intro addr hnot
    rw [hymem]
    have hb_lo := base_lt_nodeAddr base t u 0
    apply memInsertLeaf_outside ht hm_le hslot
    by_contra h_in; apply hnot
    simp only [Block.mem_footprint, Block.Owns, nodeStride, hau_def] at h_in ⊢
    omega
  exact ⟨y, hfull, hfull.bounded hbdd, hymem, hmod, hb_y, hd_y, hz_y, hact_y⟩

/-! ## 8. Proactive top-down insertion (`insertCode`, `O(t log_t n)`) -/

private def overwriteValCode : Code .standard 20 := ram[
  rTmp1 ← rCur * rStride;
  rTmp1 ← rBase + rTmp1;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rDeg;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rSlot;
  *rTmp1 ← rVal;
  rActive ← #0 ]

private def insertDescendAfterSplit : Code .standard 20 := ram[
  rTmp1 ← rCur * rStride;
  rTmp1 ← rBase + rTmp1;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rOne;
  rTmp1 ← rTmp1 + rSlot;
  rTmp2 ← *rTmp1;
  if rTmp2 = rKey then [
    ⟪overwriteValCode⟫
  ] else [
    if rKey < rTmp2 then [
      rCur ← rChild
    ] else [
      rCur ← rCnt - rOne
    ]
  ] ]

private def insertDescendOrLeaf : Code .standard 20 := ram[
  rTmp1 ← rSrc - rOne;
  rTmp1 ← rTmp1 - rOne;
  rTmp2 ← *rTmp1;
  if rTmp2 = rZero then [
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rDeg;
    rTmp1 ← rTmp1 + rSlot;
    rChild ← *rTmp1;
    rTmp1 ← rChild * rStride;
    rTmp1 ← rBase + rTmp1;
    rTmp1 ← rTmp1 + rOne;
    rTmp1 ← rTmp1 + rOne;
    rTmp1 ← rTmp1 + rOne;
    rTmp2 ← *rTmp1;
    rTmp1 ← rDeg + rDeg;
    rTmp1 ← rTmp1 - rOne;
    if rTmp2 = rTmp1 then [
      ⟪splitChildCode⟫;
      ⟪insertDescendAfterSplit⟫
    ] else [
      rCur ← rChild
    ]
  ] else [
    ⟪leafInsertCode⟫
  ] ]

private def insertBranch : Code .standard 20 := ram[
  if rSlot < rNumK then [
    rTmp1 ← rSrc + rSlot;
    rTmp2 ← *rTmp1;
    if rTmp2 = rKey then [
      ⟪overwriteValCode⟫
    ] else [
      ⟪insertDescendOrLeaf⟫
    ]
  ] else [
    ⟪insertDescendOrLeaf⟫
  ] ]

private def insertStep : Code .standard 20 := ram[
  ⟪loadAndScan⟫;
  ⟪insertBranch⟫ ]

private def insertLoop : Code .standard 20 := ram[
  while rZero < rActive do [⟪insertStep⟫] ]

private def initSingleCode : Code .standard 20 := ram[
  rTmp1 ← rBase + rOne;
  rTmp1 ← rTmp1 + rOne;
  *rTmp1 ← rOne;
  rTmp2 ← rTmp1 + rOne;
  *rTmp2 ← rOne;
  rTmp2 ← rTmp2 + rOne;
  *rTmp2 ← rKey;
  rTmp2 ← rTmp1 + rDeg;
  rTmp2 ← rTmp2 + rDeg;
  rTmp2 ← rTmp2 + rOne;
  *rTmp2 ← rVal;
  *rBase ← rZero;
  rTmp1 ← rBase + rOne;
  *rTmp1 ← rOne ]

/-- Insert `(rKey, rVal)` into the B-tree arena at `rBase` of minimum degree `rDeg` using proactive
top-down node splitting ([CLRS2009], Section 18.2). -/
def insertCode : Code .standard 20 := ram[
  rZero ← #0;
  rOne ← #1;
  rTmp1 ← rBase + rOne;
  rCnt ← *rTmp1;
  if rCnt = rZero then [
    ⟪initSingleCode⟫
  ] else [
    rStride ← rDeg + rDeg;
    rTmp1 ← rStride + rStride;
    rStride ← rStride + rTmp1;
    rChild ← *rBase;
    rTmp1 ← rChild * rStride;
    rTmp1 ← rBase + rTmp1;
    rTmp1 ← rTmp1 + rOne;
    rTmp1 ← rTmp1 + rOne;
    rTmp1 ← rTmp1 + rOne;
    rNumK ← *rTmp1;
    rTmp1 ← rDeg + rDeg;
    rTmp1 ← rTmp1 - rOne;
    if rNumK = rTmp1 then [
      ⟪splitRootCode⟫
    ] else [
      rCur ← rChild
    ];
    rActive ← #1;
    ⟪insertLoop⟫
  ] ]

private theorem overwriteValCode_spec {w base capNodes t u slot v : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hslot : slot < 2 * t - 1)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (ho : x.regs rOne = 1) (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t) (hcur : x.regs rCur = u)
    (hslot_reg : x.regs rSlot = slot) (hval : x.regs rVal = v) :
    ∃ y, ExecWithin w overwriteValCode x y 10 ∧
      y.Bounded w ∧
      y.mem = memOverwriteVal base t u slot v x.mem ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rZero = x.regs rZero ∧
      y.regs rBase = base ∧
      y.regs rDeg = t ∧
      y.regs rActive = 0 := by
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  have hau_le : au + 6 * t ≤ base + arenaWords t capNodes :=
    hau_def ▸ nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
  have hna_u : base + u * (6 * t) + 1 + 1 = au := by
    rw [← hau_def]; simp only [nodeAddr, nodeStride]; omega
  have h2t_u : au + t + t + 1 = au + (2 * t + 1) := by omega
  have hf_umul : Fits w (u * (6 * t)) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_ub0 : Fits w (base + u * (6 * t)) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_ub1 : Fits w (base + u * (6 * t) + 1) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_ub2 : Fits w (base + u * (6 * t) + 1 + 1) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_au : Fits w au := hfit.of_le (by omega)
  have hf_aut1 : Fits w (au + t) := hfit.of_le (by omega)
  have hf_aut2 : Fits w (au + t + t) := hfit.of_le (by omega)
  have hf_aut21 : Fits w (au + t + t + 1) := hfit.of_le (by omega)
  have hf_au2t1 : Fits w (au + (2 * t + 1)) := hfit.of_le (by omega)
  have hf_auvs : Fits w (au + (2 * t + 1) + slot) := hfit.of_le (by omega)
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  obtain ⟨y, he, hymem, hz_y, hb_y, hd_y, hact_y⟩ :
      ∃ y, ExecWithin w overwriteValCode x y 10 ∧
        y.mem = memOverwriteVal base t u slot v x.mem ∧
        y.regs rZero = x.regs rZero ∧ y.regs rBase = base ∧ y.regs rDeg = t ∧
        y.regs rActive = 0 := by
    unfold overwriteValCode
    apply WP.exists_execWithin
    wram_exec [ho, hbase, hdeg, hstride, hcur, hslot_reg, hval, hna_u, h2t_u,
      hf_umul, hf_ub0, hf_ub1, hf_ub2, hf_au, hf_aut1, hf_aut2, hf_aut21, hf_au2t1, hf_auvs, hf0]
    wram_simp [hbase, hdeg]
    simp only [memOverwriteVal, hau_def]
  have hmod : Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
    rw [hymem]
    have hb_lo : base + 1 < au := hau_def ▸ base_lt_nodeAddr base t u 0
    exact Modifies.write_of_owns (n := arenaWords t capNodes)
      ⟨by rw [hau_def]; omega, by rw [hau_def]; omega⟩ v
  exact ⟨y, he, he.bounded hbdd, hymem, hmod, hz_y, hb_y, hd_y, hact_y⟩

private theorem insertDescendAfterSplit_spec {w base capNodes t u slot c cnt₁ k v : ℕ}
    {x : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes) (hslot : slot < 2 * t - 1) (hcnt_pos : 1 ≤ cnt₁)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (ho : x.regs rOne = 1) (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t) (hcur : x.regs rCur = u)
    (hslot_reg : x.regs rSlot = slot) (hchild : x.regs rChild = c) (hcnt : x.regs rCnt = cnt₁)
    (hkey : x.regs rKey = k) (hval : x.regs rVal = v) :
    ∃ y, ExecWithin w insertDescendAfterSplit x y 20 ∧
      y.Bounded w ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rZero = x.regs rZero ∧ y.regs rOne = 1 ∧
      y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
      y.regs rKey = k ∧ y.regs rVal = v ∧ y.regs rCnt = cnt₁ ∧
      (if keyAt base t x.mem u slot = k then
        y.mem = memOverwriteVal base t u slot v x.mem ∧ y.regs rActive = 0
      else if k < keyAt base t x.mem u slot then
        y.mem = x.mem ∧ y.regs rCur = c ∧ y.regs rActive = x.regs rActive
      else
        y.mem = x.mem ∧ y.regs rCur = cnt₁ - 1 ∧ y.regs rActive = x.regs rActive) := by
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  have hau_le : au + 6 * t ≤ base + arenaWords t capNodes :=
    hau_def ▸ nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
  have hna_u : base + u * (6 * t) + 1 + 1 = au := by
    rw [← hau_def]; simp only [nodeAddr, nodeStride]; omega
  have hau2_eq : au + 1 + 1 = au + 2 := by omega
  have hf_umul : Fits w (u * (6 * t)) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_ub0 : Fits w (base + u * (6 * t)) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_ub1 : Fits w (base + u * (6 * t) + 1) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_ub2 : Fits w (base + u * (6 * t) + 1 + 1) := hfit.of_le (by
    rw [← hau_def] at hau_le; simp only [nodeAddr, nodeStride] at hau_le; omega)
  have hf_au : Fits w au := hfit.of_le (by omega)
  have hf_au1 : Fits w (au + 1) := hfit.of_le (by omega)
  have hf_au11 : Fits w (au + 1 + 1) := hfit.of_le (by omega)
  have hf_au2 : Fits w (au + 2) := hfit.of_le (by omega)
  have hf_auks : Fits w (au + 2 + slot) := hfit.of_le (by omega)
  have hks_eq : x.mem (au + 2 + slot) = keyAt base t x.mem u slot := by
    simp only [keyAt, hau_def]
  by_cases heq_k : keyAt base t x.mem u slot = k
  · have he_full : ∃ y', ExecWithin w insertDescendAfterSplit x y' 20 ∧
        y'.mem = memOverwriteVal base t u slot v x.mem ∧
        y'.regs rZero = x.regs rZero ∧ y'.regs rOne = 1 ∧
        y'.regs rBase = base ∧ y'.regs rDeg = t ∧ y'.regs rStride = 6 * t ∧
        y'.regs rKey = k ∧ y'.regs rVal = v ∧ y'.regs rCnt = cnt₁ ∧ y'.regs rActive = 0 := by
      unfold insertDescendAfterSplit overwriteValCode
      have h2t_u : au + t + t + 1 = au + (2 * t + 1) := by omega
      have hf_aut1 : Fits w (au + t) := hfit.of_le (by omega)
      have hf_aut2 : Fits w (au + t + t) := hfit.of_le (by omega)
      have hf_aut21 : Fits w (au + t + t + 1) := hfit.of_le (by omega)
      have hf_au2t1 : Fits w (au + (2 * t + 1)) := hfit.of_le (by omega)
      have hf_auvs : Fits w (au + (2 * t + 1) + slot) := hfit.of_le (by omega)
      have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
      apply WP.exists_execWithin
      wram_exec [ho, hbase, hdeg, hstride, hcur, hslot_reg, hkey, hval, hna_u, hau2_eq, h2t_u,
        hks_eq, heq_k, hf_umul, hf_ub0, hf_ub1, hf_ub2, hf_au, hf_au1, hf_au11, hf_au2, hf_auks,
        hf_aut1, hf_aut2, hf_aut21, hf_au2t1, hf_auvs, hf0]
      wram_simp [ho, hbase, hdeg, hstride, hkey, hval, hcnt]
      simp only [memOverwriteVal, hau_def]
    obtain ⟨y', he', hymem', hz', ho', hb', hd', hst', hk', hv', hcnt', hact'⟩ := he_full
    have hmod' : Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y'.mem := by
      rw [hymem']
      have hb_lo : base + 1 < au := hau_def ▸ base_lt_nodeAddr base t u 0
      exact Modifies.write_of_owns (n := arenaWords t capNodes)
        ⟨by rw [hau_def]; omega, by rw [hau_def]; omega⟩ v
    refine ⟨y', he', he'.bounded hbdd, hmod', hz', ho', hb', hd', hst', hk', hv', hcnt', ?_⟩
    simp only [heq_k, ↓reduceIte]
    exact ⟨hymem', hact'⟩
  · by_cases hlt_k : k < keyAt base t x.mem u slot
    · obtain ⟨y, he, hymem, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hv_y, hcnt_y, hcur_y, hact_y⟩ :
          ∃ y, ExecWithin w insertDescendAfterSplit x y 20 ∧ y.mem = x.mem ∧
            y.regs rZero = x.regs rZero ∧ y.regs rOne = 1 ∧
            y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
            y.regs rKey = k ∧ y.regs rVal = v ∧ y.regs rCnt = cnt₁ ∧
            y.regs rCur = c ∧ y.regs rActive = x.regs rActive := by
        unfold insertDescendAfterSplit
        apply WP.exists_execWithin
        wram_exec [ho, hbase, hdeg, hstride, hcur, hslot_reg, hchild, hkey, hna_u, hau2_eq,
          hks_eq, heq_k, hlt_k, hf_umul, hf_ub0, hf_ub1, hf_ub2, hf_au, hf_au1, hf_au11,
          hf_au2, hf_auks]
        wram_simp [ho, hbase, hdeg, hstride, hkey, hval, hcnt]
      refine ⟨y, he, he.bounded hbdd, hymem ▸ Modifies.refl _ _, hz_y, ho_y, hb_y, hd_y, hst_y,
        hk_y, hv_y, hcnt_y, ?_⟩
      simp only [heq_k, hlt_k, ↓reduceIte]
      exact ⟨hymem, hcur_y, hact_y⟩
    · have hf_cm1 : Fits w (cnt₁ - 1) := (hbdd.1 rCnt).of_le (by rw [hcnt]; omega)
      obtain ⟨y, he, hymem, hz_y, ho_y, hb_y, hd_y, hst_y, hk_y, hv_y, hcnt_y, hcur_y, hact_y⟩ :
          ∃ y, ExecWithin w insertDescendAfterSplit x y 20 ∧ y.mem = x.mem ∧
            y.regs rZero = x.regs rZero ∧ y.regs rOne = 1 ∧
            y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rStride = 6 * t ∧
            y.regs rKey = k ∧ y.regs rVal = v ∧ y.regs rCnt = cnt₁ ∧
            y.regs rCur = cnt₁ - 1 ∧ y.regs rActive = x.regs rActive := by
        unfold insertDescendAfterSplit
        apply WP.exists_execWithin
        wram_exec [ho, hbase, hdeg, hstride, hcur, hslot_reg, hcnt, hkey, hna_u, hau2_eq,
          hks_eq, heq_k, hlt_k, hf_umul, hf_ub0, hf_ub1, hf_ub2, hf_au, hf_au1, hf_au11,
          hf_au2, hf_auks, hf_cm1]
        wram_simp [ho, hbase, hdeg, hstride, hkey, hval, hcnt]
      refine ⟨y, he, he.bounded hbdd, hymem ▸ Modifies.refl _ _, hz_y, ho_y, hb_y, hd_y, hst_y,
        hk_y, hv_y, hcnt_y, ?_⟩
      simp only [heq_k, hlt_k, ↓reduceIte]
      exact ⟨hymem, hcur_y, hact_y⟩

private theorem keyAt_memSplitChild_lt {base t u m slot c cnt i : ℕ} {mem : ℕ → ℕ}
    (ht : 2 ≤ t) (hm_le : m ≤ 2 * t - 2) (hslot : slot ≤ m)
    (huc : u ≠ c) (huz : u ≠ cnt) (hi : i < slot) :
    keyAt base t (memSplitChild base t u m slot c cnt mem) u i = keyAt base t mem u i := by
  have hb_k := base_lt_nodeAddr base t u (2 + i)
  have hsu := nodeAddr_sep base t huc
  have hsz := nodeAddr_sep base t huz
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t c = ac := ⟨_, rfl⟩
  obtain ⟨az, haz_def⟩ : ∃ az, nodeAddr base t cnt = az := ⟨_, rfl⟩
  simp only [nodeStride, hau_def, hac_def, haz_def] at hb_k hsu hsz
  dsimp only [keyAt, memSplitChild]
  simp only [hau_def]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega)]
  exact memCopyUpper_outside ht mem _ (by rw [hac_def]; simp only [nodeStride]; omega)
    (by rw [haz_def]; simp only [nodeStride]; omega)

private theorem keyAt_memSplitChild_gt {base t u m slot c cnt i : ℕ} {mem : ℕ → ℕ}
    (ht : 2 ≤ t) (hm_le : m ≤ 2 * t - 2) (hslot : slot ≤ m)
    (huc : u ≠ c) (huz : u ≠ cnt) (hge : slot + 1 ≤ i) (hi : i < m + 1) :
    keyAt base t (memSplitChild base t u m slot c cnt mem) u i = keyAt base t mem u (i - 1) := by
  have hb_k := base_lt_nodeAddr base t u (2 + i)
  have hsu := nodeAddr_sep base t huc
  have hsz := nodeAddr_sep base t huz
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t c = ac := ⟨_, rfl⟩
  obtain ⟨az, haz_def⟩ : ∃ az, nodeAddr base t cnt = az := ⟨_, rfl⟩
  simp only [nodeStride, hau_def, hac_def, haz_def] at hb_k hsu hsz
  dsimp only [keyAt, memSplitChild]
  simp only [hau_def]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
    shiftArrRight_outside _ _ _ _ (by omega) _ (by omega),
    shiftArrRight_shifted (au + 2) m (m - slot) _ (by omega) i (by omega) (by omega)]
  exact memCopyUpper_outside ht mem _ (by rw [hac_def]; simp only [nodeStride]; omega)
    (by rw [haz_def]; simp only [nodeStride]; omega)

private theorem insertDescendOrLeaf_int_spec
    {w base capNodes t u m slot c cnt k v : ℕ} {mem₀ : ℕ → ℕ} {z : Data 20}
    (ht : 2 ≤ t) (hu_lt_cnt : u < cnt) (hc_lt_cnt : c < cnt) (huc : u ≠ c)
    (hcap_cnt1 : cnt + 1 ≤ capNodes) (hnonfull : m ≤ 2 * t - 2) (hslot_le : slot ≤ m)
    (hlf0 : leafFlag base t mem₀ u = 0) (hcid : childAt base t mem₀ u slot = c)
    (hfit : Fits w (base + arenaWords t capNodes))
    (hbz : z.Bounded w) (hmz : z.mem = mem₀)
    (hzz : z.regs rZero = 0) (hoz : z.regs rOne = 1)
    (hbaz : z.regs rBase = base) (hdz : z.regs rDeg = t) (hstz : z.regs rStride = 6 * t)
    (hkz : z.regs rKey = k) (hvz : z.regs rVal = v)
    (hcurz : z.regs rCur = u) (hcntz : z.regs rCnt = cnt)
    (hnkz : z.regs rNumK = m) (hslz : z.regs rSlot = slot)
    (hsrcz : z.regs rSrc = nodeAddr base t u + 2) (hactz : z.regs rActive = 1) :
    ∃ x₃, ExecWithin w insertDescendOrLeaf z x₃ (75 * t + 155) ∧
      x₃.Bounded w ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint mem₀ x₃.mem ∧
      x₃.regs rZero = 0 ∧ x₃.regs rOne = 1 ∧
      x₃.regs rBase = base ∧ x₃.regs rDeg = t ∧ x₃.regs rStride = 6 * t ∧
      x₃.regs rKey = k ∧ x₃.regs rVal = v ∧
      (if numKeys base t mem₀ c = 2 * t - 1 then
        let mem₁ := memSplitChild base t u m slot c cnt mem₀
        x₃.regs rCnt = cnt + 1 ∧
        (if keyAt base t mem₁ u slot = k then
          x₃.mem = memOverwriteVal base t u slot v mem₁ ∧ x₃.regs rActive = 0
        else if k < keyAt base t mem₁ u slot then
          x₃.mem = mem₁ ∧ x₃.regs rCur = c ∧ x₃.regs rActive = 1
        else
          x₃.mem = mem₁ ∧ x₃.regs rCur = cnt ∧ x₃.regs rActive = 1)
      else
        x₃.mem = mem₀ ∧ x₃.regs rCur = c ∧ x₃.regs rCnt = cnt ∧ x₃.regs rActive = 1) := by
  obtain ⟨au, hau_def⟩ : ∃ au, nodeAddr base t u = au := ⟨_, rfl⟩
  obtain ⟨ac, hac_def⟩ : ∃ ac, nodeAddr base t c = ac := ⟨_, rfl⟩
  have hu_cap : u < capNodes := by omega
  have hc_cap : c < capNodes := by omega
  have hau_le' : au + 6 * t ≤ base + arenaWords t capNodes :=
    hau_def ▸ nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
  have hac_le' : ac + 6 * t ≤ base + arenaWords t capNodes :=
    hac_def ▸ nodeAddr_add_le_arena (base := base) hc_cap (o := 6 * t) le_rfl
  have hsrcz_au : z.regs rSrc = au + 2 := hau_def ▸ hsrcz
  have hsub2 : au + 2 - 1 - 1 = au := by omega
  have hadd4 : au + t + t + t + t = au + 4 * t := by omega
  have hna_c : base + c * (6 * t) + 1 + 1 + 1 = ac + 1 := by
    rw [← hac_def]; simp only [nodeAddr, nodeStride]; omega
  have hlfz : z.mem au = 0 := by rw [hmz, ← hau_def]; exact hlf0
  have hcidz : z.mem (au + 4 * t + slot) = c := by
    rw [hmz, ← hau_def, ← hcid]; rfl
  have hnkc_z : z.mem (ac + 1) = numKeys base t mem₀ c := by
    rw [hmz, ← hac_def]; rfl
  have hcap_le : capNodes ≤ capNodes * nodeStride t :=
    Nat.le_mul_of_pos_right _ (by simp only [nodeStride]; omega)
  have hf_au1 : Fits w (au + 2 - 1) := hfit.of_le (by omega)
  have hf_au22 : Fits w (au + 2 - 1 - 1) := hfit.of_le (by omega)
  have hf_au : Fits w au := hfit.of_le (by omega)
  have hf_t1 : Fits w (au + t) := hfit.of_le (by omega)
  have hf_t2 : Fits w (au + t + t) := hfit.of_le (by omega)
  have hf_t3 : Fits w (au + t + t + t) := hfit.of_le (by omega)
  have hf_t40 : Fits w (au + t + t + t + t) := hfit.of_le (by omega)
  have hf_t4 : Fits w (au + 4 * t) := hfit.of_le (by omega)
  have hf_cs : Fits w (au + 4 * t + slot) := hfit.of_le (by omega)
  have hf_cmul : Fits w (c * (6 * t)) := hfit.of_le (by
    rw [← hac_def] at hac_le'; simp only [nodeAddr, nodeStride] at hac_le'; omega)
  have hf_cb0 : Fits w (base + c * (6 * t)) := hfit.of_le (by
    rw [← hac_def] at hac_le'; simp only [nodeAddr, nodeStride] at hac_le'; omega)
  have hf_cb1 : Fits w (base + c * (6 * t) + 1) := hfit.of_le (by
    rw [← hac_def] at hac_le'; simp only [nodeAddr, nodeStride] at hac_le'; omega)
  have hf_cb2 : Fits w (base + c * (6 * t) + 1 + 1) := hfit.of_le (by
    rw [← hac_def] at hac_le'; simp only [nodeAddr, nodeStride] at hac_le'; omega)
  have hf_ac10 : Fits w (base + c * (6 * t) + 1 + 1 + 1) := hfit.of_le (by
    rw [← hac_def] at hac_le'; simp only [nodeAddr, nodeStride] at hac_le'; omega)
  have hf_ac1 : Fits w (ac + 1) := hfit.of_le (by omega)
  have hf_2t : Fits w (t + t) := hfit.of_le (by omega)
  have hf_2tm10 : Fits w (t + t - 1) := hfit.of_le (by omega)
  have hf_2tm1 : Fits w (2 * t - 1) := hfit.of_le (by omega)
  have h2tm1_eq : t + t - 1 = 2 * t - 1 := by omega
  by_cases hfull_c : numKeys base t mem₀ c = 2 * t - 1
  · let z₁ : Data 20 :=
      ((((((((((((((((z.set rTmp1 (au + 2 - 1)).set rTmp1 au).set rTmp2 0).set rTmp1
        (au + t)).set rTmp1 (au + t + t)).set rTmp1 (au + t + t + t)).set rTmp1
        (au + 4 * t)).set rTmp1 (au + 4 * t + slot)).set rChild c).set rTmp1
        (c * (6 * t))).set rTmp1 (base + c * (6 * t))).set rTmp1
        (base + c * (6 * t) + 1)).set rTmp1
        (base + c * (6 * t) + 1 + 1)).set rTmp1 (ac + 1)).set rTmp2
        (2 * t - 1)).set rTmp1 (t + t)).set rTmp1 (2 * t - 1)
    have hbz₁ : z₁.Bounded w := by
      dsimp only [z₁]
      exact ((((((((((((((((hbz.set hf_au1).set hf_au).set
        (hfit.of_le (Nat.zero_le _))).set hf_t1).set hf_t2).set hf_t3).set hf_t4).set
        hf_cs).set (hfit.of_le (by simp only [arenaWords]; omega))).set hf_cmul).set
        hf_cb0).set hf_cb1).set hf_cb2).set hf_ac1).set hf_2tm1).set hf_2t).set hf_2tm1
    obtain ⟨z₂, hsc_exec, hbz₂, hmem_z₂, hmod_sc, hz_z₂, ho_z₂, hb_z₂, hd_z₂, hst_z₂,
        hk_z₂, hv_z₂, hact_z₂, hcur_z₂, hsl_z₂, hch_z₂, _, hcnt_z₂⟩ :=
      splitChildCode_spec (x := z₁) (c := c) ht hu_lt_cnt hc_lt_cnt huc hcap_cnt1 hnonfull
        hslot_le hbz₁ hfit hzz hoz hbaz hdz hstz hcurz hnkz hslz rfl hcntz
    simp only [z₁, Data.set_mem] at hmem_z₂ hmod_sc
    dsimp only [z₁] at hk_z₂ hv_z₂ hact_z₂
    rw [hmz] at hmem_z₂ hmod_sc
    wram_simp at hk_z₂ hv_z₂ hact_z₂
    obtain ⟨x₃, hdas, hbx₃, hmod_das, hz_x₃, ho_x₃, hb_x₃, hd_x₃, hst_x₃, hk_x₃, hv_x₃,
        hcnt_x₃, hbr_das⟩ :=
      insertDescendAfterSplit_spec (x := z₂) ht hu_cap (by omega) (by omega) hbz₂ hfit
        ho_z₂ hb_z₂ hd_z₂ hst_z₂ hcur_z₂ hsl_z₂ hch_z₂ hcnt_z₂ (hk_z₂.trans hkz)
        (hv_z₂.trans hvz)
    have he_dl : ExecWithin w insertDescendOrLeaf z x₃ (75 * t + 155) := by
      unfold insertDescendOrLeaf
      apply WP.execWithin
      wram_exec [hzz, hoz, hbaz, hdz, hstz, hslz, hsrcz_au, hsub2, hadd4, hna_c,
        hlfz, hcidz, hnkc_z, hfull_c, h2tm1_eq,
        hf_au1, hf_au22, hf_au, hf_t1, hf_t2, hf_t3, hf_t40, hf_t4, hf_cs,
        hf_cmul, hf_cb0, hf_cb1, hf_cb2, hf_ac10, hf_ac1, hf_2t, hf_2tm10, hf_2tm1]
      refine WP.of_execWithin hsc_exec ?_
      exact WP.of_execWithin hdas ⟨by omega, rfl⟩
    have hmod_all : Modifies (Block.mk base (arenaWords t capNodes)).footprint mem₀ x₃.mem := by
      simpa only [Finset.union_idempotent] using hmod_sc.trans hmod_das
    rw [hmem_z₂] at hbr_das
    rw [hact_z₂.trans hactz] at hbr_das
    simp only [Nat.add_sub_cancel] at hbr_das
    refine ⟨x₃, he_dl, hbx₃, hmod_all, hz_x₃.trans hz_z₂, ho_x₃,
      hb_x₃, hd_x₃, hst_x₃, hk_x₃, hv_x₃, ?_⟩
    simp only [hfull_c, ↓reduceIte]
    exact ⟨hcnt_x₃, hbr_das⟩
  · obtain ⟨x₃, he_dl, hmx₃, hzx₃, hox₃, hbx₃, hdx₃, hstx₃, hkx₃, hvx₃, hcurx₃, hcntx₃,
        hactx₃⟩ :
        ∃ x₃, ExecWithin w insertDescendOrLeaf z x₃ (75 * t + 155) ∧
          x₃.mem = z.mem ∧ x₃.regs rZero = 0 ∧ x₃.regs rOne = 1 ∧
          x₃.regs rBase = base ∧ x₃.regs rDeg = t ∧ x₃.regs rStride = 6 * t ∧
          x₃.regs rKey = k ∧ x₃.regs rVal = v ∧
          x₃.regs rCur = c ∧ x₃.regs rCnt = cnt ∧ x₃.regs rActive = 1 := by
      unfold insertDescendOrLeaf
      apply WP.exists_execWithin
      wram_exec [hzz, hoz, hbaz, hdz, hstz, hslz, hsrcz_au, hsub2, hadd4, hna_c,
        hlfz, hcidz, hnkc_z, hfull_c, h2tm1_eq,
        hf_au1, hf_au22, hf_au, hf_t1, hf_t2, hf_t3, hf_t40, hf_t4, hf_cs,
        hf_cmul, hf_cb0, hf_cb1, hf_cb2, hf_ac10, hf_ac1, hf_2t, hf_2tm10, hf_2tm1]
      wram_simp [hzz, hoz, hbaz, hdz, hstz, hkz, hvz, hcntz, hactz]
    refine ⟨x₃, he_dl, he_dl.bounded hbz, (hmx₃.trans hmz) ▸ Modifies.refl _ _, hzx₃,
      hox₃, hbx₃, hdx₃, hstx₃, hkx₃, hvx₃, ?_⟩
    simp only [hfull_c, ↓reduceIte]
    exact ⟨hmx₃.trans hmz, hcurx₃, hcntx₃, hactx₃⟩

private theorem insertLoop_overwrite_spec {l w base capNodes t u cnt k v : ℕ} {x x₂ : Data 20}
    (ht : 2 ≤ t) (hu_cap : u < capNodes)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hv : ValidNode l base t x.mem u) (hs : SortedNode l base t x.mem u)
    (hnonfull : numKeys base t x.mem u ≤ 2 * t - 2)
    (hcnt_mem : x.mem (base + 1) = cnt)
    (hcond_in : (Cond.lt rZero rActive).Holds x)
    (h12 : ExecWithin w loadAndScan x x₂ (8 * numKeys base t x.mem u + 12))
    (hb₂ : x₂.Bounded w) (hmem₂ : x₂.mem = x.mem)
    (hz₂ : x₂.regs rZero = 0) (ho₂ : x₂.regs rOne = 1)
    (hb₂_reg : x₂.regs rBase = base) (hd₂ : x₂.regs rDeg = t)
    (hst₂ : x₂.regs rStride = 6 * t)
    (hk₂ : x₂.regs rKey = k) (hv₂ : x₂.regs rVal = v) (hcur₂ : x₂.regs rCur = u)
    (hsrc₂ : x₂.regs rSrc = nodeAddr base t u + 2)
    (hnk₂ : x₂.regs rNumK = numKeys base t x.mem u)
    (hslot₂ : x₂.regs rSlot = slotCount base t x.mem u k (numKeys base t x.mem u))
    (hhit : slotCount base t x.mem u k (numKeys base t x.mem u) < numKeys base t x.mem u ∧
      keyAt base t x.mem u (slotCount base t x.mem u k (numKeys base t x.mem u)) = k) :
    ∃ y cnt',
      ExecWithin w insertLoop x y ((91 * t + 160) * (l + 1) + 2) ∧
      y.Bounded w ∧
      cnt ≤ cnt' ∧ cnt' ≤ cnt + l ∧
      y.mem base = x.mem base ∧
      y.mem (base + 1) = cnt' ∧
      y.regs rBase = base ∧
      y.regs rDeg = t ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      (∀ w_id, w_id ∉ readNodeSet l base t x.mem u ∪ Finset.Ico cnt cnt' →
        ∀ o < nodeStride t, y.mem (nodeAddr base t w_id + o) = x.mem (nodeAddr base t w_id + o)) ∧
      ValidNode l base t y.mem u ∧
      SortedNode l base t y.mem u ∧
      numKeys base t x.mem u ≤ numKeys base t y.mem u ∧
      readNodeSet l base t y.mem u ⊆ readNodeSet l base t x.mem u ∪ Finset.Ico cnt cnt' ∧
      (readTree l base t y.mem u).toList =
        Cslib.SortedAssoc.insert k v (readTree l base t x.mem u).toList := by
  set m := numKeys base t x.mem u
  set slot := slotCount base t x.mem u k m
  have hau_le := nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
  have hlt_m : slot < m := hhit.1
  have heq_k : keyAt base t x.mem u slot = k := hhit.2
  have hf_ks : Fits w (nodeAddr base t u + 2 + slot) := hfit.of_le (by omega)
  have hks_eq : x₂.mem (nodeAddr base t u + 2 + slot) = k := by rw [hmem₂]; exact heq_k
  let x₂' := (x₂.set rTmp1 (nodeAddr base t u + 2 + slot)).set rTmp2 k
  obtain ⟨y, hov, _, hymem, hmod_y, hz_y, hb_y_reg, hd_y, hact_y⟩ :=
    overwriteValCode_spec (x := x₂') ht hu_cap (by omega)
      ((hb₂.set hf_ks).set (hk₂ ▸ hb₂.1 rKey))
      hfit ho₂ hb₂_reg hd₂ hst₂ hcur₂ hslot₂ hv₂
  have h3 : ExecWithin w insertBranch x₂ y 15 := by
    unfold insertBranch
    apply WP.execWithin
    wram_exec [hnk₂, hsrc₂, hslot₂, hk₂, hlt_m, hks_eq, hf_ks]
    exact WP.of_execWithin hov ⟨by omega, rfl⟩
  have hstep : ExecWithin w insertStep x y (91 * t + 158) :=
    (h12.seq h3).mono (by omega)
  have hz_y0 : y.regs rZero = 0 := hz_y.trans hz₂
  have hexit : ExecWithin w insertLoop y y 2 :=
    ExecWithin.loop_exit (by simp only [Cond.holds_lt, hz_y0, hact_y, Nat.lt_irrefl,
      not_false_eq_true])
  have hiter_bound : (91 * t + 158) + 2 + 2 ≤ (91 * t + 160) * (l + 1) + 2 := by
    have hmul1 : 91 * t + 160 ≤ (91 * t + 160) * (l + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos l)
    omega
  have hymem' : y.mem = memOverwriteVal base t u slot v x.mem := by
    rw [hymem]; simp only [x₂', Data.set_mem, hmem₂]
  obtain ⟨hv', hs', hset', htr'⟩ := memOverwriteVal_spec ht hv hs hlt_m heq_k
  have hb_lo := base_lt_nodeAddr base t u (2 * t + 1 + slot)
  simp only [x₂', Data.set_mem, hmem₂] at hmod_y
  refine ⟨y, cnt, (hstep.loop_iter hcond_in hexit).mono hiter_bound,
    (hstep.loop_iter hcond_in hexit).bounded hbdd, le_rfl, Nat.le_add_right cnt l, ?_, ?_,
    hb_y_reg, hd_y, hmod_y, ?_, hymem' ▸ hv', hymem' ▸ hs', ?_, ?_, hymem' ▸ htr'⟩
  · rw [hymem']; dsimp only [memOverwriteVal]; rw [Function.update_of_ne (by omega)]
  · rw [hymem']; dsimp only [memOverwriteVal]; rw [Function.update_of_ne (by omega), hcnt_mem]
  · intro w_id hnot o ho_lt
    have hw_ne : w_id ≠ u := fun heq => hnot (by
      rw [heq]; exact Finset.mem_union_left _ (self_mem_readNodeSet l base t x.mem u))
    have hsep := nodeAddr_disjoint (base := base) (o₂ := (2 * t + 1) + slot) hw_ne ho_lt
      (by simp only [nodeStride]; omega)
    rw [← Nat.add_assoc] at hsep
    rw [hymem']; dsimp only [memOverwriteVal]
    exact Function.update_of_ne hsep _ _
  · rw [hymem']; dsimp only [numKeys, memOverwriteVal]
    have hst_eq : nodeStride t = 6 * t := rfl
    rw [Function.update_of_ne (by omega)]
    exact le_rfl
  · rw [hymem', hset']; exact Finset.subset_union_left

private theorem insertLoop_spec {l w base capNodes t u cnt k v : ℕ} {x : Data 20}
    (ht : 2 ≤ t)
    (hbdd : x.Bounded w)
    (hfit : Fits w (base + arenaWords t capNodes))
    (hv : ValidNode l base t x.mem u)
    (hs : SortedNode l base t x.mem u)
    (hnonfull : numKeys base t x.mem u ≤ 2 * t - 2)
    (hrange : readNodeSet l base t x.mem u ⊆ Finset.range cnt)
    (hcap : cnt + l ≤ capNodes)
    (hcnt_mem : x.mem (base + 1) = cnt)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hstride : x.regs rStride = 6 * t)
    (hkey : x.regs rKey = k) (hval : x.regs rVal = v)
    (hcur : x.regs rCur = u) (hcnt_reg : x.regs rCnt = cnt)
    (hact : x.regs rActive = 1) :
    ∃ y cnt',
      ExecWithin w insertLoop x y ((91 * t + 160) * (l + 1) + 2) ∧
      y.Bounded w ∧
      cnt ≤ cnt' ∧ cnt' ≤ cnt + l ∧
      y.mem base = x.mem base ∧
      y.mem (base + 1) = cnt' ∧
      y.regs rBase = base ∧
      y.regs rDeg = t ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      (∀ w_id, w_id ∉ readNodeSet l base t x.mem u ∪ Finset.Ico cnt cnt' →
        ∀ o < nodeStride t, y.mem (nodeAddr base t w_id + o) = x.mem (nodeAddr base t w_id + o)) ∧
      ValidNode l base t y.mem u ∧
      SortedNode l base t y.mem u ∧
      numKeys base t x.mem u ≤ numKeys base t y.mem u ∧
      readNodeSet l base t y.mem u ⊆ readNodeSet l base t x.mem u ∪ Finset.Ico cnt cnt' ∧
      (readTree l base t y.mem u).toList =
        Cslib.SortedAssoc.insert k v (readTree l base t x.mem u).toList := by
  induction l generalizing u cnt x with
  | zero =>
    have hu_lt_cnt : u < cnt :=
      Finset.mem_range.mp (hrange (self_mem_readNodeSet 0 base t x.mem u))
    have hu_cap : u < capNodes := by omega
    set m := numKeys base t x.mem u
    have hau_le := nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
    obtain ⟨x₂, h12, hb₂, hmem₂, hz₂, ho₂, hb₂_reg, hd₂, hst₂, hk₂, hcur₂, hsrc₂, hnk₂,
        hslot₂, hreg₂⟩ :=
      loadAndScan_spec ht hu_cap hv.numKeys_le hbdd hfit hz ho hbase hdeg hstride hkey hcur
    have hv₂ : x₂.regs rVal = v :=
      (hreg₂ rVal (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hval
    set slot := slotCount base t x.mem u k m
    have hsc := slotCount_spec (k := k) (fun _ _ => hs.keys_strict) m le_rfl
    have hslot_le : slot ≤ m := hsc.1
    have hcond_in : (Cond.lt rZero rActive).Holds x := by
      simp only [Cond.holds_lt, hz, hact, Nat.zero_lt_one]
    by_cases hhit : slot < m ∧ keyAt base t x.mem u slot = k
    · exact insertLoop_overwrite_spec ht hu_cap hbdd hfit hv hs hnonfull hcnt_mem hcond_in
        h12 hb₂ hmem₂ hz₂ ho₂ hb₂_reg hd₂ hst₂ hk₂ hv₂ hcur₂ hsrc₂ hnk₂ hslot₂ hhit
    · -- Shift-insert into leaf `u`:
      have hgt_all : ∀ i, slot ≤ i → i < m → k < keyAt base t x.mem u i := by
        intro i hge hi
        rcases eq_or_lt_of_le hge with rfl | hgt
        · have hle_s := hsc.2.2 slot le_rfl hi
          have hne_s : keyAt base t x.mem u slot ≠ k := fun heq => hhit ⟨hi, heq⟩
          omega
        · have hle_s := hsc.2.2 slot le_rfl (by omega)
          have hne_s : keyAt base t x.mem u slot ≠ k := fun heq => hhit ⟨by omega, heq⟩
          exact (show k < keyAt base t x.mem u slot by omega).trans (hs.keys_strict hgt hi)
      have hf_au1 : Fits w (nodeAddr base t u + 2 - 1) := hfit.of_le (by omega)
      have hf_au : Fits w (nodeAddr base t u) := hfit.of_le (by omega)
      have hsub2 : nodeAddr base t u + 2 - 1 - 1 = nodeAddr base t u := by omega
      have h1_ne_0 : (1 : ℕ) ≠ 0 := by omega
      -- Execute `insertDescendOrLeaf` on leaf `u`:
      have hdesc_leaf : ∀ z : Data 20,
          z.Bounded w → z.mem = x.mem → z.regs rZero = 0 → z.regs rOne = 1 →
          z.regs rBase = base → z.regs rDeg = t → z.regs rKey = k → z.regs rVal = v →
          z.regs rNumK = m → z.regs rSlot = slot → z.regs rSrc = nodeAddr base t u + 2 →
          ∃ y, ExecWithin w insertDescendOrLeaf z y (36 * t + 28) ∧
            y.mem = memInsertLeaf base t u m slot k v x.mem ∧
            Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
            y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rZero = 0 ∧ y.regs rActive = 0 := by
        intro z hbz hmz hzz hoz hbaz hdz hkz hvz hnkz hslz hsrcz
        have hlfz : z.mem (nodeAddr base t u) = 1 := by rw [hmz]; exact hv.leafFlag_eq
        let z' := ((z.set rTmp1 (nodeAddr base t u + 2 - 1)).set rTmp1
          (nodeAddr base t u)).set rTmp2 1
        obtain ⟨y, hli, _, hym, hmod_l, hby, hdy, hzy, hacty⟩ :=
          leafInsertCode_spec (x := z') ht hu_cap hnonfull hslot_le
            (((hbz.set hf_au1).set hf_au).set (hfit.of_le (by omega)))
            hfit hoz hbaz hdz hkz hvz hnkz hslz hsrcz
        have he_dl : ExecWithin w insertDescendOrLeaf z y (36 * t + 28) := by
          unfold insertDescendOrLeaf
          apply WP.execWithin
          wram_exec [hzz, hoz, hsrcz, hsub2, hlfz, h1_ne_0, hf_au1, hf_au]
          exact WP.of_execWithin hli ⟨by omega, rfl⟩
        simp only [z', Data.set_mem, Data.set_regs_of_ne (by decide : rZero ≠ rTmp2) _,
          Data.set_regs_of_ne (by decide : rZero ≠ rTmp1) _] at hym hmod_l hzy
        rw [hmz] at hym hmod_l
        exact ⟨y, he_dl, hym, hmod_l, hby, hdy, hzy.trans hzz, hacty⟩
      have hbranch : ∃ y, ExecWithin w insertBranch x₂ y (36 * t + 35) ∧
          y.mem = memInsertLeaf base t u m slot k v x.mem ∧
          Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
          y.regs rBase = base ∧ y.regs rDeg = t ∧ y.regs rZero = 0 ∧ y.regs rActive = 0 := by
        by_cases hlt_m : slot < m
        · have hne_k : keyAt base t x.mem u slot ≠ k := fun heq => hhit ⟨hlt_m, heq⟩
          have hf_ks : Fits w (nodeAddr base t u + 2 + slot) := hfit.of_le (by omega)
          have hks_eq : x₂.mem (nodeAddr base t u + 2 + slot) = keyAt base t x.mem u slot := by
            rw [hmem₂]; rfl
          let x₂' := (x₂.set rTmp1 (nodeAddr base t u + 2 + slot)).set rTmp2
            (keyAt base t x.mem u slot)
          obtain ⟨y, hdl, hym, hmod_l, hby, hdy, hzy, hacty⟩ :=
            hdesc_leaf x₂' ((hb₂.set hf_ks).set (hmem₂ ▸ hb₂.2 _)) hmem₂ hz₂ ho₂ hb₂_reg hd₂ hk₂ hv₂
              hnk₂ hslot₂ hsrc₂
          have he_br : ExecWithin w insertBranch x₂ y (36 * t + 35) := by
            unfold insertBranch
            apply WP.execWithin
            wram_exec [hnk₂, hsrc₂, hslot₂, hk₂, hlt_m, hks_eq, hne_k, hf_ks]
            exact WP.of_execWithin hdl ⟨by omega, rfl⟩
          exact ⟨y, he_br, hym, hmod_l, hby, hdy, hzy, hacty⟩
        · obtain ⟨y, hdl, hym, hmod_l, hby, hdy, hzy, hacty⟩ :=
            hdesc_leaf x₂ hb₂ hmem₂ hz₂ ho₂ hb₂_reg hd₂ hk₂ hv₂ hnk₂ hslot₂ hsrc₂
          have he_br : ExecWithin w insertBranch x₂ y (36 * t + 35) := by
            unfold insertBranch
            apply WP.execWithin
            wram_exec [hnk₂, hslot₂, hlt_m]
            exact WP.of_execWithin hdl ⟨by omega, rfl⟩
          exact ⟨y, he_br, hym, hmod_l, hby, hdy, hzy, hacty⟩
      obtain ⟨y, h3, hymem, hmod_y, hb_y, hd_y, hz_y, hact_y⟩ := hbranch
      have hstep : ExecWithin w insertStep x y (91 * t + 158) :=
        (h12.seq h3).mono (by omega)
      have hexit : ExecWithin w insertLoop y y 2 :=
        ExecWithin.loop_exit (by simp only [Cond.holds_lt, hz_y, hact_y, Nat.lt_irrefl,
          not_false_eq_true])
      obtain ⟨hv', hs', hnk', htr'⟩ := memInsertLeaf_spec ht hv hs hnonfull hslot_le hsc.2.1 hgt_all
      have hb_lo := base_lt_nodeAddr base t u 0
      refine ⟨y, cnt, (hstep.loop_iter hcond_in hexit).mono (by omega),
        (hstep.loop_iter hcond_in hexit).bounded hbdd, le_rfl, le_rfl, ?_, ?_,
        hb_y, hd_y, hmod_y, ?_, hymem ▸ hv', hymem ▸ hs', ?_, ?_, hymem ▸ htr'⟩
      · rw [hymem]; exact memInsertLeaf_outside ht hnonfull hslot_le x.mem base (by omega)
      · rw [hymem, memInsertLeaf_outside ht hnonfull hslot_le x.mem (base + 1) (by omega),
          hcnt_mem]
      · intro w_id hnot o ho_lt
        have hw_ne : w_id ≠ u := fun heq => hnot (by
          rw [heq]; exact Finset.mem_union_left _ (self_mem_readNodeSet 0 base t x.mem u))
        have hsep := nodeAddr_sep base t hw_ne
        rw [hymem]
        exact memInsertLeaf_outside ht hnonfull hslot_le x.mem _ (by omega)
      · rw [hymem, hnk']; omega
      · simp only [readNodeSet_zero]; exact Finset.subset_union_left
  | succ l ih =>
    have hu_lt_cnt : u < cnt :=
      Finset.mem_range.mp (hrange (self_mem_readNodeSet (l + 1) base t x.mem u))
    have hu_cap : u < capNodes := by omega
    set m := numKeys base t x.mem u
    have hau_le := nodeAddr_add_le_arena (base := base) hu_cap (o := 6 * t) le_rfl
    obtain ⟨x₂, h12, hb₂, hmem₂, hz₂, ho₂, hb₂_reg, hd₂, hst₂, hk₂, hcur₂, hsrc₂, hnk₂,
        hslot₂, hreg₂⟩ :=
      loadAndScan_spec ht hu_cap hv.numKeys_le hbdd hfit hz ho hbase hdeg hstride hkey hcur
    have hv₂ : x₂.regs rVal = v :=
      (hreg₂ rVal (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hval
    have hcnt₂ : x₂.regs rCnt = cnt :=
      (hreg₂ rCnt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hcnt_reg
    have hact₂ : x₂.regs rActive = 1 :=
      (hreg₂ rActive (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans hact
    set slot := slotCount base t x.mem u k m
    have hsc := slotCount_spec (k := k) (fun _ _ => hs.keys_strict) m le_rfl
    have hslot_le : slot ≤ m := hsc.1
    have hcond_in : (Cond.lt rZero rActive).Holds x := by
      simp only [Cond.holds_lt, hz, hact, Nat.zero_lt_one]
    have hmul_step : (91 * t + 160) * (l + 1 + 1) = (91 * t + 160) * (l + 1) + (91 * t + 160) :=
      Nat.mul_succ _ _
    by_cases hhit : slot < m ∧ keyAt base t x.mem u slot = k
    · exact insertLoop_overwrite_spec ht hu_cap hbdd hfit hv hs hnonfull hcnt_mem hcond_in
        h12 hb₂ hmem₂ hz₂ ho₂ hb₂_reg hd₂ hst₂ hk₂ hv₂ hcur₂ hsrc₂ hnk₂ hslot₂ hhit
    · -- Internal descent into `c = childAt u slot`:
      have hgt_all : ∀ i, slot ≤ i → i < m → k < keyAt base t x.mem u i := by
        intro i hge hi
        rcases eq_or_lt_of_le hge with rfl | hgt
        · have hle_s := hsc.2.2 slot le_rfl hi
          have hne_s : keyAt base t x.mem u slot ≠ k := fun heq => hhit ⟨hi, heq⟩
          omega
        · have hle_s := hsc.2.2 slot le_rfl (by omega)
          have hne_s : keyAt base t x.mem u slot ≠ k := fun heq => hhit ⟨by omega, heq⟩
          exact (show k < keyAt base t x.mem u slot by omega).trans (hs.keys_strict hgt hi)
      obtain ⟨c, hc_def⟩ : ∃ c, childAt base t x.mem u slot = c := ⟨_, rfl⟩
      have hslot_lt1 : slot < m + 1 := by omega
      have hv_c : ValidNode l base t x.mem c := hc_def ▸ hv.child_valid hslot_lt1
      have hs_c : SortedNode l base t x.mem c := hc_def ▸ hs.child_sorted hslot_lt1
      have hrange_c : readNodeSet l base t x.mem c ⊆ Finset.range cnt :=
        (hc_def ▸ child_subset_readNodeSet l base t x.mem u slot hslot_lt1).trans hrange
      have hc_lt_cnt : c < cnt :=
        Finset.mem_range.mp (hrange_c (self_mem_readNodeSet l base t x.mem c))
      have hc_cap : c < capNodes := by omega
      have hac_le := nodeAddr_add_le_arena (base := base) hc_cap (o := 6 * t) le_rfl
      have huc : u ≠ c := fun heq =>
        (hc_def ▸ hv.not_mem_child_readNodeSet hslot_lt1)
          (Eq.ndrec (motive := fun w_id => w_id ∈ readNodeSet l base t x.mem c)
            (self_mem_readNodeSet l base t x.mem c) heq.symm)
      -- Lift `insertDescendOrLeaf_int_spec` through `insertBranch` from `x₂`:
      have hbranch : ∃ x₃, ExecWithin w insertBranch x₂ x₃ (75 * t + 162) ∧
          x₃.Bounded w ∧
          Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem x₃.mem ∧
          x₃.regs rZero = 0 ∧ x₃.regs rOne = 1 ∧
          x₃.regs rBase = base ∧ x₃.regs rDeg = t ∧ x₃.regs rStride = 6 * t ∧
          x₃.regs rKey = k ∧ x₃.regs rVal = v ∧
          (if numKeys base t x.mem c = 2 * t - 1 then
            let mem₁ := memSplitChild base t u m slot c cnt x.mem
            x₃.regs rCnt = cnt + 1 ∧
            (if keyAt base t mem₁ u slot = k then
              x₃.mem = memOverwriteVal base t u slot v mem₁ ∧ x₃.regs rActive = 0
            else if k < keyAt base t mem₁ u slot then
              x₃.mem = mem₁ ∧ x₃.regs rCur = c ∧ x₃.regs rActive = 1
            else
              x₃.mem = mem₁ ∧ x₃.regs rCur = cnt ∧ x₃.regs rActive = 1)
          else
            x₃.mem = x.mem ∧ x₃.regs rCur = c ∧ x₃.regs rCnt = cnt ∧ x₃.regs rActive = 1) := by
        by_cases hlt_m : slot < m
        · have hne_k : keyAt base t x.mem u slot ≠ k := fun heq => hhit ⟨hlt_m, heq⟩
          have hf_ks : Fits w (nodeAddr base t u + 2 + slot) := hfit.of_le (by omega)
          have hks_eq : x₂.mem (nodeAddr base t u + 2 + slot) = keyAt base t x.mem u slot := by
            rw [hmem₂]; rfl
          let x₂' := (x₂.set rTmp1 (nodeAddr base t u + 2 + slot)).set rTmp2
            (keyAt base t x.mem u slot)
          obtain ⟨x₃, hdl, hbx₃, hmod₃, hz₃, ho₃, hb₃, hd₃, hst₃, hk₃, hv₃, hbr₃⟩ :=
            insertDescendOrLeaf_int_spec (z := x₂') ht hu_lt_cnt hc_lt_cnt huc (by omega) hnonfull
              hslot_le hv.leafFlag_eq hc_def hfit ((hb₂.set hf_ks).set (hmem₂ ▸ hb₂.2 _)) hmem₂ hz₂
              ho₂ hb₂_reg hd₂ hst₂ hk₂ hv₂ hcur₂ hcnt₂ hnk₂ hslot₂ hsrc₂ hact₂
          have he_br : ExecWithin w insertBranch x₂ x₃ (75 * t + 162) := by
            unfold insertBranch
            apply WP.execWithin
            wram_exec [hnk₂, hsrc₂, hslot₂, hk₂, hlt_m, hks_eq, hne_k, hf_ks]
            exact WP.of_execWithin hdl ⟨by omega, rfl⟩
          exact ⟨x₃, he_br, hbx₃, hmod₃, hz₃, ho₃, hb₃, hd₃, hst₃, hk₃, hv₃, hbr₃⟩
        · obtain ⟨x₃, hdl, hbx₃, hmod₃, hz₃, ho₃, hb₃, hd₃, hst₃, hk₃, hv₃, hbr₃⟩ :=
            insertDescendOrLeaf_int_spec (z := x₂) ht hu_lt_cnt hc_lt_cnt huc (by omega) hnonfull
              hslot_le hv.leafFlag_eq hc_def hfit hb₂ hmem₂ hz₂ ho₂ hb₂_reg hd₂ hst₂ hk₂ hv₂ hcur₂
              hcnt₂ hnk₂ hslot₂ hsrc₂ hact₂
          have he_br : ExecWithin w insertBranch x₂ x₃ (75 * t + 162) := by
            unfold insertBranch
            apply WP.execWithin
            wram_exec [hnk₂, hslot₂, hlt_m]
            exact WP.of_execWithin hdl ⟨by omega, rfl⟩
          exact ⟨x₃, he_br, hbx₃, hmod₃, hz₃, ho₃, hb₃, hd₃, hst₃, hk₃, hv₃, hbr₃⟩
      obtain ⟨x₃, h3, hbx₃, hmod₃, hz₃, ho₃, hb₃, hd₃, hst₃, hk₃, hv₃, hbr₃⟩ := hbranch
      have hstep : ExecWithin w insertStep x x₃ (91 * t + 158) :=
        (h12.seq h3).mono (by omega)
      -- Now split on whether `c` was full (`numKeys c = 2 * t - 1`) or non-full:
      by_cases hfull_c : numKeys base t x.mem c = 2 * t - 1
      · simp only [hfull_c, ↓reduceIte] at hbr₃
        obtain ⟨hcnt₃, hbr₃⟩ := hbr₃
        obtain ⟨mem₁, hmem₁_def⟩ :
            ∃ mem₁, memSplitChild base t u m slot c cnt x.mem = mem₁ := ⟨_, rfl⟩
        rw [hmem₁_def] at hbr₃
        have hcnt_fresh : cnt ∉ readNodeSet (l + 1) base t x.mem u := fun hin => by
          have := Finset.mem_range.mp (hrange hin); omega
        have hmsc := memSplitChild_spec ht hv hs hnonfull hslot_le
          (hc_def.symm ▸ hfull_c) hcnt_fresh
        dsimp only at hmsc
        change (let m' := m; let c' := childAt base t x.mem u slot; _) at hmsc
        rw [hc_def, hmem₁_def] at hmsc
        obtain ⟨hm1_b1, hm1_b0, hv_u1, hs_u1, hnk_u1, hk_s1, hv_s1, hc_s1, hc_s11, hnk_c1, hnk_z1,
            hsub_u1, htr_u1⟩ := hmsc
        have hrange_u1 : readNodeSet (l + 1) base t mem₁ u ⊆ Finset.range (cnt + 1) := by
          intro w_id hwin
          rw [Finset.mem_range]
          rcases Finset.mem_insert.mp (hsub_u1 hwin) with rfl | hold
          · omega
          · have := Finset.mem_range.mp (hrange hold); omega
        -- Node framing of `mem₁` vs `x.mem`: `mem₁` only touches `u`, `c`, `cnt`:
        have hframe_mem₁ : ∀ w_id, w_id ≠ u → w_id ≠ c → w_id ≠ cnt →
            ∀ o < nodeStride t, mem₁ (nodeAddr base t w_id + o) =
              x.mem (nodeAddr base t w_id + o) := by
          intro w_id hnu hnc hnz o ho_lt
          have hb_lo := base_lt_nodeAddr base t w_id o
          have hsu := nodeAddr_sep base t hnu
          have hsc_d := nodeAddr_sep base t hnc
          have hsz := nodeAddr_sep base t hnz
          rw [← hmem₁_def]
          exact memSplitChild_outside ht hnonfull hslot_le x.mem _ (by omega) (by omega)
            (by omega) (by omega)
        have hu_in_old : u ∈ readNodeSet (l + 1) base t x.mem u :=
          self_mem_readNodeSet (l + 1) base t x.mem u
        have hc_in_old : c ∈ readNodeSet (l + 1) base t x.mem u :=
          hc_def ▸ child_subset_readNodeSet l base t x.mem u slot hslot_lt1
            (self_mem_readNodeSet l base t x.mem (childAt base t x.mem u slot))
        by_cases heq_med : keyAt base t mem₁ u slot = k
        · -- Subcase 3b(i): `k = k_med`! Overwritten immediately, loop exits!
          simp only [heq_med, ↓reduceIte] at hbr₃
          obtain ⟨hmem₃_eq, hact₃⟩ := hbr₃
          have hexit : ExecWithin w insertLoop x₃ x₃ 2 :=
            ExecWithin.loop_exit (by simp only [Cond.holds_lt, hz₃, hact₃, Nat.lt_irrefl,
              not_false_eq_true])
          have hslot_lt_u1 : slot < numKeys base t mem₁ u := by rw [hnk_u1]; omega
          obtain ⟨hv_u2, hs_u2, hset_u2, htr_u2⟩ :=
            memOverwriteVal_spec ht hv_u1 hs_u1 hslot_lt_u1 heq_med
          have hb_lo := base_lt_nodeAddr base t u (2 * t + 1 + slot)
          refine ⟨x₃, cnt + 1, (hstep.loop_iter hcond_in hexit).mono (by omega),
            (hstep.loop_iter hcond_in hexit).bounded hbdd, by omega, by omega, ?_, ?_,
            hb₃, hd₃, hmod₃, ?_, hmem₃_eq ▸ hv_u2, hmem₃_eq ▸ hs_u2, ?_, ?_, ?_⟩
          · rw [hmem₃_eq]; dsimp only [memOverwriteVal]
            rw [Function.update_of_ne (by omega), hm1_b0]
          · rw [hmem₃_eq]; dsimp only [memOverwriteVal]
            rw [Function.update_of_ne (by omega), hm1_b1]
          · intro w_id hnot o ho_lt
            simp only [Finset.mem_union, Finset.mem_Ico, not_or] at hnot
            have hnu : w_id ≠ u := fun heq => hnot.1 (heq ▸ hu_in_old)
            have hnc : w_id ≠ c := fun heq => hnot.1 (heq ▸ hc_in_old)
            have hnz : w_id ≠ cnt := by omega
            have hsep := nodeAddr_disjoint (base := base) (o₂ := (2 * t + 1) + slot) hnu ho_lt
              (by simp only [nodeStride]; omega)
            rw [← Nat.add_assoc] at hsep
            rw [hmem₃_eq]; dsimp only [memOverwriteVal]
            rw [Function.update_of_ne hsep]
            exact hframe_mem₁ w_id hnu hnc hnz o ho_lt
          · rw [hmem₃_eq]; dsimp only [numKeys, memOverwriteVal]
            have hst_eq : nodeStride t = 6 * t := rfl
            rw [Function.update_of_ne (by omega)]
            change m ≤ numKeys base t mem₁ u
            rw [hnk_u1]; omega
          · rw [hmem₃_eq, hset_u2]
            intro w_id hwin
            rcases Finset.mem_insert.mp (hsub_u1 hwin) with rfl | hold
            · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
            · exact Finset.mem_union_left _ hold
          · rw [hmem₃_eq, htr_u2, htr_u1]
        · by_cases hlt_med : k < keyAt base t mem₁ u slot
          · -- Subcase 3b(ii): `k < k_med`, descend into left half `c = childAt mem₁ u slot`!
            simp only [heq_med, hlt_med, ↓reduceIte] at hbr₃
            obtain ⟨hmem₃_eq, hcur₃, hact₃⟩ := hbr₃
            have hslot_le_u1 : slot ≤ numKeys base t mem₁ u := by rw [hnk_u1]; omega
            have hslot_lt1_u1 : slot < numKeys base t mem₁ u + 1 := by rw [hnk_u1]; omega
            have hv_c_m1 : ValidNode l base t x₃.mem c := by
              rw [hmem₃_eq, ← hc_s1]; exact hv_u1.child_valid hslot_lt1_u1
            have hs_c_m1 : SortedNode l base t x₃.mem c := by
              rw [hmem₃_eq, ← hc_s1]; exact hs_u1.child_sorted hslot_lt1_u1
            have hnf_c_m1 : numKeys base t x₃.mem c ≤ 2 * t - 2 := by
              rw [hmem₃_eq, hnk_c1]; omega
            have hrange_c_m1 : readNodeSet l base t x₃.mem c ⊆ Finset.range (cnt + 1) := by
              rw [hmem₃_eq, ← hc_s1]
              exact (child_subset_readNodeSet l base t mem₁ u slot hslot_lt1_u1).trans hrange_u1
            obtain ⟨y, cnt', hy_rec, hby, hcnt1_le, hcnt'_hi, hmb0, hmb1, hby_reg, hdy_reg,
                hmod_rec, hfr_rec, hv_c', hs_c', hnk_c_le, hsub_c', htr_c'⟩ :=
              ih hbx₃ hv_c_m1 hs_c_m1 hnf_c_m1 hrange_c_m1 (by omega) (hmem₃_eq ▸ hm1_b1)
                hz₃ ho₃ hb₃ hd₃ hst₃ hk₃ hv₃ hcur₃ hcnt₃ hact₃
            rw [hmem₃_eq] at hfr_rec hnk_c_le hsub_c' htr_c' hmb0
            -- Slot key bounds on `mem₁` at `slot`:
            have hlt_u1 : ∀ i < slot, keyAt base t mem₁ u i < k := by
              intro i hi
              rw [← hmem₁_def,
                keyAt_memSplitChild_lt ht hnonfull hslot_le huc (by omega) hi]
              exact hsc.2.1 i hi
            have hgt_u1 : ∀ i, slot ≤ i → i < numKeys base t mem₁ u →
                k < keyAt base t mem₁ u i := by
              intro i hge hi
              rcases eq_or_lt_of_le hge with rfl | hgt
              · exact hlt_med
              · exact hlt_med.trans (hs_u1.keys_strict hgt hi)
            obtain ⟨hv_u', hs_u', hnk_u', hsub_u', htr_u'⟩ :=
              childInsert_spec (cnt := cnt + 1) (cnt' := cnt') ht hv_u1 hs_u1 hslot_le_u1
                hlt_u1 hgt_u1 hrange_u1
                (by rwa [hc_s1])
                (by rwa [hc_s1])
                (by rwa [hc_s1])
                (by rw [hc_s1]; omega)
                (by rwa [hc_s1])
                (by rwa [hc_s1])
            refine ⟨y, cnt', (hstep.loop_iter hcond_in hy_rec).mono (by omega), hby,
              by omega, by omega, hmb0.trans hm1_b0, hmb1, hby_reg, hdy_reg,
              by simpa only [Finset.union_idempotent] using hmod₃.trans hmod_rec, ?_, hv_u', hs_u',
              by rw [hnk_u', hnk_u1]; omega, ?_, by rw [htr_u', htr_u1]⟩
            · intro w_id hnot o ho_lt
              have hnot_rec : w_id ∉ readNodeSet l base t mem₁ c ∪ Finset.Ico (cnt + 1) cnt' := by
                intro hin
                apply hnot
                rcases Finset.mem_union.mp hin with hinc | hico
                · have hin_u1 : w_id ∈ readNodeSet (l + 1) base t mem₁ u := by
                    rw [← hc_s1] at hinc
                    exact child_subset_readNodeSet l base t mem₁ u slot hslot_lt1_u1 hinc
                  rcases Finset.mem_insert.mp (hsub_u1 hin_u1) with rfl | hold
                  · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
                  · exact Finset.mem_union_left _ hold
                · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr
                    ⟨by have := (Finset.mem_Ico.mp hico).1; omega, (Finset.mem_Ico.mp hico).2⟩)
              rw [hfr_rec w_id hnot_rec o ho_lt]
              simp only [Finset.mem_union, Finset.mem_Ico, not_or] at hnot
              exact hframe_mem₁ w_id (fun h => hnot.1 (h ▸ hu_in_old))
                (fun h => hnot.1 (h ▸ hc_in_old)) (by omega) o ho_lt
            · intro w_id hwin
              rcases Finset.mem_union.mp (hsub_u' hwin) with hin_u1 | hico
              · rcases Finset.mem_insert.mp (hsub_u1 hin_u1) with rfl | hold
                · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
                · exact Finset.mem_union_left _ hold
              · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr
                  ⟨by have := (Finset.mem_Ico.mp hico).1; omega, (Finset.mem_Ico.mp hico).2⟩)
          · -- Subcase 3b(iii): `k_med < k`, descend into right half `cnt`:
            simp only [heq_med, hlt_med, ↓reduceIte] at hbr₃
            obtain ⟨hmem₃_eq, hcur₃, hact₃⟩ := hbr₃
            have hmed_lt_k : keyAt base t mem₁ u slot < k := by omega
            have hslot1_le_u1 : slot + 1 ≤ numKeys base t mem₁ u := by rw [hnk_u1]; omega
            have hslot1_lt1_u1 : slot + 1 < numKeys base t mem₁ u + 1 := by rw [hnk_u1]; omega
            have hv_z_m1 : ValidNode l base t x₃.mem cnt := by
              rw [hmem₃_eq, ← hc_s11]; exact hv_u1.child_valid hslot1_lt1_u1
            have hs_z_m1 : SortedNode l base t x₃.mem cnt := by
              rw [hmem₃_eq, ← hc_s11]; exact hs_u1.child_sorted hslot1_lt1_u1
            have hnf_z_m1 : numKeys base t x₃.mem cnt ≤ 2 * t - 2 := by
              rw [hmem₃_eq, hnk_z1]; omega
            have hrange_z_m1 : readNodeSet l base t x₃.mem cnt ⊆ Finset.range (cnt + 1) := by
              rw [hmem₃_eq]; nth_rw 1 [← hc_s11]
              exact (child_subset_readNodeSet l base t mem₁ u (slot + 1) hslot1_lt1_u1).trans
                hrange_u1
            obtain ⟨y, cnt', hy_rec, hby, hcnt1_le, hcnt'_hi, hmb0, hmb1, hby_reg, hdy_reg,
                hmod_rec, hfr_rec, hv_z', hs_z', hnk_z_le, hsub_z', htr_z'⟩ :=
              ih hbx₃ hv_z_m1 hs_z_m1 hnf_z_m1 hrange_z_m1 (by omega) (hmem₃_eq ▸ hm1_b1)
                hz₃ ho₃ hb₃ hd₃ hst₃ hk₃ hv₃ hcur₃ hcnt₃ hact₃
            rw [hmem₃_eq] at hfr_rec hnk_z_le hsub_z' htr_z' hmb0
            have hlt_u1 : ∀ i < slot + 1, keyAt base t mem₁ u i < k := by
              intro i hi
              rcases eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | hlt_s
              · exact hmed_lt_k
              · exact (hs_u1.keys_strict hlt_s (by rw [hnk_u1]; omega)).trans hmed_lt_k
            have hgt_u1 : ∀ i, slot + 1 ≤ i → i < numKeys base t mem₁ u →
                k < keyAt base t mem₁ u i := by
              intro i hge hi
              rw [hnk_u1] at hi
              rw [← hmem₁_def,
                keyAt_memSplitChild_gt ht hnonfull hslot_le huc (by omega) hge hi]
              exact hgt_all (i - 1) (by omega) (by omega)
            obtain ⟨hv_u', hs_u', hnk_u', hsub_u', htr_u'⟩ :=
              childInsert_spec (slot := slot + 1) (cnt := cnt + 1) (cnt' := cnt') ht hv_u1 hs_u1
                hslot1_le_u1 hlt_u1 hgt_u1 hrange_u1
                (by rwa [hc_s11])
                (by rwa [hc_s11])
                (by rwa [hc_s11])
                (by rw [hc_s11]; omega)
                (by rwa [hc_s11])
                (by rwa [hc_s11])
            refine ⟨y, cnt', (hstep.loop_iter hcond_in hy_rec).mono (by omega), hby,
              by omega, by omega, hmb0.trans hm1_b0, hmb1, hby_reg, hdy_reg,
              by simpa only [Finset.union_idempotent] using hmod₃.trans hmod_rec, ?_, hv_u', hs_u',
              by rw [hnk_u', hnk_u1]; omega, ?_, by rw [htr_u', htr_u1]⟩
            · intro w_id hnot o ho_lt
              have hnot_rec : w_id ∉ readNodeSet l base t mem₁ cnt ∪ Finset.Ico (cnt + 1) cnt' := by
                intro hin
                apply hnot
                rcases Finset.mem_union.mp hin with hinz | hico
                · have hin_u1 : w_id ∈ readNodeSet (l + 1) base t mem₁ u := by
                    rw [← hc_s11] at hinz
                    exact child_subset_readNodeSet l base t mem₁ u (slot + 1) hslot1_lt1_u1 hinz
                  rcases Finset.mem_insert.mp (hsub_u1 hin_u1) with rfl | hold
                  · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
                  · exact Finset.mem_union_left _ hold
                · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr
                    ⟨by have := (Finset.mem_Ico.mp hico).1; omega, (Finset.mem_Ico.mp hico).2⟩)
              rw [hfr_rec w_id hnot_rec o ho_lt]
              simp only [Finset.mem_union, Finset.mem_Ico, not_or] at hnot
              exact hframe_mem₁ w_id (fun h => hnot.1 (h ▸ hu_in_old))
                (fun h => hnot.1 (h ▸ hc_in_old)) (by omega) o ho_lt
            · intro w_id hwin
              rcases Finset.mem_union.mp (hsub_u' hwin) with hin_u1 | hico
              · rcases Finset.mem_insert.mp (hsub_u1 hin_u1) with rfl | hold
                · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
                · exact Finset.mem_union_left _ hold
              · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr
                  ⟨by have := (Finset.mem_Ico.mp hico).1; omega, (Finset.mem_Ico.mp hico).2⟩)
      · -- Subcase 3a: child `c` is already non-full (`numKeys c ≤ 2 * t - 2`)!
        simp only [hfull_c, ↓reduceIte] at hbr₃
        obtain ⟨hmem₃_eq, hcur₃, hcnt₃, hact₃⟩ := hbr₃
        have hnf_c : numKeys base t x₃.mem c ≤ 2 * t - 2 := by
          rw [hmem₃_eq]
          have := hv_c.numKeys_le
          omega
        obtain ⟨y, cnt', hy_rec, hby, hcnt_le, hcnt'_hi, hmb0, hmb1, hby_reg, hdy_reg,
            hmod_rec, hfr_rec, hv_c', hs_c', hnk_c_le, hsub_c', htr_c'⟩ :=
          ih hbx₃ (hmem₃_eq ▸ hv_c) (hmem₃_eq ▸ hs_c) hnf_c (hmem₃_eq ▸ hrange_c) (by omega)
            (hmem₃_eq ▸ hcnt_mem) hz₃ ho₃ hb₃ hd₃ hst₃ hk₃ hv₃ hcur₃ hcnt₃ hact₃
        rw [hmem₃_eq] at hmb0 hfr_rec hnk_c_le hsub_c' htr_c'
        have hnk_c_ge : t - 1 ≤ numKeys base t y.mem c :=
          le_trans (hc_def ▸ hv.child_numKeys_ge hslot_lt1) hnk_c_le
        obtain ⟨hv_u', hs_u', hnk_u', hsub_u', htr_u'⟩ :=
          childInsert_spec (cnt := cnt) (cnt' := cnt') ht hv hs hslot_le hsc.2.1 hgt_all hrange
            (hc_def.symm ▸ hfr_rec) (hc_def.symm ▸ hv_c') (hc_def.symm ▸ hs_c')
            (hc_def.symm ▸ hnk_c_ge) (hc_def.symm ▸ hsub_c') (hc_def.symm ▸ htr_c')
        refine ⟨y, cnt', (hstep.loop_iter hcond_in hy_rec).mono (by omega), hby,
          hcnt_le, by omega, hmb0, hmb1, hby_reg, hdy_reg,
          by simpa only [Finset.union_idempotent] using hmod₃.trans hmod_rec, ?_,
          hv_u', hs_u', by rw [hnk_u'], hsub_u', htr_u'⟩
        intro w_id hnot o ho_lt
        apply hfr_rec w_id _ o ho_lt
        intro hin
        apply hnot
        rcases Finset.mem_union.mp hin with hinc | hico
        · rw [← hc_def] at hinc
          exact Finset.mem_union_left _ (child_subset_readNodeSet l base t x.mem u slot hslot_lt1
            hinc)
        · exact Finset.mem_union_right _ hico

private theorem initSingleCode_spec {w base capNodes t k v : ℕ} {x : Data 20}
    (ht : 2 ≤ t) (hcap : 1 ≤ capNodes)
    (hbdd : x.Bounded w) (hfit : Fits w (base + arenaWords t capNodes))
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1)
    (hbase : x.regs rBase = base) (hdeg : x.regs rDeg = t)
    (hkey : x.regs rKey = k) (hval : x.regs rVal = v) :
    ∃ y, ExecWithin w initSingleCode x y 14 ∧
      y.Bounded w ∧
      y.mem = memInitSingle base t k v x.mem ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem ∧
      y.regs rBase = base ∧
      y.regs rDeg = t := by
  obtain ⟨a0, ha0_def⟩ : ∃ a0, nodeAddr base t 0 = a0 := ⟨_, rfl⟩
  have ha0_eq : base + 1 + 1 = a0 := by rw [← ha0_def]; simp only [nodeAddr]; omega
  have ha0_le : a0 + 6 * t ≤ base + arenaWords t capNodes :=
    ha0_def ▸ nodeAddr_add_le_arena (base := base) (u := 0) (by omega : 0 < capNodes)
      (o := 6 * t) le_rfl
  have h2t1_eq : a0 + t + t + 1 = a0 + (2 * t + 1) := by omega
  have ha02_eq : a0 + 1 + 1 = a0 + 2 := by omega
  have hf_b1 : Fits w (base + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_b11 : Fits w (base + 1 + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_a0 : Fits w a0 := hfit.of_le (by omega)
  have hf_a01 : Fits w (a0 + 1) := hfit.of_le (by omega)
  have hf_a011 : Fits w (a0 + 1 + 1) := hfit.of_le (by omega)
  have hf_a02 : Fits w (a0 + 2) := hfit.of_le (by omega)
  have hf_a0t : Fits w (a0 + t) := hfit.of_le (by omega)
  have hf_a02t : Fits w (a0 + t + t) := hfit.of_le (by omega)
  have hf_a02t10 : Fits w (a0 + t + t + 1) := hfit.of_le (by omega)
  have hf_a02t1 : Fits w (a0 + (2 * t + 1)) := hfit.of_le (by omega)
  obtain ⟨y, he, hymem, hb_y, hd_y⟩ :
      ∃ y, ExecWithin w initSingleCode x y 14 ∧
        y.mem = memInitSingle base t k v x.mem ∧
        y.regs rBase = base ∧ y.regs rDeg = t := by
    unfold initSingleCode
    apply WP.exists_execWithin
    wram_exec [hz, ho, hbase, hdeg, hkey, hval, ha0_eq, h2t1_eq, ha02_eq,
      hf_b1, hf_b11, hf_a0, hf_a01, hf_a011, hf_a02, hf_a0t, hf_a02t, hf_a02t10, hf_a02t1]
    wram_simp [hbase, hdeg]
    simp only [memInitSingle, ha0_def]
  have hmod : Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
    intro addr hnot
    rw [hymem]
    dsimp only [memInitSingle]
    rw [ha0_def]
    have hb_lo : base + 1 < a0 := ha0_def ▸ base_lt_nodeAddr base t 0 0
    repeat rw [Function.update_of_ne (by
      intro heq; apply hnot
      simp only [Block.mem_footprint, Block.Owns] at heq ha0_le ⊢
      omega)]
  exact ⟨y, he, he.bounded hbdd, hymem, hmod, hb_y, hd_y⟩

/-- `insertCode` inserts `(k, v)` into `tr` in at most
`(91 * t + 160) * (tr.height + 1) + (21 * t + 120)` standard Word-RAM instructions, preserving
`Rep` (`BTree.IsWF t tr'`), realizing `Cslib.SortedAssoc.insert k v tr.toList`, allocating at most
`tr.height + 2` arena nodes, and modifying only `[base, base + arenaWords t capNodes)`. -/
theorem insertCode_spec {w base capNodes t k v : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x)
    (hkey : x.regs rKey = k)
    (hval : x.regs rVal = v)
    (hcap : allocCount base x + tr.height + 2 ≤ capNodes) :
    ∃ y tr',
      ExecWithin w insertCode x y ((91 * t + 160) * (tr.height + 1) + (21 * t + 120)) ∧
      Rep base capNodes t w tr' y ∧
      tr'.toList = Cslib.SortedAssoc.insert k v tr.toList ∧
      allocCount base y ≤ allocCount base x + tr.height + 2 ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
  dsimp only [allocCount] at hcap ⊢
  have ht := hr.two_le
  have hfit := hr.fits_arena
  have hf0 : Fits w 0 := hfit.of_le (Nat.zero_le _)
  have hf1 : Fits w 1 := hfit.of_le (by simp only [arenaWords]; omega)
  have hf_b1 : Fits w (base + 1) := hfit.of_le (by simp only [arenaWords]; omega)
  rcases hr.tree_spec with ⟨hcnt0, rfl⟩ | ⟨hcnt_pos, l, rfl, hv, hs, hrange⟩
  · -- Empty tree (`cnt = 0`, `tr = .leaf`): `initSingleCode` creates a 1-key leaf root!
    let x₀ := (((x.set rZero 0).set rOne 1).set rTmp1 (base + 1)).set rCnt 0
    obtain ⟨y, his, hby, hymem, hmod, hb_y, hd_y⟩ :=
      initSingleCode_spec (x := x₀) (k := k) (v := v) ht (by omega)
        ((((hr.bounded.set hf0).set hf1).set hf_b1).set hf0) hfit rfl rfl
        (by dsimp only [x₀]; wram_simp; exact hr.base_eq)
        (by dsimp only [x₀]; wram_simp; exact hr.deg_eq)
        (by dsimp only [x₀]; wram_simp; exact hkey)
        (by dsimp only [x₀]; wram_simp; exact hval)
    have he : ExecWithin w insertCode x y ((91 * t + 160) * ((.leaf : BTree ℕ ℕ).height + 1) +
        (21 * t + 120)) := by
      unfold insertCode
      apply WP.execWithin
      wram_exec [hr.base_eq, hcnt0, hf0, hf1, hf_b1]
      exact WP.of_execWithin his ⟨by omega, rfl⟩
    simp only [x₀, Data.set_mem] at hymem hmod
    obtain ⟨hb0_s, hb1_s, hv_s, hs_s, htl_s, hset_s⟩ := memInitSingle_spec (base := base)
      (k := k) (v := v) ht x.mem
    have hrep : Rep base capNodes t w (readTree 0 base t y.mem 0) y := by
      refine ⟨hby, ht, hb_y, hd_y, hfit, ?_, Or.inr ⟨?_, 0, ?_, ?_, ?_, ?_⟩⟩
      · rw [hymem, hb1_s]; omega
      · rw [hymem, hb1_s]; omega
      · rw [hymem, hb0_s]
      · rw [hymem, hb0_s]; exact hv_s
      · rw [hymem, hb0_s]; exact hs_s
      · rw [hymem, hb0_s, hb1_s, hset_s]
        intro w_id hw; simp only [Finset.mem_singleton] at hw; subst hw; simp
    refine ⟨y, readTree 0 base t y.mem 0, he, hrep, ?_, ?_, hmod⟩
    · rw [hymem, htl_s]; rfl
    · rw [hymem, hb1_s]; omega
  · -- Non-empty tree (`0 < cnt`, `tr = readTree l base t x.mem oldRoot`, `tr.height = l + 1`):
    obtain ⟨cnt, hcnt_def⟩ : ∃ cnt, x.mem (base + 1) = cnt := ⟨_, rfl⟩
    obtain ⟨oldRoot, holdRoot_def⟩ : ∃ oldRoot, x.mem base = oldRoot := ⟨_, rfl⟩
    rw [hcnt_def] at hcnt_pos hrange hcap
    rw [holdRoot_def] at hv hs hrange hcap ⊢
    have hh_eq : (readTree l base t x.mem oldRoot).height = l + 1 := hv.balanced_and_height.2
    have hcnt_ne : cnt ≠ 0 := by omega
    have hr_lt_cnt : oldRoot < cnt :=
      Finset.mem_range.mp (hrange (self_mem_readNodeSet l base t x.mem oldRoot))
    have hcap1 : 1 ≤ capNodes := by omega
    have hst_le := stride_le_arena (base := base) (t := t) hcap1
    have har_old := nodeAddr_add_le_arena (base := base) (u := oldRoot)
      (by omega : oldRoot < capNodes) (o := 6 * t) le_rfl
    have hnk_old_eq : x.mem (nodeAddr base t oldRoot + 1) = numKeys base t x.mem oldRoot := rfl
    have hf_2t : Fits w (t + t) := hfit.of_le (by omega)
    have hf_4t : Fits w ((t + t) + (t + t)) := hfit.of_le (by omega)
    have hf_6t : Fits w (6 * t) := hfit.of_le hst_le
    have hf_rmul : Fits w (oldRoot * (6 * t)) := hfit.of_le (by
      simp only [nodeAddr, nodeStride] at har_old; omega)
    have hf_rb0 : Fits w (base + oldRoot * (6 * t)) := hfit.of_le (by
      simp only [nodeAddr, nodeStride] at har_old; omega)
    have hf_rb1 : Fits w (base + oldRoot * (6 * t) + 1) := hfit.of_le (by
      simp only [nodeAddr, nodeStride] at har_old; omega)
    have hf_rb2 : Fits w (base + oldRoot * (6 * t) + 1 + 1) := hfit.of_le (by
      simp only [nodeAddr, nodeStride] at har_old; omega)
    have hf_rb3 : Fits w (base + oldRoot * (6 * t) + 1 + 1 + 1) := hfit.of_le (by
      simp only [nodeAddr, nodeStride] at har_old; omega)
    have hf_ar1 : Fits w (nodeAddr base t oldRoot + 1) := hfit.of_le (by omega)
    have hf_2tm10 : Fits w (t + t - 1) := hfit.of_le (by omega)
    have hf_2tm1 : Fits w (2 * t - 1) := hfit.of_le (by omega)
    have h6t : (t + t) + ((t + t) + (t + t)) = 6 * t := by omega
    have hna_r1 : base + oldRoot * (6 * t) + 1 + 1 + 1 = nodeAddr base t oldRoot + 1 := by
      simp only [nodeAddr, nodeStride]; omega
    have h2tm1_eq : t + t - 1 = 2 * t - 1 := by omega
    let x₁ : Data 20 :=
      (((((((((((((((x.set rZero 0).set rOne 1).set rTmp1 (base + 1)).set rCnt cnt).set rStride
        (t + t)).set rTmp1 ((t + t) + (t + t))).set rStride (6 * t)).set rChild oldRoot).set rTmp1
        (oldRoot * (6 * t))).set rTmp1 (base + oldRoot * (6 * t))).set rTmp1
        (base + oldRoot * (6 * t) + 1)).set rTmp1
        (base + oldRoot * (6 * t) + 1 + 1)).set rTmp1
        (nodeAddr base t oldRoot + 1)).set rNumK (numKeys base t x.mem oldRoot)).set rTmp1
        (t + t)).set rTmp1 (2 * t - 1)
    have hbx₁ : x₁.Bounded w := by
      dsimp only [x₁]
      exact (((((((((((((((hr.bounded.set hf0).set hf1).set hf_b1).set
        (hcnt_def ▸ hr.bounded.2 _)).set
        hf_2t).set hf_4t).set hf_6t).set (holdRoot_def ▸ hr.bounded.2 _)).set hf_rmul).set
        hf_rb0).set hf_rb1).set hf_rb2).set hf_ar1).set (hr.bounded.2 _)).set hf_2t).set hf_2tm1
    by_cases hfull_r : numKeys base t x.mem oldRoot = 2 * t - 1
    · -- Full root (`numKeys oldRoot = 2 * t - 1`): `splitRootCode` allocates `cnt, cnt + 1`,
      -- raising height to `l + 2` with a 1-key non-full root `cnt + 1`, then `insertLoop` runs!
      obtain ⟨x₂, hsr, hbx₂, hmem_x₂, hmod_sr, hz_x₂, ho_x₂, hb_x₂, hd_x₂, hst_x₂,
          hk_x₂, hv_x₂, hcur_x₂, hcnt_x₂⟩ :=
        splitRootCode_spec (x := x₁) (oldRoot := oldRoot) (cnt := cnt)
          ht hr_lt_cnt (by rw [hh_eq] at hcap; omega) hbx₁ hfit
          rfl rfl
          (by dsimp only [x₁]; wram_simp; exact hr.base_eq)
          (by dsimp only [x₁]; wram_simp; exact hr.deg_eq)
          rfl rfl rfl
      simp only [x₁, Data.set_mem] at hmem_x₂ hmod_sr
      dsimp only [x₁] at hk_x₂ hv_x₂
      wram_simp at hk_x₂ hv_x₂
      obtain ⟨hmr_b0, hmr_b1, hv_r1, hs_r1, hnk_r1, hrange_r1, htr_r1⟩ :=
        memSplitRoot_spec ht hv hs hfull_r hrange
      let x₃ := x₂.set rActive 1
      have hnf_r1 : numKeys base t x₃.mem (cnt + 1) ≤ 2 * t - 2 := by
        change numKeys base t x₂.mem (cnt + 1) ≤ 2 * t - 2
        rw [hmem_x₂, hnk_r1]; omega
      obtain ⟨y, cnt', hloop, hby, hcnt_le, hcnt'_hi, hmb0, hmb1, hby_reg, hdy_reg,
          hmod_loop, _, hv_y, hs_y, _, hsub_y, htr_y⟩ :=
        insertLoop_spec (x := x₃) (l := l + 1) (u := cnt + 1) (cnt := cnt + 2) (k := k) (v := v) ht
          (hbx₂.set hf1) hfit
          (by change ValidNode _ _ _ x₂.mem _; rwa [hmem_x₂])
          (by change SortedNode _ _ _ x₂.mem _; rwa [hmem_x₂])
          hnf_r1
          (by change readNodeSet _ _ _ x₂.mem _ ⊆ _; rwa [hmem_x₂])
          (by rw [hh_eq] at hcap; omega)
          (by change x₂.mem (base + 1) = cnt + 2; rw [hmem_x₂, hmr_b1])
          hz_x₂ ho_x₂ hb_x₂ hd_x₂ hst_x₂ (hk_x₂.trans hkey) (hv_x₂.trans hval)
          hcur_x₂ hcnt_x₂ rfl
      have he : ExecWithin w insertCode x y
          ((91 * t + 160) * ((readTree l base t x.mem oldRoot).height + 1) + (21 * t + 120)) := by
        rw [hh_eq]
        unfold insertCode
        apply WP.execWithin
        wram_exec [hr.base_eq, hr.deg_eq, hcnt_def, holdRoot_def, hnk_old_eq,
          hcnt_ne, h6t, hna_r1, h2tm1_eq, hfull_r,
          hf0, hf1, hf_b1, hf_2t, hf_4t, hf_6t,
          hf_rmul, hf_rb0, hf_rb1, hf_rb2, hf_rb3, hf_ar1, hf_2tm10, hf_2tm1]
        dsimp only [x₁] at hsr
        rw [hfull_r] at hsr
        refine WP.of_execWithin hsr ?_
        wram_exec [hf1]
        exact WP.of_execWithin hloop ⟨by omega, rfl⟩
      have hy_b0 : y.mem base = cnt + 1 := by
        rw [hmb0]; change x₂.mem base = cnt + 1; rw [hmem_x₂, hmr_b0]
      have hrange_y : readNodeSet (l + 1) base t y.mem (cnt + 1) ⊆ Finset.range cnt' := by
        intro w_id hwin
        rw [Finset.mem_range]
        rcases Finset.mem_union.mp (hsub_y hwin) with hold | hico
        · change w_id ∈ readNodeSet (l + 1) base t x₂.mem (cnt + 1) at hold
          rw [hmem_x₂] at hold
          have := Finset.mem_range.mp (hrange_r1 hold); omega
        · exact (Finset.mem_Ico.mp hico).2
      have hrep : Rep base capNodes t w (readTree (l + 1) base t y.mem (cnt + 1)) y := by
        refine ⟨hby, ht, hby_reg, hdy_reg, hfit, ?_, Or.inr ⟨?_, l + 1, ?_, ?_, ?_, ?_⟩⟩
        · rw [hmb1]; rw [hh_eq] at hcap; omega
        · rw [hmb1]; omega
        · rw [hy_b0]
        · rw [hy_b0]; exact hv_y
        · rw [hy_b0]; exact hs_y
        · rw [hy_b0, hmb1]; exact hrange_y
      simp only [x₃, Data.set_mem] at hmod_loop
      refine ⟨y, readTree (l + 1) base t y.mem (cnt + 1), he, hrep, ?_, ?_,
        by simpa only [Finset.union_idempotent] using hmod_sr.trans hmod_loop⟩
      · rw [htr_y]
        have htr_x₃ : readTree (l + 1) base t x₃.mem (cnt + 1) =
            readTree (l + 1) base t (memSplitRoot base t oldRoot cnt x.mem) (cnt + 1) := by
          change readTree (l + 1) base t x₂.mem (cnt + 1) = _
          rw [hmem_x₂]
        rw [htr_x₃, htr_r1]
      · rw [hmb1, hh_eq]; omega
    · -- Non-full root (`numKeys oldRoot ≤ 2 * t - 2`): descend directly via `insertLoop`!
      let x₂ := (x₁.set rCur oldRoot).set rActive 1
      have hnf_r : numKeys base t x₂.mem oldRoot ≤ 2 * t - 2 := by
        have := hv.numKeys_le
        simp only [x₂, x₁, Data.set_mem]
        omega
      obtain ⟨y, cnt', hloop, hby, hcnt_le, hcnt'_hi, hmb0, hmb1, hby_reg, hdy_reg,
          hmod_loop, _, hv_y, hs_y, _, hsub_y, htr_y⟩ :=
        insertLoop_spec (x := x₂) (l := l) (u := oldRoot) (cnt := cnt) (k := k) (v := v) ht
          ((hbx₁.set (holdRoot_def ▸ hr.bounded.2 _)).set hf1) hfit
          (by simp only [x₂, x₁, Data.set_mem]; exact hv)
          (by simp only [x₂, x₁, Data.set_mem]; exact hs)
          hnf_r
          (by simp only [x₂, x₁, Data.set_mem]; exact hrange)
          (by rw [hh_eq] at hcap; omega)
          (by simp only [x₂, x₁, Data.set_mem, hcnt_def])
          rfl rfl
          (by dsimp only [x₂, x₁]; wram_simp; exact hr.base_eq)
          (by dsimp only [x₂, x₁]; wram_simp; exact hr.deg_eq)
          rfl
          (by dsimp only [x₂, x₁]; wram_simp; exact hkey)
          (by dsimp only [x₂, x₁]; wram_simp; exact hval)
          rfl rfl rfl
      simp only [x₂, x₁, Data.set_mem] at hmb0 hmod_loop hsub_y htr_y
      have he : ExecWithin w insertCode x y
          ((91 * t + 160) * ((readTree l base t x.mem oldRoot).height + 1) + (21 * t + 120)) := by
        rw [hh_eq]
        unfold insertCode
        apply WP.execWithin
        wram_exec [hr.base_eq, hr.deg_eq, hcnt_def, holdRoot_def, hnk_old_eq,
          hcnt_ne, h6t, hna_r1, h2tm1_eq, hfull_r,
          hf0, hf1, hf_b1, hf_2t, hf_4t, hf_6t,
          hf_rmul, hf_rb0, hf_rb1, hf_rb2, hf_rb3, hf_ar1, hf_2tm10, hf_2tm1]
        exact WP.of_execWithin hloop ⟨by
          have : (91 * t + 160) * (l + 1) ≤ (91 * t + 160) * (l + 1 + 1) :=
            Nat.mul_le_mul_left _ (by omega)
          omega, rfl⟩
      have hy_b0 : y.mem base = oldRoot := hmb0.trans holdRoot_def
      have hrange_y : readNodeSet l base t y.mem oldRoot ⊆ Finset.range cnt' := by
        intro w_id hwin
        rw [Finset.mem_range]
        rcases Finset.mem_union.mp (hsub_y hwin) with hold | hico
        · have := Finset.mem_range.mp (hrange hold); omega
        · exact (Finset.mem_Ico.mp hico).2
      have hrep : Rep base capNodes t w (readTree l base t y.mem oldRoot) y := by
        refine ⟨hby, ht, hby_reg, hdy_reg, hfit, ?_, Or.inr ⟨?_, l, ?_, ?_, ?_, ?_⟩⟩
        · rw [hmb1]; rw [hh_eq] at hcap; omega
        · rw [hmb1]; omega
        · rw [hy_b0]
        · rw [hy_b0]; exact hv_y
        · rw [hy_b0]; exact hs_y
        · rw [hy_b0, hmb1]; exact hrange_y
      refine ⟨y, readTree l base t y.mem oldRoot, he, hrep, htr_y, ?_, hmod_loop⟩
      rw [hmb1, hh_eq]; omega

/-- Logarithmic `O(t log_t n)` Word-RAM instruction bound for `insertCode`. -/
theorem insertCode_log_spec {w base capNodes t k v : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x)
    (hkey : x.regs rKey = k)
    (hval : x.regs rVal = v)
    (hcap : allocCount base x + tr.height + 2 ≤ capNodes) :
    ∃ y tr',
      ExecWithin w insertCode x y
        ((91 * t + 160) * (Nat.log t ((tr.size + 1) / 2) + 2) + (21 * t + 120)) ∧
      Rep base capNodes t w tr' y ∧
      tr'.toList = Cslib.SortedAssoc.insert k v tr.toList ∧
      allocCount base y ≤ allocCount base x + tr.height + 2 ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
  obtain ⟨y, tr', he, hrep, htl, hcnt, hmod⟩ := insertCode_spec hr hkey hval hcap
  have h2 : tr.height + 1 ≤ Nat.log t ((tr.size + 1) / 2) + 2 := by
    have := hr.height_le_log; omega
  have hle := Nat.mul_le_mul_left (91 * t + 160) h2
  exact ⟨y, tr', he.mono (by omega), hrep, htl, hcnt, hmod⟩

/-- Complete flat Word-RAM insertion program (`insertCode` followed by `halt rBase`). -/
def insertProgram : Program .standard 20 := insertCode.program rBase

/-- `insertCode` does not read the runtime word width `w`. -/
theorem not_readsWidth_insertCode : ¬insertCode.ReadsWidth := by decide

/-- `insertCode` is deterministic (`rand`-free). -/
theorem isRandFree_insertCode : insertCode.IsRandFree := by decide

/-- `insertProgram` does not read the runtime word width `w`. -/
theorem not_readsWidth_insertProgram : ¬insertProgram.ReadsWidth :=
  Code.not_readsWidth_program not_readsWidth_insertCode rBase

/-- `insertProgram` is deterministic (`rand`-free). -/
theorem isRandFree_insertProgram : insertProgram.IsRandFree :=
  Code.isRandFree_program.mpr isRandFree_insertCode

/-- Complete halting flat-program specification of `insertProgram`: runs in at most
`(91 * t + 160) * (Nat.log t ((tr.size + 1) / 2) + 2) + (21 * t + 121)` Word-RAM instructions
(charging the final `halt`), halting with `base` in `rBase` while preserving `Rep` on `tr'` with
`tr'.toList = Cslib.SortedAssoc.insert k v tr.toList`, bounding node allocation, and modifying only
`[base, base + arenaWords t capNodes)`. -/
theorem insertProgram_spec {w base capNodes t k v : ℕ} {tr : BTree ℕ ℕ} {x : Data 20}
    (hr : Rep base capNodes t w tr x)
    (hkey : x.regs rKey = k)
    (hval : x.regs rVal = v)
    (hcap : allocCount base x + tr.height + 2 ≤ capNodes) :
    ∃ y tr' steps,
      Runs w insertProgram ⟨0, x⟩ ⟨insertCode.size, y⟩ steps ∧
      step w insertProgram ⟨insertCode.size, y⟩ = .halt base ∧
      steps + 1 ≤ (91 * t + 160) * (Nat.log t ((tr.size + 1) / 2) + 2) + (21 * t + 121) ∧
      Rep base capNodes t w tr' y ∧
      tr'.toList = Cslib.SortedAssoc.insert k v tr.toList ∧
      allocCount base y ≤ allocCount base x + tr.height + 2 ∧
      Modifies (Block.mk base (arenaWords t capNodes)).footprint x.mem y.mem := by
  obtain ⟨y, tr', ⟨steps, hle, hexec⟩, hrep, htl, hcnt, hmod⟩ :=
    insertCode_log_spec hr hkey hval hcap
  have hruns : Runs w insertProgram ⟨0, x⟩ ⟨insertCode.size, y⟩ steps := by
    simpa only [Nat.zero_add] using
      hexec.runs (pc := 0) (p := insertProgram) (Program.Contains.self _).append_left
  have hhalt : step w insertProgram ⟨0 + insertCode.size, y⟩ = .halt (y.regs rBase) :=
    step_halt (by simp [insertProgram, Code.program])
  rw [Nat.zero_add, hrep.base_eq] at hhalt
  exact ⟨y, tr', steps, hruns, hhalt, by omega, hrep, htl, hcnt, hmod⟩

end Cslib.DataStructure.BTree.WordRAM
