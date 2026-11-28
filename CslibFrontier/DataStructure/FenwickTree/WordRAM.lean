/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.FenwickTree.Basic
public import CslibFrontier.DataStructure.WordRAM.StateTransition
public import CslibFrontier.Computability.WordRAM.CountingLoop
public import CslibFrontier.Computability.WordRAM.ExactNotation
import CslibFrontier.Tactic.WramOmega

/-!
# Word-RAM Fenwick Trees (Binary Indexed Trees)

This module implements Fenwick trees (`[Fenwick1994]`, pp. 328–332) as fixed bounded-word machine
programs over `Cslib.WordRAM.Basis.exact` (lifted to `Basis.standard` via
`StateTransitionImpl.toStandard`), realizing dynamic prefix sums (`PrefixSums.Op ℕ`,
`PrefixSums.step`) in exact `n` words of memory `[base, base + n)` for any length `n`:

* **Bitwise lowest-set-bit stepping (`and_pred_eq_sub_lowbit`, `sub_and_pred_eq_lowbit`):** on
  unsigned naturals, `m &&& (m - 1) = m - lowbit m` clears the lowest set bit without word-width
  masks, and `m - (m &&& (m - 1)) = lowbit m` isolates it in `O(1)` exact-basis instructions with
  every intermediate value `≤ m`.
* **Overflow-free parent bounds:** upward updates and immediate-parent construction compare
  `n - m < lowbit m` before computing `m + lowbit m`, requiring only `Fits w (base + n)` rather
  than `Fits w (base + 2 * n)`.
* **Logarithmic operations (`opCode`, `impl`, `implStandard`, `certificate`):** a single fixed
  12-register `SubroutineCode .exact 12 1` serves both point increments (`add pos δ`) and prefix
  queries (`sum len`, clamped to `n`) within `13 * Nat.clog 2 (s.length + 1) + 10` body
  instructions (`+ 2` with canonical result recoding and `halt` in `DynamicCertificate`).
* **Linear initialization (`initClear_exec`, `buildCode`, `buildCode_spec`):** dirty-memory zero
  initialization runs in `4 * n + 9` instructions via `SubroutineBase.initClear_exec` (`3`
  instructions on fresh zeroed memory via `initFresh_exec`), and in-place immediate-parent
  propagation `buildCode` converts raw array entries `s` in `[base, base + s.length)` into a valid
  Fenwick tree (`ofList s`) in at most `17 * s.length + 5` exact-basis instructions whenever
  `Fits w s.sum`.

## Main definitions

* `Cslib.DataStructure.FenwickTree.WordRAM.spec`: dynamic prefix-sum `StateTransitionSpec` on
  `List ℕ` with word-width admissibility `valid w`.
* `Cslib.DataStructure.FenwickTree.WordRAM.treeOfMem`, `Rep`: view of `[base, base + n)` as a
  `FenwickTree ℕ` and bounded machine representation invariant.
* `Cslib.DataStructure.FenwickTree.WordRAM.queryLoop`, `updateLoop`, `opCode`, `subroutineCode`:
  exact-basis structured loops, dispatcher, and relocatable `SubroutineCode .exact 12 1`.
* `Cslib.DataStructure.FenwickTree.WordRAM.buildCode`: `O(n)` in-place immediate-parent Fenwick
  tree construction over `Basis.exact`.
* `Cslib.DataStructure.FenwickTree.WordRAM.impl`, `implStandard`, `recoding`, `certificate`:
  `WordRAM.StateTransitionImpl` certificates over `Basis.exact` and `Basis.standard` and standalone
  `DynamicCertificate`.

## Main results

* `Cslib.DataStructure.FenwickTree.and_pred_eq_sub_lowbit`, `sub_and_pred_eq_lowbit`: unsigned
  bitwise identities `m &&& (m - 1) = m - lowbit m` and `m - (m &&& (m - 1)) = lowbit m`.
* `Cslib.DataStructure.FenwickTree.WordRAM.queryLoop_spec`, `updateLoop_spec`, `opCode_spec`:
  logarithmic instruction bounds and memory framing for prefix queries and point increments.
* `Cslib.DataStructure.FenwickTree.WordRAM.buildCode_spec`: in-place immediate-parent construction
  establishes `Rep` for `s` (matching `ofList s`) in at most `17 * s.length + 5` instructions.
* `Cslib.DataStructure.FenwickTree.WordRAM.instruction_bound`, `totalCost_charge`, `client_spec`:
  `13 * Nat.clog 2 (s.length + 1) + 12` per-operation `DynamicProgram` instruction bound and
  adaptive-client execution theorem.

## References

* [P. M. Fenwick, *A New Data Structure for Cumulative Frequency Tables*, pp. 328–332][Fenwick1994]
-/

@[expose] public section

namespace Cslib.DataStructure.FenwickTree

/-! ## Unsigned bitwise `lowbit` identities -/

/-- Clearing the lowest set bit via `m &&& (m - 1)` equals `m - lowbit m` for every `m : ℕ`. -/
theorem and_pred_eq_sub_lowbit (m : ℕ) : m &&& (m - 1) = m - lowbit m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.zero_sub, lowbit_zero, Nat.and_zero]
    · rw [lowbit]
      have hne : m ≠ 0 := Nat.ne_of_gt hm
      simp only [hne, ↓reduceIte]
      split_ifs with hodd
      · apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_and]
        cases i with
        | zero =>
          simp only [Nat.testBit_zero]
          have h0 : (m - 1) % 2 = 0 := by omega
          simp only [hodd, h0]
          decide
        | succ i =>
          rw [Nat.testBit_succ, Nat.testBit_succ]
          have hdiv : (m - 1) / 2 = m / 2 := by omega
          rw [hdiv, Bool.and_self]
      · have hsub := ih (m / 2) (by omega)
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_and]
        cases i with
        | zero =>
          simp only [Nat.testBit_zero]
          have hm0 : m % 2 = 0 := by omega
          have hlb_even : (m - 2 * lowbit (m / 2)) % 2 = 0 := by
            have hle := lowbit_le (m / 2)
            omega
          simp only [hm0, hlb_even]
          exact Bool.false_and _
        | succ i =>
          rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
          have hpred_div : (m - 1) / 2 = m / 2 - 1 := by omega
          have hsub_div : (m - 2 * lowbit (m / 2)) / 2 = m / 2 - lowbit (m / 2) := by
            have hle := lowbit_le (m / 2)
            omega
          rw [hpred_div, hsub_div, ← Nat.testBit_and, hsub]

/-- Isolating the lowest set bit via `m - (m &&& (m - 1))` equals `lowbit m` for every `m : ℕ`. -/
theorem sub_and_pred_eq_lowbit (m : ℕ) : m - (m &&& (m - 1)) = lowbit m := by
  rw [and_pred_eq_sub_lowbit]
  have hle := lowbit_le m
  omega

namespace WordRAM

open Cslib.WordRAM Cslib.DataStructure

/-! ## Word-bounded dynamic prefix-sum specification -/

/-- Word-fit admissibility for `PrefixSums.Op ℕ` at word width `w`: operation arguments fit in a
`w`-bit word, and an in-bounds increment `add pos δ` keeps the total sum below `2 ^ w`. -/
def valid (w : ℕ) (s : List ℕ) : PrefixSums.Op ℕ → Prop
  | .add pos δ => Fits w pos ∧ Fits w δ ∧ (pos < s.length → Fits w (s.sum + δ))
  | .sum len => Fits w len

/-- Dynamic prefix sums on `List ℕ` restricted to `w`-bit fitting operations (`PrefixSums.step`). -/
abbrev spec (w : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn
    (State := List ℕ) (Op := PrefixSums.Op ℕ) (Result := PrefixSums.Op.Result ℕ)
    PrefixSums.step (valid w)

private theorem sum_addAt_of_lt {s : List ℕ} {pos : ℕ} (δ : ℕ) (hpos : pos < s.length) :
    (PrefixSums.addAt s pos δ).sum = s.sum + δ := by
  induction s generalizing pos with
  | nil => simp at hpos
  | cons a as ih =>
    cases pos with
    | zero =>
      simp only [PrefixSums.addAt, List.getD_cons_zero, List.set_cons_zero, List.sum_cons]
      omega
    | succ pos =>
      simp only [List.length_cons] at hpos
      simp only [PrefixSums.addAt, List.getD_cons_succ, List.set_cons_succ, List.sum_cons]
      have h := ih (by omega : pos < as.length)
      simp only [PrefixSums.addAt] at h
      omega

/-! ## Memory view as a `FenwickTree ℕ` -/

/-- Extract the `n`-word region `[base, base + n)` of Word-RAM memory as a `FenwickTree ℕ`. -/
def treeOfMem (base n : ℕ) (mem : ℕ → ℕ) : FenwickTree ℕ :=
  ⟨Array.ofFn fun i : Fin n => mem (base + i.1)⟩

@[simp]
theorem size_treeOfMem (base n : ℕ) (mem : ℕ → ℕ) :
    (treeOfMem base n mem).size = n := by
  simp only [FenwickTree.size, treeOfMem, Array.size_ofFn]

@[simp]
theorem size_tree_treeOfMem (base n : ℕ) (mem : ℕ → ℕ) :
    (treeOfMem base n mem).tree.size = n := by
  simp only [treeOfMem, Array.size_ofFn]

@[simp]
theorem getElem_treeOfMem (base n : ℕ) (mem : ℕ → ℕ) (i : ℕ)
    (hi : i < (treeOfMem base n mem).tree.size) :
    (treeOfMem base n mem).tree[i] = mem (base + i) := by
  simp only [treeOfMem, Array.getElem_ofFn]

theorem treeOfMem_congr {base n : ℕ} {mem mem' : ℕ → ℕ}
    (h : ∀ a ∈ (Block.mk base n).footprint, mem' a = mem a) :
    treeOfMem base n mem' = treeOfMem base n mem := by
  simp only [treeOfMem, FenwickTree.mk.injEq]
  refine Array.ext (by simp) fun i hi₁ hi₂ => ?_
  simp only [Array.size_ofFn] at hi₁
  simp only [Array.getElem_ofFn]
  exact h (base + i) (by simp only [Block.mem_footprint, Block.Owns]; omega)

theorem treeOfMem_zeros {base n : ℕ} {mem : ℕ → ℕ}
    (hzero : ∀ a ∈ (Block.mk base n).footprint, mem a = 0) :
    treeOfMem base n mem = FenwickTree.zeros n := by
  simp only [treeOfMem, FenwickTree.zeros, FenwickTree.mk.injEq]
  refine Array.ext (by simp) fun i hi₁ hi₂ => ?_
  simp only [Array.size_ofFn] at hi₁
  simp only [Array.getElem_ofFn, Array.getElem_replicate]
  exact hzero (base + i) (by simp only [Block.mem_footprint, Block.Owns]; omega)

theorem tree_treeOfMem_update_add {base n idx v : ℕ} {mem : ℕ → ℕ} :
    (treeOfMem base n (Function.update mem (base + idx) (mem (base + idx) + v))).tree =
      (treeOfMem base n mem).tree.modify idx (· + v) := by
  refine Array.ext (by simp) fun i hi₁ hi₂ => ?_
  simp only [size_tree_treeOfMem] at hi₁
  simp only [getElem_treeOfMem, Array.getElem_modify]
  by_cases heq : idx = i
  · subst heq
    simp only [↓reduceIte, Function.update_self]
  · have hne : base + i ≠ base + idx := by omega
    simp only [heq, ↓reduceIte, Function.update_of_ne hne]

/-! ## Register assignment and machine programs -/

namespace Reg
/-- Persistent bump-pointer frontier register (`base + n` after initialization). -/
abbrev rFrontier : Fin 12 := 0
/-- Persistent base address of `[base, base + n)`. -/
abbrev rBase : Fin 12 := 1
/-- Persistent array length `n`. -/
abbrev rLen : Fin 12 := 2
/-- Operation tag (`0` for `add`, nonzero for `sum`). -/
abbrev rTag : Fin 12 := 3
/-- Operation `pos` (for `add`) or `len` (for `sum`). -/
abbrev rPos : Fin 12 := 4
/-- Operation increment `δ` (for `add`). -/
abbrev rDelta : Fin 12 := 5
/-- Query accumulator / output register (`curReg` during `initClear`). -/
abbrev rAns : Fin 12 := 6
/-- Traversal index register (`1`-based node `m` or `0`-based counter in `buildCode`). -/
abbrev rIdx : Fin 12 := 7
/-- Constant `0` scratch (`zeroReg` during `initClear`). -/
abbrev rZero : Fin 12 := 8
/-- Constant `1` scratch (`oneReg` during `initClear`). -/
abbrev rOne : Fin 12 := 9
/-- Bitwise / address scratch 1. -/
abbrev rTmp1 : Fin 12 := 10
/-- Address / value scratch 2. -/
abbrev rTmp2 : Fin 12 := 11
end Reg

open Reg

/-- Concrete Fenwick-tree representation invariant at `[base, base + n)` and word width `w`. -/
structure Rep (b n w : ℕ) (s : List ℕ) (x : Data 12) : Prop where
  /-- All registers and memory words fit in `w` bits. -/
  bounded : x.Bounded w
  /-- Persistent base register holds `b`. -/
  base_eq : x.regs rBase = b
  /-- Persistent size register holds `n`. -/
  size_eq : x.regs rLen = n
  /-- Total sum of `s` fits in `w` bits (so no prefix or Fenwick interval sum overflows). -/
  sum_fits : Fits w s.sum
  /-- `[b, b + n)` forms the unique valid Fenwick tree for `s`. -/
  valid_tree : Valid (treeOfMem b n x.mem) s

theorem Rep.length_eq {b n w : ℕ} {s : List ℕ} {x : Data 12} (hr : Rep b n w s x) :
    s.length = n := by
  simpa only [size_treeOfMem] using hr.valid_tree.size_eq.symm

/-! ### Downward prefix-query loop (`queryLoop`) -/

/-- Single downward Fenwick query step: adds `mem[rBase + (rIdx - 1)]` to `rAns` and clears the
lowest set bit of `rIdx` (`rIdx ← rIdx &&& (rIdx - 1)`). -/
def queryBody : Code .exact 12 := ram_exact[
  rTmp1 ← rIdx - rOne;
  rTmp2 ← rBase + rTmp1;
  rTmp2 ← *rTmp2;
  rAns ← rAns + rTmp2;
  rIdx ← rIdx &&& rTmp1 ]

/-- Downward Fenwick prefix-query loop (`while 0 < rIdx`). -/
def queryLoop : Code .exact 12 := ram_exact[while rZero < rIdx do [⟪queryBody⟫]]

/-- Post-iteration register state of `queryBody`. -/
private def queryNext (x : Data 12) (b m a : ℕ) : Data 12 :=
  let v := x.mem (b + (m - 1))
  ((((x.set rTmp1 (m - 1)).set rTmp2 (b + (m - 1))).set rTmp2 v).set rAns (a + v)).set
    rIdx (m &&& (m - 1))

private theorem queryBody_exec {w b n m a : ℕ} {x : Data 12}
    (ho : x.regs rOne = 1) (hb : x.regs rBase = b)
    (hm_reg : x.regs rIdx = m) (ha_reg : x.regs rAns = a)
    (hm_pos : 0 < m) (hm_le : m ≤ n)
    (hfit_addr : Fits w (b + n))
    (hfit_sum : Fits w (a + x.mem (b + (m - 1)))) :
    ExecWithin w queryBody x (queryNext x b m a) 5 := by
  have hle1 : 1 ≤ m := hm_pos
  have hf_sub : Fits w (m - 1) := hfit_addr.of_le (by omega)
  have hf_addr : Fits w (b + (m - 1)) := hfit_addr.of_le (by omega)
  have hand_le : m &&& (m - 1) ≤ m := by rw [and_pred_eq_sub_lowbit]; omega
  have hf_and : Fits w (m &&& (m - 1)) := hfit_addr.of_le (by omega)
  ram_exact_eval [queryBody, queryNext, ho, hb, hm_reg, ha_reg, hle1,
    hf_sub, hf_addr, hfit_sum, hf_and]

/-- `queryLoop` accumulates `(s.take m).sum` into `rAns` in `7 * (downChain m).length + 2`
instructions (`≤ 7 * Nat.clog 2 (n + 1) + 2`), preserving memory and persistent registers. -/
theorem queryLoop_spec {w b n m a : ℕ} {s : List ℕ} {x : Data 12}
    (hvt : Valid (treeOfMem b n x.mem) s)
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hb : x.regs rBase = b)
    (hm_reg : x.regs rIdx = m) (ha_reg : x.regs rAns = a)
    (hm_le : m ≤ n)
    (hfit_addr : Fits w (b + n))
    (hfit_sum : Fits w (a + (s.take m).sum)) :
    ∃ y, ExecWithin w queryLoop x y (7 * (downChain m).length + 2) ∧
      y.regs rAns = a + (s.take m).sum ∧
      y.regs rBase = b ∧
      y.regs rLen = x.regs rLen ∧
      y.regs rFrontier = x.regs rFrontier ∧
      y.mem = x.mem := by
  induction m using Nat.strongRecOn generalizing x a with
  | ind m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · refine ⟨x, (ExecWithin.loop_exit ?_).mono (by simp [downChain_zero]), ?_, hb, rfl, rfl, rfl⟩
      · simp only [Cond.holds_lt, hz, hm_reg, Nat.lt_irrefl, not_false_eq_true]
      · simpa only [List.take_zero, List.sum_nil, add_zero] using ha_reg
    · have hm_sz : m ≤ (treeOfMem b n x.mem).tree.size := by
        simpa only [size_tree_treeOfMem] using hm_le
      have hcell : x.mem (b + (m - 1)) = ((s.take m).drop (m - lowbit m)).sum := by
        simpa only [getElem_treeOfMem] using hvt.2 m hm_pos hm_sz
      have hlt : m - lowbit m < m := Nat.sub_lt hm_pos (lowbit_pos hm_pos)
      have hsplit : (s.take m).sum =
          (s.take (m - lowbit m)).sum + ((s.take m).drop (m - lowbit m)).sum := by
        conv_lhs =>
          rw [← List.take_append_drop (m - lowbit m) (s.take m),
            List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt), List.sum_append]
      have hfit_step : Fits w (a + x.mem (b + (m - 1))) :=
        hfit_sum.of_le (by rw [hcell, hsplit]; omega)
      have hbody := queryBody_exec ho hb hm_reg ha_reg hm_pos hm_le hfit_addr hfit_step
      let x₁ := queryNext x b m a
      have hvt₁ : Valid (treeOfMem b n x₁.mem) s := hvt
      have hz₁ : x₁.regs rZero = 0 := by simp +decide [x₁, queryNext, hz]
      have ho₁ : x₁.regs rOne = 1 := by simp +decide [x₁, queryNext, ho]
      have hb₁ : x₁.regs rBase = b := by simp +decide [x₁, queryNext, hb]
      have hsz₁ : x₁.regs rLen = x.regs rLen := by simp +decide [x₁, queryNext]
      have hfr₁ : x₁.regs rFrontier = x.regs rFrontier := by simp +decide [x₁, queryNext]
      have hm₁ : x₁.regs rIdx = m - lowbit m := and_pred_eq_sub_lowbit m
      have ha₁ : x₁.regs rAns = a + x.mem (b + (m - 1)) := by simp +decide [x₁, queryNext]
      have hfit_next : Fits w ((a + x.mem (b + (m - 1))) + (s.take (m - lowbit m)).sum) :=
        hfit_sum.of_le (by rw [hcell, hsplit]; omega)
      obtain ⟨y, hy, hy_ans, hy_b, hy_sz, hy_fr, hy_mem⟩ :=
        ih (m - lowbit m) hlt hvt₁ hz₁ ho₁ hb₁ hm₁ ha₁ (by omega) hfit_next
      have hcond : (Cond.lt rZero rIdx).Holds x := by
        simp only [Cond.holds_lt, hz, hm_reg, hm_pos]
      have hchain : (downChain m).length = (downChain (m - lowbit m)).length + 1 := by
        conv_lhs => rw [downChain]
        simp only [hm_pos, ↓reduceDIte, List.length_cons]
      refine ⟨y, (hbody.loop_iter hcond hy).mono (by rw [hchain]; omega), ?_, hy_b,
        hy_sz.trans hsz₁, hy_fr.trans hfr₁, hy_mem⟩
      rw [hy_ans, hcell, hsplit]
      omega

/-! ### Upward point-update loop (`updateLoop`) -/

/-- Single upward Fenwick update step: adds `rDelta` to `mem[rBase + (rIdx - 1)]`, isolates
`lb = lowbit rIdx` via `rIdx - (rIdx &&& (rIdx - 1))`, and either exits (`rIdx ← 0`) when
`rLen - rIdx < lb` or advances `rIdx ← rIdx + lb`. -/
def updateBody : Code .exact 12 := ram_exact[
  rTmp1 ← rIdx - rOne;
  rTmp2 ← rBase + rTmp1;
  rAns ← *rTmp2;
  rAns ← rAns + rDelta;
  *rTmp2 ← rAns;
  rTmp1 ← rIdx &&& rTmp1;
  rTmp1 ← rIdx - rTmp1;
  rTmp2 ← rLen - rIdx;
  if rTmp2 < rTmp1 then [rIdx ← #0] else [rIdx ← rIdx + rTmp1] ]

/-- Upward Fenwick point-update loop (`while 0 < rIdx`). -/
def updateLoop : Code .exact 12 := ram_exact[while rZero < rIdx do [⟪updateBody⟫]]

/-- Post-iteration machine state of `updateBody`. -/
private def updateNext (x : Data 12) (b n m δ : ℕ) : Data 12 :=
  let v := x.mem (b + (m - 1))
  let lb := m - (m &&& (m - 1))
  let y := (((((((x.set rTmp1 (m - 1)).set rTmp2 (b + (m - 1))).set rAns v).set rAns (v + δ)).write
    (b + (m - 1)) (v + δ)).set rTmp1 (m &&& (m - 1))).set rTmp1 lb).set rTmp2 (n - m)
  if n - m < lb then y.set rIdx 0 else y.set rIdx (m + lb)

private theorem updateBody_exec {w b n m δ : ℕ} {x : Data 12}
    (ho : x.regs rOne = 1) (hb : x.regs rBase = b) (hsz : x.regs rLen = n)
    (hm_reg : x.regs rIdx = m) (hd_reg : x.regs rDelta = δ)
    (hm_pos : 0 < m) (hm_le : m ≤ n)
    (hfit_addr : Fits w (b + n))
    (hfit_val : Fits w (x.mem (b + (m - 1)) + δ)) :
    ExecWithin w updateBody x (updateNext x b n m δ) 11 := by
  have hle1 : 1 ≤ m := hm_pos
  have hand_le : m &&& (m - 1) ≤ m := by rw [and_pred_eq_sub_lowbit]; omega
  have hf_sub1 : Fits w (m - 1) := hfit_addr.of_le (by omega)
  have hf_addr : Fits w (b + (m - 1)) := hfit_addr.of_le (by omega)
  have hf_and : Fits w (m &&& (m - 1)) := hfit_addr.of_le (by omega)
  have hf_lb : Fits w (m - (m &&& (m - 1))) := hfit_addr.of_le (by omega)
  have hf_rem : Fits w (n - m) := hfit_addr.of_le (by omega)
  by_cases hlt : n - m < m - (m &&& (m - 1))
  · ram_exact_eval [updateBody, updateNext, ho, hb, hsz, hm_reg, hd_reg,
      hle1, hand_le, hm_le, hlt, hf_sub1, hf_addr, hfit_val, hf_and, hf_lb, hf_rem]
  · have hf_next : Fits w (m + (m - (m &&& (m - 1)))) := hfit_addr.of_le (by omega)
    ram_exact_eval [updateBody, updateNext, ho, hb, hsz, hm_reg, hd_reg,
      hle1, hand_le, hm_le, hlt, hf_sub1, hf_addr, hfit_val, hf_and, hf_lb, hf_rem, hf_next]

private theorem updateNext_mem (x : Data 12) (b n m δ a : ℕ) :
    (updateNext x b n m δ).mem a =
      Function.update x.mem (b + (m - 1)) (x.mem (b + (m - 1)) + δ) a := by
  simp only [updateNext]
  split <;> rfl

/-- `updateLoop` performs `addLoop n m δ` in-place on `[b, b + n)` in at most
`13 * (upChain n m).length + 2` instructions (`≤ 13 * Nat.clog 2 (n + 1) + 2`), preserving
outside memory and persistent registers. -/
theorem updateLoop_spec {w b n m δ S : ℕ} {x : Data 12}
    (hz : x.regs rZero = 0) (ho : x.regs rOne = 1) (hb : x.regs rBase = b) (hsz : x.regs rLen = n)
    (hm_reg : x.regs rIdx = m) (hd_reg : x.regs rDelta = δ)
    (hm_pos : 0 < m) (hm_le : m ≤ n)
    (hfit_addr : Fits w (b + n))
    (hfit_sum : Fits w (S + δ))
    (hcells : ∀ k, m ≤ k → k ≤ n → x.mem (b + (k - 1)) ≤ S) :
    ∃ y, ExecWithin w updateLoop x y (13 * (upChain n m).length + 2) ∧
      (treeOfMem b n y.mem).tree = addLoop n m δ (treeOfMem b n x.mem).tree ∧
      Modifies (Block.mk b n).footprint x.mem y.mem ∧
      y.regs rBase = b ∧
      y.regs rLen = n ∧
      y.regs rFrontier = x.regs rFrontier := by
  induction m using (_root_.measure fun m => n + 1 - m).wf.induction generalizing x with
  | h m ih =>
    have hfit_val : Fits w (x.mem (b + (m - 1)) + δ) :=
      hfit_sum.of_le (Nat.add_le_add_right (hcells m (Nat.le_refl m) hm_le) δ)
    have hbody := updateBody_exec ho hb hsz hm_reg hd_reg hm_pos hm_le hfit_addr hfit_val
    let x₁ := updateNext x b n m δ
    have hx₁_mem : x₁.mem = Function.update x.mem (b + (m - 1)) (x.mem (b + (m - 1)) + δ) :=
      funext (updateNext_mem x b n m δ)
    have hmod₁ : Modifies (Block.mk b n).footprint x.mem x₁.mem := fun a ha => by
      rw [hx₁_mem, Function.update_of_ne]
      exact fun heq => ha (by simp only [Block.mem_footprint, Block.Owns]; omega)
    have htree₁ : (treeOfMem b n x₁.mem).tree =
        (treeOfMem b n x.mem).tree.modify (m - 1) (· + δ) := by
      rw [hx₁_mem]
      exact tree_treeOfMem_update_add
    have hcond : (Cond.lt rZero rIdx).Holds x := by
      simp only [Cond.holds_lt, hz, hm_reg, hm_pos]
    have hlb_eq : m - (m &&& (m - 1)) = lowbit m := sub_and_pred_eq_lowbit m
    have hlb_pos : 0 < lowbit m := lowbit_pos hm_pos
    have hz₁ : x₁.regs rZero = 0 := by dsimp only [x₁, updateNext]; split <;> exact hz
    have ho₁ : x₁.regs rOne = 1 := by dsimp only [x₁, updateNext]; split <;> exact ho
    have hb₁ : x₁.regs rBase = b := by dsimp only [x₁, updateNext]; split <;> exact hb
    have hsz₁ : x₁.regs rLen = n := by dsimp only [x₁, updateNext]; split <;> exact hsz
    have hfr₁ : x₁.regs rFrontier = x.regs rFrontier := by
      dsimp only [x₁, updateNext]; split <;> rfl
    have hd₁ : x₁.regs rDelta = δ := by dsimp only [x₁, updateNext]; split <;> exact hd_reg
    by_cases hstop : n - m < lowbit m
    · have hstop' : n - m < m - (m &&& (m - 1)) := hlb_eq.symm ▸ hstop
      have hidx₁ : x₁.regs rIdx = 0 := by
        dsimp only [x₁, updateNext]
        rw [ite_eq_left_iff.mpr fun h => (h hstop').elim]
        rfl
      have hexit : ExecWithin w updateLoop x₁ x₁ 2 :=
        ExecWithin.loop_exit
          (by simp only [Cond.holds_lt, hz₁, hidx₁, Nat.lt_irrefl, not_false_eq_true])
      have hchain : (upChain n m).length = 1 := by
        rw [upChain]
        simp only [hm_pos, hm_le, and_self, ↓reduceDIte, List.length_cons]
        rw [upChain]
        have hnot : ¬ (0 < m + lowbit m ∧ m + lowbit m ≤ n) := by omega
        simp only [hnot, ↓reduceDIte, List.length_nil]
      have hloop_eq : addLoop n m δ (treeOfMem b n x.mem).tree =
          (treeOfMem b n x.mem).tree.modify (m - 1) (· + δ) := by
        conv_lhs => rw [addLoop]
        simp only [hm_pos, hm_le, and_self, ↓reduceDIte]
        conv_lhs => rw [addLoop]
        have hnot : ¬ (0 < m + lowbit m ∧ m + lowbit m ≤ n) := by omega
        simp only [hnot, ↓reduceDIte]
      exact ⟨x₁, (hbody.loop_iter hcond hexit).mono (by rw [hchain]),
        htree₁.trans hloop_eq.symm, hmod₁, hb₁, hsz₁, hfr₁⟩
    · have hstop' : ¬ (n - m < m - (m &&& (m - 1))) := hlb_eq.symm ▸ hstop
      have hm_next_le : m + lowbit m ≤ n := by omega
      have hidx₁ : x₁.regs rIdx = m + lowbit m := by
        dsimp only [x₁, updateNext]
        rw [ite_eq_right_iff.mpr fun h => (hstop' h).elim, ← hlb_eq]
        rfl
      have hcells₁ : ∀ k, m + lowbit m ≤ k → k ≤ n → x₁.mem (b + (k - 1)) ≤ S := by
        intro k hk1 hk2
        rw [hx₁_mem, Function.update_of_ne (by omega : b + (k - 1) ≠ b + (m - 1))]
        exact hcells k (by omega) hk2
      obtain ⟨y, hy, hy_tree, hy_mod, hy_b, hy_sz, hy_fr⟩ :=
        @ih (m + lowbit m) (show n + 1 - (m + lowbit m) < n + 1 - m by omega)
          x₁ hz₁ ho₁ hb₁ hsz₁ hidx₁ hd₁ (by omega) hm_next_le hcells₁
      have hchain : (upChain n m).length = (upChain n (m + lowbit m)).length + 1 := by
        conv_lhs => rw [upChain]
        simp only [hm_pos, hm_le, and_self, ↓reduceDIte, List.length_cons]
      have hloop_eq : addLoop n m δ (treeOfMem b n x.mem).tree =
          addLoop n (m + lowbit m) δ ((treeOfMem b n x.mem).tree.modify (m - 1) (· + δ)) := by
        conv_lhs => rw [addLoop]
        simp only [hm_pos, hm_le, and_self, ↓reduceDIte]
      refine ⟨y, (hbody.loop_iter hcond hy).mono (by rw [hchain]; omega), ?_,
        fun a ha => (hy_mod a ha).trans (hmod₁ a ha), hy_b, hy_sz, hy_fr.trans hfr₁⟩
      rw [hy_tree, htree₁, hloop_eq]

/-! ### Operation dispatcher and `StateTransitionImpl` -/

/-- Constant-register initialization prefix of `opCode`. -/
def opSetup : Code .exact 12 := ram_exact[
  rZero ← #0;
  rOne ← #1;
  rAns ← #0 ]

/-- Unified operation dispatcher for `add` (`rTag = 0`) and `sum` (`rTag ≠ 0`) over
`Basis.exact`. -/
def opCode : Code .exact 12 := ram_exact[
  ⟪opSetup⟫;
  if rTag = rZero then [
    if rPos < rLen then [
      rIdx ← rPos + rOne;
      ⟪updateLoop⟫
    ] else [
      rIdx ← #0
    ]
  ] else [
    if rLen < rPos then [
      rIdx ← rLen
    ] else [
      rIdx ← rPos
    ];
    ⟪queryLoop⟫
  ] ]

/-- Allocate `[rFrontier, rFrontier + rLen)` by copying `rFrontier` to `rBase` and advancing
`rFrontier` by `rLen`. -/
def allocSpanCode : Code .exact 12 := ram_exact[
  rBase ← rFrontier;
  rFrontier ← rFrontier + rLen ]

/-- Trivial post-zeroed scalar setup. -/
def initSetupCode : Code .exact 12 := ram_exact[
  rZero ← #0 ]

/-- Relocatable `SubroutineCode` over `Basis.exact` for Fenwick-tree dynamic prefix sums. -/
def subroutineCode : SubroutineCode .exact 12 1 where
  allocSpan := allocSpanCode
  initSetup := initSetupCode
  code := opCode
  frontierReg := rFrontier
  baseReg := rBase
  initParams := ![rLen]
  curReg := rAns
  zeroReg := rZero
  oneReg := rOne
  incCur := .exactBin .add rAns rAns rOne
  input i := !(i == rFrontier || i == rBase || i == rLen)
  output := rAns

/-- Encode `PrefixSums.Op ℕ` into caller-supplied input registers (`rTag`, `rPos`, `rDelta`). -/
def encodeOp (o : PrefixSums.Op ℕ) (i : Fin 12) : ℕ :=
  match o with
  | .add pos δ =>
      if i = rTag then 0
      else if i = rPos then pos
      else if i = rDelta then δ
      else 0
  | .sum len =>
      if i = rTag then 1
      else if i = rPos then len
      else 0

/-- Register calling convention matching `encodeOp` on `rTag`, `rPos`, and `rDelta`. -/
def argMatch (o : PrefixSums.Op ℕ) (regs : Fin 12 → ℕ) : Prop :=
  match o with
  | .add pos δ => regs rTag = 0 ∧ regs rPos = pos ∧ regs rDelta = δ
  | .sum len => regs rTag ≠ 0 ∧ regs rPos = len

/-- Decode the typed result of `PrefixSums.Op ℕ` from `rAns`. -/
def decodeOp : (o : PrefixSums.Op ℕ) → (Fin 12 → ℕ) → Option (PrefixSums.Op.Result ℕ o)
  | .add _ _, _ => some ()
  | .sum _, regs => some (regs rAns)

/-- Representation-independent per-operation instruction budget `13 * ⌈log₂ (|s| + 1)⌉ + 10`. -/
def charge (s : List ℕ) (_ : PrefixSums.Op ℕ) : ℕ :=
  13 * Nat.clog 2 (s.length + 1) + 10

/-- Because every `PrefixSums.Op ℕ` preserves `s.length`, `totalCost` along any `k`-operation
history simplifies to `k * (13 * Nat.clog 2 (s.length + 1) + 10 + c)` for any constant offset
`c`. -/
private theorem totalCost_charge_add (w c : ℕ) (s : List ℕ) (os : List (PrefixSums.Op ℕ)) :
    (spec w).totalCost (fun st o => charge st o + c) s os =
      os.length * (13 * Nat.clog 2 (s.length + 1) + 10 + c) := by
  induction os generalizing s with
  | nil => simp only [StateTransitionSpec.totalCost_nil, List.length_nil, Nat.zero_mul]
  | cons o os ih =>
    rw [StateTransitionSpec.totalCost_cons, ih ((spec w).stepFn s o).1, PrefixSums.length_stepFn]
    simp only [charge, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm, Nat.add_assoc]

theorem totalCost_charge (w : ℕ) (s : List ℕ) (os : List (PrefixSums.Op ℕ)) :
    (spec w).totalCost charge s os =
      os.length * (13 * Nat.clog 2 (s.length + 1) + 10) := by
  simpa only [Nat.add_zero] using totalCost_charge_add w 0 s os

/-- Per-operation execution theorem for `opCode` over `Basis.exact`. -/
theorem opCode_spec {w b n : ℕ} (hw : 0 < w) (hfit_addr : Fits w (b + n))
    {s : List ℕ} {x : Data 12} (o : PrefixSums.Op ℕ)
    (hr : Rep b n w s x) (hv : (spec w).valid s o) (harg : argMatch o x.regs) :
    ∃ y t, Exec w opCode x y t ∧
      decodeOp o y.regs = some ((spec w).stepFn s o).2 ∧
      Rep b n w ((spec w).stepFn s o).1 y ∧
      Modifies (Block.mk b n).footprint x.mem y.mem ∧
      y.regs rFrontier = x.regs rFrontier ∧
      t ≤ charge s o := by
  have hf1 : Fits w 1 := fits_one (Nat.ne_of_gt hw)
  have hlen_s : s.length = n := hr.length_eq
  let x₀ := ((x.set rZero 0).set rOne 1).set rAns 0
  have hpre : ExecWithin w opSetup x x₀ 3 := by
    ram_exact_eval [opSetup, x₀, hf1]
  cases o with
  | add pos δ =>
    obtain ⟨htag, hpos_reg, hdelta_reg⟩ := harg
    obtain ⟨hf_pos, hf_δ, hf_sum_add⟩ := hv
    have hcond_tag : (Cond.eq rTag rZero).Holds x₀ := by
      simp +decide [Cond.Holds, x₀, htag]
    by_cases hlt : pos < n
    · have hcond_pos : (Cond.lt rPos rLen).Holds x₀ := by
        simp +decide [Cond.Holds, x₀, hpos_reg, hr.size_eq, hlt]
      let x₁ := x₀.set rIdx (pos + 1)
      have hf_p1 : Fits w (pos + 1) := hfit_addr.of_le (by omega)
      have hset_idx : ExecWithin w (ram_exact[rIdx ← rPos + rOne] : Code .exact 12) x₀ x₁ 1 := by
        have hpos₀ : x₀.regs rPos = pos := hpos_reg
        have hone₀ : x₀.regs rOne = 1 := rfl
        ram_exact_eval [x₁, hpos₀, hone₀, hf_p1]
      have hpos_s : pos < s.length := hlen_s ▸ hlt
      have hfit_tot : Fits w (s.sum + δ) := hf_sum_add hpos_s
      have hcells : ∀ k, pos + 1 ≤ k → k ≤ n → x₁.mem (b + (k - 1)) ≤ s.sum := by
        intro k hk1 hk2
        have hlt_sz : k - 1 < (treeOfMem b n x.mem).tree.size := by
          rw [size_tree_treeOfMem]
          omega
        have hle := hr.valid_tree.getElem_le_sum hlt_sz
        dsimp only [x₁, x₀, Data.set]
        simpa only [getElem_treeOfMem] using hle
      obtain ⟨y, hy_loop, hy_tree, hy_mod, hy_b, hy_sz, hy_fr⟩ :=
        updateLoop_spec (w := w) (b := b) (n := n) (m := pos + 1) (δ := δ) (S := s.sum)
          (x := x₁) rfl rfl hr.base_eq hr.size_eq rfl hdelta_reg
          (by omega) (by omega) hfit_addr hfit_tot hcells
      have hup_le : (upChain n (pos + 1)).length ≤ Nat.clog 2 (s.length + 1) := by
        rw [hlen_s]
        exact length_upChain_le_clog n (pos + 1)
      have hfull_w : ExecWithin w opCode x y (charge s (.add pos δ)) :=
        (hpre.seq (((hset_idx.seq hy_loop).branch_pos hcond_pos).branch_pos hcond_tag)).mono
          (by simp only [charge]; omega)
      obtain ⟨t, ht, hfull⟩ := hfull_w
      have htree_eq : treeOfMem b n y.mem = FenwickTree.add (treeOfMem b n x.mem) pos δ := by
        unfold FenwickTree.add
        have hlt' : pos < (treeOfMem b n x.mem).tree.size := by
          simpa only [size_tree_treeOfMem] using hlt
        simp only [hlt', ↓reduceIte]
        cases h : treeOfMem b n y.mem with
        | mk arr =>
          simp only [h] at hy_tree
          rw [size_tree_treeOfMem]
          exact congrArg FenwickTree.mk hy_tree
      have hvalid_y : Valid (treeOfMem b n y.mem) (PrefixSums.addAt s pos δ) := by
        rw [htree_eq]
        exact valid_add hr.valid_tree pos δ
      have hsum_y : Fits w (PrefixSums.addAt s pos δ).sum := by
        rwa [sum_addAt_of_lt δ hpos_s]
      exact ⟨y, t, hfull, rfl,
        ⟨hfull.within.bounded hr.bounded, hy_b, hy_sz, hsum_y, hvalid_y⟩,
        hy_mod, hy_fr, ht⟩
    · have hcond_pos : ¬ (Cond.lt rPos rLen).Holds x₀ := by
        simp +decide [Cond.Holds, x₀, hpos_reg, hr.size_eq]
        omega
      let y := x₀.set rIdx 0
      have helse : ExecWithin w (ram_exact[rIdx ← #0] : Code .exact 12) x₀ y 1 := by
        ram_exact_eval [y]
      have hfull_w : ExecWithin w opCode x y (charge s (.add pos δ)) :=
        (hpre.seq ((helse.branch_neg hcond_pos).branch_pos hcond_tag)).mono
          (by simp only [charge]; omega)
      obtain ⟨t, ht, hfull⟩ := hfull_w
      have hadd_noop : PrefixSums.addAt s pos δ = s :=
        PrefixSums.addAt_of_length_le δ (by omega)
      refine ⟨y, t, hfull, rfl, ?_, Modifies.refl _ _, rfl, ht⟩
      change Rep b n w (PrefixSums.addAt s pos δ) y
      rw [hadd_noop]
      exact ⟨hfull.within.bounded hr.bounded, hr.base_eq, hr.size_eq, hr.sum_fits, hr.valid_tree⟩
  | sum len =>
    obtain ⟨htag, hlen_reg⟩ := harg
    have hcond_tag : ¬ (Cond.eq rTag rZero).Holds x₀ := by
      simp +decide [Cond.Holds, x₀, htag]
    let m := min len n
    let x₁ := x₀.set rIdx m
    have hclamp : ExecWithin w
        (ram_exact[if rLen < rPos then [rIdx ← rLen] else [rIdx ← rPos]] : Code .exact 12)
        x₀ x₁ 3 := by
      have hsz₀ : x₀.regs rLen = n := hr.size_eq
      have harg₀ : x₀.regs rPos = len := hlen_reg
      by_cases hgt : n < len
      · have hm_eq : m = n := Nat.min_eq_right (Nat.le_of_lt hgt)
        ram_exact_eval [x₁, hm_eq, hsz₀, harg₀, hgt]
      · have hm_eq : m = len := Nat.min_eq_left (Nat.le_of_not_gt hgt)
        ram_exact_eval [x₁, hm_eq, hsz₀, harg₀, hgt]
    have hfit_take : Fits w (0 + (s.take m).sum) := by
      refine hr.sum_fits.of_le ?_
      conv_rhs => rw [← List.take_append_drop m s, List.sum_append]
      omega
    obtain ⟨y, hy_q, hy_ans, hy_b, hy_sz, hy_fr, hy_mem⟩ :=
      queryLoop_spec (w := w) (b := b) (n := n) (m := m) (a := 0) (x := x₁) hr.valid_tree
        rfl rfl hr.base_eq rfl rfl (Nat.min_le_right len n) hfit_addr hfit_take
    have hdown_le : (downChain m).length ≤ Nat.clog 2 (s.length + 1) := by
      rw [hlen_s]
      exact length_downChain_le_clog (Nat.min_le_right len n)
    have hfull_w : ExecWithin w opCode x y (charge s (.sum len)) :=
      (hpre.seq ((hclamp.seq hy_q).branch_neg hcond_tag)).mono (by simp only [charge]; omega)
    obtain ⟨t, ht, hfull⟩ := hfull_w
    have htake_eq : (s.take m).sum = (s.take len).sum := by
      dsimp only [m]
      rcases le_or_gt len n with hle | hgt
      · rw [Nat.min_eq_left hle]
      · rw [Nat.min_eq_right (Nat.le_of_lt hgt), ← hlen_s, List.take_length,
          List.take_of_length_le (by omega)]
    refine ⟨y, t, hfull, ?_,
      ⟨hfull.within.bounded hr.bounded, hy_b, hy_sz.trans hr.size_eq,
        hr.sum_fits, hy_mem.symm ▸ hr.valid_tree⟩,
      hy_mem ▸ Modifies.refl _ _, hy_fr, ht⟩
    change some (y.regs rAns) = some (s.take len).sum
    rw [hy_ans, zero_add, htake_eq]

/-- Unified `WordRAM.StateTransitionImpl` certificate over `Basis.exact` for Fenwick-tree dynamic
prefix sums of length `n` starting from `List.replicate n 0`. -/
def impl {w b n : ℕ} (hw : 0 < w) (hfit_addr : Fits w (b + n)) :
    Cslib.DataStructure.WordRAM.StateTransitionImpl subroutineCode (spec w) w b ![n]
      (List.replicate n 0) :=
  Cslib.DataStructure.WordRAM.StateTransitionImpl.ofFn
    (space := n) (spanTime := 2) (setupTime := 1) (initPotential := 0)
    (charge := charge)
    (rep := Rep b n w)
    (potential := fun _ => 0)
    (encode := encodeOp)
    (argMatch := argMatch)
    (decode := decodeOp)
    (bounded := Rep.bounded)
    (arguments_fit := by
      intro s o hv i _
      cases o with
      | add pos δ =>
        obtain ⟨hpos, hδ, _⟩ := hv
        simp only [encodeOp]
        split_ifs
        · exact fits_zero w
        · exact hpos
        · exact hδ
        · exact fits_zero w
      | sum len =>
        simp only [encodeOp]
        split_ifs
        · exact fits_one (Nat.ne_of_gt hw)
        · exact hv
        · exact fits_zero w)
    (encode_matches := by
      intro o regs
      cases o <;> simp +decide [argMatch, encodeOp])
    (rep_supported := by
      intro s x x' hreg hmem hbdd hr
      refine ⟨hbdd, ?_, ?_, hr.sum_fits, ?_⟩
      · exact (hreg rBase rfl).trans hr.base_eq
      · exact (hreg rLen rfl).trans hr.size_eq
      · rw [treeOfMem_congr hmem]
        exact hr.valid_tree)
    (potential_supported := fun _ _ _ => rfl)
    (clear_nodup := by decide)
    (params_not_clear := fun j => by fin_cases j; decide)
    (incCur_eval := fun {x} h1 hfit => by
      change x.regs rOne = 1 at h1
      change Data.put w x rAns (x.regs rAns + x.regs rOne) = some (x.set rAns (x.regs rAns + 1))
      rw [h1]
      exact Data.put_of_fits hfit)
    (span_exec := fun {x} _ hfr hpar => by
      change x.regs rFrontier = b at hfr
      have hn_reg : x.regs rLen = n := hpar 0
      refine ⟨(x.set rBase b).set rFrontier (b + n), ?_, rfl,
        by simp +decide [subroutineCode], by simp +decide [subroutineCode], ?_⟩
      · ram_exact_eval [subroutineCode, allocSpanCode, hfr, hn_reg, hfit_addr]
      · intro j
        fin_cases j
        simpa +decide [subroutineCode] using hn_reg)
    (setup_exec := fun {x₁} hbdd₁ hb₁ hfr₁ hpar₁ hzero => by
      have hn₁ : x₁.regs rLen = n := hpar₁ 0
      refine ⟨x₁.set rZero 0, ?_, by simpa +decide [subroutineCode] using hfr₁, ?_,
        Nat.le_refl 0, Modifies.refl _ _⟩
      · ram_exact_eval [subroutineCode, initSetupCode]
      · refine ⟨hbdd₁.set (fits_zero w),
          by simpa +decide [subroutineCode] using hb₁,
          by simpa +decide [subroutineCode] using hn₁,
          by simp only [List.sum_replicate, smul_zero, fits_zero],
          ?_⟩
        change Valid (treeOfMem b n x₁.mem) (List.replicate n 0)
        rw [treeOfMem_zeros hzero]
        exact valid_zeros n)
    (step_exec := fun o hr hv harg => by
      obtain ⟨y, t, he, hdec, hrep, hmod, _, ht⟩ := opCode_spec hw hfit_addr o hr hv harg
      exact ⟨y, t, he, hdec, hrep, hmod, by omega⟩)

/-- Standard-basis Fenwick-tree `WordRAM.StateTransitionImpl`, lifted from `Basis.exact`. -/
abbrev implStandard {w b n : ℕ} (hw : 0 < w) (hfit_addr : Fits w (b + n)) :
    Cslib.DataStructure.WordRAM.StateTransitionImpl subroutineCode.toStandard (spec w) w b ![n]
      (List.replicate n 0) :=
  (impl hw hfit_addr).toStandard

/-- Canonical native result format for `PrefixSums.Op.Result ℕ`. -/
def resultType : PrefixSums.Op ℕ → ResultType
  | .add _ _ => .unit
  | .sum _ => .nat

theorem resultType_eq (o : PrefixSums.Op ℕ) :
    PrefixSums.Op.Result ℕ o = (resultType o).Value := by
  cases o <;> rfl

/-- Paid 1-instruction canonical result recoding for standalone `DynamicProgram` projection. -/
def recoding {w b n : ℕ} (hw : 0 < w) (hfit_addr : Fits w (b + n)) :
    NativeResultRecoding (PrefixSums.Op.Result ℕ) .standard 12 w
      (implStandard hw hfit_addr).decode (implStandard hw hfit_addr).rep
      (implStandard hw hfit_addr).potential :=
  NativeResultRecoding.ofCanonical rAns (fun _ => rAns) resultType resultType_eq
    fun {s x} o a _ hd => by
      cases o with
      | add pos δ =>
        cases a
        rfl
      | sum len =>
        change some (x.regs rAns) = some a at hd
        cases hd
        rfl

/-- Standalone `DynamicCertificate` over `Basis.standard` for Fenwick-tree dynamic prefix sums. -/
def certificate {w b n : ℕ} (hw : 0 < w) (hfit_addr : Fits w (b + n)) :
    DynamicCertificate (D := spec w)
      ((implStandard hw hfit_addr).toDynamicProgram (recoding hw hfit_addr)) w :=
  (implStandard hw hfit_addr).toCertificate (recoding hw hfit_addr) (fun _ _ _ _ => trivial)

/-- Worst-case instruction bound `13 * Nat.clog 2 (s.length + 1) + 12` per `DynamicProgram` call
(including 1-instruction canonical recoding and final `halt`). -/
theorem instruction_bound {w b n : ℕ} (hw : 0 < w) (hfit_addr : Fits w (b + n)) :
    DataStructure.Bound (certificate hw hfit_addr).impl
      DynamicProgram.OperationTrace.instructions
      (fun s _ => 13 * Nat.clog 2 (s.length + 1) + 12) :=
  (implStandard hw hfit_addr).toBound (recoding hw hfit_addr) (fun _ _ _ _ => trivial)
    (fun _ => rfl)

/-- Every admissible adaptive client executes on the Word-RAM Fenwick tree from any valid
representation `Rep b n w s x` (whether zero-initialized or constructed in `O(n)` instructions by
`buildCode_spec`), returning `(spec w).clientResult s p` in at most
`history.length * (13 * Nat.clog 2 (s.length + 1) + 12)` total instructions. -/
theorem client_spec {w b n : ℕ} (hw : 0 < w) (hfit_addr : Fits w (b + n))
    {β : Type*} (p : (spec w).Client β) {s : List ℕ} {x : Data 12}
    (hr : Rep b n w s x) (hv : (spec w).ValidHistory s ((spec w).clientHistory s p)) :
    ∃ y traces,
      DataStructure.Executes
        (((implStandard hw hfit_addr).toDynamicProgram (recoding hw hfit_addr)).ExecOp w)
        p x ((spec w).clientResult s p) y traces ∧
      Rep b n w ((spec w).clientState s p) y ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces ≤
        ((spec w).clientHistory s p).length * (13 * Nat.clog 2 (s.length + 1) + 12) := by
  obtain ⟨y, traces, he, hy, htot⟩ :=
    (implStandard hw hfit_addr).run_client_bound (recoding hw hfit_addr)
      (fun _ _ _ _ => trivial) (fun _ => rfl) p hr hv
  refine ⟨y, traces, he, hy, ?_⟩
  have heq := totalCost_charge_add w 2 s ((spec w).clientHistory s p)
  exact htot.trans (le_of_eq heq)

/-! ## `O(n)` in-place Word-RAM immediate-parent construction (`buildCode`) -/

/-- Single immediate-parent propagation iteration (`m = rIdx + 1`): adds `mem[rBase + rIdx]` into
`mem[rBase + (m + lowbit m - 1)]` when `m + lowbit m ≤ rLen`, then increments `rIdx`. -/
def buildBody : Code .exact 12 := ram_exact[
  rAns ← rIdx + rOne;
  rTmp1 ← rAns &&& rIdx;
  rTmp1 ← rAns - rTmp1;
  rTmp2 ← rLen - rAns;
  if rTmp2 < rTmp1 then [
    rZero ← #0
  ] else [
    rTmp1 ← rAns + rTmp1;
    rTmp1 ← rTmp1 - rOne;
    rTmp1 ← rBase + rTmp1;
    rTmp2 ← rBase + rIdx;
    rTmp2 ← *rTmp2;
    rAns ← *rTmp1;
    rAns ← rAns + rTmp2;
    *rTmp1 ← rAns
  ];
  rIdx ← rIdx + rOne ]

/-- In-place `O(n)` Fenwick-tree construction over `Basis.exact`: transforms an array of `n` raw
values in `[rBase, rBase + n)` into its Fenwick tree (`ofList s`). -/
def buildCode : Code .exact 12 := ram_exact[
  rZero ← #0;
  rOne ← #1;
  rIdx ← #0;
  while rIdx < rLen do [⟪buildBody⟫] ]

/-- Post-iteration machine state of `buildBody` at `0`-based counter `j < n` (`m = j + 1`). -/
private def buildNext (x : Data 12) (b n j : ℕ) : Data 12 :=
  let m := j + 1
  let a := m &&& j
  let lb := m - a
  let rem := n - m
  let y := (((x.set rAns m).set rTmp1 a).set rTmp1 lb).set rTmp2 rem
  let z :=
    if rem < lb then
      y.set rZero 0
    else
      let p := m + lb
      let vm := x.mem (b + j)
      let vp := x.mem (b + (p - 1))
      ((((((((y.set rTmp1 p).set rTmp1 (p - 1)).set rTmp1 (b + (p - 1))).set rTmp2 (b + j)).set
        rTmp2 vm).set rAns vp).set rAns (vp + vm)).write (b + (p - 1)) (vp + vm))
  z.set rIdx (j + 1)

private theorem buildBody_exec {w b n j : ℕ} {s : List ℕ} {x : Data 12}
    (ho : x.regs rOne = 1) (hb : x.regs rBase = b) (hsz : x.regs rLen = n)
    (hj_reg : x.regs rIdx = j) (hj_lt : j < n)
    (hfit_addr : Fits w (b + n)) (hfit_sum : Fits w s.sum)
    (hinv : BuildInv s (j + 1) (treeOfMem b n x.mem).tree) :
    ExecWithin w buildBody x (buildNext x b n j) 15 := by
  have hm1 : 1 ≤ j + 1 := by omega
  have hmn : j + 1 ≤ n := by omega
  have hlen_s : s.length = n := by
    simpa only [size_tree_treeOfMem] using hinv.size_eq.symm
  have hand_eq : (j + 1) &&& j = (j + 1) - lowbit (j + 1) := by
    simpa only [Nat.add_sub_cancel] using and_pred_eq_sub_lowbit (j + 1)
  have hand_le : (j + 1) &&& j ≤ j + 1 := by rw [hand_eq]; omega
  have hlb_eq : (j + 1) - ((j + 1) &&& j) = lowbit (j + 1) := by
    simpa only [Nat.add_sub_cancel] using sub_and_pred_eq_lowbit (j + 1)
  have hlb_pos : 0 < lowbit (j + 1) := lowbit_pos hm1
  have hf_m : Fits w (j + 1) := hfit_addr.of_le (by omega)
  have hf_and : Fits w ((j + 1) &&& j) := hfit_addr.of_le (by omega)
  have hf_lb : Fits w ((j + 1) - ((j + 1) &&& j)) := hfit_addr.of_le (by omega)
  have hf_rem : Fits w (n - (j + 1)) := hfit_addr.of_le (by omega)
  by_cases hlt : n - (j + 1) < (j + 1) - ((j + 1) &&& j)
  · ram_exact_eval [buildBody, buildNext, ho, hb, hsz, hj_reg,
      hand_le, hmn, hlt, hf_m, hf_and, hf_lb, hf_rem]
  · have hp_le : (j + 1) + lowbit (j + 1) ≤ n := by omega
    have hp_le_s : (j + 1) + lowbit (j + 1) ≤ s.length := hlen_s ▸ hp_le
    have hsum_le : x.mem (b + ((j + 1) + lowbit (j + 1) - 1)) + x.mem (b + j) ≤ s.sum := by
      have h := hinv.parent_add_le_sum hm1 (hlen_s ▸ hmn) hp_le_s
      simpa only [getElem_treeOfMem, Nat.add_sub_cancel] using h
    have hp1 : 1 ≤ (j + 1) + ((j + 1) - ((j + 1) &&& j)) := by omega
    have hf_p : Fits w ((j + 1) + ((j + 1) - ((j + 1) &&& j))) := hfit_addr.of_le (by omega)
    have hf_pm1 : Fits w ((j + 1) + ((j + 1) - ((j + 1) &&& j)) - 1) := hfit_addr.of_le (by omega)
    have hf_addr_p : Fits w (b + ((j + 1) + ((j + 1) - ((j + 1) &&& j)) - 1)) :=
      hfit_addr.of_le (by omega)
    have hf_addr_j : Fits w (b + j) := hfit_addr.of_le (by omega)
    have hf_add_val :
        Fits w (x.mem (b + ((j + 1) + ((j + 1) - ((j + 1) &&& j)) - 1)) + x.mem (b + j)) :=
      hfit_sum.of_le (by rwa [hlb_eq])
    ram_exact_eval [buildBody, buildNext, ho, hb, hsz, hj_reg,
      hand_le, hmn, hlt, hp1, hf_m, hf_and, hf_lb, hf_rem,
      hf_p, hf_pm1, hf_addr_p, hf_addr_j, hf_add_val]

/-- In-place immediate-parent propagation `buildCode` transforms raw entries `s` in
`[b, b + s.length)` into a valid `Rep b s.length w s y` (whose memory equals `ofList s`) within
`17 * s.length + 5` exact-basis instructions, preserving outside memory and persistent registers. -/
theorem buildCode_spec {w b : ℕ} {s : List ℕ} {x : Data 12}
    (hw : 0 < w) (hfit_addr : Fits w (b + s.length)) (hfit_sum : Fits w s.sum)
    (hbdd : x.Bounded w) (hb : x.regs rBase = b) (hsz : x.regs rLen = s.length)
    (hmem : ∀ i (hi : i < s.length), x.mem (b + i) = s[i]) :
    ∃ y, ExecWithin w buildCode x y (17 * s.length + 5) ∧
      Rep b s.length w s y ∧
      treeOfMem b s.length y.mem = ofList s ∧
      Modifies (Block.mk b s.length).footprint x.mem y.mem ∧
      y.regs rFrontier = x.regs rFrontier := by
  set n := s.length
  have hf1 : Fits w 1 := fits_one (Nat.ne_of_gt hw)
  let x₀ := ((x.set rZero 0).set rOne 1).set rIdx 0
  have hsetup :
      ExecWithin w (ram_exact[rZero ← #0; rOne ← #1; rIdx ← #0] : Code .exact 12) x x₀ 3 := by
    ram_exact_eval [x₀, hf1]
  have htree_init : (treeOfMem b n x₀.mem).tree = s.toArray := by
    refine Array.ext (by simp [n]) fun i hi₁ hi₂ => ?_
    simp only [size_tree_treeOfMem] at hi₁
    simp only [getElem_treeOfMem, x₀, List.getElem_toArray]
    exact hmem i hi₁
  let P (j : ℕ) (z : Data 12) : Prop :=
    z.regs rOne = 1 ∧ z.regs rBase = b ∧ z.regs rLen = n ∧
      z.regs rFrontier = x.regs rFrontier ∧
      Modifies (Block.mk b n).footprint x.mem z.mem ∧
      BuildInv s (j + 1) (treeOfMem b n z.mem).tree
  have hP0 : P (x₀.regs rIdx) x₀ := by
    have hidx0 : x₀.regs rIdx = 0 := rfl
    rw [hidx0]
    refine ⟨rfl, hb, hsz, rfl, Modifies.refl _ _, ?_⟩
    rw [htree_init]
    simpa only [List.toList_toArray] using buildInv_init s.toArray
  obtain ⟨y, hy_loop, hPn, _⟩ := ExecWithin.loop_count (w := w) (N := n) (T := 15)
    (index := rIdx) (limit := rLen) (body := buildBody) P
    (fun z hz => hz.2.2.1)
    (fun z hz hj_lt => by
      obtain ⟨ho_z, hb_z, hsz_z, hfr_z, hmod_z, hinv_z⟩ := hz
      set j := z.regs rIdx
      have he_b := buildBody_exec ho_z hb_z hsz_z rfl hj_lt hfit_addr hfit_sum hinv_z
      let z' := buildNext z b n j
      have ho' : z'.regs rOne = 1 := by dsimp only [z', buildNext]; split <;> exact ho_z
      have hb' : z'.regs rBase = b := by dsimp only [z', buildNext]; split <;> exact hb_z
      have hsz' : z'.regs rLen = n := by dsimp only [z', buildNext]; split <;> exact hsz_z
      have hfr' : z'.regs rFrontier = x.regs rFrontier := by
        dsimp only [z', buildNext]; split <;> exact hfr_z
      have hidx' : z'.regs rIdx = j + 1 := rfl
      have hlb_eq : (j + 1) - ((j + 1) &&& j) = lowbit (j + 1) := by
        simpa only [Nat.add_sub_cancel] using sub_and_pred_eq_lowbit (j + 1)
      have hstep_inv := hinv_z.step (by omega : 1 ≤ j + 1) (by omega : j + 1 ≤ s.length)
      by_cases hlt : n - (j + 1) < (j + 1) - ((j + 1) &&& j)
      · have hp_not : ¬ (j + 1 + lowbit (j + 1) ≤ s.length) := by omega
        simp only [hp_not, ↓reduceIte] at hstep_inv
        have hmem_eq : z'.mem = z.mem := by
          dsimp only [z', buildNext]
          rw [ite_eq_left_iff.mpr fun h => (h hlt).elim]
          rfl
        exact ⟨z', he_b, ⟨ho', hb', hsz', hfr', hmem_eq ▸ hmod_z, hmem_eq ▸ hstep_inv⟩, hidx'⟩
      · have hp_le : j + 1 + lowbit (j + 1) ≤ s.length := by omega
        simp only [hp_le, ↓reduceIte] at hstep_inv
        set p := j + 1 + lowbit (j + 1)
        have hp_gt : j + 1 < p := by
          have := lowbit_pos (by omega : 0 < j + 1)
          omega
        have hmem_eq : z'.mem =
            Function.update z.mem (b + (p - 1)) (z.mem (b + (p - 1)) + z.mem (b + j)) := by
          dsimp only [z', buildNext]
          rw [ite_eq_right_iff.mpr fun h => (hlt h).elim]
          dsimp only [Data.set, Data.write, p]
          rw [hlb_eq]
        have hmod_step : Modifies (Block.mk b n).footprint z.mem z'.mem := fun a ha => by
          rw [hmem_eq, Function.update_of_ne]
          exact fun heq => ha (by simp only [Block.mem_footprint, Block.Owns]; omega)
        have htree_eq : (treeOfMem b n z'.mem).tree =
            (treeOfMem b n z.mem).tree.modify (p - 1)
              (· + (treeOfMem b n z.mem).tree[j]'(by rw [size_tree_treeOfMem]; omega)) := by
          rw [hmem_eq]
          simpa only [getElem_treeOfMem] using tree_treeOfMem_update_add (idx := p - 1)
        refine ⟨z', he_b, ⟨ho', hb', hsz', hfr',
          fun a ha => (hmod_step a ha).trans (hmod_z a ha), ?_⟩, hidx'⟩
        simpa only [Nat.add_sub_cancel, htree_eq] using hstep_inv)
    (Nat.zero_le n) hP0
  have hfull : ExecWithin w buildCode x y (17 * n + 5) := by
    change ExecWithin w (.seq (.op (.const rZero 0)) (.seq (.op (.const rOne 1))
      (.seq (.op (.const rIdx 0)) _))) x y _
    obtain ⟨k, hk, he_s⟩ := hsetup
    cases he_s with
    | seq h1 hrest =>
      cases hrest with
      | seq h2 h3 =>
        refine (h1.within.seq (h2.within.seq (h3.within.seq hy_loop))).mono ?_
        have hidx0 : x₀.regs rIdx = 0 := rfl
        rw [hidx0]
        omega
  obtain ⟨_, hb_y, hsz_y, hfr_y, hmod_y, hinv_n⟩ := hPn
  have hvalid_y : Valid (treeOfMem b n y.mem) s := hinv_n.to_valid
  have hrep_y : Rep b n w s y := ⟨hfull.bounded hbdd, hb_y, hsz_y, hfit_sum, hvalid_y⟩
  exact ⟨y, hfull, hrep_y, hvalid_y.unique (valid_ofList s), hmod_y, hfr_y⟩

end WordRAM

end Cslib.DataStructure.FenwickTree
