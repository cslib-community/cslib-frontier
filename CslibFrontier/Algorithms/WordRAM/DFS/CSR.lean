/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.DFS.SCC
public import CslibFrontier.Computability.WordRAM.Allocation
public import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec
import Mathlib.Algebra.BigOperators.Fin

/-!
# CSR graph representation, scratch layout, and word-RAM CSR primitives

Register allocation (`Reg`), scratch memory layout (`kOffAddr`..`kTopAddr`), compressed sparse
row predicates (`csrOffset`, `CSRAt`, `PartialCSRAt`), and shared array/CSR subroutines
(`zeroBlockCode`, `incCurCode`, `prefixSumCode`, `backfillStepCode`).

Shared with `CslibFrontier.Algorithms.WordRAM.TwoSAT`.
-/

public section

namespace Cslib.Algorithms.WordRAM.DFS

open Cslib.WordRAM
open Cslib.Algorithms.Lean.DFS

/-! ### Registers and scratch memory layout -/

namespace Reg
/-- Constant `0`. -/
abbrev cZero : Fin 28 := ⟨0, by decide⟩
/-- Constant `1`. -/
abbrev cOne : Fin 28 := ⟨1, by decide⟩
/-- Constant `3` (words per DFS stack frame). -/
abbrev cThree : Fin 28 := ⟨3, by decide⟩
/-- Vertex count `N`. -/
abbrev nVerts : Fin 28 := ⟨6, by decide⟩
/-- Base address of the CSR offset array being traversed. -/
abbrev offB : Fin 28 := ⟨8, by decide⟩
/-- Base address of the CSR edge array being traversed. -/
abbrev edgeB : Fin 28 := ⟨9, by decide⟩
/-- Base address of the visited-flag array. -/
abbrev visB : Fin 28 := ⟨10, by decide⟩
/-- Base address of the finishing-order output array. -/
abbrev finB : Fin 28 := ⟨11, by decide⟩
/-- Base address of the explicit DFS stack. -/
abbrev stkB : Fin 28 := ⟨12, by decide⟩
/-- Base address of the transpose fill cursors. -/
abbrev curB : Fin 28 := ⟨13, by decide⟩
/-- Base address of the transpose CSR offset array. -/
abbrev revOffB : Fin 28 := ⟨14, by decide⟩
/-- Base address of the transpose CSR edge array. -/
abbrev revEdgeB : Fin 28 := ⟨15, by decide⟩
/-- Base address of the forward finishing order. -/
abbrev ordB : Fin 28 := ⟨16, by decide⟩
/-- Base address of the component-index array. -/
abbrev compB : Fin 28 := ⟨17, by decide⟩
/-- Outer loop counter. -/
abbrev iReg : Fin 28 := ⟨18, by decide⟩
/-- Stack depth or inner loop counter. -/
abbrev pReg : Fin 28 := ⟨19, by decide⟩
/-- Number of finished vertices. -/
abbrev finCnt : Fin 28 := ⟨20, by decide⟩
/-- Current component index. -/
abbrev compIdxReg : Fin 28 := ⟨21, by decide⟩
/-- Finished count before the current root. -/
abbrev oldFinReg : Fin 28 := ⟨22, by decide⟩
/-- Current vertex. -/
abbrev uReg : Fin 28 := ⟨23, by decide⟩
/-- Current successor. -/
abbrev vReg : Fin 28 := ⟨24, by decide⟩
/-- Current edge position. -/
abbrev jReg : Fin 28 := ⟨25, by decide⟩
/-- End of the current edge range. -/
abbrev jEndReg : Fin 28 := ⟨26, by decide⟩
/-- Address scratch register. -/
abbrev addr : Fin 28 := ⟨27, by decide⟩
/-- Output-list header register (end-to-end programs). -/
abbrev outReg : Fin 28 := ⟨7, by decide⟩

end Reg

open Reg

local macro "mem_upd" : tactic =>
  `(tactic| simp only [Data.set_mem, Data.set_mem_apply, Data.write_mem])

/-- Address of the forward CSR offset array in the scratch layout based at `wb`. -/
@[expose] def kOffAddr (wb : ℕ) : ℕ := wb
/-- Address of the forward CSR edge array. -/
@[expose] def kEdgeAddr (wb N : ℕ) : ℕ := wb + N + 1
/-- Address of the transpose CSR offset array. -/
@[expose] def kRevOffAddr (wb N Mc : ℕ) : ℕ := wb + N + 1 + Mc
/-- Address of the transpose CSR edge array. -/
@[expose] def kRevEdgeAddr (wb N Mc : ℕ) : ℕ := wb + 2 * N + 2 + Mc
/-- Address of the transpose fill cursors. -/
@[expose] def kCurAddr (wb N Mc : ℕ) : ℕ := wb + 2 * N + 2 + 2 * Mc
/-- Address of the visited-flag array. -/
@[expose] def kVisAddr (wb N Mc : ℕ) : ℕ := wb + 3 * N + 3 + 2 * Mc
/-- Address of the forward finishing order. -/
@[expose] def kOrdAddr (wb N Mc : ℕ) : ℕ := wb + 4 * N + 3 + 2 * Mc
/-- Address of the second-pass finishing order. -/
@[expose] def kFinAddr (wb N Mc : ℕ) : ℕ := wb + 5 * N + 3 + 2 * Mc
/-- Address of the explicit DFS stack (`3` words per frame). -/
@[expose] def kStkAddr (wb N Mc : ℕ) : ℕ := wb + 6 * N + 3 + 2 * Mc
/-- Address of the component-index array. -/
@[expose] def kCompAddr (wb N Mc : ℕ) : ℕ := wb + 9 * N + 3 + 2 * Mc
/-- First address past the scratch layout. -/
@[expose] def kTopAddr (wb N Mc : ℕ) : ℕ := wb + 10 * N + 3 + 2 * Mc

/-! ### Reusable CSR representation and shared array/CSR primitives -/

/-- Number of arcs leaving vertices below `u`: the CSR offset of vertex `u`. -/
@[expose] def csrOffset {N : ℕ} (adj : Fin N → List (Fin N)) (u : ℕ) : ℕ :=
  (((List.finRange N).take u).map fun w => (adj w).length).sum

@[simp]
theorem csrOffset_zero {N : ℕ} (adj : Fin N → List (Fin N)) :
    csrOffset adj 0 = 0 := rfl

theorem csrOffset_succ {N : ℕ} (adj : Fin N → List (Fin N)) {u : ℕ} (hu : u < N) :
    csrOffset adj (u + 1) = csrOffset adj u + (adj ⟨u, hu⟩).length := by
  rw [csrOffset, List.take_add_one, List.getElem?_eq_getElem (by simpa using hu)]
  simp [csrOffset]

theorem csrOffset_mono {N : ℕ} (adj : Fin N → List (Fin N)) {a b : ℕ} (hab : a ≤ b) :
    csrOffset adj a ≤ csrOffset adj b := by
  obtain ⟨rest, h⟩ := List.take_prefix_take_left (l := List.finRange N) hab
  unfold csrOffset
  rw [← h, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

private theorem csrOffset_add_lt {N : ℕ} (adj : Fin N → List (Fin N)) (u : Fin N)
    {k : ℕ} (hk : k < (adj u).length) : csrOffset adj u.val + k < csrOffset adj N := by
  refine (Nat.add_lt_add_left hk _).trans_le ?_
  rw [← csrOffset_succ adj u.isLt]
  exact csrOffset_mono adj u.isLt

theorem csrOffset_eq_outDegreeSum {N : ℕ} (adj : Fin N → List (Fin N)) :
    csrOffset adj N = outDegreeSum adj (List.finRange N) := by
  unfold csrOffset outDegreeSum
  rw [List.take_of_length_le (by simp)]

/-- `adj` is stored in CSR form: offsets at `offBase`, successor lists at `edgeBase`. -/
@[expose] def CSRAt {N : ℕ} (adj : Fin N → List (Fin N)) (offBase edgeBase : ℕ)
    (mem : ℕ → ℕ) : Prop :=
  (∀ u ≤ N, mem (offBase + u) = csrOffset adj u) ∧
    ∀ (u : Fin N) (k : ℕ) (hk : k < (adj u).length),
      mem (edgeBase + csrOffset adj u.val + k) = ((adj u)[k]).val

private theorem CSRAt.of_eqOn {N : ℕ} {adj : Fin N → List (Fin N)} {offBase edgeBase : ℕ}
    {mem₁ mem₂ : ℕ → ℕ} (h : CSRAt adj offBase edgeBase mem₁)
    (hoff : ∀ u ≤ N, mem₂ (offBase + u) = mem₁ (offBase + u))
    (hedge : ∀ e < csrOffset adj N, mem₂ (edgeBase + e) = mem₁ (edgeBase + e)) :
    CSRAt adj offBase edgeBase mem₂ := by
  refine ⟨fun u hu => (hoff u hu).trans (h.1 u hu), fun u k hk => ?_⟩
  rw [Nat.add_assoc, hedge _ (csrOffset_add_lt adj u hk), ← Nat.add_assoc]
  exact h.2 u k hk

/-- Invariant of the backward CSR fill: the successor lists `part` written so far end at the cursors
`curBase`. -/
@[expose] def PartialCSRAt {N : ℕ} (targetAdj part : Fin N → List (Fin N))
    (curBase edgeBase : ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ w : Fin N, (part w).length ≤ (targetAdj w).length) ∧
    (∀ w : Fin N, mem (curBase + w.val) + (part w).length = csrOffset targetAdj (w.val + 1)) ∧
    ∀ (w : Fin N) (k : ℕ) (hk : k < (part w).length),
      mem (edgeBase + mem (curBase + w.val) + k) = ((part w)[k]).val

-- The cursor leaves one position for every successor still to be written.
private theorem PartialCSRAt.cursor_eq {N : ℕ} {targetAdj part : Fin N → List (Fin N)}
    {curBase edgeBase : ℕ} {mem : ℕ → ℕ} (hp : PartialCSRAt targetAdj part curBase edgeBase mem)
    (u : Fin N) :
    mem (curBase + u.val) =
      csrOffset targetAdj u.val + ((targetAdj u).length - (part u).length) := by
  refine Nat.add_right_cancel (m := (part u).length) ?_
  simpa only [csrOffset_succ targetAdj u.isLt, Fin.eta, Nat.add_assoc,
    Nat.sub_add_cancel (hp.1 u)] using hp.2.1 u

private theorem PartialCSRAt.edge_in_row {N : ℕ} {targetAdj part : Fin N → List (Fin N)}
    {curBase edgeBase : ℕ} {mem : ℕ → ℕ} (hp : PartialCSRAt targetAdj part curBase edgeBase mem)
    (u : Fin N) {k : ℕ} (hk : k < (part u).length) :
    csrOffset targetAdj u.val ≤ mem (curBase + u.val) + k ∧
      mem (curBase + u.val) + k < csrOffset targetAdj (u.val + 1) := by
  constructor
  · rw [hp.cursor_eq u]
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  · rw [← hp.2.1 u]
    exact Nat.add_lt_add_left hk _

private theorem PartialCSRAt.backfill_bounds {N : ℕ} {targetAdj part : Fin N → List (Fin N)}
    {curBase edgeBase : ℕ} {mem : ℕ → ℕ} (hp : PartialCSRAt targetAdj part curBase edgeBase mem)
    (u : Fin N) (hroom : (part u).length + 1 ≤ (targetAdj u).length) :
    let c := mem (curBase + u.val) - 1
    c + 1 = mem (curBase + u.val) ∧
      csrOffset targetAdj u.val ≤ c ∧ c < csrOffset targetAdj (u.val + 1) := by
  dsimp only
  have hbefore : csrOffset targetAdj u.val < mem (curBase + u.val) := by
    rw [hp.cursor_eq u]
    exact Nat.lt_add_of_pos_right (Nat.sub_pos_of_lt hroom)
  have hpos := (Nat.zero_le _).trans_lt hbefore
  refine ⟨Nat.sub_add_cancel hpos, Nat.le_pred_of_lt hbefore, ?_⟩
  rw [← hp.2.1 u]
  exact (Nat.sub_lt hpos Nat.zero_lt_one).trans_le (Nat.le_add_right _ _)

theorem partialCSRAt_init {N : ℕ} (targetAdj : Fin N → List (Fin N))
    (curBase edgeBase : ℕ) (mem : ℕ → ℕ)
    (hcur : ∀ w : Fin N, mem (curBase + w.val) = csrOffset targetAdj (w.val + 1)) :
    PartialCSRAt targetAdj (fun _ => []) curBase edgeBase mem :=
  ⟨fun _ => Nat.zero_le _, fun w => by simp [hcur w], fun _ _ hk => by simp at hk⟩

theorem csrAt_of_partialCSRAt {N : ℕ} (targetAdj : Fin N → List (Fin N))
    (offBase curBase edgeBase : ℕ) (mem : ℕ → ℕ)
    (hoff : ∀ u ≤ N, mem (offBase + u) = csrOffset targetAdj u)
    (hp : PartialCSRAt targetAdj targetAdj curBase edgeBase mem) :
    CSRAt targetAdj offBase edgeBase mem := by
  refine ⟨hoff, fun u k hk => ?_⟩
  simpa only [hp.cursor_eq u, Nat.sub_self, Nat.add_zero] using hp.2.2 u k hk

/-- Zero `[baseReg, baseReg + nVerts)` in `4 * N + 4` instructions via `Cslib.WordRAM.zeroFill`. -/
def zeroBlockCode (baseReg : Fin 28) : Code .standard 28 :=
  (ram[ addr ← baseReg; jEndReg ← baseReg + nVerts ]).seq
    (zeroFill addr jEndReg cZero cOne)

theorem zeroBlockCode_spec {w : ℕ} (baseReg : Fin 28) (hbr : baseReg.val < 18)
    (B N : ℕ) (hfit : Fits w (B + N)) {x : Data 28}
    (hc0 : x.regs cZero = 0) (hc1 : x.regs cOne = 1)
    (hB : x.regs baseReg = B) (hN : x.regs nVerts = N) :
    ∃ y, ExecWithin w (zeroBlockCode baseReg) x y (4 * N + 4) ∧
      (∀ i < N, y.mem (B + i) = 0) ∧
      (∀ a, ¬ (B ≤ a ∧ a < B + N) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  let x₁ := (x.set addr B).set jEndReg (B + N)
  have hprep : ExecWithin (B := .standard) w
      (ram[ addr ← baseReg; jEndReg ← baseReg + nVerts ]) x x₁ 2 := by
    wram_exec [hB, hN, hfit]
  have hx₁_addr : x₁.regs addr = B := by wram_simp [x₁]
  have hx₁_stop : x₁.regs jEndReg = B + N := by wram_simp [x₁]
  have hzf := zeroFill_exec (w := w) (cur := addr) (stop := jEndReg) (zero := cZero) (one := cOne)
    (x := x₁) (by decide) (by decide) (by decide) (by wram_simp [x₁, hc0]) (by wram_simp [x₁, hc1])
    (by rw [hx₁_addr, hx₁_stop]; omega) (by rw [hx₁_stop]; exact hfit)
  rw [hx₁_addr, hx₁_stop, Nat.add_sub_cancel_left] at hzf
  refine ⟨_, (hprep.seq hzf.within).mono (by omega),
    fun i hi => clear_of_owns ⟨Nat.le_add_right B i, Nat.add_lt_add_left hi B⟩,
    fun a ha => clear_of_not_owns ha, fun r hr => ?_⟩
  have hne : r ≠ addr := fun h => absurd (h ▸ hr) (by decide)
  simp only [Function.update_of_ne hne]
  wram_simp [x₁]

/-- `zeroBlockCode baseReg` does not read the word width. -/
theorem not_readsWidth_zeroBlockCode (baseReg : Fin 28) :
    ¬ (zeroBlockCode baseReg).ReadsWidth := by
  revert baseReg; decide +kernel

/-- `zeroBlockCode baseReg` is `rand`-free. -/
theorem isRandFree_zeroBlockCode (baseReg : Fin 28) :
    (zeroBlockCode baseReg).IsRandFree := by
  revert baseReg; decide +kernel

/-- Increment `mem[curB + vReg]` by `1` in `4` instructions. -/
def incCurCode : Code .standard 28 := ram[
  addr ← curB + vReg; jEndReg ← *addr; jEndReg ← jEndReg + cOne; *addr ← jEndReg ]

/-- `incCurCode` does not read the word width. -/
theorem not_readsWidth_incCurCode : ¬ incCurCode.ReadsWidth := by decide +kernel

/-- `incCurCode` is `rand`-free. -/
theorem isRandFree_incCurCode : incCurCode.IsRandFree := by decide +kernel

theorem incCurCode_spec {N w : ℕ} (curBase maxDeg : ℕ)
    (hfit : Fits w (curBase + N + maxDeg + 1))
    (deg : Fin N → ℕ) (src : Fin N) (hdeg_le : deg src + 1 ≤ maxDeg)
    {x : Data 28} (hc1 : x.regs cOne = 1) (hcur : x.regs curB = curBase)
    (hsrc : x.regs vReg = src.val)
    (hmem : ∀ u : Fin N, x.mem (curBase + u.val) = deg u) :
    ∃ y, ExecWithin w incCurCode x y 4 ∧
      (∀ u : Fin N, y.mem (curBase + u.val) = Function.update deg src (deg src + 1) u) ∧
      (∀ a, ¬ (curBase ≤ a ∧ a < curBase + N) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = x.regs r) := by
  have hlt := src.isLt
  have hm_src := hmem src
  unfold incCurCode
  wram_exec [hc1, hcur, hsrc, hm_src]
  refine ⟨fun u => ?_, fun a ha => ?_, fun r h1 h2 => ?_⟩
  · mem_upd
    by_cases hu : u = src
    · subst hu; simp
    · have hne : curBase + u.val ≠ curBase + src.val := fun h => hu (Fin.ext (by omega))
      simp [Function.update_of_ne hne, Function.update_of_ne hu, hmem u]
  · mem_upd
    exact Function.update_of_ne (by omega) _ _
  · wram_simp [h1, h2]

/-- Compute CSR prefix sums `offB[0..N]` from degrees in `curB[0..N)` and set
`curB[u] := offB[u + 1]` in `9 * N + 5` instructions. -/
private def prefixSumBody : Code .standard 28 := ram[
  addr ← curB + iReg; uReg ← *addr;
  pReg ← pReg + uReg;
  *addr ← pReg;
  iReg ← iReg + cOne;
  addr ← offB + iReg; *addr ← pReg ]

/-- Prefix sums turning out-degrees at `offB` into CSR offsets and fill cursors. -/
def prefixSumCode : Code .standard 28 :=
  (ram[ *offB ← cZero; pReg ← cZero; iReg ← cZero ]).seq
    (.loop (.lt iReg nVerts) prefixSumBody)

/-- `prefixSumCode` does not read the word width. -/
theorem not_readsWidth_prefixSumCode : ¬ prefixSumCode.ReadsWidth := by decide +kernel

/-- `prefixSumCode` is `rand`-free. -/
theorem isRandFree_prefixSumCode : prefixSumCode.IsRandFree := by decide +kernel

theorem prefixSumCode_spec {N w : ℕ} (targetAdj : Fin N → List (Fin N))
    (degBase offBase Mc : ℕ) (hdisj : offBase + N + 1 ≤ degBase)
    (hmc : csrOffset targetAdj N ≤ Mc)
    (hfit : Fits w (degBase + N + Mc + 2))
    {x : Data 28} (hc0 : x.regs cZero = 0) (hc1 : x.regs cOne = 1)
    (hdegB : x.regs curB = degBase) (hoffB : x.regs offB = offBase)
    (hL : x.regs nVerts = N)
    (hdeg : ∀ u : Fin N, x.mem (degBase + u.val) = (targetAdj u).length) :
    ∃ y, ExecWithin w prefixSumCode x y (9 * N + 5) ∧
      (∀ u ≤ N, y.mem (offBase + u) = csrOffset targetAdj u) ∧
      (∀ u : Fin N, y.mem (degBase + u.val) = csrOffset targetAdj (u.val + 1)) ∧
      (∀ a, ¬ ((offBase ≤ a ∧ a < offBase + N + 1) ∨ (degBase ≤ a ∧ a < degBase + N)) →
        y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  obtain ⟨x₀, hx₀_ex, hx₀_mem, hx₀_p, hx₀_i, hx₀_fr⟩ : ∃ x₀, ExecWithin (B := .standard) w
      (ram[ *offB ← cZero; pReg ← cZero; iReg ← cZero ]) x x₀ 3 ∧
      x₀.mem = Function.update x.mem offBase 0 ∧
      x₀.regs pReg = 0 ∧ x₀.regs iReg = 0 ∧
      (∀ r : Fin 28, r.val < 18 → x₀.regs r = x.regs r) := by
    wram_exec [hc0, hoffB]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, fun r hr => by wram_simp⟩
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) ∧
      y.regs pReg = csrOffset targetAdj k ∧
      (∀ u ≤ k, y.mem (offBase + u) = csrOffset targetAdj u) ∧
      (∀ u : Fin N, y.mem (degBase + u.val) =
        if u.val < k then csrOffset targetAdj (u.val + 1) else (targetAdj u).length) ∧
      (∀ a, ¬ ((offBase ≤ a ∧ a ≤ offBase + k) ∨ (degBase ≤ a ∧ a < degBase + k)) →
        y.mem a = x.mem a)
  have hbody : ∀ y, P (y.regs iReg) y → y.regs iReg < N →
      ∃ z, ExecWithin w prefixSumBody y z 7 ∧
        P (y.regs iReg + 1) z ∧ z.regs iReg = y.regs iReg + 1 := by
    intro y ⟨hy_fr, hy_p, hy_off, hy_deg, hy_out⟩ hlt
    have hdeg_k : y.mem (degBase + y.regs iReg) = (targetAdj ⟨y.regs iReg, hlt⟩).length := by
      simpa using hy_deg ⟨y.regs iReg, hlt⟩
    have hoff_succ := csrOffset_succ targetAdj hlt
    have hoff_le : csrOffset targetAdj (y.regs iReg + 1) ≤ Mc :=
      (csrOffset_mono targetAdj hlt).trans hmc
    unfold prefixSumBody
    wram_exec [hy_fr, hc1, hdegB, hoffB, hy_p, hdeg_k]
    dsimp only [P]
    refine ⟨⟨fun r hr => ?_, ?_, fun u hu => ?_, fun u => ?_, fun a ha => ?_⟩, by wram_simp⟩
    · wram_simp [hy_fr r hr]
    · wram_simp; exact hoff_succ.symm
    · mem_upd
      by_cases huk : u = y.regs iReg + 1
      · subst huk; simp [hoff_succ]
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hy_off u (by omega)
    · mem_upd
      rw [Function.update_of_ne (by have := u.isLt; omega)]
      by_cases huk : u.val = y.regs iReg
      · rw [huk, Function.update_self]
        simp [hoff_succ]
      · rw [Function.update_of_ne (by omega), hy_deg u]
        simp only [Nat.lt_succ_iff, le_iff_lt_or_eq, huk, or_false]
    · mem_upd
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hy_out a (by omega)
  have hx₀_P : P (x₀.regs iReg) x₀ := by
    rw [hx₀_i]
    refine ⟨hx₀_fr, hx₀_p, fun u hu => by simp [Nat.le_zero.mp hu, hx₀_mem],
      fun u => ?_, fun a ha => hx₀_mem ▸ Function.update_of_ne (by omega) 0 x.mem⟩
    simp only [Nat.not_lt_zero, ↓reduceIte, hx₀_mem]
    rw [Function.update_of_ne (by omega), hdeg u]
  obtain ⟨y, hy_loop, hy_P, -⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 nVerts (by decide)).trans hL) hbody
    (x := x₀) (by omega) hx₀_P
  exact ⟨y, (hx₀_ex.seq hy_loop).mono (by omega), hy_P.2.2.1,
    fun u => by simpa [u.isLt] using hy_P.2.2.2.1 u,
    fun a ha => hy_P.2.2.2.2 a (by omega), hy_P.1⟩

/-- Decrement `curB[vReg]` and write `uReg` into `edgeB[curB[vReg]]` in `6` instructions. -/
def backfillStepCode : Code .standard 28 := ram[
  addr ← curB + vReg;
  jEndReg ← *addr; jEndReg ← jEndReg - cOne;
  *addr ← jEndReg;
  addr ← edgeB + jEndReg; *addr ← uReg ]

/-- `backfillStepCode` does not read the word width. -/
theorem not_readsWidth_backfillStepCode : ¬ backfillStepCode.ReadsWidth := by decide +kernel

/-- `backfillStepCode` is `rand`-free. -/
theorem isRandFree_backfillStepCode : backfillStepCode.IsRandFree := by decide +kernel

private theorem csrOffset_disjoint {N : ℕ} (adj : Fin N → List (Fin N)) {u v : Fin N}
    (hne : u ≠ v) {p q : ℕ}
    (hp1 : csrOffset adj u.val ≤ p) (hp2 : p < csrOffset adj (u.val + 1))
    (hq1 : csrOffset adj v.val ≤ q) (hq2 : q < csrOffset adj (v.val + 1)) : p ≠ q := by
  have hval : u.val ≠ v.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
  · exact (hp2.trans_le ((csrOffset_mono adj hlt).trans hq1)).ne
  · exact (hq2.trans_le ((csrOffset_mono adj hgt).trans hp1)).ne'

private theorem partialCSRAt_step {N : ℕ}
    (targetAdj part : Fin N → List (Fin N))
    (curBase edgeBase Mc : ℕ)
    (hdisj : edgeBase + Mc ≤ curBase)
    (hmc : csrOffset targetAdj N ≤ Mc)
    (src dst : Fin N) (hroom : (part src).length + 1 ≤ (targetAdj src).length)
    (mem : ℕ → ℕ)
    (hp : PartialCSRAt targetAdj part curBase edgeBase mem) :
    let c := mem (curBase + src.val) - 1
    let mem' := Function.update (Function.update mem (curBase + src.val) c) (edgeBase + c) dst.val
    PartialCSRAt targetAdj (Function.update part src (dst :: part src)) curBase edgeBase mem' ∧
      (∀ a, ¬ ((curBase ≤ a ∧ a < curBase + N) ∨
          (edgeBase ≤ a ∧ a < edgeBase + csrOffset targetAdj N)) → mem' a = mem a) := by
  dsimp only
  set c := mem (curBase + src.val) - 1
  set mem₁ := Function.update mem (curBase + src.val) c
  set mem' := Function.update mem₁ (edgeBase + c) dst.val
  obtain ⟨hc_succ, hc_low, hc_high⟩ := hp.backfill_bounds src hroom
  have hsrc_lt := src.isLt
  have hc_lt_N := hc_high.trans_le (csrOffset_mono targetAdj hsrc_lt)
  have hm_cur (u : Fin N) : mem' (curBase + u.val) = mem₁ (curBase + u.val) :=
    Function.update_of_ne (by have := u.isLt; omega) _ _
  have hm_edge (p : ℕ) (hp_lt : p < csrOffset targetAdj N) (hpc : p ≠ c) :
      mem' (edgeBase + p) = mem (edgeBase + p) :=
    (Function.update_of_ne (by omega) _ _).trans (Function.update_of_ne (by omega) _ _)
  refine ⟨⟨fun u => ?_, fun u => ?_, fun u k hk => ?_⟩,
    fun a ha => (Function.update_of_ne (by omega) _ _).trans (Function.update_of_ne (by omega) _ _)⟩
  · by_cases hu : u = src <;> simp [*, hp.1 u]
  · rw [hm_cur]
    by_cases hu : u = src
    · simp only [hu, mem₁, Function.update_self, List.length_cons]
      rw [← Nat.add_assoc, Nat.add_right_comm c _ 1, hc_succ, hp.2.1 src]
    · have hne : curBase + u.val ≠ curBase + src.val := fun h => hu (Fin.ext (by omega))
      simp [mem₁, Function.update_of_ne hu, Function.update_of_ne hne, hp.2.1 u]
  · rw [hm_cur]
    by_cases hu : u = src
    · subst hu
      simp only [mem₁, Function.update_self] at hk ⊢
      cases k with
      | zero => exact Function.update_self (edgeBase + c) dst.val mem₁
      | succ k' =>
        have hk' : k' < (part u).length := Nat.lt_of_succ_lt_succ hk
        have hq := (hp.edge_in_row u hk').2.trans_le (csrOffset_mono targetAdj u.isLt)
        have hne := ((Nat.lt_succ_self c).trans_eq hc_succ).trans_le (Nat.le_add_right _ k')
        change mem' (edgeBase + c + (k' + 1)) = ((part u)[k']).val
        rw [Nat.add_assoc edgeBase c, Nat.add_comm k' 1, ← Nat.add_assoc c, hc_succ,
          hm_edge _ hq hne.ne', ← Nat.add_assoc]
        exact hp.2.2 u k' hk'
    · have hne_c : curBase + u.val ≠ curBase + src.val := fun h => hu (Fin.ext (by omega))
      simp only [Function.update_of_ne hu] at hk ⊢
      simp only [mem₁, Function.update_of_ne hne_c]
      obtain ⟨hq_low, hq_high⟩ := hp.edge_in_row u hk
      have hne_edge := csrOffset_disjoint targetAdj hu hq_low hq_high hc_low hc_high
      have hq_lt_N := hq_high.trans_le (csrOffset_mono targetAdj u.isLt)
      rw [Nat.add_assoc, hm_edge _ hq_lt_N hne_edge, ← Nat.add_assoc]
      exact hp.2.2 u k hk

theorem backfillStepCode_spec {N w : ℕ}
    (targetAdj part : Fin N → List (Fin N))
    (curBase edgeBase Mc : ℕ)
    (hdisj : edgeBase + Mc ≤ curBase)
    (hmc : csrOffset targetAdj N ≤ Mc)
    (hfit : Fits w (curBase + N + Mc + 1))
    (src dst : Fin N) (hroom : (part src).length + 1 ≤ (targetAdj src).length)
    {x : Data 28} (hc1 : x.regs cOne = 1)
    (hcurB : x.regs curB = curBase) (hedgeB : x.regs edgeB = edgeBase)
    (hsrc : x.regs vReg = src.val) (hdst : x.regs uReg = dst.val)
    (hp : PartialCSRAt targetAdj part curBase edgeBase x.mem) :
    ∃ y, ExecWithin w backfillStepCode x y 6 ∧
      PartialCSRAt targetAdj (Function.update part src (dst :: part src)) curBase edgeBase y.mem ∧
      (∀ a, ¬ ((curBase ≤ a ∧ a < curBase + N) ∨
          (edgeBase ≤ a ∧ a < edgeBase + csrOffset targetAdj N)) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = x.regs r) := by
  set c := x.mem (curBase + src.val) - 1
  obtain ⟨hc_succ, _, hc_high⟩ := hp.backfill_bounds src hroom
  have hc_pos : 1 ≤ x.mem (curBase + src.val) := hc_succ ▸ Nat.le_add_left 1 c
  have hsrc_lt := src.isLt
  have hc_lt_N := hc_high.trans_le (csrOffset_mono targetAdj hsrc_lt)
  have hstep := partialCSRAt_step targetAdj part curBase edgeBase Mc hdisj hmc src dst hroom
    x.mem hp
  unfold backfillStepCode
  wram_exec [hc1, hcurB, hedgeB, hsrc, hdst]
  refine ⟨?_, fun a ha => ?_, fun r h1 h2 => ?_⟩
  · mem_upd; exact hstep.1
  · mem_upd; exact hstep.2 a ha
  · wram_simp [h1, h2]

-- Shared purely mathematical offset identity used by both `Transpose` and `Kosaraju`.
private theorem csrOffset_transposeAdj_eq {N : ℕ} (adj : Fin N → List (Fin N)) :
    csrOffset (transposeAdj adj (List.finRange N)) N = csrOffset adj N := by
  rw [csrOffset_eq_outDegreeSum, csrOffset_eq_outDegreeSum, outDegreeSum, ← Fin.sum_univ_def,
    sum_length_transposeAdj]

end Cslib.Algorithms.WordRAM.DFS
