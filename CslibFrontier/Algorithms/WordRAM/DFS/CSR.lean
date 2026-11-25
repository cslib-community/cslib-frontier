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
  unfold csrOffset
  have hlen : u < (List.finRange N).length := by simpa using hu
  rw [List.take_add_one, List.getElem?_eq_getElem hlen]
  simp

theorem csrOffset_mono {N : ℕ} (adj : Fin N → List (Fin N)) {a b : ℕ} (hab : a ≤ b) :
    csrOffset adj a ≤ csrOffset adj b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    by_cases hlt : a + d < N
    · rw [Nat.add_succ, csrOffset_succ adj hlt]
      exact ih.trans (Nat.le_add_right _ _)
    · have heq : csrOffset adj (a + (d + 1)) = csrOffset adj (a + d) := by
        unfold csrOffset
        rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
      rw [heq]
      exact ih

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
  have hk_lt : csrOffset adj u.val + k < csrOffset adj N := by
    have h1 := csrOffset_succ adj u.isLt
    simp only [Fin.eta] at h1
    have h2 := csrOffset_mono adj (by omega : u.val + 1 ≤ N)
    omega
  rw [Nat.add_assoc, hedge _ hk_lt, ← Nat.add_assoc]
  exact h.2 u k hk

/-- Invariant of the backward CSR fill: the successor lists `part` written so far end at the cursors
`curBase`. -/
@[expose] def PartialCSRAt {N : ℕ} (targetAdj part : Fin N → List (Fin N))
    (curBase edgeBase : ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ w : Fin N, (part w).length ≤ (targetAdj w).length) ∧
    (∀ w : Fin N, mem (curBase + w.val) + (part w).length = csrOffset targetAdj (w.val + 1)) ∧
    ∀ (w : Fin N) (k : ℕ) (hk : k < (part w).length),
      mem (edgeBase + mem (curBase + w.val) + k) = ((part w)[k]).val

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
  have hcur_u := hp.2.1 u
  rw [csrOffset_succ targetAdj u.isLt] at hcur_u
  simp only [Fin.eta] at hcur_u
  have heq : mem (curBase + u.val) = csrOffset targetAdj u.val := by omega
  have hget := hp.2.2 u k hk
  rwa [heq] at hget

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
  refine ⟨_, (hprep.seq hzf.within).mono (by omega), fun i hi => ?_, fun a ha => ?_, fun r hr => ?_⟩
  · exact clear_of_owns ⟨Nat.le_add_right B i, Nat.add_lt_add_left hi B⟩
  · exact clear_of_not_owns ha
  · simp only [Function.update_of_ne (show r ≠ addr by rintro rfl; exact absurd hr (by decide))]
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
    have hoff_succ : csrOffset targetAdj (y.regs iReg + 1) =
        csrOffset targetAdj (y.regs iReg) + (targetAdj ⟨y.regs iReg, hlt⟩).length :=
      csrOffset_succ targetAdj hlt
    have hoff_le : csrOffset targetAdj (y.regs iReg + 1) ≤ Mc :=
      (csrOffset_mono targetAdj (by omega : y.regs iReg + 1 ≤ N)).trans hmc
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
        simp only [show u.val < y.regs iReg + 1 ↔ u.val < y.regs iReg by omega]
    · mem_upd
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hy_out a (by omega)
  have hx₀_P : P (x₀.regs iReg) x₀ := by
    rw [hx₀_i]
    refine ⟨hx₀_fr, hx₀_p, fun u hu => ?_, fun u => ?_, fun a ha => ?_⟩
    · have hu0 : u = 0 := by omega
      subst hu0; simp [hx₀_mem]
    · simp only [Nat.not_lt_zero, ↓reduceIte, hx₀_mem]
      rw [Function.update_of_ne (by omega)]
      exact hdeg u
    · rw [hx₀_mem, Function.update_of_ne (by omega)]
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
  · have := csrOffset_mono adj (by omega : u.val + 1 ≤ v.val)
    omega
  · have := csrOffset_mono adj (by omega : v.val + 1 ≤ u.val)
    omega

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
  have hsrc_lt := src.isLt
  have hcur_eq := hp.2.1 src
  have hoff_src : csrOffset targetAdj (src.val + 1) =
      csrOffset targetAdj src.val + (targetAdj src).length := by
    simpa using csrOffset_succ targetAdj hsrc_lt
  have hoff_le_N := csrOffset_mono targetAdj (by omega : src.val + 1 ≤ N)
  set c := mem (curBase + src.val) - 1
  set mem₁ := Function.update mem (curBase + src.val) c
  set mem' := Function.update mem₁ (edgeBase + c) dst.val
  have hc_pos : 1 ≤ mem (curBase + src.val) := by omega
  have hc_low : csrOffset targetAdj src.val ≤ c := by omega
  have hc_high : c < csrOffset targetAdj (src.val + 1) := by omega
  have hc_lt_N : c < csrOffset targetAdj N := lt_of_lt_of_le hc_high hoff_le_N
  refine ⟨⟨fun u => ?_, fun u => ?_, fun u k hk => ?_⟩, fun a ha => ?_⟩
  · by_cases hu : u = src
    · subst hu; simp [hroom]
    · simp [Function.update_of_ne hu, hp.1 u]
  · have hm_ne : edgeBase + c ≠ curBase + u.val := by have := u.isLt; omega
    rw [show mem' (curBase + u.val) = mem₁ (curBase + u.val) from
      Function.update_of_ne hm_ne.symm _ _]
    rcases eq_or_ne src u with rfl | hu
    · rw [Function.update_self, show mem₁ (curBase + src.val) = c from Function.update_self _ _ _,
        List.length_cons]
      omega
    · have hne : curBase + u.val ≠ curBase + src.val := fun h => hu (Fin.ext (by omega)).symm
      rw [Function.update_of_ne hu.symm,
        show mem₁ (curBase + u.val) = mem (curBase + u.val) from Function.update_of_ne hne _ _]
      exact hp.2.1 u
  · rcases eq_or_ne src u with rfl | hu
    · have hm_cur : mem' (curBase + src.val) = c := by
        change Function.update mem₁ (edgeBase + c) dst.val (curBase + src.val) = c
        rw [Function.update_of_ne (by omega)]
        exact Function.update_self _ _ _
      rw [hm_cur]
      simp only [Function.update_self] at hk ⊢
      cases k with
      | zero =>
        change Function.update mem₁ (edgeBase + c) dst.val (edgeBase + c + 0) = dst.val
        rw [Nat.add_zero, Function.update_self]
      | succ k' =>
        have hk' : k' < (part src).length := by simpa using hk
        have hidx : edgeBase + c + (k' + 1) = edgeBase + mem (curBase + src.val) + k' := by omega
        change Function.update mem₁ (edgeBase + c) dst.val (edgeBase + c + (k' + 1)) =
          ((part src)[k']).val
        rw [hidx, Function.update_of_ne (by omega)]
        change Function.update mem (curBase + src.val) c (edgeBase + mem (curBase + src.val) + k') =
          ((part src)[k']).val
        rw [Function.update_of_ne (by omega)]
        exact hp.2.2 src k' hk'
    · have hu' : u ≠ src := hu.symm
      simp only [Function.update_of_ne hu'] at hk ⊢
      have hne_c : curBase + u.val ≠ curBase + src.val := fun h => hu' (Fin.ext (by omega))
      have hm_cur : mem' (curBase + u.val) = mem (curBase + u.val) := by
        change Function.update mem₁ (edgeBase + c) dst.val (curBase + u.val) = mem (curBase + u.val)
        rw [Function.update_of_ne (by have := u.isLt; omega)]
        exact Function.update_of_ne hne_c _ _
      rw [hm_cur]
      have hu_cur := hp.2.1 u
      have hu_len := hp.1 u
      have hu_off : csrOffset targetAdj (u.val + 1) =
          csrOffset targetAdj u.val + (targetAdj u).length := by
        simpa using csrOffset_succ targetAdj u.isLt
      have hq_low : csrOffset targetAdj u.val ≤ mem (curBase + u.val) + k := by omega
      have hq_high : mem (curBase + u.val) + k < csrOffset targetAdj (u.val + 1) := by omega
      have hne_edge : mem (curBase + u.val) + k ≠ c :=
        csrOffset_disjoint targetAdj hu' hq_low hq_high hc_low hc_high
      have hq_lt_N : mem (curBase + u.val) + k < csrOffset targetAdj N :=
        lt_of_lt_of_le hq_high (csrOffset_mono targetAdj (by omega : u.val + 1 ≤ N))
      change Function.update mem₁ (edgeBase + c) dst.val (edgeBase + mem (curBase + u.val) + k) = _
      rw [Function.update_of_ne (by omega)]
      change Function.update mem (curBase + src.val) c (edgeBase + mem (curBase + u.val) + k) = _
      rw [Function.update_of_ne (by omega)]
      exact hp.2.2 u k hk
  · exact (Function.update_of_ne (by omega) _ _).trans (Function.update_of_ne (by omega) _ _)

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
  have hsrc_lt := src.isLt
  have hcur_eq := hp.2.1 src
  have hoff_src : csrOffset targetAdj (src.val + 1) =
      csrOffset targetAdj src.val + (targetAdj src).length := by
    simpa using csrOffset_succ targetAdj hsrc_lt
  have hoff_le_N := csrOffset_mono targetAdj (by omega : src.val + 1 ≤ N)
  set c := x.mem (curBase + src.val) - 1
  have hc_pos : 1 ≤ x.mem (curBase + src.val) := by omega
  have hc_lt_N : c < csrOffset targetAdj N :=
    lt_of_lt_of_le (by omega : c < csrOffset targetAdj (src.val + 1)) hoff_le_N
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
