/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DFS.CSR
import all CslibFrontier.Algorithms.WordRAM.DFS.CSR
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Explicit-stack iterative CSR depth-first search (`O(N + M)`)

Exports the DFS register invariant `DfsRegs` and proves the private single-root traversal
specification `visitRootCode_spec` used by the forward DFS and Kosaraju passes through
`import all`.
-/

public section

namespace Cslib.Algorithms.WordRAM.DFS

open Cslib.WordRAM
open Cslib.Algorithms.Lean.DFS
open Reg

local macro "mem_upd" : tactic =>
  `(tactic| simp only [Data.set_mem, Data.set_mem_apply, Data.write_mem])

/-! ### Explicit-stack iterative CSR depth-first search (`O(N + M)`) -/

/-- Pure depth-first search over the successor list `es` from the visited set `vis` with an empty
finishing list. -/
private def foldEmpty {V : Type*} [DecidableEq V] (adj : V → List V) (k : ℕ)
    (es : List V) (vis : Finset V) : Cslib.Algorithms.Lean.DFS.State V :=
  es.foldl (fun t v => visit adj k v t) ⟨vis, []⟩

private theorem foldl_visit_append {V : Type*} [DecidableEq V] (adj : V → List V) (k : ℕ) :
    ∀ (es : List V) (vis : Finset V) (fin : List V),
      es.foldl (fun t v => visit adj k v t) ⟨vis, fin⟩ =
        ⟨(foldEmpty adj k es vis).visited, (foldEmpty adj k es vis).finished ++ fin⟩
  | [], _, _ => rfl
  | v :: es, vis, fin => by
    dsimp only [foldEmpty, List.foldl_cons]
    rw [visit_eq_of_nil k v vis fin, foldl_visit_append adj k es _ _,
      foldl_visit_append adj k es _ _, List.append_assoc]

private theorem foldEmpty_cons {V : Type*} [DecidableEq V] (adj : V → List V) (k : ℕ)
    (v : V) (es : List V) (vis : Finset V) :
    foldEmpty adj k (v :: es) vis =
      let s₁ := visit adj k v ⟨vis, []⟩
      let s₂ := foldEmpty adj k es s₁.visited
      ⟨s₂.visited, s₂.finished ++ s₁.finished⟩ := by
  dsimp only [foldEmpty, List.foldl_cons]
  exact foldl_visit_append adj k es (visit adj k v ⟨vis, []⟩).visited
    (visit adj k v ⟨vis, []⟩).finished

private theorem visit_eq_foldEmpty {V : Type*} [DecidableEq V] {adj : V → List V} {k : ℕ}
    {u : V} {vis : Finset V} (hu : u ∉ vis) :
    visit adj (k + 1) u ⟨vis, []⟩ =
      let s := foldEmpty adj k (adj u) (insert u vis)
      ⟨s.visited, u :: s.finished⟩ := by
  simp [visit, hu, foldEmpty]

/-- The visited flags at `visAddr` encode the set `vis`. -/
private def VisAt {N : ℕ} (vis : Finset (Fin N)) (visAddr : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ w : Fin N, mem (visAddr + w.val) = (decide (w ∈ vis)).toNat

/-- Register invariant of the depth-first search: constants and array bases. -/
structure DfsRegs (offAddr edgeAddr visAddr finAddr stkAddr : ℕ) (x : Data 28) : Prop where
  czero : x.regs cZero = 0
  cone : x.regs cOne = 1
  cthree : x.regs cThree = 3
  hoff : x.regs offB = offAddr
  hedge : x.regs edgeB = edgeAddr
  hvis : x.regs visB = visAddr
  hfin : x.regs finB = finAddr
  hstk : x.regs stkB = stkAddr

private theorem dfsRegs_of_frame {offAddr edgeAddr visAddr finAddr stkAddr : ℕ} {x y : Data 28}
    (hx : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hfr : ∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) :
    DfsRegs offAddr edgeAddr visAddr finAddr stkAddr y := by
  obtain ⟨⟩ := hx
  constructor <;> wram_simp [*]

/-- Push the root `uReg` as the first DFS stack frame. -/
private def dfsPushRoot : Code .standard 28 := ram[
  *addr ← cOne;
  addr ← offB + uReg; jReg ← *addr;
  addr ← addr + cOne; jEndReg ← *addr;
  *stkB ← uReg;
  addr ← stkB + cOne; *addr ← jReg;
  addr ← addr + cOne; *addr ← jEndReg;
  pReg ← cOne ]

/-- One DFS step on the top stack frame: pop and finish, skip a visited successor, or push an
unvisited one. -/
private def dfsStepBody : Code .standard 28 := ram[
  vReg ← pReg - cOne;
  addr ← cThree * vReg; addr ← stkB + addr;
  uReg ← *addr;
  addr ← addr + cOne; jReg ← *addr;
  addr ← addr + cOne; jEndReg ← *addr;
  if jReg < jEndReg then [
    addr ← cThree * vReg; addr ← stkB + addr; addr ← addr + cOne;
    jEndReg ← jReg + cOne; *addr ← jEndReg;
    addr ← edgeB + jReg; vReg ← *addr;
    addr ← visB + vReg; jReg ← *addr;
    if jReg = cZero then [
      *addr ← cOne;
      addr ← offB + vReg; jReg ← *addr;
      addr ← addr + cOne; jEndReg ← *addr;
      addr ← cThree * pReg; addr ← stkB + addr;
      *addr ← vReg;
      addr ← addr + cOne; *addr ← jReg;
      addr ← addr + cOne; *addr ← jEndReg;
      pReg ← pReg + cOne ]
    else [ pReg ← pReg ] ]
  else [
    pReg ← vReg;
    addr ← finB + finCnt; *addr ← uReg;
    finCnt ← finCnt + cOne ] ]

/-- Run DFS steps while the stack is nonempty. -/
private def dfsLoop : Code .standard 28 :=
  .loop (.lt cZero pReg) dfsStepBody

/-- Visit the root `uReg` if it is unvisited, running the DFS loop from it. -/
private def visitRootCode : Code .standard 28 := ram[
  addr ← visB + uReg; jReg ← *addr;
  if jReg = cZero then [
    ⟪dfsPushRoot.seq dfsLoop⟫ ]
  else [ pReg ← cZero ] ]

/-- Instruction budget of the DFS loop on the remaining successors `es` of a frame, given the
vertices `new` finished during it. -/
private def dfsFrameTime {N : ℕ} (adj : Fin N → List (Fin N)) (es new : List (Fin N)) : ℕ :=
  20 + 36 * es.length + 60 * new.length + 36 * outDegreeSum adj new

private theorem visAt_insert {N : ℕ} {vis : Finset (Fin N)} {visAddr : ℕ} {mem : ℕ → ℕ}
    (h : VisAt vis visAddr mem) (v : Fin N) :
    VisAt (insert v vis) visAddr (Function.update mem (visAddr + v.val) 1) := by
  intro w
  by_cases hw : w = v
  · subst hw; simp
  · have hne : visAddr + w.val ≠ visAddr + v.val := fun heq => hw (Fin.ext (by omega))
    rw [Function.update_of_ne hne, h w]
    simp [hw]

private theorem dfsStepBody_pop {N w : ℕ} (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4))
    (u : Fin N) (idx d F₀ : ℕ) (vis : Finset (Fin N)) {x : Data 28}
    (hidx : idx = (adj u).length)
    (hcons : F₀ + d + 1 + (N - vis.card) ≤ N)
    (hregs : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hcsr : CSRAt adj offAddr edgeAddr x.mem)
    (hvis : VisAt vis visAddr x.mem)
    (hp : x.regs pReg = d + 1)
    (hfc : x.regs finCnt = F₀)
    (hstk0 : x.mem (stkAddr + 3 * d) = u.val)
    (hstk1 : x.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + idx)
    (hstk2 : x.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1)) :
    ∃ x₁, ExecWithin w dfsStepBody x x₁ 16 ∧
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt vis visAddr x₁.mem ∧
      x₁.regs pReg = d ∧
      x₁.regs finCnt = F₀ + 1 ∧
      x₁.mem (finAddr + F₀) = u.val ∧
      (∀ a, ¬ (a = finAddr + F₀) → x₁.mem a = x.mem a) ∧
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r) := by
  have hoff_u := csrOffset_succ adj u.isLt
  simp only [Fin.eta] at hoff_u
  have hstk1' : x.mem (stkAddr + 3 * d + 1) = csrOffset adj (u.val + 1) := by omega
  have hu_lt := u.isLt
  have hstk2' : x.mem (stkAddr + 3 * d + 1 + 1) = csrOffset adj (u.val + 1) := by
    simpa [Nat.add_assoc] using hstk2
  unfold dfsStepBody
  wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
    hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1', hstk2']
  refine ⟨dfsRegs_of_frame hregs fun r hr => by wram_simp, ?_, fun v => ?_, by wram_simp,
    by wram_simp, by wram_simp, fun a ha => by wram_simp,
    fun r hr => by rcases hr with hr | rfl | rfl <;> wram_simp⟩
  · mem_upd
    exact hcsr.of_eqOn
      (fun _ _ => Function.update_of_ne (by omega) _ _)
      (fun _ _ => Function.update_of_ne (by omega) _ _)
  · have := v.isLt
    wram_simp [hvis v]

private theorem CSRAt.successor {N offAddr edgeAddr : ℕ} {adj : Fin N → List (Fin N)}
    {mem : ℕ → ℕ} (hcsr : CSRAt adj offAddr edgeAddr mem) (u v : Fin N) (idx : ℕ)
    (hidx : idx < (adj u).length) (hv : (adj u)[idx]'hidx = v) :
    let j := csrOffset adj u.val + idx
    j < csrOffset adj (u.val + 1) ∧ j < csrOffset adj N ∧ mem (edgeAddr + j) = v.val := by
  have hend : csrOffset adj u.val + idx < csrOffset adj (u.val + 1) := by
    rw [csrOffset_succ adj u.isLt]
    simpa only [Fin.eta] using Nat.add_lt_add_left hidx _
  exact ⟨hend, hend.trans_le (csrOffset_mono adj (Nat.succ_le_of_lt u.isLt)),
    by simpa only [Nat.add_assoc, hv] using hcsr.2 u idx hidx⟩

private theorem dfsStepBody_skip {N w : ℕ} (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4))
    (u v : Fin N) (idx d F₀ : ℕ) (vis : Finset (Fin N)) {x : Data 28}
    (hidx_lt : idx < (adj u).length)
    (hv_eq : (adj u)[idx]'hidx_lt = v)
    (hmem : v ∈ vis)
    (hcons : F₀ + d + 1 + (N - vis.card) ≤ N)
    (hregs : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hcsr : CSRAt adj offAddr edgeAddr x.mem)
    (hvis : VisAt vis visAddr x.mem)
    (hp : x.regs pReg = d + 1)
    (hfc : x.regs finCnt = F₀)
    (hstk0 : x.mem (stkAddr + 3 * d) = u.val)
    (hstk1 : x.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + idx)
    (hstk2 : x.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1)) :
    ∃ x₁, ExecWithin w dfsStepBody x x₁ 24 ∧
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt vis visAddr x₁.mem ∧
      x₁.regs pReg = d + 1 ∧
      x₁.regs finCnt = F₀ ∧
      x₁.mem (stkAddr + 3 * d) = u.val ∧
      x₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) ∧
      x₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) ∧
      (∀ a, a ≠ stkAddr + 3 * d + 1 → x₁.mem a = x.mem a) ∧
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r) := by
  obtain ⟨hj_lt_end, hj_lt_N, hedge_j⟩ := hcsr.successor u v idx hidx_lt hv_eq
  have hvis_v1 : x.mem (visAddr + v.val) = 1 := by simpa [hmem] using hvis v
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  have hstk2' : x.mem (stkAddr + 3 * d + 1 + 1) = csrOffset adj (u.val + 1) := by
    simpa [Nat.add_assoc] using hstk2
  unfold dfsStepBody
  wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
    hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1, hstk2', hedge_j, hvis_v1, hj_lt_end]
  refine ⟨dfsRegs_of_frame hregs fun r hr => by wram_simp, ?_, fun v => ?_, by wram_simp,
    by wram_simp [hfc], by wram_simp [hstk0], by wram_simp; omega, by wram_simp [hstk2],
    fun a ha => by wram_simp, fun r hr => by rcases hr with hr | rfl | rfl <;> wram_simp⟩
  · mem_upd
    exact hcsr.of_eqOn
      (fun _ _ => Function.update_of_ne (by omega) _ _)
      (fun _ _ => Function.update_of_ne (by omega) _ _)
  · have := v.isLt
    wram_simp [hvis v]

private theorem dfsStepBody_push {N w : ℕ} (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4))
    (u v : Fin N) (idx d F₀ : ℕ) (vis : Finset (Fin N)) {x : Data 28}
    (hidx_lt : idx < (adj u).length)
    (hv_eq : (adj u)[idx]'hidx_lt = v)
    (hmem : v ∉ vis)
    (hcons_child : F₀ + (d + 1) + 1 + (N - (insert v vis).card) ≤ N)
    (hregs : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hcsr : CSRAt adj offAddr edgeAddr x.mem)
    (hvis : VisAt vis visAddr x.mem)
    (hp : x.regs pReg = d + 1)
    (hfc : x.regs finCnt = F₀)
    (hstk0 : x.mem (stkAddr + 3 * d) = u.val)
    (hstk1 : x.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + idx)
    (hstk2 : x.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1)) :
    ∃ x₁, ExecWithin w dfsStepBody x x₁ 34 ∧
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt (insert v vis) visAddr x₁.mem ∧
      x₁.regs pReg = (d + 1) + 1 ∧
      x₁.regs finCnt = F₀ ∧
      x₁.mem (stkAddr + 3 * d) = u.val ∧
      x₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) ∧
      x₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) ∧
      x₁.mem (stkAddr + 3 * (d + 1)) = v.val ∧
      x₁.mem (stkAddr + 3 * (d + 1) + 1) = csrOffset adj v.val + 0 ∧
      x₁.mem (stkAddr + 3 * (d + 1) + 2) = csrOffset adj (v.val + 1) ∧
      (∀ a, ¬ (a = visAddr + v.val ∨
          (stkAddr + 3 * d ≤ a ∧ a < stkAddr + 3 * N)) → x₁.mem a = x.mem a) ∧
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r) := by
  obtain ⟨hj_lt_end, hj_lt_N, hedge_j⟩ := hcsr.successor u v idx hidx_lt hv_eq
  have hvis_v0 : x.mem (visAddr + v.val) = 0 := by simpa [hmem] using hvis v
  set vis₁ := insert v vis
  have hcard_vis₁_le : vis₁.card ≤ N := by simpa using Finset.card_le_univ vis₁
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  have hoff_v0 : x.mem (offAddr + v.val) = csrOffset adj v.val := hcsr.1 v.val (by omega)
  have hoff_v1 : x.mem (offAddr + v.val + 1) = csrOffset adj (v.val + 1) := by
    simpa [Nat.add_assoc] using hcsr.1 (v.val + 1) (by omega)
  have hstk2' : x.mem (stkAddr + 3 * d + 1 + 1) = csrOffset adj (u.val + 1) := by
    simpa [Nat.add_assoc] using hstk2
  unfold dfsStepBody
  wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
    hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1, hstk2', hedge_j, hvis_v0, hj_lt_end,
    hoff_v0, hoff_v1]
  refine ⟨dfsRegs_of_frame hregs fun r hr => by wram_simp, ?_, fun w_v => ?_, by wram_simp,
    by wram_simp [hfc], by wram_simp [hstk0], by wram_simp; omega, by wram_simp [hstk2],
    by wram_simp, by wram_simp, by wram_simp, fun a ha => by wram_simp,
    fun r hr => by rcases hr with hr | rfl | rfl <;> wram_simp⟩
  · mem_upd
    exact hcsr.of_eqOn
      (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
      (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
  · have := w_v.isLt
    mem_upd
    repeat rw [Function.update_of_ne (by omega)]
    refine visAt_insert (fun w' => ?_) v w_v
    rw [Function.update_of_ne (by have := w'.isLt; omega)]; exact hvis w'

/-- The cells from `base` on hold the vertices of `L` in order. -/
private def FinAt {N : ℕ} (L : List (Fin N)) (base : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ q (hq : q < L.length), mem (base + q) = L[q].val

private theorem FinAt.append {N : ℕ} {A B : List (Fin N)} {base : ℕ} {mem : ℕ → ℕ}
    (hA : FinAt A base mem) (hB : FinAt B (base + A.length) mem) : FinAt (A ++ B) base mem := by
  intro q hq
  rw [List.length_append] at hq
  by_cases h : q < A.length
  · rw [List.getElem_append_left h]; exact hA q h
  · rw [List.getElem_append_right (by omega), ← hB (q - A.length) (by omega)]
    congr 1; omega

/-- One iteration of the DFS loop on a nonempty stack, then the rest of the loop. -/
private theorem dfsLoop_iter {w offAddr edgeAddr visAddr finAddr stkAddr d T₁ T₂ : ℕ}
    {x x₁ z : Data 28} (hregs : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hp : x.regs pReg = d + 1) (h₁ : ExecWithin w dfsStepBody x x₁ T₁)
    (h₂ : ExecWithin w dfsLoop x₁ z T₂) : ExecWithin w dfsLoop x z (T₁ + T₂ + 2) := by
  have hlt : (Cond.lt cZero pReg).Holds x := by
    change x.regs cZero < x.regs pReg; rw [hregs.czero, hp]; omega
  exact h₁.loop_iter hlt h₂

private theorem dfsLoop_cps {N w : ℕ} (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4)) :
    ∀ (k : ℕ),
      ∀ (u : Fin N) (es : List (Fin N)) (idx d F₀ T_cont : ℕ)
        (vis : Finset (Fin N)) (x : Data 28) (Q : Data 28 → Prop)
        (_ : idx + es.length = (adj u).length),
        (∀ q (hq : q < es.length),
          (adj u)[idx + q]'(by omega) = es[q]) →
        N - vis.card ≤ k →
        F₀ + d + 1 + (N - vis.card) ≤ N →
        DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x →
        CSRAt adj offAddr edgeAddr x.mem →
        VisAt vis visAddr x.mem →
        x.regs pReg = d + 1 →
        x.regs finCnt = F₀ →
        x.mem (stkAddr + 3 * d) = u.val →
        x.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + idx →
        x.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) →
        (∀ y : Data 28,
          let s := foldEmpty adj k es vis
          DfsRegs offAddr edgeAddr visAddr finAddr stkAddr y →
          CSRAt adj offAddr edgeAddr y.mem →
          VisAt s.visited visAddr y.mem →
          y.regs pReg = d →
          y.regs finCnt = F₀ + s.finished.length + 1 →
          FinAt (s.finished.reverse ++ [u]) (finAddr + F₀) y.mem →
          (∀ a, ¬ ((visAddr ≤ a ∧ a < visAddr + N) ∨
              (finAddr + F₀ ≤ a ∧ a < finAddr + F₀ + s.finished.length + 1) ∨
              (stkAddr + 3 * d ≤ a ∧ a < stkAddr + 3 * N)) → y.mem a = x.mem a) →
          (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → y.regs r = x.regs r) →
          ∃ z, ExecWithin w dfsLoop y z T_cont ∧ Q z) →
        ∃ z, ExecWithin w dfsLoop x z
          (dfsFrameTime adj es (foldEmpty adj k es vis).finished + T_cont) ∧ Q z := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih_k =>
    intro u es
    induction es with
    | nil =>
      intro idx d F₀ T_cont vis x Q hidx _ _ hcons hregs hcsr hvis hp hfc hstk0 hstk1 hstk2 hcont
      simp only [List.length_nil, Nat.add_zero] at hidx
      obtain ⟨x₁, hx₁, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_fin0, hx₁_out, hx₁_fr⟩ :=
        dfsStepBody_pop adj offAddr edgeAddr visAddr finAddr stkAddr Mc
          hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit u idx d F₀ vis hidx hcons
          hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
      obtain ⟨z, hz, hQz⟩ := hcont x₁ hx₁_r hx₁_csr hx₁_vis hx₁_p
        (by simpa [foldEmpty] using hx₁_fc)
        (fun q hq => by
          obtain rfl : q = 0 := by simpa [foldEmpty] using hq
          simpa [foldEmpty] using hx₁_fin0)
        (fun a ha => hx₁_out a (by dsimp only [foldEmpty, List.length_nil] at ha; omega))
        hx₁_fr
      exact ⟨z, (dfsLoop_iter hregs hp hx₁ hz).mono
        (by dsimp only [dfsFrameTime, foldEmpty, outDegreeSum]; omega), hQz⟩
    | cons v es' ih_es =>
      intro idx d F₀ T_cont vis x Q hidx hes hk hcons hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
        hcont
      simp only [List.length_cons] at hidx
      have hv_eq : (adj u)[idx]'(by omega) = v := by
        have h0 := hes 0 (by simp)
        simpa only [Nat.add_zero, List.getElem_cons_zero] using h0
      have hes' : ∀ q (hq : q < es'.length), (adj u)[idx + 1 + q]'(by omega) = es'[q] := by
        intro q hq
        have h := hes (q + 1) (by simp only [List.length_cons]; omega)
        simp only [show idx + 1 + q = idx + (q + 1) by omega]
        simpa only [List.getElem_cons_succ] using h
      by_cases hmem : v ∈ vis
      · -- Case 1: `v ∈ vis`
        have hvisit_v : visit adj k v ⟨vis, []⟩ = ⟨vis, []⟩ := by
          cases k
          exacts [rfl, visit_of_mem hmem]
        have hfold_eq : foldEmpty adj k (v :: es') vis = foldEmpty adj k es' vis := by
          rw [foldEmpty_cons, hvisit_v]
          simp
        rw [hfold_eq] at hcont ⊢
        obtain ⟨x₁, hx₁, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_s0, hx₁_s1, hx₁_s2, hx₁_out,
          hx₁_fr⟩ :=
          dfsStepBody_skip adj offAddr edgeAddr visAddr finAddr stkAddr Mc
            hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit u v idx d F₀ vis (by omega) hv_eq hmem hcons
            hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
        obtain ⟨z, hz, hQz⟩ := ih_es (idx + 1) d F₀ T_cont vis x₁ Q (by omega) hes'
          hk hcons hx₁_r hx₁_csr hx₁_vis hx₁_p hx₁_fc hx₁_s0 hx₁_s1 hx₁_s2
          (fun y hy_r hy_csr hy_vis hy_p hy_fc hy_fin hy_out hy_fr =>
            hcont y hy_r hy_csr hy_vis hy_p hy_fc hy_fin
              (fun a ha => (hy_out a ha).trans (hx₁_out a (by omega)))
              (fun r hr => (hy_fr r hr).trans (hx₁_fr r hr)))
        refine ⟨z, (dfsLoop_iter hregs hp hx₁ hz).mono ?_, hQz⟩
        simp only [dfsFrameTime, List.length_cons]
        omega
      · -- Case 2: `v ∉ vis`
        have hcard_lt : vis.card < N := by simpa using Finset.card_lt_univ_of_notMem hmem
        rcases k with _ | k'
        · omega
        set vis₁ := insert v vis
        have hcard_vis₁ : vis₁.card = vis.card + 1 := Finset.card_insert_of_notMem hmem
        have hcard_vis₁_le : vis₁.card ≤ N := by simpa using Finset.card_le_univ vis₁
        have hk' : N - vis₁.card ≤ k' := by omega
        have hcons_child : F₀ + (d + 1) + 1 + (N - vis₁.card) ≤ N := by omega
        obtain ⟨x₁, hx₁, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_d0, hx₁_d1,
          hx₁_d2, hx₁_c0, hx₁_c1, hx₁_c2, hx₁_out, hx₁_fr⟩ :=
          dfsStepBody_push adj offAddr edgeAddr visAddr finAddr stkAddr Mc
            hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit u v idx d F₀ vis (by omega) hv_eq hmem
            hcons_child hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
        obtain ⟨s₁, hs₁_def⟩ : ∃ s₁, visit adj (k' + 1) v ⟨vis, []⟩ = s₁ := ⟨_, rfl⟩
        obtain ⟨s_child, hsc_def⟩ : ∃ s_child, foldEmpty adj k' (adj v) vis₁ = s_child := ⟨_, rfl⟩
        have hs₁_eq : s₁ = ⟨s_child.visited, v :: s_child.finished⟩ := by
          rw [← hs₁_def, ← hsc_def]; exact visit_eq_foldEmpty hmem
        obtain ⟨s₂, hs₂_def⟩ : ∃ s₂, foldEmpty adj (k' + 1) es' s₁.visited = s₂ := ⟨_, rfl⟩
        have hfold_cons : foldEmpty adj (k' + 1) (v :: es') vis =
            ⟨s₂.visited, s₂.finished ++ s₁.finished⟩ := by
          rw [← hs₂_def, ← hs₁_def]; exact foldEmpty_cons adj (k' + 1) v es' vis
        have hcard_s₁ : s₁.visited.card = vis.card + s₁.finished.length := by
          rw [← hs₁_def]; exact card_visit_nil adj (k' + 1) v vis
        have hcard_s₁_le : s₁.visited.card ≤ N := by
          simpa only [Fintype.card_fin] using Finset.card_le_univ s₁.visited
        have hlen_s₁ : s₁.finished.length = s_child.finished.length + 1 := by
          rw [hs₁_eq]; rfl
        have hk_s₁ : N - s₁.visited.card ≤ k' + 1 := by omega
        have hcons_after : (F₀ + s₁.finished.length) + d + 1 + (N - s₁.visited.card) ≤ N := by
          omega
        rw [hfold_cons] at hcont ⊢
        dsimp only at hcont
        obtain ⟨z, hz, hQz⟩ := ih_k k' (Nat.lt_succ_self k') v (adj v) 0 (d + 1) F₀
          (dfsFrameTime adj es' s₂.finished + T_cont) vis₁ x₁ Q (Nat.zero_add _)
          (fun q hq => by simp only [Nat.zero_add]) hk' hcons_child hx₁_r hx₁_csr hx₁_vis hx₁_p
          hx₁_fc hx₁_c0 hx₁_c1 hx₁_c2
          (fun y₁ hy₁_r hy₁_csr hy₁_vis hy₁_p hy₁_fc hy₁_fin hy₁_out hy₁_fr => by
            rw [hsc_def] at hy₁_vis hy₁_fc hy₁_fin hy₁_out
            have hy₁_fin' : FinAt s₁.finished.reverse (finAddr + F₀) y₁.mem := by
              rw [hs₁_eq, List.reverse_cons]; exact hy₁_fin
            rw [← hs₂_def]
            refine ih_es (idx + 1) d (F₀ + s₁.finished.length) T_cont s₁.visited y₁ Q
              (by omega) hes' hk_s₁ hcons_after hy₁_r hy₁_csr (by rw [hs₁_eq]; exact hy₁_vis)
              hy₁_p (by omega) ((hy₁_out _ (by omega)).trans hx₁_d0)
              ((hy₁_out _ (by omega)).trans hx₁_d1) ((hy₁_out _ (by omega)).trans hx₁_d2)
              (fun y₂ hy₂_r hy₂_csr hy₂_vis hy₂_p hy₂_fc hy₂_fin hy₂_out hy₂_fr => ?_)
            rw [hs₂_def] at hy₂_vis hy₂_fc hy₂_fin hy₂_out
            refine hcont y₂ hy₂_r hy₂_csr hy₂_vis hy₂_p
              (by simp only [List.length_append]; omega) ?_ (fun a ha => ?_)
              (fun r hr => (hy₂_fr r hr).trans ((hy₁_fr r hr).trans (hx₁_fr r hr)))
            · rw [List.reverse_append, List.append_assoc]
              refine FinAt.append (fun q hq => (hy₂_out _ ?_).trans (hy₁_fin' q hq)) ?_
              · simp only [List.length_reverse] at hq; omega
              · rwa [List.length_reverse, Nat.add_assoc]
            · simp only [List.length_append] at ha
              exact (hy₂_out a (by omega)).trans ((hy₁_out a (by omega)).trans
                (hx₁_out a (by have := v.isLt; omega))))
        refine ⟨z, (dfsLoop_iter hregs hp hx₁ hz).mono ?_, hQz⟩
        rw [hsc_def, hs₁_eq]
        simp only [dfsFrameTime, outDegreeSum, List.length_cons, List.length_append,
          List.map_append, List.map_cons, List.sum_append, List.sum_cons]
        omega

private theorem visitRootCode_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (offAddr edgeAddr visAddr finAddr stkAddr Mc : ℕ)
    (hdisj1 : offAddr + N + 1 ≤ visAddr)
    (hdisj2 : edgeAddr + Mc ≤ visAddr)
    (hdisj3 : visAddr + N ≤ finAddr)
    (hdisj4 : finAddr + N ≤ stkAddr)
    (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (stkAddr + 3 * N + Mc + 4))
    (r : Fin N) (F₀ : ℕ) (vis : Finset (Fin N))
    (hcons : F₀ + (N - vis.card) ≤ N)
    {x : Data 28}
    (hregs : DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x)
    (hcsr : CSRAt adj offAddr edgeAddr x.mem)
    (hvis : VisAt vis visAddr x.mem)
    (hu : x.regs uReg = r.val)
    (hfc : x.regs finCnt = F₀) :
    let s := visit adj N r ⟨vis, []⟩
    ∃ y, ExecWithin w visitRootCode x y
        (16 + 60 * s.finished.length + 36 * outDegreeSum adj s.finished) ∧
      DfsRegs offAddr edgeAddr visAddr finAddr stkAddr y ∧
      CSRAt adj offAddr edgeAddr y.mem ∧
      VisAt s.visited visAddr y.mem ∧
      y.regs finCnt = F₀ + s.finished.length ∧
      (∀ q (hq : q < s.finished.reverse.length),
        y.mem (finAddr + F₀ + q) = (s.finished.reverse[q]).val) ∧
      (∀ a, ¬ ((visAddr ≤ a ∧ a < visAddr + N) ∨
          (finAddr + F₀ ≤ a ∧ a < finAddr + F₀ + s.finished.length) ∨
          (stkAddr ≤ a ∧ a < stkAddr + 3 * N)) → y.mem a = x.mem a) ∧
      (∀ reg : Fin 28, (reg.val < 19 ∨ reg = compIdxReg ∨ reg = oldFinReg) →
        y.regs reg = x.regs reg) := by
  have hr_lt := r.isLt
  have hvis_r : x.mem (visAddr + r.val) = (decide (r ∈ vis)).toNat := hvis r
  obtain ⟨k', hkN⟩ : ∃ k', N = k' + 1 := ⟨N - 1, by omega⟩
  let RootPost (y : Data 28) : Prop :=
    let s := visit adj N r ⟨vis, []⟩
    DfsRegs offAddr edgeAddr visAddr finAddr stkAddr y ∧
      CSRAt adj offAddr edgeAddr y.mem ∧
      VisAt s.visited visAddr y.mem ∧
      y.regs finCnt = F₀ + s.finished.length ∧
      (∀ q (hq : q < s.finished.reverse.length),
        y.mem (finAddr + F₀ + q) = (s.finished.reverse[q]).val) ∧
      (∀ a, ¬ ((visAddr ≤ a ∧ a < visAddr + N) ∨
          (finAddr + F₀ ≤ a ∧ a < finAddr + F₀ + s.finished.length) ∨
          (stkAddr ≤ a ∧ a < stkAddr + 3 * N)) → y.mem a = x.mem a) ∧
      (∀ reg : Fin 28, (reg.val < 19 ∨ reg = compIdxReg ∨ reg = oldFinReg) →
        y.regs reg = x.regs reg)
  change ∃ y, ExecWithin w visitRootCode x y _ ∧ RootPost y
  by_cases hmem : r ∈ vis
  · have hvis_1 : x.mem (visAddr + r.val) = 1 := by simpa [hmem] using hvis_r
    have hs_eq : visit adj N r ⟨vis, []⟩ = ⟨vis, []⟩ :=
      (congrArg (fun fuel => visit adj fuel r ⟨vis, []⟩) hkN).trans (visit_of_mem hmem)
    unfold visitRootCode
    wram_exec [hregs.czero, hregs.hvis, hu, hvis_1]
    dsimp only [RootPost]
    rw [hs_eq]
    exact ⟨dfsRegs_of_frame hregs fun reg hreg => by wram_simp, by mem_upd; exact hcsr,
      fun w_v => by mem_upd; exact hvis w_v, by wram_simp; simpa using hfc,
      fun _ hq => by simp at hq, fun _ _ => rfl,
      fun reg hreg => by rcases hreg with hreg | rfl | rfl <;> wram_simp⟩
  · have hvis_0 : x.mem (visAddr + r.val) = 0 := by simpa [hmem] using hvis_r
    set vis₁ := insert r vis
    have hcard_vis₁ : vis₁.card = vis.card + 1 := Finset.card_insert_of_notMem hmem
    have hcard_vis₁_le : vis₁.card ≤ N := by simpa using Finset.card_le_univ vis₁
    have hk' : N - vis₁.card ≤ k' := by omega
    have hcons_root : F₀ + 0 + 1 + (N - vis₁.card) ≤ N := by omega
    have hoff_r0 : x.mem (offAddr + r.val) = csrOffset adj r.val := hcsr.1 r.val (by omega)
    have hoff_r1 : x.mem (offAddr + r.val + 1) = csrOffset adj (r.val + 1) := by
      simpa [Nat.add_assoc] using hcsr.1 (r.val + 1) (by omega)
    obtain ⟨x₁, hx₁_ex, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_s0, hx₁_s1, hx₁_s2,
      hx₁_out, hx₁_fr⟩ : ∃ x₁, ExecWithin w dfsPushRoot
        ((x.set addr (visAddr + r.val)).set jReg 0) x₁ 11 ∧
        DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
        CSRAt adj offAddr edgeAddr x₁.mem ∧
        VisAt vis₁ visAddr x₁.mem ∧
        x₁.regs pReg = 1 ∧
        x₁.regs finCnt = F₀ ∧
        x₁.mem (stkAddr + 3 * 0) = r.val ∧
        x₁.mem (stkAddr + 3 * 0 + 1) = csrOffset adj r.val + 0 ∧
        x₁.mem (stkAddr + 3 * 0 + 2) = csrOffset adj (r.val + 1) ∧
        (∀ a, ¬ (a = visAddr + r.val ∨ (stkAddr ≤ a ∧ a < stkAddr + 3 * N)) →
          x₁.mem a = x.mem a) ∧
        (∀ reg : Fin 28, (reg.val < 19 ∨ reg = compIdxReg ∨ reg = oldFinReg) →
          x₁.regs reg = x.regs reg) := by
      unfold dfsPushRoot
      wram_exec [hregs.cone, hregs.hoff, hregs.hstk, hu, hoff_r0, hoff_r1]
      refine ⟨dfsRegs_of_frame hregs fun reg hreg => by wram_simp, ?_, fun w_v => ?_, by wram_simp,
        by wram_simp [hfc], by wram_simp, by wram_simp, by wram_simp, fun a ha => by wram_simp,
        fun reg hreg => by rcases hreg with hreg | rfl | rfl <;> wram_simp⟩
      · mem_upd
        exact hcsr.of_eqOn
          (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
          (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
      · have hw_lt := w_v.isLt
        mem_upd
        repeat rw [Function.update_of_ne (by omega)]
        exact visAt_insert hvis r w_v
    have hs_eq : visit adj N r ⟨vis, []⟩ =
        ⟨(foldEmpty adj k' (adj r) vis₁).visited,
          r :: (foldEmpty adj k' (adj r) vis₁).finished⟩ :=
      (congrArg (fun fuel => visit adj fuel r ⟨vis, []⟩) hkN).trans (visit_eq_foldEmpty hmem)
    obtain ⟨z, ⟨t_loop, ht_loop, he_loop⟩, hRz⟩ := dfsLoop_cps adj offAddr edgeAddr visAddr
      finAddr stkAddr Mc hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit k' r (adj r) 0 0 F₀ 2 vis₁ x₁
      RootPost (by simp) (fun q hq => by simp) hk' hcons_root hx₁_r hx₁_csr hx₁_vis hx₁_p hx₁_fc
      hx₁_s0 hx₁_s1 hx₁_s2
      (fun y hy_r hy_csr hy_vis hy_p hy_fc hy_fin hy_out hy_fr => by
        have hend : ¬ (Cond.lt cZero pReg).Holds y := by
          change ¬ y.regs cZero < y.regs pReg
          have := hy_r.czero; omega
        refine ⟨y, ExecWithin.loop_exit hend, ?_⟩
        dsimp only [RootPost]
        rw [hs_eq]
        dsimp only
        refine ⟨hy_r, hy_csr, hy_vis, by rw [List.length_cons, hy_fc]; omega,
          fun q hq => ?_, fun a ha => ?_, fun reg hreg => (hy_fr reg hreg).trans (hx₁_fr reg hreg)⟩
        · simp only [List.reverse_cons] at hq ⊢; exact hy_fin q hq
        · simp only [List.length_cons] at ha
          exact (hy_out a (by omega)).trans (hx₁_out a (by omega)))
    have hbound : 2 + 1 + 11 + t_loop ≤
        16 + 60 * (visit adj N r ⟨vis, []⟩).finished.length +
          36 * outDegreeSum adj (visit adj N r ⟨vis, []⟩).finished := by
      rw [hs_eq]
      simp only [dfsFrameTime, List.length_cons, outDegreeSum, List.map_cons,
        List.sum_cons] at ht_loop ⊢
      omega
    unfold visitRootCode
    wram_exec [hregs.czero, hregs.hvis, hu, hvis_0]
    refine WP.of_execWithin hx₁_ex ?_
    refine WP.of_execWithin ⟨t_loop, le_rfl, he_loop⟩ ?_
    exact ⟨by omega, hRz⟩

end Cslib.Algorithms.WordRAM.DFS
