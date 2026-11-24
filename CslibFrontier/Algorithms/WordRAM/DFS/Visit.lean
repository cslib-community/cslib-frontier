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

local macro "reg_ne" : tactic =>
  `(tactic| exact Fin.ne_of_val_ne (by
    simp only [ne_eq, Fin.ext_iff, cZero, cOne, cThree, nVerts, offB, edgeB, visB, finB, stkB,
      curB, revOffB, revEdgeB, ordB, compB, iReg, pReg, finCnt, compIdxReg, oldFinReg, uReg, vReg,
      jReg, jEndReg, addr, outReg] at *
    omega))

local macro "regs_lt" : tactic =>
  `(tactic| (
    repeat (first
      | rw [Data.write_regs_apply]
      | rw [Data.set_regs_of_ne (by reg_ne)])
    try rfl))

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

private theorem visit_nil_struct {V : Type*} [DecidableEq V] (adj : V → List V) :
    ∀ (k : ℕ) (u : V) (vis : Finset V),
      let s := visit adj k u ⟨vis, []⟩
      s.finished.Nodup ∧ (∀ x ∈ s.finished, x ∉ vis) ∧
        (∀ x, x ∈ s.visited ↔ x ∈ vis ∨ x ∈ s.finished)
  | 0, _, vis => ⟨List.nodup_nil, by simp [visit], by simp [visit]⟩
  | k + 1, u, vis => by
    by_cases hu : u ∈ vis
    · simp [visit, hu]
    · have hfold : ∀ (es : List V) (v₀ : Finset V),
          let t := foldEmpty adj k es v₀
          t.finished.Nodup ∧ (∀ x ∈ t.finished, x ∉ v₀) ∧
            (∀ x, x ∈ t.visited ↔ x ∈ v₀ ∨ x ∈ t.finished) := by
        intro es
        induction es with
        | nil => intro v₀; exact ⟨List.nodup_nil, by simp [foldEmpty], by simp [foldEmpty]⟩
        | cons w es ih =>
          intro v₀
          obtain ⟨hnd₁, hdis₁, hvis₁⟩ := visit_nil_struct adj k w v₀
          obtain ⟨hnd₂, hdis₂, hvis₂⟩ := ih (visit adj k w ⟨v₀, []⟩).visited
          rw [foldEmpty_cons]
          dsimp only
          refine ⟨List.nodup_append.2 ⟨hnd₂, hnd₁, fun x hx₂ y hx₁ hxy => ?_⟩,
            fun x hx => ?_, fun x => ?_⟩
          · subst hxy
            exact hdis₂ x hx₂ ((hvis₁ x).2 (.inr hx₁))
          · rcases List.mem_append.1 hx with hx₂ | hx₁
            · exact fun hv => hdis₂ x hx₂ ((hvis₁ x).2 (.inl hv))
            · exact hdis₁ x hx₁
          · rw [hvis₂ x, hvis₁ x, List.mem_append]
            tauto
      obtain ⟨hnd, hdis, hvis⟩ := hfold (adj u) (insert u vis)
      rw [visit_eq_foldEmpty hu]
      dsimp only
      refine ⟨List.nodup_cons.2 ⟨fun hmem => hdis u hmem (Finset.mem_insert_self u vis), hnd⟩,
        fun x hx => ?_, fun x => ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hu
        · exact fun hv => hdis x hx (Finset.mem_insert_of_mem hv)
      · rw [hvis x, Finset.mem_insert, List.mem_cons]
        tauto

private theorem card_visit_nil {V : Type*} [DecidableEq V] (adj : V → List V)
    (k : ℕ) (u : V) (vis : Finset V) :
    (visit adj k u ⟨vis, []⟩).visited.card =
      vis.card + (visit adj k u ⟨vis, []⟩).finished.length := by
  obtain ⟨hnd, hdis, hvis⟩ := visit_nil_struct adj k u vis
  have hdisj : Disjoint vis (visit adj k u ⟨vis, []⟩).finished.toFinset :=
    Finset.disjoint_right.2 fun x hx => hdis x (List.mem_toFinset.1 hx)
  have hunion : (visit adj k u ⟨vis, []⟩).visited =
      vis ∪ (visit adj k u ⟨vis, []⟩).finished.toFinset := by
    ext x
    simp [hvis x]
  rw [hunion, Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup hnd]

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
    DfsRegs offAddr edgeAddr visAddr finAddr stkAddr y :=
  { czero := (hfr cZero (by decide)).trans hx.czero
    cone := (hfr cOne (by decide)).trans hx.cone
    cthree := (hfr cThree (by decide)).trans hx.cthree
    hoff := (hfr offB (by decide)).trans hx.hoff
    hedge := (hfr edgeB (by decide)).trans hx.hedge
    hvis := (hfr visB (by decide)).trans hx.hvis
    hfin := (hfr finB (by decide)).trans hx.hfin
    hstk := (hfr stkB (by decide)).trans hx.hstk }

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
  have hjeq : csrOffset adj u.val + idx = csrOffset adj (u.val + 1) := by omega
  have hstk1' : x.mem (stkAddr + 3 * d + 1) = csrOffset adj (u.val + 1) := hstk1.trans hjeq
  have hu_lt := u.isLt
  have hf_3d : Fits w (3 * d) := hfit.of_le (by omega)
  have hf_s0 : Fits w (stkAddr + 3 * d) := hfit.of_le (by omega)
  have hf_s1 : Fits w (stkAddr + 3 * d + 1) := hfit.of_le (by omega)
  have hf_s2 : Fits w (stkAddr + 3 * d + 1 + 1) := hfit.of_le (by omega)
  have hf_fin : Fits w (finAddr + F₀) := hfit.of_le (by omega)
  have hf_fc1 : Fits w (F₀ + 1) := hfit.of_le (by omega)
  let PopPost (x₁ : Data 28) : Prop :=
    DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt vis visAddr x₁.mem ∧
      x₁.regs pReg = d ∧
      x₁.regs finCnt = F₀ + 1 ∧
      x₁.mem (finAddr + F₀) = u.val ∧
      (∀ a, ¬ (a = finAddr + F₀) → x₁.mem a = x.mem a) ∧
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r)
  change ∃ x₁, ExecWithin w dfsStepBody x x₁ 16 ∧ PopPost x₁
  have hstk2' : x.mem (stkAddr + 3 * d + 1 + 1) = csrOffset adj (u.val + 1) := by
    simpa [Nat.add_assoc] using hstk2
  unfold dfsStepBody
  wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
    hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1', hstk2',
    hf_3d, hf_s0, hf_s1, hf_s2, hf_fin, hf_fc1]
  dsimp only [PopPost]
  refine ⟨?_, ?_, ?_, by wram_simp, by wram_simp, ?_, fun a ha => ?_, fun r hr => ?_⟩
  · refine dfsRegs_of_frame hregs fun r hr => ?_
    regs_lt
  · mem_upd
    exact hcsr.of_eqOn
      (fun _ _ => Function.update_of_ne (by omega) _ _)
      (fun _ _ => Function.update_of_ne (by omega) _ _)
  · intro w_v; mem_upd
    rw [Function.update_of_ne (by have := w_v.isLt; omega)]; exact hvis w_v
  · mem_upd; exact Function.update_self _ _ _
  · mem_upd; exact Function.update_of_ne ha _ _
  · have hv : r ≠ vReg := by reg_ne
    have ha : r ≠ addr := by reg_ne
    have hu' : r ≠ uReg := by reg_ne
    have hj : r ≠ jReg := by reg_ne
    have hje : r ≠ jEndReg := by reg_ne
    have hp' : r ≠ pReg := by reg_ne
    have hfc' : r ≠ finCnt := by reg_ne
    simp only [Data.write_regs_apply, Data.set_regs_of_ne hv, Data.set_regs_of_ne ha,
      Data.set_regs_of_ne hu', Data.set_regs_of_ne hj, Data.set_regs_of_ne hje,
      Data.set_regs_of_ne hp', Data.set_regs_of_ne hfc']

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
  have hoff_u := csrOffset_succ adj u.isLt
  simp only [Fin.eta] at hoff_u
  set j := csrOffset adj u.val + idx
  have hj_lt_end : j < csrOffset adj (u.val + 1) := by omega
  have hj_lt_N : j < csrOffset adj N :=
    lt_of_lt_of_le hj_lt_end (csrOffset_mono adj (by have := u.isLt; omega : u.val + 1 ≤ N))
  have hedge_j : x.mem (edgeAddr + j) = v.val := by
    rw [show edgeAddr + j = edgeAddr + csrOffset adj u.val + idx by dsimp only [j]; omega,
      hcsr.2 u idx hidx_lt, hv_eq]
  have hvis_v1 : x.mem (visAddr + v.val) = 1 := by simpa [hmem] using hvis v
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  have hf_3d : Fits w (3 * d) := hfit.of_le (by omega)
  have hf_s0 : Fits w (stkAddr + 3 * d) := hfit.of_le (by omega)
  have hf_s1 : Fits w (stkAddr + 3 * d + 1) := hfit.of_le (by omega)
  have hf_s2 : Fits w (stkAddr + 3 * d + 1 + 1) := hfit.of_le (by omega)
  have hf_j1 : Fits w (j + 1) := hfit.of_le (by omega)
  have hf_ej : Fits w (edgeAddr + j) := hfit.of_le (by omega)
  have hf_vv : Fits w (visAddr + v.val) := hfit.of_le (by omega)
  have hstk2' : x.mem (stkAddr + 3 * d + 1 + 1) = csrOffset adj (u.val + 1) := by
    simpa [Nat.add_assoc] using hstk2
  let SkipPost (x₁ : Data 28) : Prop :=
    DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt vis visAddr x₁.mem ∧
      x₁.regs pReg = d + 1 ∧
      x₁.regs finCnt = F₀ ∧
      x₁.mem (stkAddr + 3 * d) = u.val ∧
      x₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) ∧
      x₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) ∧
      (∀ a, a ≠ stkAddr + 3 * d + 1 → x₁.mem a = x.mem a) ∧
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r)
  change ∃ x₁, ExecWithin w dfsStepBody x x₁ 24 ∧ SkipPost x₁
  unfold dfsStepBody
  wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
    hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1, hstk2', hedge_j, hvis_v1, hj_lt_end,
    hf_3d, hf_s0, hf_s1, hf_s2, hf_j1, hf_ej, hf_vv]
  dsimp only [SkipPost]
  refine ⟨?_, ?_, ?_, by wram_simp, by wram_simp; exact hfc, ?_, ?_, ?_,
    fun a ha => ?_, fun r hr => ?_⟩
  · refine dfsRegs_of_frame hregs fun r hr => ?_
    regs_lt
  · mem_upd
    exact hcsr.of_eqOn
      (fun _ _ => Function.update_of_ne (by omega) _ _)
      (fun _ _ => Function.update_of_ne (by omega) _ _)
  · intro w_v; mem_upd
    rw [Function.update_of_ne (by have := w_v.isLt; omega)]; exact hvis w_v
  · mem_upd; rw [Function.update_of_ne (by omega)]; exact hstk0
  · mem_upd; rw [Function.update_self]; omega
  · mem_upd; rw [Function.update_of_ne (by omega)]; exact hstk2
  · mem_upd; exact Function.update_of_ne ha _ _
  · have hv : r ≠ vReg := by reg_ne
    have ha : r ≠ addr := by reg_ne
    have hu' : r ≠ uReg := by reg_ne
    have hj : r ≠ jReg := by reg_ne
    have hje : r ≠ jEndReg := by reg_ne
    have hp' : r ≠ pReg := by reg_ne
    simp only [Data.write_regs_apply, Data.set_regs_of_ne hv, Data.set_regs_of_ne ha,
      Data.set_regs_of_ne hu', Data.set_regs_of_ne hj, Data.set_regs_of_ne hje,
      Data.set_regs_of_ne hp']

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
  have hoff_u := csrOffset_succ adj u.isLt
  simp only [Fin.eta] at hoff_u
  set j := csrOffset adj u.val + idx
  have hj_lt_end : j < csrOffset adj (u.val + 1) := by omega
  have hj_lt_N : j < csrOffset adj N :=
    lt_of_lt_of_le hj_lt_end (csrOffset_mono adj (by have := u.isLt; omega : u.val + 1 ≤ N))
  have hedge_j : x.mem (edgeAddr + j) = v.val := by
    rw [show edgeAddr + j = edgeAddr + csrOffset adj u.val + idx by dsimp only [j]; omega,
      hcsr.2 u idx hidx_lt, hv_eq]
  have hvis_v0 : x.mem (visAddr + v.val) = 0 := by simpa [hmem] using hvis v
  set vis₁ := insert v vis
  have hcard_vis₁_le : vis₁.card ≤ N := by
    have := Finset.card_le_univ vis₁; simpa using this
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  have hoff_v0 : x.mem (offAddr + v.val) = csrOffset adj v.val := hcsr.1 v.val (by omega)
  have hoff_v1 : x.mem (offAddr + v.val + 1) = csrOffset adj (v.val + 1) := by
    simpa [Nat.add_assoc] using hcsr.1 (v.val + 1) (by omega)
  have hf_3d : Fits w (3 * d) := hfit.of_le (by omega)
  have hf_s0 : Fits w (stkAddr + 3 * d) := hfit.of_le (by omega)
  have hf_s1 : Fits w (stkAddr + 3 * d + 1) := hfit.of_le (by omega)
  have hf_s2 : Fits w (stkAddr + 3 * d + 1 + 1) := hfit.of_le (by omega)
  have hf_j1 : Fits w (j + 1) := hfit.of_le (by omega)
  have hf_ej : Fits w (edgeAddr + j) := hfit.of_le (by omega)
  have hf_vv : Fits w (visAddr + v.val) := hfit.of_le (by omega)
  have hf_ov0 : Fits w (offAddr + v.val) := hfit.of_le (by omega)
  have hf_ov1 : Fits w (offAddr + v.val + 1) := hfit.of_le (by omega)
  have hf_3d1 : Fits w (3 * (d + 1)) := hfit.of_le (by omega)
  have hf_c0 : Fits w (stkAddr + 3 * (d + 1)) := hfit.of_le (by omega)
  have hf_c1 : Fits w (stkAddr + 3 * (d + 1) + 1) := hfit.of_le (by omega)
  have hf_c2 : Fits w (stkAddr + 3 * (d + 1) + 1 + 1) := hfit.of_le (by omega)
  have hf_p2 : Fits w (d + 1 + 1) := hfit.of_le (by omega)
  have hstk2' : x.mem (stkAddr + 3 * d + 1 + 1) = csrOffset adj (u.val + 1) := by
    simpa [Nat.add_assoc] using hstk2
  let PushPost (x₁ : Data 28) : Prop :=
    DfsRegs offAddr edgeAddr visAddr finAddr stkAddr x₁ ∧
      CSRAt adj offAddr edgeAddr x₁.mem ∧
      VisAt vis₁ visAddr x₁.mem ∧
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
      (∀ r : Fin 28, (r.val < 19 ∨ r = compIdxReg ∨ r = oldFinReg) → x₁.regs r = x.regs r)
  change ∃ x₁, ExecWithin w dfsStepBody x x₁ 34 ∧ PushPost x₁
  unfold dfsStepBody
  wram_exec [hregs.czero, hregs.cone, hregs.cthree, hregs.hoff, hregs.hedge, hregs.hvis,
    hregs.hfin, hregs.hstk, hp, hfc, hstk0, hstk1, hstk2', hedge_j, hvis_v0, hj_lt_end,
    hoff_v0, hoff_v1, hf_3d, hf_s0, hf_s1, hf_s2, hf_j1, hf_ej, hf_vv,
    hf_ov0, hf_ov1, hf_3d1, hf_c0, hf_c1, hf_c2, hf_p2]
  dsimp only [PushPost]
  refine ⟨?_, ?_, ?_, by wram_simp, by wram_simp; exact hfc,
    ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun r hr => ?_⟩
  · refine dfsRegs_of_frame hregs fun r hr => ?_
    regs_lt
  · mem_upd
    exact hcsr.of_eqOn
      (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
      (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
  · intro w_v; mem_upd
    have hw_lt := w_v.isLt
    repeat rw [Function.update_of_ne (by omega)]
    by_cases hwv : w_v = v
    · subst hwv
      rw [Function.update_self]
      simp [vis₁]
    · have hne : visAddr + w_v.val ≠ visAddr + v.val := fun h => hwv (Fin.ext (by omega))
      rw [Function.update_of_ne hne, Function.update_of_ne (by omega)]
      simpa [vis₁, hwv] using hvis w_v
  · mem_upd; repeat rw [Function.update_of_ne (by omega)]
    exact hstk0
  · mem_upd; repeat rw [Function.update_of_ne (by omega)]
    rw [Function.update_self]; omega
  · mem_upd; repeat rw [Function.update_of_ne (by omega)]
    exact hstk2
  · mem_upd
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · mem_upd
    rw [Function.update_of_ne (by omega), Function.update_self]; omega
  · mem_upd
    rw [show stkAddr + 3 * (d + 1) + 2 = stkAddr + 3 * (d + 1) + 1 + 1 by omega,
      Function.update_self]
  · mem_upd
    repeat rw [Function.update_of_ne (by omega)]
  · have hv : r ≠ vReg := by reg_ne
    have ha : r ≠ addr := by reg_ne
    have hu' : r ≠ uReg := by reg_ne
    have hj : r ≠ jReg := by reg_ne
    have hje : r ≠ jEndReg := by reg_ne
    have hp' : r ≠ pReg := by reg_ne
    simp only [Data.write_regs_apply, Data.set_regs_of_ne hv, Data.set_regs_of_ne ha,
      Data.set_regs_of_ne hu', Data.set_regs_of_ne hj, Data.set_regs_of_ne hje,
      Data.set_regs_of_ne hp']

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
          (∀ q (hq : q < s.finished.reverse.length),
            y.mem (finAddr + F₀ + q) = (s.finished.reverse[q]).val) →
          y.mem (finAddr + F₀ + s.finished.length) = u.val →
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
      obtain ⟨x₁, ⟨t₁, ht₁, he₁⟩, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_fin0, hx₁_out,
        hx₁_fr⟩ :=
        dfsStepBody_pop adj offAddr edgeAddr visAddr finAddr stkAddr Mc
          hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit u idx d F₀ vis hidx hcons
          hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
      obtain ⟨z, ⟨t₂, ht₂, he₂⟩, hQz⟩ := hcont x₁ hx₁_r hx₁_csr hx₁_vis hx₁_p
        (by simpa [foldEmpty] using hx₁_fc)
        (fun q hq => by simp [foldEmpty] at hq)
        (by simpa [foldEmpty] using hx₁_fin0)
        (fun a ha => hx₁_out a (by dsimp only [foldEmpty, List.length_nil] at ha; omega))
        hx₁_fr
      have hlt : (Cond.lt cZero pReg).Holds x := by
        have := hregs.czero
        change x.regs cZero < x.regs pReg; omega
      exact ⟨z, ⟨t₁ + t₂ + 2, by dsimp only [dfsFrameTime, foldEmpty, outDegreeSum]; omega,
        Exec.loop_iter hlt he₁ he₂⟩, hQz⟩
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
        have hcongr : (adj u)[idx + 1 + q]'(by omega) = (adj u)[idx + (q + 1)]'(by omega) := by
          congr 1; omega
        exact hcongr.trans (by simpa only [List.getElem_cons_succ] using h)
      by_cases hmem : v ∈ vis
      · -- Case 1: `v ∈ vis`
        have hvisit_v : visit adj k v ⟨vis, []⟩ = ⟨vis, []⟩ := by
          cases k with
          | zero => rfl
          | succ k' => exact visit_of_mem hmem
        have hfold_eq : foldEmpty adj k (v :: es') vis = foldEmpty adj k es' vis := by
          rw [foldEmpty_cons, hvisit_v]
          simp
        obtain ⟨x₁, ⟨t₁, ht₁, he₁⟩, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_s0, hx₁_s1,
          hx₁_s2, hx₁_out, hx₁_fr⟩ :=
          dfsStepBody_skip adj offAddr edgeAddr visAddr finAddr stkAddr Mc
            hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit u v idx d F₀ vis (by omega) hv_eq hmem hcons
            hregs hcsr hvis hp hfc hstk0 hstk1 hstk2
        obtain ⟨z, ⟨t₂, ht₂, he₂⟩, hQz⟩ := ih_es (idx + 1) d F₀ T_cont vis x₁ Q (by omega) hes'
          hk hcons hx₁_r hx₁_csr hx₁_vis hx₁_p hx₁_fc hx₁_s0 hx₁_s1 hx₁_s2
          (fun y hy_r hy_csr hy_vis hy_p hy_fc hy_fin hy_u hy_out hy_fr => by
            rw [hfold_eq] at hcont
            exact hcont y hy_r hy_csr hy_vis hy_p hy_fc hy_fin hy_u
              (fun a ha => (hy_out a ha).trans (hx₁_out a (by omega)))
              (fun r hr => (hy_fr r hr).trans (hx₁_fr r hr)))
        have hlt : (Cond.lt cZero pReg).Holds x := by
          have := hregs.czero
          change x.regs cZero < x.regs pReg; omega
        refine ⟨z, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩, hQz⟩
        rw [hfold_eq]
        simp only [dfsFrameTime, List.length_cons] at ht₂ ⊢
        omega
      · -- Case 2: `v ∉ vis`
        have hcard_lt : vis.card < N := by simpa using Finset.card_lt_univ_of_notMem hmem
        rcases k with _ | k'
        · omega
        set vis₁ := insert v vis
        have hcard_vis₁ : vis₁.card = vis.card + 1 := Finset.card_insert_of_notMem hmem
        have hcard_vis₁_le : vis₁.card ≤ N := by
          have := Finset.card_le_univ vis₁; simpa using this
        have hk' : N - vis₁.card ≤ k' := by omega
        have hcons_child : F₀ + (d + 1) + 1 + (N - vis₁.card) ≤ N := by omega
        obtain ⟨x₁, ⟨t₁, ht₁, he₁⟩, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_d0, hx₁_d1,
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
          have := Finset.card_le_univ s₁.visited; simpa only [Fintype.card_fin] using this
        have hlen_s₁ : s₁.finished.length = s_child.finished.length + 1 := by
          rw [hs₁_eq]; rfl
        have hk_s₁ : N - s₁.visited.card ≤ k' + 1 := by omega
        have hcons_after : (F₀ + s₁.finished.length) + d + 1 + (N - s₁.visited.card) ≤ N := by
          omega
        obtain ⟨z, ⟨t₂, ht₂, he₂⟩, hQz⟩ := ih_k k' (Nat.lt_succ_self k') v (adj v) 0 (d + 1) F₀
          (dfsFrameTime adj es' s₂.finished + T_cont) vis₁ x₁ Q (Nat.zero_add _)
          (fun q hq => by simp only [Nat.zero_add]) hk' hcons_child hx₁_r hx₁_csr hx₁_vis hx₁_p
          hx₁_fc hx₁_c0 hx₁_c1 hx₁_c2
          (fun y₁ hy₁_r hy₁_csr hy₁_vis hy₁_p hy₁_fc hy₁_fin hy₁_v hy₁_out hy₁_fr => by
            rw [hsc_def] at hy₁_vis hy₁_fc hy₁_fin hy₁_v hy₁_out
            have hy₁_vis' : VisAt s₁.visited visAddr y₁.mem := by rw [hs₁_eq]; exact hy₁_vis
            have hy₁_fc' : y₁.regs finCnt = F₀ + s₁.finished.length := by
              rw [hlen_s₁]; exact hy₁_fc
            have hy₁_d0 : y₁.mem (stkAddr + 3 * d) = u.val :=
              (hy₁_out (stkAddr + 3 * d) (by omega)).trans hx₁_d0
            have hy₁_d1 : y₁.mem (stkAddr + 3 * d + 1) = csrOffset adj u.val + (idx + 1) :=
              (hy₁_out (stkAddr + 3 * d + 1) (by omega)).trans hx₁_d1
            have hy₁_d2 : y₁.mem (stkAddr + 3 * d + 2) = csrOffset adj (u.val + 1) :=
              (hy₁_out (stkAddr + 3 * d + 2) (by omega)).trans hx₁_d2
            rw [← hs₂_def]
            exact ih_es (idx + 1) d (F₀ + s₁.finished.length) T_cont s₁.visited y₁ Q
              (by omega) hes' hk_s₁ hcons_after hy₁_r hy₁_csr hy₁_vis' hy₁_p hy₁_fc'
              hy₁_d0 hy₁_d1 hy₁_d2
              (fun y₂ hy₂_r hy₂_csr hy₂_vis hy₂_p hy₂_fc hy₂_fin hy₂_u hy₂_out hy₂_fr => by
                rw [hs₂_def] at hy₂_vis hy₂_fc hy₂_fin hy₂_u hy₂_out
                have hy₂_vis' : VisAt (foldEmpty adj (k' + 1) (v :: es') vis).visited
                    visAddr y₂.mem := by
                  rw [hfold_cons]; exact hy₂_vis
                have hy₂_fc' : y₂.regs finCnt =
                    F₀ + (foldEmpty adj (k' + 1) (v :: es') vis).finished.length + 1 := by
                  rw [hfold_cons]; dsimp only; rw [List.length_append]; omega
                have hy₂_u' : y₂.mem (finAddr + F₀ +
                    (foldEmpty adj (k' + 1) (v :: es') vis).finished.length) = u.val := by
                  rw [hfold_cons]; dsimp only; rw [List.length_append]
                  rw [show finAddr + F₀ + (s₂.finished.length + s₁.finished.length) =
                    finAddr + (F₀ + s₁.finished.length) + s₂.finished.length by omega]
                  exact hy₂_u
                have hy₂_fin_all :
                    ∀ q (hq : q < (foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse.length),
                      y₂.mem (finAddr + F₀ + q) =
                        ((foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse[q]).val := by
                  intro q hq
                  have hrev : (foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse =
                      s_child.finished.reverse ++ [v] ++ s₂.finished.reverse := by
                    rw [hfold_cons, hs₁_eq]
                    simp only [List.reverse_append, List.reverse_cons, List.append_assoc]
                  have hrev2 : (foldEmpty adj (k' + 1) (v :: es') vis).finished.reverse =
                      s₁.finished.reverse ++ s₂.finished.reverse := by
                    rw [hfold_cons]; dsimp only; exact List.reverse_append
                  have hq_tot : q < s_child.finished.length + 1 + s₂.finished.length := by
                    rw [hrev] at hq
                    simp only [List.length_append, List.length_reverse,
                      List.length_singleton] at hq
                    omega
                  by_cases hq1 : q < s_child.finished.length
                  · have hpres : y₂.mem (finAddr + F₀ + q) = y₁.mem (finAddr + F₀ + q) :=
                      hy₂_out (finAddr + F₀ + q) (by omega)
                    rw [hpres, hy₁_fin q (by rw [List.length_reverse]; exact hq1)]
                    congr 1
                    simp only [hrev, List.append_assoc]
                    rw [List.getElem_append_left (by rw [List.length_reverse]; exact hq1)]
                  · by_cases hq2 : q = s_child.finished.length
                    · subst hq2
                      have hpres : y₂.mem (finAddr + F₀ + s_child.finished.length) =
                          y₁.mem (finAddr + F₀ + s_child.finished.length) :=
                        hy₂_out (finAddr + F₀ + s_child.finished.length) (by omega)
                      rw [hpres, hy₁_v]
                      congr 1
                      simp only [hrev, List.append_assoc]
                      rw [List.getElem_append_right (by rw [List.length_reverse])]
                      simp only [List.length_reverse, Nat.sub_self, List.singleton_append,
                        List.getElem_cons_zero]
                    · set q' := q - s₁.finished.length
                      have hq'_lt : q' < s₂.finished.reverse.length := by
                        rw [List.length_reverse]; omega
                      have haddr_eq :
                          finAddr + F₀ + q = finAddr + (F₀ + s₁.finished.length) + q' := by
                        omega
                      rw [haddr_eq, hy₂_fin q' hq'_lt]
                      congr 1
                      simp only [hrev2]
                      have hge : s₁.finished.reverse.length ≤ q := by
                        rw [List.length_reverse]; omega
                      rw [List.getElem_append_right hge]
                      congr 1
                      rw [List.length_reverse]
                exact hcont y₂ hy₂_r hy₂_csr hy₂_vis' hy₂_p hy₂_fc' hy₂_fin_all hy₂_u'
                  (fun a ha => by
                    rw [hfold_cons] at ha; dsimp only at ha
                    rw [List.length_append] at ha
                    have h2 := hy₂_out a (by omega)
                    have h1 := hy₁_out a (by omega)
                    have h0 := hx₁_out a (by have := v.isLt; omega)
                    exact h2.trans (h1.trans h0))
                  (fun r hr => (hy₂_fr r hr).trans ((hy₁_fr r hr).trans (hx₁_fr r hr)))))
        have hlt : (Cond.lt cZero pReg).Holds x := by
          have := hregs.czero
          change x.regs cZero < x.regs pReg; omega
        refine ⟨z, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩, hQz⟩
        rw [hsc_def] at ht₂
        have hout_eq : outDegreeSum adj (foldEmpty adj (k' + 1) (v :: es') vis).finished =
            outDegreeSum adj s₂.finished +
              ((adj v).length + outDegreeSum adj s_child.finished) := by
          rw [hfold_cons, hs₁_eq]
          dsimp only
          rw [outDegreeSum_append]
          simp only [outDegreeSum, List.map_cons, List.sum_cons]
        have hlen_eq : (foldEmpty adj (k' + 1) (v :: es') vis).finished.length =
            s₂.finished.length + (1 + s_child.finished.length) := by
          rw [hfold_cons, hs₁_eq]; dsimp only; rw [List.length_append, List.length_cons]; omega
        simp only [dfsFrameTime, List.length_cons, hout_eq, hlen_eq] at ht₂ ⊢
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
  have hf_vr : Fits w (visAddr + r.val) := hfit.of_le (by omega)
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
    wram_exec [hregs.czero, hregs.hvis, hu, hvis_1, hf_vr]
    dsimp only [RootPost]
    rw [hs_eq]
    refine ⟨?_, ?_, ?_, ?_, fun _ hq => by simp at hq, fun _ _ => rfl, fun reg hreg => ?_⟩
    · refine dfsRegs_of_frame hregs fun reg hreg => ?_
      regs_lt
    · mem_upd; exact hcsr
    · intro w_v; mem_upd; exact hvis w_v
    · wram_simp; simpa using hfc
    · regs_lt
  · have hvis_0 : x.mem (visAddr + r.val) = 0 := by simpa [hmem] using hvis_r
    set vis₁ := insert r vis
    have hcard_vis₁ : vis₁.card = vis.card + 1 := Finset.card_insert_of_notMem hmem
    have hcard_vis₁_le : vis₁.card ≤ N := by
      have := Finset.card_le_univ vis₁; simpa using this
    have hk' : N - vis₁.card ≤ k' := by omega
    have hcons_root : F₀ + 0 + 1 + (N - vis₁.card) ≤ N := by omega
    have hoff_r0 : x.mem (offAddr + r.val) = csrOffset adj r.val := hcsr.1 r.val (by omega)
    have hoff_r1 : x.mem (offAddr + r.val + 1) = csrOffset adj (r.val + 1) := by
      simpa [Nat.add_assoc] using hcsr.1 (r.val + 1) (by omega)
    have hf_or0 : Fits w (offAddr + r.val) := hfit.of_le (by omega)
    have hf_or1 : Fits w (offAddr + r.val + 1) := hfit.of_le (by omega)
    have hf_s1 : Fits w (stkAddr + 1) := hfit.of_le (by omega)
    have hf_s2 : Fits w (stkAddr + 1 + 1) := hfit.of_le (by omega)
    let PushRootPost (x₁ : Data 28) : Prop :=
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
          x₁.regs reg = x.regs reg)
    have hpush : ∃ x₁, ExecWithin w dfsPushRoot
        ((x.set addr (visAddr + r.val)).set jReg 0) x₁ 11 ∧ PushRootPost x₁ := by
      unfold dfsPushRoot
      wram_exec [hregs.cone, hregs.hoff, hregs.hstk, hu, hoff_r0, hoff_r1,
        hf_or0, hf_or1, hf_s1, hf_s2]
      dsimp only [PushRootPost]
      refine ⟨?_, ?_, ?_, by wram_simp, by wram_simp; exact hfc,
        ?_, ?_, ?_, fun a ha => ?_, fun reg hreg => ?_⟩
      · refine dfsRegs_of_frame hregs fun reg hreg => ?_
        regs_lt
      · mem_upd
        exact hcsr.of_eqOn
          (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
          (fun _ _ => by repeat rw [Function.update_of_ne (by omega)])
      · intro w_v; mem_upd
        have hw_lt := w_v.isLt
        repeat rw [Function.update_of_ne (by omega)]
        exact visAt_insert hvis r w_v
      · mem_upd
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Nat.add_zero, Function.update_self]
      · mem_upd
        rw [Function.update_of_ne (by omega), Nat.mul_zero, Nat.add_zero, Function.update_self]
        omega
      · mem_upd
        rw [show stkAddr + 2 = stkAddr + 1 + 1 by omega, Function.update_self]
      · mem_upd
        repeat rw [Function.update_of_ne (by omega)]
      · have ha : reg ≠ addr := by reg_ne
        have hj : reg ≠ jReg := by reg_ne
        have hje : reg ≠ jEndReg := by reg_ne
        have hp' : reg ≠ pReg := by reg_ne
        simp only [Data.write_regs_apply, Data.set_regs_of_ne ha, Data.set_regs_of_ne hj,
          Data.set_regs_of_ne hje, Data.set_regs_of_ne hp']
    obtain ⟨x₁, hx₁_ex, hx₁_r, hx₁_csr, hx₁_vis, hx₁_p, hx₁_fc, hx₁_s0, hx₁_s1, hx₁_s2,
      hx₁_out, hx₁_fr⟩ := hpush
    have hs_eq : visit adj N r ⟨vis, []⟩ =
        ⟨(foldEmpty adj k' (adj r) vis₁).visited,
          r :: (foldEmpty adj k' (adj r) vis₁).finished⟩ :=
      (congrArg (fun fuel => visit adj fuel r ⟨vis, []⟩) hkN).trans (visit_eq_foldEmpty hmem)
    obtain ⟨z, ⟨t_loop, ht_loop, he_loop⟩, hRz⟩ := dfsLoop_cps adj offAddr edgeAddr visAddr
      finAddr stkAddr Mc hdisj1 hdisj2 hdisj3 hdisj4 hmc hfit k' r (adj r) 0 0 F₀ 2 vis₁ x₁
      RootPost (by simp) (fun q hq => by simp) hk' hcons_root hx₁_r hx₁_csr hx₁_vis hx₁_p hx₁_fc
      hx₁_s0 hx₁_s1 hx₁_s2
      (fun y hy_r hy_csr hy_vis hy_p hy_fc hy_fin hy_rval hy_out hy_fr => by
        have hend : ¬ (Cond.lt cZero pReg).Holds y := by
          change ¬ y.regs cZero < y.regs pReg
          have := hy_r.czero; omega
        refine ⟨y, ⟨2, le_rfl, Exec.loop_exit hend⟩, ?_⟩
        dsimp only [RootPost]
        rw [hs_eq]
        dsimp only
        refine ⟨hy_r, hy_csr, hy_vis, by rw [List.length_cons, hy_fc]; omega,
          fun q hq => ?_, fun a ha => ?_, fun reg hreg => (hy_fr reg hreg).trans (hx₁_fr reg hreg)⟩
        · simp only [List.reverse_cons, List.length_append, List.length_reverse,
            List.length_singleton] at hq
          by_cases hq_lt : q < (foldEmpty adj k' (adj r) vis₁).finished.length
          · rw [hy_fin q (by simpa using hq_lt)]
            congr 1
            simp only [List.reverse_cons]
            rw [List.getElem_append_left (by simpa using hq_lt)]
          · have hq_eq : q = (foldEmpty adj k' (adj r) vis₁).finished.length := by omega
            subst hq_eq
            rw [hy_rval]
            congr 1
            simp
        · simp only [List.length_cons] at ha
          have h1 := hy_out a (by omega)
          have h0 := hx₁_out a (by omega)
          exact h1.trans h0)
    have hbound : 2 + 1 + 11 + t_loop ≤
        16 + 60 * (visit adj N r ⟨vis, []⟩).finished.length +
          36 * outDegreeSum adj (visit adj N r ⟨vis, []⟩).finished := by
      rw [hs_eq]
      simp only [dfsFrameTime, List.length_cons, outDegreeSum, List.map_cons,
        List.sum_cons] at ht_loop ⊢
      omega
    unfold visitRootCode
    wram_exec [hregs.czero, hregs.hvis, hu, hvis_0, hf_vr]
    refine WP.of_execWithin hx₁_ex ?_
    refine WP.of_execWithin ⟨t_loop, le_rfl, he_loop⟩ ?_
    exact ⟨by omega, hRz⟩


end Cslib.Algorithms.WordRAM.DFS
