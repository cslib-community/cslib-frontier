/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DFS.Visit
import all CslibFrontier.Algorithms.WordRAM.DFS.CSR
import all CslibFrontier.Algorithms.WordRAM.DFS.Visit
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Word-RAM forward DFS finishing order (`O(N + M)`)

## Main definitions

* `Cslib.Algorithms.WordRAM.DFS.forwardDFSCode`: visits every vertex in order to record the
  DFS finishing order.

## Main results

* `Cslib.Algorithms.WordRAM.DFS.forwardDFSCode_spec`: writes
  `(topologicalSort adj (List.finRange N)).reverse` in `87 * N + 36 * Mc + 10` instructions.
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

/-! ### Pass 1: Forward DFS finishing order (`O(N + M)`) -/

/-- Visit vertex `iReg` as a DFS root and advance `iReg`. -/
private def forwardDFSBody : Code .standard 28 :=
  (ram[ uReg ← iReg ]).seq (visitRootCode.seq (ram[ iReg ← iReg + cOne ]))

/-- Forward pass: clear the visited flags and visit every vertex as a root, writing the DFS
finishing order at `finB`. -/
def forwardDFSCode : Code .standard 28 :=
  (zeroBlockCode visB).seq
    ((ram[ finCnt ← cZero; iReg ← cZero ]).seq
      (.loop (.lt iReg nVerts) forwardDFSBody))

private theorem forwardDFSLoop_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) :
    ∀ (rs : List (Fin N)) (idx : ℕ) (vis : Finset (Fin N)) (F₀ : ℕ) (x : Data 28)
      (_ : idx + rs.length = N),
      (∀ q (hq : q < rs.length), rs[q].val = idx + q) →
      F₀ = vis.card →
      DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc) (kOrdAddr wb N Mc)
        (kStkAddr wb N Mc) x →
      CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem →
      VisAt vis (kVisAddr wb N Mc) x.mem →
      x.regs nVerts = N →
      x.regs iReg = idx →
      x.regs finCnt = F₀ →
      ∃ y,
        let s := foldEmpty adj N rs vis
        ExecWithin w (.loop (.lt iReg nVerts) forwardDFSBody) x y
          (22 * rs.length + 60 * s.finished.length + 36 * outDegreeSum adj s.finished + 2) ∧
        DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc) (kOrdAddr wb N Mc)
          (kStkAddr wb N Mc) y ∧
        CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) y.mem ∧
        VisAt s.visited (kVisAddr wb N Mc) y.mem ∧
        y.regs finCnt = F₀ + s.finished.length ∧
        (∀ q (hq : q < s.finished.reverse.length),
          y.mem (kOrdAddr wb N Mc + F₀ + q) = (s.finished.reverse[q]).val) ∧
        (∀ a, ¬ ((kVisAddr wb N Mc ≤ a ∧ a < kVisAddr wb N Mc + N) ∨
            (kOrdAddr wb N Mc + F₀ ≤ a ∧ a < kOrdAddr wb N Mc + F₀ + s.finished.length) ∨
            (kStkAddr wb N Mc ≤ a ∧ a < kStkAddr wb N Mc + 3 * N)) → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], idx, vis, F₀, x, hidx, _, _, hregs, hcsr, hvis, hNv, hi, hfc => by
    simp only [List.length_nil, Nat.add_zero] at hidx
    have hend : ¬ (Cond.lt iReg nVerts).Holds x := by
      change ¬ x.regs iReg < x.regs nVerts; omega
    refine ⟨x, ⟨2, by simp [foldEmpty, outDegreeSum], Exec.loop_exit hend⟩,
      hregs, hcsr, hvis, by simpa [foldEmpty] using hfc,
      fun _ hq => by simp [foldEmpty] at hq, fun _ _ => rfl, fun _ _ => rfl⟩
  | r :: rs, idx, vis, F₀, x, hidx, hrs, hF₀, hregs, hcsr, hvis, hNv, hi, hfc => by
    simp only [List.length_cons] at hidx
    have hr_val : r.val = idx := by
      have h0 := hrs 0 (by simp)
      rwa [List.getElem_cons_zero, Nat.add_zero] at h0
    have hcard_le : vis.card ≤ N := by have := Finset.card_le_univ vis; simpa using this
    have hcons : F₀ + (N - vis.card) ≤ N := by omega
    have hfit_stk : Fits w (kStkAddr wb N Mc + 3 * N + Mc + 4) :=
      hfit.of_le (by simp only [kStkAddr, kTopAddr]; omega)
    let st_u := x.set uReg idx
    obtain ⟨y₁, hy₁_ex, hy₁_r, hy₁_csr, hy₁_vis, hy₁_fc, hy₁_ord, hy₁_out, hy₁_fr⟩ :=
      visitRootCode_spec hN adj (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc)
        (kOrdAddr wb N Mc) (kStkAddr wb N Mc) Mc
        (by simp only [kOffAddr, kVisAddr]; omega)
        (by simp only [kEdgeAddr, kVisAddr]; omega)
        (by simp only [kVisAddr, kOrdAddr]; omega)
        (by simp only [kOrdAddr, kStkAddr]; omega)
        hmc hfit_stk r F₀ vis hcons (x := st_u)
        (dfsRegs_of_frame hregs fun reg hreg => by
          dsimp only [st_u]; regs_lt)
        hcsr hvis (by dsimp only [st_u]; wram_simp; omega)
        (by dsimp only [st_u]; wram_simp; exact hfc)
    set s₁ := visit adj N r ⟨vis, []⟩
    have hy₁_i : y₁.regs iReg = idx :=
      (hy₁_fr iReg (.inl (by decide))).trans (by dsimp only [st_u]; wram_simp; exact hi)
    have hy₁_1 : y₁.regs cOne = 1 := hy₁_r.cone
    have hf_i1 : Fits w (idx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    have hbody_ex : ExecWithin w forwardDFSBody x (y₁.set iReg (idx + 1))
        (18 + 60 * s₁.finished.length + 36 * outDegreeSum adj s₁.finished) := by
      have h1 : ExecWithin (B := .standard) w (ram[ uReg ← iReg ]) x st_u 1 := by
        have htriv : st_u = x.set uReg idx := rfl
        wram_exec [hi]
      have h2 : ExecWithin w (ram[ iReg ← iReg + cOne ]) y₁ (y₁.set iReg (idx + 1)) 1 := by
        wram_exec [hy₁_i, hy₁_1, hf_i1]
      exact (h1.seq (hy₁_ex.seq h2)).mono (by omega)
    set x₂ := y₁.set iReg (idx + 1)
    have hcard_s₁ : s₁.visited.card = vis.card + s₁.finished.length :=
      card_visit_nil adj N r vis
    have hcard_s₁_le : s₁.visited.card ≤ N := by
      have := Finset.card_le_univ s₁.visited; simpa using this
    have hrs' : ∀ q (hq : q < rs.length), rs[q].val = (idx + 1) + q := by
      intro q hq
      have h := hrs (q + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 q] using h
    obtain ⟨y, hy_ex, hy_r, hy_csr, hy_vis, hy_fc, hy_ord, hy_out, hy_fr⟩ :=
      forwardDFSLoop_spec hN adj wb Mc hmc hfit rs (idx + 1) s₁.visited
        (F₀ + s₁.finished.length) x₂ (by omega) hrs' (by omega)
        (dfsRegs_of_frame hy₁_r fun reg hreg => by
          dsimp only [x₂]; regs_lt)
        hy₁_csr hy₁_vis
        (by
          dsimp only [x₂]; wram_simp
          exact (hy₁_fr nVerts (.inl (by decide))).trans
            (by dsimp only [st_u]; wram_simp; exact hNv))
        (by dsimp only [x₂]; wram_simp)
        (by dsimp only [x₂]; wram_simp; exact hy₁_fc)
    set s₂ := foldEmpty adj N rs s₁.visited
    have hfold_cons : foldEmpty adj N (r :: rs) vis =
        ⟨s₂.visited, s₂.finished ++ s₁.finished⟩ :=
      foldEmpty_cons adj N r rs vis
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt iReg nVerts).Holds x := by
      change x.regs iReg < x.regs nVerts; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩, hy_r, hy_csr,
      by simpa [hfold_cons] using hy_vis,
      by rw [hfold_cons]; dsimp only; rw [List.length_append]; omega,
      fun q hq => ?_, fun a ha => ?_, fun reg hreg => ?_⟩
    · rw [hfold_cons]; dsimp only
      rw [List.length_cons, List.length_append, outDegreeSum_append]
      omega
    · have hrev : (foldEmpty adj N (r :: rs) vis).finished.reverse =
          s₁.finished.reverse ++ s₂.finished.reverse := by
        simp [hfold_cons]
      simp only [hrev, List.length_append, List.length_reverse] at hq
      by_cases hq1 : q < s₁.finished.length
      · have hpres : y.mem (kOrdAddr wb N Mc + F₀ + q) = y₁.mem (kOrdAddr wb N Mc + F₀ + q) :=
          hy_out (kOrdAddr wb N Mc + F₀ + q) (by
            dsimp only [kVisAddr, kOrdAddr, kStkAddr] at *; omega)
        rw [hpres, hy₁_ord q (by simpa using hq1)]
        congr 1
        simp only [hrev]
        rw [List.getElem_append_left (by simpa using hq1)]
      · set q' := q - s₁.finished.length
        have hq'_lt : q' < s₂.finished.reverse.length := by simp; omega
        have haddr : kOrdAddr wb N Mc + F₀ + q =
            kOrdAddr wb N Mc + (F₀ + s₁.finished.length) + q' := by omega
        rw [haddr, hy_ord q' hq'_lt]
        congr 1
        simp only [hrev]
        rw [List.getElem_append_right (by simp; omega)]
        simp [q']
    · rw [hfold_cons] at ha; dsimp only at ha; rw [List.length_append] at ha
      have h2 := hy_out a (by dsimp only [kVisAddr, kOrdAddr, kStkAddr] at *; omega)
      have h1 := hy₁_out a (by dsimp only [kVisAddr, kOrdAddr, kStkAddr] at *; omega)
      exact h2.trans h1
    · have h2 := hy_fr reg hreg
      have h1 := hy₁_fr reg (.inl (by omega))
      have hne_i : reg ≠ iReg := by reg_ne
      have hne_u : reg ≠ uReg := by reg_ne
      dsimp only [x₂] at h2
      rw [h2, Data.set_regs_of_ne hne_i, h1]
      dsimp only [st_u]
      exact Data.set_regs_of_ne hne_u _

theorem forwardDFSCode_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) {x : Data 28}
    (hregs : DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc) (kOrdAddr wb N Mc)
      (kStkAddr wb N Mc) x)
    (hNv : x.regs nVerts = N)
    (hcsr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem) :
    let ord := topologicalSort adj (List.finRange N)
    ∃ y, ExecWithin w forwardDFSCode x y (87 * N + 36 * Mc + 10) ∧
      ord.length = N ∧
      (∀ idx (hidx : idx < N),
        y.mem (kOrdAddr wb N Mc + (N - 1 - idx)) =
          (ord[idx]'(by rw [length_topologicalSort_finRange]; exact hidx)).val) ∧
      CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) y.mem ∧
      (∀ a, ¬ ((kVisAddr wb N Mc ≤ a ∧ a < kVisAddr wb N Mc + N) ∨
          (kOrdAddr wb N Mc ≤ a ∧ a < kOrdAddr wb N Mc + N) ∨
          (kStkAddr wb N Mc ≤ a ∧ a < kStkAddr wb N Mc + 3 * N)) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  have hfit_vis : Fits w (kVisAddr wb N Mc + N) :=
    hfit.of_le (by simp only [kVisAddr, kTopAddr]; omega)
  obtain ⟨x₁, hx₁_ex, hx₁_zero, hx₁_out, hx₁_fr⟩ :=
    zeroBlockCode_spec visB (by decide) (kVisAddr wb N Mc) N hfit_vis hregs.czero hregs.cone
      hregs.hvis hNv
  have hx₁_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₁.mem :=
    hcsr.of_eqOn
      (fun _ _ => hx₁_out _ (by dsimp only [kOffAddr, kVisAddr]; omega))
      (fun _ _ => hx₁_out _ (by dsimp only [kEdgeAddr, kVisAddr]; omega))
  have hx₁_vis : VisAt (∅ : Finset (Fin N)) (kVisAddr wb N Mc) x₁.mem := by
    intro w_v; simp [hx₁_zero w_v.val w_v.isLt]
  have hx₁_r := dfsRegs_of_frame hregs hx₁_fr
  let x₂ := (x₁.set finCnt 0).set iReg 0
  have hprep : ExecWithin (B := .standard) w (ram[ finCnt ← cZero; iReg ← cZero ]) x₁ x₂ 2 := by
    have hc0 := hx₁_r.czero
    wram_exec [hc0]
  obtain ⟨y, hy_ex, -, hy_csr, -, -, hy_ord, hy_out, hy_fr⟩ :=
    forwardDFSLoop_spec hN adj wb Mc hmc hfit (List.finRange N) 0 ∅ 0 x₂ (by simp)
      (fun q hq => by simp) rfl
      (dfsRegs_of_frame hx₁_r fun reg hreg => by
        dsimp only [x₂]; regs_lt)
      hx₁_csr hx₁_vis
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr nVerts (by decide)).trans hNv)
      (by dsimp only [x₂]; wram_simp)
      (by dsimp only [x₂]; wram_simp)
  set ord := topologicalSort adj (List.finRange N)
  have hfold_eq : (foldEmpty adj N (List.finRange N) ∅).finished = ord := by
    simp [foldEmpty, ord, topologicalSort, dfs]
  have hnd_ord : ord.Nodup := nodup_topologicalSort List.mem_finRange
  have hmem_ord : ∀ v : Fin N, v ∈ ord := mem_topologicalSort List.mem_finRange
  have huniv_ord : ord.toFinset = Finset.univ := by ext v; simp [hmem_ord v]
  have hlen_ord : ord.length = N := length_topologicalSort_finRange adj
  have hout_ord : outDegreeSum adj ord = csrOffset adj N := by
    rw [csrOffset_eq_outDegreeSum]
    unfold outDegreeSum
    rw [← List.sum_toFinset _ hnd_ord, ← List.sum_toFinset _ (List.nodup_finRange N), huniv_ord]
    have huniv2 : (List.finRange N).toFinset = Finset.univ := by ext v; simp
    rw [huniv2]
  rw [hfold_eq] at hy_ex hy_ord hy_out
  rw [hlen_ord, hout_ord] at hy_ex
  simp only [List.length_finRange, Nat.add_zero] at hy_ex hy_ord hy_out
  refine ⟨y, (hx₁_ex.seq (hprep.seq hy_ex)).mono (by omega), hlen_ord,
    fun idx hidx => ?_, hy_csr, fun a ha => ?_, fun r hr => ?_⟩
  · have hrev_idx : N - 1 - idx < ord.reverse.length := by simp [hlen_ord]; omega
    rw [hy_ord (N - 1 - idx) hrev_idx]
    congr 1
    rw [List.getElem_reverse]
    congr 1
    omega
  · rw [hlen_ord] at hy_out
    exact (hy_out a ha).trans (hx₁_out a (by omega))
  · have h2 := hy_fr r hr
    dsimp only [x₂] at h2
    have hne1 : r ≠ iReg := by reg_ne
    have hne2 : r ≠ finCnt := by reg_ne
    rw [h2, Data.set_regs_of_ne hne1, Data.set_regs_of_ne hne2]
    exact hx₁_fr r hr

end Cslib.Algorithms.WordRAM.DFS
