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
# Word-RAM Kosaraju SCC peeling and indexing (`O(N + M)`)

## Main definitions

* `Cslib.Algorithms.WordRAM.DFS.kosarajuIndexCode`: peels the transposed CSR graph in reverse
  finishing order.

## Main results

* `Cslib.Algorithms.WordRAM.DFS.kosarajuIndexCode_spec`: writes
  `indexComponents (sccs adj (List.finRange N))` in `102 * N + 36 * Mc + 9` instructions.
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

/-! ### Pass 3: Kosaraju SCC peeling and component indexing (`O(N + M)`) -/

/-- Write the current component index for one newly finished vertex. -/
private def writeCompBody : Code .standard 28 := ram[
  addr ← finB + pReg; vReg ← *addr;
  addr ← compB + vReg; *addr ← compIdxReg;
  pReg ← pReg + cOne ]

/-- Kosaraju peeling step: visit the next vertex in reverse finishing order in the transpose and
index the vertices finished as one component. -/
private def peelStepBody : Code .standard 28 :=
  (ram[ addr ← nVerts - cOne; addr ← addr - iReg; addr ← ordB + addr; uReg ← *addr;
        oldFinReg ← finCnt ]).seq
    (visitRootCode.seq
      ((Code.branch (.lt oldFinReg finCnt)
          ((ram[ pReg ← oldFinReg ]).seq
            ((Code.loop (.lt pReg finCnt) writeCompBody).seq
              (ram[ compIdxReg ← compIdxReg + cOne ])))
          (ram[ compIdxReg ← compIdxReg ])).seq
        (ram[ iReg ← iReg + cOne ])))

/-- Second Kosaraju pass: peel the transpose in reverse finishing order, writing component indices
at `compB`. -/
def kosarajuIndexCode : Code .standard 28 :=
  (zeroBlockCode visB).seq
    ((ram[ finCnt ← cZero; compIdxReg ← cZero; iReg ← cZero ]).seq
      (.loop (.lt iReg nVerts) peelStepBody))

private theorem writeCompLoop_spec {N w : ℕ} (finAddr compAddr : ℕ) (hdisj : finAddr + N ≤ compAddr)
    (F₀ L cIdx : ℕ) (hFL : F₀ + L ≤ N) (hfit : Fits w (compAddr + N + 2))
    (comp : List (Fin N)) (hnd : comp.Nodup) (hlen : comp.length = L) :
    ∀ (rem k : ℕ) (f : Fin N → ℕ) (x : Data 28)
      (_ : k + rem = L),
      (∀ q (hq : q < L), x.mem (finAddr + F₀ + q) = (comp[q]'(hlen ▸ hq)).val) →
      (∀ u : Fin N, x.mem (compAddr + u.val) =
        if u ∈ comp.take k then cIdx else f u) →
      x.regs cOne = 1 → x.regs finB = finAddr → x.regs compB = compAddr →
      x.regs compIdxReg = cIdx → x.regs finCnt = F₀ + L → x.regs pReg = F₀ + k →
      ∃ y, ExecWithin w (.loop (.lt pReg finCnt) writeCompBody) x y (7 * rem + 2) ∧
        (∀ u : Fin N, y.mem (compAddr + u.val) = if u ∈ comp then cIdx else f u) ∧
        (∀ a, ¬ (compAddr ≤ a ∧ a < compAddr + N) → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r ≠ addr → r ≠ vReg → r ≠ pReg → y.regs r = x.regs r)
  | 0, k, f, x, hk, _, hf_mem, _, _, _, _, hfc, hp => by
    have hk_eq : k = L := by omega
    subst hk_eq
    have hend : ¬ (Cond.lt pReg finCnt).Holds x := by
      change ¬ x.regs pReg < x.regs finCnt; omega
    refine ⟨x, ⟨2, by simp, Exec.loop_exit hend⟩, fun u => ?_, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    simpa [List.take_of_length_le (by omega : comp.length ≤ k)] using hf_mem u
  | rem + 1, k, f, x, hk, hfin_mem, hf_mem, hc1, hfb, hcb, hcIdx, hfc, hp => by
    have hk_lt : k < L := by omega
    set v := comp[k]'(by omega)
    have hm_v : x.mem (finAddr + (F₀ + k)) = v.val := by
      rw [← Nat.add_assoc]; exact hfin_mem k hk_lt
    have hf_fa : Fits w (finAddr + (F₀ + k)) := hfit.of_le (by omega)
    have hf_ca : Fits w (compAddr + v.val) := hfit.of_le (by have := v.isLt; omega)
    have hf_p1 : Fits w (F₀ + k + 1) := hfit.of_le (by omega)
    let StepPost (x₁ : Data 28) : Prop :=
      (∀ u : Fin N, x₁.mem (compAddr + u.val) =
          if u ∈ comp.take (k + 1) then cIdx else f u) ∧
        (∀ a, ¬ (compAddr ≤ a ∧ a < compAddr + N) → x₁.mem a = x.mem a) ∧
        x₁.regs pReg = F₀ + (k + 1) ∧
        (∀ r : Fin 28, r ≠ addr → r ≠ vReg → r ≠ pReg → x₁.regs r = x.regs r)
    have hstep : ∃ x₁, ExecWithin w writeCompBody x x₁ 5 ∧ StepPost x₁ := by
      unfold writeCompBody
      wram_exec [hc1, hfb, hcb, hcIdx, hp, hm_v, hf_fa, hf_ca, hf_p1]
      dsimp only [StepPost]
      refine ⟨fun u => ?_, fun a ha => ?_, by wram_simp; omega, fun r h1 h2 h3 => ?_⟩
      · mem_upd
        have htake : comp.take (k + 1) = comp.take k ++ [v] := by
          rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
          rfl
        rw [htake]
        by_cases huv : u = v
        · subst huv; simp
        · have hne : compAddr + u.val ≠ compAddr + v.val := fun h => huv (Fin.ext (by omega))
          rw [Function.update_of_ne hne, hf_mem u]
          simp [huv]
      · mem_upd
        exact Function.update_of_ne (by have := v.isLt; omega) _ _
      · regs_lt
    obtain ⟨x₁, hx₁_ex, hx₁_f, hx₁_out, hx₁_p, hx₁_fr⟩ := hstep
    have hfin_mem₁ : ∀ q (hq : q < L), x₁.mem (finAddr + F₀ + q) = (comp[q]'(hlen ▸ hq)).val :=
      fun q hq => (hx₁_out _ (by omega)).trans (hfin_mem q hq)
    obtain ⟨y, hy_ex, hy_f, hy_out, hy_fr⟩ :=
      writeCompLoop_spec finAddr compAddr hdisj F₀ L cIdx hFL hfit comp hnd hlen rem (k + 1) f x₁
        (by omega) hfin_mem₁ hx₁_f
        ((hx₁_fr cOne (by decide) (by decide) (by decide)).trans hc1)
        ((hx₁_fr finB (by decide) (by decide) (by decide)).trans hfb)
        ((hx₁_fr compB (by decide) (by decide) (by decide)).trans hcb)
        ((hx₁_fr compIdxReg (by decide) (by decide) (by decide)).trans hcIdx)
        ((hx₁_fr finCnt (by decide) (by decide) (by decide)).trans hfc)
        hx₁_p
    obtain ⟨t₁, ht₁, he₁⟩ := hx₁_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt pReg finCnt).Holds x := by
      change x.regs pReg < x.regs finCnt; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, by omega, Exec.loop_iter hlt he₁ he₂⟩,
      hy_f, fun a ha => (hy_out a ha).trans (hx₁_out a ha),
      fun r h1 h2 h3 => (hy_fr r h1 h2 h3).trans (hx₁_fr r h1 h2 h3)⟩

private theorem peelLoop_spec {N w : ℕ} (hN : 0 < N) (revAdj : Fin N → List (Fin N))
    (ord : List (Fin N)) (hord_len : ord.length = N)
    (wb Mc : ℕ) (hmc : csrOffset revAdj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) :
    ∀ (rs : List (Fin N)) (idx F₀ cIdx : ℕ) (vis : Finset (Fin N)) (f : Fin N → ℕ) (x : Data 28)
      (_ : idx + rs.length = N),
      (∀ q (hq : q < rs.length), rs[q] = ord[idx + q]'(by omega)) →
      F₀ = vis.card →
      cIdx ≤ F₀ →
      DfsRegs (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) (kVisAddr wb N Mc) (kFinAddr wb N Mc)
        (kStkAddr wb N Mc) x →
      x.regs nVerts = N → x.regs ordB = kOrdAddr wb N Mc → x.regs compB = kCompAddr wb N Mc →
      x.regs iReg = idx → x.regs finCnt = F₀ → x.regs compIdxReg = cIdx →
      CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) x.mem →
      (∀ q (hq : q < N), x.mem (kOrdAddr wb N Mc + (N - 1 - q)) = (ord[q]'(by omega)).val) →
      VisAt vis (kVisAddr wb N Mc) x.mem →
      (∀ u : Fin N, u ∈ vis → x.mem (kCompAddr wb N Mc + u.val) = f u) →
      ∃ y,
        let comps := peelSCCs revAdj N vis rs
        ExecWithin w (.loop (.lt iReg nVerts) peelStepBody) x y
          (30 * rs.length + 68 * comps.flatten.length +
            36 * outDegreeSum revAdj comps.flatten + 2) ∧
        (∀ u : Fin N, u ∈ vis ∨ u ∈ comps.flatten →
          y.mem (kCompAddr wb N Mc + u.val) = indexComponentsAux cIdx comps f u) ∧
        (∀ a, a < kVisAddr wb N Mc → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], idx, F₀, cIdx, vis, f, x, hidx, _, _, _, _, _, _, _, _, _, _, _, _, _, hf_vis => by
    simp only [List.length_nil, Nat.add_zero] at hidx
    have hend : ¬ (Cond.lt iReg nVerts).Holds x := by
      change ¬ x.regs iReg < x.regs nVerts; omega
    refine ⟨x, ⟨2, by simp [peelSCCs, outDegreeSum], Exec.loop_exit hend⟩,
      fun u hu => ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    simp only [peelSCCs, List.flatten_nil, List.not_mem_nil, or_false] at hu
    simpa [peelSCCs, indexComponentsAux] using hf_vis u hu
  | r :: rs, idx, F₀, cIdx, vis, f, x, hidx, hrs, hF₀, hcIdx_le, hregs, hNv, hordB, hcompB,
      hi, hfc, hcIdx, hcsr, hord_mem, hvis, hf_vis => by
    simp only [List.length_cons] at hidx
    have hr_eq : r = ord[idx]'(by omega) := by
      have h0 := hrs 0 (by simp)
      simpa only [Nat.add_zero, List.getElem_cons_zero] using h0
    have hm_ord : x.mem (kOrdAddr wb N Mc + (N - 1 - idx)) = r.val := by
      rw [hr_eq]; exact hord_mem idx (by omega)
    have hcard_le : vis.card ≤ N := by have := Finset.card_le_univ vis; simpa using this
    have hcons : F₀ + (N - vis.card) ≤ N := by omega
    have hf_n1 : Fits w (N - 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    have hf_sub : Fits w (N - 1 - idx) := hfit.of_le (by simp only [kTopAddr]; omega)
    have hf_oa : Fits w (kOrdAddr wb N Mc + (N - 1 - idx)) :=
      hfit.of_le (by simp only [kOrdAddr, kTopAddr]; omega)
    have hfit_stk : Fits w (kStkAddr wb N Mc + 3 * N + Mc + 4) :=
      hfit.of_le (by simp only [kStkAddr, kTopAddr]; omega)
    let x₁ := ((((x.set addr (N - 1)).set addr (N - 1 - idx)).set
      addr (kOrdAddr wb N Mc + (N - 1 - idx))).set uReg r.val).set oldFinReg F₀
    have hp1 : ExecWithin w
        (ram[ addr ← nVerts - cOne; addr ← addr - iReg; addr ← ordB + addr; uReg ← *addr;
              oldFinReg ← finCnt ]) x x₁ 5 := by
      have hc1 := hregs.cone
      have htriv : x₁ = ((((x.set addr (N - 1)).set addr (N - 1 - idx)).set
        addr (kOrdAddr wb N Mc + (N - 1 - idx))).set uReg r.val).set oldFinReg F₀ := rfl
      wram_exec [hNv, hc1, hi, hordB, hm_ord, hfc, hf_n1, hf_oa]
    obtain ⟨y₁, hy₁_ex, hy₁_r, hy₁_csr, hy₁_vis, hy₁_fc, hy₁_fin_mem, hy₁_out, hy₁_fr⟩ :=
      visitRootCode_spec hN revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc)
        (kVisAddr wb N Mc) (kFinAddr wb N Mc) (kStkAddr wb N Mc) Mc
        (by simp only [kRevOffAddr, kVisAddr]; omega)
        (by simp only [kRevEdgeAddr, kVisAddr]; omega)
        (by simp only [kVisAddr, kFinAddr]; omega)
        (by simp only [kFinAddr, kStkAddr]; omega)
        hmc hfit_stk r F₀ vis hcons (x := x₁)
        (dfsRegs_of_frame hregs fun reg hreg => by
          dsimp only [x₁]; regs_lt)
        hcsr hvis (by dsimp only [x₁]; wram_simp) (by dsimp only [x₁]; wram_simp; exact hfc)
    set s := visit revAdj N r ⟨vis, []⟩
    obtain ⟨hnd_s, hdis_s, hvis_s⟩ := visit_nil_struct revAdj N r vis
    have hcard_s : s.visited.card = vis.card + s.finished.length := card_visit_nil revAdj N r vis
    have hy₁_of : y₁.regs oldFinReg = F₀ :=
      (hy₁_fr oldFinReg (.inr (.inr rfl))).trans (by dsimp only [x₁]; wram_simp)
    have hy₁_cIdx : y₁.regs compIdxReg = cIdx :=
      (hy₁_fr compIdxReg (.inr (.inl rfl))).trans (by dsimp only [x₁]; wram_simp; exact hcIdx)
    have hy₁_i : y₁.regs iReg = idx :=
      (hy₁_fr iReg (.inl (by decide))).trans (by dsimp only [x₁]; wram_simp; exact hi)
    have hy₁_fr0 : ∀ reg : Fin 28, reg.val < 18 → y₁.regs reg = x.regs reg := fun reg hreg => by
      rw [hy₁_fr reg (.inl (by omega))]
      dsimp only [x₁]; regs_lt
    let f' : Fin N → ℕ :=
      if s.finished.isEmpty then f
      else s.finished.foldl (fun g v => Function.update g v cIdx) f
    let cIdx' : ℕ := if s.finished.isEmpty then cIdx else cIdx + 1
    have hf_i1 : Fits w (idx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    have hbranch : ∃ y₂,
        ExecWithin w
          ((Code.branch (.lt oldFinReg finCnt)
              ((ram[ pReg ← oldFinReg ]).seq
                ((Code.loop (.lt pReg finCnt) writeCompBody).seq
                  (ram[ compIdxReg ← compIdxReg + cOne ])))
              (ram[ compIdxReg ← compIdxReg ])).seq
            (ram[ iReg ← iReg + cOne ]))
          y₁ y₂ (7 * s.finished.length + 7) ∧
        y₂.regs iReg = idx + 1 ∧ y₂.regs finCnt = F₀ + s.finished.length ∧
        y₂.regs compIdxReg = cIdx' ∧
        (∀ u : Fin N, u ∈ s.visited → y₂.mem (kCompAddr wb N Mc + u.val) = f' u) ∧
        (∀ a, ¬ (kCompAddr wb N Mc ≤ a ∧ a < kCompAddr wb N Mc + N) → y₂.mem a = y₁.mem a) ∧
        (∀ reg : Fin 28, reg.val < 18 → y₂.regs reg = y₁.regs reg) := by
      have hFL : F₀ + s.finished.length ≤ N := by
        have := Finset.card_le_univ s.visited
        simp only [Fintype.card_fin] at this
        omega
      by_cases hempty : s.finished.isEmpty
      · have hlen0 : s.finished = [] := List.isEmpty_iff.1 hempty
        have hnlt : ¬ (Cond.lt oldFinReg finCnt).Holds y₁ := by
          change ¬ y₁.regs oldFinReg < y₁.regs finCnt
          simp [hy₁_of, hy₁_fc, hlen0]
        let y₂ := (y₁.set compIdxReg cIdx).set iReg (idx + 1)
        have hb : ExecWithin w
            (.branch (.lt oldFinReg finCnt)
              ((ram[ pReg ← oldFinReg ]).seq
                ((Code.loop (.lt pReg finCnt) writeCompBody).seq
                  (ram[ compIdxReg ← compIdxReg + cOne ])))
              (ram[ compIdxReg ← compIdxReg ]))
            y₁ (y₁.set compIdxReg cIdx) 3 := by
          have hnop : Exec (B := .standard) w (ram[ compIdxReg ← compIdxReg ])
              y₁ (y₁.set compIdxReg cIdx) 1 := by
            simpa [hy₁_cIdx] using
              Exec.op (B := .standard) (o := .copy compIdxReg compIdxReg) (x := y₁) (w := w) rfl
          exact ⟨3, le_rfl, Exec.branch_neg hnlt hnop⟩
        have hinc : ExecWithin w (ram[ iReg ← iReg + cOne ]) (y₁.set compIdxReg cIdx) y₂ 1 := by
          have hc1' := hy₁_r.cone
          wram_exec [hy₁_i, hc1', hf_i1]
        refine ⟨y₂, (hb.seq hinc).mono (by omega),
          by dsimp only [y₂]; wram_simp,
          by dsimp only [y₂]; wram_simp; exact hy₁_fc,
          by dsimp only [y₂, cIdx']; wram_simp; simp [hempty],
          fun u hu => ?_, fun _ _ => rfl, fun reg hreg => ?_⟩
        · dsimp only [y₂, f']; mem_upd
          simp only [hempty, ↓reduceIte]
          have huv : u ∈ vis := by simpa [s, hlen0] using (hvis_s u).1 hu
          rw [hy₁_out (kCompAddr wb N Mc + u.val) (by
            have := u.isLt
            dsimp only [s, kVisAddr, kFinAddr, kStkAddr, kCompAddr] at hFL ⊢
            omega)]
          exact hf_vis u huv
        · dsimp only [y₂]; regs_lt
      · have hpos : 0 < s.finished.length := List.length_pos_iff.2 (mt List.isEmpty_iff.2 hempty)
        have hlt_br : (Cond.lt oldFinReg finCnt).Holds y₁ := by
          change y₁.regs oldFinReg < y₁.regs finCnt
          omega
        let z₀ := y₁.set pReg F₀
        have hp_z₀ : ExecWithin (B := .standard) w (ram[ pReg ← oldFinReg ]) y₁ z₀ 1 := by
          wram_exec [hy₁_of]
        have hf_comp : Fits w (kCompAddr wb N Mc + N + 2) :=
          hfit.of_le (by simp only [kCompAddr, kTopAddr]; omega)
        obtain ⟨z₁, hz₁_ex, hz₁_mem, hz₁_out, hz₁_fr⟩ :=
          writeCompLoop_spec (kFinAddr wb N Mc) (kCompAddr wb N Mc)
            (by simp only [kFinAddr, kCompAddr]; omega) F₀ s.finished.length cIdx hFL hf_comp
            s.finished.reverse (List.nodup_reverse.2 hnd_s) (by simp) s.finished.length 0
            (fun u => y₁.mem (kCompAddr wb N Mc + u.val)) z₀ (by simp)
            (fun q hq => by dsimp only [z₀]; exact hy₁_fin_mem q (by simpa using hq))
            (fun u => by dsimp only [z₀]; simp)
            (by dsimp only [z₀]; wram_simp; exact hy₁_r.cone)
            (by dsimp only [z₀]; wram_simp; exact hy₁_r.hfin)
            (by dsimp only [z₀]; wram_simp; exact (hy₁_fr0 compB (by decide)).trans hcompB)
            (by dsimp only [z₀]; wram_simp; exact hy₁_cIdx)
            (by dsimp only [z₀]; wram_simp; exact hy₁_fc)
            (by dsimp only [z₀]; wram_simp)
        have hz₁_cIdx : z₁.regs compIdxReg = cIdx :=
          (hz₁_fr compIdxReg (by decide) (by decide) (by decide)).trans
            (by dsimp only [z₀]; wram_simp; exact hy₁_cIdx)
        have hz₁_1 : z₁.regs cOne = 1 :=
          (hz₁_fr cOne (by decide) (by decide) (by decide)).trans
            (by dsimp only [z₀]; wram_simp; exact hy₁_r.cone)
        have hz₁_i : z₁.regs iReg = idx :=
          (hz₁_fr iReg (by decide) (by decide) (by decide)).trans
            (by dsimp only [z₀]; wram_simp; exact hy₁_i)
        have hf_c1 : Fits w (cIdx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
        let y₂ := (z₁.set compIdxReg (cIdx + 1)).set iReg (idx + 1)
        have hp_tail : ExecWithin w
            ((ram[ compIdxReg ← compIdxReg + cOne ]).seq (ram[ iReg ← iReg + cOne ]))
            z₁ y₂ 2 := by
          have htriv : y₂ = (z₁.set compIdxReg (cIdx + 1)).set iReg (idx + 1) := rfl
          wram_exec [hz₁_cIdx, hz₁_1, hz₁_i, hf_c1, hf_i1]
        obtain ⟨tb, htb, heb⟩ := hp_z₀.seq (hz₁_ex.seq
          (show ExecWithin w (ram[ compIdxReg ← compIdxReg + cOne ]) z₁
              (z₁.set compIdxReg (cIdx + 1)) 1 by wram_exec [hz₁_cIdx, hz₁_1, hf_c1]))
        have hbr_ex : ExecWithin w
            (.branch (.lt oldFinReg finCnt)
              ((ram[ pReg ← oldFinReg ]).seq
                ((Code.loop (.lt pReg finCnt) writeCompBody).seq
                  (ram[ compIdxReg ← compIdxReg + cOne ])))
              (ram[ compIdxReg ← compIdxReg ]))
            y₁ (z₁.set compIdxReg (cIdx + 1)) (7 * s.finished.length + 5) :=
          ⟨tb + 1, by omega, Exec.branch_pos hlt_br heb⟩
        have hinc_i : ExecWithin w (ram[ iReg ← iReg + cOne ])
            (z₁.set compIdxReg (cIdx + 1)) y₂ 1 := by
          wram_exec [hz₁_i, hz₁_1, hf_i1]
        refine ⟨y₂, (hbr_ex.seq hinc_i).mono (by omega),
          by dsimp only [y₂]; wram_simp,
          by
            dsimp only [y₂]; wram_simp
            exact (hz₁_fr finCnt (by decide) (by decide) (by decide)).trans
              (by dsimp only [z₀]; wram_simp; exact hy₁_fc),
          by dsimp only [y₂, cIdx']; wram_simp; simp [hempty],
          fun u hu => ?_, fun a ha => hz₁_out a ha, fun reg hreg => ?_⟩
        · dsimp only [y₂, f']; mem_upd
          simp only [hempty, Bool.false_eq_true, ↓reduceIte, hz₁_mem u, List.mem_reverse,
            foldl_update_const]
          by_cases huf : u ∈ s.finished
          · simp [huf]
          · simp only [huf, ↓reduceIte]
            have huv : u ∈ vis := ((hvis_s u).1 hu).resolve_right huf
            rw [hy₁_out (kCompAddr wb N Mc + u.val) (by
              have := u.isLt; dsimp only [kVisAddr, kFinAddr, kStkAddr, kCompAddr]; omega)]
            exact hf_vis u huv
        · dsimp only [y₂]; regs_lt
          rw [hz₁_fr reg (by reg_ne) (by reg_ne) (by reg_ne)]; dsimp only [z₀]; regs_lt
    obtain ⟨y₂, hy₂_ex, hy₂_i, hy₂_fc, hy₂_cIdx, hy₂_comp, hy₂_out, hy₂_fr⟩ := hbranch
    have hy₂_fr0 : ∀ reg : Fin 28, reg.val < 18 → y₂.regs reg = x.regs reg :=
      fun reg hreg => (hy₂_fr reg hreg).trans (hy₁_fr0 reg hreg)
    have hy₂_csr : CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) y₂.mem :=
      hy₁_csr.of_eqOn
        (fun _ _ => hy₂_out _ (by dsimp only [kRevOffAddr, kCompAddr]; omega))
        (fun _ _ => hy₂_out _ (by dsimp only [kRevEdgeAddr, kCompAddr]; omega))
    have hy₂_ord : ∀ q (hq : q < N), y₂.mem (kOrdAddr wb N Mc + (N - 1 - q)) =
        (ord[q]'(by omega)).val := fun q hq => by
      rw [hy₂_out _ (by simp only [kOrdAddr, kCompAddr]; omega),
        hy₁_out _ (by simp only [kVisAddr, kOrdAddr, kFinAddr, kStkAddr]; omega)]
      exact hord_mem q hq
    have hy₂_vis : VisAt s.visited (kVisAddr wb N Mc) y₂.mem := fun z => by
      rw [hy₂_out _ (by have := z.isLt; simp only [kVisAddr, kCompAddr]; omega)]
      exact hy₁_vis z
    have hcIdx'_le : cIdx' ≤ F₀ + s.finished.length := by
      dsimp only [cIdx']
      split_ifs with he
      · omega
      · have := List.length_pos_iff.2 (mt List.isEmpty_iff.2 he); omega
    obtain ⟨y, hy_ex, hy_comp, hy_out, hy_fr⟩ :=
      peelLoop_spec hN revAdj ord hord_len wb Mc hmc hfit rs (idx + 1)
        (F₀ + s.finished.length) cIdx' s.visited f' y₂ (by omega)
        (fun q hq => by
          have h := hrs (q + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using h)
        (by omega) hcIdx'_le
        (dfsRegs_of_frame hy₁_r hy₂_fr)
        ((hy₂_fr0 nVerts (by decide)).trans hNv)
        ((hy₂_fr0 ordB (by decide)).trans hordB)
        ((hy₂_fr0 compB (by decide)).trans hcompB)
        hy₂_i hy₂_fc hy₂_cIdx hy₂_csr hy₂_ord hy₂_vis hy₂_comp
    have hbody_ex : ExecWithin w peelStepBody x y₂
        (28 + 67 * s.finished.length + 36 * outDegreeSum revAdj s.finished) :=
      (hp1.seq (hy₁_ex.seq hy₂_ex)).mono (by omega)
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt iReg nVerts).Holds x := by
      change x.regs iReg < x.regs nVerts; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩,
      fun u hu => ?_, fun a ha => ?_, fun reg hreg => (hy_fr reg hreg).trans (hy₂_fr0 reg hreg)⟩
    · rw [peelSCCs, show visit revAdj N r ⟨vis, []⟩ = s from rfl]
      split_ifs with he
      · have hlen0 : s.finished = [] := List.isEmpty_iff.1 he
        simp only [hlen0, List.length_nil, outDegreeSum, List.map_nil, List.sum_nil] at ht₁
        simp only [List.length_cons]
        omega
      · simp only [List.length_cons, List.flatten_cons, List.length_append,
          outDegreeSum_append]
        omega
    · rw [peelSCCs, show visit revAdj N r ⟨vis, []⟩ = s from rfl] at hu ⊢
      split_ifs with he
      · simp only [he, ↓reduceIte] at hu
        dsimp only [cIdx', f'] at hy_comp
        simp only [he, ↓reduceIte] at hy_comp
        exact hy_comp u (hu.imp (fun h => (hvis_s u).2 (.inl h)) id)
      · simp only [he, Bool.false_eq_true, ↓reduceIte] at hu
        dsimp only [cIdx', f', indexComponentsAux] at hy_comp ⊢
        simp only [he, Bool.false_eq_true, ↓reduceIte] at hy_comp
        refine hy_comp u ?_
        rcases hu with huv | hflat
        · exact .inl ((hvis_s u).2 (.inl huv))
        · rcases List.mem_append.1 (by rwa [List.flatten_cons] at hflat) with huf | hrest
          · exact .inl ((hvis_s u).2 (.inr huf))
          · exact .inr hrest
    · rw [hy_out a ha, hy₂_out a (by dsimp only [kVisAddr, kCompAddr] at *; omega),
        hy₁_out a (by dsimp only [kVisAddr, kFinAddr, kStkAddr] at *; omega)]
      dsimp only [x₁]; mem_upd

theorem kosarajuIndexCode_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) {x : Data 28}
    (hregs : DfsRegs (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) (kVisAddr wb N Mc)
      (kFinAddr wb N Mc) (kStkAddr wb N Mc) x)
    (hNv : x.regs nVerts = N) (hordB : x.regs ordB = kOrdAddr wb N Mc)
    (hcompB : x.regs compB = kCompAddr wb N Mc)
    (hcsr : CSRAt (transposeAdj adj (List.finRange N))
      (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) x.mem)
    (hord_len : (topologicalSort adj (List.finRange N)).length = N)
    (hord_mem : ∀ idx (hidx : idx < N),
      x.mem (kOrdAddr wb N Mc + (N - 1 - idx)) =
        ((topologicalSort adj (List.finRange N))[idx]'(by
          rw [length_topologicalSort_finRange]; exact hidx)).val) :
    ∃ y, ExecWithin w kosarajuIndexCode x y (102 * N + 36 * Mc + 9) ∧
      (∀ u : Fin N, y.mem (kCompAddr wb N Mc + u.val) =
        indexComponents (sccs adj (List.finRange N)) u) ∧
      (∀ a, a < kVisAddr wb N Mc → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  set revAdj := transposeAdj adj (List.finRange N)
  set ord := topologicalSort adj (List.finRange N)
  have hmc_rev : csrOffset revAdj N ≤ Mc := by
    dsimp only [revAdj]; rwa [csrOffset_transposeAdj_eq]
  have hfit_vis : Fits w (kVisAddr wb N Mc + N) :=
    hfit.of_le (by simp only [kVisAddr, kTopAddr]; omega)
  obtain ⟨x₁, hx₁_ex, hx₁_zero, hx₁_out, hx₁_fr⟩ :=
    zeroBlockCode_spec visB (by decide) (kVisAddr wb N Mc) N hfit_vis
      hregs.czero hregs.cone hregs.hvis hNv
  have hx₁_csr : CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) x₁.mem :=
    hcsr.of_eqOn
      (fun _ _ => hx₁_out _ (by dsimp only [kRevOffAddr, kVisAddr]; omega))
      (fun _ _ => hx₁_out _ (by dsimp only [kRevEdgeAddr, kVisAddr]; omega))
  have hx₁_ord : ∀ idx (hidx : idx < N),
      x₁.mem (kOrdAddr wb N Mc + (N - 1 - idx)) =
        (ord[idx]'(by rw [hord_len]; exact hidx)).val :=
    fun idx hidx =>
      (hx₁_out _ (by dsimp only [kVisAddr, kOrdAddr]; omega)).trans (hord_mem idx hidx)
  have hx₁_vis : VisAt (∅ : Finset (Fin N)) (kVisAddr wb N Mc) x₁.mem := fun u => by
    simp [hx₁_zero u.val u.isLt]
  let x₂ := ((x₁.set finCnt 0).set compIdxReg 0).set iReg 0
  have hp : ExecWithin (B := .standard) w
      (ram[ finCnt ← cZero; compIdxReg ← cZero; iReg ← cZero ]) x₁ x₂ 3 := by
    have hc0 : x₁.regs cZero = 0 := (hx₁_fr cZero (by decide)).trans hregs.czero
    wram_exec [hc0]
  have hx₂_fr0 : ∀ r : Fin 28, r.val < 18 → x₂.regs r = x.regs r := fun r hr => by
    have h1 : r ≠ iReg := by reg_ne
    have h2 : r ≠ compIdxReg := by reg_ne
    have h3 : r ≠ finCnt := by reg_ne
    dsimp only [x₂]
    rw [Data.set_regs_of_ne h1, Data.set_regs_of_ne h2, Data.set_regs_of_ne h3]
    exact hx₁_fr r hr
  obtain ⟨y, hy_ex, hy_comp, hy_out, hy_fr⟩ :=
    peelLoop_spec hN revAdj ord hord_len wb Mc hmc_rev hfit ord 0 0 0 ∅ (fun _ => 0) x₂
      (by omega) (fun q _ => by simp) rfl (le_refl 0)
      (dfsRegs_of_frame hregs hx₂_fr0)
      ((hx₂_fr0 nVerts (by decide)).trans hNv)
      ((hx₂_fr0 ordB (by decide)).trans hordB)
      ((hx₂_fr0 compB (by decide)).trans hcompB)
      (by dsimp only [x₂]; wram_simp)
      (by dsimp only [x₂]; wram_simp)
      (by dsimp only [x₂]; wram_simp)
      hx₁_csr hx₁_ord hx₁_vis (fun _ hu => by simp at hu)
  have hsccs_eq : peelSCCs revAdj N ∅ ord = sccs adj (List.finRange N) := by
    simp [sccs, revAdj, ord]
  have hcond : IsSCCCondensation adj (sccs adj (List.finRange N)) :=
    isSCCCondensation_sccs List.mem_finRange
  have hflat_len : (sccs adj (List.finRange N)).flatten.length = N := by
    simpa using hcond.length_flatten_eq_card
  have hout_flat : outDegreeSum revAdj (sccs adj (List.finRange N)).flatten = csrOffset adj N := by
    rw [outDegreeSum, ← List.sum_toFinset _ hcond.nodup_flatten]
    have huniv : (sccs adj (List.finRange N)).flatten.toFinset = Finset.univ := by
      ext v; simp [hcond.mem_flatten v]
    rw [huniv, sum_length_transposeAdj, ← csrOffset_eq_outDegreeSum]
  rw [hsccs_eq, hord_len, hflat_len, hout_flat] at hy_ex
  refine ⟨y, (hx₁_ex.seq (hp.seq hy_ex)).mono (by omega), fun u => ?_, fun a ha => ?_,
    fun r hr => (hy_fr r hr).trans (hx₂_fr0 r hr)⟩
  · rw [hsccs_eq] at hy_comp
    exact hy_comp u (.inr (hcond.mem_flatten u))
  · exact (hy_out a ha).trans (hx₁_out a (by omega))


end Cslib.Algorithms.WordRAM.DFS
