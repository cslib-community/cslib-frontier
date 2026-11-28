/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TwoSAT.EquivDFS
public import CslibFrontier.Algorithms.WordRAM.TwoSAT.Layout

/-!
# Witness extraction and scratch-register setup (`extractAssignmentCode`, `setupWorkRegsCode`)

Internal Pass 4 subroutines comparing literal SCC indices and writing `answerWords G`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TwoSAT

open Cslib.Logic.PL Cslib.WordRAM
open Cslib.Algorithms.Lean.TwoSAT
open Cslib.Algorithms.WordRAM.ClauseCode
open Reg Cslib.Algorithms.WordRAM.DFS Cslib.Algorithms.WordRAM.DFS.Reg

/-- Loop body checking `comp[2i] ≠ comp[2i + 1]` and writing variable `i`'s bit. -/
@[expose] def extractVarBody : Code .standard 28 := ram[
  uReg ← cTwo * iReg;
  addr ← compB + uReg; jReg ← *addr;
  addr ← addr + cOne; jEndReg ← *addr;
  if jReg = jEndReg then [ compIdxReg ← cZero ]
  else [
    if jReg < jEndReg then [ vReg ← cOne ] else [ vReg ← cZero ];
    addr ← outBase + cTwo; addr ← addr + iReg; *addr ← vReg ];
  iReg ← iReg + cOne ]

/-- Extract the satisfying assignment from `compB` or write `0` on conflict. -/
@[expose] def extractAssignmentCode : Code .standard 28 :=
  (ram[ compIdxReg ← cOne; iReg ← cZero ]).seq
    ((Code.loop (.lt iReg nv) extractVarBody).seq
      (.branch (.eq compIdxReg cOne)
        (ram[ addr ← nv + cOne; *outBase ← addr; addr ← outBase + cOne; *addr ← cOne ])
        (ram[ *outBase ← cZero ])))

theorem extractVarLoop_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound)
    (compIdx : Literal (Fin G.n) → ℕ) :
    ∀ (vs : List (Fin G.n)) (idx : ℕ) (ok : Bool) (x : Data 28)
      (_ : idx + vs.length = G.n),
      (∀ q (hq : q < vs.length), vs[q].val = idx + q) →
      (∀ u : Fin (2 * G.n),
        x.mem (kCompAddr G.workBase (2 * G.n) (2 * G.φ.length) + u.val) =
          compIdx ((litEquiv G.n).symm u)) →
      (∀ q : Fin G.n, q.val < idx → compIdx (q, true) ≠ compIdx (q, false) →
        x.mem (G.outAddrBase + 2 + q.val) =
          (decide (compIdx (q, false) < compIdx (q, true))).toNat) →
      x.regs cZero = 0 → x.regs cOne = 1 → x.regs cTwo = 2 → x.regs nv = G.n →
      x.regs outBase = G.outAddrBase →
      x.regs compB = kCompAddr G.workBase (2 * G.n) (2 * G.φ.length) →
      x.regs iReg = idx → x.regs compIdxReg = ok.toNat →
      ∃ y, ExecWithin w (.loop (.lt iReg nv) extractVarBody) x y (16 * vs.length + 2) ∧
        y.regs outBase = G.outAddrBase ∧ y.regs nv = G.n ∧
        y.regs cZero = 0 ∧ y.regs cOne = 1 ∧
        y.regs compIdxReg =
          (vs.foldl (fun acc v => acc && decide (compIdx (v, true) ≠ compIdx (v, false)))
            ok).toNat ∧
        (∀ v : Fin G.n, compIdx (v, true) ≠ compIdx (v, false) →
          y.mem (G.outAddrBase + 2 + v.val) =
            (decide (compIdx (v, false) < compIdx (v, true))).toNat)
  | [], idx, ok, x, hidx, _, _, hout_prev, hc0, hc1, _, hnv, hob, _, hi, hok => by
    simp only [List.length_nil, Nat.add_zero] at hidx
    have hend : ¬ (Cond.lt iReg nv).Holds x := by
      change ¬ x.regs iReg < x.regs nv; omega
    refine ⟨x, ⟨2, by simp, Exec.loop_exit hend⟩, hob, hnv, hc0, hc1, hok, fun v hne => ?_⟩
    exact hout_prev v (by have := v.isLt; omega) hne
  | v :: vs, idx, ok, x, hidx, hvs, hcomp, hout_prev, hc0, hc1, hc2, hnv, hob, hcb, hi, hok => by
    simp only [List.length_cons] at hidx
    have hv_val : v.val = idx := by simpa using hvs 0 (Nat.zero_lt_succ _)
    set compBase := kCompAddr G.workBase (2 * G.n) (2 * G.φ.length)
    have hm (b : Bool) : x.mem (compBase + 2 * idx + b.toNat) = compIdx (v, b) := by
      have hu := hcomp (litEquiv G.n (v, b))
      rw [Equiv.symm_apply_apply] at hu
      cases b <;> simpa [litEquiv, litCodeBy, hv_val, Nat.add_assoc] using hu
    have hm_f : x.mem (compBase + 2 * idx) = compIdx (v, false) := hm false
    have hm_t : x.mem (compBase + 2 * idx + 1) = compIdx (v, true) := hm true
    have hf_ct : Fits w (compBase + 2 * idx + 1) :=
      G.fits_of_le hfit (by
        simp only [compBase, kCompAddr, Instance.workBase, Instance.outAddrBase,
          G.encode_length, Instance.wordBound]; omega)
    have hf_ob2i : Fits w (G.outAddrBase + 2 + idx) :=
      G.fits_of_le hfit (by
        simp only [Instance.outAddrBase, G.encode_length, Instance.wordBound]; omega)
    obtain ⟨x₁, hx₁_ex, hx₁_comp, hx₁_prev, hx₁_0, hx₁_1, hx₁_2, hx₁_nv, hx₁_ob, hx₁_cb,
      hx₁_i, hx₁_ok⟩ : ∃ x₁, ExecWithin w extractVarBody x x₁ 14 ∧
        (∀ u : Fin (2 * G.n), x₁.mem (compBase + u.val) = compIdx ((litEquiv G.n).symm u)) ∧
          (∀ q : Fin G.n, q.val < idx + 1 → compIdx (q, true) ≠ compIdx (q, false) →
            x₁.mem (G.outAddrBase + 2 + q.val) =
              (decide (compIdx (q, false) < compIdx (q, true))).toNat) ∧
          x₁.regs cZero = 0 ∧ x₁.regs cOne = 1 ∧ x₁.regs cTwo = 2 ∧ x₁.regs nv = G.n ∧
          x₁.regs outBase = G.outAddrBase ∧ x₁.regs compB = compBase ∧
          x₁.regs iReg = idx + 1 ∧
          x₁.regs compIdxReg = (ok && decide (compIdx (v, true) ≠ compIdx (v, false))).toNat := by
      wram_exec [extractVarBody, hc0, hc1, hc2, hnv, hob, hcb, hi, hok, hm_f, hm_t, hf_ct, hf_ob2i]
      · -- equal components: compIdx (v, false) = compIdx (v, true)
        refine ⟨hcomp, fun q hq hne_q => ?_, by wram_simp [hc0], by wram_simp [hc1],
          by wram_simp [hc2], by wram_simp [hnv], by wram_simp [hob], by wram_simp [hcb],
          by wram_simp, ?_⟩
        · by_cases hqi : q = v
          · subst hqi
            exact absurd ‹compIdx (q, false) = compIdx (q, true)›.symm hne_q
          · have hqv : q.val ≠ idx := fun h => hqi (Fin.ext (h.trans hv_val.symm))
            exact hout_prev q (by omega) hne_q
        · wram_simp
          simp [‹compIdx (v, false) = compIdx (v, true)›]
      all_goals
        -- unequal components: the bit is written
        refine ⟨fun u => ?_, fun q hq hne_q => ?_, by wram_simp [hc0], by wram_simp [hc1],
          by wram_simp [hc2], by wram_simp [hnv], by wram_simp [hob], by wram_simp [hcb],
          by wram_simp, ?_⟩
        · mem_upd
          rw [Function.update_of_ne (by
            simp only [compBase, kCompAddr, Instance.workBase]; omega)]
          exact hcomp u
        · mem_upd
          by_cases hqi : q = v
          · subst hqi
            rw [hv_val, Function.update_self]
            by_cases h : compIdx (q, false) < compIdx (q, true) <;> simp [h]; omega
          · have hqv : q.val ≠ idx := fun h => hqi (Fin.ext (h.trans hv_val.symm))
            rw [Function.update_of_ne (by omega)]
            exact hout_prev q (by omega) hne_q
        · wram_simp
          have hne_v : compIdx (v, true) ≠ compIdx (v, false) := by omega
          simp [hne_v, hok]
    obtain ⟨y, hy_ex, hy_ob, hy_nv, hy_0, hy_1, hy_ok, hy_bits⟩ :=
      extractVarLoop_spec G hfit compIdx vs (idx + 1)
        (ok && decide (compIdx (v, true) ≠ compIdx (v, false))) x₁ (by omega)
        (fun q hq => by
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using hvs (q + 1) (Nat.succ_lt_succ hq))
        hx₁_comp hx₁_prev hx₁_0 hx₁_1 hx₁_2 hx₁_nv hx₁_ob hx₁_cb hx₁_i hx₁_ok
    have hlt : (Cond.lt iReg nv).Holds x := by
      change x.regs iReg < x.regs nv; omega
    exact ⟨y, (hx₁_ex.loop_iter hlt hy_ex).mono (by simp only [List.length_cons]; omega),
      hy_ob, hy_nv, hy_0, hy_1, hy_ok, hy_bits⟩

/-- Populate all `DFS` scratch base-address registers starting at `G.workBase`. -/
@[expose] def setupWorkRegsCode : Code .standard 28 := ram[
  nVerts ← cTwo * nv;
  uReg ← cTwo * mClauses;
  offB ← outBase + nv; offB ← offB + cTwo;
  edgeB ← offB + nVerts; edgeB ← edgeB + cOne;
  revOffB ← edgeB + uReg;
  revEdgeB ← revOffB + nVerts; revEdgeB ← revEdgeB + cOne;
  curB ← revEdgeB + uReg;
  visB ← curB + nVerts; visB ← visB + cOne;
  ordB ← visB + nVerts;
  finB ← ordB;
  stkB ← ordB + nVerts; stkB ← stkB + nVerts;
  compB ← stkB + nVerts; compB ← compB + nVerts; compB ← compB + nVerts ]

theorem not_readsWidth_extractAssignmentCode : ¬ extractAssignmentCode.ReadsWidth := by
  simp [extractAssignmentCode, extractVarBody, Code.ReadsWidth, Op.ReadsWidth, Op.bin]

theorem isRandFree_extractAssignmentCode : extractAssignmentCode.IsRandFree := by
  simp only [extractAssignmentCode, extractVarBody, Code.IsRandFree, and_self]

theorem not_readsWidth_setupWorkRegsCode : ¬ setupWorkRegsCode.ReadsWidth := by
  simp [setupWorkRegsCode, Code.ReadsWidth, Op.ReadsWidth, Op.bin]

theorem isRandFree_setupWorkRegsCode : setupWorkRegsCode.IsRandFree := by
  simp only [setupWorkRegsCode, Code.IsRandFree, and_self]

end Cslib.Algorithms.WordRAM.TwoSAT
