/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TwoSAT.Layout

/-!
# Header setup and `O(|φ|)` clause-width validation (`headerSetupCode`, `checkClausesCode`)

Internal Pass 1 subroutines reading `(n, |φ|)` and validating `1 ≤ c.length ≤ 2` across all
encoded clauses.
-/

public section

namespace Cslib.Algorithms.WordRAM.TwoSAT

open Cslib.Logic.PL Cslib.WordRAM
open Cslib.Algorithms.Lean.TwoSAT
open Cslib.Algorithms.WordRAM.ClauseCode
open Reg Cslib.Algorithms.WordRAM.DFS Cslib.Algorithms.WordRAM.DFS.Reg

/-- Setup constants, input dimensions, and `outBase`. -/
@[expose] def headerSetupCode : Code .standard 28 := ram[
  cZero ← #0; cOne ← #1; cTwo ← #2; cThree ← #3;
  outBase ← *cZero; outBase ← outBase + cOne;
  nv ← *cOne; mClauses ← *cTwo ]

/-- Body checking `1 ≤ c.length ≤ 2` and advancing `pReg` by `c.length + 1` in `O(1)` steps. -/
def checkClauseBody : Code .standard 28 := ram[
  jReg ← *pReg;
  if jReg = cZero then [ compIdxReg ← cZero ]
  else [
    if cTwo < jReg then [ compIdxReg ← cZero ] else [ compIdxReg ← compIdxReg ] ];
  pReg ← pReg + jReg; pReg ← pReg + cOne;
  iReg ← iReg + cOne ]

/-- Scan all `mClauses` clauses and set `compIdxReg` to `(checkClauses G.φ).toNat`. -/
@[expose] def checkClausesCode : Code .standard 28 :=
  (ram[ compIdxReg ← cOne; pReg ← cThree; iReg ← cZero ]).seq
    (.loop (.lt iReg mClauses) checkClauseBody)

theorem checkClausesLoop_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∀ (cs : CNF (Fin G.n)) (idx p : ℕ) (ok : Bool) (x : Data 28),
      idx + cs.length = G.φ.length →
      p + (cs.flatMap (encodeClauseBy Fin.val)).length = G.encode.length + 1 →
      ClauseMemAt x.mem p cs →
      x.regs cZero = 0 → x.regs cOne = 1 → x.regs cTwo = 2 →
      x.regs mClauses = G.φ.length →
      x.regs iReg = idx → x.regs pReg = p → x.regs compIdxReg = ok.toNat →
      ∃ y, ExecWithin w (.loop (.lt iReg mClauses) checkClauseBody) x y (12 * cs.length + 2) ∧
        y.mem = x.mem ∧
        y.regs compIdxReg = (cs.foldl (fun acc c => acc && isValidTwoClause c) ok).toNat ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], idx, _, ok, x, hidx, _, _, _, _, _, hm, hi, _, hok => by
    simp only [List.length_nil] at hidx
    exact ⟨x, ExecWithin.loop_exit (by change ¬ x.regs iReg < x.regs mClauses; omega), rfl, hok,
      fun _ _ => rfl⟩
  | c :: cs, idx, p, ok, x, hidx, hp, hcm, hc0, hc1, hc2, hm, hi, hpR, hok => by
    obtain ⟨hlen_p, -, hcm_rest⟩ := clauseMemAt_cons hcm
    have hflat_cons : ((c :: cs).flatMap (encodeClauseBy Fin.val)).length =
        c.length + 1 + (cs.flatMap (encodeClauseBy Fin.val)).length := by
      simp [List.flatMap_cons, length_encodeClauseBy, Nat.add_assoc]
    have hp_bound : Fits w (p + c.length) :=
      G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
    have hp_bound1 : Fits w (p + c.length + 1) :=
      G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
    have hi_bound : Fits w (idx + 1) :=
      G.fits_of_le hfit (by unfold Instance.wordBound; omega)
    obtain ⟨x₁, hx₁_ex, hx₁_mem, hx₁_i, hx₁_p, hx₁_ok, hx₁_fr⟩ :
        ∃ x₁, ExecWithin w checkClauseBody x x₁ 10 ∧ x₁.mem = x.mem ∧
          x₁.regs iReg = idx + 1 ∧ x₁.regs pReg = p + 1 + c.length ∧
          x₁.regs compIdxReg = (ok && isValidTwoClause c).toNat ∧
          (∀ r : Fin 28, r.val < 18 → x₁.regs r = x.regs r) := by
      wram_exec [checkClauseBody,
        hc0, hc1, hc2, hi, hpR, hok, hlen_p, hp_bound, hp_bound1, hi_bound]
      all_goals
        refine ⟨rfl, by wram_simp, by wram_simp; omega, ?_, fun r hr => by regs_lt⟩
        wram_simp
      · simp [isValidTwoClause, ‹c.length = 0›]
      · simp [isValidTwoClause, show ¬c.length ≤ 2 by omega]
      · simp [isValidTwoClause, show 1 ≤ c.length ∧ c.length ≤ 2 by omega]
    have hlt : (Cond.lt iReg mClauses).Holds x := by
      simp only [Cond.holds_lt, hi, hm]
      simp only [List.length_cons] at hidx; omega
    obtain ⟨y, hy_ex, hy_mem, hy_ok, hy_fr⟩ := checkClausesLoop_spec G hfit cs (idx + 1)
      (p + 1 + c.length) (ok && isValidTwoClause c) x₁
      (by simp only [List.length_cons] at hidx; omega)
      (by rw [hflat_cons] at hp; omega)
      (hx₁_mem ▸ hcm_rest)
      ((hx₁_fr cZero (by decide)).trans hc0)
      ((hx₁_fr cOne (by decide)).trans hc1)
      ((hx₁_fr cTwo (by decide)).trans hc2)
      ((hx₁_fr mClauses (by decide)).trans hm)
      hx₁_i hx₁_p hx₁_ok
    exact ⟨y, (ExecWithin.loop_iter hlt hx₁_ex hy_ex).mono (by simp only [List.length_cons]; omega),
      hy_mem.trans hx₁_mem, hy_ok, fun r hr => (hy_fr r hr).trans (hx₁_fr r hr)⟩

theorem not_readsWidth_headerSetupCode : ¬ headerSetupCode.ReadsWidth := by
  simp [headerSetupCode, Code.ReadsWidth, Op.ReadsWidth, Op.bin]

theorem isRandFree_headerSetupCode : headerSetupCode.IsRandFree := by
  simp only [headerSetupCode, Code.IsRandFree, and_self]

theorem not_readsWidth_checkClausesCode : ¬ checkClausesCode.ReadsWidth := by
  simp [checkClausesCode, checkClauseBody, Code.ReadsWidth, Op.ReadsWidth, Op.bin]

theorem isRandFree_checkClausesCode : checkClausesCode.IsRandFree := by
  simp only [checkClausesCode, checkClauseBody, Code.IsRandFree, and_self]

end Cslib.Algorithms.WordRAM.TwoSAT
