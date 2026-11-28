/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Time
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Header
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Foundations.Data.List.GetD

/-!
# Complete parameter-selecting native caller execution

Only original n,F,pointers/workspace and the actual original signed array words are premises.
The real parameter program determines the regime, the real selector determines its prime,
and the real concrete solver or exhaustive block determines the verdict. Both verdict
directions and original-argument/memory frames are established in the same actual final state.
General arbitrary-old-data execution does not assert physical bounds on unused old words;
original-admission prefix theorems impose those resource hypotheses separately.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

/-- Actual complete ET caller on original arrays. The selected prime and source-reference
memory are derived witnesses of real calls, never algorithm inputs or assumed contracts. -/
theorem exec_at {W n F ap bp cp b : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (x : Data 640) (xn : x.regs Reg.side = n) (xF : x.regs Reg.bound = F)
    (xap : x.regs Reg.ab = ap) (xbp : x.regs Reg.bc = bp)
    (xcp : x.regs Reg.ac = cp) (xb : x.regs Reg.free = b)
    (hab : ap + n * n ≤ b) (hbc : bp + n * n ≤ b) (hac : cp + n * n ≤ b)
    (vab : ∀ q < n * n, x.mem (ap + q) = Signed.encode (values.getD q 0))
    (vbc : ∀ q < n * n, x.mem (bp + q) = Signed.encode (values.getD (n * n + q) 0))
    (vac : ∀ q < n * n, x.mem (cp + q) = Signed.encode (values.getD (2 * (n * n) + q) 0))
    (hW : executionWidth n F b ap bp cp values ≤ W) :
    let V := fun q => values.getD q 0
    let A := fun i j : Fin n => V (pairIndex (i, j))
    let B := fun i j : Fin n => V (n * n + pairIndex (i, j))
    let C := fun i j : Fin n => V (2 * (n * n) + pairIndex (i, j))
    ∃ (p : ℕ) (mem : ℕ → ℕ) (y : Data 640),
      ExecWithin W program x y (timeBound n p values mem) ∧
      (y.regs Reg.result = 0 ∨ y.regs Reg.result = 1) ∧
      (y.regs Reg.result = 1 ↔ HasZeroTriangle A B C) ∧
      (0 < ParameterChoice.blocks n → IsSelectedPrime A B C (ParameterChoice.window n) p) ∧
      (¬0 < ParameterChoice.blocks n → p = 0) ∧
      (∀ q, q < b ∨ workspaceEnd n b values ≤ q → y.mem q = x.mem q) ∧
      y.regs Reg.side = n ∧ y.regs Reg.bound = F ∧ y.regs Reg.ab = ap ∧
      y.regs Reg.bc = bp ∧ y.regs Reg.ac = cp ∧ y.regs Reg.free = b := by
  let V := fun q => values.getD q 0
  let A := fun i j : Fin n => V (pairIndex (i, j))
  let B := fun i j : Fin n => V (n * n + pairIndex (i, j))
  let C := fun i j : Fin n => V (2 * (n * n) + pairIndex (i, j))
  obtain ⟨s, hs, sm, sF, sn, sa, sb, sc, sf, spn, sp, _⟩ := exec_save x
    ((envelope_fits values hW).of_le (Nat.zero_le _))
  obtain ⟨a, ha, an, ablocks, al, ad, ag, aL, aflag, am, ar⟩ := exec_parameters s
    (spn.trans xn) (parameter_fits values hW)
  obtain ⟨aF, aN, aAB, aBC, aAC, aBase, aPrime⟩ :
      a.regs Reg.savedBound = F ∧ a.regs CallableFixedPrime.Reg.n = n ∧
      a.regs CallableFixedPrime.Reg.ab = ap ∧ a.regs CallableFixedPrime.Reg.bc = bp ∧
      a.regs CallableFixedPrime.Reg.ac = cp ∧ a.regs CallableFixedPrime.Reg.base = b ∧
      a.regs CallableFixedPrime.Reg.prime = 0 := by clear hs ha; regs_frame
  have aMem : a.mem = x.mem := am.trans sm
  let cond := Cond.lt CallableFixedPrime.Reg.prime (parameterBank DyadicParameters.Reg.fast)
  obtain ⟨p, mem, r, he, hbool, hiff, hprime, hzero, hframe, hregs⟩ :
      ∃ (p : ℕ) (mem : ℕ → ℕ) (r : Data 640),
        ExecWithin W (.branch cond fast slow) a r (stageBudget n p values mem + 2) ∧
        (r.regs CallableFixedPrime.Reg.found = 0 ∨ r.regs CallableFixedPrime.Reg.found = 1) ∧
        (r.regs CallableFixedPrime.Reg.found = 1 ↔ HasZeroTriangle A B C) ∧
        (0 < ParameterChoice.blocks n → IsSelectedPrime A B C (ParameterChoice.window n) p) ∧
        (¬0 < ParameterChoice.blocks n → p = 0) ∧
        (∀ q, q < b ∨ workspaceEnd n b values ≤ q → r.mem q = a.mem q) ∧
        ∀ j : Fin 640, (143 ≤ j.val ∧ j.val < 160) ∨
          j = CallableFixedPrime.Reg.n ∨ (604 ≤ j.val ∧ j.val ≤ 607) → r.regs j = a.regs j := by
    by_cases hfast : 0 < ParameterChoice.blocks n
    · obtain ⟨p, reference, hp, hout, r, hr, rf, riff, rs, frame, regs⟩ := exec_fast values hlen hv
        hfast a aN ad ag aBase (aAB ▸ hab) (aBC ▸ hbc) (aAC ▸ hac)
        (fun q hq => by rw [aAB, aMem]; exact vab q hq)
        (fun q hq => by rw [aBC, aMem]; exact vbc q hq)
        (fun q hq => by rw [aAC, aMem]; exact vac q hq)
        (counter_magnitude_fits (n := n) (F := F) (b := b) (ap := ap) (bp := bp) (cp := cp) values)
        (by simpa only [aAB, aBC, aAC, ParameterChoice.window,
          Cslib.Algorithms.MatrixMultiplication.Schonhage.D] using
          counter_address_fits (n := n) (F := F) (b := b) (ap := ap) (bp := bp) (cp := cp) values)
        (by simpa only [executionWidth, Nat.add_assoc] using hW)
        (controller_fits values hW) (callable_fits values hW)
      have hstage : ExecWithin W fast a r (stageBudget n p values reference.mem) := by
        simpa only [stageBudget, dite_eq_left hfast, ParameterChoice.window,
          Cslib.Algorithms.MatrixMultiplication.Schonhage.D] using hr
      refine ⟨p, reference.mem, r, (ExecWithin.branch_pos ?_ hstage).mono (by omega), rf, riff,
        fun _ => hp, fun h => False.elim (h hfast), frame, regs⟩
      simpa only [cond, Cond.holds_lt, aPrime, aflag, ite_eq_left hfast] using (by decide : 0 < 1)
    · have abs_bound (q : ℕ) (hq : q < 3 * (n * n)) : |V q| ≤ (F : ℤ) := by
        simpa only [Int.natCast_natAbs] using
          (Int.ofNat_le.mpr (hv (values.getD q 0) (List.getD_mem 0 (by omega))))
      obtain ⟨r, hr, rf, riff, rm, regs⟩ := exec_slow a A B C aN (aAB ▸ hab) (aBC ▸ hbc)
        (aAC ▸ hac) (slow_fits values hW)
        (fun i j => by
          rw [aAB, aMem]
          simpa only [A, V, pairIndex, Nat.add_assoc] using vab _ (pairIndex_lt (i, j)))
        (fun i j => by
          rw [aBC, aMem]
          simpa only [B, V, pairIndex, Nat.add_assoc] using vbc _ (pairIndex_lt (i, j)))
        (fun i j => by
          rw [aAC, aMem]
          simpa only [C, V, pairIndex, Nat.add_assoc] using vac _ (pairIndex_lt (i, j)))
        (fun i j => abs_bound _ (by have := pairIndex_lt (i, j); omega))
        (fun i j => abs_bound _ (by have := pairIndex_lt (i, j); omega))
        (fun i j => abs_bound _ (by have := pairIndex_lt (i, j); omega))
      have hc : ¬cond.Holds a := by
        simp only [cond, Cond.holds_lt, aPrime, aflag, ite_eq_right hfast, lt_self_iff_false,
          not_false_eq_true]
      have hstage : ExecWithin W slow a r (stageBudget n 0 values (fun _ => 0)) := by
        simpa only [stageBudget, dite_eq_right hfast] using hr
      refine ⟨0, fun _ => 0, r, ExecWithin.branch_neg hc hstage, by omega, riff,
        fun h => False.elim (hfast h), fun _ => rfl, fun q _ => congrFun rm q,
        fun j hj => regs j ?_ ?_⟩
      · rcases hj with h | rfl | h <;> first | omega | decide
      · rintro rfl; exact absurd hj (by decide)
  obtain ⟨y, hy, ym, yn, yF, ya, yb, yc, yf, yo, _⟩ := exec_restore (W := W) r
  exact ⟨p, mem, y, hs.seq (ha.seq (he.seq hy)), yo ▸ hbool, yo ▸ hiff, hprime, hzero,
    fun q hq => (congrFun ym q).trans ((hframe q hq).trans (congrFun aMem q)),
    by clear hs ha he hy; regs_frame⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
