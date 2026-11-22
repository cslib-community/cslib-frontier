/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalStart

/-!
# The start term computes the packed start

`startT_denote`: the start term is `cpack R (nStart …)`, when its data terms
implement the interval's start data.
-/

public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM
  _root_.Turing.MultiTapeNTM.ChoiceTable

variable {w : List Bool}

theorem ipAux (P M N : ℕ) :
    (if 0 < (1 - (if P < M then 1 else 0)) * (if P - M < N + 2 then 1 else 0) then P - M
      else 0) = if M ≤ P ∧ P - M < N + 2 then P - M else 0 := by
  by_cases h1 : P < M <;> by_cases h2 : P - M < N + 2 <;> simp [h1, h2]

theorem denote_ipStartT (bT NT JpT JmT o : Term) (env : List ℕ) :
    (ipStartT bT NT JpT JmT o).denote w env =
      ipStart (bT.denote w env) (NT.denote w env) (JpT.denote w env) (JmT.denote w env)
        (o.denote w env) := by
  unfold ipStartT ipStart
  simp only [denote_ite, denote_mul, denote_sub, denote_const, denote_lt, denote_add]
  exact ipAux _ _ _

theorem denote_startCompT {bT NT JpT JmT stI trI : Term} {offI cellI : Term → Term}
    {OffI CellI : ℕ → ℕ} {env : List ℕ} (hb : StableAt w bT env)
    (hoff : ImplementsFun w env offI OffI) (hcell : ImplementsFun w env cellI CellI)
    {i : Term} (hi : StableAt w i env) :
    (startCompT bT NT JpT JmT stI trI offI cellI i).denote w env =
      startComp (bT.denote w env) (NT.denote w env) (JpT.denote w env) (JmT.denote w env)
        (stI.denote w env) (trI.denote w env) OffI CellI (i.denote w env) := by
  have hhT : StableAt w (div (sub i (const 3)) (const 4)) env :=
    (hi.sub (stableAt_const _ _)).div (stableAt_const _ _)
  have hoffA : StableAt w (add (div (sub i (const 3)) (const 4)) (const 1)) env :=
    hhT.add (stableAt_const _ _)
  have hpos : StableAt w (add bT (offI (add (div (sub i (const 3)) (const 4)) (const 1)))) env :=
    hb.add (hoff.stable hoffA)
  have hbase : StableAt w (mul (div (sub i (const 3)) (const 4)) (mul (const 3) bT)) env :=
    hhT.mul ((stableAt_const _ _).mul hb)
  have hposv : (add bT (offI (add (div (sub i (const 3)) (const 4)) (const 1)))).denote w env =
      bT.denote w env + OffI ((i.denote w env - 3) / 4 + 1) := by
    rw [denote_add, hoff.den hoffA]; simp
  have hbasev : (mul (div (sub i (const 3)) (const 4)) (mul (const 3) bT)).denote w env =
      (i.denote w env - 3) / 4 * (3 * bT.denote w env) := by simp
  unfold startCompT startComp
  simp only [denote_ite, denote_eqT, denote_const, denote_ipStartT, hoff.den (stableAt_const _ _),
    denote_mod, denote_sub, denote_leftT hcell hbase hpos, denote_rightT hcell hbase hpos
      ((stableAt_const _ _).mul hb), hcell.den (hbase.add hpos), denote_add, hposv, hbasev,
    denote_mul]
  by_cases h0 : i.denote w env = 0
  · simp [h0]
  by_cases h1 : i.denote w env = 1
  · simp [h1]
  by_cases h2 : i.denote w env = 2
  · simp [h2]
  simp only [h0, h1, h2, ite_false, Nat.lt_irrefl]
  by_cases f0 : (i.denote w env - 3) % 4 = 0
  · simp [f0]
  by_cases f1 : (i.denote w env - 3) % 4 = 1
  · simp [f1]
  by_cases f2 : (i.denote w env - 3) % 4 = 2
  · simp [f2]
  · simp [f0, f1, f2]

variable {k s : ℕ} {State : Type} {e : State ≃ Fin s}

/-- **The start term computes the packed start.** -/
theorem startT_denote {R bT NT JpT JmT stI trI : Term} {offI cellI : Term → Term}
    {OffI CellI : ℕ → ℕ} {env : List ℕ} (hR : StableAt w R env) (hb : StableAt w bT env)
    (hN : StableAt w NT env) (hJp : StableAt w JpT env) (hJm : StableAt w JmT env)
    (hst : StableAt w stI env) (htr : StableAt w trI env)
    (hoff : ImplementsFun w env offI OffI) (hcell : ImplementsFun w env cellI CellI)
    (b : ℕ) (J : Option (Fin k) → ℤ) (cIn : ControlData k State)
    (wIn : Fin k → List (Option Bool)) (Jp Jm : ℕ)
    (hbv : bT.denote w env = b) (hNv : NT.denote w env = w.length)
    (hJpv : JpT.denote w env = Jp) (hJmv : JmT.denote w env = Jm)
    (hstv : stI.denote w env = stc e cIn.1) (htrv : trI.denote w env = trc cIn.2.2)
    (hJ : J none = (Jp : ℤ) - Jm) (hoff0 : OffI 0 = cIn.2.1 none)
    (hoffh : ∀ h : Fin k, OffI (h + 1) = cIn.2.1 (some h)) (hoffb : ∀ h, cIn.2.1 (some h) < b)
    (hlen : ∀ h, (wIn h).length = 3 * b)
    (hcellv : ∀ (h : Fin k) c, c < 3 * b → CellI (h * (3 * b) + c) = cc ((wIn h).getD c none)) :
    (startT k R bT NT JpT JmT stI trI offI cellI).denote w env =
      cpack (R.denote w env) (nStart e b w J cIn wIn) := by
  unfold startT
  rw [denote_sumT _ _ env (fun i => startComp b w.length Jp Jm (stc e cIn.1) (trc cIn.2.2)
    OffI CellI i * R.denote w env ^ i)]
  · rw [denote_const, cpack, packDigits]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [startComp_eq b w J cIn wIn Jp Jm OffI CellI hJ hoff0 hoffh hoffb hlen hcellv
      (Finset.mem_range.mp hi)]
  · intro acc i
    have env' : acc :: i :: env = [acc, i] ++ env := rfl
    have hR' : StableAt w R (acc :: i :: env) := hR.extend [acc, i]
    rw [denote_mul, powT_denote _ _ _ hR', env',
      denote_startCompT (hb.extend _) (hoff.extend' _) (hcell.extend' _) (stableAt_lvl (by simp))]
    simp only [← env', hb.cons₂, hN.cons₂, hJp.cons₂, hJm.cons₂, hst.cons₂, htr.cons₂, hR.cons₂,
      hbv, hNv, hJpv, hJmv, hstv, htrv, denote_lvl_index]

end Cslib.Complexity.NtimeDspace.LocalSim
