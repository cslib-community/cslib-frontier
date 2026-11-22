/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalCount
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalIntervalTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalStartTerm

/-!
# The interval count term computes the interval tensor entry

`intervalCountT` sums the condition test over the replays of all `2^b` coin
strings from the packed start. `intervalCountT_denote`: given terms
implementing an interval's data, it computes Complexitylib's
`localIntervalCount`, which is the tensor entry of an interval vertex of the
block-counting network (`intervalEntryNum`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM
  _root_.Turing.MultiTapeNTM.ChoiceTable

variable {w : List Bool} {k s : ℕ} {State : Type}

variable (e : State ≃ Fin s) (machine : MultiTapePTM k Bool State) in
/-- **The interval count term.** -/
def intervalCountT (R NT bT JpT JmT stI trI stO trO : Term)
    (offI cellI offO dC cellO : Term → Term) : Term :=
  sumT (pow2 bT) fun x => condT k bT JpT JmT stO trO offO dC cellO R
    (runT e machine R NT bT x (startT k R bT NT JpT JmT stI trI offI cellI))

theorem countP_eq_sum (m : ℕ) (p : ℕ → Bool) :
    (List.range m).countP p = ∑ x ∈ Finset.range m, if p x then 1 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.sum_range_succ]
    simp [List.countP_cons]

variable {e : State ≃ Fin s} {machine : MultiTapePTM k Bool State}

/-- **The interval count term computes the interval count.** -/
theorem intervalCountT_denote [DecidableEq State]
    {R NT bT JpT JmT stI trI stO trO : Term} {offI cellI offO dC cellO : Term → Term}
    {OffI CellI OffO DC CellO : ℕ → ℕ} {env : List ℕ}
    (hR : StableAt w R env) (hb : StableAt w bT env) (hN : StableAt w NT env)
    (hJp : StableAt w JpT env) (hJm : StableAt w JmT env) (hstI : StableAt w stI env)
    (htrI : StableAt w trI env) (hstO : StableAt w stO env) (htrO : StableAt w trO env)
    (hoffI : ImplementsFun w env offI OffI) (hcellI : ImplementsFun w env cellI CellI)
    (hoffO : ImplementsFun w env offO OffO) (hdc : ImplementsFun w env dC DC)
    (hcellO : ImplementsFun w env cellO CellO)
    (b : ℕ) (J : Option (Fin k) → ℤ) (δ : Option (Fin k) → SignType)
    (cIn : ControlData k State) (wIn : Fin k → List (Option Bool))
    (cOut : ControlData k State) (wOut : Fin k → List (Option Bool)) (Jp Jm : ℕ)
    (hRv : R.denote w env = radix b w.length s) (hbv : bT.denote w env = b)
    (hNv : NT.denote w env = w.length) (hJpv : JpT.denote w env = Jp)
    (hJmv : JmT.denote w env = Jm)
    (hstIv : stI.denote w env = stc e cIn.1) (htrIv : trI.denote w env = trc cIn.2.2)
    (hstOv : stO.denote w env = stc e cOut.1) (htrOv : trO.denote w env = trc cOut.2.2)
    (hJ : J none = (Jp : ℤ) - Jm)
    (hoffI0 : OffI 0 = cIn.2.1 none) (hoffIh : ∀ h : Fin k, OffI (h + 1) = cIn.2.1 (some h))
    (hoffb : ∀ h, cIn.2.1 (some h) < b) (hlenI : ∀ h, (wIn h).length = 3 * b)
    (hcellIv : ∀ (h : Fin k) c, c < 3 * b → CellI (h * (3 * b) + c) = cc ((wIn h).getD c none))
    (hdc0 : DC 0 = sgnCode (δ none)) (hdch : ∀ h : Fin k, DC (h + 1) = sgnCode (δ (some h)))
    (hoffO0 : OffO 0 = cOut.2.1 none) (hoffOh : ∀ h : Fin k, OffO (h + 1) = cOut.2.1 (some h))
    (hlenO : ∀ h, (wOut h).length = 3 * b)
    (hcellOv : ∀ (h : Fin k) c, c < 3 * b → CellO (h * (3 * b) + c) = cc ((wOut h).getD c none)) :
    (intervalCountT e machine R NT bT JpT JmT stI trI stO trO offI cellI offO dC cellO).denote w
        env = machine.localIntervalCount b w J δ cIn wIn cOut wOut := by
  classical
  have hpos : 0 < radix b w.length s := by unfold radix; positivity
  have hB := bounded_nStart (e := e) w J cIn wIn (stc_lt e _) hoffb (fun h => (hlenI h).le)
  -- the start and the replay at any extension of `env`
  have hstart : ∀ pre : List ℕ, (startT k R bT NT JpT JmT stI trI offI cellI).denote w
      (pre ++ env) = cpack (radix b w.length s) (nStart e b w J cIn wIn) := fun pre => by
    rw [startT_denote (hR.extend pre) (hb.extend pre) (hN.extend pre) (hJp.extend pre)
      (hJm.extend pre) (hstI.extend pre) (htrI.extend pre) (hoffI.extend' pre)
      (hcellI.extend' pre) b J cIn wIn Jp Jm (by rw [hb pre, hbv]) (by rw [hN pre, hNv])
      (by rw [hJp pre, hJpv]) (by rw [hJm pre, hJmv]) (by rw [hstI pre, hstIv])
      (by rw [htrI pre, htrIv]) hJ hoffI0 hoffIh hoffb hlenI hcellIv, hR pre, hRv]
  have hrun : ∀ (pre : List ℕ) (x : Term), StableAt w x (pre ++ env) →
      (runT e machine R NT bT x (startT k R bT NT JpT JmT stI trI offI cellI)).denote w
        (pre ++ env) = cpack (radix b w.length s)
          (nRun e machine w (coinsOf b (x.denote w (pre ++ env))) (nStart e b w J cIn wIn)) :=
    fun pre x hx => runT_denote R NT bT x _ (pre ++ env) (hR.extend pre) (hN.extend pre) hx
      (by rw [hR pre, hRv]) (by rw [hN pre, hNv]) (by rw [hb pre, hbv]) hB (hstart pre)
  rw [localIntervalCount_eq (e := e) b w J δ cIn wIn cOut wOut, countP_eq_sum]
  unfold intervalCountT
  rw [denote_sumT _ _ env (fun x => if NCond e b J δ cOut wOut
      (nRun e machine w (coinsOf b x) (nStart e b w J cIn wIn)) then 1 else 0), denote_pow2, hbv]
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp only [decide_eq_true_eq]
  · intro acc x
    have env' : acc :: x :: env = [acc, x] ++ env := rfl
    have hxs : StableAt w (lvl env.length) ([acc, x] ++ env) := stableAt_lvl (by simp)
    have hrunS : StableAt w (runT e machine R NT bT (lvl env.length)
        (startT k R bT NT JpT JmT stI trI offI cellI)) ([acc, x] ++ env) := fun extra => by
      rw [← List.append_assoc, hrun _ _ (by rw [List.append_assoc]; exact hxs.extend extra),
        hrun _ _ hxs, List.append_assoc, hxs extra]
    rw [env', denote_condT k (hb.extend _) (hR.extend _) hrunS (hJp.extend _) (hJm.extend _)
      (hoffO.extend' _) (hdc.extend' _) (hcellO.extend' _), hrun _ _ hxs]
    have hfit := fits_of_bounded (b := b) (bounded_runPrefix (e := e) (machine := machine) hB x b)
      (by omega)
    rw [← nRun_coinsOf] at hfit
    have hxv : (lvl env.length).denote w ([acc, x] ++ env) = x := by simp
    rw [hxv]
    apply ite_iff
    rw [hb [acc, x], hbv, hJp [acc, x], hJpv, hJm [acc, x], hJmv, hstO [acc, x], hstOv,
      htrO [acc, x], htrOv, hR [acc, x], hRv]
    exact condN_iff hpos hfit b J δ cOut wOut Jp Jm OffO DC CellO hJ hdc0 hdch hoffO0 hoffOh
      hlenO hcellOv

end Cslib.Complexity.NtimeDspace.LocalSim
