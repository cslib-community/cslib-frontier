/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceSemantics
public import CslibFrontier.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceStepCert
public import CslibFrontier.Computability.PolyTime.CNF.BranchedSparseCNFCounter
import CslibFrontier.Tactic.EncLen
import all CslibFrontier.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceStepCert
import CslibFrontier.Computability.Complexity.FineGrained.SparseBranchAsymptotics
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Data.List.Fold
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Native Resource Bounds for the Bounded-Incidence Branch Evaluator (Proposition 5.3)

This file establishes the native multi-tape Turing machine resource certificate, global polynomial
workspace bound across all raw `BranchEvalInput` tuples, and subexponential
$O^*(2^{O(\mathrm{interpolationScale}(n'))})$ runtime bound for the Proposition 5.3
bounded-incidence, bounded-width $\mathbb{F}_2$ polynomial-system branch evaluator
`evalBoundedIncidenceBranch` of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
(§§3.4–3.5, §4.7, §§5.3–5.5, Proposition 5.3, and Appendix B.2–B.3, pp. 24–26, 34–35, 37–39,
48–50).

The certificate reuses the private encodings and polynomial-time lemmas of
`BoundedIncidenceStepCert`, which this module completes and reads through `import all`.

## Main definitions

* `Cslib.Complexity.SubexponentialSAT.SparsePolyCounter.boundedIncidenceBranchCertificate`:
  uniform `NativeCertificate` for `evalBoundedIncidenceBranch` on `encBranchEvalInput`.

## Main results

* `SparsePolyCounter.auxDim_lt_self_of_two_le`: `ReplacementParams.auxDim n' < n'` for `2 ≤ n'`.
* `SparsePolyCounter.polyBounded_boundedIncidenceBranchCertificate_space`: global `PolyBounded`
  workspace bound across all raw `BranchEvalInput` tuples.
* `SparsePolyCounter.exists_boundedIncidenceBranchCertificate_time_bound`: subexponential
  $O^*(2^{O(\mathrm{interpolationScale}(n'))})$ branch runtime bound on
  `prepareBranchEvalInput (n', sys')` under polylogarithmic factor incidence and scope width
  (Proposition 5.3, pp. 37–39).
* `SparsePolyCounter.branchPolylogTimeBound_boundedIncidenceBranchCertificate`: discharges
  `Cslib.Complexity.BranchedSparseCNFCounter.BranchPolylogTimeBound` for
  `boundedIncidenceBranchCertificate`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§3.4–3.5, §4.7, §§5.3–5.5,
  Proposition 5.3, Appendix B.2–B.3.
-/

namespace Cslib.Complexity.SubexponentialSAT.SparsePolyCounter

open Finset Cslib Cslib.BitString Cslib.CommonCountingAccum Cslib.Complexity Cslib.GenericRAM
open Cslib.LinearAlgebra Turing.MultiTapeTM ComputableInPolyTime

local notation "PolyT" => ComputableInPolyTime
local notation "Cert" => NativeCertificate

/-! ### 1. Asymptotic Branch Step-Count Transfer to `interpolationScale` -/

/-- For `2 ≤ n'`, the Section 4.7 auxiliary dimension `auxDim n' = r ^ (2 * Q)` is strictly bounded
by `n'` itself (since `D ≤ 2 ^ (λ / 128) ≤ 2 ^ (λ - 1) < n'`). -/
public theorem auxDim_lt_self_of_two_le {n' : ℕ} (hn' : 2 ≤ n') :
    ReplacementParams.auxDim n' < n' := by
  have hlam1 : 1 ≤ Nat.clog 2 n' := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega)
  have hpow_lt : 2 ^ (Nat.clog 2 n' - 1) < n' := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mp
    (by omega)
  exact (ReplacementParams.auxDim_le_two_pow n').trans_lt
    ((Nat.pow_le_pow_right Nat.zero_lt_two (by omega)).trans_lt hpow_lt)

private theorem numGroups_pow_numNodes_le_self {n' : ℕ} (hn' : 2 ≤ n')
    (hr : 1 ≤ ReplacementParams.numGroups n') :
    ReplacementParams.numGroups n' ^ ReplacementParams.numNodes n' ≤ n' := by
  refine (?_ : _ ≤ ReplacementParams.auxDim n').trans (auxDim_lt_self_of_two_le hn').le
  unfold ReplacementParams.auxDim; exact Nat.pow_le_pow_right hr (by omega)

private theorem chooseBeta_le_succ_of_le_mul_clog_pow {n' b w β C_inc : ℕ}
    (hn4 : 4 ≤ n') (hnC : 2 ^ C_inc ≤ n')
    (hb : b ≤ C_inc * Nat.clog 2 n' ^ β) (hw : w ≤ C_inc * Nat.clog 2 n' ^ β) :
    1 ≤ ParameterCheck.chooseBeta (Nat.clog 2 n') b w ∧
      ParameterCheck.chooseBeta (Nat.clog 2 n') b w ≤ β + 1 := by
  set lam := Nat.clog 2 n'
  have hlam2 : 2 ≤ lam :=
    (Nat.clog_pow 2 2 Nat.one_lt_two).symm.trans_le (Nat.clog_mono_right 2 hn4)
  have hC : C_inc ≤ lam :=
    (Nat.clog_pow 2 C_inc Nat.one_lt_two).symm.trans_le (Nat.clog_mono_right 2 hnC)
  have hb' : b ≤ lam ^ (β + 1) := pow_succ' lam β ▸ hb.trans (Nat.mul_le_mul_right _ hC)
  have hw' : w ≤ lam ^ (β + 1) := pow_succ' lam β ▸ hw.trans (Nat.mul_le_mul_right _ hC)
  obtain ⟨h1, _, _, hmin⟩ := ParameterCheck.chooseBeta_spec (b := b) (w := w) hlam2
  exact ⟨h1, by_contra fun hgt => hmin (β + 1) (Nat.succ_pos β) (Nat.lt_of_not_ge hgt) ⟨hb', hw'⟩⟩

private theorem step_prefactor_le {rQ Q r S M G L : ℕ} (hrQ : rQ ≤ L) (hQ : Q ≤ L) (hr2 : 2 ≤ r)
    (hrL : r ≤ L) (hS : 1 ≤ S) (hM : 1 ≤ M) (hG : 1 ≤ G) :
    (rQ + 1) + (Q + 1) * (S + 1) * (M + 1) * (r * (G + 1) + 1) ≤
      64 * (L + 1) ^ 3 * (S * M * G) := by
  have hE : 1 ≤ S * M * G := Nat.mul_pos (Nat.mul_pos hS hM) hG
  have hGp1 : r * (G + 1) + 1 ≤ 4 * (L + 1) * G := by nlinarith
  have hprod4 : (Q + 1) * (S + 1) * (M + 1) * (r * (G + 1) + 1) ≤
      16 * (L + 1) ^ 2 * (S * M * G) :=
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega : Q + 1 ≤ L + 1)
      (by omega : S + 1 ≤ 2 * S)) (by omega : M + 1 ≤ 2 * M)) hGp1).trans_eq (by ring)
  have hL3 : L + 1 ≤ (L + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hL23 : (L + 1) ^ 2 ≤ (L + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos L) (by omega)
  nlinarith

private theorem nat_pow_le_exp_of_le {b e : ℕ} {r u : ℝ}
    (hb : 1 ≤ (b : ℝ)) (he : (e : ℝ) ≤ r) (hu : Real.log b * r ≤ u) :
    ((b ^ e : ℕ) : ℝ) ≤ Real.exp u :=
  calc ((b ^ e : ℕ) : ℝ)
      = (b : ℝ) ^ (e : ℝ) := by rw [Nat.cast_pow, Real.rpow_natCast]
    _ ≤ (b : ℝ) ^ r := Real.rpow_le_rpow_of_exponent_le hb he
    _ = Real.exp (Real.log b * r) := Real.rpow_def_of_pos (zero_lt_one.trans_le hb) _
    _ ≤ Real.exp u := Real.exp_le_exp.mpr hu

private theorem threeTerm_product_le_two_pow {β β' n' b w a q c_meas d_max c_deg : ℕ}
    (hn16384 : 16384 ≤ n') (hβ' : β' ≤ β + 1)
    (hF : ReplacementParams.Feasible β' n' b w a)
    (hq_real : (q : ℝ) ≤ (c_deg : ℝ) * (n' : ℝ) *
      ((ReplacementParams.rowBound β' n' : ℝ) / ReplacementParams.numNodes n'))
    (hc_meas : (c_meas : ℝ) ≤ 2 * ReplacementParams.tau n' * (n' : ℝ))
    (hd_max : d_max ≤ 2 * n' / ReplacementParams.numGroups n') :
    ((Cslib.subsetPairCount n' q *
      (2 * ReplacementParams.auxDim n' + 1) ^ c_meas * 2 ^ d_max : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (((65792 * (c_deg + 4) * (β + 4) : ℕ) : ℝ) * interpolationScale n') := by
  set D := ReplacementParams.auxDim n'
  set r := ReplacementParams.numGroups n'; set Q := ReplacementParams.numNodes n'
  set R := ReplacementParams.rowBound β' n'
  have hR32 : 32 ≤ R := hF.thirtyTwo_le_rowBound
  have hRQ6 : 6 * R ≤ Q := hF.six_mul_rowBound_le_numNodes
  have hS := Cslib.ReplacementCounting.subsetPairCount_le_exp_mul_log_ratio
    (by omega : 1 ≤ R) (by omega : R ≤ Q) hq_real
  have hM : (((2 * D + 1) ^ c_meas : ℕ) : ℝ) ≤ Real.exp
      (((c_deg : ℝ) + 4) * (n' : ℝ) * (ReplacementParams.tau n' * Real.log (2 * D + 1))) := by
    have hlog := Real.log_nonneg (by push_cast; linarith : (1 : ℝ) ≤ (2 * D + 1 : ℕ))
    refine nat_pow_le_exp_of_le (by push_cast; linarith) hc_meas ?_
    have h := mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) c_deg] :
      (2 : ℝ) ≤ c_deg + 4) (mul_nonneg (Nat.cast_nonneg n') (mul_nonneg hF.tau_pos.le hlog))
    push_cast at h ⊢; linarith
  have hG : ((2 ^ d_max : ℕ) : ℝ) ≤
      Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) * (1 / (r : ℝ))) := by
    have hd : (d_max : ℝ) ≤ 2 * (n' : ℝ) / r :=
      ((Nat.cast_le.mpr hd_max).trans (Nat.cast_div_le (α := ℝ))).trans_eq (by push_cast; ring)
    refine nat_pow_le_exp_of_le (by norm_num) hd ?_
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos zero_lt_two]
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) c_deg] :
        2 * Real.log 2 ≤ c_deg + 4) (by positivity : (0 : ℝ) ≤ n' / r)
  have hE : ((Cslib.subsetPairCount n' q * (2 * D + 1) ^ c_meas * 2 ^ d_max : ℕ) : ℝ) ≤
      Real.exp (((c_deg : ℝ) + 4) * (n' : ℝ) * ReplacementParams.rowCost β' n') := by
    rw [Nat.cast_mul, Nat.cast_mul, ← ReplacementParams.threeTermExponent_eq_rowCost β' n']
    refine (mul_le_mul (mul_le_mul hS hM (by positivity) (by positivity))
      hG (by positivity) (by positivity)).trans_eq ?_
    rw [← Real.exp_add, ← Real.exp_add]; congr 1
    unfold Cslib.ReplacementCounting.threeTermExponent; ring
  have hscale_nn : 0 ≤ interpolationScale n' :=
    (by positivity : (0 : ℝ) ≤ 2 * Q * r).trans
      (ReplacementParams.two_mul_numNodes_mul_numGroups_le_interpolationScale hn16384 le_rfl)
  have hrc : (n' : ℝ) * ReplacementParams.rowCost β' n' ≤
      32896 * ((β : ℝ) + 4) * interpolationScale n' :=
    (hF.mul_rowCost_le_interpolationScale hn16384 (by omega) le_rfl).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (by exact_mod_cast (by omega : β' + 3 ≤ β + 4)) (by positivity)) hscale_nn)
  have hexp : ((c_deg : ℝ) + 4) * (n' : ℝ) * ReplacementParams.rowCost β' n' ≤
      ((32896 * (c_deg + 4) * (β + 4) : ℕ) : ℝ) * interpolationScale n' := by
    rw [mul_assoc]; exact (mul_le_mul_of_nonneg_left hrc (by positivity)).trans_eq
      (by push_cast; ring)
  exact (hE.trans (Real.exp_le_exp.mpr hexp)).trans
    ((exp_le_two_rpow_two_mul (by positivity)).trans_eq
      (congrArg ((2 : ℝ) ^ ·) (by push_cast; ring)))

/-- Core subexponential step-count bound for Proposition 5.3: under `checkBranchFeasible`,
polylogarithmic `(b, w)` bounds, linear equation count `sys'.length ≤ C_inc * n'`, and degree
`sysMaxDegree sys' ≤ k_deg`, any parametric loop-product bound is dominated above
`max 16384 (2 ^ C_inc)` by a fixed polynomial in
`(encPair encUnary encSparseSystem (n', sys')).length`
times `2 ^ (A_br * interpolationScale n')`. -/
private theorem parametric_branch_step_bound {N₀_branch k_deg β C_inc C_p d_p : ℕ}
    {T : ℕ × List (List (List ℕ)) → ℕ}
    (hT : ∀ n' sys', checkBranchFeasible N₀_branch (n', sys') = true → 16384 ≤ n' →
      let β' := ParameterCheck.chooseBeta (Nat.clog 2 n')
        (branchMaxFactorIncidence n' sys') (branchMaxFactorWidth n' sys')
      let r := ReplacementParams.numGroups n'; let Q := ReplacementParams.numNodes n'
      let R := ReplacementParams.rowBound β' n'
      let q := (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n') / max 1 Q
      ∃ c_meas d_max : ℕ, (c_meas : ℝ) ≤ 2 * ReplacementParams.tau n' * (n' : ℝ) ∧
        d_max ≤ 2 * n' / r ∧ T (n', sys') ≤ ((r ^ Q + 1) + (Q + 1) *
          (SubsetPairFold.subsetPairCount n' q + 1) * ((2 * r ^ (2 * Q) + 1) ^ c_meas + 1) *
            (r * (2 ^ d_max + 1) + 1)) *
          (C_p * ((encPair encUnary encSparseSystem (n', sys')).length + 1) ^ d_p)) :
    let c_deg := k_deg * (C_inc + 2); let A_br := 65792 * (c_deg + 4) * (β + 4)
    ∀ n' : ℕ, ∀ sys' : List (List (List ℕ)),
      checkBranchFeasible N₀_branch (n', sys') = true → max 16384 (2 ^ C_inc) ≤ n' →
      sysMaxDegree sys' ≤ k_deg → sys'.length ≤ C_inc * n' →
      branchMaxFactorIncidence n' sys' ≤ C_inc * Nat.clog 2 n' ^ β →
      branchMaxFactorWidth n' sys' ≤ C_inc * Nat.clog 2 n' ^ β →
      (T (n', sys') : ℝ) ≤
        ((64 * C_p : ℕ) : ℝ) *
            ((encPair encUnary encSparseSystem (n', sys')).length + 1 : ℝ) ^ (d_p + 3) *
          (2 : ℝ) ^ ((A_br : ℝ) * interpolationScale n') := by
  intro c_deg A_br n' sys' hfeas hn' hdeg hlen hb hw
  have hn16384 : 16384 ≤ n' := (le_max_left _ _).trans hn'
  obtain ⟨_, _, _, hF⟩ := feasible_of_checkBranchFeasible hfeas
  set β' := ParameterCheck.chooseBeta (Nat.clog 2 n')
    (branchMaxFactorIncidence n' sys') (branchMaxFactorWidth n' sys')
  set r := ReplacementParams.numGroups n'; set Q := ReplacementParams.numNodes n'
  set R := ReplacementParams.rowBound β' n'
  set q := (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n') / max 1 Q
  obtain ⟨_, hβ'_le⟩ :=
    chooseBeta_le_succ_of_le_mul_clog_pow (by omega) ((le_max_right _ _).trans hn') hb hw
  obtain ⟨c_meas, d_max, hc_meas, hd_max, hT_le⟩ := hT n' sys' hfeas hn16384
  have hr2 : 2 ≤ r := hF.two_le_numGroups; have hR32 : 32 ≤ R := hF.thirtyTwo_le_rowBound
  have hRQ6 : 6 * R ≤ Q := hF.six_mul_rowBound_le_numNodes; have hQ_pos : 1 ≤ Q := by omega
  have hvar_bal : 2 * Q * r ^ 2 ≤ n' := hF.var_balance
  have hQ_le_n : Q ≤ n' := by nlinarith [Nat.one_le_pow 2 r (by omega : 0 < r)]
  have hr_le_n : r ≤ n' := by nlinarith
  have hn_le_enc : n' ≤ (encPair encUnary encSparseSystem (n', sys')).length := by enc_len
  generalize (encPair encUnary encSparseSystem (n', sys')).length = L at hn_le_enc hT_le ⊢
  set S_sp := Cslib.subsetPairCount n' q; set D := ReplacementParams.auxDim n'
  have hS_eq : SubsetPairFold.subsetPairCount n' q = S_sp := SubsetPairFold.subsetPairCount_eq n' q
  set E_nat := S_sp * (2 * D + 1) ^ c_meas * 2 ^ d_max
  have hstep_nat : (r ^ Q + 1) + (Q + 1) * (SubsetPairFold.subsetPairCount n' q + 1) *
      ((2 * r ^ (2 * Q) + 1) ^ c_meas + 1) * (r * (2 ^ d_max + 1) + 1) ≤
      64 * (L + 1) ^ 3 * E_nat := by
    rw [hS_eq, (rfl : r ^ (2 * Q) = D)]
    exact step_prefactor_le ((numGroups_pow_numNodes_le_self (by omega) (by omega)).trans hn_le_enc)
      (hQ_le_n.trans hn_le_enc) hr2 (hr_le_n.trans hn_le_enc)
      (hS_eq ▸ SubsetPairFold.subsetPairCount_pos n' q) (Nat.one_le_pow _ _ (by omega))
      Nat.one_le_two_pow
  have hq_real : (q : ℝ) ≤ (c_deg : ℝ) * (n' : ℝ) * ((R : ℝ) / Q) := by
    have hnum : (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n') ≤ c_deg * n' * R :=
      (Nat.mul_le_mul (Nat.mul_le_mul hdeg (Nat.sub_le R 1))
        (by rw [Nat.add_mul]; omega : sys'.length + 2 * n' ≤ (C_inc + 2) * n')).trans_eq
        (by dsimp only [c_deg]; ring)
    have hq_le : q ≤ (c_deg * n' * R) / Q := by
      simpa only [q, Nat.max_eq_right hQ_pos] using Nat.div_le_div_right hnum
    exact ((Nat.cast_le.mpr hq_le).trans Nat.cast_div_le).trans_eq (by push_cast; ring)
  have hE_pow2 := threeTerm_product_le_two_pow hn16384 hβ'_le hF hq_real hc_meas hd_max
  have hT_nat : T (n', sys') ≤ (64 * C_p * (L + 1) ^ (d_p + 3)) * E_nat :=
    (hT_le.trans (Nat.mul_le_mul_right _ hstep_nat)).trans_eq (by rw [pow_add]; ring)
  exact ((Nat.cast_le.mpr hT_nat).trans_eq (by dsimp only [E_nat, S_sp]; push_cast; ring)).trans
    (mul_le_mul_of_nonneg_left hE_pow2 (by positivity))

/-! ### 2. Outer Loop Certificates and Global Polynomial Workspace -/

section LoopCertificates

private theorem poly_apply_le {α : Type} {f Lfn : α → ℕ} {c d L : ℕ}
    (hf : ∀ a, f a ≤ c * (Lfn a + 1) ^ d) {a : α} (hla : Lfn a ≤ L) :
    f a ≤ c * (L + 1) ^ d :=
  (hf a).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hla 1) d))

private theorem computableInPolyTime_ctxAddJet
    {α Ctx : Type} {eα : α ↪ List Bool} {eCtx : Ctx ↪ List Bool}
    {J ℓ : Ctx → ℕ} (hJ : PolyT J eCtx encUnary) (hℓ : PolyT ℓ eCtx encUnary) :
    PolyT (fun q : (α × (Ctx × JetRows)) × JetRows =>
      (q.1.2.1, addJet (J q.1.2.1) (ℓ q.1.2.1) q.1.2.2 q.2))
      (encPair (encPair eα (encPair eCtx encJet)) encJet) (encPair eCtx encJet) := by
  have hq1 := fst (encPair eα (encPair eCtx encJet)) encJet
  have hq2 := snd (encPair eα (encPair eCtx encJet)) encJet
  have hctx := hq1.snd'.fst'
  exact hctx.prod (computableInPolyTime_addJet (hJ.comp hctx) (hℓ.comp hctx) hq1.snd'.snd' hq2)

private def jetFoldBound (J ℓ bN bM : ℕ) : ℕ :=
  J * (2 * (ℓ * (2 * (bN + (bM + 1)) + 3)) + 1)

private theorem jetFoldl_bound_mono {J ℓ N M bN : ℕ} (hN : N.size ≤ bN) :
    J * (2 * (ℓ * (2 * (N.size + (2 ^ M).size) + 3)) + 1) ≤ jetFoldBound J ℓ bN M := by
  have hM : (2 ^ M).size ≤ M + 1 := by rw [Nat.size_pow]
  unfold jetFoldBound; gcongr

private theorem mul_inner_add_absorb {A B p q ov r : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hr : p + q + ov ≤ r) :
    A * (B * p + q) + ov ≤ A * B * r := by
  have hAB : 1 ≤ A * B := Nat.mul_pos hA hB
  calc A * (B * p + q) + ov
      ≤ A * (B * (p + q)) + A * B * ov :=
        Nat.add_le_add (Nat.mul_le_mul_left A (absorb_step_add B p q hB))
          (Nat.le_mul_of_pos_left ov hAB)
    _ = A * B * (p + q + ov) := by ring
    _ ≤ A * B * r := Nat.mul_le_mul_left _ hr

private theorem exists_computableInO_pairPost {α β γ : Type}
    {eα : α ↪ List Bool} {eβ : β ↪ List Bool} {eγ : γ ↪ List Bool}
    {f : α → β} {g : α × β → γ} {A B p q sp : α → ℕ}
    (hf : ComputableInO f eα eβ (fun a => A a * (B a * p a + q a)) sp)
    (hsp : PolyBounded (fun a => (eα a).length) sp)
    (hp : PolyBounded (fun a => (eα a).length) p)
    (hq : PolyBounded (fun a => (eα a).length) q)
    (hA : ∀ a, 1 ≤ A a) (hB : ∀ a, 1 ≤ B a)
    (hg : PolyT g (encPair eα eβ) eγ) :
    ∃ P : α → ℕ, PolyBounded (fun a => (eα a).length) P ∧
      ComputableInO (fun a => g (a, f a)) eα eγ (fun a => A a * B a * P a) P := by
  let cF : Cert f eα eβ := ⟨_, sp, hf⟩
  obtain ⟨cG, hcG⟩ := NativeCertificate.exists_polynomial hg
  let cId := NativeCertificate.linear (ei := eα) (ComputableInO.of_eq fun _ => rfl)
  let cOut := cG.comp (cId.prod cF)
  have hspP : HasPolySpace (cId.prod cF) := hasPolySpace_prod .self hsp
  let P (a : α) : ℕ := p a + q a + ((eα a).length + cG.time (a, f a)) + cOut.space a
  have hP : PolyBounded (fun a => (eα a).length) P := by
    have hGt : PolyBounded (fun a => (eα a).length) (fun a => cG.time (a, f a)) :=
      hcG.1.comp (polyBounded_length_of_hasPolySpace hspP)
    have hOs : PolyBounded (fun a => (eα a).length) cOut.space := hasPolySpace_comp hcG.2 hspP
    growth_poly [hGt, hOs]
  refine ⟨P, hP, cOut.computes.mono_le (fun a => ?_) fun _ => Nat.le_add_left _ _⟩
  exact (by dsimp only [cOut, cId, cF, NativeCertificate.comp_time, NativeCertificate.prod_time,
      NativeCertificate.linear_time, Function.comp_apply]; omega :
    cOut.time a ≤ A a * (B a * p a + q a) + ((eα a).length + cG.time (a, f a))).trans
    (mul_inner_add_absorb (hA a) (hB a) (by dsimp only [P]; omega))

private theorem exists_computableInO_guardZero {α : Type} {eα : α ↪ List Bool}
    {p : α → Bool} {f : α → ℕ} {K Pf : α → ℕ}
    (hp : PolyT p eα encBool) (hK : ∀ a, 1 ≤ K a)
    (hf : ComputableInO f eα encNat (fun a => K a * Pf a) Pf)
    (hPf : PolyBounded (fun a => (eα a).length) Pf) :
    ∃ P : α → ℕ, PolyBounded (fun a => (eα a).length) P ∧
      ComputableInO (fun a => if p a then f a else 0) eα encNat (fun a => K a * P a) P := by
  obtain ⟨cP, hcP⟩ := NativeCertificate.exists_polynomial hp
  let cB := NativeCertificate.branch cP (⟨_, Pf, hf⟩ : Cert f eα encNat)
    (NativeCertificate.const (ei := eα) (em := encNat) 0)
  have hcB_sp : PolyBounded (fun a => (eα a).length) cB.space :=
    ExhaustiveCountFallback.polyBounded_branch_space _ _ _ hcP.2 hPf
      (NativeCertificate.const_isPolynomial 0).2
  let P (a : α) : ℕ := cP.time a + (eα a).length + Pf a + cB.space a
  refine ⟨P, by growth_poly [hcB_sp],
    cB.computes.mono_le (fun a => ?_) fun _ => Nat.le_add_left _ _⟩
  dsimp only [cB]; simp only [NativeCertificate.branch_time, NativeCertificate.const_time]
  split_ifs
  · exact (Nat.add_le_add (Nat.le_mul_of_pos_left _ (hK a)) le_rfl).trans
      (by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by dsimp only [P]; omega))
  · exact (Nat.le_mul_of_pos_left _ (hK a)).trans
      (Nat.mul_le_mul_left _ (by dsimp only [P]; omega))

private def mkMeasCtx (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) : MeasStepCtx :=
  (dc.2.1, dc.2.2.2.1, dc.2.2.2.2.1, dc.2.2.2.2.2.1, (dc.1.1, dc.1.2.1), dc.2.2.2.2.2.2)

private def evalSignedMeasJet (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) : JetRows :=
  let measJet := (MeasurementFold.run measurementStepBody dc.2.2.1
    (mkMeasCtx dc, zeroJet dc.2.jetOrder dc.2.precision)).2.2.2
  if dc.1.2.2 then smulJet dc.2.jetOrder dc.2.precision (-1) measJet else measJet

private theorem subsetPairStepBody_eq
    (inp : SubsetPairFold.DecodedPair × (SubsetStepCtx × JetRows)) :
    subsetPairStepBody inp = (inp.2.1, addJet inp.2.1.jetOrder inp.2.1.precision inp.2.2
      (evalSignedMeasJet (inp.1, inp.2.1))) := rfl

private theorem computableInPolyTime_mkMeasCtx :
    PolyT mkMeasCtx (encPair SubsetPairFold.encDecodedPair encSubsetStepCtx) encMeasStepCtx := by
  have hdc1 := fst SubsetPairFold.encDecodedPair encSubsetStepCtx
  have hdc2 := snd SubsetPairFold.encDecodedPair encSubsetStepCtx
  unfold SubsetPairFold.encDecodedPair encSubsetStepCtx at hdc1 hdc2
  unfold encMeasStepCtx mkMeasCtx
  exact hdc2.fst'.prod (hdc2.snd'.snd'.fst'.prod (hdc2.snd'.snd'.snd'.fst'.prod
    (hdc2.snd'.snd'.snd'.snd'.fst'.prod ((hdc1.fst'.prod hdc1.snd'.fst').prod
      hdc2.snd'.snd'.snd'.snd'.snd'))))

private theorem measFold_run_eq (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) (j : ℕ) :
    (IndexFold.run (MeasurementFold.visit measurementStepBody) j
      (dc.2.2.1, (mkMeasCtx dc, zeroJet dc.2.jetOrder dc.2.precision))).2 =
    (dc.2.2.1, (mkMeasCtx dc, (List.range j).foldl
      (fun acc i => (evalMeasPayload
        (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, mkMeasCtx dc)).elim acc
        (fun y => addJet dc.2.jetOrder dc.2.precision acc y))
      (zeroJet dc.2.jetOrder dc.2.precision))) := by
  refine Prod.ext (MeasurementFold.prefix_parameters _ _ _ _) ?_
  change (MeasurementFold.runPrefix measurementStepBody dc.2.2.1 j
    (mkMeasCtx dc, zeroJet dc.2.jetOrder dc.2.precision)).2.2 = _
  rw [MeasurementFold.prefix_accumulator]; simp only [measurementStepBody_eq]
  have hstep : (fun (acc : MeasStepCtx × JetRows) (i : ℕ) =>
      (evalMeasPayload (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, acc.1)).elim acc
        fun y => (acc.1, addJet acc.1.2.1.1 acc.1.2.1.2.1 acc.2 y)) =
    fun pa i => (pa.1,
      (evalMeasPayload (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, pa.1)).elim pa.2
        fun y => addJet pa.1.2.1.1 pa.1.2.1.2.1 pa.2 y) :=
    funext fun pa => funext fun i => by cases evalMeasPayload _ <;> rfl
  rw [hstep]
  exact List.foldl_keep_fst
    (fun (m : MeasStepCtx) (acc : JetRows) (i : ℕ) =>
      (evalMeasPayload (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, m)).elim acc
        (fun y => addJet m.2.1.1 m.2.1.2.1 acc y))
    (mkMeasCtx dc) (List.range j) (zeroJet dc.2.jetOrder dc.2.precision)

private theorem exists_measVisit_cert
    (cPay : Cert evalMeasPayload (encPair (encList encIntBin) encMeasStepCtx) (encOption encJet))
    (hcPay_sp : HasPolySpace cPay) :
    let eAcc := encPair encMeasStepCtx encJet
    let eOut := encPair (encPair encUnary encNat) eAcc
    let eSt := encPair encNat eOut
    ∃ (cVisit : Cert (MeasurementFold.visit measurementStepBody) eSt eOut) (cv dv : ℕ),
      HasPolySpace cVisit ∧
      ∀ st : ℕ × ((ℕ × ℕ) × (MeasStepCtx × JetRows)),
        cVisit.time st ≤
          2 * cPay.time (Cslib.Radix.measurementValues st.2.1.1 st.2.1.2 st.1, st.2.2.1) +
            cv * ((eSt st).length + 1) ^ dv := by
  let eWC := encPair (encList encIntBin) encMeasStepCtx
  let eAcc := encPair encMeasStepCtx encJet
  let eMIn := encPair (encPair (encPair encUnary encNat) (encList encIntBin)) eAcc
  have hprojWC : PolyT
      (fun inp : ((ℕ × ℕ) × List ℤ) × (MeasStepCtx × JetRows) => (inp.1.2, inp.2.1)) eMIn eWC :=
    (fst _ eAcc).snd'.prod (snd _ eAcc).fst'
  have haddM : PolyT
      (fun q : (((ℕ × ℕ) × List ℤ) × (MeasStepCtx × JetRows)) × JetRows =>
        (q.1.2.1, addJet q.1.2.1.jetOrder q.1.2.1.precision q.1.2.2 q.2))
      (encPair eMIn encJet) eAcc :=
    computableInPolyTime_ctxAddJet (J := MeasStepCtx.jetOrder) (ℓ := MeasStepCtx.precision)
      (by unfold encMeasStepCtx; exact (snd _ _).fst'.fst')
      (by unfold encMeasStepCtx; exact (snd _ _).fst'.snd'.fst')
  obtain ⟨cProjWC, hcProjWC⟩ := NativeCertificate.exists_polynomial hprojWC
  obtain ⟨cAddM, hcAddM⟩ := NativeCertificate.exists_polynomial haddM
  let cNoM := NativeCertificate.snd
    (NativeCertificate.linear (ei := eMIn) (ComputableInO.of_eq fun _ => rfl))
  let cValM := cPay.comp cProjWC; let cbM₀ := NativeCertificate.option cValM cNoM cAddM
  have hcValM_sp : HasPolySpace cValM := hasPolySpace_comp hcPay_sp hcProjWC.2
  have hcbM_sp : HasPolySpace cbM₀ := by
    dsimp only [HasPolySpace, cbM₀, cValM, cNoM, NativeCertificate.option, NativeCertificate.comp,
      NativeCertificate.snd, NativeCertificate.post, NativeCertificate.linear, Function.comp_apply]
    growth_poly [NativeCertificate.polyBounded_optionElim
      (polyBounded_length_of_hasPolySpace hcValM_sp) PolyBounded.self hcAddM.2]
  let cbM : Cert measurementStepBody eMIn eAcc :=
    ⟨cbM₀.time, cbM₀.space,
      cbM₀.computes.of_enc_eq fun inp => congrArg eAcc (measurementStepBody_eq inp)⟩
  let hprep := MeasurementFold.prepare_polyTime (encB := eAcc)
  let cPrep := NativeCertificate.ofPolyTime hprep
  have hcPrep : cPrep.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial hprep
  have hovM_pb : PolyBounded (fun inp => (eMIn inp).length)
      (fun inp => 2 * cProjWC.time inp + (eMIn inp).length +
        (evalMeasPayload (inp.1.2, inp.2.1)).elim (eMIn inp).length
          (fun b => cAddM.time (inp, b))) := by
    growth_poly [NativeCertificate.polyBounded_optionElim
      (polyBounded_length_of_hasPolySpace hcValM_sp) PolyBounded.self hcAddM.1]
  obtain ⟨cv, dv, hv_le⟩ := ((PolyBounded.self.add hcPrep.1).add
    (hovM_pb.comp hprep.polyBounded_length)).exists_le
  refine ⟨MeasurementFold.visitCertificate cbM, cv, dv,
    hasPolySpace_prod (by exact .self) (hasPolySpace_comp hcbM_sp hcPrep.2), fun st => ?_⟩
  have hov := hv_le st
  dsimp only [MeasurementFold.visitCertificate, cbM, cbM₀, cValM, cNoM, cPrep] at hov ⊢
  simp only [NativeCertificate.prod_time, NativeCertificate.comp_time, NativeCertificate.snd_time,
    NativeCertificate.linear_time, NativeCertificate.option_time, Function.comp_apply] at hov ⊢
  exact (le_of_eq (by ring)).trans (Nat.add_le_add_left hov _)

private theorem measFold_encJet_bound
    (co1 do1 : ℕ) (ho1_le : ∀ wc : List ℤ × MeasStepCtx,
      (encOption encJet (evalMeasPayload wc)).length ≤
        co1 * ((encPair (encList encIntBin) encMeasStepCtx wc).length + 1) ^ do1)
    (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) {j : ℕ}
    (hj : j ≤ MeasurementFold.count dc.2.2.1) :
    let L_wc := 2 * (dc.2.2.1.1 * (2 * ((dc.2.2.1.2).size + 1) + 1)) +
      2 * (encMeasStepCtx (mkMeasCtx dc)).length + 1
    let B_jet := jetFoldBound dc.2.jetOrder dc.2.precision
      (dc.2.2.1.1 * ((dc.2.2.1.2).size + 1) + 1) (co1 * (L_wc + 1) ^ do1)
    (encPair (encPair encUnary encNat) (encPair encMeasStepCtx encJet)
      (IndexFold.run (MeasurementFold.visit measurementStepBody) j
        (dc.2.2.1, (mkMeasCtx dc, zeroJet dc.2.jetOrder dc.2.precision))).2).length ≤
      2 * (encPair encUnary encNat dc.2.2.1).length +
        2 * (2 * (encMeasStepCtx (mkMeasCtx dc)).length + 2 * B_jet + 1) + 1 := by
  intro L_wc B_jet; rw [measFold_run_eq dc j]
  have hf_le := length_encJetRows_foldl_optAddJet_le (J := dc.2.jetOrder) (ℓ := dc.2.precision)
    (N := MeasurementFold.count dc.2.2.1) (M := 2 ^ (co1 * (L_wc + 1) ^ do1))
    (f := fun i => evalMeasPayload
      (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, mkMeasCtx dc))
    hj fun i _ y hy j' _ u' _ => by
      have hw_len := MeasurementFold.length_values_le dc.2.2.1.1 dc.2.2.1.2 i
      have hwc : (encPair (encList encIntBin) encMeasStepCtx
          (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 i, mkMeasCtx dc)).length ≤ L_wc := by
        enc_len [L_wc]
      have hopt : (encOption encJet (some y)).length ≤ co1 * (L_wc + 1) ^ do1 :=
        hy ▸ poly_apply_le ho1_le hwc
      simp only [encOption_some, List.length_cons] at hopt
      exact (Nat.size_le.mp ((CommonCountingAccum.size_natAbs_rowEntry_le_length_encJetRows y j'
        u').trans (by omega : (encJet y).length ≤ co1 * (L_wc + 1) ^ do1))).le
  have hN_sz : (MeasurementFold.count dc.2.2.1).size ≤
      dc.2.2.1.1 * ((dc.2.2.1.2).size + 1) + 1 := by
    rw [← Nat.size_eq_bits_len, ← encNat_apply]; exact MeasurementFold.length_count_le _ _
  have hjet := hf_le.trans (jetFoldl_bound_mono hN_sz)
  rw [length_encPair (enc₁ := encPair encUnary encNat), length_encPair (enc₁ := encMeasStepCtx)]
  dsimp only
  calc _ ≤ 2 * (encPair encUnary encNat dc.2.2.1).length + 1 +
      (2 * (encMeasStepCtx (mkMeasCtx dc)).length + 1 + B_jet) := by gcongr
    _ ≤ _ := by omega

private theorem exists_computableInO_signedMeasJet :
    ∃ P : SubsetPairFold.DecodedPair × SubsetStepCtx → ℕ,
      PolyBounded (fun dc => (encPair SubsetPairFold.encDecodedPair encSubsetStepCtx dc).length) P ∧
      ComputableInO evalSignedMeasJet
        (encPair SubsetPairFold.encDecodedPair encSubsetStepCtx) encJet
        (fun dc => ((2 * dc.2.2.1.2 + 1) ^ dc.2.2.1.1 + 1) *
          (dc.2.numGroups * (2 ^ maxGroupDim dc.2.numVars dc.2.numGroups dc.2.varGroups + 1) + 1) *
            P dc)
        P := by
  obtain ⟨P₁, hP₁_pb, hPay⟩ := exists_computableInO_measPayload
  let eWC := encPair (encList encIntBin) encMeasStepCtx
  let cPay : Cert evalMeasPayload eWC (encOption encJet) := ⟨_, P₁, hPay⟩
  let eAcc := encPair encMeasStepCtx encJet
  obtain ⟨cVisit, cv, dv, hcVisit_sp, hvisit_t⟩ := exists_measVisit_cert cPay hP₁_pb
  let eDC := encPair SubsetPairFold.encDecodedPair encSubsetStepCtx
  have hparDC : PolyT (fun dc : _ × SubsetStepCtx => dc.2.2.1) eDC (encPair encUnary encNat) := by
    unfold eDC encSubsetStepCtx; exact (snd _ _).snd'.fst'
  have hJ_dc : PolyT (fun dc : _ × SubsetStepCtx => dc.2.jetOrder) eDC encUnary := by
    unfold eDC encSubsetStepCtx; exact (snd _ _).snd'.snd'.fst'.fst'
  have hℓ_dc : PolyT (fun dc : _ × SubsetStepCtx => dc.2.precision) eDC encUnary := by
    unfold eDC encSubsetStepCtx; exact (snd _ _).snd'.snd'.fst'.snd'.fst'
  have hinitDC := hparDC.prod (computableInPolyTime_mkMeasCtx.prod
    (computableInPolyTime_zeroJet hJ_dc hℓ_dc))
  have hc_pb := ((fst encUnary encNat).comp hparDC).polyBounded
  have hDsz_pb : PolyBounded (fun dc => (eDC dc).length) (fun dc => (dc.2.2.1.2).size) :=
    (((snd encUnary encNat).comp hparDC).polyBounded_length).mono
      fun dc => by simp only [Function.comp_apply, encNat_apply, Nat.size_eq_bits_len]; exact le_rfl
  obtain ⟨cp1, dp1, hp1_le⟩ := hP₁_pb.exists_le
  obtain ⟨co1, do1, ho1_le⟩ := (polyBounded_length_of_hasPolySpace (c := cPay) hP₁_pb).exists_le
  have hmk_pb := computableInPolyTime_mkMeasCtx.polyBounded_length
  let L_wc (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) :=
    2 * (dc.2.2.1.1 * (2 * ((dc.2.2.1.2).size + 1) + 1)) +
      2 * (encMeasStepCtx (mkMeasCtx dc)).length + 1
  let P_pay (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) := cp1 * (L_wc dc + 1) ^ dp1
  let B_outer (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) :=
    2 * (encPair encUnary encNat dc.2.2.1).length +
      2 * (2 * (encMeasStepCtx (mkMeasCtx dc)).length +
        2 * jetFoldBound dc.2.jetOrder dc.2.precision
          (dc.2.2.1.1 * ((dc.2.2.1.2).size + 1) + 1) (co1 * (L_wc dc + 1) ^ do1) + 1) + 1
  have hBout_pb : PolyBounded (fun dc => (eDC dc).length) B_outer := by growth_poly
  let cCnt := MeasurementFold.clock.comp (.ofPolyTime hparDC)
  have hcCnt := NativeCertificate.comp_isPolynomial _ _ MeasurementFold.clock_isPolynomial
    (NativeCertificate.ofPolyTime_isPolynomial hparDC)
  let P_cb (dc : SubsetPairFold.DecodedPair × SubsetStepCtx) :=
    cv * (2 * (encNat (MeasurementFold.count dc.2.2.1)).length + 1 + B_outer dc + 1) ^ dv
  have hPcb_pb : PolyBounded (fun dc => (eDC dc).length) P_cb := by growth_poly
  obtain ⟨P_loop, hPloop_pb, hloop⟩ := computableInO_snd_indexFold cCnt (.ofPolyTime hinitDC)
    cVisit hcCnt (NativeCertificate.ofPolyTime_isPolynomial hinitDC) hcVisit_sp hBout_pb
    (fun dc _ hj => measFold_encJet_bound co1 do1 ho1_le dc hj)
    (fun dc =>
      (dc.2.numGroups * (2 ^ maxGroupDim dc.2.numVars dc.2.numGroups dc.2.varGroups + 1) + 1) *
        (2 * P_pay dc)) P_cb hPcb_pb fun dc j _ hst_len => by
      set st := IndexFold.run (MeasurementFold.visit measurementStepBody) j
        (dc.2.2.1, (mkMeasCtx dc, zeroJet dc.2.jetOrder dc.2.precision))
      have hw_len := MeasurementFold.length_values_le dc.2.2.1.1 dc.2.2.1.2 j
      have hwc_eq : (Cslib.Radix.measurementValues st.2.1.1 st.2.1.2 st.1, st.2.2.1) =
          (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 j, mkMeasCtx dc) := by
        rw [IndexFold.run_index, measFold_run_eq dc j]
      have hwc_len : (eWC (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 j,
          mkMeasCtx dc)).length ≤ L_wc dc := by enc_len [eWC, L_wc]
      have hpay_t : 2 * cPay.time (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 j,
          mkMeasCtx dc) ≤
          (dc.2.numGroups * (2 ^ maxGroupDim dc.2.numVars dc.2.numGroups dc.2.varGroups + 1) + 1) *
            (2 * P_pay dc) := by
        have hp : P₁ (Cslib.Radix.measurementValues dc.2.2.1.1 dc.2.2.1.2 j, mkMeasCtx dc) ≤
            P_pay dc := poly_apply_le hp1_le hwc_len
        exact (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hp)).trans_eq
          (Nat.mul_left_comm _ _ _)
      refine (hvisit_t st).trans (Nat.add_le_add (hwc_eq ▸ hpay_t) ?_)
      exact poly_apply_le (fun s => le_rfl) hst_len
  let cMeasJet := NativeCertificate.snd (NativeCertificate.snd
    (⟨_, _, hloop⟩ : Cert _ eDC (encPair (encPair encUnary encNat) eAcc)))
  have hsign : PolyT
      (fun p : (SubsetPairFold.DecodedPair × SubsetStepCtx) × JetRows =>
        if p.1.1.2.2 then smulJet p.1.2.jetOrder p.1.2.precision (-1) p.2 else p.2)
      (encPair eDC encJet) encJet := by
    have hp1 := fst eDC encJet; have hp2 := snd eDC encJet
    have hodd : PolyT (fun p : _ × JetRows => p.1.1.2.2) (encPair eDC encJet) encBool := by
      unfold eDC SubsetPairFold.encDecodedPair; exact hp1.fst'.snd'.snd'
    exact hodd.ite' (computableInPolyTime_smulJet (hJ_dc.comp hp1)
      (hℓ_dc.comp hp1) (const (-1)) hp2) hp2
  exact exists_computableInO_pairPost (eα := eDC)
    (A := fun dc => (2 * dc.2.2.1.2 + 1) ^ dc.2.2.1.1 + 1)
    (B := fun dc => dc.2.numGroups *
      (2 ^ maxGroupDim dc.2.numVars dc.2.numGroups dc.2.varGroups + 1) + 1)
    (p := fun dc => 2 * P_pay dc) (q := P_loop)
    cMeasJet.computes hPloop_pb (by growth_poly) hPloop_pb
    (fun _ => Nat.succ_pos _) (fun _ => Nat.succ_pos _) hsign

private theorem length_unrankSubsetPair_le (n q i : ℕ) :
    (SubsetPairFold.encDecodedPair (SubsetPairFold.unrankSubsetPair n q i)).length ≤
      6 * n + 7 := by
  unfold SubsetPairFold.encDecodedPair
  enc_len [SubsetPairFold.length_fst_unrankSubsetPair, SubsetPairFold.length_snd_unrankSubsetPair]

private theorem subsetPairFold_runPrefix_eq (qs : ℕ × SubsetStepCtx) (j : ℕ) :
    (SubsetPairFold.runPrefix subsetPairStepBody qs.2.numVars qs.1 j
      (qs.2, zeroJet qs.2.jetOrder qs.2.precision)).2.2 =
    (qs.2, (List.range j).foldl (fun acc i =>
      addJet qs.2.jetOrder qs.2.precision acc
        (evalSignedMeasJet (SubsetPairFold.unrankSubsetPair qs.2.numVars qs.1 i, qs.2)))
      (zeroJet qs.2.jetOrder qs.2.precision)) := by
  rw [SubsetPairFold.runPrefix_acc]; simp only [subsetPairStepBody_eq]
  exact List.foldl_keep_fst (fun (s : SubsetStepCtx) (acc : JetRows) (i : ℕ) =>
    addJet s.jetOrder s.precision acc
      (evalSignedMeasJet (SubsetPairFold.unrankSubsetPair qs.2.numVars qs.1 i, s)))
    qs.2 (List.range j) (zeroJet qs.2.jetOrder qs.2.precision)

private theorem exists_subsetPairStep_cert
    (cSignM : Cert evalSignedMeasJet
      (encPair SubsetPairFold.encDecodedPair encSubsetStepCtx) encJet)
    (hcSignM_sp : HasPolySpace cSignM) :
    let eSubAcc := encPair encSubsetStepCtx encJet
    let eSubIn := encPair SubsetPairFold.encDecodedPair eSubAcc
    ∃ (cbSub : Cert subsetPairStepBody eSubIn eSubAcc) (co do_ cs ds : ℕ),
      (∀ inp, cbSub.time inp ≤
        cSignM.time (inp.1, inp.2.1) + co * ((eSubIn inp).length + 1) ^ do_) ∧
      ∀ inp, cbSub.space inp ≤ cs * ((eSubIn inp).length + 1) ^ ds := by
  let eDC := encPair SubsetPairFold.encDecodedPair encSubsetStepCtx
  let eSubAcc := encPair encSubsetStepCtx encJet
  let eSubIn := encPair SubsetPairFold.encDecodedPair eSubAcc
  have hprojDC : PolyT
      (fun inp : SubsetPairFold.DecodedPair × (SubsetStepCtx × JetRows) => (inp.1, inp.2.1))
      eSubIn eDC := (fst _ eSubAcc).prod (snd _ eSubAcc).fst'
  have haddSub : PolyT
      (fun q : (SubsetPairFold.DecodedPair × (SubsetStepCtx × JetRows)) × JetRows =>
        (q.1.2.1, addJet q.1.2.1.jetOrder q.1.2.1.precision q.1.2.2 q.2))
      (encPair eSubIn encJet) eSubAcc :=
    computableInPolyTime_ctxAddJet (J := SubsetStepCtx.jetOrder) (ℓ := SubsetStepCtx.precision)
      (by unfold encSubsetStepCtx; exact (snd _ _).snd'.fst'.fst')
      (by unfold encSubsetStepCtx; exact (snd _ _).snd'.fst'.snd'.fst')
  obtain ⟨cProjDC, hcProjDC⟩ := NativeCertificate.exists_polynomial hprojDC
  obtain ⟨cAddSub, hcAddSub⟩ := NativeCertificate.exists_polynomial haddSub
  let cIdSub := NativeCertificate.linear (ei := eSubIn) (ComputableInO.of_eq fun _ => rfl)
  let cbSub₀ := cAddSub.comp (cIdSub.prod (cSignM.comp cProjDC))
  have hspSubP : HasPolySpace (cIdSub.prod (cSignM.comp cProjDC)) :=
    hasPolySpace_prod .self (hasPolySpace_comp hcSignM_sp hcProjDC.2)
  obtain ⟨co, do_, ho_le⟩ := ((PolyBounded.self.add hcProjDC.1).add
    (hcAddSub.1.comp (polyBounded_length_of_hasPolySpace hspSubP))).exists_le
  obtain ⟨cs, ds, hs_le⟩ := (hasPolySpace_comp hcAddSub.2 hspSubP).exists_le
  refine ⟨⟨cbSub₀.time, cbSub₀.space,
    cbSub₀.computes.of_enc_eq fun inp => congrArg eSubAcc (subsetPairStepBody_eq inp)⟩,
    co, do_, cs, ds, fun inp => ?_, hs_le⟩
  have hov := ho_le inp
  simp only [cbSub₀, cIdSub, eSubIn, eSubAcc, NativeCertificate.comp_time,
    NativeCertificate.prod_time, NativeCertificate.linear_time, Function.comp_apply] at hov ⊢
  omega

private theorem subsetPairFold_encJet_bound (qs : ℕ × SubsetStepCtx) {M j : ℕ}
    (hj : j ≤ SubsetPairFold.subsetPairCount qs.2.numVars qs.1)
    (hrow : ∀ i < SubsetPairFold.subsetPairCount qs.2.numVars qs.1, ∀ j' u',
      (rowEntry (evalSignedMeasJet (SubsetPairFold.unrankSubsetPair qs.2.numVars qs.1 i,
        qs.2)) j' u').natAbs ≤ 2 ^ M) :
    (encPair encSubsetStepCtx encJet (SubsetPairFold.runPrefix subsetPairStepBody
      qs.2.numVars qs.1 j (qs.2, zeroJet qs.2.jetOrder qs.2.precision)).2.2).length ≤
      2 * (encSubsetStepCtx qs.2).length +
        2 * jetFoldBound qs.2.jetOrder qs.2.precision (2 * qs.2.numVars + 1) M + 1 := by
  rw [subsetPairFold_runPrefix_eq qs j]
  have hf_le := length_encJetRows_foldl_optAddJet_le (J := qs.2.jetOrder) (ℓ := qs.2.precision)
    (N := SubsetPairFold.subsetPairCount qs.2.numVars qs.1) (M := 2 ^ M)
    (f := fun i =>
      some (evalSignedMeasJet (SubsetPairFold.unrankSubsetPair qs.2.numVars qs.1 i, qs.2)))
    hj fun i hi y hy j' _ u' _ => by cases hy; exact hrow i (hi.trans_le hj) j' u'
  have hN_sz : (SubsetPairFold.subsetPairCount qs.2.numVars qs.1).size ≤ 2 * qs.2.numVars + 1 := by
    rw [← Nat.size_eq_bits_len, ← encNat_apply]
    exact SubsetPairFold.length_encNat_subsetPairCount_le _ _
  have hjet := hf_le.trans (jetFoldl_bound_mono hN_sz)
  simp only [Option.elim_some] at hjet
  rw [length_encPair (enc₁ := encSubsetStepCtx)]; dsimp only
  exact (Nat.add_le_add_left hjet _).trans (by omega)

private theorem exists_computableInO_nodeJet :
    ∃ P : ℕ × SubsetStepCtx → ℕ,
      PolyBounded (fun qs => (encPair encUnary encSubsetStepCtx qs).length) P ∧
      ComputableInO
        (fun qs : ℕ × SubsetStepCtx =>
          (SubsetPairFold.run subsetPairStepBody qs.2.numVars qs.1
            (qs.2, zeroJet qs.2.jetOrder qs.2.precision)).2)
        (encPair encUnary encSubsetStepCtx) encJet
        (fun qs => (SubsetPairFold.subsetPairCount qs.2.numVars qs.1 + 1) *
          ((2 * qs.2.2.1.2 + 1) ^ qs.2.2.1.1 + 1) *
          (qs.2.numGroups * (2 ^ maxGroupDim qs.2.numVars qs.2.numGroups qs.2.varGroups + 1) + 1) *
            P qs)
        P := by
  obtain ⟨P₂, hP₂_pb, hSignM⟩ := exists_computableInO_signedMeasJet
  let eDC := encPair SubsetPairFold.encDecodedPair encSubsetStepCtx
  let cSignM : Cert evalSignedMeasJet eDC encJet := ⟨_, P₂, hSignM⟩
  obtain ⟨cbSub, co, do_, cs, ds, hcb_t, hcb_s⟩ := exists_subsetPairStep_cert cSignM hP₂_pb
  let eQS := encPair encUnary encSubsetStepCtx
  have hn_qs : PolyT (fun qs : ℕ × SubsetStepCtx => qs.2.numVars) eQS encUnary := by
    unfold eQS encSubsetStepCtx; exact (snd encUnary _).fst'.fst'
  have hq_qs : PolyT (fun qs : ℕ × SubsetStepCtx => qs.1) eQS encUnary :=
    fst encUnary encSubsetStepCtx
  have hJ_qs : PolyT (fun qs : ℕ × SubsetStepCtx => qs.2.jetOrder) eQS encUnary := by
    unfold eQS encSubsetStepCtx; exact (snd encUnary _).snd'.snd'.fst'.fst'
  have hℓ_qs : PolyT (fun qs : ℕ × SubsetStepCtx => qs.2.precision) eQS encUnary := by
    unfold eQS encSubsetStepCtx; exact (snd encUnary _).snd'.snd'.fst'.snd'.fst'
  have hinitQS := (snd encUnary encSubsetStepCtx).prod (computableInPolyTime_zeroJet hJ_qs hℓ_qs)
  have hctx_pb := (snd encUnary encSubsetStepCtx).polyBounded_length
  let L_dc (qs : ℕ × SubsetStepCtx) :=
    2 * (6 * qs.2.numVars + 7) + 2 * (encSubsetStepCtx qs.2).length + 1
  have hLdc_pb : PolyBounded (fun qs => (eQS qs).length) L_dc := by growth_poly
  obtain ⟨M_entry, hM_pb, hM_le⟩ := exists_natAbs_rowEntry_le_two_pow
    (polyBounded_length_of_hasPolySpace (c := cSignM) hP₂_pb) hLdc_pb
  obtain ⟨cp2, dp2, hp2_le⟩ := hP₂_pb.exists_le
  let P_sm (qs : ℕ × SubsetStepCtx) := cp2 * (L_dc qs + 1) ^ dp2
  let B_sub (qs : ℕ × SubsetStepCtx) := 2 * (encSubsetStepCtx qs.2).length +
    2 * jetFoldBound qs.2.jetOrder qs.2.precision (2 * qs.2.numVars + 1) (M_entry qs) + 1
  have hBsub_pb : PolyBounded (fun qs => (eQS qs).length) B_sub := by growth_poly
  have hdp_len (qs : ℕ × SubsetStepCtx) (i : ℕ) :
      (eDC (SubsetPairFold.unrankSubsetPair qs.2.numVars qs.1 i, qs.2)).length ≤ L_dc qs := by
    have hdp := length_unrankSubsetPair_le qs.2.numVars qs.1 i
    dsimp only [eDC, L_dc]; rw [length_encPair]; dsimp only; omega
  have hB (qs : ℕ × SubsetStepCtx) (j : ℕ)
      (hj : j ≤ SubsetPairFold.subsetPairCount qs.2.numVars qs.1) :
      (encPair encSubsetStepCtx encJet (SubsetPairFold.runPrefix subsetPairStepBody
        qs.2.numVars qs.1 j (qs.2, zeroJet qs.2.jetOrder qs.2.precision)).2.2).length ≤
        B_sub qs :=
    subsetPairFold_encJet_bound qs hj fun i _ j' u' => hM_le qs _ (hdp_len qs i) j' u'
  let L_sub (qs : ℕ × SubsetStepCtx) := 2 * (6 * qs.2.numVars + 7) + 2 * B_sub qs + 1
  let Q_sub (qs : ℕ × SubsetStepCtx) := cs * (L_sub qs + 1) ^ ds
  have hQsub_pb : PolyBounded (fun qs => (eQS qs).length) Q_sub := by growth_poly
  let Ov_sub (qs : ℕ × SubsetStepCtx) := co * (L_sub qs + 1) ^ do_
  obtain ⟨cn, hcn⟩ := NativeCertificate.exists_polynomial hn_qs
  obtain ⟨cq, hcq⟩ := NativeCertificate.exists_polynomial hq_qs
  obtain ⟨ci, hci⟩ := NativeCertificate.exists_polynomial hinitQS
  let R_sub (qs : ℕ × SubsetStepCtx) := ((2 * qs.2.2.1.2 + 1) ^ qs.2.2.1.1 + 1) *
    (qs.2.numGroups * (2 ^ maxGroupDim qs.2.numVars qs.2.numGroups qs.2.varGroups + 1) + 1) *
    P_sm qs + Ov_sub qs
  have hinp_len (qs : ℕ × SubsetStepCtx) (j : ℕ)
      (hj : j ≤ SubsetPairFold.subsetPairCount qs.2.numVars qs.1) :
      (encPair SubsetPairFold.encDecodedPair (encPair encSubsetStepCtx encJet)
        (SubsetPairFold.unrankSubsetPair qs.2.numVars qs.1 j,
          (SubsetPairFold.runPrefix subsetPairStepBody qs.2.numVars qs.1 j
            (qs.2, zeroJet qs.2.jetOrder qs.2.precision)).2.2)).length ≤ L_sub qs := by
    have hdp := length_unrankSubsetPair_le qs.2.numVars qs.1 j; have hb := hB qs j hj
    dsimp only [L_sub]; rw [length_encPair]; dsimp only; omega
  have hsp_run := SubsetPairFold.computableInO cn cq ci cbSub R_sub Q_sub B_sub
    (fun qs j hj => by
      have hfst : (SubsetPairFold.runPrefix subsetPairStepBody qs.2.numVars qs.1 j
          (qs.2, zeroJet qs.2.jetOrder qs.2.precision)).2.2.1 = qs.2 := by
        rw [subsetPairFold_runPrefix_eq qs j]
      have hsm_p := poly_apply_le hp2_le (hdp_len qs j)
      refine (hcb_t _).trans
        (Nat.add_le_add ?_ (poly_apply_le (fun _ => le_rfl) (hinp_len qs j hj)))
      dsimp only [cSignM, SubsetPairFold.LoopState.payload]; rw [hfst]
      exact Nat.mul_le_mul_left _ hsm_p)
    (fun qs j hj => (hcb_s _).trans (poly_apply_le (fun _ => le_rfl) (hinp_len qs j hj))) hB
  have hS_pb :=
    SubsetPairFold.polyBounded_space_of_polyBounded cn cq ci hcn hcq hci hBsub_pb hQsub_pb
  let cSubRun : Cert _ eQS (encPair encSubsetStepCtx encJet) := ⟨_, _, hsp_run⟩
  let hd_ov (qs : ℕ × SubsetStepCtx) := SubsetPairFold.decodeOverhead (qs.2.numVars + qs.1)
  have hhd_pb : PolyBounded (fun qs => (eQS qs).length) hd_ov := hS_pb.mono fun qs => by
    dsimp only [hd_ov]; omega
  let P_out (qs : ℕ × SubsetStepCtx) := P_sm qs + Ov_sub qs + hd_ov qs + B_sub qs +
    ((eQS qs).length + cn.time qs + cq.time qs + ci.time qs + hd_ov qs) +
    (NativeCertificate.snd cSubRun).space qs
  refine ⟨P_out,
    by growth_poly [hS_pb],
    (NativeCertificate.snd cSubRun).computes.mono_le (fun qs => ?_) fun _ => Nat.le_add_left _ _⟩
  clear_value L_dc P_sm B_sub L_sub Q_sub Ov_sub
  set S_cnt := SubsetPairFold.subsetPairCount qs.2.numVars qs.1 + 1
  set M_cnt := (2 * qs.2.2.1.2 + 1) ^ qs.2.2.1.1 + 1
  set G_cnt := qs.2.numGroups * (2 ^ maxGroupDim qs.2.numVars qs.2.numGroups qs.2.varGroups + 1) + 1
  have hstep := mul_inner_add_absorb (A := S_cnt) (B := M_cnt * G_cnt)
    (p := P_sm qs) (q := hd_ov qs + B_sub qs + Ov_sub qs)
    (ov := (eQS qs).length + cn.time qs + cq.time qs + ci.time qs + hd_ov qs)
    (r := P_out qs) (Nat.succ_pos _) (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
    (by dsimp only [P_out]; omega)
  dsimp only [NativeCertificate.snd_time, cSubRun, R_sub, hd_ov] at hstep ⊢
  exact (le_of_eq (by dsimp only [S_cnt, M_cnt, G_cnt]; ring)).trans
    (hstep.trans_eq (by dsimp only [S_cnt, M_cnt, G_cnt]; ring))

private def branchQ_u (inp : BranchEvalInput) : ℕ := min inp.numVars inp.numNodes
private def branchR_u (inp : BranchEvalInput) : ℕ := min inp.numVars inp.rowBound
private def branchr_u (inp : BranchEvalInput) : ℕ := min inp.numVars inp.numGroups
private def branchA₀_u (inp : BranchEvalInput) : ℕ := min (inp.numVars + 1) inp.intervalStart
private def branchD_cap (inp : BranchEvalInput) : ℕ :=
  min inp.numVars (branchr_u inp ^ (2 * branchQ_u inp))
private def branchTruncQ (inp : BranchEvalInput) : ℕ :=
  (inp.maxDegree * (branchR_u inp - 1)) * (inp.equations.length + 2 * inp.numVars) /
    max 1 (branchQ_u inp)
private def branchAugScopes (inp : BranchEvalInput) : List (List ℕ) :=
  withNeutralScopesList (inp.equations.map equationVars) inp.numVars

private theorem computableInPolyTime_branchClamped :
    PolyT BranchEvalInput.numVars encBranchEvalInput encUnary ∧
    PolyT BranchEvalInput.maxDegree encBranchEvalInput encUnary ∧
    PolyT BranchEvalInput.equations encBranchEvalInput encSparseSystem ∧
    PolyT branchQ_u encBranchEvalInput encUnary ∧
    PolyT branchR_u encBranchEvalInput encUnary ∧
    PolyT branchr_u encBranchEvalInput encUnary ∧
    PolyT branchA₀_u encBranchEvalInput encUnary ∧
    PolyT branchD_cap encBranchEvalInput encUnary ∧
    PolyT branchTruncQ encBranchEvalInput encUnary ∧
    PolyT branchAugScopes encBranchEvalInput (encList (encList encNat)) := by
  have hn' := BranchEvalInput.computableInPolyTime_numVars
  have hk' := BranchEvalInput.computableInPolyTime_maxDegree
  have heqs := BranchEvalInput.computableInPolyTime_equations
  have hr := BranchEvalInput.computableInPolyTime_numGroups
  have hQ := BranchEvalInput.computableInPolyTime_numNodes
  have hR := BranchEvalInput.computableInPolyTime_rowBound
  have hA₀ := BranchEvalInput.computableInPolyTime_intervalStart
  have hQu : PolyT branchQ_u encBranchEvalInput encUnary := binary_min_unary' hn' hQ
  have hRu : PolyT branchR_u encBranchEvalInput encUnary := binary_min_unary' hn' hR
  have hru : PolyT branchr_u encBranchEvalInput encUnary := binary_min_unary' hn' hr
  have hA₀u : PolyT branchA₀_u encBranchEvalInput encUnary :=
    binary_min_unary' (unary_add.comp (hn'.prod (const 1))) hA₀
  have hpow : PolyT (fun inp : BranchEvalInput => branchr_u inp ^ (2 * branchQ_u inp))
      encBranchEvalInput encNat :=
    (binary_pow.comp
      ((unary_to_binary.comp hru).prod (unary_add.comp (hQu.prod hQu)))).of_enc_eq
      fun inp => congrArg encNat (congrArg (branchr_u inp ^ ·)
        (by dsimp only [Function.comp_apply]; omega))
  have hDcap : PolyT branchD_cap encBranchEvalInput encUnary := binary_min_unary' hn' hpow
  have hnum := unary_mul.comp
    ((unary_mul.comp (hk'.prod (unary_sub.comp (hRu.prod (const 1))))).prod
    (unary_add.comp (((length_list (encList (encList encNat))).comp heqs).prod
      (unary_add.comp (hn'.prod hn')))))
  have hdiv := binary_div.comp ((unary_to_binary.comp hnum).prod
    (unary_to_binary.comp (unary_max' (const 1) hQu)))
  have hq : PolyT branchTruncQ encBranchEvalInput encUnary := by
    refine (binary_min_unary' hnum hdiv).of_enc_eq fun inp => congrArg encUnary ?_
    dsimp only [Function.comp_apply, branchTruncQ]
    rw [show inp.numVars + inp.numVars = 2 * inp.numVars by omega]
    exact (Nat.min_eq_right (Nat.div_le_self _ _)).symm
  exact ⟨hn', hk', heqs, hQu, hRu, hru, hA₀u, hDcap, hq,
    computableInPolyTime_withNeutralScopesListWithInput
      (bi_mapWithId (computableInPolyTime_equationVars.comp
        (snd encBranchEvalInput (encList (encList encNat))))
        heqs) hn'⟩

private def prepScheduleParams (inp : BranchEvalInput) : BalancedSchedules.ScheduleParams :=
  let aug := branchAugScopes inp
  ((inp.numVars, aug.length, branchQ_u inp), (branchr_u inp, inp.factorIncidence + inp.factorWidth),
    scopeIncidencesList inp.numVars aug)

private def mkDesignFromScheds (p : BranchEvalInput × (List (List ℕ) × List (List ℕ))) :
    BranchEvalInput × ReplacementDesignData :=
  (p.1, buildReplacementDesignData p.1.1.1 (branchD_cap p.1) (branchQ_u p.1) (branchr_u p.1)
    (branchA₀_u p.1) (branchR_u p.1) (branchAugScopes p.1) p.2.1 p.2.2)

private def mkDesignPair (inp : BranchEvalInput) : BranchEvalInput × ReplacementDesignData :=
  let p := prepScheduleParams inp
  mkDesignFromScheds (inp,
    BalancedSchedules.constructBalancedSchedules p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2)

private theorem exists_computableInO_mkDesignPair :
    ∃ P : BranchEvalInput → ℕ, PolyBounded (fun inp => (encBranchEvalInput inp).length) P ∧
      ComputableInO mkDesignPair encBranchEvalInput
        (encPair encBranchEvalInput encReplacementDesignData)
        (fun inp => (branchr_u inp ^ branchQ_u inp + 1) * P inp) P := by
  obtain ⟨hn', _, _, hQu, hRu, hru, hA₀u, hDcap, _, haug⟩ := computableInPolyTime_branchClamped
  have hprep : PolyT prepScheduleParams encBranchEvalInput
      BalancedSchedules.encScheduleParams := by
    unfold BalancedSchedules.encScheduleParams prepScheduleParams
    exact (hn'.prod (((length_list (encList encNat)).comp haug).prod hQu)).prod
      (((unary_to_binary.comp hru).prod
        (binary_add' BranchEvalInput.computableInPolyTime_factorIncidence
          BranchEvalInput.computableInPolyTime_factorWidth)).prod
        (computableInPolyTime_scopeIncidencesList hn' haug))
  let eSchOut := encPair (encList (encList encNat)) (encList (encList encNat))
  have hbuild : PolyT mkDesignFromScheds (encPair encBranchEvalInput eSchOut)
      (encPair encBranchEvalInput encReplacementDesignData) := by
    have hp1 : PolyT Prod.fst (encPair encBranchEvalInput eSchOut) encBranchEvalInput :=
      fst encBranchEvalInput eSchOut
    have hp2' := snd encBranchEvalInput eSchOut
    exact hp1.prod (computableInPolyTime_buildReplacementDesignData
      (hn'.comp hp1) (hDcap.comp hp1) (hQu.comp hp1) (hru.comp hp1) (hA₀u.comp hp1)
      (hRu.comp hp1) (haug.comp hp1) hp2'.fst' hp2'.snd')
  let cSched := BalancedSchedules.constructBalancedSchedulesCertificate
  obtain ⟨poly, hpoly, _, hB⟩ := BalancedSchedules.constructBalancedSchedulesCertificate_bounds
  obtain ⟨cPrep, hcPrep⟩ := NativeCertificate.exists_polynomial hprep
  have hcS := hasPolySpace_comp ((PolyBounded.of_polynomiallyBounded _ hpoly).mono
    fun p => (hB p).2) hcPrep.2
  have hpoly_pb : PolyBounded (fun inp => (encBranchEvalInput inp).length)
      (fun inp => poly (BalancedSchedules.encScheduleParams (prepScheduleParams inp)).length) :=
    (PolyBounded.of_polynomiallyBounded _ hpoly).comp hprep.polyBounded_length
  let cMid := cSched.comp cPrep
  have hmid : ComputableInO (fun inp => let p := prepScheduleParams inp
      BalancedSchedules.constructBalancedSchedules p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2 p.2.2)
      encBranchEvalInput eSchOut (fun inp => (branchr_u inp ^ branchQ_u inp + 1) *
        (1 * poly (BalancedSchedules.encScheduleParams (prepScheduleParams inp)).length +
          cPrep.time inp)) cMid.space :=
    cMid.computes.mono_le (fun inp => by
      have h1 := (hB (prepScheduleParams inp)).1
      have h2 := Nat.le_mul_of_pos_left (cPrep.time inp)
        (Nat.succ_pos (branchr_u inp ^ branchQ_u inp))
      rw [one_mul, Nat.mul_add]
      exact (Nat.add_comm _ _).le.trans (Nat.add_le_add h1 h2))
      fun _ => le_rfl
  obtain ⟨P, hP, hcomp⟩ := exists_computableInO_pairPost hmid hcS hpoly_pb hcPrep.1
    (fun _ => Nat.succ_pos _) (fun _ => le_rfl) hbuild
  exact ⟨P, hP, (hcomp.of_enc_eq fun _ => rfl).mono_le
    (fun _ => Nat.mul_le_mul_right _ (mul_one _).le) fun _ => le_rfl⟩

private def mkNodeSubIn (p : ((BranchEvalInput × ReplacementDesignData) ×
    List (List (List (List ℤ)))) × ℕ) : ℕ × SubsetStepCtx :=
  let inp := p.1.1.1; let data := p.1.1.2; let eqRowTables := p.1.2; let t := p.2
  let n' := inp.numVars; let k' := inp.maxDegree; let eqs' := inp.equations
  let r_u := branchr_u inp; let D_cap := branchD_cap inp; let q := branchTruncQ inp
  let m_rows := data.measurementMatrix.length
  let c_meas := min (4 * (n' + 1) * (eqs'.length * n' + n' + 1)) (r_u * m_rows)
  let grpEqLists := (List.range r_u).map fun g =>
    groupEquationsAt eqs' data.factorGroups eqRowTables t g
  (q, ((n', r_u, m_rows), (c_meas, D_cap), (q + 1, n' + 1, k'), ((t : ℤ) + 1, data.denom),
    (data.varGroups.getD t [], data.groupMeasurementMatrices.getD t []), grpEqLists))

private def finalizeDesignStage
    (p : (BranchEvalInput × ReplacementDesignData) × List JetRows) : ℕ :=
  let inp := p.1.1; let data := p.1.2; let n' := inp.numVars; let ℓ := n' + 1
  let nodes : List ℤ := (List.range (branchQ_u inp)).map fun (t : ℕ) => ((t : ℤ) + 1)
  let Ω : ℤ := ((data.denom ^ inp.maxDegree) ^ (2 * ℓ - 1)) ^ inp.equations.length
  let recCount :=
    CommonCountingAccum.recoverOuterJetSumModPowTwo nodes (branchTruncQ inp + 1) ℓ Ω p.2
  min (2 ^ n') recCount.toNat

private def evalDesignStageCore (idPair : BranchEvalInput × ReplacementDesignData) : ℕ :=
  let eqRowTables := buildEqRowTables idPair.1.numVars idPair.1.equations idPair.2
  let nodeJets := (List.range (branchQ_u idPair.1)).map fun t =>
    let qs := mkNodeSubIn ((idPair, eqRowTables), t)
    (SubsetPairFold.run subsetPairStepBody qs.2.numVars qs.1
      (qs.2, zeroJet qs.2.jetOrder qs.2.precision)).2
  finalizeDesignStage (idPair, nodeJets)

private def evalDesignStage (idPair : BranchEvalInput × ReplacementDesignData) : ℕ :=
  if validDesignShape idPair.1.numVars (branchr_u idPair.1) idPair.1.equations.length idPair.2 then
    evalDesignStageCore idPair
  else 0

private def branchCMeas (inp : BranchEvalInput) (m_rows : ℕ) : ℕ :=
  min (4 * (inp.numVars + 1) * (inp.equations.length * inp.numVars + inp.numVars + 1))
    (branchr_u inp * m_rows)

private def designNodeFactor (idPair : BranchEvalInput × ReplacementDesignData) : ℕ :=
  let n' := idPair.1.numVars; let r_u := branchr_u idPair.1
  (SubsetPairFold.subsetPairCount n' (branchTruncQ idPair.1) + 1) *
    ((2 * branchD_cap idPair.1 + 1) ^ branchCMeas idPair.1 idPair.2.measurementMatrix.length + 1) *
    (r_u * (2 ^ maxAllGroupDim n' (branchQ_u idPair.1) r_u idPair.2.varGroups + 1) + 1)

private theorem computableInPolyTime_mkNodeSubIn :
    PolyT mkNodeSubIn
      (encPair (encPair (encPair encBranchEvalInput encReplacementDesignData)
        (encList (encList (encList (encList encIntBin))))) encUnary)
      (encPair encUnary encSubsetStepCtx) := by
  obtain ⟨hn', hk', heqs, _, _, hru, _, hDcap, hq, _⟩ := computableInPolyTime_branchClamped
  let eCtx := encPair (encPair encBranchEvalInput encReplacementDesignData)
    (encList (encList (encList (encList encIntBin))))
  have hc := fst eCtx encUnary; have ht := snd eCtx encUnary
  have hinp := hc.fst'.fst'; have hdat := hc.fst'.snd'; have htab := hc.snd'
  have hn_p := hn'.comp hinp; have hk_p := hk'.comp hinp; have heqs_p := heqs.comp hinp
  have hru_p := hru.comp hinp; have hq_p := hq.comp hinp
  have hm_rows :=
    (length_list (encList encIntBin)).comp (computableInPolyTime_measurementMatrix hdat)
  have hℓ_p := unary_add.comp (hn_p.prod (const 1))
  have hc_cap := unary_mul.comp ((unary_mul.comp ((const 4).prod hℓ_p)).prod
    (unary_add.comp ((unary_add.comp ((unary_mul.comp
      (((length_list (encList (encList encNat))).comp heqs_p).prod hn_p)).prod hn_p)).prod
      (const 1))))
  let eIn := encPair eCtx encUnary
  have hp0 := fst eIn encUnary
  let grpEqAtFn (x : ((BranchEvalInput × ReplacementDesignData) ×
      List (List (List (List ℤ)))) × ℕ) (g : ℕ) :=
    groupEquationsAt x.1.1.1.equations x.1.1.2.factorGroups x.1.2 x.2 g
  have hge : PolyT (fun q => grpEqAtFn q.1 q.2) (encPair eIn encUnary) (encList encGroupEqEntry) :=
    computableInPolyTime_groupEquationsAt (heqs_p.comp hp0)
      ((computableInPolyTime_factorGroups hdat).comp hp0)
      (htab.comp hp0) (ht.comp hp0) (snd eIn encUnary)
  have hgrpEqs := mapWithInput (range.comp hru_p) hge
  unfold mkNodeSubIn encSubsetStepCtx
  exact hq_p.prod (((hn_p.prod (hru_p.prod hm_rows)).prod
    (((unary_min' hc_cap (unary_mul' hru_p hm_rows)).prod
        (unary_to_binary.comp (hDcap.comp hinp))).prod
      (((unary_add.comp (hq_p.prod (const 1))).prod (hℓ_p.prod hk_p)).prod
        (((intBin_add' (intBin_natCast.comp (unary_to_binary.comp ht)) (const 1)).prod
            (computableInPolyTime_denom hdat)).prod
          ((((listGetD (encA := encList (encList encNat)) []).comp
              ((computableInPolyTime_varGroups hdat).prod ht)).prod
            ((listGetD (encA := encList (encList (encList encIntBin))) []).comp
              ((computableInPolyTime_groupMeasurementMatrices hdat).prod ht))).prod hgrpEqs))))))

private theorem computableInPolyTime_finalizeDesignStage :
    PolyT finalizeDesignStage
      (encPair (encPair encBranchEvalInput encReplacementDesignData) (encList encJet)) encNat := by
  obtain ⟨hn', hk', heqs, hQu, _, _, _, _, hq, _⟩ := computableInPolyTime_branchClamped
  let eID := encPair encBranchEvalInput encReplacementDesignData
  let eF := encPair eID (encList encJet)
  have hp1 := (fst eID (encList encJet)).fst'; have hdat := (fst eID (encList encJet)).snd'
  have hn_f := hn'.comp hp1; have hℓ_f := unary_add.comp (hn_f.prod (const 1))
  have h2ℓ_sub1 := unary_sub.comp ((unary_mul.comp ((const 2).prod hℓ_f)).prod (const 1))
  let hnodeFn (q : ((BranchEvalInput × ReplacementDesignData) × List JetRows)) (t : ℕ) : ℤ :=
    (t : ℤ) + 1
  have hnode_fn : PolyT (fun q => hnodeFn q.1 q.2) (encPair eF encUnary) encIntBin :=
    intBin_add' (intBin_natCast.comp (unary_to_binary.comp (snd eF encUnary))) (const 1)
  have hnodes := mapWithInput (range.comp (hQu.comp hp1)) hnode_fn
  have hΩ := intBin_pow' (intBin_pow' (intBin_pow'
    (computableInPolyTime_denom hdat) (hk'.comp hp1)) h2ℓ_sub1)
    ((length_list (encList (encList encNat))).comp (heqs.comp hp1))
  have hrec := intBin_toNat.comp
    (CommonCountingAccum.computableInPolyTime_recoverOuterJetSumModPowTwo
    hnodes (unary_add.comp ((hq.comp hp1).prod (const 1))) hℓ_f hΩ (snd eID (encList encJet)))
  have h2pow := binary_two_pow.comp hn_f
  refine ((binary_le' h2pow hrec).ite' h2pow hrec).of_enc_eq fun p => congrArg encNat ?_
  simp only [finalizeDesignStage, hnodeFn, Nat.min_def, decide_eq_true_eq, Function.comp_apply]

private theorem exists_computableInO_evalDesignStage :
    ∃ P : BranchEvalInput × ReplacementDesignData → ℕ,
      PolyBounded
        (fun idPair => (encPair encBranchEvalInput encReplacementDesignData idPair).length) P ∧
      ComputableInO evalDesignStage (encPair encBranchEvalInput encReplacementDesignData) encNat
        (fun idPair => (branchQ_u idPair.1 + 1) * designNodeFactor idPair * P idPair) P := by
  obtain ⟨hn', _, heqs, hQu, _, hru, _, _, _, _⟩ := computableInPolyTime_branchClamped
  let eID := encPair encBranchEvalInput encReplacementDesignData
  let eTabs := encList (encList (encList (encList encIntBin)))
  let eCtx := encPair eID eTabs
  have hid_inp := fst encBranchEvalInput encReplacementDesignData
  have hid_data := snd encBranchEvalInput encReplacementDesignData
  have hctx_build : PolyT (fun p : BranchEvalInput × ReplacementDesignData =>
      (p, buildEqRowTables p.1.numVars p.1.equations p.2)) eID eCtx :=
    id'.prod (computableInPolyTime_buildEqRowTables (hn'.comp hid_inp) (heqs.comp hid_inp) hid_data)
  obtain ⟨P_nj, hPnj_pb, hNJ⟩ := exists_computableInO_nodeJet
  let cNJ : Cert _ (encPair encUnary encSubsetStepCtx) encJet := ⟨_, P_nj, hNJ⟩
  obtain ⟨cMkNode, hcMkNode⟩ := NativeCertificate.exists_polynomial computableInPolyTime_mkNodeSubIn
  have hcNodeOne_sp : HasPolySpace (cNJ.comp cMkNode) := hasPolySpace_comp hPnj_pb hcMkNode.2
  obtain ⟨cn1, dn1, hn1_le⟩ :=
    (hcMkNode.1.add (hPnj_pb.comp computableInPolyTime_mkNodeSubIn.polyBounded_length)).exists_le
  let Pn_iter (p : BranchEvalInput × ReplacementDesignData) : ℕ :=
    cn1 * (2 * (eCtx (p, buildEqRowTables p.1.numVars p.1.equations p.2)).length +
      2 * branchQ_u p.1 + 1 + 1) ^ dn1
  have hPn_pb : PolyBounded (fun p => (eID p).length) Pn_iter := by growth_poly
  obtain ⟨Pm_nodes, hPmn_pb, hcomp_nodes⟩ := exists_computableInO_mapRange (hQu.comp hid_inp)
    hctx_build hcNodeOne_sp (cNJ.comp cMkNode).computes
    (fun p => designNodeFactor p * Pn_iter p) fun p t ht => by
      have ht' : t < branchQ_u p.1 := ht
      have hlen : (encPair eCtx encUnary
          ((p, buildEqRowTables p.1.numVars p.1.equations p.2), t)).length ≤
          2 * (eCtx (p, buildEqRowTables p.1.numVars p.1.equations p.2)).length +
            2 * branchQ_u p.1 + 1 := by enc_len
      have hov := poly_apply_le hn1_le hlen
      have hpow_le := Nat.pow_le_pow_right Nat.zero_lt_two (maxGroupDim_le_maxAllGroupDim
        (n' := p.1.numVars) (r_u := branchr_u p.1) (varGroups := p.2.varGroups) ht')
      have hK_pos : 1 ≤ designNodeFactor p :=
        Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)
      have hKt_le : _ ≤ designNodeFactor p := Nat.mul_le_mul_left _
        (Nat.succ_le_succ (Nat.mul_le_mul_left _ (Nat.succ_le_succ hpow_le)))
      exact ((Nat.add_comm _ _).le.trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ hKt_le) _)).trans
        ((absorb_step_add _ _ _ hK_pos).trans
          (Nat.mul_le_mul_left _ (by dsimp only [Pn_iter]; omega)))
  obtain ⟨P_core, hPcore_pb, hcore⟩ := exists_computableInO_pairPost (eα := eID)
    (A := fun p => branchQ_u p.1 + 1) (B := designNodeFactor) (p := Pn_iter) (q := Pm_nodes)
    hcomp_nodes hPmn_pb hPn_pb hPmn_pb (fun _ => Nat.succ_pos _)
    (fun _ => Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _))
    computableInPolyTime_finalizeDesignStage
  exact exists_computableInO_guardZero
    (computableInPolyTime_validDesignShape (hn'.comp hid_inp) (hru.comp hid_inp)
      ((length_list (encList (encList encNat))).comp (heqs.comp hid_inp)) hid_data)
    (fun _ => Nat.mul_pos (Nat.succ_pos _)
      (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)))
    hcore hPcore_pb

private theorem exists_boundedIncidenceBranch_cert :
    ∃ c : Cert evalBoundedIncidenceBranch encBranchEvalInput encNat,
      PolyBounded (fun x => (encBranchEvalInput x).length) c.space ∧
      ∃ P : BranchEvalInput → ℕ, PolyBounded (fun x => (encBranchEvalInput x).length) P ∧
        ∀ inp : BranchEvalInput,
          let n' := inp.numVars; let Q_u := branchQ_u inp; let r_u := branchr_u inp
          let D_cap := branchD_cap inp; let q := branchTruncQ inp
          let data := (mkDesignPair inp).2; let m_rows := data.measurementMatrix.length
          let c_meas := min (4 * (n' + 1) * (inp.equations.length * n' + n' + 1)) (r_u * m_rows)
          let d_max := maxAllGroupDim n' Q_u r_u data.varGroups
          c.time inp ≤ ((r_u ^ Q_u + 1) + (Q_u + 1) * (SubsetPairFold.subsetPairCount n' q + 1) *
            ((2 * D_cap + 1) ^ c_meas + 1) * (r_u * (2 ^ d_max + 1) + 1)) * P inp := by
  let eID := encPair encBranchEvalInput encReplacementDesignData
  obtain ⟨P_stg1, hPstg1_pb, hStg1⟩ := exists_computableInO_mkDesignPair
  obtain ⟨P_stg2, hPstg2_pb, hStg2⟩ := exists_computableInO_evalDesignStage
  let cStg1 : Cert mkDesignPair encBranchEvalInput eID := ⟨_, P_stg1, hStg1⟩
  let cStg2 : Cert evalDesignStage eID encNat := ⟨_, P_stg2, hStg2⟩
  let c12 := cStg2.comp cStg1
  let K (inp : BranchEvalInput) : ℕ :=
    (branchr_u inp ^ branchQ_u inp + 1) + (branchQ_u inp + 1) * designNodeFactor (mkDesignPair inp)
  let P12 (inp : BranchEvalInput) : ℕ := P_stg1 inp + P_stg2 (mkDesignPair inp) + c12.space inp
  have hP12_pb : PolyBounded (fun inp => (encBranchEvalInput inp).length) P12 := by
    have hsp1 : HasPolySpace cStg1 := hPstg1_pb
    have hsp2 : HasPolySpace cStg2 := hPstg2_pb
    have h2sp : HasPolySpace c12 := hasPolySpace_comp hsp2 hsp1
    growth_poly [hPstg2_pb.comp (polyBounded_length_of_hasPolySpace hsp1), h2sp]
  have hcomp12 : ComputableInO (fun inp => evalDesignStage (mkDesignPair inp)) encBranchEvalInput
      encNat (fun inp => K inp * P12 inp) P12 :=
    c12.computes.mono_le (fun inp => by
      change (branchr_u inp ^ branchQ_u inp + 1) * P_stg1 inp +
        (branchQ_u inp + 1) * designNodeFactor (mkDesignPair inp) * P_stg2 (mkDesignPair inp) ≤ _
      exact (Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
        (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))).trans
        (by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by dsimp only [P12]; omega)))
      fun _ => Nat.le_add_left _ _
  obtain ⟨P, hP_pb, hguard⟩ := exists_computableInO_guardZero
    computableInPolyTime_validBranchEvalParams
    (fun _ => Nat.add_pos_left (Nat.succ_pos _) _) hcomp12 hP12_pb
  have heval_eq : (fun inp => if validBranchEvalParams inp then evalDesignStage (mkDesignPair inp)
      else 0) = evalBoundedIncidenceBranch := by
    funext inp
    unfold evalBoundedIncidenceBranch evalDesignStage evalDesignStageCore mkDesignPair
      mkDesignFromScheds prepScheduleParams mkNodeSubIn finalizeDesignStage branchAugScopes
      branchD_cap branchTruncQ branchQ_u branchR_u branchr_u branchA₀_u
    dsimp only; cases validBranchEvalParams inp; · rfl
    · cases validDesignShape _ _ _ _ <;> rfl
  refine ⟨⟨_, P, hguard.of_enc_eq fun inp => congrArg encNat (congrFun heval_eq inp).symm⟩,
    hP_pb, P, hP_pb, fun inp => le_of_eq ?_⟩
  have hmk1 : (mkDesignPair inp).1 = inp := rfl
  dsimp only [K, designNodeFactor, branchCMeas]; rw [hmk1]
  simp only [Nat.mul_assoc, Nat.succ_eq_add_one]

end LoopCertificates

/-! ### 3. Public Branch Certificate, Polynomial Workspace, and Subexponential Runtime Bound -/

/-- **Proposition 5.3 native branch certificate**: uniform multi-tape Turing machine resource
certificate for `evalBoundedIncidenceBranch` on `encBranchEvalInput`
([OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§5.3–5.5, Proposition 5.3,
pp. 37–39). -/
public noncomputable def boundedIncidenceBranchCertificate :
    NativeCertificate evalBoundedIncidenceBranch encBranchEvalInput encNat :=
  exists_boundedIncidenceBranch_cert.choose

/-- **Global polynomial workspace bound**: `boundedIncidenceBranchCertificate.space` is
polynomially bounded in `(encBranchEvalInput x).length` across **all** raw `BranchEvalInput`
tuples `x` (including malformed or unfeasible inputs). -/
public theorem polyBounded_boundedIncidenceBranchCertificate_space :
    PolyBounded (fun x => (encBranchEvalInput x).length)
      boundedIncidenceBranchCertificate.space :=
  exists_boundedIncidenceBranch_cert.choose_spec.1

private theorem listMax_range_le {n bound : ℕ} {f : ℕ → ℕ} (h : ∀ i < n, f i ≤ bound) :
    (0 :: (List.range n).map f).max (List.cons_ne_nil _ _) ≤ bound := by
  refine (List.max_le_iff _).mpr ?_
  simp only [List.mem_cons, List.mem_map, List.mem_range, forall_eq_or_imp]
  exact ⟨Nat.zero_le _, by rintro _ ⟨i, hi, rfl⟩; exact h i hi⟩

/-- **Proposition 5.3 subexponential branch runtime bound**: for every degree bound `k_deg`,
polylogarithmic exponent `β`, and constant `C_inc`, above `N₀_br`, every feasible reduced branch
`(n', sys')` with `sysMaxDegree sys' ≤ k_deg`, `sys'.length ≤ C_inc * n'`, and neutral-augmented
factor incidence and scope width at most `C_inc * (Nat.clog 2 n') ^ β` runs in
`O^*(2^{O(interpolationScale n')})` native TM steps. -/
public theorem exists_boundedIncidenceBranchCertificate_time_bound
    (N₀_branch k_deg β C_inc : ℕ) :
    ∃ N₀_br C_br d_br A_br : ℕ,
      ∀ n' : ℕ, ∀ sys' : List (List (List ℕ)),
        checkBranchFeasible N₀_branch (n', sys') = true → N₀_br ≤ n' →
        sysMaxDegree sys' ≤ k_deg → sys'.length ≤ C_inc * n' →
        branchMaxFactorIncidence n' sys' ≤ C_inc * Nat.clog 2 n' ^ β →
        branchMaxFactorWidth n' sys' ≤ C_inc * Nat.clog 2 n' ^ β →
        (boundedIncidenceBranchCertificate.time (prepareBranchEvalInput (n', sys')) : ℝ) ≤
          (C_br : ℝ) * ((encPair encUnary encSparseSystem (n', sys')).length + 1 : ℝ) ^ d_br *
            (2 : ℝ) ^ ((A_br : ℝ) * interpolationScale n') := by
  obtain ⟨P, hP_pb, htime⟩ := exists_boundedIncidenceBranch_cert.choose_spec.2
  obtain ⟨C_p, d_p, hCp⟩ :=
    (hP_pb.comp computableInPolyTime_prepareBranchEvalInput.polyBounded_length).exists_le
  refine ⟨max 16384 (2 ^ C_inc), 64 * C_p, d_p + 3,
    65792 * (k_deg * (C_inc + 2) + 4) * (β + 4), ?_⟩
  exact parametric_branch_step_bound (N₀_branch := N₀_branch) (k_deg := k_deg) (β := β)
    (C_inc := C_inc) (C_p := C_p) (d_p := d_p)
    (T := fun ns => boundedIncidenceBranchCertificate.time (prepareBranchEvalInput ns))
    fun n' sys' hfeas _ => by
    intro β' r Q R q
    have hex := exists_refines_prepare_of_feasible hfeas
    dsimp only [prepareBranchEvalInput, ParameterCheck.computeScheduleParams] at hex
    obtain ⟨hQn, hRn, hrn, _, haux, _, D, href, hmeas_len, _⟩ := hex
    let inp := prepareBranchEvalInput (n', sys')
    let A₀ := ReplacementParams.intervalStart β' n'
    have hQu_eq : branchQ_u inp = Q := Nat.min_eq_right hQn
    have hRu_eq : branchR_u inp = R := Nat.min_eq_right hRn
    have hru_eq : branchr_u inp = r := Nat.min_eq_right hrn
    have hDcap_eq : branchD_cap inp = r ^ (2 * Q) := by
      simp only [branchD_cap, hru_eq, hQu_eq]; exact Nat.min_eq_right haux
    have hq_eq : branchTruncQ inp =
        (sysMaxDegree sys' * (R - 1)) * (sys'.length + 2 * n') / max 1 Q := by
      simp only [branchTruncQ, hRu_eq, hQu_eq]; rfl
    let data := (mkDesignPair inp).2; let m_rows := data.measurementMatrix.length
    let c_meas := min (4 * (n' + 1) * (sys'.length * n' + n' + 1)) (r * m_rows)
    let d_max := maxAllGroupDim n' Q r data.varGroups
    refine ⟨c_meas, d_max, ?_, ?_, ?_⟩
    · have hc_le : c_meas ≤ r * (D.h * #(measurementIndices Q r A₀ R)) :=
        (Nat.min_le_right _ _).trans (le_of_eq (congrArg (r * ·) hmeas_len))
      have hrat_r : (((r * (D.h * #(measurementIndices Q r A₀ R)) : ℕ) : ℚ) : ℝ) ≤
          ((2 * ReplacementParams.tauRat n' * (n' : ℚ) : ℚ) : ℝ) :=
        Rat.cast_le.mpr D.total_measurement_rows_le
      simp only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_ofNat,
        ReplacementParams.cast_tauRat] at hrat_r
      exact (Nat.cast_le.mpr hc_le).trans hrat_r
    · exact listMax_range_le fun t ht => listMax_range_le fun g hg =>
        (Nat.min_le_right _ _).trans (href.2.2.1 ⟨t, ht⟩ ⟨g, hg⟩).2.1
    · have ht := htime inp; have hp := hCp (n', sys')
      change boundedIncidenceBranchCertificate.time inp ≤ _
      dsimp only [boundedIncidenceBranchCertificate]; rw [hQu_eq, hru_eq, hDcap_eq, hq_eq] at ht
      exact ht.trans (Nat.mul_le_mul_left _ hp)

/-- **Instantiation of `BranchPolylogTimeBound`**: `boundedIncidenceBranchCertificate` satisfies
`Cslib.Complexity.BranchedSparseCNFCounter.BranchPolylogTimeBound` for every `N₀_branch`. -/
public theorem branchPolylogTimeBound_boundedIncidenceBranchCertificate (N₀_branch : ℕ) :
    Cslib.Complexity.BranchedSparseCNFCounter.BranchPolylogTimeBound N₀_branch
      boundedIncidenceBranchCertificate :=
  fun k_deg β C_inc => exists_boundedIncidenceBranchCertificate_time_bound N₀_branch k_deg β C_inc

end Cslib.Complexity.SubexponentialSAT.SparsePolyCounter
