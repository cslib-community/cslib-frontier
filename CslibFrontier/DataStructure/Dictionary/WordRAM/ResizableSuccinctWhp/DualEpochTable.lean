/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochProgs
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Overflow-Free `EpochParamTable` Builder and `clog`/`log` Helpers (`DualEpochTable`)

This module provides the `RealizesBounded .exact` (`¬ReadsWidth`) `Memory.Prog` routines that
compute and write the static parameter words (`FastEpochLayout.paramWord` slots `0..47` and
`61..62`, leaving `48..60` for `setSlotIoProg`) of a large-epoch 64-word `EpochParamTable`
`[pBase, pBase + 64)` at the end of the `log2Calc` phase—with **zero** `w`-bit overflow even when
`N = U = 2 ^ w - 1` (`11 ≤ w`):

* `clog_eq_of_log`, `clog_succ_eq_of_log`, `clog_add_two_eq_of_log`, `logLogFactor_eq_of_log`:
  exact `Nat.clog 2 N`, `Nat.clog 2 (N + 1)`, `Nat.clog 2 (N + 2)`, and `Dynamic.logLogFactor N`
  identities computed without ever forming `N + 1` or `N + 2` in a register.
* `packedWordsSafeProg` and `pairStreamWordsSafeProg`: `0`-cost overflow-free computations of
  `packedWords n k w` and `pairStreamWords n qb vb w`.
* `writeLargeParamTableProg`: writes slots `0..47` and `61..62` of `FastEpochLayout.paramWord`,
  leaving slots `48..60` ready for `setSlotIoProg`, and returning
  `(offPageDir, offPageTail, epochMetaWordsWhp c w N)`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM

private theorem cstate_write_eq (a v : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (Memory.write a v) =
      { mem := Function.update s.mem a v, frontier := s.frontier } := rfl

private theorem cstate_read_eq (a : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (Memory.read a) = s := rfl

private theorem cres_read_eq (a : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (Memory.read a) = s.mem a := rfl

private theorem mcost_read_eq (a : ℕ) (s : Memory.State) :
    memoryCost (Memory.read a) s = 1 := rfl

private theorem mcost_write_eq (a v : ℕ) (s : Memory.State) :
    memoryCost (Memory.write a v) s = 1 := rfl

/-! ## Section 1: Overflow-Free `Nat.clog 2` Identities from `Nat.log 2 N` -/

/-- Exact `Nat.clog 2 N` expressed from `k = Nat.log 2 N` using `p = 2 ^ k ≤ N`. -/
theorem clog_eq_of_log {N : ℕ} (hN : 0 < N) :
    Nat.clog 2 N = if N = 2 ^ Nat.log 2 N then Nat.log 2 N else Nat.log 2 N + 1 := by
  set k := Nat.log 2 N
  have hlo : 2 ^ k ≤ N := Nat.pow_log_le_self 2 hN.ne'
  have hhi : N < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two N
  by_cases heq : N = 2 ^ k
  · rw [ite_eq_left heq, heq]
    exact Nat.clog_pow 2 k Nat.one_lt_two
  · rw [ite_eq_right heq]
    have hlt : 2 ^ k < N := lt_of_le_of_ne hlo (Ne.symm heq)
    have hle1 : Nat.clog 2 N ≤ k + 1 := (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr hhi.le
    have hge1 : k < Nat.clog 2 N := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr hlt
    omega

/-- Exact `Nat.clog 2 (N + 1) = Nat.log 2 N + 1` for every `0 < N`. -/
theorem clog_succ_eq_of_log {N : ℕ} (hN : 0 < N) :
    Nat.clog 2 (N + 1) = Nat.log 2 N + 1 := by
  set k := Nat.log 2 N
  have hlo : 2 ^ k ≤ N := Nat.pow_log_le_self 2 hN.ne'
  have hhi : N < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two N
  have hle : Nat.clog 2 (N + 1) ≤ k + 1 :=
    (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr (by omega)
  have hge : k < Nat.clog 2 (N + 1) :=
    (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega)
  omega

/-- Overflow-free `Nat.clog 2 (N + 2)` from `k = Nat.log 2 N` and `p = 2 ^ k` (never computes
`N + 2` or `2 * p`, valid even at `N = 2 ^ w - 1`). -/
theorem clog_add_two_eq_of_log {N : ℕ} (hN : 0 < N) :
    let p := 2 ^ Nat.log 2 N
    Nat.clog 2 (N + 2) = if N - p = p - 1 then Nat.log 2 N + 2 else Nat.log 2 N + 1 := by
  dsimp only
  set k := Nat.log 2 N
  set p := 2 ^ k
  have hp_pos : 0 < p := by positivity
  have hlo : p ≤ N := Nat.pow_log_le_self 2 hN.ne'
  have hhi : N < 2 * p := by
    have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two N
    change N < 2 ^ (k + 1) at hlt
    rw [Nat.pow_succ] at hlt
    change N < p * 2 at hlt
    omega
  have hpow1 : 2 ^ (k + 1) = 2 * p := by rw [Nat.pow_succ]; ring
  have hpow2 : 2 ^ (k + 2) = 4 * p := by rw [Nat.pow_succ, Nat.pow_succ]; ring
  by_cases htop : N - p = p - 1
  · rw [ite_eq_left htop]
    have hN_eq : N = 2 * p - 1 := by omega
    have hle : Nat.clog 2 (N + 2) ≤ k + 2 :=
      (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr (by rw [hpow2]; omega)
    have hgt : k + 1 < Nat.clog 2 (N + 2) :=
      (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by rw [hpow1]; omega)
    omega
  · rw [ite_eq_right htop]
    have hle : Nat.clog 2 (N + 2) ≤ k + 1 :=
      (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr (by rw [hpow1]; omega)
    have hgt : k < Nat.clog 2 (N + 2) :=
      (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by change p < N + 2; omega)
    omega

/-- For every `4 ≤ N`, `Dynamic.logLogFactor N = Nat.log 2 (Nat.clog 2 N - 1) + 1`. -/
theorem logLogFactor_eq_of_log {N : ℕ} (hN : 4 ≤ N) :
    Dynamic.logLogFactor N = Nat.log 2 (Nat.clog 2 N - 1) + 1 := by
  unfold Dynamic.logLogFactor
  rw [max_eq_left hN]
  have hcl : 1 < Nat.clog 2 N := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega)
  exact clog_eq_log_pred_succ hcl

/-! ## Section 2: Overflow-Free `packedWordsSafeProg` and `pairStreamWordsSafeProg` -/

/-- `0`-memory-cost overflow-free computation of `packedWords n k wv` (avoids `n * k` overflow). -/
def packedWordsSafeProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((n, k), wv) =>
    let q := n / wv
    let r := n % wv
    let rk := r * k
    let rem := rk + wv - 1
    pure (q * k + rem / wv + 2)

theorem packedWordsSafeProg_spec (n k w : ℕ) (hw : 0 < w) (s : Memory.State) :
    (Memory.spec 0).clientState s (packedWordsSafeProg ((n, k), w)) = s ∧
    (Memory.spec 0).clientResult s (packedWordsSafeProg ((n, k), w)) = packedWords n k w ∧
    memoryCost (packedWordsSafeProg ((n, k), w)) s = 0 := by
  refine ⟨rfl, ?_, memoryCost_pure _ _⟩
  exact packedWordsSafe_eq hw

theorem validHistory_packedWordsSafeProg (w n k wv : ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (packedWordsSafeProg ((n, k), wv))) :=
  trivial

theorem realizesBounded_packedWordsSafe :
    RealizesBounded .exact packedWordsSafeProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((n, k), wv) _ =>
        11 ≤ w ∧ wv = w ∧ k ≤ 2 * w ∧ Fits w (packedWords n k w))
      (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨n, k⟩, wv⟩
    obtain ⟨hw11, hw_eq, hk, hfit⟩ := h
    subst hw_eq
    have hw_pos : 0 < wv := by omega
    have hpow := two_mul_sq_add_lt_pow hw11
    have hr_lt : n % wv < wv := Nat.mod_lt n hw_pos
    have hrk_le : n % wv * k ≤ 2 * wv * wv := by
      calc n % wv * k ≤ wv * (2 * wv) := Nat.mul_le_mul hr_lt.le hk
        _ = 2 * wv * wv := by ring
    have hsum_le : n / wv * k + (n % wv * k + wv - 1) / wv + 2 = packedWords n k wv :=
      packedWordsSafe_eq hw_pos
    dsimp only [Fits] at *
    try omega)

/-- `0`-memory-cost overflow-free computation of `pairStreamWords n qB vB w`. -/
def pairStreamWordsSafeProg : ((ℕ × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((n, qb), vb), wv) => packedWordsSafeProg ((n, qb + vb), wv)

theorem pairStreamWordsSafeProg_spec (n qb vb w : ℕ) (hw : 0 < w) (s : Memory.State) :
    (Memory.spec 0).clientState s (pairStreamWordsSafeProg (((n, qb), vb), w)) = s ∧
    (Memory.spec 0).clientResult s (pairStreamWordsSafeProg (((n, qb), vb), w)) =
      pairStreamWords n qb vb w ∧
    memoryCost (pairStreamWordsSafeProg (((n, qb), vb), w)) s = 0 :=
  packedWordsSafeProg_spec n (qb + vb) w hw s

theorem realizesBounded_pairStreamWordsSafe :
    RealizesBounded .exact pairStreamWordsSafeProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((n, qb), vb), wv) _ =>
        11 ≤ w ∧ wv = w ∧ qb ≤ w ∧ vb ≤ w ∧ Fits w (pairStreamWords n qb vb w))
      (fun _ _ => 0) := by
  have hp := realizesBounded_packedWordsSafe
  realize
  all_goals (
    rcases d with ⟨⟨⟨n, qb⟩, vb⟩, wv⟩
    obtain ⟨hw11, hw_eq, hqb, hvb, hfit⟩ := h
    subst hw_eq
    have hw_pos : 0 < wv := by omega
    have hpow := two_mul_sq_add_lt_pow hw11
    have h2w : qb + vb < 2 ^ wv := by
      have hww : 2 * wv ≤ 2 * wv * wv + wv := by
        calc 2 * wv = 2 * wv * 1 := (mul_one _).symm
          _ ≤ 2 * wv * wv := Nat.mul_le_mul_left _ (by omega)
          _ ≤ 2 * wv * wv + wv := Nat.le_add_right _ _
      omega
    have hr_lt : n % wv < wv := Nat.mod_lt n hw_pos
    have hrk_le : n % wv * (qb + vb) ≤ 2 * wv * wv := by
      calc n % wv * (qb + vb) ≤ wv * (2 * wv) := Nat.mul_le_mul hr_lt.le (by omega)
        _ = 2 * wv * wv := by ring
    have hsafe : n / wv * (qb + vb) + (n % wv * (qb + vb) + wv - 1) / wv + 2 =
        pairStreamWords n qb vb wv := packedWordsSafe_eq hw_pos
    dsimp only [Fits] at *
    omega)

/-! ## Section 3: Exact Arithmetic Helper Bounds for `writeLargeParamTableProg` -/

private theorem slabScale_pow_eq_shift (N k : ℕ) :
    slabScale N ^ k = 2 ^ (k * Dynamic.logLogFactor N) := by
  unfold slabScale
  rw [← Nat.pow_mul, Nat.mul_comm _ k]

private theorem scale12_mul_le_pow_bChar {c N : ℕ} (hth : whpThreshold c ≤ N) :
    32 * slabScale N ^ 12 ≤ 2 ^ bCharWhp N ∧
    qEpochWhp N ≤ 2 ^ bCharWhp N ∧
    2 ^ bCharWhp N ≤ N ∧
    slabScale N ≥ 8 := by
  have h320 : 320 * Dynamic.logLogFactor N ≤ bCharWhp N :=
    (Nat.mul_le_mul_right _ (le_codeExpWhp c)).trans (codeExpWhp_mul_ell_le_bCharWhp hth)
  have hell := Dynamic.one_le_logLogFactor N
  have hN_pos : 0 < N := (whpThreshold_pos c).trans_le hth
  have hbm := bMinWhp_le_log hth
  have hbmin := le_bMinWhp c
  have hN4 := four_le_of_whpThreshold_le hth
  have hbc_log : bCharWhp N ≤ Nat.log 2 N := by unfold bCharWhp; omega
  have hpow_le : 2 ^ bCharWhp N ≤ N :=
    (Nat.pow_le_pow_right (by decide) hbc_log).trans (Nat.pow_log_le_self 2 hN_pos.ne')
  have h32_le : 32 * slabScale N ^ 12 ≤ 2 ^ bCharWhp N := by
    rw [slabScale_pow_eq_shift]
    have h5 : (32 : ℕ) = 2 ^ 5 := by decide
    rw [h5, ← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hq_le : qEpochWhp N ≤ 2 ^ bCharWhp N := by
    unfold qEpochWhp
    rw [slabScale_pow_eq_shift]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hell3 : 3 ≤ Dynamic.logLogFactor N := by
    unfold Dynamic.logLogFactor
    rw [max_eq_left hN4]
    refine (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr ?_
    have h5 : 2 ^ 5 ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right (by decide) (by omega)
    have hpowN : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN_pos.ne'
    have hlt2 : 2 ^ 4 < N := by omega
    exact (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr hlt2
  have hL8 : 8 ≤ slabScale N := by
    unfold slabScale
    exact (by decide : 8 = 2 ^ 3) ▸ Nat.pow_le_pow_right (by decide) hell3
  exact ⟨h32_le, hq_le, hpow_le, hL8⟩

private theorem param_scalar_bounds {c U w N : ℕ} (hth : whpThreshold c ≤ N)
    (hNU : N ≤ U) (hU : Fits w U) :
    16 * numBucketsWhp N ≤ N ∧
    numBucketsWhp N * maxSlabsPerBktWhp N ≤ N ∧
    sMaxWhp c N ≤ N ∧
    cTabWhp c * bCharWhp N < 2 ^ w ∧
    4 * (cTabWhp c + 2) < w ∧
    11 ≤ w ∧
    18 * Dynamic.logLogFactor N < w ∧
    36 * Dynamic.logLogFactor N < w ∧
    160 * Dynamic.logLogFactor N < w ∧
    2 ≤ tMinWhp N ∧
    1 + 1 ≤ cTabWhp c + 1 := by
  have hpb := largeEpoch_param_bounds hth hNU hU
  have ⟨h32, hq, hpow_bc, hL8⟩ := scale12_mul_le_pow_bChar hth
  have hM_L12 := numBucketsWhp_mul_scale_pow12_le hth
  have h320 : 320 * Dynamic.logLogFactor N ≤ bCharWhp N :=
    (Nat.mul_le_mul_right _ (le_codeExpWhp c)).trans (codeExpWhp_mul_ell_le_bCharWhp hth)
  have hlog_w : Nat.log 2 N < w := hpb.2.2.1
  have hbc_w : bCharWhp N < w := hpb.2.2.2.1
  have hbm := bMinWhp_le_log hth
  have hbmin := le_bMinWhp c
  have hw11 : 11 ≤ w := by omega
  have hL12_16 : 16 ≤ slabScale N ^ 12 := by
    have h2 : 2 ≤ slabScale N := by omega
    calc 16 = 2 ^ 4 := by decide
      _ ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (by decide)
      _ ≤ slabScale N ^ 12 := Nat.pow_le_pow_left h2 12
  have h16M : 16 * numBucketsWhp N ≤ N :=
    calc 16 * numBucketsWhp N = numBucketsWhp N * 16 := by ring
      _ ≤ numBucketsWhp N * slabScale N ^ 12 := Nat.mul_le_mul_left _ hL12_16
      _ ≤ N := hM_L12
  have hMs : numBucketsWhp N * maxSlabsPerBktWhp N ≤ N := by
    unfold maxSlabsPerBktWhp
    have h4L : 4 * slabScale N ^ 10 ≤ slabScale N ^ 12 := by
      have hL2 : 4 ≤ slabScale N ^ 2 := by
        have : 8 ^ 2 ≤ slabScale N ^ 2 := Nat.pow_le_pow_left hL8 2
        omega
      calc 4 * slabScale N ^ 10 ≤ slabScale N ^ 2 * slabScale N ^ 10 :=
            Nat.mul_le_mul_right _ hL2
        _ = slabScale N ^ 12 := by rw [← Nat.pow_add]
    exact (Nat.mul_le_mul_left _ h4L).trans hM_L12
  have hc_lt : 4 * (cTabWhp c + 2) < w := by
    have hct := le_cTabWhp c
    have hqt := le_qTabWhp c
    have hce := codeExpWhp_mul_ell_le_bCharWhp hth
    have hell := Dynamic.one_le_logLogFactor N
    have hsq1 : 4 * (cTabWhp c + 2) ≤ 16 * (cTabWhp c + 1) ^ 2 * qTabWhp c := by
      have h1 : cTabWhp c + 2 ≤ 2 * (cTabWhp c + 1) := by omega
      have h2 : (cTabWhp c + 1) ≤ (cTabWhp c + 1) ^ 2 := by
        rw [sq]; exact Nat.le_mul_of_pos_right _ (by omega)
      have h3 : 4 * (cTabWhp c + 2) ≤ 16 * (cTabWhp c + 1) ^ 2 := by omega
      exact h3.trans (Nat.le_mul_of_pos_right _ (by omega))
    have hcb : 16 * (cTabWhp c + 1) ^ 2 * qTabWhp c ≤ codeExpWhp c := by
      rw [codeExpWhp_eq]; omega
    have hmul : codeExpWhp c ≤ codeExpWhp c * Dynamic.logLogFactor N :=
      Nat.le_mul_of_pos_right _ hell
    omega
  have hred_lt : cTabWhp c * bCharWhp N < 2 ^ w := by
    have hsq := two_mul_sq_add_lt_pow hw11
    have h1 : cTabWhp c ≤ w := by omega
    have h2 : bCharWhp N ≤ w := by omega
    have h3 : w * w ≤ 2 * w * w + w := by
      calc w * w = 1 * (w * w) := (one_mul _).symm
        _ ≤ 2 * (w * w) := Nat.mul_le_mul_right _ (by decide)
        _ = 2 * w * w := by ring
        _ ≤ 2 * w * w + w := Nat.le_add_right _ _
    exact (Nat.mul_le_mul h1 h2).trans_lt (h3.trans_lt hsq)
  have hsmax : sMaxWhp c N ≤ N := by
    unfold sMaxWhp
    have hce_le : cEff c + 4 ≤ cTabWhp c + 1 := by unfold cTabWhp; omega
    have hL_le : slabScale N ≤ qEpochWhp N := by
      unfold qEpochWhp; exact Nat.le_self_pow (by decide) _
    have hct_le : (cEff c + 4) * slabScale N ≤ 6 * maxTrieNodesWhp c N := by
      unfold maxTrieNodesWhp
      exact (Nat.mul_le_mul hce_le hL_le).trans (by
        have := Nat.le_add_right ((cTabWhp c + 1) * qEpochWhp N) 2
        omega)
    exact hct_le.trans hpb.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hell_pos := Dynamic.one_le_logLogFactor N
  have hcT := le_cTabWhp c
  refine ⟨h16M, hMs, hsmax, hred_lt, hc_lt, hw11, ?_, ?_, ?_, le_max_left 2 _, by omega⟩
  · omega
  · unfold bCharWhp at h320; omega
  · unfold bCharWhp at h320; omega

private theorem sublinear_word_fits_le {c w N : ℕ} (hth : whpThreshold c ≤ N) :
    32 + BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp N) (bWhp N) =
      offFpHash c w N ∧
    offFpHash c w N ≤ offBktMeta c w N ∧
    offBktMeta c w N ≤ offSlabDir c w N ∧
    offSlabDir c w N ≤ offTailDir c w N ∧
    offTailDir c w N ≤ offSlabOwner c w N ∧
    offSlabOwner c w N ≤ offTailOwner c w N ∧
    offTailOwner c w N ≤ offBTreeMeta c w N ∧
    offBTreeMeta c w N ≤ offBTreeKeys c w N ∧
    offBTreeKeys c w N ≤ offBTreeVals c w N ∧
    offBTreeVals c w N ≤ offTrieChild c w N 0 ∧
    offTrieChild c w N 0 ≤ offTrieChild c w N 1 ∧
    offTrieChild c w N 1 ≤ offTrieNode c w N 0 ∧
    offTrieNode c w N 0 ≤ offTrieNode c w N 1 ∧
    offTrieNode c w N 1 ≤ offTrieItem c w N 0 ∧
    offTrieItem c w N 0 ≤ offTrieItem c w N 1 ∧
    offTrieItem c w N 1 ≤ offPageDir c w N ∧
    offPageDir c w N ≤ offPageTail c w N ∧
    offPageTail c w N ≤ epochMetaWordsWhp c w N := by
  have heq := offEpochEnd_eq_epochMetaWordsWhp (w := w) hth
  rw [← heq]
  unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
    offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
    offBktMeta offFpHash offBktHash
  repeat' constructor <;> omega

/-! ## Section 4: Modular `writeLargeParamTableProg` (`RealizesBounded .exact`, `¬ReadsWidth`) -/

/-- Static header predicate guaranteeing `[base, base + 10)` holds the universe and `c` constants
initialized by `initCodeWhp`. -/
@[expose] def RootStaticHeader (c U V w base : ℕ) (mem : ℕ → ℕ) : Prop :=
  mem (base + hdrU1) = U - 1 ∧
  mem (base + hdrV1) = V - 1 ∧
  mem (base + hdrW) = w ∧
  mem (base + hdrKeyBits) = keyBits U ∧
  mem (base + hdrValBits) = valBits V ∧
  mem (base + hdrThresh) = (if whpThreshold c ≤ U then whpThreshold c else 0) ∧
  mem (base + hdrCTab) = (if whpThreshold c ≤ U then cTabWhp c else 0) ∧
  mem (base + hdrDTab) = (if whpThreshold c ≤ U then dTabWhp c else 0) ∧
  mem (base + hdrRedW) = redWidthWhp U ∧
  mem (base + hdrCEff) = (if whpThreshold c ≤ U then cEff c else 0)

/-- Write a single slot `pBase + off ← prev + packedWords n k wv` and return the new offset. -/
private def addPackedWriteProg : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((pBase, off), (prev, n)), (k, wv)) => do
    let pw ← packedWordsSafeProg ((n, k), wv)
    let nxt := prev + pw
    Memory.write (pBase + off) nxt
    pure nxt

private theorem mcost_addPackedWriteProg (x : ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (addPackedWriteProg x) s = 1 := by
  rcases x with ⟨⟨⟨pBase, off⟩, ⟨prev, n⟩⟩, ⟨k, w⟩⟩
  unfold addPackedWriteProg packedWordsSafeProg
  rw [Realization.memoryCost_bind', memoryCost_pure, Realization.memoryCost_bind',
    mcost_write_eq, memoryCost_pure]

private theorem mcost_packedWordsSafeProg (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (packedWordsSafeProg x) s = 0 := by
  rcases x with ⟨⟨_, _⟩, _⟩; exact memoryCost_pure _ _

private theorem cstate_packedWordsSafeProg (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (packedWordsSafeProg x) = s := by
  rcases x with ⟨⟨_, _⟩, _⟩; rfl

private theorem addPackedWriteProg_spec {pBase off prev n k w : ℕ} (hw : 0 < w)
    (s : Memory.State) :
    let p := addPackedWriteProg (((pBase, off), (prev, n)), (k, w))
    let nxt := prev + packedWords n k w
    (Memory.spec 0).clientResult s p = nxt ∧
    (Memory.spec 0).clientState s p =
      ({ mem := Function.update s.mem (pBase + off) nxt, frontier := s.frontier } :
        Memory.State) ∧
    memoryCost p s = 1 := by
  have heq : packedWordsSafe n k w = packedWords n k w := packedWordsSafe_eq hw
  refine ⟨?_, ?_, mcost_addPackedWriteProg _ _⟩
  · change prev + packedWordsSafe n k w = prev + packedWords n k w; rw [heq]
  · unfold addPackedWriteProg packedWordsSafeProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure,
      StateTransitionSpec.clientResult_pure, StateTransitionSpec.clientState_bind,
      cstate_write_eq, StateTransitionSpec.clientState_pure]
    congr 1; simp only [show n / w * k + (n % w * k + w - 1) / w + 2 = packedWordsSafe n k w
      from rfl, heq]

private theorem validHistory_addPackedWrite {w pBase off prev n k : ℕ} {s : Memory.State}
    (hw : 0 < w) (ha : pBase + off < s.frontier) (hf : Fits w (prev + packedWords n k w)) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (addPackedWriteProg (((pBase, off), (prev, n)), (k, w)))) := by
  have heq : packedWordsSafe n k w = packedWords n k w := packedWordsSafe_eq hw
  unfold addPackedWriteProg
  dsimp only
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
    ((packedWordsSafeProg ((n, k), w)).bind fun pw =>
      (Memory.write (pBase + off) (prev + pw)).bind fun _ => pure (prev + pw)))
  rw [validHistory_bind, clientResult_width, clientState_width]
  refine ⟨trivial, ?_⟩
  have hr : (Memory.spec 0).clientResult s (packedWordsSafeProg ((n, k), w)) =
      packedWords n k w := heq
  change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
    ((Memory.write (pBase + off) (prev + packedWordsSafe n k w)).bind fun _ => _))
  rw [heq, validHistory_bind]
  exact ⟨⟨⟨ha, hf⟩, trivial⟩, trivial⟩

private theorem realizesBounded_addPackedWrite :
    RealizesBounded .exact addPackedWriteProg
      (WordEncoding.encode (α := ((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w (((pBase, off), (prev, n)), (k, wv)) s =>
        11 ≤ w ∧ wv = w ∧ k ≤ 2 * w ∧ pBase + off < s.frontier ∧
        Fits w (prev + packedWords n k w))
      (fun _ _ => 0) := by
  have hpws := realizesBounded_packedWordsSafe
  realize
  all_goals (
    rcases d with ⟨⟨⟨pBase, off⟩, ⟨prev, n⟩⟩, ⟨k, wv⟩⟩
    obtain ⟨hw11, hw_eq, hk, ha, hfit⟩ := h
    subst hw_eq
    have hw_pos : 0 < wv := by omega
    have hfr_w := hmem.1
    have hpw : packedWordsSafe n k wv = packedWords n k wv := packedWordsSafe_eq hw_pos
    have hpw_res : (Memory.spec 0).clientResult s (packedWordsSafeProg ((n, k), wv)) =
        packedWords n k wv := hpw
    try rw [hpw_res]
    dsimp only [Fits] at *
    try omega)

private theorem mem_update_at {m : ℕ → ℕ} {a v : ℕ} : Function.update m a v a = v :=
  Function.update_self a v m

private theorem mem_update_other {m : ℕ → ℕ} {a v b : ℕ} (h : b ≠ a) :
    Function.update m a v b = m b :=
  Function.update_of_ne h v m

/-- Phase A of `writeLargeCore`: writes slots `0..4`, `46`, `47` of `pBase`. -/
private def writeCoreAProg : (ℕ × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | ((base, pBase), ((N, metaBase), logN)) => do
    let u1 ← Memory.read (base + hdrU1)
    let v1 ← Memory.read (base + hdrV1)
    let wv ← Memory.read (base + hdrW)
    let redW ← Memory.read (base + hdrRedW)
    let cTab ← Memory.read (base + hdrCTab)
    let bChar := logN / 4
    Memory.write pBase N
    Memory.write (pBase + 1) metaBase
    Memory.write (pBase + 2) wv
    Memory.write (pBase + 3) redW
    Memory.write (pBase + 4) (cTab * bChar)
    Memory.write (pBase + 46) u1
    Memory.write (pBase + 47) v1

/-- Phase B of `writeLargeCore`: writes slots `5..10` of `pBase`. -/
private def writeCoreBProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((base, pBase), (logN, ell)) => do
    let cTab ← Memory.read (base + hdrCTab)
    let dTab ← Memory.read (base + hdrDTab)
    Memory.write (pBase + 5) cTab
    Memory.write (pBase + 6) dTab
    Memory.write (pBase + 7) (logN / 4)
    Memory.write (pBase + 8) (logN - 12 * ell)
    Memory.write (pBase + 9) (36 * ell)
    Memory.write (pBase + 10) (logN + 1)

/-- Phase C of `writeLargeCore`: writes slots `11..15` of `pBase`. -/
private def writeCoreCProg : (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((pBase, nCap), (bWhpv, ell)) => do
    let mBkt := 1 <<< bWhpv
    let l2 := 1 <<< (2 * ell)
    let l10 := 1 <<< (10 * ell)
    Memory.write (pBase + 11) mBkt
    Memory.write (pBase + 12) l2
    Memory.write (pBase + 13) (4 * l10)
    Memory.write (pBase + 14) (nCap / l2 + 4)
    Memory.write (pBase + 15) (mBkt * l2 + 4)

/-- Phase D of `writeLargeCore`: writes slots `16..20` of `pBase`. -/
private def writeCoreDProg : ℕ × (ℕ × ℕ) → Memory.Prog Unit
  | (pBase, (logN, ell)) => do
    let fpB := 36 * ell
    let dT := logN / (160 * ell)
    let tMin := if dT < 2 then 2 else dT
    let valLane := 12 * ell + 8
    Memory.write (pBase + 16) (ell + 4)
    Memory.write (pBase + 17) (2 * tMin * (fpB + 2))
    Memory.write (pBase + 18) (2 * tMin * valLane)
    Memory.write (pBase + 19) valLane
    Memory.write (pBase + 20) tMin

/-- Phase E of `writeLargeCore`: writes slots `21..28` of `pBase`. -/
private def writeCoreEProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((base, pBase), ell) => do
    let cEffv ← Memory.read (base + hdrCEff)
    let cTab ← Memory.read (pBase + 5)
    let tMin ← Memory.read (pBase + 20)
    let lScale := 1 <<< ell
    let l12 := 1 <<< (12 * ell)
    let l18 := 1 <<< (18 * ell)
    Memory.write (pBase + 21) ((32 * l12) / (tMin - 1) + 64)
    Memory.write (pBase + 22) ((cTab + 1) * l18 + 2)
    Memory.write (pBase + 23) l18
    Memory.write (pBase + 24) ((cEffv + 4) * lScale)
    Memory.write (pBase + 25) (4 * l12)
    Memory.write (pBase + 26) (6 * l12)
    Memory.write (pBase + 27) (8 * l12)
    Memory.write (pBase + 28) (4 * (cTab + 2))

/-- Hash offset writer (`29..31, 61..62` of `pBase`). -/
private def writeOffHashProg : ℕ → Memory.Prog Unit := fun pBase => do
  let metaBase ← Memory.read (pBase + 1)
  let wv ← Memory.read (pBase + 2)
  let cTab ← Memory.read (pBase + 5)
  let dTab ← Memory.read (pBase + 6)
  let bChar ← Memory.read (pBase + 7)
  let bWhpv ← Memory.read (pBase + 8)
  let fpB ← Memory.read (pBase + 9)
  let b2 := 1 <<< bChar
  let botE := dTab * b2
  let topE := (cTab + 1) * botE
  let topW ← packedWordsSafeProg ((topE, bChar), wv)
  let botWB ← packedWordsSafeProg ((botE, bWhpv), wv)
  let botWF ← packedWordsSafeProg ((botE, fpB), wv)
  let offBot := 1 + topW
  let offFp := 32 + offBot + botWB
  let offBM := offFp + offBot + botWF
  Memory.write (pBase + 29) offBot
  Memory.write (pBase + 30) offFp
  Memory.write (pBase + 31) offBM
  Memory.write (pBase + 61) (metaBase + 32)
  Memory.write (pBase + 62) (metaBase + offFp)

/-- Block-pool offset writer (`32..36` of `pBase`). -/
private def writeOffBpProg : ℕ → Memory.Prog Unit := fun pBase => do
  let wv ← Memory.read (pBase + 2)
  let ptrB ← Memory.read (pBase + 10)
  let mBkt ← Memory.read (pBase + 11)
  let l2 ← Memory.read (pBase + 12)
  let maxSlabs ← Memory.read (pBase + 13)
  let maxBlks ← Memory.read (pBase + 14)
  let maxTail ← Memory.read (pBase + 15)
  let offBM ← Memory.read (pBase + 31)
  let o1 ← addPackedWriteProg (((pBase, 32), (offBM, 16 * mBkt)), (ptrB, wv))
  let o2 ← addPackedWriteProg (((pBase, 33), (o1, mBkt * maxSlabs)), (ptrB, wv))
  let o3 ← addPackedWriteProg (((pBase, 34), (o2, 8 * mBkt * l2)), (ptrB, wv))
  let o4 ← addPackedWriteProg (((pBase, 35), (o3, 4 * maxBlks)), (ptrB, wv))
  let _ ← addPackedWriteProg (((pBase, 36), (o4, 16 * maxTail)), (ptrB, wv))
  pure ()

/-- SWAR B+-tree offset writer (`37..39` of `pBase`). -/
private def writeOffBtProg : ℕ → Memory.Prog Unit := fun pBase => do
  let wv ← Memory.read (pBase + 2)
  let mBkt ← Memory.read (pBase + 11)
  let nmB ← Memory.read (pBase + 16)
  let keysW ← Memory.read (pBase + 17)
  let valsW ← Memory.read (pBase + 18)
  let nSlice ← Memory.read (pBase + 21)
  let offBTM ← Memory.read (pBase + 36)
  let totBT := 3 * mBkt * nSlice
  let o1 ← addPackedWriteProg (((pBase, 37), (offBTM, totBT)), (nmB, wv))
  let o2 ← addPackedWriteProg (((pBase, 38), (o1, totBT)), (keysW, wv))
  let _ ← addPackedWriteProg (((pBase, 39), (o2, totBT)), (valsW, wv))
  pure ()

/-- `BufTrie` + page offset writer (`40..45` of `pBase`), returning
`((offPageDir, offPageTail), epochMetaWordsWhp)`. -/
private def writeOffTriePageProg : ℕ × ℕ → Memory.Prog ((ℕ × ℕ) × ℕ)
  | (pBase, pgB) => do
    let nCap ← Memory.read pBase
    let wv ← Memory.read (pBase + 2)
    let bChar ← Memory.read (pBase + 7)
    let ptrB ← Memory.read (pBase + 10)
    let maxTrie ← Memory.read (pBase + 22)
    let qEp ← Memory.read (pBase + 23)
    let offTC0 ← Memory.read (pBase + 39)
    let b2 := 1 <<< bChar
    let wTC ← packedWordsSafeProg ((maxTrie * b2, ptrB), wv)
    let wTN ← packedWordsSafeProg ((6 * maxTrie, ptrB), wv)
    let wTI ← packedWordsSafeProg ((6 * qEp + 6, ptrB), wv)
    let offTC1 := offTC0 + wTC
    let offTN0 := offTC1 + wTC
    let offTN1 := offTN0 + wTN
    let offTI0 := offTN1 + wTN
    let offTI1 := offTI0 + wTI
    let offPD := offTI1 + wTI
    Memory.write (pBase + 40) offTC1
    Memory.write (pBase + 41) offTN0
    Memory.write (pBase + 42) offTN1
    Memory.write (pBase + 43) offTI0
    Memory.write (pBase + 44) offTI1
    let wPD ← packedWordsSafeProg ((4 * (nCap / pgB + 4), ptrB), wv)
    let offPT := offPD + wPD
    let offEnd ← addPackedWriteProg (((pBase, 45), (offPT, 16 * pgB)), (ptrB, wv))
    pure ((offPD, offPT), offEnd)

/-- Full overflow-free `FastEpochLayout.ParamTable` initializer (`¬ReadsWidth`): writes slots
`0..47` and `61..62` of `[pBase, pBase + 64)` (`48..60` installed afterwards via `setSlotIoProg`),
returning `((offPageDir, offPageTail), epochMetaWordsWhp c w N)`. -/
def writeLargeParamTableProg :
    (ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × ℕ)) → Memory.Prog ((ℕ × ℕ) × ℕ)
  | ((base, pBase), ((N, metaBase), ((logN, ell), pgB))) => do
    writeCoreAProg ((base, pBase), ((N, metaBase), logN))
    writeCoreBProg ((base, pBase), (logN, ell))
    writeCoreCProg ((pBase, N), (logN - 12 * ell, ell))
    writeCoreDProg (pBase, (logN, ell))
    writeCoreEProg ((base, pBase), ell)
    writeOffHashProg pBase
    writeOffBpProg pBase
    writeOffBtProg pBase
    writeOffTriePageProg (pBase, pgB)

private theorem shift_one_eq (k : ℕ) : (1 : ℕ) <<< k = 2 ^ k := by
  rw [Nat.shiftLeft_eq, one_mul]

private theorem vh_rd {α : Type} {w a : ℕ} {s : Memory.State} {k : ℕ → Memory.Prog α}
    (ha : a < s.frontier)
    (hk : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (k (s.mem a)))) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s ((Memory.read a).bind k)) := by
  rw [validHistory_bind, clientResult_width, clientState_width]; exact ⟨⟨ha, trivial⟩, hk⟩

private theorem vh_wr {α : Type} {w a v : ℕ} {m : ℕ → ℕ} {fr : ℕ} {rest : Memory.Prog α}
    (ha : a < fr) (hv : Fits w v)
    (hr : (Memory.spec w).ValidHistory ⟨Function.update m a v, fr⟩
      ((Memory.spec w).clientHistory ⟨Function.update m a v, fr⟩ rest)) :
    (Memory.spec w).ValidHistory ⟨m, fr⟩
      ((Memory.spec w).clientHistory ⟨m, fr⟩ ((Memory.write a v).bind fun _ => rest)) := by
  rw [validHistory_bind]; exact ⟨⟨⟨ha, hv⟩, trivial⟩, hr⟩

private theorem vh_wr_last {w a v : ℕ} {m : ℕ → ℕ} {fr : ℕ} (ha : a < fr) (hv : Fits w v) :
    (Memory.spec w).ValidHistory ⟨m, fr⟩
      ((Memory.spec w).clientHistory ⟨m, fr⟩ (Memory.write a v)) :=
  ⟨⟨ha, hv⟩, trivial⟩

private theorem writeCoreAProg_spec {base : ℕ} {fl : FastEpochLayout} {s : Memory.State}
    (hth : whpThreshold fl.c ≤ fl.N) (hNU : fl.N ≤ fl.U)
    (hhdr : RootStaticHeader fl.c fl.U fl.V fl.w base s.mem) :
    let p := writeCoreAProg ((base, fl.pBase), ((fl.N, fl.metaBase), Nat.log 2 fl.N))
    let s' := (Memory.spec 0).clientState s p
    s'.frontier = s.frontier ∧ memoryCost p s = 12 ∧
    (∀ k < 5, s'.mem (fl.pBase + k) = fl.paramWord k) ∧
    s'.mem (fl.pBase + 46) = fl.paramWord 46 ∧
    s'.mem (fl.pBase + 47) = fl.paramWord 47 ∧
    (∀ a, ¬(fl.pBase ≤ a ∧ a < fl.pBase + 5 ∨ a = fl.pBase + 46 ∨ a = fl.pBase + 47) →
      s'.mem a = s.mem a) := by
  have hU_th : whpThreshold fl.c ≤ fl.U := hth.trans hNU
  have hCT : s.mem (base + hdrCTab) = cTabWhp fl.c := by
    rw [hhdr.2.2.2.2.2.2.1, ite_eq_left hU_th]
  have hmc : memoryCost (writeCoreAProg ((base, fl.pBase),
      ((fl.N, fl.metaBase), Nat.log 2 fl.N))) s = 12 := by
    unfold writeCoreAProg
    iterate 5 (rw [Realization.memoryCost_bind', mcost_read_eq, cstate_read_eq])
    iterate 6 (rw [Realization.memoryCost_bind', mcost_write_eq])
    rw [mcost_write_eq]
  have hst : (Memory.spec 0).clientState s (writeCoreAProg ((base, fl.pBase),
      ((fl.N, fl.metaBase), Nat.log 2 fl.N))) =
      { mem := Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update s.mem fl.pBase fl.N)
            (fl.pBase + 1) fl.metaBase) (fl.pBase + 2) fl.w) (fl.pBase + 3) (redWidthWhp fl.U))
          (fl.pBase + 4) (redBitsWhp fl.c fl.N))
          (fl.pBase + 46) (fl.U - 1)) (fl.pBase + 47) (fl.V - 1),
        frontier := s.frontier } := by
    unfold writeCoreAProg
    iterate 5 (rw [StateTransitionSpec.clientState_bind, cstate_read_eq, cres_read_eq])
    rw [hhdr.1, hhdr.2.1, hhdr.2.2.1, hhdr.2.2.2.2.2.2.2.2.1, hCT]
    rfl
  refine ⟨by rw [hst], hmc, fun k hk => ?_, ?_, ?_, fun a ha => ?_⟩
  · rw [hst]; dsimp only
    interval_cases k
    · rw [add_zero]
      iterate 6 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 5 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 4 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 3 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 2 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
  · rw [hst]; dsimp only
    rw [mem_update_other (by omega), mem_update_at]; rfl
  · rw [hst]; dsimp only; rw [mem_update_at]; rfl
  · rw [hst]; dsimp only
    iterate 7 rw [Function.update_of_ne (by omega)]

private theorem writeCoreBProg_spec {base : ℕ} {fl : FastEpochLayout} {s : Memory.State}
    (hth : whpThreshold fl.c ≤ fl.N) (hNU : fl.N ≤ fl.U)
    (hhdr : RootStaticHeader fl.c fl.U fl.V fl.w base s.mem) :
    let p := writeCoreBProg ((base, fl.pBase), (Nat.log 2 fl.N, Dynamic.logLogFactor fl.N))
    let s' := (Memory.spec 0).clientState s p
    s'.frontier = s.frontier ∧ memoryCost p s = 8 ∧
    (∀ k, 5 ≤ k → k ≤ 10 → s'.mem (fl.pBase + k) = fl.paramWord k) ∧
    (∀ a, ¬(fl.pBase + 5 ≤ a ∧ a < fl.pBase + 11) → s'.mem a = s.mem a) := by
  have hU_th : whpThreshold fl.c ≤ fl.U := hth.trans hNU
  have hN_pos : 0 < fl.N := (whpThreshold_pos fl.c).trans_le hth
  have hCT : s.mem (base + hdrCTab) = cTabWhp fl.c := by
    rw [hhdr.2.2.2.2.2.2.1, ite_eq_left hU_th]
  have hDT : s.mem (base + hdrDTab) = dTabWhp fl.c := by
    rw [hhdr.2.2.2.2.2.2.2.1, ite_eq_left hU_th]
  have hp_eq : Nat.log 2 fl.N + 1 = globalPtrBits fl.N := (clog_succ_eq_of_log hN_pos).symm
  have hmc : memoryCost (writeCoreBProg ((base, fl.pBase),
      (Nat.log 2 fl.N, Dynamic.logLogFactor fl.N))) s = 8 := by
    unfold writeCoreBProg
    iterate 2 (rw [Realization.memoryCost_bind', mcost_read_eq, cstate_read_eq])
    iterate 5 (rw [Realization.memoryCost_bind', mcost_write_eq])
    rw [mcost_write_eq]
  have hst : (Memory.spec 0).clientState s (writeCoreBProg ((base, fl.pBase),
      (Nat.log 2 fl.N, Dynamic.logLogFactor fl.N))) =
      { mem := Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update s.mem (fl.pBase + 5) (cTabWhp fl.c))
            (fl.pBase + 6) (dTabWhp fl.c)) (fl.pBase + 7) (bCharWhp fl.N))
          (fl.pBase + 8) (bWhp fl.N)) (fl.pBase + 9) (fpBitsWhp fl.N))
          (fl.pBase + 10) (globalPtrBits fl.N),
        frontier := s.frontier } := by
    unfold writeCoreBProg
    iterate 2 (rw [StateTransitionSpec.clientState_bind, cstate_read_eq, cres_read_eq])
    rw [hCT, hDT, ← hp_eq]; rfl
  refine ⟨by rw [hst], hmc, fun k hk1 hk2 => ?_, fun a ha => ?_⟩
  · rw [hst]; dsimp only; interval_cases k
    · iterate 5 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 4 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 3 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 2 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _
    · exact Function.update_self _ _ _
  · rw [hst]; dsimp only; iterate 6 rw [Function.update_of_ne (by omega)]

private theorem writeCoreCProg_spec {fl : FastEpochLayout} {s : Memory.State} :
    let p := writeCoreCProg ((fl.pBase, fl.N), (bWhp fl.N, Dynamic.logLogFactor fl.N))
    let s' := (Memory.spec 0).clientState s p
    s'.frontier = s.frontier ∧ memoryCost p s = 5 ∧
    (∀ k, 11 ≤ k → k ≤ 15 → s'.mem (fl.pBase + k) = fl.paramWord k) ∧
    (∀ a, ¬(fl.pBase + 11 ≤ a ∧ a < fl.pBase + 16) → s'.mem a = s.mem a) := by
  have hmc : memoryCost (writeCoreCProg ((fl.pBase, fl.N),
      (bWhp fl.N, Dynamic.logLogFactor fl.N))) s = 5 := by
    unfold writeCoreCProg
    iterate 4 (rw [Realization.memoryCost_bind', mcost_write_eq])
    rw [mcost_write_eq]
  have hst : (Memory.spec 0).clientState s (writeCoreCProg ((fl.pBase, fl.N),
      (bWhp fl.N, Dynamic.logLogFactor fl.N))) =
      { mem := Function.update (Function.update (Function.update (Function.update
          (Function.update s.mem (fl.pBase + 11) (numBucketsWhp fl.N))
            (fl.pBase + 12) (slabSizeWhp fl.N))
            (fl.pBase + 13) (maxSlabsPerBktWhp fl.N))
            (fl.pBase + 14) (fl.N / slabSizeWhp fl.N + 4))
            (fl.pBase + 15) (maxTailWhp fl.N),
        frontier := s.frontier } := by
    unfold writeCoreCProg
    iterate 4 (rw [StateTransitionSpec.clientState_bind, cstate_write_eq])
    rw [cstate_write_eq]
    simp only [shift_one_eq, ← slabScale_pow_eq_shift]
    rfl
  refine ⟨by rw [hst], hmc, fun k hk1 hk2 => ?_, fun a ha => ?_⟩
  · rw [hst]; dsimp only; interval_cases k
    · iterate 4 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 3 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 2 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _
    · exact Function.update_self _ _ _
  · rw [hst]; dsimp only; iterate 5 rw [Function.update_of_ne (by omega)]

private theorem writeCoreDProg_spec {fl : FastEpochLayout} {s : Memory.State} :
    let p := writeCoreDProg (fl.pBase, (Nat.log 2 fl.N, Dynamic.logLogFactor fl.N))
    let s' := (Memory.spec 0).clientState s p
    s'.frontier = s.frontier ∧ memoryCost p s = 5 ∧
    (∀ k, 16 ≤ k → k ≤ 20 → s'.mem (fl.pBase + k) = fl.paramWord k) ∧
    (∀ a, ¬(fl.pBase + 16 ≤ a ∧ a < fl.pBase + 21) → s'.mem a = s.mem a) := by
  have htm : (if Nat.log 2 fl.N / (160 * Dynamic.logLogFactor fl.N) < 2 then 2
      else Nat.log 2 fl.N / (160 * Dynamic.logLogFactor fl.N)) = tMinWhp fl.N := by
    unfold tMinWhp
    by_cases h : Nat.log 2 fl.N / (160 * Dynamic.logLogFactor fl.N) < 2
    · rw [ite_eq_left h, max_eq_left (by omega)]
    · rw [ite_eq_right h, max_eq_right (by omega)]
  have hmc : memoryCost (writeCoreDProg (fl.pBase,
      (Nat.log 2 fl.N, Dynamic.logLogFactor fl.N))) s = 5 := by
    unfold writeCoreDProg
    iterate 4 (rw [Realization.memoryCost_bind', mcost_write_eq])
    rw [mcost_write_eq]
  have hst : (Memory.spec 0).clientState s (writeCoreDProg (fl.pBase,
      (Nat.log 2 fl.N, Dynamic.logLogFactor fl.N))) =
      { mem := Function.update (Function.update (Function.update (Function.update
          (Function.update s.mem (fl.pBase + 16) (nodeMetaBitsWhp fl.N))
            (fl.pBase + 17) (keysWordBitsWhp fl.N))
            (fl.pBase + 18) (valsWordBitsWhp fl.N))
            (fl.pBase + 19) (valLaneBitsWhp fl.N))
            (fl.pBase + 20) (tMinWhp fl.N),
        frontier := s.frontier } := by
    unfold writeCoreDProg
    iterate 4 (rw [StateTransitionSpec.clientState_bind, cstate_write_eq])
    rw [cstate_write_eq, htm]; rfl
  refine ⟨by rw [hst], hmc, fun k hk1 hk2 => ?_, fun a ha => ?_⟩
  · rw [hst]; dsimp only; interval_cases k
    · iterate 4 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 3 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 2 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _
    · exact Function.update_self _ _ _
  · rw [hst]; dsimp only; iterate 5 rw [Function.update_of_ne (by omega)]

private theorem writeCoreEProg_spec {base : ℕ} {fl : FastEpochLayout} {s : Memory.State}
    (hce : s.mem (base + hdrCEff) = cEff fl.c)
    (hct : s.mem (fl.pBase + 5) = cTabWhp fl.c)
    (htm : s.mem (fl.pBase + 20) = tMinWhp fl.N) :
    let p := writeCoreEProg ((base, fl.pBase), Dynamic.logLogFactor fl.N)
    let s' := (Memory.spec 0).clientState s p
    s'.frontier = s.frontier ∧ memoryCost p s = 11 ∧
    (∀ k, 21 ≤ k → k ≤ 28 → s'.mem (fl.pBase + k) = fl.paramWord k) ∧
    (∀ a, ¬(fl.pBase + 21 ≤ a ∧ a < fl.pBase + 29) → s'.mem a = s.mem a) := by
  have hmc : memoryCost (writeCoreEProg ((base, fl.pBase), Dynamic.logLogFactor fl.N)) s = 11 := by
    unfold writeCoreEProg
    iterate 3 (rw [Realization.memoryCost_bind', mcost_read_eq, cstate_read_eq])
    iterate 7 (rw [Realization.memoryCost_bind', mcost_write_eq])
    rw [mcost_write_eq]
  have hst : (Memory.spec 0).clientState s (writeCoreEProg ((base, fl.pBase),
      Dynamic.logLogFactor fl.N)) =
      { mem := Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (Function.update s.mem
            (fl.pBase + 21) (nSliceWhp fl.N))
            (fl.pBase + 22) (maxTrieNodesWhp fl.c fl.N))
            (fl.pBase + 23) (qEpochWhp fl.N))
            (fl.pBase + 24) (sMaxWhp fl.c fl.N))
            (fl.pBase + 25) (capMaxWhp fl.N))
            (fl.pBase + 26) (6 * slabScale fl.N ^ 12))
            (fl.pBase + 27) (8 * slabScale fl.N ^ 12))
            (fl.pBase + 28) (4 * (cTabWhp fl.c + 2)),
        frontier := s.frontier } := by
    unfold writeCoreEProg
    iterate 3 (rw [StateTransitionSpec.clientState_bind, cstate_read_eq, cres_read_eq])
    rw [hce, hct, htm]
    iterate 7 (rw [StateTransitionSpec.clientState_bind, cstate_write_eq])
    rw [cstate_write_eq]
    simp only [shift_one_eq, ← slabScale_pow_eq_shift]
    rfl
  refine ⟨by rw [hst], hmc, fun k hk1 hk2 => ?_, fun a ha => ?_⟩
  · rw [hst]; dsimp only; interval_cases k
    · iterate 7 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 6 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 5 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 4 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 3 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 2 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _
    · exact Function.update_self _ _ _
  · rw [hst]; dsimp only; iterate 8 rw [Function.update_of_ne (by omega)]

private theorem writeOffHashProg_spec {fl : FastEpochLayout} {s : Memory.State}
    (hw : 0 < fl.w) (hm : s.mem (fl.pBase + 1) = fl.metaBase) (hwm : s.mem (fl.pBase + 2) = fl.w)
    (hct : s.mem (fl.pBase + 5) = cTabWhp fl.c) (hdt : s.mem (fl.pBase + 6) = dTabWhp fl.c)
    (hbc : s.mem (fl.pBase + 7) = bCharWhp fl.N) (hbw : s.mem (fl.pBase + 8) = bWhp fl.N)
    (hfp : s.mem (fl.pBase + 9) = fpBitsWhp fl.N) :
    let s' := (Memory.spec 0).clientState s (writeOffHashProg fl.pBase)
    s'.frontier = s.frontier ∧ memoryCost (writeOffHashProg fl.pBase) s = 12 ∧
    s'.mem (fl.pBase + 29) = fl.paramWord 29 ∧
    s'.mem (fl.pBase + 30) = fl.paramWord 30 ∧
    s'.mem (fl.pBase + 31) = fl.paramWord 31 ∧
    s'.mem (fl.pBase + 61) = fl.paramWord 61 ∧
    s'.mem (fl.pBase + 62) = fl.paramWord 62 ∧
    (∀ a, ¬(fl.pBase + 29 ≤ a ∧ a < fl.pBase + 32 ∨
      a = fl.pBase + 61 ∨ a = fl.pBase + 62) → s'.mem a = s.mem a) := by
  have hmc : memoryCost (writeOffHashProg fl.pBase) s = 12 := by
    unfold writeOffHashProg
    iterate 7 (rw [Realization.memoryCost_bind', mcost_read_eq, cstate_read_eq])
    iterate 3 (rw [Realization.memoryCost_bind', mcost_packedWordsSafeProg,
      cstate_packedWordsSafeProg])
    iterate 4 (rw [Realization.memoryCost_bind', mcost_write_eq])
    rw [mcost_write_eq]
  have hst : (Memory.spec 0).clientState s (writeOffHashProg fl.pBase) =
      { mem := Function.update (Function.update (Function.update (Function.update
          (Function.update s.mem (fl.pBase + 29) fl.dtOffBot)
            (fl.pBase + 30) (offFpHash fl.c fl.w fl.N))
            (fl.pBase + 31) (offBktMeta fl.c fl.w fl.N))
            (fl.pBase + 61) fl.bktHashBase)
            (fl.pBase + 62) fl.fpHashBase,
        frontier := s.frontier } := by
    unfold writeOffHashProg
    iterate 7 (rw [StateTransitionSpec.clientState_bind, cstate_read_eq, cres_read_eq])
    rw [hm, hwm, hct, hdt, hbc, hbw, hfp, shift_one_eq]
    have hmul : (cTabWhp fl.c + 1) * (dTabWhp fl.c * 2 ^ bCharWhp fl.N) =
        BitPackedDoubleTabulation.topEntries (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) := by
      ring
    have heq : ∀ n k, packedWordsSafe n k fl.w = packedWords n k fl.w := fun _ _ =>
      packedWordsSafe_eq hw
    have hcr : ∀ n k, (Memory.spec 0).clientResult s (packedWordsSafeProg ((n, k), fl.w)) =
        packedWords n k fl.w := heq
    have hcs : ∀ n k, (Memory.spec 0).clientState s (packedWordsSafeProg ((n, k), fl.w)) = s :=
      fun _ _ => rfl
    iterate 3 (rw [StateTransitionSpec.clientState_bind, hcs, hcr])
    rw [hmul]
    iterate 4 (rw [StateTransitionSpec.clientState_bind, cstate_write_eq])
    rw [cstate_write_eq]
    have h30 : 32 + (1 + packedWords (BitPackedDoubleTabulation.topEntries (cTabWhp fl.c)
        (dTabWhp fl.c) (bCharWhp fl.N)) (bCharWhp fl.N) fl.w) +
        packedWords (dTabWhp fl.c * 2 ^ bCharWhp fl.N) (bWhp fl.N) fl.w =
        offFpHash fl.c fl.w fl.N := by
      unfold offFpHash offBktHash BitPackedDoubleTabulation.space
        BitPackedDoubleTabulation.topWords BitPackedDoubleTabulation.botWords
        BitPackedDoubleTabulation.botEntries; omega
    have h31 : offFpHash fl.c fl.w fl.N +
        (1 + packedWords (BitPackedDoubleTabulation.topEntries (cTabWhp fl.c)
          (dTabWhp fl.c) (bCharWhp fl.N)) (bCharWhp fl.N) fl.w) +
        packedWords (dTabWhp fl.c * 2 ^ bCharWhp fl.N) (fpBitsWhp fl.N) fl.w =
        offBktMeta fl.c fl.w fl.N := by
      unfold offBktMeta BitPackedDoubleTabulation.space
        BitPackedDoubleTabulation.topWords BitPackedDoubleTabulation.botWords
        BitPackedDoubleTabulation.botEntries; omega
    rw [h30, h31]; rfl
  refine ⟨by rw [hst], hmc, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · rw [hst]; dsimp only
    iterate 4 rw [Function.update_of_ne (by omega)]
    exact Function.update_self _ _ _
  · rw [hst]; dsimp only
    iterate 3 rw [Function.update_of_ne (by omega)]
    exact Function.update_self _ _ _
  · rw [hst]; dsimp only
    iterate 2 rw [Function.update_of_ne (by omega)]
    exact Function.update_self _ _ _
  · rw [hst]; dsimp only
    rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _
  · rw [hst]; dsimp only; exact Function.update_self _ _ _
  · rw [hst]; dsimp only; iterate 5 rw [Function.update_of_ne (by omega)]

private theorem writeOffBpProg_spec {fl : FastEpochLayout} {s : Memory.State} (hw : 0 < fl.w)
    (hwm : s.mem (fl.pBase + 2) = fl.w) (hpb : s.mem (fl.pBase + 10) = globalPtrBits fl.N)
    (hmb : s.mem (fl.pBase + 11) = numBucketsWhp fl.N)
    (hl2 : s.mem (fl.pBase + 12) = slabSizeWhp fl.N)
    (hms : s.mem (fl.pBase + 13) = maxSlabsPerBktWhp fl.N)
    (hmbk : s.mem (fl.pBase + 14) = fl.N / slabSizeWhp fl.N + 4)
    (hmt : s.mem (fl.pBase + 15) = maxTailWhp fl.N)
    (hbm : s.mem (fl.pBase + 31) = offBktMeta fl.c fl.w fl.N) :
    let s' := (Memory.spec 0).clientState s (writeOffBpProg fl.pBase)
    s'.frontier = s.frontier ∧ memoryCost (writeOffBpProg fl.pBase) s = 13 ∧
    (∀ k, 32 ≤ k → k ≤ 36 → s'.mem (fl.pBase + k) = fl.paramWord k) ∧
    (∀ a, ¬(fl.pBase + 32 ≤ a ∧ a < fl.pBase + 37) → s'.mem a = s.mem a) := by
  have hmc : memoryCost (writeOffBpProg fl.pBase) s = 13 := by
    unfold writeOffBpProg
    iterate 8 (rw [Realization.memoryCost_bind', mcost_read_eq, cstate_read_eq])
    iterate 5 (rw [Realization.memoryCost_bind', mcost_addPackedWriteProg])
    rw [memoryCost_pure]
  have hst : (Memory.spec 0).clientState s (writeOffBpProg fl.pBase) =
      { mem := Function.update (Function.update (Function.update (Function.update
          (Function.update s.mem (fl.pBase + 32) (offSlabDir fl.c fl.w fl.N))
            (fl.pBase + 33) (offTailDir fl.c fl.w fl.N))
            (fl.pBase + 34) (offSlabOwner fl.c fl.w fl.N))
            (fl.pBase + 35) (offTailOwner fl.c fl.w fl.N))
            (fl.pBase + 36) (offBTreeMeta fl.c fl.w fl.N),
        frontier := s.frontier } := by
    unfold writeOffBpProg
    iterate 8 (rw [StateTransitionSpec.clientState_bind, cstate_read_eq, cres_read_eq])
    rw [hwm, hpb, hmb, hl2, hms, hmbk, hmt, hbm]
    iterate 4 (rw [StateTransitionSpec.clientState_bind,
      (addPackedWriteProg_spec hw _).1, (addPackedWriteProg_spec hw _).2.1])
    rw [StateTransitionSpec.clientState_bind, (addPackedWriteProg_spec hw _).2.1,
      StateTransitionSpec.clientState_pure]; rfl
  refine ⟨by rw [hst], hmc, fun k hk1 hk2 => ?_, fun a ha => ?_⟩
  · rw [hst]; dsimp only; interval_cases k
    · iterate 4 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 3 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 2 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _
    · exact Function.update_self _ _ _
  · rw [hst]; dsimp only; iterate 5 rw [Function.update_of_ne (by omega)]

private theorem writeOffBtProg_spec {fl : FastEpochLayout} {s : Memory.State} (hw : 0 < fl.w)
    (hwm : s.mem (fl.pBase + 2) = fl.w) (hmb : s.mem (fl.pBase + 11) = numBucketsWhp fl.N)
    (hnm : s.mem (fl.pBase + 16) = nodeMetaBitsWhp fl.N)
    (hkw : s.mem (fl.pBase + 17) = keysWordBitsWhp fl.N)
    (hvw : s.mem (fl.pBase + 18) = valsWordBitsWhp fl.N)
    (hns : s.mem (fl.pBase + 21) = nSliceWhp fl.N)
    (hbt : s.mem (fl.pBase + 36) = offBTreeMeta fl.c fl.w fl.N) :
    let s' := (Memory.spec 0).clientState s (writeOffBtProg fl.pBase)
    s'.frontier = s.frontier ∧ memoryCost (writeOffBtProg fl.pBase) s = 10 ∧
    (∀ k, 37 ≤ k → k ≤ 39 → s'.mem (fl.pBase + k) = fl.paramWord k) ∧
    (∀ a, ¬(fl.pBase + 37 ≤ a ∧ a < fl.pBase + 40) → s'.mem a = s.mem a) := by
  have hmc : memoryCost (writeOffBtProg fl.pBase) s = 10 := by
    unfold writeOffBtProg
    iterate 7 (rw [Realization.memoryCost_bind', mcost_read_eq, cstate_read_eq])
    iterate 3 (rw [Realization.memoryCost_bind', mcost_addPackedWriteProg])
    rw [memoryCost_pure]
  have h39 : offBTreeVals fl.c fl.w fl.N +
      packedWords (totalBTreeNodesWhp fl.N) (valsWordBitsWhp fl.N) fl.w =
      offTrieChild fl.c fl.w fl.N 0 := by unfold offTrieChild; simp
  have hst : (Memory.spec 0).clientState s (writeOffBtProg fl.pBase) =
      { mem := Function.update (Function.update (Function.update s.mem
          (fl.pBase + 37) (offBTreeKeys fl.c fl.w fl.N))
          (fl.pBase + 38) (offBTreeVals fl.c fl.w fl.N))
          (fl.pBase + 39) (offTrieChild fl.c fl.w fl.N 0),
        frontier := s.frontier } := by
    unfold writeOffBtProg
    iterate 7 (rw [StateTransitionSpec.clientState_bind, cstate_read_eq, cres_read_eq])
    rw [hwm, hmb, hnm, hkw, hvw, hns, hbt]
    have htot : 3 * numBucketsWhp fl.N * nSliceWhp fl.N = totalBTreeNodesWhp fl.N := rfl
    rw [htot]
    iterate 2 (rw [StateTransitionSpec.clientState_bind,
      (addPackedWriteProg_spec hw _).1, (addPackedWriteProg_spec hw _).2.1])
    rw [StateTransitionSpec.clientState_bind, (addPackedWriteProg_spec hw _).2.1,
      StateTransitionSpec.clientState_pure]
    congr 1; dsimp only
    rw [show offBTreeMeta fl.c fl.w fl.N +
          packedWords (totalBTreeNodesWhp fl.N) (nodeMetaBitsWhp fl.N) fl.w =
          offBTreeKeys fl.c fl.w fl.N from rfl,
      show offBTreeKeys fl.c fl.w fl.N +
          packedWords (totalBTreeNodesWhp fl.N) (keysWordBitsWhp fl.N) fl.w =
          offBTreeVals fl.c fl.w fl.N from rfl, h39]
  refine ⟨by rw [hst], hmc, fun k hk1 hk2 => ?_, fun a ha => ?_⟩
  · rw [hst]; dsimp only; interval_cases k
    · iterate 2 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _
    · exact Function.update_self _ _ _
  · rw [hst]; dsimp only; iterate 3 rw [Function.update_of_ne (by omega)]

private theorem writeOffTriePageProg_spec {fl : FastEpochLayout} {s : Memory.State}
    (hth : whpThreshold fl.c ≤ fl.N) (hw : 0 < fl.w)
    (hn : s.mem fl.pBase = fl.N) (hwm : s.mem (fl.pBase + 2) = fl.w)
    (hbc : s.mem (fl.pBase + 7) = bCharWhp fl.N)
    (hpb : s.mem (fl.pBase + 10) = globalPtrBits fl.N)
    (hmt : s.mem (fl.pBase + 22) = maxTrieNodesWhp fl.c fl.N)
    (hqe : s.mem (fl.pBase + 23) = qEpochWhp fl.N)
    (htc : s.mem (fl.pBase + 39) = offTrieChild fl.c fl.w fl.N 0) :
    let p := writeOffTriePageProg (fl.pBase, pageSizeWhp fl.N)
    let s' := (Memory.spec 0).clientState s p
    (Memory.spec 0).clientResult s p =
      ((offPageDir fl.c fl.w fl.N, offPageTail fl.c fl.w fl.N),
        epochMetaWordsWhp fl.c fl.w fl.N) ∧
    s'.frontier = s.frontier ∧ memoryCost p s = 13 ∧
    (∀ k, 40 ≤ k → k ≤ 45 → s'.mem (fl.pBase + k) = fl.paramWord k) ∧
    (∀ a, ¬(fl.pBase + 40 ≤ a ∧ a < fl.pBase + 46) → s'.mem a = s.mem a) := by
  have heq_end := offEpochEnd_eq_epochMetaWordsWhp (w := fl.w) hth
  have e40 : offTrieChild fl.c fl.w fl.N 0 + trieChildWords fl.c fl.w fl.N =
      offTrieChild fl.c fl.w fl.N 1 := by unfold offTrieChild; omega
  have e41 : offTrieChild fl.c fl.w fl.N 1 + trieChildWords fl.c fl.w fl.N =
      offTrieNode fl.c fl.w fl.N 0 := by unfold offTrieNode offTrieChild; omega
  have e42 : offTrieNode fl.c fl.w fl.N 0 + trieNodeWords fl.c fl.w fl.N =
      offTrieNode fl.c fl.w fl.N 1 := by unfold offTrieNode; omega
  have e43 : offTrieNode fl.c fl.w fl.N 1 + trieNodeWords fl.c fl.w fl.N =
      offTrieItem fl.c fl.w fl.N 0 := by unfold offTrieItem offTrieNode; omega
  have e44 : offTrieItem fl.c fl.w fl.N 0 + trieItemWords fl.w fl.N =
      offTrieItem fl.c fl.w fl.N 1 := by unfold offTrieItem; omega
  have ePD : offTrieItem fl.c fl.w fl.N 1 + trieItemWords fl.w fl.N =
      offPageDir fl.c fl.w fl.N := by unfold offPageDir offTrieItem; omega
  have hcr : ∀ n k st, (Memory.spec 0).clientResult st (packedWordsSafeProg ((n, k), fl.w)) =
      packedWords n k fl.w := fun _ _ _ => packedWordsSafe_eq hw
  have hcs : ∀ n k st, (Memory.spec 0).clientState st (packedWordsSafeProg ((n, k), fl.w)) = st :=
    fun _ _ _ => rfl
  have hmc : memoryCost (writeOffTriePageProg (fl.pBase, pageSizeWhp fl.N)) s = 13 := by
    unfold writeOffTriePageProg
    iterate 7 (rw [Realization.memoryCost_bind', mcost_read_eq, cstate_read_eq])
    iterate 3 (rw [Realization.memoryCost_bind', mcost_packedWordsSafeProg,
      cstate_packedWordsSafeProg])
    iterate 5 (rw [Realization.memoryCost_bind', mcost_write_eq])
    rw [Realization.memoryCost_bind', mcost_packedWordsSafeProg, cstate_packedWordsSafeProg,
      Realization.memoryCost_bind', mcost_addPackedWriteProg, memoryCost_pure]
  have hres : (Memory.spec 0).clientResult s
      (writeOffTriePageProg (fl.pBase, pageSizeWhp fl.N)) =
      ((offPageDir fl.c fl.w fl.N, offPageTail fl.c fl.w fl.N),
        epochMetaWordsWhp fl.c fl.w fl.N) := by
    unfold writeOffTriePageProg
    iterate 7 (rw [StateTransitionSpec.clientResult_bind, cstate_read_eq, cres_read_eq])
    rw [hn, hwm, hbc, hpb, hmt, hqe, htc, shift_one_eq]
    iterate 3 (rw [StateTransitionSpec.clientResult_bind, hcs, hcr])
    iterate 5 (rw [StateTransitionSpec.clientResult_bind, cstate_write_eq])
    rw [StateTransitionSpec.clientResult_bind, hcs, hcr, StateTransitionSpec.clientResult_bind,
      (addPackedWriteProg_spec hw _).1, (addPackedWriteProg_spec hw _).2.1,
      StateTransitionSpec.clientResult_pure]
    simp only [trieChildWords, trieNodeWords, trieItemWords] at e40 e41 e42 e43 e44 ePD
    rw [e40, e41, e42, e43, e44, ePD, ← heq_end]; rfl
  have hst : (Memory.spec 0).clientState s
      (writeOffTriePageProg (fl.pBase, pageSizeWhp fl.N)) =
      { mem := Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update s.mem
            (fl.pBase + 40) (offTrieChild fl.c fl.w fl.N 1))
            (fl.pBase + 41) (offTrieNode fl.c fl.w fl.N 0))
            (fl.pBase + 42) (offTrieNode fl.c fl.w fl.N 1))
            (fl.pBase + 43) (offTrieItem fl.c fl.w fl.N 0))
            (fl.pBase + 44) (offTrieItem fl.c fl.w fl.N 1))
            (fl.pBase + 45) (epochMetaWordsWhp fl.c fl.w fl.N),
        frontier := s.frontier } := by
    unfold writeOffTriePageProg
    iterate 7 (rw [StateTransitionSpec.clientState_bind, cstate_read_eq, cres_read_eq])
    rw [hn, hwm, hbc, hpb, hmt, hqe, htc, shift_one_eq]
    iterate 3 (rw [StateTransitionSpec.clientState_bind, hcs, hcr])
    iterate 5 (rw [StateTransitionSpec.clientState_bind, cstate_write_eq])
    rw [StateTransitionSpec.clientState_bind, hcs, hcr, StateTransitionSpec.clientState_bind,
      (addPackedWriteProg_spec hw _).1, (addPackedWriteProg_spec hw _).2.1,
      StateTransitionSpec.clientState_pure]
    simp only [trieChildWords, trieNodeWords, trieItemWords] at e40 e41 e42 e43 e44 ePD
    rw [e40, e41, e42, e43, e44, ePD, ← heq_end]; rfl
  refine ⟨hres, by rw [hst], hmc, fun k hk1 hk2 => ?_, fun a ha => ?_⟩
  · rw [hst]; dsimp only; interval_cases k
    · iterate 5 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 4 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 3 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · iterate 2 rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _
    · exact Function.update_self _ _ _
  · rw [hst]; dsimp only; iterate 6 rw [Function.update_of_ne (by omega)]

/-- Full correctness, exact memory cost (`89`), return value, and frame preservation for
`writeLargeParamTableProg`. -/
theorem writeLargeParamTableProg_spec {base : ℕ} {fl : FastEpochLayout} {s : Memory.State}
    (hdisj : base + 10 ≤ fl.pBase ∨ fl.pBase + 63 ≤ base)
    (hth : whpThreshold fl.c ≤ fl.N) (hNU : fl.N ≤ fl.U) (hw : 0 < fl.w)
    (hhdr : RootStaticHeader fl.c fl.U fl.V fl.w base s.mem) :
    let logN := Nat.log 2 fl.N
    let ell := Dynamic.logLogFactor fl.N
    let p := writeLargeParamTableProg ((base, fl.pBase), ((fl.N, fl.metaBase),
      ((logN, ell), pageSizeWhp fl.N)))
    let s' := (Memory.spec 0).clientState s p
    (Memory.spec 0).clientResult s p =
      ((offPageDir fl.c fl.w fl.N, offPageTail fl.c fl.w fl.N),
        epochMetaWordsWhp fl.c fl.w fl.N) ∧
    s'.frontier = s.frontier ∧
    memoryCost p s = 89 ∧
    (∀ k < 48, s'.mem (fl.pBase + k) = fl.paramWord k) ∧
    s'.mem (fl.pBase + 61) = fl.paramWord 61 ∧
    s'.mem (fl.pBase + 62) = fl.paramWord 62 ∧
    (∀ a, ¬(fl.pBase ≤ a ∧ a < fl.pBase + 48 ∨
      a = fl.pBase + 61 ∨ a = fl.pBase + 62) → s'.mem a = s.mem a) := by
  dsimp only
  have hU_th : whpThreshold fl.c ≤ fl.U := hth.trans hNU
  set logN := Nat.log 2 fl.N
  set ell := Dynamic.logLogFactor fl.N
  set pgB := pageSizeWhp fl.N
  set s1 := (Memory.spec 0).clientState s
    (writeCoreAProg ((base, fl.pBase), ((fl.N, fl.metaBase), logN)))
  set s2 := (Memory.spec 0).clientState s1 (writeCoreBProg ((base, fl.pBase), (logN, ell)))
  set s3 := (Memory.spec 0).clientState s2 (writeCoreCProg ((fl.pBase, fl.N), (bWhp fl.N, ell)))
  set s4 := (Memory.spec 0).clientState s3 (writeCoreDProg (fl.pBase, (logN, ell)))
  set s5 := (Memory.spec 0).clientState s4 (writeCoreEProg ((base, fl.pBase), ell))
  set s6 := (Memory.spec 0).clientState s5 (writeOffHashProg fl.pBase)
  set s7 := (Memory.spec 0).clientState s6 (writeOffBpProg fl.pBase)
  set s8 := (Memory.spec 0).clientState s7 (writeOffBtProg fl.pBase)
  set s9 := (Memory.spec 0).clientState s8 (writeOffTriePageProg (fl.pBase, pgB))
  have hA := writeCoreAProg_spec (fl := fl) (s := s) hth hNU hhdr
  have hhdr1 : RootStaticHeader fl.c fl.U fl.V fl.w base s1.mem := by
    have heq : ∀ j < 10, s1.mem (base + j) = s.mem (base + j) := fun j hj =>
      hA.2.2.2.2.2 (base + j) (by rcases hdisj with h | h <;> omega)
    exact ⟨(heq 0 (by decide)).trans hhdr.1, (heq 1 (by decide)).trans hhdr.2.1,
      (heq 2 (by decide)).trans hhdr.2.2.1, (heq 3 (by decide)).trans hhdr.2.2.2.1,
      (heq 4 (by decide)).trans hhdr.2.2.2.2.1, (heq 5 (by decide)).trans hhdr.2.2.2.2.2.1,
      (heq 6 (by decide)).trans hhdr.2.2.2.2.2.2.1, (heq 7 (by decide)).trans hhdr.2.2.2.2.2.2.2.1,
      (heq 8 (by decide)).trans hhdr.2.2.2.2.2.2.2.2.1,
      (heq 9 (by decide)).trans hhdr.2.2.2.2.2.2.2.2.2⟩
  have hB := writeCoreBProg_spec (fl := fl) (s := s1) hth hNU hhdr1
  have hC := writeCoreCProg_spec (fl := fl) (s := s2)
  have hD := writeCoreDProg_spec (fl := fl) (s := s3)
  have hce4 : s4.mem (base + hdrCEff) = cEff fl.c := by
    rw [hD.2.2.2 _ (by unfold hdrCEff; rcases hdisj with h | h <;> omega),
      hC.2.2.2 _ (by unfold hdrCEff; rcases hdisj with h | h <;> omega),
      hB.2.2.2 _ (by unfold hdrCEff; rcases hdisj with h | h <;> omega),
      hhdr1.2.2.2.2.2.2.2.2.2, ite_eq_left hU_th]
  have hct4 : s4.mem (fl.pBase + 5) = cTabWhp fl.c := by
    rw [hD.2.2.2 _ (by omega), hC.2.2.2 _ (by omega)]; exact hB.2.2.1 5 (by decide) (by decide)
  have htm4 : s4.mem (fl.pBase + 20) = tMinWhp fl.N := hD.2.2.1 20 (by decide) (by decide)
  have hE := writeCoreEProg_spec (fl := fl) (s := s4) hce4 hct4 htm4
  have hs5 : ∀ k ≤ 28, s5.mem (fl.pBase + k) = fl.paramWord k := by
    intro k hk
    by_cases h21 : 21 ≤ k
    · exact hE.2.2.1 k h21 hk
    · rw [hE.2.2.2 _ (by omega)]
      by_cases h16 : 16 ≤ k
      · exact hD.2.2.1 k h16 (by omega)
      · rw [hD.2.2.2 _ (by omega)]
        by_cases h11 : 11 ≤ k
        · exact hC.2.2.1 k h11 (by omega)
        · rw [hC.2.2.2 _ (by omega)]
          by_cases h5 : 5 ≤ k
          · exact hB.2.2.1 k h5 (by omega)
          · rw [hB.2.2.2 _ (by omega)]; exact hA.2.2.1 k (by omega)
  have hH := writeOffHashProg_spec (fl := fl) (s := s5) hw
    (hs5 1 (by decide)) (hs5 2 (by decide)) (hs5 5 (by decide)) (hs5 6 (by decide))
    (hs5 7 (by decide)) (hs5 8 (by decide)) (hs5 9 (by decide))
  have hs6k : ∀ k ≤ 28, s6.mem (fl.pBase + k) = fl.paramWord k := fun k hk =>
    (hH.2.2.2.2.2.2.2 _ (by omega)).trans (hs5 k hk)
  have hBp := writeOffBpProg_spec (fl := fl) (s := s6) hw
    (hs6k 2 (by decide)) (hs6k 10 (by decide)) (hs6k 11 (by decide)) (hs6k 12 (by decide))
    (hs6k 13 (by decide)) (hs6k 14 (by decide)) (hs6k 15 (by decide)) hH.2.2.2.2.1
  have hs7k : ∀ k ≤ 28, s7.mem (fl.pBase + k) = fl.paramWord k := fun k hk =>
    (hBp.2.2.2 _ (by omega)).trans (hs6k k hk)
  have hBt := writeOffBtProg_spec (fl := fl) (s := s7) hw
    (hs7k 2 (by decide)) (hs7k 11 (by decide)) (hs7k 16 (by decide)) (hs7k 17 (by decide))
    (hs7k 18 (by decide)) (hs7k 21 (by decide)) (hBp.2.2.1 36 (by decide) (by decide))
  have hs8k : ∀ k ≤ 28, s8.mem (fl.pBase + k) = fl.paramWord k := fun k hk =>
    (hBt.2.2.2 _ (by omega)).trans (hs7k k hk)
  have hTP := writeOffTriePageProg_spec (fl := fl) (s := s8) hth hw
    (by have h0 := hs8k 0 (by decide); simpa only [add_zero, FastEpochLayout.paramWord] using h0)
    (hs8k 2 (by decide)) (hs8k 7 (by decide)) (hs8k 10 (by decide))
    (hs8k 22 (by decide)) (hs8k 23 (by decide)) (hBt.2.2.1 39 (by decide) (by decide))
  have hbwhp_eq : logN - 12 * ell = bWhp fl.N := rfl
  have hmc_eq : memoryCost (writeLargeParamTableProg ((base, fl.pBase),
      ((fl.N, fl.metaBase), ((logN, ell), pgB)))) s = 89 := by
    unfold writeLargeParamTableProg
    dsimp only
    rw [hbwhp_eq]
    rw [Realization.memoryCost_bind', hA.2.1]
    change 12 + memoryCost _ s1 = 89
    rw [Realization.memoryCost_bind', hB.2.1]
    change 12 + (8 + memoryCost _ s2) = 89
    rw [Realization.memoryCost_bind', hC.2.1]
    change 12 + (8 + (5 + memoryCost _ s3)) = 89
    rw [Realization.memoryCost_bind', hD.2.1]
    change 12 + (8 + (5 + (5 + memoryCost _ s4))) = 89
    rw [Realization.memoryCost_bind', hE.2.1]
    change 12 + (8 + (5 + (5 + (11 + memoryCost _ s5)))) = 89
    rw [Realization.memoryCost_bind', hH.2.1]
    change 12 + (8 + (5 + (5 + (11 + (12 + memoryCost _ s6))))) = 89
    rw [Realization.memoryCost_bind', hBp.2.1]
    change 12 + (8 + (5 + (5 + (11 + (12 + (13 + memoryCost _ s7)))))) = 89
    rw [Realization.memoryCost_bind', hBt.2.1]
    change 12 + (8 + (5 + (5 + (11 + (12 + (13 + (10 + memoryCost _ s8))))))) = 89
    rw [hTP.2.2.1]
  have hseq_st : ∀ {α : Type} (q1 q2 q3 q4 q5 q6 q7 q8 : Memory.Prog Unit)
      (q9 : Memory.Prog α) (st : Memory.State),
      (Memory.spec 0).clientState st (do q1; q2; q3; q4; q5; q6; q7; q8; q9) =
        (Memory.spec 0).clientState
          ((Memory.spec 0).clientState
            ((Memory.spec 0).clientState
              ((Memory.spec 0).clientState
                ((Memory.spec 0).clientState
                  ((Memory.spec 0).clientState
                    ((Memory.spec 0).clientState
                      ((Memory.spec 0).clientState
                        ((Memory.spec 0).clientState st q1) q2) q3) q4) q5) q6) q7) q8) q9 := by
    intro α q1 q2 q3 q4 q5 q6 q7 q8 q9 st
    repeat rw [StateTransitionSpec.clientState_bind]
  have hseq_res : ∀ {α : Type} (q1 q2 q3 q4 q5 q6 q7 q8 : Memory.Prog Unit)
      (q9 : Memory.Prog α) (st : Memory.State),
      (Memory.spec 0).clientResult st (do q1; q2; q3; q4; q5; q6; q7; q8; q9) =
        (Memory.spec 0).clientResult
          ((Memory.spec 0).clientState
            ((Memory.spec 0).clientState
              ((Memory.spec 0).clientState
                ((Memory.spec 0).clientState
                  ((Memory.spec 0).clientState
                    ((Memory.spec 0).clientState
                      ((Memory.spec 0).clientState
                        ((Memory.spec 0).clientState st q1) q2) q3) q4) q5) q6) q7) q8) q9 := by
    intro α q1 q2 q3 q4 q5 q6 q7 q8 q9 st
    repeat rw [StateTransitionSpec.clientResult_bind]
  have hst_eq : (Memory.spec 0).clientState s (writeLargeParamTableProg ((base, fl.pBase),
      ((fl.N, fl.metaBase), ((logN, ell), pgB)))) = s9 := by
    change (Memory.spec 0).clientState s (do
      writeCoreAProg ((base, fl.pBase), ((fl.N, fl.metaBase), logN))
      writeCoreBProg ((base, fl.pBase), (logN, ell))
      writeCoreCProg ((fl.pBase, fl.N), (logN - 12 * ell, ell))
      writeCoreDProg (fl.pBase, (logN, ell))
      writeCoreEProg ((base, fl.pBase), ell)
      writeOffHashProg fl.pBase
      writeOffBpProg fl.pBase
      writeOffBtProg fl.pBase
      writeOffTriePageProg (fl.pBase, pgB)) = s9
    rw [hseq_st, hbwhp_eq]
  have hres_eq : (Memory.spec 0).clientResult s (writeLargeParamTableProg ((base, fl.pBase),
      ((fl.N, fl.metaBase), ((logN, ell), pgB)))) =
      (Memory.spec 0).clientResult s8 (writeOffTriePageProg (fl.pBase, pgB)) := by
    change (Memory.spec 0).clientResult s (do
      writeCoreAProg ((base, fl.pBase), ((fl.N, fl.metaBase), logN))
      writeCoreBProg ((base, fl.pBase), (logN, ell))
      writeCoreCProg ((fl.pBase, fl.N), (logN - 12 * ell, ell))
      writeCoreDProg (fl.pBase, (logN, ell))
      writeCoreEProg ((base, fl.pBase), ell)
      writeOffHashProg fl.pBase
      writeOffBpProg fl.pBase
      writeOffBtProg fl.pBase
      writeOffTriePageProg (fl.pBase, pgB)) = _
    rw [hseq_res, hbwhp_eq]
  refine ⟨hres_eq.trans hTP.1, by rw [hst_eq, hTP.2.1, hBt.1, hBp.1, hH.1, hE.1, hD.1, hC.1, hB.1,
    hA.1], hmc_eq, fun k hk => ?_, ?_, ?_, fun a ha => ?_⟩
  · rw [hst_eq]
    by_cases h40 : 40 ≤ k
    · by_cases h45 : k ≤ 45
      · exact hTP.2.2.2.1 k h40 h45
      · rw [hTP.2.2.2.2 _ (by omega), hBt.2.2.2 _ (by omega), hBp.2.2.2 _ (by omega),
          hH.2.2.2.2.2.2.2 _ (by omega), hE.2.2.2 _ (by omega), hD.2.2.2 _ (by omega),
          hC.2.2.2 _ (by omega), hB.2.2.2 _ (by omega)]
        rcases (by omega : k = 46 ∨ k = 47) with rfl | rfl
        · exact hA.2.2.2.1
        · exact hA.2.2.2.2.1
    · rw [hTP.2.2.2.2 _ (by omega)]
      by_cases h37 : 37 ≤ k
      · exact hBt.2.2.1 k h37 (by omega)
      · rw [hBt.2.2.2 _ (by omega)]
        by_cases h32 : 32 ≤ k
        · exact hBp.2.2.1 k h32 (by omega)
        · rw [hBp.2.2.2 _ (by omega)]
          by_cases h29 : 29 ≤ k
          · interval_cases k
            · exact hH.2.2.1
            · exact hH.2.2.2.1
            · exact hH.2.2.2.2.1
          · exact (hH.2.2.2.2.2.2.2 _ (by omega)).trans (hs5 k (by omega))
  · rw [hst_eq, hTP.2.2.2.2 _ (by omega), hBt.2.2.2 _ (by omega), hBp.2.2.2 _ (by omega)]
    exact hH.2.2.2.2.2.1
  · rw [hst_eq, hTP.2.2.2.2 _ (by omega), hBt.2.2.2 _ (by omega), hBp.2.2.2 _ (by omega)]
    exact hH.2.2.2.2.2.2.1
  · rw [hst_eq, hTP.2.2.2.2 _ (by omega), hBt.2.2.2 _ (by omega), hBp.2.2.2 _ (by omega),
      hH.2.2.2.2.2.2.2 _ (by omega), hE.2.2.2 _ (by omega), hD.2.2.2 _ (by omega),
      hC.2.2.2 _ (by omega), hB.2.2.2 _ (by omega), hA.2.2.2.2.2 _ (by omega)]

/-- Combine `writeLargeParamTableProg_spec` with `setSlotIoProg` to produce `fl.ParamTable`. -/
theorem paramTable_of_writeLarge_and_setSlotIo {fl : FastEpochLayout} {s : Memory.State}
    (hlo : ∀ k < 48, s.mem (fl.pBase + k) = fl.paramWord k)
    (h61 : s.mem (fl.pBase + 61) = fl.paramWord 61)
    (h62 : s.mem (fl.pBase + 62) = fl.paramWord 62) :
    fl.ParamTable ((Memory.spec 0).clientState s (setSlotIoProg (fl.pBase, fl.io.toCtx))).mem := by
  have hvals := setSlotIoProg_mem_vals fl.pBase fl.io s
  have hframe := setSlotIoProg_frame fl.pBase fl.io.toCtx
  intro k hk
  by_cases h48 : k < 48
  · rw [hframe.mem_outside s (fl.pBase + k) (by omega)]; exact hlo k h48
  · by_cases h61c : k = 61
    · subst h61c; rw [hframe.mem_outside s (fl.pBase + 61) (by omega)]; exact h61
    · by_cases h62c : k = 62
      · subst h62c; rw [hframe.mem_outside s (fl.pBase + 62) (by omega)]; exact h62
      · interval_cases k
        · exact hvals.1
        · exact hvals.2.1
        · exact hvals.2.2.1
        · exact hvals.2.2.2.1
        · exact hvals.2.2.2.2.1
        · exact hvals.2.2.2.2.2.1
        · exact hvals.2.2.2.2.2.2.1
        · exact hvals.2.2.2.2.2.2.2.1
        · exact hvals.2.2.2.2.2.2.2.2.1
        · exact hvals.2.2.2.2.2.2.2.2.2.1
        · exact hvals.2.2.2.2.2.2.2.2.2.2.1
        · exact hvals.2.2.2.2.2.2.2.2.2.2.2.1
        · exact hvals.2.2.2.2.2.2.2.2.2.2.2.2
        · contradiction
        · contradiction

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
