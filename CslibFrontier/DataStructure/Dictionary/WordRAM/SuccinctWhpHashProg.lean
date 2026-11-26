/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg
import CslibFrontier.Tactic.Realize

/-!
# Certified `Memory.Prog` Hash, Feistel Quotient, and Salted Fingerprint Subroutines

This module builds parameter-free `Memory.Prog` subroutines over `Basis.exact` (certified with zero
local work via `realize`) for all hash and one-round Feistel operations used by the WHP succinct
dynamic dictionary (`SuccinctWhpModel` and `SuccinctWhpFallback`):

1. Frontier-independent `Realizes .exact` wrappers around `BitPackedDoubleTabulation`'s 4-limb
   `oddMulModWord` universe reduction and bit-packed double tabulation loop (`outerLoopGenProg`).
2. `HashRt` and `mkHashRtGenProg`: compact 38-word runtime parameter bundle extracted from the
   101-word `(WhpParams, base)` input.
3. `bktHashRtProg`, `feistelSplitRtProg`, `feistelReconstructRtProg`, `fpReducedKeyOptRtProg`,
   `fpOfSaltOptRtProg`, `rKeyOfQuotRtProg`, and `fpOfQuotRtProg`: exact `Memory.Prog` refinements of
   `bktHash`, `(feistelBucket, keyQuotient)`, `feistelReconstruct`, `fpReducedKey`, `fpOfSalt`,
   `FastState.rKeyAt`, and `FastState.fpAt` under `SeedWhpMemRep`, each running in `O_c(1)`
   worst-case memory operations without mutating memory.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.HashRt`, `mkHashRt`, `mkHashRtGenProg`,
  `hashEvalCostWhp`: compact hash runtime parameter tuple and `c`-only cost bound.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.feistelSplitRtProg`,
  `fpReducedKeyOptRtProg`, `fpOfSaltOptRtProg`, `rKeyOfQuotRtProg`,
  `fpOfQuotRtProg`: certified `Memory.Prog` hash and Feistel subroutines.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_feistelSplitRt`,
  `realizes_fpReducedKeyOptRt`, `realizes_fpOfSaltOptRt`, `realizes_rKeyOfQuotRt`,
  `realizes_fpOfQuotRt`: parameter-free `Realizes .exact` certificates.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.feistelSplitRtProg_spec`,
  `fpReducedKeyOptRtProg_spec`, `fpOfSaltOptRtProg_spec`, `rKeyOfQuotRtProg_spec`,
  `fpOfQuotRtProg_spec`:
  exact functional refinement, state preservation, `O_c(1)` `memoryCost`, and `ValidProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.Probability

/-! ## Section 1: Frontier-Independent `stage1RedGenProg` and `evalHashGenProg` -/

/-- `c`-only worst-case `memoryCost` bound for a full bit-packed double-tabulation evaluation. -/
@[expose] def hashEvalCostWhp (c : ℕ) : ℕ :=
  1 + 2 * dTabWhp c * (cTabWhp c + 2)

/-- Precondition for `stage1RedGenProg` (`d = (hp, (hBase, u_val))`), avoiding any `s.frontier`
obligation inside `Realizes`. -/
private def Stage1RedPre (w : ℕ) (d : HashParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  HashEnv w d.1 d.2.1 ∧
  s.mem d.2.1 ≤ hpMaskM d.1 ∧
  d.2.2 ≤ (hpMaskM d.1 <<< 1) + 1

/-- Parameter-free Stage-1 4-limb `oddMulModWord` universe reduction (`d = (hp, (hBase, u_val))`).
-/
@[irreducible] private def stage1RedGenProg (d : HashParams × (ℕ × ℕ)) : Memory.Prog ℕ := do
  let α_val ← Memory.read d.2.1
  let x' ← pure (d.2.2 &&& hpMaskM d.1)
  let α₀ ← pure (α_val &&& hpMaskHalf d.1)
  let α₁ ← pure (α_val >>> hpHalfM d.1)
  let x₀ ← pure (x' &&& hpMaskHalf d.1)
  let x₁ ← pure (x' >>> hpHalfM d.1)
  let p₀ ← pure ((α₀ * x₀) &&& hpMaskM d.1)
  let p₁ ← pure (((α₀ * x₁) &&& hpMaskRem d.1) <<< hpHalfM d.1)
  let p₂ ← pure (((α₁ * x₀) &&& hpMaskRem d.1) <<< hpHalfM d.1)
  let p₃ ← pure (((α₁ &&& hpMaskTop d.1) * (x₁ &&& hpMaskTop d.1)) <<< hpTwoHalfM d.1)
  let s₁ ← pure ((p₀ + p₁) &&& hpMaskM d.1)
  let s₂ ← pure ((s₁ + p₂) &&& hpMaskM d.1)
  let hm ← pure ((s₂ + p₃) &&& hpMaskM d.1)
  let one_v ← pure 1
  pure (((d.2.2 &&& one_v) +
    ((((d.2.2 >>> one_v) + hm) &&& hpMaskM d.1) <<< one_v)) >>> hpShiftR d.1)

private theorem realizes_stage1RedGen :
    Realizes .exact stage1RedGenProg
      (WordEncoding.encode (α := HashParams × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      Stage1RedPre
      (fun _ _ => 0) := by
  unfold stage1RedGenProg
  realize
  all_goals (
    rcases d with ⟨hp, hBase, u_val⟩
    obtain ⟨henv, hα_le, hu_le⟩ := h
    obtain ⟨w₀, R, c_tab, d_par, b_char, M_out, hw, hw₀, hw₀_le, _, _, _, _, _, _, hfit_sp,
      heq_hp⟩ := henv
    subst heq_hp
    simp only [hpHalfM_mk, hpTwoHalfM_mk, hpMaskM_mk, hpMaskHalf_mk, hpMaskRem_mk,
      hpMaskTop_mk] at *
    have hα_lt : s.mem hBase < 2 ^ (w₀ - 1) := by
      have : 1 ≤ 2 ^ (w₀ - 1) := Nat.one_le_two_pow; omega
    have hu_lt : u_val < 2 ^ w₀ := by
      rw [Nat.shiftLeft_eq, pow_one] at hu_le
      have hpow : 2 * 2 ^ (w₀ - 1) = 2 ^ w₀ := by rw [← pow_succ', Nat.sub_add_cancel hw₀]
      have : 1 ≤ 2 ^ (w₀ - 1) := Nat.one_le_two_pow; omega
    have hpow : 2 ^ w₀ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos hw₀_le
    obtain ⟨h1, h2, h3, h4, h5, _, h7, h8, h9, h10, h11, _, h13⟩ :=
      oddMulModWord_parts_lt hw₀ hα_lt hu_lt
    change _ < 2 ^ w
    first
    | exact h1.trans_le hpow | exact h2.trans_le hpow | exact h3.trans_le hpow
    | exact h4.trans_le hpow | exact h5.trans_le hpow | exact h7.trans_le hpow
    | exact h8.trans_le hpow | exact h9.trans_le hpow | exact h10.trans_le hpow
    | exact h11.trans_le hpow | exact h13.trans_le hpow
    | exact Nat.one_lt_two_pow hw.ne'
  )

private theorem stage1RedGenProg_spec {U w w₀ R c_tab d b_char M_out hBase F : ℕ}
    {θ : BitPackedDoubleTabulation.Seed w₀ c_tab d b_char M_out} {s : Memory.State}
    (hw₀ : 0 < w₀) (hh_lt : hBase < F)
    (hrep : BitPackedDoubleTabulation.SeedRep hBase w w₀ c_tab d b_char M_out θ s.mem)
    (u : Fin U) :
    let prog := stage1RedGenProg (mkHashParams w w₀ R c_tab d b_char M_out, (hBase, u.val))
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (multiplyShiftReduced U w₀ R θ.1 u).val ∧
    memoryCost prog s = 1 ∧
    ValidProg w F s prog := by
  have hrkey_eq : oddMulModWord w₀ (s.mem hBase) u.val >>> (w₀ - R) =
      (multiplyShiftReduced U w₀ R θ.1 u).val :=
    hrep.1.symm ▸ oddMulModWord_shiftRight_eq_multiplyShiftReduced hw₀ θ.1 u
  unfold stage1RedGenProg
  simp only [pure_bind, hpMaskM_mk, hpMaskHalf_mk, hpHalfM_mk, hpMaskRem_mk, hpMaskTop_mk,
    hpTwoHalfM_mk, hpShiftR_mk]
  exact ⟨rfl, hrkey_eq, rfl, validProg_bind (validProg_read hh_lt) (validProg_pure _)⟩

/-- Precondition for `evalHashGenProg` (`d = (hp, ((hBase, salt), u_val))`), without `s.frontier`.
-/
private def EvalHashPre (w : ℕ) (d : HashParams × ((ℕ × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  HashEnv w d.1 d.2.1.1 ∧
  s.mem d.2.1.1 ≤ hpMaskM d.1 ∧
  d.2.1.2 < hpPowB d.1 ∧
  d.2.2 ≤ (hpMaskM d.1 <<< 1) + 1

/-- Frontier-free wrapper equivalent to `BitPackedDoubleTabulation.evalGenProg`. -/
@[irreducible] private def evalHashGenProg (d : HashParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog ℕ := do
  let rKey ← stage1RedGenProg (d.1, (d.2.1.1, d.2.2))
  let zero_v ← pure 0
  let out ← BitPackedDoubleTabulation.outerLoopGenProg
    (((d.1, (d.2.1.1, (d.2.1.2, rKey))), (zero_v, zero_v)), hpD d.1)
  pure out.2

private theorem evalHashGenProg_eq_evalGenProg (d : HashParams × ((ℕ × ℕ) × ℕ)) :
    evalHashGenProg d = BitPackedDoubleTabulation.evalGenProg d := by
  unfold evalHashGenProg stage1RedGenProg BitPackedDoubleTabulation.evalGenProg
  simp only [pure_bind, bind_assoc]

private theorem realizes_evalHashGen :
    Realizes .exact evalHashGenProg
      (WordEncoding.encode (α := HashParams × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ℕ))
      EvalHashPre
      (fun _ _ => 0) := by
  have hpre : EvalHashPre = BitPackedDoubleTabulation.EvalGenPre :=
    funext fun _ => funext fun ⟨_, ⟨_, _⟩, _⟩ => funext fun _ => rfl
  simpa only [funext evalHashGenProg_eq_evalGenProg, hpre] using
    BitPackedDoubleTabulation.realizes_evalGen

private theorem validWhpProg_innerLoop {w w₀ R c_tab d b_char M_out hBase F j : ℕ}
    (hw : 0 < w) (hj : j < d)
    (hseg : hBase + BitPackedDoubleTabulation.space w c_tab d b_char M_out ≤ F) :
    let hp := mkHashParams w w₀ R c_tab d b_char M_out
    ∀ m i y r (s : Memory.State), i + m ≤ c_tab →
      ValidProg w F s (BitPackedDoubleTabulation.innerLoopGenProg
        (((hp, (hBase, j)), ((i, y), r)), m)) ∧
      (Memory.spec 0).clientState s (BitPackedDoubleTabulation.innerLoopGenProg
        (((hp, (hBase, j)), ((i, y), r)), m)) = s := by
  intro hp m
  have htop_seg : hBase + 1 +
      packedWords (BitPackedDoubleTabulation.topEntries c_tab d b_char) b_char w ≤ F := by
    unfold BitPackedDoubleTabulation.space BitPackedDoubleTabulation.topWords at hseg
    omega
  induction m with
  | zero => exact fun _ _ _ _ _ => ⟨validProg_pure _, rfl⟩
  | succ m ih =>
    intro i y r s him
    have hch_lt : r &&& (2 ^ b_char - 1) < 2 ^ b_char :=
      Nat.and_two_pow_sub_one_eq_mod r b_char ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
    have hidx₁ : (j * (c_tab + 1) + i) * 2 ^ b_char + (r &&& (2 ^ b_char - 1)) <
        BitPackedDoubleTabulation.topEntries c_tab d b_char := by
      have h := DoubleTabulation.topAddr_lt_base_add_topWords 0 (c_tab + 1) d b_char
        ⟨i, by omega⟩ ⟨j, hj⟩ ⟨_, hch_lt⟩
      dsimp only [DoubleTabulation.topAddr, DoubleTabulation.topWords,
        BitPackedDoubleTabulation.topEntries] at h ⊢
      omega
    have hstep_vp : ValidProg w F s
        (BitPackedDoubleTabulation.innerStepGenProg ((hp, (hBase, j)), ((i, y), r))) := by
      unfold BitPackedDoubleTabulation.innerStepGenProg
      simp only [hp, pure_bind, hpMaskB_mk, hpCPlusOne_mk, hpPowB_mk, hpBChar_mk, hpW_mk]
      exact validProg_bind (validProg_readPacked hw hidx₁ htop_seg) (validProg_pure _)
    obtain ⟨hvp_m, hst_m⟩ := ih (i + 1) _ _ s (by omega)
    refine ⟨validProg_bind hstep_vp hvp_m, ?_⟩
    change (Memory.spec 0).clientState s
      (BitPackedDoubleTabulation.innerStepGenProg ((hp, (hBase, j)), ((i, y), r)) >>=
        fun x => BitPackedDoubleTabulation.innerLoopGenProg (((hp, (hBase, j)), x), m)) = s
    rwa [clientState_bind]

private theorem validWhpProg_outerLoop {w w₀ R c_tab d b_char M_out hBase F s_val rKey : ℕ}
    (henv : HashEnv w (mkHashParams w w₀ R c_tab d b_char M_out) hBase)
    (hw : 0 < w) (hs_lt : s_val < 2 ^ b_char)
    (hseg : hBase + BitPackedDoubleTabulation.space w c_tab d b_char M_out ≤ F) :
    let hp := mkHashParams w w₀ R c_tab d b_char M_out
    ∀ m j out (s : Memory.State), j + m ≤ d →
      ValidProg w F s (BitPackedDoubleTabulation.outerLoopGenProg
        ((((hp, (hBase, (s_val, rKey))), (j, out)), m))) := by
  intro hp m
  have htop_seg : hBase + 1 +
      packedWords (BitPackedDoubleTabulation.topEntries c_tab d b_char) b_char w ≤ F := by
    unfold BitPackedDoubleTabulation.space BitPackedDoubleTabulation.topWords at hseg
    omega
  have hbot_seg : hBase + BitPackedDoubleTabulation.offBot w c_tab d b_char +
      packedWords (BitPackedDoubleTabulation.botEntries d b_char) M_out w ≤ F := by
    simp only [BitPackedDoubleTabulation.space, BitPackedDoubleTabulation.offBot,
      BitPackedDoubleTabulation.botWords] at hseg ⊢
    omega
  induction m with
  | zero => exact fun _ _ _ _ => validProg_pure _
  | succ m ih =>
    intro j out s hjm
    have hj : j < d := by omega
    obtain ⟨hvp_in, hst_in⟩ := validWhpProg_innerLoop (w₀ := w₀) (R := R) (M_out := M_out)
      hw hj hseg c_tab 0 0 rKey s (Nat.zero_add _).le
    have hinv_in := BitPackedDoubleTabulation.innerLoop_invariant (s := s) henv
      (by dsimp only [hpD_mk]; exact hj) c_tab 0 0 rKey
      (by dsimp only [hpCTab_mk]; omega) (by dsimp only [hpPowB_mk]; exact Nat.two_pow_pos b_char)
    dsimp only [hpPowB_mk] at hinv_in
    have hidx_s : (j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val <
        BitPackedDoubleTabulation.topEntries c_tab d b_char := by
      have h := DoubleTabulation.topAddr_lt_base_add_topWords 0 (c_tab + 1) d b_char
        ⟨c_tab, by omega⟩ ⟨j, hj⟩ ⟨s_val, hs_lt⟩
      dsimp only [DoubleTabulation.topAddr, DoubleTabulation.topWords,
        BitPackedDoubleTabulation.topEntries] at h ⊢
      omega
    have hy_lt : ((Memory.spec 0).clientResult s
        (BitPackedDoubleTabulation.innerLoopGenProg
          (((hp, (hBase, j)), ((0, 0), rKey)), c_tab))).1.2 ^^^
        readPacked (hBase + 1) b_char w s.mem
          ((j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val) < 2 ^ b_char :=
      Nat.xor_lt_two_pow hinv_in.2.2 (readPacked_lt _ _ _ _ _)
    have hidx₂ : j * 2 ^ b_char +
        (((Memory.spec 0).clientResult s
          (BitPackedDoubleTabulation.innerLoopGenProg
            (((hp, (hBase, j)), ((0, 0), rKey)), c_tab))).1.2 ^^^
          readPacked (hBase + 1) b_char w s.mem
            ((j * (c_tab + 1) + c_tab) * 2 ^ b_char + s_val)) <
        BitPackedDoubleTabulation.botEntries d b_char := by
      calc _ < j * 2 ^ b_char + 2 ^ b_char := Nat.add_lt_add_left hy_lt _
        _ = (j + 1) * 2 ^ b_char := by ring
        _ ≤ d * 2 ^ b_char := Nat.mul_le_mul_right _ hj
    have hstep_vp : ValidProg w F s
        (BitPackedDoubleTabulation.outerStepGenProg ((hp, (hBase, (s_val, rKey))), (j, out))) := by
      unfold BitPackedDoubleTabulation.outerStepGenProg
      simp only [hp, pure_bind, hpCTab_mk, hpCPlusOne_mk, hpPowB_mk, hpBChar_mk, hpW_mk,
        hpOffBot_mk, hpMOut_mk, readPackedGenProg]
      refine validProg_bind hvp_in
        (hst_in.symm ▸ validProg_bind (validProg_readPacked hw hidx_s htop_seg) ?_)
      rw [clientState_readPackedProg, clientResult_readPackedProg]
      exact validProg_bind (validProg_readPacked hw hidx₂ hbot_seg) (validProg_pure _)
    have hstep : (Memory.spec 0).clientState s
        (BitPackedDoubleTabulation.outerStepGenProg ((hp, (hBase, (s_val, rKey))), (j, out))) =
        s ∧ ((Memory.spec 0).clientResult s
        (BitPackedDoubleTabulation.outerStepGenProg ((hp, (hBase, (s_val, rKey))), (j, out)))).1 =
        j + 1 := by
      unfold BitPackedDoubleTabulation.outerStepGenProg readPackedGenProg
      simp only [hp, pure_bind, hpCTab_mk]
      rw [clientState_bind, clientResult_bind, hst_in, clientState_bind, clientResult_bind,
        clientState_readPackedProg, clientState_bind, clientResult_bind, clientState_readPackedProg]
      exact ⟨rfl, rfl⟩
    change ValidProg w F s
      (BitPackedDoubleTabulation.outerStepGenProg ((hp, (hBase, (s_val, rKey))), (j, out)) >>=
        fun x => BitPackedDoubleTabulation.outerLoopGenProg
          (((hp, (hBase, (s_val, rKey))), x), m))
    refine validProg_bind hstep_vp ?_
    rw [hstep.1]
    exact ih _ _ s (by rw [hstep.2]; omega)

private theorem evalHashGenProg_spec {U w w₀ R c_tab d b_char M_out s_max hBase F : ℕ}
    {θ : BitPackedDoubleTabulation.Seed w₀ c_tab d b_char M_out} {s : Memory.State}
    (henv : HashEnv w (mkHashParams w w₀ R c_tab d b_char M_out) hBase)
    (hw : 0 < w) (hw₀ : 0 < w₀) (_hU_pow : U ≤ 2 ^ w₀) (hs_max : s_max ≤ 2 ^ b_char)
    (hseg : hBase + BitPackedDoubleTabulation.space w c_tab d b_char M_out ≤ F)
    (hrep : BitPackedDoubleTabulation.SeedRep hBase w w₀ c_tab d b_char M_out θ s.mem)
    (salt : Fin s_max) (u : Fin U) :
    let prog := evalHashGenProg
      (mkHashParams w w₀ R c_tab d b_char M_out, ((hBase, salt.val), u.val))
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (evalSalted U w₀ R c_tab d b_char M_out s_max θ (salt, u)).val ∧
    memoryCost prog s = 1 + 2 * d * (c_tab + 2) ∧
    ValidProg w F s prog := by
  dsimp only
  have hsp_pos := BitPackedDoubleTabulation.space_pos w c_tab d b_char M_out
  have hs1 := stage1RedGenProg_spec (R := R) hw₀ (by omega : hBase < F) hrep u
  have hol_vp := validWhpProg_outerLoop henv hw (salt.isLt.trans_le hs_max) hseg
    (rKey := (Memory.spec 0).clientResult s
      (stage1RedGenProg (mkHashParams w w₀ R c_tab d b_char M_out, (hBase, u.val))))
    d 0 0 s (Nat.zero_add _).le
  have hvp : ValidProg w F s
      (evalHashGenProg (mkHashParams w w₀ R c_tab d b_char M_out, ((hBase, salt.val), u.val))) := by
    unfold evalHashGenProg
    simp only [pure_bind, hpD_mk]
    exact validProg_bind hs1.2.2.2 (hs1.1.symm ▸ validProg_bind hol_vp (validProg_pure _))
  rw [evalHashGenProg_eq_evalGenProg] at hvp ⊢
  obtain ⟨hres, hst⟩ := BitPackedDoubleTabulation.evalProg_spec (R := R) hw₀ hs_max hrep salt u
  exact ⟨hst, hres, BitPackedDoubleTabulation.memoryCost_evalProg .., hvp⟩

/-! ## Section 2: Compact 38-Word Hash Runtime Parameter Bundle (`HashRt`) -/

/-- Compact 38-word runtime parameter bundle `(hp₁, hp₂, base, U, bWhp, maskBkt, sMax, offHashFp)`.
-/
abbrev HashRt : Type :=
  (HashParams × HashParams) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)))

private def hrHpBkt (hrt : HashRt) : HashParams := hrt.1.1
private def hrHpFp (hrt : HashRt) : HashParams := hrt.1.2
/-- Base word address extracted from `HashRt`. -/
@[expose] def hrBase (hrt : HashRt) : ℕ := hrt.2.1.1
private def hrULim (hrt : HashRt) : ℕ := hrt.2.1.2
private def hrBBits (hrt : HashRt) : ℕ := hrt.2.2.1.1
private def hrMaskBkt (hrt : HashRt) : ℕ := hrt.2.2.1.2
private def hrSMax (hrt : HashRt) : ℕ := hrt.2.2.2.1
private def hrOffFp (hrt : HashRt) : ℕ := hrt.2.2.2.2

/-- Pure constructor for `HashRt` in the large regime. -/
@[expose] def mkHashRt (c U w n_max base : ℕ) : HashRt :=
  ((mkHashParams w (w0Whp U) (rRedWhp c n_max)
      (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max),
    mkHashParams w (w0Whp U) (rRedWhp c n_max)
      (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max)),
   ((base, U), ((bWhp n_max, numBucketsWhp n_max - 1), (sMaxWhp c n_max, offHashFp c w n_max))))

/-- Runtime envelope for `hrt : HashRt` coupled with `SeedWhpMemRep`. -/
@[expose] def HashRtEnv (w : ℕ) (hrt : HashRt) (s : Memory.State) : Prop :=
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max),
    WhpLargeEnv c U V w₀ n_max w (hrBase hrt) ∧
    hrt = mkHashRt c U w₀ n_max (hrBase hrt) ∧
    SeedWhpMemRep (hrBase hrt) c U w₀ n_max θ s.mem

/-- Extract `HashRt` from `(wp, base) : WhpParams × ℕ` in 0 memory operations. -/
@[irreducible] def mkHashRtGenProg : WhpParams × ℕ → Memory.Prog HashRt
  | ((cp, hps), base) => do
    let uLim ← pure (wpU cp)
    let bBits ← pure (wpBWhp cp)
    let maskBkt ← pure (wpMaskBkt cp)
    let sMax ← pure (wpSMax cp)
    let offFp ← pure (wpOffHashFp cp)
    pure (hps, ((base, uLim), ((bBits, maskBkt), (sMax, offFp))))

theorem realizes_mkHashRtGen :
    Realizes .exact mkHashRtGenProg
      (WordEncoding.encode (α := WhpParams × ℕ))
      (WordEncoding.encode (α := HashRt))
      (fun _ _ _ => True)
      (fun _ _ => 0) := by
  unfold mkHashRtGenProg
  realize

theorem mkHashRtGenProg_spec {c U V w n_max base : ℕ} (hth : whpThreshold c ≤ n_max)
    (s : Memory.State) :
    let prog := mkHashRtGenProg (mkWhpParams c U V w n_max, base)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = mkHashRt c U w n_max base ∧
    memoryCost prog s = 0 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  unfold mkHashRtGenProg
  simp only [pure_bind]
  have hwp : mkWhpParams c U V w n_max =
      (mkWhpCoreParams c U V w n_max,
       (mkHashParams w (w0Whp U) (rRedWhp c n_max)
          (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max),
        mkHashParams w (w0Whp U) (rRedWhp c n_max)
          (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max))) := by
    unfold mkWhpParams; exact ite_eq_right (Nat.not_lt.mpr hth)
  rw [hwp, wp_large_U hth, wp_large_bWhp hth, wp_large_maskBkt hth, wp_large_sMax hth,
    wp_large_offHashFp hth]
  exact ⟨rfl, rfl, rfl, validProg_pure _⟩

/-- A key below `U` meets the stage-1 input bound `(2 ^ (w0Whp U - 1) - 1) <<< 1 + 1`. -/
private theorem le_maskM_shiftLeft_of_lt {U x : ℕ} (hx : x < U) :
    x ≤ ((2 ^ (w0Whp U - 1) - 1) <<< 1) + 1 := by
  have hpow : 2 * 2 ^ (w0Whp U - 1) = 2 ^ w0Whp U := by
    rw [← pow_succ', Nat.sub_add_cancel (w0Whp_pos U)]
  have : 1 ≤ 2 ^ (w0Whp U - 1) := Nat.one_le_two_pow
  have := hx.trans_le (le_two_pow_w0Whp U)
  rw [Nat.shiftLeft_eq, pow_one]
  omega

private theorem hashRt_segments_le {c U V w n_max base : ℕ} :
    base + offHashBkt +
      BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max) ≤
      base + largeSpaceWhp c U V w n_max ∧
    base + offHashFp c w n_max +
      BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max)
        (fpBitsWhp n_max) ≤
      base + largeSpaceWhp c U V w n_max ∧
    base + offHashFp c w n_max < base + largeSpaceWhp c U V w n_max := by
  have hsp2 := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
    (bCharWhp n_max) (fpBitsWhp n_max)
  have hch := largeOffsetChain c U V w n_max
  exact ⟨by omega, by omega, by omega⟩

/-! ## Section 3: Certified `bktHash`, Feistel Split/Reconstruct, `fpReducedKey`, `fpOfSalt` -/

/-- Compute `bktHash c U n_max θ.1 q` (`d = (hrt, q)`, works for any `q : ℕ`). -/
@[irreducible] private def bktHashRtProg (d : HashRt × ℕ) : Memory.Prog ℕ := do
  let hrt := d.1
  let q ← pure d.2
  let uLim ← pure (hrULim hrt)
  if q < uLim then
    let off32 ← pure 32
    let hBaseBkt ← pure (hrBase hrt + off32)
    let zero_v ← pure 0
    evalHashGenProg (hrHpBkt hrt, ((hBaseBkt, zero_v), q))
  else
    pure 0

private theorem realizes_bktHashRt :
    Realizes .exact bktHashRtProg
      (WordEncoding.encode (α := HashRt × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => HashRtEnv w d.1 s)
      (fun _ _ => 0) := by
  unfold bktHashRtProg
  realize [realizes_evalHashGen]
  all_goals (
    rcases d with ⟨hrt, q⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed⟩ := h
    have hth := henv.2.2.2.1
    have hw := henv.2.1
    obtain rfl := henv.2.2.1
    have hU_eq : hrULim hrt = U := congrArg hrULim heq_hrt
    obtain ⟨henv1, _⟩ := hashEnvs_of_large hw hth henv.2.2.2.2.1 henv.2.2.2.2.2.1 henv.2.2.2.2.2.2.2
    dsimp only [hrBase] at *
    try exact henv.fits_const (by decide)
  )
  · refine henv.fits_largeSpace.of_le ?_
    have hseg1 := (hashRt_segments_le (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
      (base := hrt.2.1.1)).1
    have hsp1 := BitPackedDoubleTabulation.space_pos w (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (bWhp n_max)
    dsimp only [offHashBkt] at hseg1
    omega
  · dsimp only [EvalHashPre]
    rw [congrArg hrHpBkt heq_hrt]
    dsimp only [hrHpBkt, mkHashRt, offHashBkt, hpMaskM_mk] at henv1 ⊢
    refine ⟨henv1, ?_, by simp [hpPowB_mk], le_maskM_shiftLeft_of_lt (by rwa [← hU_eq])⟩
    exact (hseed.1.1 : s.mem (hrt.2.1.1 + offHashBkt) = _) ▸ Nat.le_sub_one_of_lt θ.1.1.isLt

private theorem bktHashRtProg_spec {c U V w n_max base q : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := bktHashRtProg (mkHashRt c U w n_max base, q)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = bktHash c U n_max θ.1 q ∧
    memoryCost prog s ≤ hashEvalCostWhp c ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  obtain ⟨henv1, _⟩ := hashEnvs_of_large hw hth henv.2.2.2.2.1 henv.2.2.2.2.2.1 henv.2.2.2.2.2.2.2
  have hseg1 := (hashRt_segments_le (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
    (base := base)).1
  dsimp only
  unfold bktHashRtProg bktHash
  simp only [pure_bind, mkHashRt, hrULim, hrBase, hrHpBkt]
  split_ifs with hq
  · obtain ⟨hst, hres, hmc, hvp⟩ := evalHashGenProg_spec henv1 hw (w0Whp_pos U)
      (le_two_pow_w0Whp U) Nat.one_le_two_pow hseg1 hseed.1 ⟨0, Nat.zero_lt_one⟩ ⟨q, hq⟩
    exact ⟨hst, hres, hmc.le, hvp⟩
  · exact ⟨rfl, rfl, Nat.zero_le _, validProg_pure 0⟩

/-- Split any `u_val : ℕ` into `(feistelBucket, keyQuotient)`. -/
@[irreducible] def feistelSplitRtProg (d : HashRt × ℕ) : Memory.Prog (ℕ × ℕ) := do
  let hrt := d.1
  let u_val ← pure d.2
  let q ← pure (u_val >>> hrBBits hrt)
  let low ← pure (u_val &&& hrMaskBkt hrt)
  let h ← bktHashRtProg (hrt, q)
  let h_low ← pure (h &&& hrMaskBkt hrt)
  let b ← pure (h_low ^^^ low)
  pure (b, q)

theorem realizes_feistelSplitRt :
    Realizes .exact feistelSplitRtProg
      (WordEncoding.encode (α := HashRt × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w d s => HashRtEnv w d.1 s)
      (fun _ _ => 0) := by
  unfold feistelSplitRtProg
  realize [realizes_bktHashRt]
  all_goals (
    rcases d with ⟨hrt, u_val⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed⟩ := h
    obtain rfl := henv.2.2.1
    have hM_lt : numBucketsWhp n_max < 2 ^ w :=
      henv.numBuckets_le_n_max.trans_lt (henv.2.2.2.2.1.trans_lt henv.2.2.2.2.2.1)
    first
    | exact ⟨c, U, V, w, n_max, θ, henv, heq_hrt, hseed⟩
    | (rw [heq_hrt]; dsimp only [mkHashRt, hrMaskBkt, numBucketsWhp]
       rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
       exact (Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _))
         (Nat.mod_lt _ (Nat.two_pow_pos _))).trans hM_lt)
  )

theorem feistelSplitRtProg_spec {c U V w n_max base u_val : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := feistelSplitRtProg (mkHashRt c U w n_max base, u_val)
    let q := keyQuotient (bWhp n_max) u_val
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (b, q) ∧
    memoryCost prog s ≤ hashEvalCostWhp c ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  set q := u_val >>> bWhp n_max
  obtain ⟨hst, hres, hmc, hvp⟩ := bktHashRtProg_spec (q := q) henv hseed (s := s)
  have hq_eq : q = keyQuotient (bWhp n_max) u_val := Nat.shiftRight_eq_div_pow u_val (bWhp n_max)
  dsimp only
  unfold feistelSplitRtProg
  have hrt_eq : hrBBits (mkHashRt c U w n_max base) = bWhp n_max ∧
      hrMaskBkt (mkHashRt c U w n_max base) = numBucketsWhp n_max - 1 := ⟨rfl, rfl⟩
  simp only [pure_bind, hrt_eq.1, hrt_eq.2]
  refine ⟨by rw [clientState_bind, hst]; rfl, ?_, ?_,
    validProg_bind hvp (hst ▸ validProg_pure _)⟩
  · rw [clientResult_bind, hst, hres, StateTransitionSpec.clientResult_pure]
    apply Prod.ext
    · unfold feistelBucket keyLow numBucketsWhp
      rw [← hq_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
    · exact hq_eq
  · simpa only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, memoryCost_pure,
      Nat.add_zero] using hmc

/-- Reconstruct key `feistelReconstruct (bWhp n_max) (bktHash ...) b q` (`d = ((hrt, b), q)` with
`q < 2 ^ quotBitsWhp U n_max`). -/
@[irreducible] private def feistelReconstructRtProg : (HashRt × ℕ) × ℕ → Memory.Prog ℕ
  | ((hrt, b_in), q_in) => do
    let b ← pure b_in
    let q ← pure q_in
    let h ← bktHashRtProg (hrt, q)
    let h_low ← pure (h &&& hrMaskBkt hrt)
    let b_low ← pure (b &&& hrMaskBkt hrt)
    let low ← pure (h_low ^^^ b_low)
    let hi ← pure (q <<< hrBBits hrt)
    pure (hi + low)

/-- Precondition for subroutines taking a stored quotient `q < 2 ^ quotBitsWhp U n_max`. -/
@[expose] def QuotHashRtEnv (w : ℕ) (hrt : HashRt) (q : ℕ) (s : Memory.State) : Prop :=
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max),
    WhpLargeEnv c U V w₀ n_max w (hrBase hrt) ∧
    hrt = mkHashRt c U w₀ n_max (hrBase hrt) ∧
    SeedWhpMemRep (hrBase hrt) c U w₀ n_max θ s.mem ∧
    q < 2 ^ quotBitsWhp U n_max

private theorem realizes_feistelReconstructRt :
    Realizes .exact feistelReconstructRtProg
      (WordEncoding.encode (α := (HashRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((hrt, _), q) s => QuotHashRtEnv w hrt q s)
      (fun _ _ => 0) := by
  unfold feistelReconstructRtProg
  realize [realizes_bktHashRt]
  all_goals (
    rcases d with ⟨⟨hrt, b⟩, q⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed, hq_lt⟩ := h
    obtain rfl := henv.2.2.1
    have hnU := henv.2.2.2.2.1
    have hU := henv.2.2.2.2.2.1
    have hM_lt : numBucketsWhp n_max < 2 ^ w :=
      henv.numBuckets_le_n_max.trans_lt (hnU.trans_lt hU)
    have hkb_w : 2 ^ keyBits U ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (keyBits_le_w hU)
    have hsplit := quotBitsWhp_add_bWhp hnU
    have hhi_add_lt : ∀ low < 2 ^ bWhp n_max, q * 2 ^ bWhp n_max + low < 2 ^ w := by
      intro low hlow
      calc q * 2 ^ bWhp n_max + low
          < q * 2 ^ bWhp n_max + 2 ^ bWhp n_max := Nat.add_lt_add_left hlow _
        _ = (q + 1) * 2 ^ bWhp n_max := by ring
        _ ≤ 2 ^ quotBitsWhp U n_max * 2 ^ bWhp n_max := Nat.mul_le_mul_right _ hq_lt
        _ = 2 ^ keyBits U := by rw [← Nat.pow_add, hsplit]
        _ ≤ 2 ^ w := hkb_w
    first
    | exact ⟨c, U, V, w, n_max, θ, henv, heq_hrt, hseed⟩
    | (rw [heq_hrt]; dsimp only [mkHashRt, hrMaskBkt, hrBBits, numBucketsWhp, Fits]
       first
       | (rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
          exact (Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _))
            (Nat.mod_lt _ (Nat.two_pow_pos _))).trans hM_lt)
       | (rw [Nat.shiftLeft_eq]
          exact (Nat.le_add_right _ 0).trans_lt (hhi_add_lt 0 (Nat.two_pow_pos _)))
       | (rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
          exact hhi_add_lt _ (Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _))
            (Nat.mod_lt _ (Nat.two_pow_pos _)))))
  )

private theorem feistelReconstructRtProg_spec {c U V w n_max base b q : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := feistelReconstructRtProg ((mkHashRt c U w n_max base, b), q)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b q ∧
    memoryCost prog s ≤ hashEvalCostWhp c ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hst, hres, hmc, hvp⟩ := bktHashRtProg_spec (q := q) henv hseed (s := s)
  dsimp only
  unfold feistelReconstructRtProg
  have hrt_eq : hrMaskBkt (mkHashRt c U w n_max base) = numBucketsWhp n_max - 1 ∧
      hrBBits (mkHashRt c U w n_max base) = bWhp n_max := ⟨rfl, rfl⟩
  simp only [pure_bind, hrt_eq.1, hrt_eq.2]
  refine ⟨by rw [clientState_bind, hst]; rfl, ?_, ?_,
    validProg_bind hvp (hst ▸ validProg_pure _)⟩
  · rw [clientResult_bind, hst, hres, StateTransitionSpec.clientResult_pure]
    unfold feistelReconstruct numBucketsWhp
    rw [Nat.shiftLeft_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  · simpa only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, memoryCost_pure,
      Nat.add_zero] using hmc

/-- Compute `if h : kv < U then fpReducedKey c U n_max θ.2 ⟨kv, h⟩ else 0` (`d = (hrt, kv)`). -/
@[irreducible] def fpReducedKeyOptRtProg (d : HashRt × ℕ) : Memory.Prog ℕ := do
  let hrt := d.1
  let kv ← pure d.2
  let uLim ← pure (hrULim hrt)
  if kv < uLim then
    let hBaseFp ← pure (hrBase hrt + hrOffFp hrt)
    stage1RedGenProg (hrHpFp hrt, (hBaseFp, kv))
  else
    pure 0

theorem realizes_fpReducedKeyOptRt :
    Realizes .exact fpReducedKeyOptRtProg
      (WordEncoding.encode (α := HashRt × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => HashRtEnv w d.1 s)
      (fun _ _ => 0) := by
  unfold fpReducedKeyOptRtProg
  realize [realizes_stage1RedGen]
  all_goals (
    rcases d with ⟨hrt, kv⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed⟩ := h
    have hth := henv.2.2.2.1
    have hw := henv.2.1
    obtain rfl := henv.2.2.1
    have hU_eq : hrULim hrt = U := congrArg hrULim heq_hrt
    have hOff_eq : hrOffFp hrt = offHashFp c w n_max := congrArg hrOffFp heq_hrt
    obtain ⟨_, henv2⟩ := hashEnvs_of_large hw hth henv.2.2.2.2.1 henv.2.2.2.2.2.1 henv.2.2.2.2.2.2.2
    dsimp only [hrBase] at *
  )
  · rw [hOff_eq]
    exact henv.fits_largeSpace.of_le (hashRt_segments_le (c := c) (U := U) (V := V) (w := w)
      (n_max := n_max) (base := hrt.2.1.1)).2.2.le
  · dsimp only [Stage1RedPre]
    rw [hOff_eq, congrArg hrHpFp heq_hrt]
    dsimp only [hrHpFp, mkHashRt, hpMaskM_mk]
    exact ⟨henv2, hseed.2.1 ▸ Nat.le_sub_one_of_lt θ.2.1.isLt,
      le_maskM_shiftLeft_of_lt (by rwa [← hU_eq])⟩

theorem fpReducedKeyOptRtProg_spec {c U V w n_max base kv : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (_henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := fpReducedKeyOptRtProg (mkHashRt c U w n_max base, kv)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if h : kv < U then fpReducedKey c U n_max θ.2 ⟨kv, h⟩ else 0) ∧
    memoryCost prog s ≤ 1 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hh_lt := (hashRt_segments_le (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
    (base := base)).2.2
  dsimp only
  unfold fpReducedKeyOptRtProg
  simp only [pure_bind, mkHashRt, hrULim, hrBase, hrOffFp, hrHpFp]
  split_ifs with hkv
  · obtain ⟨hst, hres, hmc, hvp⟩ :=
      stage1RedGenProg_spec (R := rRedWhp c n_max) (w0Whp_pos U) hh_lt hseed.2 ⟨kv, hkv⟩
    exact ⟨hst, hres, hmc.le, hvp⟩
  · exact ⟨rfl, rfl, Nat.zero_le 1, validProg_pure 0⟩

/-- Compute `if hs : salt < sMaxWhp then if hu : kv < U then fpHash θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
else 0` (`d = ((hrt, salt), kv)`). -/
@[irreducible] def fpOfSaltOptRtProg : (HashRt × ℕ) × ℕ → Memory.Prog ℕ
  | ((hrt, salt_in), kv_in) => do
    let salt ← pure salt_in
    let kv ← pure kv_in
    let sMax ← pure (hrSMax hrt)
    if salt < sMax then
      let uLim ← pure (hrULim hrt)
      if kv < uLim then
        let hBaseFp ← pure (hrBase hrt + hrOffFp hrt)
        evalHashGenProg (hrHpFp hrt, ((hBaseFp, salt), kv))
      else
        pure 0
    else
      pure 0

theorem realizes_fpOfSaltOptRt :
    Realizes .exact fpOfSaltOptRtProg
      (WordEncoding.encode (α := (HashRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((hrt, _), _) s => HashRtEnv w hrt s)
      (fun _ _ => 0) := by
  unfold fpOfSaltOptRtProg
  realize [realizes_evalHashGen]
  all_goals (
    rcases d with ⟨⟨hrt, salt⟩, kv⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed⟩ := h
    have hth := henv.2.2.2.1
    have hw := henv.2.1
    obtain rfl := henv.2.2.1
    have hU_eq : hrULim hrt = U := congrArg hrULim heq_hrt
    have hS_eq : hrSMax hrt = sMaxWhp c n_max := congrArg hrSMax heq_hrt
    have hOff_eq : hrOffFp hrt = offHashFp c w n_max := congrArg hrOffFp heq_hrt
    obtain ⟨_, henv2⟩ := hashEnvs_of_large hw hth henv.2.2.2.2.1 henv.2.2.2.2.2.1 henv.2.2.2.2.2.2.2
    dsimp only [hrBase] at *
  )
  · rw [hOff_eq]
    exact henv.fits_largeSpace.of_le (hashRt_segments_le (c := c) (U := U) (V := V) (w := w)
      (n_max := n_max) (base := hrt.2.1.1)).2.2.le
  · dsimp only [EvalHashPre]
    rw [hOff_eq, congrArg hrHpFp heq_hrt]
    dsimp only [hrHpFp, mkHashRt, hpMaskM_mk, hpPowB_mk]
    exact ⟨henv2, hseed.2.1 ▸ Nat.le_sub_one_of_lt θ.2.1.isLt,
      (by rwa [← hS_eq] : salt < sMaxWhp c n_max).trans_le (sMaxWhp_le_pow_bChar hth),
      le_maskM_shiftLeft_of_lt (by rwa [← hU_eq])⟩

theorem fpOfSaltOptRtProg_spec {c U V w n_max base salt kv : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := fpOfSaltOptRtProg ((mkHashRt c U w n_max base, salt), kv)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if hs : salt < sMaxWhp c n_max then
        if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
       else 0) ∧
    memoryCost prog s ≤ hashEvalCostWhp c ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  obtain ⟨_, henv2⟩ := hashEnvs_of_large hw hth henv.2.2.2.2.1 henv.2.2.2.2.2.1 henv.2.2.2.2.2.2.2
  have hseg2 := (hashRt_segments_le (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
    (base := base)).2.1
  dsimp only
  unfold fpOfSaltOptRtProg
  simp only [pure_bind, mkHashRt, hrSMax, hrULim, hrBase, hrOffFp, hrHpFp]
  split_ifs with hs hu
  · obtain ⟨hst, hres, hmc, hvp⟩ := evalHashGenProg_spec henv2 hw (w0Whp_pos U)
      (le_two_pow_w0Whp U) (sMaxWhp_le_pow_bChar hth) hseg2 hseed.2 ⟨salt, hs⟩ ⟨kv, hu⟩
    exact ⟨hst, hres, hmc.le, hvp⟩
  all_goals exact ⟨rfl, rfl, Nat.zero_le _, validProg_pure 0⟩

/-- Composite `rKey` from `(b, q)` (`d = ((hrt, b), q)` with `q < 2 ^ quotBitsWhp U n_max`),
matching `FastState.rKeyAt` when `q = fs.quotArr (fs.physSlot n_max b loc)`. -/
@[irreducible] def rKeyOfQuotRtProg : (HashRt × ℕ) × ℕ → Memory.Prog ℕ
  | ((hrt, b), q) => do
    let kv ← feistelReconstructRtProg ((hrt, b), q)
    fpReducedKeyOptRtProg (hrt, kv)

theorem realizes_rKeyOfQuotRt :
    Realizes .exact rKeyOfQuotRtProg
      (WordEncoding.encode (α := (HashRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((hrt, _), q) s => QuotHashRtEnv w hrt q s)
      (fun _ _ => 0) := by
  unfold rKeyOfQuotRtProg
  realize [realizes_feistelReconstructRt, realizes_fpReducedKeyOptRt]
  all_goals (
    rcases d with ⟨⟨hrt, b⟩, q⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed, hq_lt⟩ := h
    obtain rfl := henv.2.2.1
  )
  · exact ⟨c, U, V, w, n_max, θ, henv, heq_hrt, hseed, hq_lt⟩
  · rw [heq_hrt, (feistelReconstructRtProg_spec henv hseed).1]
    exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩

theorem rKeyOfQuotRtProg_spec {c U V w n_max base b q : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := rKeyOfQuotRtProg ((mkHashRt c U w n_max base, b), q)
    let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b q
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if h : kv < U then fpReducedKey c U n_max θ.2 ⟨kv, h⟩ else 0) ∧
    memoryCost prog s ≤ hashEvalCostWhp c + 1 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hst1, hres1, hmc1, hvp1⟩ :=
    feistelReconstructRtProg_spec (b := b) (q := q) henv hseed (s := s)
  set kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b q
  obtain ⟨hst2, hres2, hmc2, hvp2⟩ :=
    fpReducedKeyOptRtProg_spec (kv := kv) henv hseed (s := s)
  dsimp only
  unfold rKeyOfQuotRtProg
  refine ⟨by rw [clientState_bind, hst1, hres1, hst2],
    by rw [clientResult_bind, hst1, hres1, hres2], ?_,
    validProg_bind hvp1 (by rwa [hst1, hres1])⟩
  rw [memoryCost_bind_of_clientState_eq hst1, hres1]
  exact Nat.add_le_add hmc1 hmc2

/-- Composite salted fingerprint from `(((hrt, salt), b), q)` (`q < 2 ^ quotBitsWhp U n_max`),
matching `FastState.fpAt` when `q = fs.quotArr (fs.physSlot n_max b loc)`. -/
@[irreducible] def fpOfQuotRtProg : ((HashRt × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((hrt, salt), b), q) => do
    let kv ← feistelReconstructRtProg ((hrt, b), q)
    fpOfSaltOptRtProg ((hrt, salt), kv)

theorem realizes_fpOfQuotRt :
    Realizes .exact fpOfQuotRtProg
      (WordEncoding.encode (α := ((HashRt × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((hrt, _), _), q) s => QuotHashRtEnv w hrt q s)
      (fun _ _ => 0) := by
  unfold fpOfQuotRtProg
  realize [realizes_feistelReconstructRt, realizes_fpOfSaltOptRt]
  all_goals (
    rcases d with ⟨⟨⟨hrt, salt⟩, b⟩, q⟩
    dsimp only at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_hrt, hseed, hq_lt⟩ := h
    obtain rfl := henv.2.2.1
  )
  · exact ⟨c, U, V, w, n_max, θ, henv, heq_hrt, hseed, hq_lt⟩
  · rw [heq_hrt, (feistelReconstructRtProg_spec henv hseed).1]
    exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩

theorem fpOfQuotRtProg_spec {c U V w n_max base salt b q : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := fpOfQuotRtProg (((mkHashRt c U w n_max base, salt), b), q)
    let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b q
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if hs : salt < sMaxWhp c n_max then
        if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
       else 0) ∧
    memoryCost prog s ≤ 2 * hashEvalCostWhp c ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hst1, hres1, hmc1, hvp1⟩ :=
    feistelReconstructRtProg_spec (b := b) (q := q) henv hseed (s := s)
  set kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b q
  obtain ⟨hst2, hres2, hmc2, hvp2⟩ :=
    fpOfSaltOptRtProg_spec (salt := salt) (kv := kv) henv hseed (s := s)
  dsimp only
  unfold fpOfQuotRtProg
  refine ⟨by rw [clientState_bind, hst1, hres1, hst2],
    by rw [clientResult_bind, hst1, hres1, hres2], ?_,
    validProg_bind hvp1 (by rwa [hst1, hres1])⟩
  rw [memoryCost_bind_of_clientState_eq hst1, hres1, Nat.two_mul]
  exact Nat.add_le_add hmc1 hmc2

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
