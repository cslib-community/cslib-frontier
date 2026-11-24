/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.ParamsInit
public import CslibFrontier.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.Horner
public import CslibFrontier.Tactic.WramOmega.Init
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Tactic.SuppCases
import CslibFrontier.Tactic.ValidProg
import CslibFrontier.Tactic.WramOmega

/-!
# Runtime-Parameterized `ReducedKWise` Hashing on the Resizable Word RAM

Completes the parameter-free (`¬ReadsWidth`) Word-RAM / Resizable Word RAM compilation of the
two-stage universe-reduced $k$-wise independent polynomial hash family of
[BenderFarachColtonKuszmaulKuszmaul2024] (`Cslib.Probability.reducedPolyHash`):
* `evalHashGenProg`: runtime polynomial evaluation and `b'`-bit output extraction in `Memory.Prog`
  certified via `by realize` (`RealizesBounded .exact`), using `O(k)` deterministic operations and
  the 162-word scratch slice `[scratchBase, scratchBase + 162)` rather than 240 static registers;
* `resampleHashCode`: parameter-free `RCode .exact r` subroutine resampling a uniform seed
  `ReducedPolySeed w₀ b b' k` (`ExecRCodeDist`).

Re-exports `RuntimeReducedKWise.ParamsInit` (`HashParams`, `mkHashParams`, `initTableGenProg`) and
`RuntimeReducedKWise.Horner`.

## Main definitions

* `Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.evalHashGenProg`, `evalMemBound`,
  `EvalHashGenPre`: runtime `k`-wise polynomial hash evaluator in `Memory.Prog`.
* `Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise.resampleHashCode`: parameter-free
  `RCode .exact r` subroutine resampling a uniform `ReducedPolySeed w₀ b b' k`.

## Main results

* `evalHashGenProg_spec`, `realizesBounded_evalHashGen`: exact agreement with
  `Cslib.Probability.reducedPolyHash`, `O(k)` memory cost,
    and `RealizesBounded .exact` certificate.
* `not_readsWidth_resampleHashCode`, `resampleHashCode_execRCodeDist`: width-independence and
  `ExecRCodeDist` uniform seed-sampling specification on the Resizable Word RAM.

## References

* [BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.HashFamily.WordRAM Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise
open Cslib.Probability
open scoped ENNReal

local notation "rStep" => reducedTrinomialStep
local notation "rChunk" w₀:arg b:arg b':arg => reducedChunkBits (reducedTrinomialStep w₀ b b')
local notation "rHalf" w₀:arg b:arg b':arg => reducedHalfLimbs (reducedTrinomialStep w₀ b b')
local notation "rLimbs" w₀:arg b:arg b':arg => reducedLimbCount (reducedTrinomialStep w₀ b b')
local notation "rPack" w:arg w₀:arg b:arg b':arg =>
  reducedPackShift (reducedTrinomialStep w₀ b b') w

/-! ## Section 1: Output limb packing and full `evalHashGenProg` -/

private def packOutStepGenProg :
    (HashParams × ℕ) × (ℕ × ℕ × ℕ × ℕ) → Memory.Prog (ℕ × ℕ × ℕ × ℕ)
  | ((hp, scratchBase), (m, out, remB, sh)) => do
    let limb ← Memory.read (scratchBase + m)
    let c := hpC hp
    if 0 < remB then
      if c < remB then
        let part := (limb &&& hpMaskC hp) <<< sh
        pure (m + 1, out ^^^ part, remB - c, sh + c)
      else
        let mask := (1 <<< remB) - 1
        let part := (limb &&& mask) <<< sh
        pure (m + 1, out ^^^ part, 0, sh + remB)
    else
      pure (m + 1, out, 0, sh)

private def PackOutStepPre (w : ℕ) :
    (HashParams × ℕ) × (ℕ × ℕ × ℕ × ℕ) → Memory.State → Prop
  | ((hp, scratchBase), (m, out, remB, sh)), s => ∃ w₀ b b' k,
    b' ≤ w ∧ 2 * rChunk w₀ b b' < w ∧ hp = mkHashParams w w₀ b b' k ∧
    scratchBase + scratchWords ≤ s.frontier ∧
    m < rLimbs w₀ b b' ∧ out < 2 ^ w ∧ remB ≤ b' ∧ sh + remB = b'

private theorem realizesBounded_packOutStepGen :
    RealizesBounded .exact packOutStepGenProg
      (WordEncoding.encode (α := (HashParams × ℕ) × (ℕ × ℕ × ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ)) PackOutStepPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨hp, scratchBase⟩, ⟨m, out, remB, sh⟩⟩
    obtain ⟨w₀, b, b', k, hb'_le, hc_lt, rfl, hfr_s, hm_lt, hout_lt, hrem_le, hsum⟩ := h
    dsimp only [hpC_mk, hpMaskC_mk] at *
    dsimp only [accWords, prodWords, scratchWords] at *
    have hL_le : rLimbs w₀ b b' ≤ 54 := reducedLimbCount_le _
    have hw_lt : Fits w w := Nat.lt_two_pow_self
    have hpow2c : Fits w (2 ^ (2 * rChunk w₀ b b')) := Nat.pow_lt_pow_right one_lt_two hc_lt
    have hpowc : Fits w (2 ^ rChunk w₀ b b') :=
      hpow2c.of_le (Nat.pow_le_pow_right two_pos (by omega)))
  all_goals try omega
  all_goals try exact hmem.1.of_le (by omega)
  all_goals try exact hw_lt.of_le (by omega)
  all_goals (try (rw [Nat.shiftLeft_eq, one_mul]; exact Nat.one_le_two_pow))
  all_goals (try
    have hrem_lt_w : remB < w := by omega
    rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right one_lt_two hrem_lt_w)
  all_goals (try
    have hpart : (s.mem (scratchBase + m) &&& (2 ^ rChunk w₀ b b' - 1)) <<< sh < 2 ^ w := by
      rw [Nat.shiftLeft_eq]
      calc (s.mem (scratchBase + m) &&& (2 ^ rChunk w₀ b b' - 1)) * 2 ^ sh
          < 2 ^ rChunk w₀ b b' * 2 ^ sh :=
            Nat.mul_lt_mul_of_pos_right (and_two_pow_sub_one_lt _ _) (Nat.two_pow_pos sh)
        _ = 2 ^ (rChunk w₀ b b' + sh) := (pow_add 2 _ sh).symm
        _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
    first | exact hpart | exact Nat.xor_lt_two_pow hout_lt hpart)
  all_goals (
    have hpart : (s.mem (scratchBase + m) &&& ((1 <<< remB) - 1)) <<< sh < 2 ^ w := by
      rw [Nat.shiftLeft_eq 1 remB, one_mul, Nat.shiftLeft_eq]
      calc (s.mem (scratchBase + m) &&& (2 ^ remB - 1)) * 2 ^ sh
          < 2 ^ remB * 2 ^ sh :=
            Nat.mul_lt_mul_of_pos_right (and_two_pow_sub_one_lt _ remB) (Nat.two_pow_pos sh)
        _ = 2 ^ (remB + sh) := (pow_add 2 remB sh).symm
        _ ≤ 2 ^ w := Nat.pow_le_pow_right two_pos (by omega)
    first | exact hpart | exact Nat.xor_lt_two_pow hout_lt hpart)

private theorem packOutLoop_spec {w w₀ b b' k scratchBase evalVal : ℕ} {s₀ : Memory.State}
    (hb'_le : b' ≤ w) (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr_s : scratchBase + scratchWords ≤ s₀.frontier)
    (heval_lt : evalVal < 2 ^ (rLimbs w₀ b b' * rChunk w₀ b b'))
    (hacc₀ : ∀ m < rLimbs w₀ b b',
      s₀.mem (scratchBase + m) = getLimb (rChunk w₀ b b') evalVal m) :
    let hp := mkHashParams w w₀ b b' k
    let prog := iterate packOutStepGenProg (hp, scratchBase) (rLimbs w₀ b b') (0, 0, b', 0)
    iterationSafe packOutStepGenProg PackOutStepPre w (hp, scratchBase) (rLimbs w₀ b b')
      (0, 0, b', 0) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ rLimbs w₀ b b' ∧ (Memory.spec 0).clientState s₀ prog = s₀ ∧
    ((Memory.spec 0).clientResult s₀ prog).2.1 = evalVal &&& (2 ^ b' - 1) := by
  intro hp prog
  have hL_le : rLimbs w₀ b b' ≤ 54 := reducedLimbCount_le _
  dsimp only [accWords, prodWords, scratchWords] at *
  let inv (m : ℕ) (st : ℕ × ℕ × ℕ × ℕ) (s : Memory.State) : Prop :=
    s₀ = s ∧ (m, packLimbs (rChunk w₀ b b') m (getLimb (rChunk w₀ b b') evalVal) &&& (2 ^ b' - 1),
      b' - m * rChunk w₀ b b', min b' (m * rChunk w₀ b b')) = st
  obtain ⟨hsafe, hv, hcost, _, _, hs'_eq, hres_eq⟩ :=
    iterate_spec packOutStepGenProg PackOutStepPre w (hp, scratchBase) 1 (rLimbs w₀ b b') inv
      (fun _ => False)
      (fun m hm st s ⟨hs_eq, hst⟩ => by
        subst hs_eq; subst hst
        have hout_lt :
            (packLimbs (rChunk w₀ b b') m (getLimb (rChunk w₀ b b') evalVal) &&& (2 ^ b' - 1)) <
              2 ^ w :=
          (and_two_pow_sub_one_lt _ b').trans_le (Nat.pow_le_pow_right two_pos hb'_le)
        refine ⟨⟨w₀, b, b', k, hb'_le, hc_lt, rfl, hfr_s, hm, hout_lt, Nat.sub_le _ _, by omega⟩,
          ?_, ?_, ?_, fun _ _ => ?_, ?_, ?_⟩
        · dsimp only [packOutStepGenProg, hp, hpC_mk, hpMaskC_mk]; valid_prog; omega
        · dsimp only [packOutStepGenProg, hp, hpC_mk, hpMaskC_mk]; prog_cost
        · dsimp only [packOutStepGenProg, hp, hpC_mk, hpMaskC_mk]; split_ifs <;> rfl
        · dsimp only [packOutStepGenProg, hp, hpC_mk, hpMaskC_mk]; split_ifs <;> rfl
        · dsimp only [packOutStepGenProg, hp, hpC_mk, hpMaskC_mk]; split_ifs <;> rfl
        · dsimp only [packOutStepGenProg, hp, hpC_mk, hpMaskC_mk]
          rw [StateTransitionSpec.clientResult_bind]
          have hread_res : (Memory.spec 0).clientResult s₀ (Memory.read (scratchBase + m)) =
              s₀.mem (scratchBase + m) := rfl
          rw [hread_res]
          by_cases hrem : 0 < b' - m * rChunk w₀ b b'
          · simp only [hrem, ↓reduceIte]
            have hm_lt_b : m * rChunk w₀ b b' < b' := by omega
            have hmin_sh : min b' (m * rChunk w₀ b b') = reducedOutShift (
              rChunk w₀ b b') b' m := by
              dsimp only [reducedOutShift]; rw [ite_eq_left hm_lt_b]; omega
            by_cases hlt : rChunk w₀ b b' < b' - m * rChunk w₀ b b'
            · simp only [hlt, ↓reduceIte]
              change _ = (m + 1, (packLimbs (rChunk w₀ b b') m (getLimb (
                rChunk w₀ b b') evalVal) &&&
                (2 ^ b' - 1)) ^^^ ((s₀.mem (scratchBase + m) &&&
                  (2 ^ rChunk w₀ b b' - 1)) <<< min b' (m * rChunk w₀ b b')),
                b' - m * rChunk w₀ b b' - rChunk w₀ b b',
                min b' (m * rChunk w₀ b b') + rChunk w₀ b b')
              have hmask_eq : 2 ^ rChunk w₀ b b' - 1 = reducedOutMask (rChunk w₀ b b') b' m := by
                dsimp only [reducedOutMask]; rw [Nat.min_eq_left (le_of_lt hlt)]
              rw [hacc₀ m hm, hmask_eq, hmin_sh, ← packLimbs_and_mask_succ, Nat.succ_mul]
              refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
              · dsimp only; omega
              · dsimp only [reducedOutShift]; rw [ite_eq_left hm_lt_b, Nat.min_eq_right (by omega)]
            · simp only [hlt, ↓reduceIte]
              change _ = (m + 1, (packLimbs (rChunk w₀ b b') m (getLimb (
                rChunk w₀ b b') evalVal) &&&
                (2 ^ b' - 1)) ^^^ ((s₀.mem (scratchBase + m) &&&
                  ((1 <<< (b' - m * rChunk w₀ b b')) - 1)) <<< min b' (m * rChunk w₀ b b')),
                0, min b' (m * rChunk w₀ b b') + (b' - m * rChunk w₀ b b'))
              have hmask_eq :
                  (1 <<< (b' - m * rChunk w₀ b b')) - 1 = reducedOutMask (
                    rChunk w₀ b b') b' m := by
                dsimp only [reducedOutMask]
                rw [Nat.shiftLeft_eq, one_mul, Nat.min_eq_right (by omega)]
              rw [hacc₀ m hm, hmask_eq, hmin_sh, ← packLimbs_and_mask_succ, Nat.succ_mul]
              refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
              · dsimp only; omega
              · dsimp only [reducedOutShift]; rw [ite_eq_left hm_lt_b, Nat.min_eq_left (by omega)]
                omega
          · simp only [hrem, ↓reduceIte]
            change _ = (m + 1, packLimbs (rChunk w₀ b b') m (getLimb (rChunk w₀ b b') evalVal) &&&
              (2 ^ b' - 1), 0, min b' (m * rChunk w₀ b b'))
            have hmask0 : reducedOutMask (rChunk w₀ b b') b' m = 0 := by
              dsimp only [reducedOutMask]
              rw [show min (rChunk w₀ b b') (b' - m * rChunk w₀ b b') = 0 by omega]; rfl
            have hsucc :
                packLimbs (rChunk w₀ b b') (m + 1) (getLimb (rChunk w₀ b b') evalVal) &&&
                  (2 ^ b' - 1) =
                packLimbs (rChunk w₀ b b') m (getLimb (rChunk w₀ b b') evalVal) &&&
                  (2 ^ b' - 1) := by
              rw [packLimbs_and_mask_succ, hmask0, Nat.and_zero, Nat.zero_shiftLeft, Nat.xor_zero]
            rw [hsucc, Nat.succ_mul]
            refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
            · dsimp only; omega
            · dsimp only; rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)])
      (0, 0, b', 0) s₀ ⟨rfl, by simp only [packLimbs, Nat.zero_and, Nat.zero_mul, Nat.sub_zero,
        Nat.min_eq_right (Nat.zero_le b')]⟩
  refine ⟨hsafe, hv, by simpa only [one_mul] using hcost, hs'_eq.symm, ?_⟩
  rw [← hres_eq, packLimbs_getLimb (reducedChunkBits_pos _) (rLimbs w₀ b b') heval_lt]

/-- Complete runtime polynomial hash evaluation `Memory.Prog`. -/
def evalHashGenProg : HashParams × ℕ × ℕ × ℕ → Memory.Prog ℕ
  | (hp, hashBase, scratchBase, uVal) => do
    let rVal ← reduceKeyGenProg (hp, hashBase, uVal)
    let _ ← iterate zeroWordsStepProg scratchBase (2 * hpL0 hp) 0
    let _ ← iterate hornerStepGenProg (hp, hashBase, scratchBase, rVal) (hpK hp) 0
    let (_, out, _, _) ← iterate packOutStepGenProg (hp, scratchBase) (2 * hpL0 hp)
      (0, 0, hpB' hp, 0)
    pure out

/-- Parameter-independent `O(k)` upper bound on `memoryCost (evalHashGenProg d) s`. -/
@[expose, wram_arith] def evalMemBound (k : ℕ) : ℕ := 15014 * k + 109

/-- Entry precondition for `evalHashGenProg`. -/
def EvalHashGenPre (w : ℕ) : HashParams × ℕ × ℕ × ℕ → Memory.State → Prop
  | (hp, hashBase, scratchBase, uVal), s =>
    ∃ U w₀ b b' k, ∃ θ : ReducedPolySeed w₀ b b' k, ∃ u : Fin U,
      0 < w₀ ∧ w₀ ≤ w ∧ U ≤ 2 ^ w₀ ∧ b' ≤ w ∧ 0 < k ∧
      2 * rChunk w₀ b b' < w ∧ hp = mkHashParams w w₀ b b' k ∧ uVal = u.val ∧
      hashBase + ReducedKWise.space w w₀ b b' k ≤ s.frontier ∧
      Fits w (hashBase + ReducedKWise.space w w₀ b b' k) ∧
      scratchBase + scratchWords ≤ s.frontier ∧ Fits w (scratchBase + scratchWords) ∧
      (hashBase + ReducedKWise.space w w₀ b b' k ≤ scratchBase ∨
        scratchBase + scratchWords ≤ hashBase) ∧
      ReducedKWise.Rep hashBase w w₀ b b' k θ s.mem

private theorem evalHashGenProg_aux {w U w₀ b b' k hashBase scratchBase : ℕ}
    {θ : ReducedPolySeed w₀ b b' k} {u : Fin U} {s₀ : Memory.State}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀) (hb' : b' ≤ w) (hk_pos : 0 < k)
    (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr_h : hashBase + ReducedKWise.space w w₀ b b' k ≤ s₀.frontier)
    (hfit_h : Fits w (hashBase + ReducedKWise.space w w₀ b b' k))
    (hfr_s : scratchBase + scratchWords ≤ s₀.frontier)
    (hfit_s : Fits w (scratchBase + scratchWords))
    (hdisj : hashBase + ReducedKWise.space w w₀ b b' k ≤ scratchBase ∨
      scratchBase + scratchWords ≤ hashBase)
    (hrep : ReducedKWise.Rep hashBase w w₀ b b' k θ s₀.mem) :
    let hp := mkHashParams w w₀ b b' k
    let r := multiplyShiftReduced U w₀ (3 * b) θ.1 u
    let prog := evalHashGenProg (hp, hashBase, scratchBase, u.val)
    let s₁ := (Memory.spec 0).clientState s₀ (iterate zeroWordsStepProg scratchBase
      (rLimbs w₀ b b') 0)
    let s₂ := (Memory.spec 0).clientState s₁
      (iterate hornerStepGenProg (hp, hashBase, scratchBase, r.val) k 0)
    let s' := (Memory.spec 0).clientState s₀ prog
    EvalHashGenPre w (hp, hashBase, scratchBase, u.val) s₀ ∧
    ReduceKeyGenPre w (hp, hashBase, u.val) s₀ ∧
    iterationSafe zeroWordsStepProg ZeroWordsStepPre w scratchBase (rLimbs w₀ b b') 0 s₀ ∧
    iterationSafe hornerStepGenProg HornerStepPre w (hp, hashBase, scratchBase, r.val) k 0 s₁ ∧
    iterationSafe packOutStepGenProg PackOutStepPre w (hp, scratchBase) (rLimbs w₀ b b')
      (0, 0, b', 0) s₂ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ evalMemBound k ∧
    (Memory.spec 0).clientResult s₀ prog = (reducedPolyHash U w₀ b b' k θ u).val ∧
    s'.frontier = s₀.frontier ∧
    (∀ a, (a < scratchBase ∨ scratchBase + scratchWords ≤ a) → s'.mem a = s₀.mem a) := by
  have haccW : accWords = 54 := rfl
  have hscrW : scratchWords = 162 := rfl
  intro hp r prog s₁ s₂ s'
  have hL_le : rLimbs w₀ b b' ≤ 54 := reducedLimbCount_le _
  have hu_lt_w0 : u.val < 2 ^ w₀ := lt_of_lt_of_le u.isLt hU
  have hα_eq : s₀.mem hashBase = θ.1.val := hrep.2.1
  have hr_eq : (Memory.spec 0).clientResult s₀ (reduceKeyGenProg (hp, hashBase, u.val)) =
    r.val := by
    change oddMulModWord w₀ (s₀.mem hashBase) u.val >>> (w₀ - min w₀ (3 * b)) = r.val
    rw [hα_eq, show w₀ - min w₀ (3 * b) = w₀ - 3 * b by omega]
    exact oddMulModWord_shiftRight_eq_multiplyShiftReduced hw₀_pos θ.1 u
  obtain ⟨hsafe_z, hv_z, hcost_z, hfr_z, hz_mem, hout_z⟩ :=
    zeroWordsLoop_spec (w := w) (baseAddr := scratchBase) (n := rLimbs w₀ b b') (s₀ := s₀)
      (by omega)
  have htab₁ : ReducedKWise.TableRep hashBase w w₀ b b' k s₁.mem :=
    tableRep_congr hrep.1 fun a h1 h2 => (hout_z a (by omega)).symm
  have hseed₁ : ReducedKWise.SeedRep hashBase w₀ b b' k θ s₁.mem :=
    seedRep_congr (w := w) hrep.2 fun a h1 h2 => (hout_z a (by omega)).symm
  obtain ⟨hsafe_h, hv_h, hcost_h, hfr_h2, hacc_h, hout_h⟩ :=
    hornerLoop_spec hw₀ hc_lt (hfr_z.symm ▸ hfr_h) (hfr_z.symm ▸ hfr_s) hdisj htab₁ hseed₁ hz_mem
  let evalVal := (trinomialPolyEval (rStep w₀ b b') k (2 ^ min w₀ (3 * b)) θ.2 r).val
  have heval_lt : evalVal < 2 ^ (rLimbs w₀ b b' * rChunk w₀ b b') := by
    rw [reducedLimbCount_mul_chunkBits]
    exact (trinomialPolyEval (rStep w₀ b b') k (2 ^ min w₀ (3 * b)) θ.2 r).isLt
  obtain ⟨hsafe_p, hv_p, hcost_p, hs_p, hres_p⟩ :=
    packOutLoop_spec (w₀ := w₀) (b := b) (k := k) hb' hc_lt
      (by rw [hfr_h2, hfr_z]; exact hfr_s) heval_lt hacc_h
  have hprog_eq : prog = (do
      let rVal ← reduceKeyGenProg (hp, hashBase, u.val)
      let _ ← iterate zeroWordsStepProg scratchBase (rLimbs w₀ b b') 0
      let _ ← iterate hornerStepGenProg (hp, hashBase, scratchBase, rVal) k 0
      let (_, out, _, _) ← iterate packOutStepGenProg (hp, scratchBase) (rLimbs w₀ b b')
        (0, 0, b', 0)
      pure out) := rfl
  have hrk_state : (Memory.spec 0).clientState s₀ (reduceKeyGenProg (hp, hashBase, u.val)) =
    s₀ := rfl
  have hs'_eq : s' = s₂ := by
    dsimp only [s']; rw [hprog_eq, StateTransitionSpec.clientState_bind, hr_eq, hrk_state,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, hs_p]; rfl
  refine ⟨⟨U, w₀, b, b', k, θ, u, hw₀_pos, hw₀, hU, hb', hk_pos, hc_lt, rfl, rfl,
      hfr_h, hfit_h, hfr_s, hfit_s, hdisj, hrep⟩,
    ⟨w₀, b, b', k, hw₀_pos, hw₀, hc_lt, rfl,
      by unfold ReducedKWise.space ReducedKWise.seedWords at hfr_h; omega,
      hα_eq ▸ θ.1.isLt, hu_lt_w0⟩,
    hsafe_z, hsafe_h, hsafe_p, ?_, ?_, ?_, by rw [hs'_eq, hfr_h2, hfr_z], fun a ha => ?_⟩
  · have hv_rk : (Memory.spec w).ValidHistory s₀
        ((Memory.spec w).clientHistory s₀ (reduceKeyGenProg (hp, hashBase, u.val))) := by
      change hashBase < s₀.frontier ∧ True
      exact ⟨by unfold ReducedKWise.space ReducedKWise.seedWords at hfr_h; omega, trivial⟩
    rw [hprog_eq]
    valid_prog [hv_rk, hv_z, hv_h, hv_p] with [hr_eq, hrk_state, hs_p]
  · have hstep_bound :
        1 + 2 * rLimbs w₀ b b' + (1 + 5 * rLimbs w₀ b b') * rLimbs w₀ b b' +
          5 * rLimbs w₀ b b' ≤ 15014 := by nlinarith
    have hmul_bound := Nat.mul_le_mul_right k hstep_bound
    have hrk_cost : memoryCost (reduceKeyGenProg (hp, hashBase, u.val)) s₀ = 1 := rfl
    rw [hprog_eq]
    prog_cost [hr_eq, hrk_state, hrk_cost, hs_p]
    wram_omega [hcost_h, hcost_p]
  · rw [hprog_eq, StateTransitionSpec.clientResult_bind, hr_eq, hrk_state,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_bind, hs_p]
    change ((Memory.spec 0).clientResult s₂
      (iterate packOutStepGenProg (hp, scratchBase) (rLimbs w₀ b b') (0, 0, b', 0))).2.1 = _
    rw [hres_p]; exact (val_trinomialPolyHash (rStep w₀ b b') k (2 ^ min w₀ (3 * b)) b' θ.2 r).symm
  · rw [hs'_eq]; exact (hout_h a ha).trans (hout_z a (by omega))

/-- **Full specification of `evalHashGenProg`**. -/
theorem evalHashGenProg_spec {w U w₀ b b' k hashBase scratchBase : ℕ}
    {θ : ReducedPolySeed w₀ b b' k} {u : Fin U} {s₀ : Memory.State}
    (hw₀_pos : 0 < w₀) (hw₀ : w₀ ≤ w) (hU : U ≤ 2 ^ w₀) (hb' : b' ≤ w) (hk_pos : 0 < k)
    (hc_lt : 2 * rChunk w₀ b b' < w)
    (hfr_h : hashBase + ReducedKWise.space w w₀ b b' k ≤ s₀.frontier)
    (hfit_h : Fits w (hashBase + ReducedKWise.space w w₀ b b' k))
    (hfr_s : scratchBase + scratchWords ≤ s₀.frontier)
    (hfit_s : Fits w (scratchBase + scratchWords))
    (hdisj : hashBase + ReducedKWise.space w w₀ b b' k ≤ scratchBase ∨
      scratchBase + scratchWords ≤ hashBase)
    (hrep : ReducedKWise.Rep hashBase w w₀ b b' k θ s₀.mem) :
    let hp := mkHashParams w w₀ b b' k
    let prog := evalHashGenProg (hp, hashBase, scratchBase, u.val)
    let s' := (Memory.spec 0).clientState s₀ prog
    EvalHashGenPre w (hp, hashBase, scratchBase, u.val) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ evalMemBound k ∧
    (Memory.spec 0).clientResult s₀ prog = (reducedPolyHash U w₀ b b' k θ u).val ∧
    s'.frontier = s₀.frontier ∧
    (∀ a, (a < scratchBase ∨ scratchBase + scratchWords ≤ a) → s'.mem a = s₀.mem a) := by
  obtain ⟨hpre, _, _, _, _, hv, hcost, hres, hfr', hout⟩ :=
    evalHashGenProg_aux hw₀_pos hw₀ hU hb' hk_pos hc_lt hfr_h hfit_h hfr_s hfit_s hdisj hrep
  exact ⟨hpre, hv, hcost, hres, hfr', hout⟩

/-- **Parameter-free `RealizesBounded .exact` certificate for `evalHashGenProg`** (
  `¬ReadsWidth`). -/
theorem realizesBounded_evalHashGen :
    RealizesBounded .exact evalHashGenProg
      (WordEncoding.encode (α := HashParams × ℕ × ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      EvalHashGenPre (fun _ _ => 0) := by
  realize [realizesBounded_reduceKeyGen, realizesBounded_zeroWordsStep,
    realizesBounded_hornerStepGen, realizesBounded_packOutStepGen]
  all_goals (
    rcases d with ⟨hp, hashBase, scratchBase, uVal⟩
    obtain ⟨U, w₀, b, b', k, θ, u, hw₀_pos, hw₀, hU, hb', hk_pos, hc_lt, rfl, rfl,
      hfr_h, hfit_h, hfr_s, hfit_s, hdisj, hrep⟩ := h
    try (dsimp only [hpL0_mk, hpK_mk, hpB'_mk] at *)
    dsimp only [accWords, prodWords, scratchWords] at *
    have hL_le : rLimbs w₀ b b' ≤ 54 := reducedLimbCount_le _
    have h2L0 : 2 * rHalf w₀ b b' = rLimbs w₀ b b' := rfl
    obtain ⟨_, hrk_pre, hsafe_z, hsafe_h, hsafe_p, _⟩ :=
      evalHashGenProg_aux (u := u) hw₀_pos hw₀ hU hb' hk_pos hc_lt hfr_h hfit_h hfr_s hfit_s
        hdisj hrep
    have hr_eq : (Memory.spec 0).clientResult s
        (reduceKeyGenProg (mkHashParams w w₀ b b' k, hashBase, u.val)) =
        (multiplyShiftReduced U w₀ (3 * b) θ.1 u).val := by
      change oddMulModWord w₀ (s.mem hashBase) u.val >>> (w₀ - min w₀ (3 * b)) = _
      rw [hrep.2.1, show w₀ - min w₀ (3 * b) = w₀ - 3 * b by omega]
      exact oddMulModWord_shiftRight_eq_multiplyShiftReduced hw₀_pos θ.1 u)
  all_goals try exact hrk_pre
  all_goals try exact hfit_s.of_le (by omega)
  all_goals first
    | (rw [h2L0]; exact iterationSafe_imp hsafe_z (fun _ => rfl) (fun _ _ hs => hs))
    | (rw [hr_eq]; exact iterationSafe_imp hsafe_h (fun _ => rfl) (fun _ _ hs => hs))
    | (rw [hr_eq, h2L0]; exact iterationSafe_imp hsafe_p (fun _ => rfl) (fun _ _ hs => hs))

/-! ## Section 4: Parameter-free seed resampling (`resampleHashCode`) on `RCode .exact r` -/

private def randFillRBody {r : ℕ} (rPtr rMask rOne rVal : Fin r) : RCode .exact r :=
  .seq (.rand rVal rMask)
    (.seq (.op (.store rPtr rVal)) (.op (.exactBin .add rPtr rPtr rOne)))

private def randFillRLoop {r : ℕ} (rPtr rEnd rMask rOne rVal : Fin r) : RCode .exact r :=
  .loop (.lt rPtr rEnd) (randFillRBody rPtr rMask rOne rVal)

private theorem randFillLoop_execRandBounded {w L bits arrBase : ℕ} (len : ℕ) {x : Data 6}
    (hL : arrBase + len ≤ L) (hfit_end : Fits w (arrBase + len))
    (hfit_mask : Fits w (2 ^ bits - 1))
    (hptr : x.regs Tabulation.regPtr = arrBase)
    (hend : x.regs Tabulation.regEnd = arrBase + len)
    (hmask : x.regs Tabulation.regMask = 2 ^ bits - 1)
    (hone : x.regs Tabulation.regOne = 1) :
    ExecRandBounded w L Tabulation.randFillLoop x
      (Tabulation.randFillComp bits arrBase len x) := by
  induction len generalizing arrBase x with
  | zero => exact .loop_exit (by simp [Cond.Holds, hptr, hend])
  | succ len ih =>
    have hc : (Cond.lt Tabulation.regPtr Tabulation.regEnd).Holds x := by
      simp [Cond.Holds, hptr, hend]
    have hbody : ExecRandBounded w L Tabulation.randFillBody x (do
        let k ← ProbComp.unifFin (2 ^ bits - 1)
        pure (Tabulation.randFillStepData arrBase k.val x, 1 + (1 + 1))) := by
      dsimp only [Tabulation.randFillBody]
      refine ExecRandBounded.rand_seq_det hmask hfit_mask fun k => ?_
      refine ExecBoundedExact.seq
        (ExecBoundedExact.op (y := (x.set Tabulation.regVal k.val).write arrBase k.val)
          (by simp [WordRAM.Op.BoundedAccess, Tabulation.regVal, Tabulation.regPtr,
                Function.update_of_ne, hptr]; omega)
          (by simp [WordRAM.Op.eval, Tabulation.regVal, Tabulation.regPtr,
                Function.update_of_ne, hptr]))
        (ExecBoundedExact.of_exec_regOnly trivial ?_)
      unfold Tabulation.randFillStepData
      wram_exec [hptr, hone]
    have hiter := ExecRandBounded.loop_iter hc hbody fun z hz => by
      supp_cases hz with ⟨k, rfl⟩
      exact ih (arrBase := arrBase + 1) (by omega)
        (by rwa [show arrBase + 1 + len = arrBase + (len + 1) by omega])
        (by wram_simp [Tabulation.randFillStepData])
        (by wram_simp [Tabulation.randFillStepData, hend]; omega)
        (by wram_simp [Tabulation.randFillStepData, hmask])
        (by wram_simp [Tabulation.randFillStepData, hone])
    simpa only [Tabulation.randFillLoop, Tabulation.randFillComp, bind_assoc, pure_bind]
      using hiter

private def fillMap9 (i : Fin 6) : Fin 9 :=
  match i.val with
  | 0 => 4 | 1 => 5 | 2 => 6 | 3 => 7 | 4 => 8 | _ => 0

private theorem injective_fillMap9 : Function.Injective fillMap9 := by decide

private def resampleHashCode9 : Code .exact 9 :=
  .seq (.op (.copy 4 0)) <| .seq (.op (.const 7 1)) <|
  .seq (.op (.exactBin .add 5 0 7)) <| .seq (.op (.copy 6 1)) <|
  .seq (Tabulation.randFillLoop.rename fillMap9) <| .seq (.op (.copy 4 5)) <|
  .seq (.op (.exactBin .add 5 5 2)) <| .seq (.op (.copy 6 3)) <|
  Tabulation.randFillLoop.rename fillMap9

private noncomputable def resampleHashComp9 (hashBase w₀ c botWords : ℕ) (x : Data 9) :
    ProbComp (Data 9 × ℕ) := do
  let x1 := (((x.set 4 hashBase).set 7 1).set 5 (hashBase + 1)).set 6 (2 ^ (w₀ - 1) - 1)
  let z1 ← Tabulation.randFillComp (w₀ - 1) hashBase 1 (x1.comap fillMap9)
  let y1 := z1.1.extend fillMap9 x1
  let x2 := ((y1.set 4 (hashBase + 1)).set 5 (hashBase + 1 + botWords)).set 6 (2 ^ c - 1)
  let z2 ← Tabulation.randFillComp c (hashBase + 1) botWords (x2.comap fillMap9)
  pure (z2.1.extend fillMap9 x2, 1 + (1 + (1 + (1 + (z1.2 + (1 + (1 + (1 + z2.2))))))))

private theorem execRandBounded_seq_op (o : WordRAM.Op .exact 9) (x y : Data 9) {w L : ℕ}
    {c₂ : Code .exact 9} {m : ProbComp (Data 9 × ℕ)} (ho : IsRegOnlyCode (.op o))
    (he : Exec w (.op o) x y 1) (h₂ : ExecRandBounded w L c₂ y m) :
    ExecRandBounded w L (.seq (.op o) c₂) x ((fun z => (z.1, 1 + z.2)) <$> m) :=
  ExecRandBounded.seq_of_exec_regOnly ho he h₂

private theorem resampleHashCode9_execRandBounded {w L w₀ c botWords hashBase : ℕ} {x : Data 9}
    (hL : hashBase + 1 + botWords ≤ L) (hfit1 : Fits w 1)
    (hfit_top : Fits w (hashBase + 1)) (hfit_end : Fits w (hashBase + 1 + botWords))
    (hfit_mM : Fits w (2 ^ (w₀ - 1) - 1)) (hfit_mC : Fits w (2 ^ c - 1))
    (h0 : x.regs 0 = hashBase) (h1 : x.regs 1 = 2 ^ (w₀ - 1) - 1)
    (h2 : x.regs 2 = botWords) (h3 : x.regs 3 = 2 ^ c - 1) :
    ExecRandBounded w L resampleHashCode9 x (resampleHashComp9 hashBase w₀ c botWords x) := by
  set x1 := (((x.set 4 hashBase).set 7 1).set 5 (hashBase + 1)).set 6 (2 ^ (w₀ - 1) - 1)
  have hl1 := (randFillLoop_execRandBounded (w := w) (L := L) (bits := w₀ - 1)
    (arrBase := hashBase) 1 (x := x1.comap fillMap9) (by omega) hfit_top hfit_mM
    (by simp +decide [x1, fillMap9, Data.comap, Tabulation.regPtr])
    (by simp +decide [x1, fillMap9, Data.comap, Tabulation.regEnd])
    (by simp +decide [x1, fillMap9, Data.comap, Tabulation.regMask])
    (by simp +decide [x1, fillMap9, Data.comap, Tabulation.regOne])).rename injective_fillMap9
  have hmid := ExecRandBounded.seq hl1
    (m₂ := fun y1 =>
      let x2 := ((y1.set 4 (hashBase + 1)).set 5 (hashBase + 1 + botWords)).set 6 (2 ^ c - 1)
      (fun z2 : Data 6 × ℕ => (z2.1.extend fillMap9 x2, 1 + (1 + (1 + z2.2)))) <$>
        Tabulation.randFillComp c (hashBase + 1) botWords (x2.comap fillMap9))
    fun z hz => by
      supp_cases hz with ⟨z1, hz1, rfl⟩
      obtain ⟨_, _, hend1, _, hone1, _, _, _⟩ := Tabulation.mem_support_randFillComp hz1
      set y1 := z1.1.extend fillMap9 x1
      have hy1_5 : y1.regs 5 = hashBase + 1 := by
        change (y1.comap fillMap9).regs Tabulation.regEnd = hashBase + 1
        rw [Data.comap_extend injective_fillMap9, hend1]
        simp +decide [x1, fillMap9, Data.comap, Tabulation.regEnd]
      have hy1_7 : y1.regs 7 = 1 := by
        change (y1.comap fillMap9).regs Tabulation.regOne = 1
        rw [Data.comap_extend injective_fillMap9, hone1]
        simp +decide [x1, fillMap9, Data.comap, Tabulation.regOne]
      have hy1_2 : y1.regs 2 = botWords := by
        rw [Data.extend_regs_of_notMem z1.1 x1 (by decide)]; simp +decide [x1, h2]
      have hy1_3 : y1.regs 3 = 2 ^ c - 1 := by
        rw [Data.extend_regs_of_notMem z1.1 x1 (by decide)]; simp +decide [x1, h3]
      set x2 := ((y1.set 4 (hashBase + 1)).set 5 (hashBase + 1 + botWords)).set 6 (2 ^ c - 1)
      have hl2 := (randFillLoop_execRandBounded (w := w) (L := L) (bits := c)
        (arrBase := hashBase + 1) botWords (x := x2.comap fillMap9) hL hfit_end hfit_mC
        (by simp +decide [x2, fillMap9, Data.comap, Tabulation.regPtr])
        (by simp +decide [x2, fillMap9, Data.comap, Tabulation.regEnd])
        (by simp +decide [x2, fillMap9, Data.comap, Tabulation.regMask])
        (by simp +decide [x2, fillMap9, Data.comap, Tabulation.regOne, hy1_7])).rename
          injective_fillMap9
      simpa only [Functor.map_map, Function.comp_def] using
        execRandBounded_seq_op (.copy 4 5) y1 (y1.set 4 (hashBase + 1))
          trivial (by wram_exec [hy1_5]) <|
        execRandBounded_seq_op (.exactBin .add 5 5 2) (y1.set 4 (hashBase + 1))
          ((y1.set 4 (hashBase + 1)).set 5 (hashBase + 1 + botWords))
          trivial (by wram_exec [hy1_5, hy1_2]) <|
        execRandBounded_seq_op (.copy 6 3)
          ((y1.set 4 (hashBase + 1)).set 5 (hashBase + 1 + botWords)) x2
          trivial (by wram_exec [hy1_3]) hl2
  have hall :=
    execRandBounded_seq_op (.copy 4 0) x (x.set 4 hashBase) trivial (by wram_exec [h0]) <|
    execRandBounded_seq_op (.const 7 1) (x.set 4 hashBase) ((x.set 4 hashBase).set 7 1)
      trivial (by wram_exec) <|
    execRandBounded_seq_op (.exactBin .add 5 0 7) ((x.set 4 hashBase).set 7 1)
      (((x.set 4 hashBase).set 7 1).set 5 (hashBase + 1)) trivial (by wram_exec [h0]) <|
    execRandBounded_seq_op (.copy 6 1)
      (((x.set 4 hashBase).set 7 1).set 5 (hashBase + 1)) x1 trivial (by wram_exec [h1]) hmid
  simpa only [resampleHashCode9, resampleHashComp9, ← bind_pure_comp, bind_assoc, pure_bind]
    using hall

/-- Parameter-free `RCode .exact r` subroutine resampling a uniform `ReducedPolySeed w₀ b b' k`. -/
def resampleHashCode {r : ℕ}
    (rBase rMaskM rBotWords rMaskC rPtr rEnd rMask rOne rVal : Fin r) : RCode .exact r :=
  .seq (.op (.copy rPtr rBase)) <| .seq (.op (.const rOne 1)) <|
  .seq (.op (.exactBin .add rEnd rBase rOne)) <| .seq (.op (.copy rMask rMaskM)) <|
  .seq (randFillRLoop rPtr rEnd rMask rOne rVal) <| .seq (.op (.copy rPtr rEnd)) <|
  .seq (.op (.exactBin .add rEnd rEnd rBotWords)) <| .seq (.op (.copy rMask rMaskC)) <|
  randFillRLoop rPtr rEnd rMask rOne rVal

theorem not_readsWidth_resampleHashCode {r : ℕ}
    (rBase rMaskM rBotWords rMaskC rPtr rEnd rMask rOne rVal : Fin r) :
    ¬(resampleHashCode rBase rMaskM rBotWords rMaskC rPtr rEnd rMask rOne rVal).ReadsWidth := by
  simp [resampleHashCode, randFillRLoop, randFillRBody, RCode.ReadsWidth, Op.ReadsWidth,
    Op.exactBin]

/-- **Compositional `ExecRCodeDist` specification of `resampleHashCode`**. -/
theorem resampleHashCode_execRCodeDist {r w L_peak w₀ b b' k hashBase : ℕ}
    {rBase rMaskM rBotWords rMaskC rPtr rEnd rMask rOne rVal : Fin r} {x : RData r}
    (hd : [rBase, rMaskM, rBotWords, rMaskC, rPtr, rEnd, rMask, rOne, rVal].Nodup)
    (hw₀ : w₀ ≤ w) (hc_lt : 2 * rChunk w₀ b b' < w) (hL : x.frontier ≤ L_peak)
    (hfr : hashBase + ReducedKWise.seedWords w₀ b b' k ≤ x.frontier)
    (hfit : Fits w (hashBase + ReducedKWise.seedWords w₀ b b' k))
    (hbase : x.regs rBase = hashBase)
    (hmaskM : x.regs rMaskM = 2 ^ (w₀ - 1) - 1)
    (hbot : x.regs rBotWords = k * rLimbs w₀ b b')
    (hmaskC : x.regs rMaskC = 2 ^ rChunk w₀ b b' - 1) :
    ∃ μ : PMF (RData r),
      ExecRCodeDist w (resampleHashCode rBase rMaskM rBotWords rMaskC rPtr rEnd rMask rOne rVal)
        x μ (5 * ReducedKWise.seedWords w₀ b b' k + 11 : ℕ) L_peak ∧
      μ.map (fun y => ReducedKWise.extractSeed hashBase w₀ b b' k y.mem) =
        PMF.uniformOfFintype (ReducedPolySeed w₀ b b' k) ∧
      ∀ y ∈ μ.support,
        y.frontier = x.frontier ∧
        ReducedKWise.SeedRep hashBase w₀ b b' k
          (ReducedKWise.extractSeed hashBase w₀ b b' k y.mem) y.mem ∧
        (∀ a, (a < hashBase ∨ hashBase + ReducedKWise.seedWords w₀ b b' k ≤ a) →
          y.mem a = x.mem a) ∧
        (∀ j, j ∉ [rPtr, rEnd, rMask, rOne, rVal] → y.regs j = x.regs j) := by
  have hsw : ReducedKWise.seedWords w₀ b b' k = 1 + k * rLimbs w₀ b b' := rfl
  have hfit1 : Fits w 1 := hfit.of_le (by omega)
  have hfit_top : Fits w (hashBase + 1) := hfit.of_le (by omega)
  have hfit_end : Fits w (hashBase + 1 + k * rLimbs w₀ b b') := hfit.of_le (by omega)
  have hfit_mM : Fits w (2 ^ (w₀ - 1) - 1) :=
    (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le (Nat.pow_le_pow_right two_pos (by omega))
  have hfit_mC : Fits w (2 ^ rChunk w₀ b b' - 1) :=
    (Nat.sub_lt (Nat.two_pow_pos _) one_pos).trans_le (Nat.pow_le_pow_right two_pos (by omega))
  let f9 (i : Fin 9) : Fin r :=
    match i.val with
    | 0 => rBase | 1 => rMaskM | 2 => rBotWords | 3 => rMaskC
    | 4 => rPtr | 5 => rEnd | 6 => rMask | 7 => rOne | _ => rVal
  have hf9 : Function.Injective f9 := by
    have hget : ∀ i : Fin 9,
        [rBase, rMaskM, rBotWords, rMaskC, rPtr, rEnd, rMask, rOne, rVal][i.val] = f9 i :=
      fun i => by fin_cases i <;> rfl
    intro i j hij
    exact Fin.ext <| (List.Nodup.getElem_inj_iff hd).mp <|
      (hget i).trans (hij.trans (hget j).symm)
  set m9 := resampleHashComp9 hashBase w₀ (rChunk w₀ b b') (k * rLimbs w₀ b b') (x.toData.comap f9)
  have hb9 : ExecRandBounded w (hashBase + 1 + k * rLimbs w₀ b b') resampleHashCode9
      (x.toData.comap f9) m9 :=
    resampleHashCode9_execRandBounded le_rfl hfit1 hfit_top hfit_end hfit_mM hfit_mC
      hbase hmaskM hbot hmaskC
  have hsupp9 : ∀ z ∈ m9.support,
      z.2 = 5 * ReducedKWise.seedWords w₀ b b' k + 11 ∧
      z.1.regs 0 = hashBase ∧ z.1.regs 1 = 2 ^ (w₀ - 1) - 1 ∧
      z.1.regs 2 = k * rLimbs w₀ b b' ∧ z.1.regs 3 = 2 ^ rChunk w₀ b b' - 1 ∧
      ReducedKWise.SeedRep hashBase w₀ b b' k
        (ReducedKWise.extractSeed hashBase w₀ b b' k z.1.mem) z.1.mem ∧
      (∀ a, (a < hashBase ∨ hashBase + ReducedKWise.seedWords w₀ b b' k ≤ a) →
        z.1.mem a = x.mem a) := by
    intro z hz
    dsimp only [m9, resampleHashComp9] at hz
    supp_cases hz with ⟨z1, hz1, z2, hz2, rfl⟩
    obtain ⟨hs1, _, _, _, _, hextra1, hlt1, hframe1⟩ := Tabulation.mem_support_randFillComp hz1
    obtain ⟨hs2, _, _, _, _, hextra2, hlt2, hframe2⟩ := Tabulation.mem_support_randFillComp hz2
    set x0 := x.toData.comap f9
    set x1 := (((x0.set 4 hashBase).set 7 1).set 5 (hashBase + 1)).set 6 (2 ^ (w₀ - 1) - 1)
    set y1 := z1.1.extend fillMap9 x1
    set x2 := ((y1.set 4 (hashBase + 1)).set 5 (hashBase + 1 + k * rLimbs w₀ b b')).set 6
      (2 ^ rChunk w₀ b b' - 1)
    set y2 := z2.1.extend fillMap9 x2
    have hy1_0 : y1.regs 0 = hashBase := by
      change (y1.comap fillMap9).regs Tabulation.regExtra = hashBase
      rw [Data.comap_extend injective_fillMap9, hextra1]
      simpa +decide [x0, x1, fillMap9, f9, Data.comap, Tabulation.regExtra] using hbase
    have hy2_0 : y2.regs 0 = hashBase := by
      change (y2.comap fillMap9).regs Tabulation.regExtra = hashBase
      rw [Data.comap_extend injective_fillMap9, hextra2]
      simpa +decide [x2, fillMap9, Data.comap, Tabulation.regExtra] using hy1_0
    have hreg123 : ∀ i : Fin 9, i ∈ ({1, 2, 3} : Set (Fin 9)) → y2.regs i = x0.regs i := by
      intro i hi
      have hni : i ∉ Set.range fillMap9 := by
        rcases hi with rfl | rfl | rfl <;> decide
      rw [Data.extend_regs_of_notMem z2.1 x2 hni]
      have hx2i : x2.regs i = y1.regs i := by
        rcases hi with rfl | rfl | rfl <;> rfl
      rw [hx2i, Data.extend_regs_of_notMem z1.1 x1 hni]
      rcases hi with rfl | rfl | rfl <;> rfl
    refine ⟨by omega, hy2_0, (hreg123 1 (by simp)).trans hmaskM,
      (hreg123 2 (by simp)).trans hbot, (hreg123 3 (by simp)).trans hmaskC,
      ⟨?_, fun j m => ?_⟩, fun a ha => ?_⟩
    · have hm_eq : z2.1.mem hashBase = z1.1.mem hashBase := hframe2 hashBase (Or.inl (by omega))
      have hlt_v : z1.1.mem hashBase < 2 ^ (w₀ - 1) := by simpa using hlt1 0 Nat.one_pos
      change z2.1.mem hashBase = (ReducedKWise.extractTop hashBase w₀ z2.1.mem).val
      rw [ReducedKWise.extractTop_val, hm_eq, wordOfNat_val_of_lt hlt_v]
    · have hidx_lt : m.val + rLimbs w₀ b b' * j.val < k * rLimbs w₀ b b' := by
        calc m.val + rLimbs w₀ b b' * j.val
            < rLimbs w₀ b b' + rLimbs w₀ b b' * j.val := Nat.add_lt_add_right m.isLt _
          _ = (j.val + 1) * rLimbs w₀ b b' := by ring
          _ ≤ k * rLimbs w₀ b b' := Nat.mul_le_mul_right _ j.isLt
      change z2.1.mem (hashBase + 1 + (m.val + rLimbs w₀ b b' * j.val)) =
        getLimb (rChunk w₀ b b') (ReducedKWise.extractBot hashBase w₀ b b' k z2.1.mem j).val m.val
      rw [ReducedKWise.getLimb_extractBot_val, wordOfNat_val_of_lt (hlt2 _ hidx_lt)]
    · change z2.1.mem a = x.mem a
      rw [hframe2 a (by omega)]
      exact hframe1 a (by omega)
  refine ⟨m9.eval.map fun z => ⟨(z.1.extend f9 x.toData).regs, z.1.mem, x.frontier⟩, ?_, ?_, ?_⟩
  · have hop : ∀ {r₁ r₂ : ℕ} (f : Fin r₁ → Fin r₂) (b : BinOp) (d i j : Fin r₁),
        WordRAM.Op.rename f (.exactBin b d i j) = .exactBin b (f d) (f i) (f j) := by
      intro _ _ f b d i j
      dsimp only [WordRAM.Op.exactBin, WordRAM.Op.rename]
      congr 1; funext a; fin_cases a <;> rfl
    have hcode : RCode.ofCode (resampleHashCode9.rename f9) =
        resampleHashCode rBase rMaskM rBotWords rMaskC rPtr rEnd rMask rOne rVal := by
      dsimp only [resampleHashCode9, resampleHashCode, randFillRLoop, randFillRBody,
        Tabulation.randFillLoop, Tabulation.randFillBody, Code.rename, Cond.rename, RCode.ofCode]
      simp only [hop]
      rfl
    exact hcode ▸ ExecRCodeDist.of_execRandBounded_rename_le hf9 hL (by omega) hb9
      fun z hz => (hsupp9 z hz).1.le
  · rw [PMF.map_comp]
    dsimp only [Function.comp_def, m9, resampleHashComp9]
    rw [ProbComp.eval_bind, PMF.map_bind]
    set x0 := x.toData.comap f9
    set x1 := (((x0.set 4 hashBase).set 7 1).set 5 (hashBase + 1)).set 6 (2 ^ (w₀ - 1) - 1)
    set m1 := Tabulation.randFillComp (w₀ - 1) hashBase 1 (x1.comap fillMap9)
    have hm1_unif : m1.eval.map
        (fun z1 => ReducedKWise.extractTop hashBase w₀ z1.1.mem) =
        PMF.uniformOfFintype (ReducedTopSeed w₀) := by
      have hc1 : (fun z1 : Data 6 × ℕ => ReducedKWise.extractTop hashBase w₀ z1.1.mem) =
          ReducedKWise.topSliceEquiv w₀ ∘
            fun z1 => Tabulation.extractSlice hashBase (w₀ - 1) 1 z1.1.mem := rfl
      rw [hc1, ← PMF.map_comp, Tabulation.map_extractSlice_eval_randFillComp,
        PMF.uniformOfFintype_map_equiv]
    have hinner : ∀ z1 : Data 6 × ℕ,
        (let y1 := z1.1.extend fillMap9 x1
         let x2 := ((y1.set 4 (hashBase + 1)).set 5 (hashBase + 1 + k * rLimbs w₀ b b')).set 6
           (2 ^ rChunk w₀ b b' - 1)
         (do let z2 ← Tabulation.randFillComp (rChunk w₀ b b') (hashBase + 1)
               (k * rLimbs w₀ b b') (x2.comap fillMap9)
             pure (z2.1.extend fillMap9 x2,
               1 + (1 + (1 + (1 + (z1.2 + (1 + (1 + (1 + z2.2))))))))).eval).map
          (fun z : Data 9 × ℕ => ReducedKWise.extractSeed hashBase w₀ b b' k z.1.mem) =
        (PMF.uniformOfFintype (ReducedBotSeed w₀ b b' k)).map
          (fun β => (ReducedKWise.extractTop hashBase w₀ z1.1.mem, β)) := fun z1 => by
      dsimp only
      set y1 := z1.1.extend fillMap9 x1
      set x2 := ((y1.set 4 (hashBase + 1)).set 5 (hashBase + 1 + k * rLimbs w₀ b b')).set 6
        (2 ^ rChunk w₀ b b' - 1)
      rw [bind_pure_comp, ProbComp.eval_map, PMF.map_comp]
      dsimp only [Function.comp_def, Data.extend]
      have hcongr : ((Tabulation.randFillComp (rChunk w₀ b b') (hashBase + 1)
            (k * rLimbs w₀ b b') (x2.comap fillMap9)).eval).map
            (fun z2 : Data 6 × ℕ => ReducedKWise.extractSeed hashBase w₀ b b' k z2.1.mem) =
          ((Tabulation.randFillComp (rChunk w₀ b b') (hashBase + 1)
            (k * rLimbs w₀ b b') (x2.comap fillMap9)).eval).map
            ((fun β => (ReducedKWise.extractTop hashBase w₀ z1.1.mem, β)) ∘
              ReducedKWise.botSliceEquiv w₀ b b' k ∘
              fun z2 : Data 6 × ℕ => Tabulation.extractSlice (hashBase + 1) (rChunk w₀ b b')
                (k * rLimbs w₀ b b') z2.1.mem) := by
        refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun z2 hz2 => ?_
        rw [ProbComp.support_eval] at hz2
        obtain ⟨_, _, _, _, _, _, _, hframe2⟩ := Tabulation.mem_support_randFillComp hz2
        have htop_eq : ReducedKWise.extractTop hashBase w₀ z2.1.mem =
            ReducedKWise.extractTop hashBase w₀ z1.1.mem := by
          dsimp only [ReducedKWise.extractTop]; congr 1 with idx : 1
          dsimp only [Tabulation.extractSlice]
          rw [hframe2 (hashBase + idx.val) (Or.inl (by have := idx.isLt; omega))]; rfl
        dsimp only [Function.comp_apply, ReducedKWise.extractSeed, ReducedKWise.extractBot]
        rw [htop_eq]
      rw [hcongr, ← PMF.map_comp, ← PMF.map_comp, Tabulation.map_extractSlice_eval_randFillComp,
        PMF.uniformOfFintype_map_equiv]
    have hbind : m1.eval.bind _ =
        m1.eval.bind (fun z1 => (PMF.uniformOfFintype (ReducedBotSeed w₀ b b' k)).map
          (fun β => (ReducedKWise.extractTop hashBase w₀ z1.1.mem, β))) :=
      congrArg _ (funext hinner)
    have hmap_bind :
        m1.eval.bind (fun z1 => (PMF.uniformOfFintype (ReducedBotSeed w₀ b b' k)).map
          (fun β => (ReducedKWise.extractTop hashBase w₀ z1.1.mem, β))) =
        (m1.eval.map (fun z1 => ReducedKWise.extractTop hashBase w₀ z1.1.mem)).bind
          (fun α => (PMF.uniformOfFintype (ReducedBotSeed w₀ b b' k)).map (α, ·)) := by
      rw [PMF.bind_map]; rfl
    rw [hbind, hmap_bind, hm1_unif, PMF.uniformOfFintype_prod]
  · intro y hy
    supp_cases hy with ⟨z, hz, rfl⟩
    rw [ProbComp.support_eval] at hz
    obtain ⟨_, hr0, hr1, hr2, hr3, hseed, hframe⟩ := hsupp9 z hz
    refine ⟨rfl, hseed, hframe, fun j hj => ?_⟩
    by_cases hjr : j ∈ Set.range f9
    · rcases hjr with ⟨i, rfl⟩
      have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        fin_cases i <;> simp_all [f9]
      change ((z.1.extend f9 x.toData).comap f9).regs i = x.regs (f9 i)
      rw [Data.comap_extend hf9]
      rcases hi4 with rfl | rfl | rfl | rfl
      · exact hr0.trans hbase.symm
      · exact hr1.trans hmaskM.symm
      · exact hr2.trans hbot.symm
      · exact hr3.trans hmaskC.symm
    · exact Data.extend_regs_of_notMem z.1 x.toData hjr

end Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
