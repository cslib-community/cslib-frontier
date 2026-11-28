/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.Primitives
public import CslibFrontier.DataStructure.HashFamily.WordRAM.KWise
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Runtime Trinomial-Step, Power-of-Three, and `HashParams` Core Evaluators

Implements the bounded `trinomialStepAux` and `3 ^ e` loops together with the read-only
`computeHashCoreProg` subroutine computing `((w0, minW0), (c, (l0, p)))` for `mkHashParams`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ParamsComputeAux

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
open Cslib.Probability

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read

/-! ## Bounded `trinomialStepAux` and `3 ^ e` Loops -/

private def trinomStepProg : ℕ × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (hdrAddr, (rem, acc)) => do
    let _ ← Memory.read hdrAddr
    if 2 < rem then pure ((rem + 2) / 3, acc + 1) else pure (rem, acc)

private def TrinomStepPre (w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (hdrAddr, (rem, acc)), s =>
    hdrAddr < s.frontier ∧ Fits w (rem + 2) ∧ Fits w (acc + 1) ∧ Fits w 3

private theorem realizesBounded_trinomStep :
    RealizesBounded .exact trinomStepProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ × ℕ))
      TrinomStepPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨hdrAddr, ⟨rem, acc⟩⟩
    obtain ⟨hfr, hrem2, hacc1, h3⟩ := h
    try dsimp only at *)
  all_goals try omega
  exact h3.of_le (by omega)

private theorem memoryCost_trinomStep_ge_one (x : ℕ × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (trinomStepProg x) s := by
  rcases x with ⟨hdrAddr, ⟨rem, acc⟩⟩
  dsimp only [trinomStepProg]
  rw [Realization.memoryCost_bind', prog_memoryCost_read]
  split_ifs <;> omega

private theorem trinomLoop_spec {w hdrAddr B : ℕ} {s₀ : Memory.State}
    (hfr : hdrAddr < s₀.frontier) (hB2 : Fits w (B + 2)) (h3 : Fits w 3) :
    let prog := iterate trinomStepProg hdrAddr B (B, 0)
    iterationSafe trinomStepProg TrinomStepPre w hdrAddr B (B, 0) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ B ∧
    (Memory.spec 0).clientState s₀ prog = s₀ ∧
    ((Memory.spec 0).clientResult s₀ prog).2 = trinomialStepAux B := by
  intro prog
  have ht_le : trinomialStepAux B ≤ B :=
    Cslib.DataStructure.HashFamily.WordRAM.KWise.trinomialStepAux_le B
  obtain ⟨hsafe, h⟩ := FramedTriple.iterate (w := w) (s := s₀) (c := 1) (S := ∅)
    (body := trinomStepProg) (safe := TrinomStepPre) (d := hdrAddr) (n := B) (a₀ := (B, 0))
    (Q := fun r t => r.2 = trinomialStepAux B ∧ t = s₀)
    (fun k st t => t = s₀ ∧ st.1 ≤ B ∧ st.1 ≤ B - k + 2 ∧
      st.2 + trinomialStepAux st.1 = trinomialStepAux B) ⟨rfl, le_rfl, by omega, Nat.zero_add _⟩
    (fun k hk ⟨rem, acc⟩ t ⟨ht, hle_B, hrem_bd, hsum⟩ _ => by
      subst ht
      refine ⟨⟨hfr, hB2.of_le (by omega), hB2.of_le (by omega), h3⟩, ?_⟩
      dsimp only [trinomStepProg] at hle_B hrem_bd hsum ⊢
      framed_triple
      dsimp only
      rw [trinomialStepAux, ite_eq_right (by omega)] at hsum
      exact ⟨rfl, by omega, by omega, by omega⟩)
    (fun ⟨rem, acc⟩ t ⟨ht, _, hrem_end, hsum_end⟩ _ => ⟨by
      rw [trinomialStepAux, ite_eq_left (by omega)] at hsum_end; omega, ht⟩)
  obtain ⟨hv, hc, -, hres, hst⟩ := framedTriple_iff_realization.mp h
  exact ⟨hsafe, hv, by simpa only [one_mul] using hc, hst, hres⟩

private def trinomProg : ℕ × ℕ → Memory.Prog ℕ
  | (hdrAddr, B) => do
    let (_, res) ← iterate trinomStepProg hdrAddr B (B, 0)
    pure res

private def TrinomPre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (hdrAddr, B), s => hdrAddr < s.frontier ∧ Fits w (B + 2) ∧ Fits w 3

private theorem realizesBounded_trinom :
    RealizesBounded .exact trinomProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      TrinomPre (fun _ _ => 0) := by
  have htr := RealizesBounded.iterate₀ (WordEncoding.encode (α := ℕ))
    (WordEncoding.encode (α := ℕ × ℕ)) realizesBounded_trinomStep memoryCost_trinomStep_ge_one
  realize
  rcases d with ⟨hdrAddr, B⟩
  obtain ⟨hfr, hB2, h3⟩ := h
  exact (trinomLoop_spec hfr hB2 h3).1

private theorem trinomProg_spec {w hdrAddr B : ℕ} {s₀ : Memory.State}
    (hfr : hdrAddr < s₀.frontier) (hB2 : Fits w (B + 2)) (h3 : Fits w 3) :
    let prog := trinomProg (hdrAddr, B)
    TrinomPre w (hdrAddr, B) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ B ∧
    (Memory.spec 0).clientState s₀ prog = s₀ ∧
    (Memory.spec 0).clientResult s₀ prog = trinomialStepAux B := by
  intro prog
  obtain ⟨_, hv, hc, hst, hres⟩ := trinomLoop_spec hfr hB2 h3
  dsimp only [prog, trinomProg]
  rw [validHistory_bind', Realization.memoryCost_bind', StateTransitionSpec.clientState_bind,
    prog_clientResult_bind, hst]
  rcases hp : (Memory.spec 0).clientResult s₀
    (iterate trinomStepProg hdrAddr B (B, 0)) with ⟨_, r⟩
  rw [hp] at hres
  exact ⟨⟨hfr, hB2, h3⟩, ⟨hv, trivial⟩, by dsimp only; rw [memoryCost_pure]; omega, rfl, hres⟩

private def pow3StepProg : ℕ × ℕ → Memory.Prog ℕ
  | (hdrAddr, acc) => do
    let _ ← Memory.read hdrAddr
    pure (acc + acc + acc)

private def Pow3StepPre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (hdrAddr, acc), s => hdrAddr < s.frontier ∧ Fits w (3 * acc)

private theorem realizesBounded_pow3Step :
    RealizesBounded .exact pow3StepProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      Pow3StepPre (fun _ _ => 0) := by
  realize
  rcases d with ⟨hdrAddr, acc⟩
  obtain ⟨hfr, h3⟩ := h
  dsimp only at *
  exact h3.of_le (by omega)

private theorem memoryCost_pow3Step_ge_one (x : ℕ × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (pow3StepProg x) s := by
  rcases x with ⟨hdrAddr, acc⟩
  dsimp only [pow3StepProg]
  rw [Realization.memoryCost_bind', prog_memoryCost_read]; omega

private theorem pow3Loop_spec {w hdrAddr e : ℕ} {s₀ : Memory.State}
    (hfr : hdrAddr < s₀.frontier) (hfit : Fits w (3 ^ e)) :
    let prog := iterate pow3StepProg hdrAddr e 1
    iterationSafe pow3StepProg Pow3StepPre w hdrAddr e 1 s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ e ∧
    (Memory.spec 0).clientState s₀ prog = s₀ ∧
    (Memory.spec 0).clientResult s₀ prog = 3 ^ e := by
  intro prog
  obtain ⟨hsafe, h⟩ := FramedTriple.iterate (w := w) (s := s₀) (c := 1) (S := ∅)
    (body := pow3StepProg) (safe := Pow3StepPre) (d := hdrAddr) (n := e) (a₀ := 1)
    (Q := fun r t => t = s₀ ∧ r = 3 ^ e) (fun k acc t => t = s₀ ∧ acc = 3 ^ k) ⟨rfl, rfl⟩
    (fun k hk acc t ⟨ht, hacc⟩ _ => by
      subst ht hacc
      have hle : 3 * 3 ^ k ≤ 3 ^ e := by
        calc 3 * 3 ^ k = 3 ^ (k + 1) := by rw [pow_succ']
          _ ≤ 3 ^ e := Nat.pow_le_pow_right (by decide) hk
      refine ⟨⟨hfr, hfit.of_le hle⟩, ?_⟩
      dsimp only [pow3StepProg]
      framed_triple)
    (fun _ _ h _ => h)
  obtain ⟨hv, hc, -, hst, hres⟩ := framedTriple_iff_realization.mp h
  exact ⟨hsafe, hv, by simpa only [one_mul] using hc, hst, hres⟩

private def pow3Prog : ℕ × ℕ → Memory.Prog ℕ
  | (hdrAddr, e) => do
    let res ← iterate pow3StepProg hdrAddr e 1
    let z ← pure 0
    pure (res + z)

private def Pow3Pre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (hdrAddr, e), s => hdrAddr < s.frontier ∧ Fits w (3 ^ e)

private theorem realizesBounded_pow3 :
    RealizesBounded .exact pow3Prog
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      Pow3Pre (fun _ _ => 0) := by
  have hp3 := RealizesBounded.iterate₀ (WordEncoding.encode (α := ℕ))
    (WordEncoding.encode (α := ℕ)) realizesBounded_pow3Step memoryCost_pow3Step_ge_one
  realize
  all_goals (
    rcases d with ⟨hdrAddr, e⟩
    obtain ⟨hfr, hfit⟩ := h
    dsimp only at *
    first
    | exact (pow3Loop_spec hfr hfit).1
    | exact hfit.of_le (Nat.one_le_pow e 3 (by decide))
    | (rw [(pow3Loop_spec hfr hfit).2.2.2.2]; exact hfit))

private theorem pow3Prog_spec {w hdrAddr e : ℕ} {s₀ : Memory.State}
    (hfr : hdrAddr < s₀.frontier) (hfit : Fits w (3 ^ e)) :
    let prog := pow3Prog (hdrAddr, e)
    Pow3Pre w (hdrAddr, e) s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ e ∧
    (Memory.spec 0).clientState s₀ prog = s₀ ∧
    (Memory.spec 0).clientResult s₀ prog = 3 ^ e := by
  intro prog
  obtain ⟨_, hv, hc, hst, hres⟩ := pow3Loop_spec hfr hfit
  dsimp only [prog, pow3Prog]; simp only [pure_bind, Nat.add_zero]
  rw [validHistory_bind', Realization.memoryCost_bind', StateTransitionSpec.clientState_bind,
    prog_clientResult_bind, hst, StateTransitionSpec.clientState_pure, prog_clientResult_pure,
    memoryCost_pure, hres]
  exact ⟨⟨hfr, hfit⟩, ⟨hv, trivial⟩, by omega, rfl, rfl⟩

/-! ## `computeHashCoreProg` and Arithmetic Invariants -/

private theorem fits_hashShifts {w t : ℕ} (hc_lt : 2 * reducedChunkBits t < w)
    (h225 : Fits w 225) :
    Fits w (3 ^ (t - 3)) ∧ Fits w (3 ^ min t 3) ∧
      Fits w (min (2 * reducedChunkBits t) (Nat.log 2 (w / (2 * reducedChunkBits t))) + 1) := by
  have hw_fit : Fits w w := Nat.lt_two_pow_self
  exact ⟨hw_fit.of_le ((Nat.le_mul_of_pos_left _ two_pos).trans hc_lt.le),
    h225.of_le ((reducedHalfLimbs_le t).trans (by decide)),
    hw_fit.of_le (lt_of_le_of_lt (Nat.min_le_left _ _) hc_lt)⟩

/-- Pure arithmetic invariants for `computeHashCoreProg` and `writeHashParamsSubProg`. -/
theorem computeHashCore_arith {w U N dstMetaBase : ℕ}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let B := reducedTargetBits (epochQBits U N) (epochHashB N) (totalMicroBits N)
    let t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
    let c := reducedChunkBits t
    8 ≤ w ∧ epochQBits U N ≤ w ∧ totalMicroBits N ≤ w ∧ Nat.log 2 N < w ∧
    2 * c < w ∧ B ≤ 3 * Nat.log 2 N + 3 ∧ 2 * c ≤ N + 8 ∧
    Fits w (B + 2) ∧ Fits w (3 ^ (t - 3)) ∧ Fits w (3 ^ min t 3) ∧
    Fits w (min (2 * c) (Nat.log 2 (w / (2 * c))) + 1) := by
  intro B t c
  have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
  have hw8 : 8 ≤ w := eight_le_of_fits_225 h225
  have hw0_le : epochQBits U N ≤ w := qBits_le_of_le_pow hw hU.le
  have hlogN_lt : Nat.log 2 N < w := Nat.log_lt_of_lt_pow (by omega) (hU.of_le hNU)
  have hb'_le : totalMicroBits N ≤ w := (totalMicroBits_eq_log N).symm ▸ hlogN_lt.le
  have hfit_hash := fits_hash_of_fits_offCompItems hfit_dst
  have hc_le : 2 * c ≤ w := two_mul_reducedChunkBits_le hw0_le hb'_le (by omega)
  have hc_lt : 2 * c < w := ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space hc_le hfit_hash
  have hB_le : B ≤ 3 * Nat.log 2 N + 3 := by
    dsimp only [B, reducedTargetBits, epochHashB]
    rw [totalMicroBits_eq_log]; omega
  have hB2_fit : Fits w (B + 2) := (fits_three_mul_w_add_five h225).of_le (by omega)
  obtain ⟨hc_fit, hl0_fit, hp_fit⟩ := fits_hashShifts (t := t) hc_lt h225
  have h2c_le : 2 * c ≤ N + 8 :=
    ((@Nat.lt_two_pow_self (2 * c)).trans_le
      ((two_pow_two_mul_reducedChunkBits_hash_le U N).trans_eq (Nat.add_comm 8 N))).le
  exact ⟨hw8, hw0_le, hb'_le, hlogN_lt, hc_lt, hB_le, h2c_le, hB2_fit, hc_fit, hl0_fit, hp_fit⟩

private def computeHashTargetProg : ℕ × (ℕ × ℕ) → Memory.Prog (ℕ × (ℕ × ℕ))
  | (hdrBase, (qBitsVal, logN)) => do
    let w0 ← maxNatProg (qBitsVal, 1)
    let minW0 ← minNatProg (w0, (logN + 1) * 3)
    let maxB' ← maxNatProg (logN, 1)
    let targB ← maxNatProg (minW0, maxB')
    let t ← trinomProg (hdrBase, targB)
    pure (w0, (minW0, t))

private def ComputeHashTargetPre (w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (hdrBase, (qBitsVal, logN)), s =>
    qBitsVal ≤ w ∧ logN < w ∧ hdrBase < s.frontier ∧ Fits w 225

private theorem computeHashTargetProg_exec {w hdrBase qBitsVal logN : ℕ} {s : Memory.State}
    (_hq : qBitsVal ≤ w) (hlog : logN < w) (hhdr : hdrBase < s.frontier) (h225 : Fits w 225) :
    let d := (hdrBase, (qBitsVal, logN))
    let w0 := max qBitsVal 1
    let minW0 := min w0 ((logN + 1) * 3)
    let targB := max minW0 (max logN 1)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeHashTargetProg d)) ∧
    (Memory.spec 0).clientState s (computeHashTargetProg d) = s ∧
    (Memory.spec 0).clientResult s (computeHashTargetProg d) =
      (w0, (minW0, trinomialStepAux targB)) ∧
    memoryCost (computeHashTargetProg d) s ≤ 3 * logN + 3 := by
  intro d w0 minW0 targB
  have htarg_le : targB ≤ 3 * logN + 3 := by dsimp only [targB, minW0]; omega
  have hB2_fit : Fits w (targB + 2) := (fits_three_mul_w_add_five h225).of_le (by omega)
  obtain ⟨_, hv_tr, hc_tr, hst_tr, hres_tr⟩ :=
    trinomProg_spec (B := max (min (max qBitsVal 1) ((logN + 1) * 3)) (max logN 1)) hhdr hB2_fit
      (h225.of_le (by decide))
  dsimp only [d, computeHashTargetProg]
  iterate 5 (
    rw [validHistory_bind', StateTransitionSpec.clientState_bind, prog_clientResult_bind,
      Realization.memoryCost_bind']
    first
      | rw [clientState_maxNatProg, clientResult_maxNatProg, memoryCost_maxNatProg]
      | rw [clientState_minNatProg, clientResult_minNatProg, memoryCost_minNatProg]
      | rw [hst_tr, hres_tr, StateTransitionSpec.clientState_pure, prog_clientResult_pure,
          memoryCost_pure])
  exact ⟨⟨validHistory_maxNatProg _ _, validHistory_minNatProg _ _, validHistory_maxNatProg _ _,
    validHistory_maxNatProg _ _, hv_tr, trivial⟩, rfl, rfl, by omega⟩

private theorem realizesBounded_computeHashTarget :
    RealizesBounded .exact computeHashTargetProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      ComputeHashTargetPre (fun _ _ => 0) := by
  have hmax := realizesBounded_maxNat
  have hmin := realizesBounded_minNat
  have htr := realizesBounded_trinom
  realize
  all_goals (
    rcases d with ⟨hdrBase, ⟨qBitsVal, logN⟩⟩
    obtain ⟨hq, hlog, hhdr, h225⟩ := h
    try dsimp only at *
    have h3w : Fits w (3 * w + 5) := fits_three_mul_w_add_five h225
    repeat rw [clientState_maxNatProg]
    repeat rw [clientResult_maxNatProg]
    repeat rw [clientState_minNatProg]
    repeat rw [clientResult_minNatProg])
  all_goals (
    first
    | exact ⟨hhdr, h3w.of_le (by omega), h225.of_le (by decide)⟩
    | exact h3w.of_le (by omega))

private def computeHashShiftsProg : (ℕ × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((hdrBase, wVal), t) => do
    let tSub3 ← subSatProg (t, 3)
    let minT3 ← minNatProg (t, 3)
    let c ← pow3Prog (hdrBase, tSub3)
    let l0 ← pow3Prog (hdrBase, minT3)
    let twoC := c + c
    let p ← log2CapProg (hdrBase, (twoC, wVal / twoC))
    pure (c, (l0, p))

private def ComputeHashShiftsPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((hdrBase, wVal), t), s =>
    0 < w ∧ wVal = w ∧ hdrBase < s.frontier ∧ 2 * reducedChunkBits t < w ∧ Fits w 225

private theorem computeHashShiftsProg_exec {w hdrBase t : ℕ} {s : Memory.State}
    (_hw : 0 < w) (hhdr : hdrBase < s.frontier) (hc_lt : 2 * reducedChunkBits t < w)
    (h225 : Fits w 225) :
    let d := ((hdrBase, w), t)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeHashShiftsProg d)) ∧
    (Memory.spec 0).clientState s (computeHashShiftsProg d) = s ∧
    (Memory.spec 0).clientResult s (computeHashShiftsProg d) =
      (reducedChunkBits t, (reducedHalfLimbs t, reducedPackShift t w)) ∧
    memoryCost (computeHashShiftsProg d) s ≤ t + 2 * reducedChunkBits t + 3 := by
  intro d
  have hw_fit : Fits w w := Nat.lt_two_pow_self
  obtain ⟨hc_fit, hl0_fit, hp_fit⟩ := fits_hashShifts hc_lt h225
  obtain ⟨_, hv_p1, hc_p1, hst_p1, hres_p1⟩ := pow3Prog_spec (e := t - 3) hhdr hc_fit
  obtain ⟨_, hv_p2, hc_p2, hst_p2, hres_p2⟩ := pow3Prog_spec (e := min t 3) hhdr hl0_fit
  obtain ⟨_, hv_lg, hc_lg, hst_lg, hres_lg⟩ :=
    log2CapProg_spec (K := 2 * reducedChunkBits t) (x₀ := w / (2 * reducedChunkBits t)) hhdr
      (hw_fit.of_le (Nat.div_le_self _ _)) hp_fit
  have h2c_sum : 3 ^ (t - 3) + 3 ^ (t - 3) = 2 * reducedChunkBits t := (two_mul _).symm
  dsimp only [d, computeHashShiftsProg]
  iterate 5 (
    rw [validHistory_bind', StateTransitionSpec.clientState_bind, prog_clientResult_bind,
      Realization.memoryCost_bind']
    first
      | rw [clientState_subSatProg, clientResult_subSatProg, memoryCost_subSatProg]
      | rw [clientState_minNatProg, clientResult_minNatProg, memoryCost_minNatProg]
      | rw [hst_p1, hres_p1]
      | rw [hst_p2, hres_p2, h2c_sum]
      | rw [hst_lg, hres_lg, StateTransitionSpec.clientState_pure, prog_clientResult_pure,
          memoryCost_pure])
  exact ⟨⟨validHistory_subSatProg _ _, validHistory_minNatProg _ _, hv_p1, hv_p2, hv_lg, trivial⟩,
    rfl, rfl, by omega⟩

private theorem realizesBounded_computeHashShifts :
    RealizesBounded .exact computeHashShiftsProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      ComputeHashShiftsPre (fun _ _ => 0) := by
  have hsub := realizesBounded_subSat
  have hmin := realizesBounded_minNat
  have hp3 := realizesBounded_pow3
  have hlg := realizesBounded_log2Cap
  realize
  all_goals (
    rcases d with ⟨⟨hdrBase, wVal⟩, t⟩
    obtain ⟨hw, hwVal, hhdr, hc_lt, h225⟩ := h
    subst wVal
    try dsimp only at *
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    obtain ⟨hc_fit, hl0_fit, hp_fit⟩ := fits_hashShifts hc_lt h225
    repeat rw [clientState_subSatProg]
    repeat rw [clientResult_subSatProg]
    repeat rw [clientState_minNatProg]
    repeat rw [clientResult_minNatProg])
  all_goals try exact h225.of_le (by decide)
  all_goals try exact ⟨hhdr, hc_fit⟩
  all_goals (
    obtain ⟨_, _, _, hst_p1, hres_p1⟩ := pow3Prog_spec (e := t - 3) hhdr hc_fit
    repeat rw [hst_p1]
    repeat rw [hres_p1])
  all_goals try exact ⟨hhdr, hl0_fit⟩
  all_goals (
    obtain ⟨_, _, _, hst_p2, _⟩ := pow3Prog_spec (e := min t 3) hhdr hl0_fit
    have h2c_sum : 3 ^ (t - 3) + 3 ^ (t - 3) = 2 * reducedChunkBits t := (two_mul _).symm
    repeat rw [hst_p2]
    repeat rw [h2c_sum])
  all_goals try exact ⟨hhdr, hw_fit.of_le (Nat.div_le_self _ _), hp_fit⟩
  all_goals (
    have hc_pos := reducedChunkBits_pos t
    first
    | omega
    | exact hw_fit.of_le (by omega))

/-- Read-only core evaluator computing `((w0, minW0), (c, (l0, p)))` for `mkHashParams`. -/
def computeHashCoreProg :
    (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))
  | ((hdrBase, wVal), (qBitsVal, logN)) => do
    let (w0, (minW0, t)) ← computeHashTargetProg (hdrBase, (qBitsVal, logN))
    let (c, (l0, p)) ← computeHashShiftsProg ((hdrBase, wVal), t)
    pure ((w0, minW0), (c, (l0, p)))

/-- Precondition for `computeHashCoreProg`. -/
@[expose] def ComputeHashCorePre (w : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((hdrBase, wVal), (qBitsVal, logN)), s =>
    ∃ U N dstMetaBase,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      wVal = w ∧ qBitsVal = quotientBits U N ∧ logN = Nat.log 2 N ∧
      hdrBase < s.frontier ∧ Fits w (dstMetaBase + offCompItems U w N)

private theorem computeHashTargetProg_epoch {w U N hdrBase dstMetaBase : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hhdr : hdrBase < s.frontier) (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (hdrBase, (quotientBits U N, Nat.log 2 N))
    let t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
    ComputeHashTargetPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeHashTargetProg d)) ∧
    (Memory.spec 0).clientState s (computeHashTargetProg d) = s ∧
    (Memory.spec 0).clientResult s (computeHashTargetProg d) =
      (epochQBits U N, (min (epochQBits U N) (3 * epochHashB N), t)) ∧
    memoryCost (computeHashTargetProg d) s ≤ 3 * Nat.log 2 N + 3 := by
  intro d t
  have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
  obtain ⟨_, hw0_le, _, hlogN_lt, _, _, _, _, _, _, _⟩ :=
    computeHashCore_arith hw hN hNU hU hfit_dst
  have hq_le : quotientBits U N ≤ w := (le_max_left _ 1).trans hw0_le
  obtain ⟨hv_tg, hst_tg, hres_tg, hc_tg⟩ :=
    computeHashTargetProg_exec (s := s) hq_le hlogN_lt hhdr h225
  simp only [t, epochHashB, reducedTrinomialStep, reducedTargetBits, totalMicroBits_eq_log,
    mul_comm _ 3] at hres_tg ⊢
  exact ⟨⟨hq_le, hlogN_lt, hhdr, h225⟩, hv_tg, hst_tg, hres_tg, hc_tg⟩

/-- Functional specification and `≤ 7 * N + 20` cost bound for `computeHashCoreProg`. -/
theorem computeHashCoreProg_exec {w U N hdrBase dstMetaBase : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hhdr : hdrBase < s.frontier) (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := ((hdrBase, w), (quotientBits U N, Nat.log 2 N))
    let t := reducedTrinomialStep (epochQBits U N) (epochHashB N) (totalMicroBits N)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeHashCoreProg d)) ∧
    (Memory.spec 0).clientState s (computeHashCoreProg d) = s ∧
    (Memory.spec 0).clientResult s (computeHashCoreProg d) =
      ((epochQBits U N, min (epochQBits U N) (3 * epochHashB N)),
        (reducedChunkBits t, (reducedHalfLimbs t, reducedPackShift t w))) ∧
    memoryCost (computeHashCoreProg d) s ≤ 7 * N + 20 := by
  intro d t
  have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
  obtain ⟨_, _, _, _, hc_lt, hB_le, h2c_le, _, _, _, _⟩ :=
    computeHashCore_arith hw hN hNU hU hfit_dst
  obtain ⟨_, hv_tg, hst_tg, hres_tg, hc_tg⟩ :=
    computeHashTargetProg_epoch (s := s) hw hN hNU hU hhdr hfit_dst
  obtain ⟨hv_sh, hst_sh, hres_sh, hc_sh⟩ :=
    computeHashShiftsProg_exec (s := s) (t := t) hw hhdr hc_lt h225
  have hlog_le_N : Nat.log 2 N ≤ N := Nat.log_le_self 2 N
  have ht_le_N3 : t ≤ 3 * N + 3 :=
    (Cslib.DataStructure.HashFamily.WordRAM.KWise.trinomialStepAux_le _).trans (by omega)
  dsimp only [t] at hc_sh h2c_le ht_le_N3
  dsimp only [d, computeHashCoreProg]
  rw [validHistory_bind', StateTransitionSpec.clientState_bind, prog_clientResult_bind,
    Realization.memoryCost_bind', hst_tg, hres_tg]
  dsimp only
  rw [validHistory_bind', StateTransitionSpec.clientState_bind, prog_clientResult_bind,
    Realization.memoryCost_bind', hst_sh, hres_sh, StateTransitionSpec.clientState_pure,
    prog_clientResult_pure, memoryCost_pure]
  exact ⟨⟨hv_tg, hv_sh, trivial⟩, rfl, rfl, by omega⟩

/-- `computeHashCoreProg` compiles via `RealizesBounded .exact`. -/
theorem realizesBounded_computeHashCore :
    RealizesBounded .exact computeHashCoreProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      ComputeHashCorePre (fun _ _ => 0) := by
  have htg := realizesBounded_computeHashTarget
  have hsh := realizesBounded_computeHashShifts
  realize
  all_goals (
    rcases d with ⟨⟨hdrBase, wVal⟩, ⟨qBitsVal, logN⟩⟩
    obtain ⟨U, N, dstMetaBase, hw, hN, hNU, hU, hwVal, rfl, rfl, hhdr, hfit_dst⟩ := h
    subst wVal
    obtain ⟨hpre_tg, _, hst_tg, hres_tg, _⟩ :=
      computeHashTargetProg_epoch (s := s) hw hN hNU hU hhdr hfit_dst)
  · exact hpre_tg
  · obtain ⟨_, _, _, _, hc_lt, _, _, _, _, _, _⟩ :=
      computeHashCore_arith hw hN hNU hU hfit_dst
    rw [hst_tg, hres_tg]; dsimp only
    exact ⟨hw, rfl, hhdr, hc_lt, fits_const_of_offCompItems hfit_dst le_rfl⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ParamsComputeAux
