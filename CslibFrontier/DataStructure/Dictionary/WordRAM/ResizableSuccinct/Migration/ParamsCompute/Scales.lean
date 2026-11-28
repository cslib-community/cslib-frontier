/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute.Primitives
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Runtime Root-Header Copy, Logarithmic Scales, Bucket Scales, and `GlobalMeta` Bases

Implements the 8-word root-header writer (`writeRootHdrSubProg`) together with the read-only
evaluators for `(logN, qBitsVal, llf)` (`computeLogScalesProg`), compacted bucket/slab/tail scales
(`computeCompScalesProg`), and `GlobalMeta` region base offsets (`computeGmBasesProg`).
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

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Root Header Copy (`writeRootHdrSubProg`) -/

/-- Copy the 5 static root-header words `[U - 1, V - 1, w, keyBits U, valBits V]` from
`[srcHdrBase, +5)` and write the 8-word root header at `[dstMetaBase, +8)`, returning
`(w, (keyBits U, valBits V))`. -/
def writeRootHdrSubProg : (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))) => do
    let uSub1 ← Memory.read srcHdrBase
    let vSub1 ← Memory.read (srcHdrBase + 1)
    let wVal ← Memory.read (srcHdrBase + 2)
    let kBits ← Memory.read (srcHdrBase + 3)
    let vBits ← Memory.read (srcHdrBase + 4)
    Memory.write dstMetaBase uSub1
    Memory.write (dstMetaBase + 1) vSub1
    Memory.write (dstMetaBase + 2) wVal
    Memory.write (dstMetaBase + 3) kBits
    Memory.write (dstMetaBase + 4) vBits
    Memory.write (dstMetaBase + 5) N
    Memory.write (dstMetaBase + 6) n_cur
    Memory.write (dstMetaBase + 7) n_init_new
    pure (wVal, (kBits, vBits))

/-- Precondition for `writeRootHdrSubProg`. -/
@[expose] def WriteRootHdrSubPre (w : ℕ) :
    (ℕ × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new))), s =>
    srcHdrBase + 5 ≤ s.frontier ∧ dstMetaBase + 8 ≤ s.frontier ∧
    Fits w (s.mem srcHdrBase) ∧ Fits w (s.mem (srcHdrBase + 1)) ∧
    Fits w (s.mem (srcHdrBase + 2)) ∧ Fits w (s.mem (srcHdrBase + 3)) ∧
    Fits w (s.mem (srcHdrBase + 4)) ∧
    Fits w N ∧ Fits w n_cur ∧ Fits w n_init_new ∧ Fits w 7

/-- `writeRootHdrSubProg` compiles via `RealizesBounded .exact`. -/
theorem realizesBounded_writeRootHdrSub :
    RealizesBounded .exact writeRootHdrSubProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      WriteRootHdrSubPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨srcHdrBase, dstMetaBase⟩, ⟨N, ⟨n_cur, n_init_new⟩⟩⟩
    obtain ⟨hsrc, hdst, hm0, hm1, hm2, hm3, hm4, hN, hnc, hni, h7⟩ := h
    dsimp only at *)
  all_goals exact hmem.frontier_fits.of_le (by omega)

/-- Functional specification and `≤ 13` memory-cost bound for `writeRootHdrSubProg`. -/
theorem writeRootHdrSubProg_spec
    {w U V N_old n_old n_init_old srcHdrBase dstMetaBase N n_cur n_init_new : ℕ}
    {s : Memory.State}
    (hhdr : RootHeaderValid U V w N_old n_old n_init_old srcHdrBase s.mem)
    (hV : V ≤ 2 ^ w) (hN_fit : Fits w N) (hnc_fit : Fits w n_cur) (hni_fit : Fits w n_init_new)
    (h7 : Fits w 7) (hsrc_fr : srcHdrBase + 5 ≤ s.frontier)
    (hdst_fr : dstMetaBase + 8 ≤ s.frontier) :
    let d := ((srcHdrBase, dstMetaBase), (N, (n_cur, n_init_new)))
    let prog := writeRootHdrSubProg d
    let s' := (Memory.spec 0).clientState s prog
    WriteRootHdrSubPre w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = (w, (keyBits U, valBits V)) ∧
    s'.frontier = s.frontier ∧
    RootHeaderValid U V w N n_cur n_init_new dstMetaBase s'.mem ∧
    (∀ a, ¬(dstMetaBase ≤ a ∧ a < dstMetaBase + 8) → s'.mem a = s.mem a) ∧
    memoryCost prog s ≤ 13 := by
  intro d prog s'
  have hU := hhdr.fits_U
  have hw_fit : Fits w w := Nat.lt_two_pow_self
  have hm0 : Fits w (s.mem srcHdrBase) := by rw [hhdr.hdr_U]; exact hU.of_le (Nat.sub_le U 1)
  have hm1 : Fits w (s.mem (srcHdrBase + 1)) := by
    rw [hhdr.hdr_V]; have := hhdr.pos_V; change V - 1 < 2 ^ w; omega
  have hm2 : Fits w (s.mem (srcHdrBase + 2)) := by rw [hhdr.hdr_w]; exact hw_fit
  have hm3 : Fits w (s.mem (srcHdrBase + 3)) := by
    rw [hhdr.hdr_keyBits]; exact hw_fit.of_le (Nat.clog_le_of_le_pow hU.le)
  have hm4 : Fits w (s.mem (srcHdrBase + 4)) := by
    rw [hhdr.hdr_valBits]; exact hw_fit.of_le (Nat.clog_le_of_le_pow hV)
  refine ⟨⟨hsrc_fr, hdst_fr, hm0, hm1, hm2, hm3, hm4, hN_fit, hnc_fit, hni_fit, h7⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases s with ⟨mem, fr⟩
    dsimp only [prog, d, writeRootHdrSubProg] at hsrc_fr hdst_fr hm0 hm1 hm2 hm3 hm4 ⊢
    iterate 5 refine validHistory_read_step (by omega) ?_
    iterate 7 refine validHistory_write_step (by omega) (by assumption) ?_
    exact ⟨⟨show dstMetaBase + 7 < fr by omega, hni_fit⟩, trivial⟩
  · dsimp only [prog, d, writeRootHdrSubProg]
    simp only [prog_clientResult_bind, prog_clientResult_read, prog_runClient_state_read,
      prog_runClient_state_write, prog_clientResult_pure,
      hhdr.hdr_w, hhdr.hdr_keyBits, hhdr.hdr_valBits]
  · dsimp only [s', prog, d, writeRootHdrSubProg]
    simp only [StateTransitionSpec.clientState, prog_runClient_state_bind,
      prog_clientResult_read, prog_runClient_state_read, prog_runClient_state_write,
      prog_runClient_state_pure]
  · dsimp only [s', prog, d, writeRootHdrSubProg, StateTransitionSpec.clientState]
    simp only [prog_runClient_state_bind,
      prog_clientResult_read, prog_runClient_state_read, prog_runClient_state_write,
      prog_runClient_state_pure, hhdr.hdr_U, hhdr.hdr_V, hhdr.hdr_w, hhdr.hdr_keyBits,
      hhdr.hdr_valBits]
    refine ⟨hU, hhdr.pos_U, hhdr.pos_V, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (simp only [Function.update_apply]; split_ifs <;> omega)
  · intro a ha
    dsimp only [s', prog, d, writeRootHdrSubProg, StateTransitionSpec.clientState]
    simp only [prog_runClient_state_bind, prog_clientResult_read, prog_runClient_state_read,
      prog_runClient_state_write, prog_runClient_state_pure, Function.update_apply]
    split_ifs <;> omega
  · dsimp only [prog, d, writeRootHdrSubProg]
    simp only [Realization.memoryCost_bind', prog_memoryCost_read, prog_runClient_state_read,
      prog_memoryCost_write, prog_runClient_state_write, memoryCost_pure]
    omega

/-! ## Logarithmic Scales (`computeLogScalesProg`) -/

/-- Branching formula for `globalMetaLen N` from `gmSlabMetaBase N + maxFullSlabs N * 4`. -/
theorem globalMetaLen_cond_eq (N : ℕ) :
    (if bucketBits N = 0 then 4
     else gmSlabMetaBase N + maxFullSlabs N * 4) =
      globalMetaLen N := by
  by_cases hb0 : bucketBits N = 0
  · simp [globalMetaLen, globalMetaVarLen, hb0]
  · rw [ite_eq_right hb0]
    have hpos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have hlen := gmSlabMetaBase_add_eq_globalMetaLen hpos
    linarith

/-- Pure arithmetic bounds for `computeLogScalesProg` and `computeCompScalesProg`. -/
theorem computeLogScales_arith {w U N : ℕ}
    (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (h225 : Fits w 225) :
    Nat.log 2 N < w ∧
    Fits w (max N 4) ∧
    2 ≤ Nat.clog 2 (max N 4) ∧
    Nat.clog 2 (max N 4) ≤ w ∧
    Nat.log 2 (max N 4 - 1) + 1 = Nat.clog 2 (max N 4) ∧
    Nat.log 2 (Nat.clog 2 (max N 4) - 1) + 1 = Dynamic.logLogFactor N ∧
    Fits w (3 * Dynamic.logLogFactor N) := by
  have hN_fit : Fits w N := hU.of_le hNU
  have hlogN_lt : Nat.log 2 N < w := by
    by_contra hge
    have : 2 ^ w ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right two_pos (by omega)
    have := Nat.pow_log_le_self 2 (by omega : N ≠ 0)
    change N < 2 ^ w at hN_fit; omega
  have hmaxN4_fit : Fits w (max N 4) := max_lt hN_fit (h225.of_le (by decide))
  have hclog1_ge2 : 2 ≤ Nat.clog 2 (max N 4) := by
    have : Nat.clog 2 4 = 2 := by decide
    rw [← this]; exact Nat.clog_mono_right 2 (le_max_right N 4)
  have hclog1_le_w : Nat.clog 2 (max N 4) ≤ w :=
    Nat.clog_le_of_le_pow (max_le hN_fit.le ((show (4 : ℕ) ≤ 225 by decide).trans h225.le))
  have hclog1_eq : Nat.log 2 (max N 4 - 1) + 1 = Nat.clog 2 (max N 4) :=
    (clog2_eq_log2_pred_add_one (lt_of_lt_of_le (by decide : 1 < 4) (le_max_right N 4))).symm
  have hllf_eq : Nat.log 2 (Nat.clog 2 (max N 4) - 1) + 1 = Dynamic.logLogFactor N :=
    (clog2_eq_log2_pred_add_one (lt_of_lt_of_le (by decide : 1 < 2) hclog1_ge2)).symm
  have hllf_le_w : Dynamic.logLogFactor N ≤ w := by
    have hlog_lt : Nat.log 2 (Nat.clog 2 (max N 4) - 1) < w :=
      (Nat.log_le_self 2 _).trans_lt (by omega)
    omega
  have h3llf_fit : Fits w (3 * Dynamic.logLogFactor N) :=
    (fits_three_mul_w_add_five h225).of_le (by omega)
  exact ⟨hlogN_lt, hmaxN4_fit, hclog1_ge2, hclog1_le_w, hclog1_eq, hllf_eq, h3llf_fit⟩

/-- Compute `(logN, (qBitsVal, llf))` from `(dstMetaBase, (N, kBits))` via `log2CapProg`. -/
def computeLogScalesProg : ℕ × (ℕ × ℕ) → Memory.Prog (ℕ × (ℕ × ℕ))
  | (dstMetaBase, (N, kBits)) => do
    let logN ← log2CapProg (dstMetaBase, (N, N))
    let maxN4 ← maxNatProg (N, 4)
    let maxN4Sub1 ← subSatProg (maxN4, 1)
    let logMaxN4Sub1 ← log2CapProg (dstMetaBase, (maxN4Sub1, maxN4Sub1))
    let clogSub1 ← subSatProg (logMaxN4Sub1 + 1, 1)
    let logClogSub1 ← log2CapProg (dstMetaBase, (clogSub1, clogSub1))
    let llf := logClogSub1 + 1
    let bBits ← subSatProg (logN, llf * 3)
    let qBitsVal ← subSatProg (kBits, bBits)
    pure (logN, (qBitsVal, llf))

/-- Precondition for `computeLogScalesProg`. -/
@[expose] def ComputeLogScalesPre (w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (dstMetaBase, (N, kBits)), s =>
    ∃ U,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ kBits = keyBits U ∧
      dstMetaBase < s.frontier ∧ Fits w 225

/-- Functional specification and `≤ 3 * N + 6` cost bound for `computeLogScalesProg`. -/
theorem computeLogScalesProg_exec {w U dstMetaBase N : ℕ} {s : Memory.State}
    (_hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hdst_lt : dstMetaBase < s.frontier) (h225 : Fits w 225) :
    let d := (dstMetaBase, (N, keyBits U))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeLogScalesProg d)) ∧
    (Memory.spec 0).clientState s (computeLogScalesProg d) = s ∧
    (Memory.spec 0).clientResult s (computeLogScalesProg d) =
      (Nat.log 2 N, (quotientBits U N, Dynamic.logLogFactor N)) ∧
    memoryCost (computeLogScalesProg d) s ≤ 3 * N + 6 := by
  intro d
  have hw_fit : Fits w w := Nat.lt_two_pow_self
  have hN_fit : Fits w N := hU.of_le hNU
  obtain ⟨hlogN_lt, hmaxN4_fit, _, hclog1_le_w, hclog1_eq, hllf_eq, _⟩ :=
    computeLogScales_arith hN hNU hU h225
  obtain ⟨_, hv1, hc1, hst1, hres1⟩ :=
    log2CapProg_spec (K := N) (x₀ := N) hdst_lt hN_fit
      (hw_fit.of_le (by have := Nat.min_le_right N (Nat.log 2 N); omega))
  rw [Nat.min_eq_right (Nat.log_le_self 2 N)] at hres1
  obtain ⟨_, hv2, hc2, hst2, hres2⟩ :=
    log2CapProg_spec (K := max N 4 - 1) (x₀ := max N 4 - 1) hdst_lt
      (hmaxN4_fit.of_le (Nat.sub_le _ _))
      (hw_fit.of_le (by have := Nat.min_le_right (max N 4 - 1) (Nat.log 2 (max N 4 - 1)); omega))
  rw [Nat.min_eq_right (Nat.log_le_self 2 _)] at hres2
  obtain ⟨_, hv3, hc3, hst3, hres3⟩ :=
    log2CapProg_spec (K := Nat.clog 2 (max N 4) - 1) (x₀ := Nat.clog 2 (max N 4) - 1) hdst_lt
      (hw_fit.of_le (by omega))
      (hw_fit.of_le (by
        have := Nat.min_le_right (Nat.clog 2 (max N 4) - 1)
          (Nat.log 2 (Nat.clog 2 (max N 4) - 1)); omega))
  rw [Nat.min_eq_right (Nat.log_le_self 2 _)] at hres3
  have hclog_le_N3 : Nat.clog 2 (max N 4) - 1 ≤ N + 3 := by
    have := Nat.log_le_self 2 (max N 4 - 1); omega
  have h3llf_comm : Dynamic.logLogFactor N * 3 = 3 * Dynamic.logLogFactor N := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [d, computeLogScalesProg]
    rw [validHistory_bind', hst1, hres1]; refine ⟨hv1, ?_⟩
    rw [validHistory_bind', clientState_maxNatProg, clientResult_maxNatProg]
    refine ⟨validHistory_maxNatProg _ _, ?_⟩
    rw [validHistory_bind', clientState_subSatProg, clientResult_subSatProg]
    refine ⟨validHistory_subSatProg _ _, ?_⟩
    rw [validHistory_bind', hst2, hres2, hclog1_eq]; refine ⟨hv2, ?_⟩
    rw [validHistory_bind', clientState_subSatProg, clientResult_subSatProg]
    refine ⟨validHistory_subSatProg _ _, ?_⟩
    rw [validHistory_bind', hst3, hres3]; refine ⟨hv3, ?_⟩
    rw [hllf_eq, validHistory_bind', clientState_subSatProg, clientResult_subSatProg]
    refine ⟨validHistory_subSatProg _ _, ?_⟩
    rw [validHistory_bind', clientState_subSatProg]
    exact ⟨validHistory_subSatProg _ _, trivial⟩
  · dsimp only [d, computeLogScalesProg]
    rw [StateTransitionSpec.clientState_bind, hst1, hres1,
      StateTransitionSpec.clientState_bind, clientState_maxNatProg, clientResult_maxNatProg,
      StateTransitionSpec.clientState_bind, clientState_subSatProg, clientResult_subSatProg,
      StateTransitionSpec.clientState_bind, hst2, hres2, hclog1_eq,
      StateTransitionSpec.clientState_bind, clientState_subSatProg, clientResult_subSatProg,
      StateTransitionSpec.clientState_bind, hst3, hres3,
      StateTransitionSpec.clientState_bind, clientState_subSatProg,
      StateTransitionSpec.clientState_bind, clientState_subSatProg,
      StateTransitionSpec.clientState_pure]
  · dsimp only [d, computeLogScalesProg]
    rw [prog_clientResult_bind, hst1, hres1,
      prog_clientResult_bind, clientState_maxNatProg, clientResult_maxNatProg,
      prog_clientResult_bind, clientState_subSatProg, clientResult_subSatProg,
      prog_clientResult_bind, hst2, hres2, hclog1_eq,
      prog_clientResult_bind, clientState_subSatProg, clientResult_subSatProg,
      prog_clientResult_bind, hst3, hres3,
      hllf_eq, h3llf_comm, prog_clientResult_bind, clientState_subSatProg,
      clientResult_subSatProg, prog_clientResult_bind, clientState_subSatProg,
      clientResult_subSatProg, prog_clientResult_pure]
    rfl
  · dsimp only [d, computeLogScalesProg]
    rw [Realization.memoryCost_bind', hst1, hres1,
      Realization.memoryCost_bind', memoryCost_maxNatProg, clientState_maxNatProg,
      clientResult_maxNatProg,
      Realization.memoryCost_bind', memoryCost_subSatProg, clientState_subSatProg,
      clientResult_subSatProg,
      Realization.memoryCost_bind', hst2, hres2, hclog1_eq,
      Realization.memoryCost_bind', memoryCost_subSatProg, clientState_subSatProg,
      clientResult_subSatProg,
      Realization.memoryCost_bind', hst3, hres3,
      Realization.memoryCost_bind', memoryCost_subSatProg, clientState_subSatProg,
      Realization.memoryCost_bind', memoryCost_subSatProg, clientState_subSatProg,
      memoryCost_pure]
    omega

/-- `computeLogScalesProg` compiles via `RealizesBounded .exact`. -/
theorem realizesBounded_computeLogScales :
    RealizesBounded .exact computeLogScalesProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      ComputeLogScalesPre (fun _ _ => 0) := by
  have hmax := realizesBounded_maxNat
  have hsub := realizesBounded_subSat
  have hlg := realizesBounded_log2Cap
  realize
  all_goals (
    rcases d with ⟨dstMetaBase, ⟨N, kBits⟩⟩
    obtain ⟨U, hw, hN, hNU, hU, rfl, hdst_lt, h225⟩ := h
    try dsimp only at *
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    have hN_fit : Fits w N := hU.of_le hNU
    obtain ⟨hlogN_lt, hmaxN4_fit, _, hclog1_le_w, hclog1_eq, hllf_eq, h3llf⟩ :=
      computeLogScales_arith hN hNU hU h225
    have hp1 : Log2CapPre w (dstMetaBase, (N, N)) s :=
      ⟨hdst_lt, hN_fit, hw_fit.of_le (by have := Nat.min_le_right N (Nat.log 2 N); omega)⟩)
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hp1
  all_goals (
    obtain ⟨_, _, _, hst1, hres1⟩ := log2CapProg_spec hp1.1 hp1.2.1 hp1.2.2
    rw [Nat.min_eq_right (Nat.log_le_self 2 N)] at hres1
    repeat rw [hst1]
    repeat rw [clientState_maxNatProg]
    repeat rw [clientResult_maxNatProg]
    repeat rw [clientState_subSatProg]
    repeat rw [clientResult_subSatProg]
    have hp2 : Log2CapPre w (dstMetaBase, (max N 4 - 1, max N 4 - 1)) s :=
      ⟨hdst_lt, hmaxN4_fit.of_le (Nat.sub_le _ _),
        hw_fit.of_le (by have := Nat.min_le_right (max N 4 - 1) (Nat.log 2 (max N 4 - 1)); omega)⟩)
  all_goals try exact hp2
  all_goals (
    obtain ⟨_, _, _, hst2, hres2⟩ := log2CapProg_spec hp2.1 hp2.2.1 hp2.2.2
    rw [Nat.min_eq_right (Nat.log_le_self 2 _)] at hres2
    repeat rw [hst2]
    repeat rw [hres2]
    repeat rw [hclog1_eq]
    have hp3 : Log2CapPre w (dstMetaBase, (Nat.clog 2 (max N 4) - 1, Nat.clog 2 (max N 4) - 1)) s :=
      ⟨hdst_lt, hw_fit.of_le (by omega),
        hw_fit.of_le (by
          have := Nat.min_le_right (Nat.clog 2 (max N 4) - 1)
            (Nat.log 2 (Nat.clog 2 (max N 4) - 1)); omega)⟩)
  all_goals try exact hp3
  all_goals (
    obtain ⟨_, _, _, _, hres3⟩ := log2CapProg_spec hp3.1 hp3.2.1 hp3.2.2
    rw [Nat.min_eq_right (Nat.log_le_self 2 _)] at hres3
    repeat rw [hres3]
    repeat rw [hllf_eq]
    first
    | exact hw_fit.of_le (by omega)
    | exact h3llf.of_le (by omega))

/-! ## Bucket/Slab Scales and `GlobalMeta` Bases (`computeCompScalesProg`, `computeGmBasesProg`) -/

private def minEffCapProg : ℕ × ℕ → Memory.Prog ℕ
  | (N, numMicro) => if (N >>> 2) < numMicro then pure N else pure (numMicro <<< 2)

@[simp] private theorem clientResult_minEffCapProg (N : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (minEffCapProg (N, numMicroPerBucket N)) =
      min N (effBucketCap N) := by
  dsimp only [minEffCapProg]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change (Memory.spec 0).clientResult s
    (if N / 4 < numMicroPerBucket N then pure N else pure (numMicroPerBucket N * 4)) =
    min N (4 * numMicroPerBucket N)
  rw [Nat.mul_comm (numMicroPerBucket N) 4]
  split_ifs with hlt <;> simp only [prog_clientResult_pure]
  · exact (Nat.min_eq_left (by omega)).symm
  · exact (Nat.min_eq_right (by omega)).symm

private theorem clientState_minEffCapProg (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (minEffCapProg p) = s := by
  rcases p with ⟨N, m⟩; dsimp only [minEffCapProg]; split_ifs <;> rfl

@[simp] private theorem runClient_state_minEffCapProg (p : ℕ × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (minEffCapProg p))) = s :=
  clientState_minEffCapProg p s

@[simp] private theorem memoryCost_minEffCapProg (p : ℕ × ℕ) (s : Memory.State) :
    memoryCost (minEffCapProg p) s = 0 := by
  rcases p with ⟨N, m⟩; dsimp only [minEffCapProg]; split_ifs <;> rfl

private theorem validHistory_minEffCapProg {w : ℕ} (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (minEffCapProg p)) := by
  rcases p with ⟨N, m⟩; dsimp only [minEffCapProg]; split_ifs <;> trivial

private def MinEffCapPre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (N, _), _ => Fits w 2 ∧ Fits w N

private theorem realizesBounded_minEffCap :
    RealizesBounded .exact minEffCapProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      MinEffCapPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨N, numMicro⟩
    obtain ⟨h2, hN_fit⟩ := h
    try dsimp only at *)
  all_goals try exact h2
  rw [Nat.shiftRight_eq_div_pow] at hc
  rw [Nat.shiftLeft_eq]
  exact hN_fit.of_le (by change ¬ N / 4 < numMicro at hc; omega)

private def dirSlabsProg : ℕ × ℕ → Memory.Prog ℕ
  | (bBits, llf) => do
    let z0 ← pure 0
    if bBits = z0 then pure 0 else pure ((1 <<< llf) <<< 2)

@[simp] private theorem clientResult_dirSlabsProg (N : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (dirSlabsProg (bucketBits N, Dynamic.logLogFactor N)) =
      dirSlabsPerBucket N := by
  dsimp only [dirSlabsProg, dirSlabsPerBucket, slabScale]
  simp only [pure_bind]
  split_ifs with hb0 <;> simp only [prog_clientResult_pure, Nat.shiftLeft_eq, one_mul]
  ring

private theorem clientState_dirSlabsProg (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (dirSlabsProg p) = s := by
  rcases p with ⟨b, l⟩; dsimp only [dirSlabsProg]; simp only [pure_bind]; split_ifs <;> rfl

@[simp] private theorem runClient_state_dirSlabsProg (p : ℕ × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (dirSlabsProg p))) = s :=
  clientState_dirSlabsProg p s

@[simp] private theorem memoryCost_dirSlabsProg (p : ℕ × ℕ) (s : Memory.State) :
    memoryCost (dirSlabsProg p) s = 0 := by
  rcases p with ⟨b, l⟩; dsimp only [dirSlabsProg]; simp only [pure_bind]; split_ifs <;> rfl

private theorem validHistory_dirSlabsProg {w : ℕ} (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dirSlabsProg p)) := by
  rcases p with ⟨b, l⟩; dsimp only [dirSlabsProg]; simp only [pure_bind]; split_ifs <;> trivial

private def DirSlabsPre (w : ℕ) : ℕ × ℕ → Memory.State → Prop
  | (bBits, llf), _ => Fits w 2 ∧ (bBits ≠ 0 → Fits w (2 ^ llf * 4))

private theorem realizesBounded_dirSlabs :
    RealizesBounded .exact dirSlabsProg
      (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      DirSlabsPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨bBits, llf⟩
    obtain ⟨h2, hfit⟩ := h
    dsimp only at *)
  all_goals try exact h2.of_le (by decide)
  have h4 := hfit hc
  simp only [Nat.shiftLeft_eq, one_mul]
  exact h4.of_le (by omega)

/-- Read-only helper computing scales for `mkCompParams`. -/
def computeCompScalesProg :
    (ℕ × ℕ) × (ℕ × ℕ) → Memory.Prog ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
  | ((dstMetaBase, N), (logN, llf)) => do
    let threeLlf := llf * 3
    let bBits ← subSatProg (logN, threeLlf)
    let mBits ← minNatProg (logN, threeLlf)
    let numMicro := 1 <<< mBits
    let minCap ← minEffCapProg (N, numMicro)
    let logMinCap ← log2CapProg (dstMetaBase, (minCap, minCap))
    let lmBits := logMinCap + 1
    let sBits ← ifEqZeroProg (bBits, (0, llf + llf))
    let sSize := 1 <<< sBits
    let dirSlabs ← dirSlabsProg (bBits, llf)
    let tailCap ← ifEqZeroProg (bBits, (0, sSize + sSize))
    pure ((bBits, lmBits), ((numMicro, minCap), (sSize, (dirSlabs, tailCap))))

/-- Precondition for `computeCompScalesProg`. -/
@[expose] def ComputeCompScalesPre (w : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((dstMetaBase, N), (logN, llf)), s =>
    ∃ U,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      logN = Nat.log 2 N ∧ llf = Dynamic.logLogFactor N ∧
      dstMetaBase < s.frontier ∧ Fits w 225

/-- Pure arithmetic invariants for `computeCompScalesProg` and `writeCompSubDProg`. -/
theorem computeCompScales_arith {w U N : ℕ}
    (_hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (h225 : Fits w 225) :
    1 ≤ min N (effBucketCap N) ∧
    Nat.log 2 (min N (effBucketCap N)) + 1 = effBucketPosBits N ∧
    effBucketPosBits N ≤ w ∧
    (bucketBits N ≠ 0 → Fits w (2 ^ Dynamic.logLogFactor N * 4)) ∧
    Fits w (2 * slabSize N) := by
  have hN_fit : Fits w N := hU.of_le hNU
  have hminCap_pos : 1 ≤ min N (effBucketCap N) :=
    le_min hN (by
      unfold effBucketCap
      have : 0 < numMicroPerBucket N := by unfold numMicroPerBucket; positivity
      omega)
  have hlmBits_eq : Nat.log 2 (min N (effBucketCap N)) + 1 = effBucketPosBits N :=
    (clog2_succ_eq_log2_add_one hminCap_pos).symm
  have hlmBits_le : effBucketPosBits N ≤ w := effBucketPosBits_le_of_lt_pow hNU hU
  have hds : bucketBits N ≠ 0 → Fits w (2 ^ Dynamic.logLogFactor N * 4) := fun hb0 => by
    have hllf_lt : Dynamic.logLogFactor N + 2 ≤ Nat.log 2 N := by
      have := Dynamic.one_le_logLogFactor N; unfold bucketBits at hb0; omega
    have hpow_llf4 : 2 ^ Dynamic.logLogFactor N * 4 ≤ N := by
      calc 2 ^ Dynamic.logLogFactor N * 4
          = 2 ^ (Dynamic.logLogFactor N + 2) := by rw [pow_add]; ring
        _ ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right two_pos hllf_lt
        _ ≤ N := Nat.pow_log_le_self 2 (by omega)
    exact hN_fit.of_le hpow_llf4
  have h2s : Fits w (2 * slabSize N) := by
    by_cases hb0 : bucketBits N = 0
    · simp only [slabSize, slabBits, hb0, ↓reduceIte, pow_zero]
      exact h225.of_le (by decide)
    · have h2llf_lt : 2 * Dynamic.logLogFactor N + 1 ≤ Nat.log 2 N := by
        have := Dynamic.one_le_logLogFactor N; unfold bucketBits at hb0; omega
      have h2s_le : 2 * slabSize N ≤ N := by
        simp only [slabSize, slabBits, hb0, ↓reduceIte]
        calc 2 * 2 ^ (2 * Dynamic.logLogFactor N)
            = 2 ^ (2 * Dynamic.logLogFactor N + 1) := by rw [pow_succ']
          _ ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right two_pos h2llf_lt
          _ ≤ N := Nat.pow_log_le_self 2 (by omega)
      exact hN_fit.of_le h2s_le
  exact ⟨hminCap_pos, hlmBits_eq, hlmBits_le, hds, h2s⟩

/-- Functional specification and `≤ N` cost bound for `computeCompScalesProg`. -/
theorem computeCompScalesProg_exec {w U dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hdst_lt : dstMetaBase < s.frontier) (h225 : Fits w 225) :
    let d := ((dstMetaBase, N), (Nat.log 2 N, Dynamic.logLogFactor N))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeCompScalesProg d)) ∧
    (Memory.spec 0).clientState s (computeCompScalesProg d) = s ∧
    (Memory.spec 0).clientResult s (computeCompScalesProg d) =
      ((bucketBits N, effBucketPosBits N),
        ((numMicroPerBucket N, min N (effBucketCap N)),
          (slabSize N, (dirSlabsPerBucket N, tailCapPerBucket N)))) ∧
    memoryCost (computeCompScalesProg d) s ≤ N := by
  intro d
  have hw_fit : Fits w w := Nat.lt_two_pow_self
  have hN_fit : Fits w N := hU.of_le hNU
  obtain ⟨_, hlmBits_eq, hlmBits_le, _, _⟩ := computeCompScales_arith hw hN hNU hU h225
  set minCap := min N (effBucketCap N)
  obtain ⟨_, hv_mc, hc_mc, hst_mc, hres_mc⟩ :=
    log2CapProg_spec (K := minCap) (x₀ := minCap) hdst_lt (hN_fit.of_le (min_le_left _ _))
      (hw_fit.of_le (by have := Nat.min_le_right minCap (Nat.log 2 minCap); omega))
  rw [Nat.min_eq_right (Nat.log_le_self 2 minCap)] at hres_mc
  have h3llf_eq : Dynamic.logLogFactor N * 3 = 3 * Dynamic.logLogFactor N := by ring
  have hmBits_def : min (Nat.log 2 N) (3 * Dynamic.logLogFactor N) = microBits N := rfl
  have hnumMicro_eq : (1 <<< microBits N) = numMicroPerBucket N := by
    rw [Nat.shiftLeft_eq, one_mul]; rfl
  have hbBits_def : Nat.log 2 N - 3 * Dynamic.logLogFactor N = bucketBits N := rfl
  have hsBits_eq : (if bucketBits N = 0 then 0
      else Dynamic.logLogFactor N + Dynamic.logLogFactor N) = slabBits N := by
    dsimp only [slabBits]; rw [two_mul]
  have hsSize_eq : (1 <<< slabBits N) = slabSize N := by
    rw [Nat.shiftLeft_eq, one_mul]; rfl
  have htwoSSize_eq : slabSize N + slabSize N = 2 * slabSize N := by ring
  have hmin_le : minCap ≤ N := min_le_left _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [d, computeCompScalesProg]
    rw [h3llf_eq, validHistory_bind', clientState_subSatProg, clientResult_subSatProg, hbBits_def]
    refine ⟨validHistory_subSatProg _ _, ?_⟩
    rw [validHistory_bind', clientState_minNatProg, clientResult_minNatProg, hmBits_def]
    refine ⟨validHistory_minNatProg _ _, ?_⟩
    rw [hnumMicro_eq, validHistory_bind', clientState_minEffCapProg, clientResult_minEffCapProg]
    refine ⟨validHistory_minEffCapProg _ _, ?_⟩
    rw [validHistory_bind', hst_mc, hres_mc]; refine ⟨hv_mc, ?_⟩
    rw [hlmBits_eq, validHistory_bind', clientState_ifEqZeroProg,
      clientResult_ifEqZeroProg, hsBits_eq]
    refine ⟨validHistory_ifEqZeroProg _ _, ?_⟩
    rw [hsSize_eq, htwoSSize_eq, validHistory_bind', clientState_dirSlabsProg,
      clientResult_dirSlabsProg]
    refine ⟨validHistory_dirSlabsProg _ _, ?_⟩
    rw [validHistory_bind', clientState_ifEqZeroProg]
    exact ⟨validHistory_ifEqZeroProg _ _, trivial⟩
  · dsimp only [d, computeCompScalesProg]
    rw [h3llf_eq, StateTransitionSpec.clientState_bind, clientState_subSatProg,
      clientResult_subSatProg, hbBits_def,
      StateTransitionSpec.clientState_bind, clientState_minNatProg, clientResult_minNatProg,
      hmBits_def, hnumMicro_eq, StateTransitionSpec.clientState_bind, clientState_minEffCapProg,
      clientResult_minEffCapProg,
      StateTransitionSpec.clientState_bind, hst_mc, hres_mc,
      StateTransitionSpec.clientState_bind, clientState_ifEqZeroProg,
      clientResult_ifEqZeroProg, hsBits_eq,
      StateTransitionSpec.clientState_bind, clientState_dirSlabsProg,
      StateTransitionSpec.clientState_bind, clientState_ifEqZeroProg,
      StateTransitionSpec.clientState_pure]
  · dsimp only [d, computeCompScalesProg]
    rw [h3llf_eq, prog_clientResult_bind, clientState_subSatProg, clientResult_subSatProg,
      hbBits_def, prog_clientResult_bind, clientState_minNatProg, clientResult_minNatProg,
      hmBits_def, hnumMicro_eq, prog_clientResult_bind, clientState_minEffCapProg,
      clientResult_minEffCapProg, prog_clientResult_bind, hst_mc, hres_mc,
      hlmBits_eq, prog_clientResult_bind, clientState_ifEqZeroProg, clientResult_ifEqZeroProg,
      hsBits_eq, hsSize_eq, htwoSSize_eq, prog_clientResult_bind, clientState_dirSlabsProg,
      clientResult_dirSlabsProg, prog_clientResult_bind, clientState_ifEqZeroProg,
      clientResult_ifEqZeroProg, prog_clientResult_pure]
    rfl
  · dsimp only [d, computeCompScalesProg]
    rw [h3llf_eq, Realization.memoryCost_bind', memoryCost_subSatProg, clientState_subSatProg,
      clientResult_subSatProg, hbBits_def,
      Realization.memoryCost_bind', memoryCost_minNatProg, clientState_minNatProg,
      clientResult_minNatProg, hmBits_def,
      hnumMicro_eq, Realization.memoryCost_bind', memoryCost_minEffCapProg,
      clientState_minEffCapProg, clientResult_minEffCapProg,
      Realization.memoryCost_bind', hst_mc, hres_mc,
      Realization.memoryCost_bind', memoryCost_ifEqZeroProg, clientState_ifEqZeroProg,
      clientResult_ifEqZeroProg, hsBits_eq,
      Realization.memoryCost_bind', memoryCost_dirSlabsProg, clientState_dirSlabsProg,
      Realization.memoryCost_bind', memoryCost_ifEqZeroProg, clientState_ifEqZeroProg,
      memoryCost_pure]
    dsimp only [minCap] at hc_mc hmin_le ⊢
    omega

/-- `computeCompScalesProg` compiles via `RealizesBounded .exact`. -/
theorem realizesBounded_computeCompScales :
    RealizesBounded .exact computeCompScalesProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      ComputeCompScalesPre (fun _ _ => 0) := by
  have hsub := realizesBounded_subSat
  have hmin := realizesBounded_minNat
  have hmec := realizesBounded_minEffCap
  have hifz := realizesBounded_ifEqZero
  have hds := realizesBounded_dirSlabs
  have hlg := realizesBounded_log2Cap
  realize
  all_goals (
    rcases d with ⟨⟨dstMetaBase, N⟩, ⟨logN, llf⟩⟩
    obtain ⟨U, hw, hN, hNU, hU, rfl, rfl, hdst_lt, h225⟩ := h
    try dsimp only at *
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    have hN_fit : Fits w N := hU.of_le hNU
    have hmax_fit : Fits w (max N 1) := max_n_one_lt_two_pow_w hw hNU hU
    obtain ⟨hlogN_lt, _, _, _, _, _, h3llf⟩ := computeLogScales_arith hN hNU hU h225
    obtain ⟨_, hlmBits_eq, hlmBits_le, hds_fit, h2s_fit⟩ :=
      computeCompScales_arith hw hN hNU hU h225
    have h3llf_eq : Dynamic.logLogFactor N * 3 = 3 * Dynamic.logLogFactor N := by ring
    have hbBits_def : Nat.log 2 N - 3 * Dynamic.logLogFactor N = bucketBits N := rfl
    have hmBits_def : min (Nat.log 2 N) (3 * Dynamic.logLogFactor N) = microBits N := rfl
    have hnumMicro_eq : (1 <<< microBits N) = numMicroPerBucket N := by
      rw [Nat.shiftLeft_eq, one_mul]; rfl
    repeat rw [h3llf_eq]
    repeat rw [clientState_subSatProg]
    repeat rw [clientResult_subSatProg]
    repeat rw [hbBits_def]
    repeat rw [clientState_minNatProg]
    repeat rw [clientResult_minNatProg]
    repeat rw [hmBits_def]
    repeat rw [hnumMicro_eq]
    repeat rw [clientState_minEffCapProg]
    repeat rw [clientResult_minEffCapProg]
    have hmc_pre : Log2CapPre w (dstMetaBase, (min N (effBucketCap N), min N (effBucketCap N))) s :=
      ⟨hdst_lt, hN_fit.of_le (min_le_left _ _),
        hw_fit.of_le (by
          have := Nat.min_le_right (min N (effBucketCap N)) (Nat.log 2 (min N (effBucketCap N)))
          omega)⟩)
  all_goals try exact ⟨h225.of_le (by decide), hN_fit⟩
  all_goals try exact h225.of_le (by decide)
  all_goals try exact hmc_pre
  all_goals (
    obtain ⟨_, _, _, hst_mc, hres_mc⟩ := log2CapProg_spec hmc_pre.1 hmc_pre.2.1 hmc_pre.2.2
    rw [Nat.min_eq_right (Nat.log_le_self 2 _)] at hres_mc
    repeat rw [hst_mc]
    repeat rw [hres_mc]
    have hsBits_eq : (if bucketBits N = 0 then 0
        else Dynamic.logLogFactor N + Dynamic.logLogFactor N) = slabBits N := by
      dsimp only [slabBits]; rw [two_mul]
    have hsSize_eq : (1 <<< slabBits N) = slabSize N := by rw [Nat.shiftLeft_eq, one_mul]; rfl
    repeat rw [hlmBits_eq]
    repeat rw [clientState_ifEqZeroProg]
    repeat rw [clientResult_ifEqZeroProg]
    repeat rw [hsBits_eq]
    repeat rw [hsSize_eq])
  all_goals try exact ⟨h225.of_le (by decide), hds_fit⟩
  all_goals (
    have hmBits_le : microBits N ≤ Nat.log 2 N := Nat.min_le_left _ _
    first
    | exact hw_fit.of_le (by omega)
    | exact h3llf.of_le (by omega)
    | (unfold numMicroPerBucket
       exact hmax_fit.of_le ((Nat.pow_le_pow_right two_pos hmBits_le).trans
         (by rw [← totalMicroBits_eq_log]; exact totalMicroBuckets_le N)))
    | exact h2s_fit.of_le (by omega))

/-- Pure helper computing `(maxTail, ((gmDirBase, gmTailPtr), (gmTailOwn, gmSlabMeta)))`. -/
def computeGmBasesProg : ℕ × (ℕ × ℕ) → Memory.Prog (ℕ × ((ℕ × ℕ) × (ℕ × ℕ)))
  | (bBits, (dirSlabs, tailCap)) => do
    let numBkts := 1 <<< bBits
    let maxTail := numBkts * tailCap
    let gmDirBase := 4 + numBkts * 3
    let gmTailPtr := gmDirBase + numBkts * dirSlabs
    pure (maxTail, ((gmDirBase, gmTailPtr), (gmTailPtr + maxTail, gmTailPtr + maxTail * 2)))

/-- Precondition for `computeGmBasesProg`. -/
@[expose] def ComputeGmBasesPre (w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (bBits, (dirSlabs, tailCap)), _s =>
    ∃ U dstMetaBase N,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧
      bBits = bucketBits N ∧ dirSlabs = dirSlabsPerBucket N ∧ tailCap = tailCapPerBucket N ∧
      Fits w (dstMetaBase + offCompItems U w N)

/-- Functional specification and zero-cost certificate for `computeGmBasesProg`. -/
theorem computeGmBasesProg_spec {w U dstMetaBase N : ℕ} {s : Memory.State}
    (hw : 0 < w) (_hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U)
    (hfit_dst : Fits w (dstMetaBase + offCompItems U w N)) :
    let d := (bucketBits N, (dirSlabsPerBucket N, tailCapPerBucket N))
    Fits w (globalMetaLen N) ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (computeGmBasesProg d)) ∧
    (Memory.spec 0).clientState s (computeGmBasesProg d) = s ∧
    (Memory.spec 0).clientResult s (computeGmBasesProg d) =
      (maxTailItems N,
        ((gmSlabDirBase N, gmTailPtrBase N), (gmTailOwnerBase N, gmSlabMetaBase N))) ∧
    memoryCost (computeGmBasesProg d) s = 0 := by
  intro d
  have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
  have hgmLen_fit : Fits w (globalMetaLen N) := by
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
    · simp only [globalMetaLen, globalMetaVarLen, hb0, ↓reduceIte]
      exact h225.of_le (by decide)
    · exact fits_of_le_globalMetaLen_comp hb_pos hw hNU hU le_rfl
  refine ⟨hgmLen_fit, trivial, rfl, ?_, rfl⟩
  dsimp only [d, computeGmBasesProg]
  rw [prog_clientResult_pure, Nat.shiftLeft_eq, one_mul]
  change (numBuckets N * tailCapPerBucket N,
    ((4 + numBuckets N * 3, 4 + numBuckets N * 3 + numBuckets N * dirSlabsPerBucket N),
      (4 + numBuckets N * 3 + numBuckets N * dirSlabsPerBucket N +
        numBuckets N * tailCapPerBucket N,
       4 + numBuckets N * 3 + numBuckets N * dirSlabsPerBucket N +
        (numBuckets N * tailCapPerBucket N) * 2))) = _
  dsimp only [gmSlabMetaBase, gmTailOwnerBase, gmTailPtrBase, gmSlabDirBase, maxTailItems]
  ext <;> dsimp only <;> ring

/-- `computeGmBasesProg` compiles via `RealizesBounded .exact`. -/
theorem realizesBounded_computeGmBases :
    RealizesBounded .exact computeGmBasesProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ((ℕ × ℕ) × (ℕ × ℕ))))
      ComputeGmBasesPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨bBits, ⟨dirSlabs, tailCap⟩⟩
    obtain ⟨U, dstMetaBase, N, hw, hN, hNU, hU, rfl, rfl, rfl, hfit_dst⟩ := h
    try dsimp only at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit_dst le_rfl
    have hw_fit : Fits w w := Nat.lt_two_pow_self
    have hmax_fit : Fits w (max N 1) := max_n_one_lt_two_pow_w hw hNU hU
    obtain ⟨hgmLen_fit, _, _, _, _⟩ := computeGmBasesProg_spec (s := s) hw hN hNU hU hfit_dst
    have hlogN_lt : Nat.log 2 N < w := (computeLogScales_arith hN hNU hU h225).1
    have hbBits_le : bucketBits N ≤ Nat.log 2 N := Nat.sub_le _ _
    try rw [Nat.shiftLeft_eq, one_mul]
    first
    | exact h225.of_le (by decide)
    | exact hmax_fit.of_le ((Nat.pow_le_pow_right two_pos (bucketBits_le_totalMicroBits N)).trans
        (totalMicroBuckets_le N))
    | (by_cases hb0 : bucketBits N = 0
       · simp only [tailCapPerBucket, dirSlabsPerBucket, hb0, ↓reduceIte, pow_zero]
         exact h225.of_le (by omega)
       · have hgm_pos : gmSlabMetaBase N + maxFullSlabs N * 4 = globalMetaLen N := by
           have := globalMetaLen_cond_eq N; simp only [hb0, ↓reduceIte] at this; exact this
         unfold gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase maxTailItems
           numBuckets at hgm_pos
         exact hgmLen_fit.of_le (by omega)))

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ParamsComputeAux
