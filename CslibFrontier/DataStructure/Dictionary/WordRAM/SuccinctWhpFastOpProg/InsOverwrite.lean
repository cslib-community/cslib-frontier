/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
import CslibFrontier.Tactic.Realize

/-!
# Fast Insertion Overwrite Branch (`fastInsertOverwriteGenProg`)

Handles key hits during `fastInsert`: overwrites `valArr[physSlot b loc]` and runs
`overmarsStepGenProg` while returning `1`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastInsertOverwriteGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.keyQuotient_lt_pow_quotBits`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fastInsertOverwriteGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastInsertOverwriteGenProg_spec`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

theorem keyQuotient_lt_pow_quotBits {U n_max : ℕ} (u : Fin U) :
    keyQuotient (bWhp n_max) u.val < 2 ^ quotBitsWhp U n_max := by
  have hu_pow : u.val < 2 ^ keyBits U := u.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two U)
  unfold keyQuotient quotBitsWhp
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
  exact hu_pow.trans_le (Nat.pow_le_pow_right two_pos (by omega))

private theorem overmarsBucketStepBounds_update_valArr {U n_max b : ℕ}
    {fs : FastState} (vArr' : ℕ → ℕ)
    (hbnds : OvermarsBucketStepBounds U n_max b fs) :
    OvermarsBucketStepBounds U n_max b { fs with valArr := vArr' } := by
  rcases hbnds with ⟨hb, hce, hlr, hor, hcnt, hq, hbp, hact⟩
  refine ⟨hb, hce, hlr, hor, hcnt, hq, hbp, ?_⟩
  unfold overmarsAfterActivate at hact ⊢
  by_cases hc : fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b
  · dsimp only; rw [ite_eq_left hc] at hact ⊢; exact hact
  · dsimp only; rw [ite_eq_right hc] at hact ⊢; exact hact

/-- Overwrite value `v_val` at physical slot `(b, loc)` (`d = (((cp, base), (b, loc)), v_val)`). -/
@[irreducible] private def fastInsertWriteOvGenProg :
    ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((cp, base), (b, loc)), v_val) => do
    let p ← physSlotGenProg (((cp, base), b), loc)
    writeValGenProg (((cp, base), p), v_val)

private theorem realizes_fastInsertWriteOvGen :
    Realizes .exact fastInsertWriteOvGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), (b, loc)), _) s =>
        PhysSlotPre w (((cp, base), b), loc) s)
      (fun _ _ => 0) := by
  unfold fastInsertWriteOvGenProg
  have hps := realizes_physSlotGen
  have hwv := realizes_writeValGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, ⟨b, loc⟩⟩, v_val⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hloc, hbp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    obtain ⟨hps_st, hps_res, hps_lt, _, _⟩ := physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
    simp only [hps_st, hps_res, wp_large_nMax hth] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hloc, hbp⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hps_lt
  )

private theorem fastInsertWriteOvGenProg_fastStep {c U V w n_max base b loc v_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max)
    (hbp : capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max)
    (hv_lt : v_val < 2 ^ valBits V)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := fastInsertWriteOvGenProg (((mkWhpCoreParams c U V w n_max, base), (b, loc)), v_val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 6 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with valArr := Function.update fs.valArr (fs.physSlot n_max b loc) v_val } s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hps_st, hps_res, hps_lt, hps_mc, hps_vp⟩ :=
    physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
  obtain ⟨hwv_mc, hwv_vp, hwv_step⟩ :=
    writeValGenProg_fastStep henv hps_lt hv_lt hseed hrep (v_val := v_val) (s := s)
  dsimp only
  unfold fastInsertWriteOvGenProg; dsimp only
  have hs'_eq : (Memory.spec 0).clientState s
      (physSlotGenProg (((cp, base), b), loc) >>= fun p =>
        writeValGenProg (((cp, base), p), v_val)) =
      (Memory.spec 0).clientState s
        (writeValGenProg (((cp, base), fs.physSlot n_max b loc), v_val)) := by
    rw [clientState_bind, hps_st, hps_res]
  rw [hs'_eq]
  refine ⟨?_, ?_, hwv_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hps_st, hps_res]; dsimp only [cp] at hps_mc hwv_mc ⊢; omega
  · refine validProg_bind hps_vp ?_; rw [hps_st, hps_res]; exact hwv_vp

/-- Hit branch of `fastInsert`: overwrite `valArr[physSlot b loc] := v_val` and run `overmarsStep`,
returning `1` (`d = (((wp, base), (b, loc)), v_val)`). -/
@[irreducible] def fastInsertOverwriteGenProg :
    ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | (((wp, base), (b, loc)), v_val) => do
    fastInsertWriteOvGenProg (((wp.1, base), (b, loc)), v_val)
    overmarsStepGenProg ((wp, base), b)
    pure 1

theorem realizes_fastInsertOverwriteGen :
    Realizes .exact fastInsertOverwriteGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((wp, base), (b, loc)), v_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          b < numBucketsWhp n_max ∧
          loc < fs.bktCount b ∧
          v_val < V)
      (fun _ _ => 0) := by
  unfold fastInsertOverwriteGenProg
  have hwv := realizes_fastInsertWriteOvGen
  have hom := realizes_overmarsStepGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, ⟨b, loc⟩⟩, v_val⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hb, hloc_b, hv_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hloc : loc < totalLocalCoordsWhp n_max := hloc_b.trans_le (hv.bktCount_le b hb)
    have hbp : capFrontWhp n_max ≤ loc →
        fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max :=
      fun hcf => (hv.backPtr_valid b hb _ (by omega)).1
    have hv_pow := val_lt_two_pow_valBits hv_v
    obtain ⟨_, _, hwv_step⟩ :=
      fastInsertWriteOvGenProg_fastStep henv hb hloc hbp hv_pow hseed hrep (s := s)
    have hbnds0 : OvermarsBucketStepBounds U n_max b fs :=
      OvermarsBucketStepBounds.of_core_and_pre hv.toCore hb
        (OvermarsBucketInv.toPre (hv.overmars_valid b hb))
    have hbnds_ov := overmarsBucketStepBounds_update_valArr
      (Function.update fs.valArr (fs.physSlot n_max b loc) v_val) hbnds0
    rw [hcp_eq] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hloc, hbp⟩
    | exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hwv_step.2.1, hwv_step.2.2.1, hbnds_ov⟩
  )

theorem fastInsertOverwriteGenProg_spec {c U V w n_max base b loc v_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max) (hloc_b : loc < fs.bktCount b) (hv_v : v_val < V) :
    let prog := fastInsertOverwriteGenProg (((mkWhpParams c U V w n_max, base), (b, loc)), v_val)
    let s' := (Memory.spec 0).clientState s prog
    let fs_ov : FastState :=
      { fs with valArr := Function.update fs.valArr (fs.physSlot n_max b loc) v_val }
    (Memory.spec 0).clientResult s prog = 1 ∧
    memoryCost prog s ≤ 32 * hashEvalCostWhp c + 39332 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (overmarsStep c U n_max θ b fs_ov) s s' := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  have hloc : loc < totalLocalCoordsWhp n_max := hloc_b.trans_le (hv.bktCount_le b hb)
  have hbp : capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max :=
    fun hcf => (hv.backPtr_valid b hb _ (by omega)).1
  have hv_pow := val_lt_two_pow_valBits hv_v
  obtain ⟨hwv_mc, hwv_vp, hwv_step⟩ :=
    fastInsertWriteOvGenProg_fastStep henv hb hloc hbp hv_pow hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s
    (fastInsertWriteOvGenProg (((cp, base), (b, loc)), v_val))
  set fs_ov : FastState :=
    { fs with valArr := Function.update fs.valArr (fs.physSlot n_max b loc) v_val }
  have hbnds_ov : OvermarsBucketStepBounds U n_max b fs_ov :=
    overmarsBucketStepBounds_update_valArr _
      (OvermarsBucketStepBounds.of_core_and_pre hv.toCore hb
        (OvermarsBucketInv.toPre (hv.overmars_valid b hb)))
  obtain ⟨hom_mc, hom_vp, hom_step⟩ :=
    overmarsStepGenProg_fastStep (fs := fs_ov) henv hbnds_ov hwv_step.2.1 hwv_step.2.2.1 (s := s1)
  dsimp only
  unfold fastInsertOverwriteGenProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  have hs'_eq : (Memory.spec 0).clientState s
      (fastInsertWriteOvGenProg (((cp, base), (b, loc)), v_val) >>= fun _ =>
        overmarsStepGenProg ((mkWhpParams c U V w n_max, base), b) >>= fun _ => pure 1) =
      (Memory.spec 0).clientState s1
        (overmarsStepGenProg ((mkWhpParams c U V w n_max, base), b)) := by
    rw [clientState_bind, clientState_bind, clientState_pure_whp]
  rw [hs'_eq]
  refine ⟨?_, ?_, ?_, hwv_step.trans hom_step⟩
  · rw [clientResult_bind, clientResult_bind, clientResult_pure_whp]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
    dsimp only [s1, cp] at hwv_mc hom_mc ⊢; omega
  · exact validProg_bind hwv_vp (validProg_bind hom_vp (validProg_pure _))

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
