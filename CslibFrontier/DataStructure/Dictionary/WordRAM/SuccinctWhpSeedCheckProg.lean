/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModel
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpPermHealProg
import CslibFrontier.Tactic.Realize

/-!
# Certified `Memory.Prog` Subroutines for `emptyFastState` Initialization and `GoodSeedOnState`

This module implements two foundational large-regime `Memory.Prog` subroutines inside genuine
`whpSpace c U V w n_max` words (zero auxiliary scratch beyond `offBktMeta`):

1. **`initFastGenProg`**: initializes `FastMemRep base c U V w n_max (emptyFastState n_max)` in
   deterministic `4 * numBucketsWhp n_max + 4 * poolSizeWhp n_max + 5` (`O(n_max)`) memory charges
   once `[base, base + 32)` and `[base + offQuotWhp c w n_max, base + largeSpaceWhp c U V w n_max)`
   are zeroed and `SeedWhpMemRep` holds on `[base + 32, base + offQuotWhp c w n_max)`.
2. **`checkGoodSeedOnStateGenProg`**: evaluates `checkGoodSeedOnState c U n_max θ csr` in place on
   any `CsrMemRep` without external scratch arrays, storing per-bucket collision-free candidate
   salts `(checkGoodSeedOnState c U n_max θ csr).2 b` into the odd `offBktMeta` entries `16 * b + 1`
   (`b < numBucketsWhp n_max`) while preserving both `SeedWhpMemRep` and `CsrMemRep`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.initFastCostWhp`, `initFastGenProg`:
  certified `Memory.Prog` initializer for `emptyFastState n_max`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.checkGoodSeedOnStateGenProg`:
  certified scratch-free `Memory.Prog` decision and salt-discovery procedure for `GoodSeedOnState`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_initFastGen`,
  `initFastGenProg_spec`: `Realizes .exact` certificate and exact `FastMemRep` initialization spec.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_checkGoodSeedOnStateGen`,
  `checkGoodSeedOnStateGenProg_spec`: `Realizes .exact` certificate and exact `checkGoodSeedOnState`
  refinement preserving `SeedWhpMemRep` and `CsrMemRep`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ## Section 1: Primitive Helpers and Zeroed Packed-Segment Lemmas -/

attribute [local simp] clientResult_pure_whp clientState_pure_whp

private theorem offQuot_le_offBktMeta (c U V w n_max : ℕ) :
    offQuotWhp c w n_max ≤ offBktMeta c U V w n_max := by
  unfold offBktMeta offLocState offPermAct offValWhp
  omega

/-! ## Section 2: `initFastGenProg` (`emptyFastState n_max` Initializer) -/

/-- Exact `memoryCost` of `initFastGenProg` (`O(n_max)` deterministic operations). -/
@[expose] def initFastCostWhp (n_max : ℕ) : ℕ :=
  4 * numBucketsWhp n_max + 4 * poolSizeWhp n_max + 5

/-- Compact 7-word runtime bundle for `initFastGenProg`:
`(((base, w), (M, poolSize)), ((gBits, offBm), offPs))`. -/
private abbrev InitFastRt : Type :=
  ((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × ℕ)

private def ifrBase (rt : InitFastRt) : ℕ := rt.1.1.1
private def ifrW (rt : InitFastRt) : ℕ := rt.1.1.2
private def ifrM (rt : InitFastRt) : ℕ := rt.1.2.1
private def ifrPoolSize (rt : InitFastRt) : ℕ := rt.1.2.2
private def ifrGBits (rt : InitFastRt) : ℕ := rt.2.1.1
private def ifrOffBm (rt : InitFastRt) : ℕ := rt.2.1.2
private def ifrOffPs (rt : InitFastRt) : ℕ := rt.2.2

/-- Construct `InitFastRt` for `(c, U, V, w, n_max, base)`. -/
private def mkInitFastRt (c U V w n_max base : ℕ) : InitFastRt :=
  (((base, w), (numBucketsWhp n_max, poolSizeWhp n_max)),
   ((globalPtrBits n_max, offBktMeta c U V w n_max), offPoolFreeStack c U V w n_max))

/-- Parameter-free `InitFastRt` envelope. -/
private def InitFastRtEnv (w : ℕ) (rt : InitFastRt) : Prop :=
  ∃ c U V w₀ n_max, WhpLargeEnv c U V w₀ n_max w (ifrBase rt) ∧
    rt = mkInitFastRt c U V w₀ n_max (ifrBase rt)

@[irreducible] private def mkInitFastRtGenProg : WhpCoreParams × ℕ → Memory.Prog InitFastRt
  | (cp, base_in) => do
    let base ← pure base_in
    let w ← pure (wpW cp)
    let M ← pure (wpM cp)
    let ps ← pure (wpPoolSize cp)
    let gBits ← pure (wpGlobalPtrBits cp)
    let offBm ← pure (wpOffBktMeta cp)
    let offPs ← pure (wpOffPoolFreeStack cp)
    pure (((base, w), (M, ps)), ((gBits, offBm), offPs))

private theorem realizes_mkInitFastRtGen :
    Realizes .exact mkInitFastRtGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := InitFastRt))
      (fun w d _ => WhpLargeEnvGen w d.1 d.2)
      (fun _ _ => 0) := by
  unfold mkInitFastRtGenProg
  realize

private theorem mkInitFastRtGenProg_spec {c U V w n_max base : ℕ}
    (hth : whpThreshold c ≤ n_max) (s : Memory.State) :
    let prog := mkInitFastRtGenProg (mkWhpCoreParams c U V w n_max, base)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = mkInitFastRt c U V w n_max base ∧
    memoryCost prog s = 0 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  dsimp only
  unfold mkInitFastRtGenProg
  simp only [wp_large_w hth, wp_large_M hth, wp_large_poolSize hth,
    wp_large_globalPtrBits hth, wp_large_offBktMeta hth, wp_large_offPoolFreeStack hth,
    pure_bind]
  exact ⟨rfl, rfl, rfl, validProg_pure _⟩

/-- Step writing `overmarsRole b := 1` at `16 * b + 4` in `offBktMeta` (`d = (rt, b)`). -/
@[irreducible] private def initOmRoleStepProg : InitFastRt × ℕ → Memory.Prog ℕ
  | (rt, b_in) => do
    let b ← pure b_in
    let one_v ← pure 1
    let idx ← pure (16 * b + 4)
    writePackedGenProg ((((ifrBase rt, ifrOffBm rt), (ifrGBits rt, ifrW rt)), idx), one_v)
    pure (b + one_v)

private theorem memoryCost_initOmRoleStep_pos (d : InitFastRt × ℕ) (s : Memory.State) :
    0 < memoryCost (initOmRoleStepProg d) s := by
  rcases d with ⟨rt, b⟩
  unfold initOmRoleStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 4 + 0
  omega

private def InitOmRoleStepPre (w : ℕ) (d : InitFastRt × ℕ) (_s : Memory.State) : Prop :=
  InitFastRtEnv w d.1 ∧ d.2 < ifrM d.1

private theorem realizes_initOmRoleStep :
    Realizes .exact initOmRoleStepProg
      (WordEncoding.encode (α := InitFastRt × ℕ))
      (WordEncoding.encode (α := ℕ))
      InitOmRoleStepPre
      (fun _ _ => 0) := by
  unfold initOmRoleStepProg
  realize [realizes_writePackedGen]
  all_goals (
    rcases d with ⟨rt, b⟩
    dsimp only [InitOmRoleStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hb_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize ifrBase rt = base at henv heq_rt
    subst heq_rt
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.1
    have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
    dsimp only [mkInitFastRt, ifrBase, ifrW, ifrM, ifrGBits, ifrOffBm] at hb_lt ⊢
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.packed_safe_of_le hgk (by omega : 16 * b + 4 < 16 * numBucketsWhp n_max) hseg
  )

@[irreducible] private def initOmRoleLoopProg : (InitFastRt × ℕ) × ℕ → Memory.Prog ℕ
  | ((rt, b₀), rem) => iterate initOmRoleStepProg rt rem b₀

private theorem realizes_initOmRoleLoop :
    Realizes .exact initOmRoleLoopProg
      (WordEncoding.encode (α := (InitFastRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((rt, b₀), rem) s =>
        iterationSafe initOmRoleStepProg InitOmRoleStepPre w rt rem b₀ s)
      (fun _ _ => 0) := by
  unfold initOmRoleLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := InitFastRt))
    (WordEncoding.encode (α := ℕ))
    realizes_initOmRoleStep
    memoryCost_initOmRoleStep_pos

private theorem initOmRoleLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkInitFastRt c U V w n_max base
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ numBucketsWhp n_max →
      iterationSafe initOmRoleStepProg InitOmRoleStepPre w rt rem b₀ s := by
  intro rt rem
  induction rem with
  | zero => intro _ _ _; exact trivial
  | succ rem ih =>
    intro b₀ s hle
    refine ⟨⟨⟨c, U, V, w, n_max, henv, rfl⟩, by dsimp [rt, mkInitFastRt, ifrM]; omega⟩, ?_⟩
    rw [clientState_width, clientResult_width]
    have hr : (Memory.spec 0).clientResult s (initOmRoleStepProg (rt, b₀)) = b₀ + 1 := by
      unfold initOmRoleStepProg; simp only [pure_bind, clientResult_bind, clientResult_pure_whp]
    rw [hr]
    exact ih (b₀ + 1) _ (by omega)

private theorem initOmRoleLoop_spec {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkInitFastRt c U V w n_max base
    let M := numBucketsWhp n_max
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ M →
      (∀ idx < 16 * M,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx =
          if idx % 16 = 4 ∧ idx / 16 < b₀ then 1 else 0) →
      let prog := initOmRoleLoopProg ((rt, b₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      memoryCost prog s = 4 * rem ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ idx < 16 * M,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
          if idx % 16 = 4 ∧ idx / 16 < b₀ + rem then 1 else 0) ∧
      (∀ a, (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
        s'.mem a = s.mem a) := by
  intro rt M rem
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.1
  have hbm_b : base + offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  have hbm_end : offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w = offFbStart c U V w n_max := rfl
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have h1_lt : 1 < 2 ^ globalPtrBits n_max :=
    Nat.one_lt_two_pow (globalPtrBits_pos_of_large hth).ne'
  induction rem with
  | zero =>
    intro b₀ s _ hbm
    unfold initOmRoleLoopProg iterate
    rw [Nat.add_zero, Nat.mul_zero]
    exact ⟨rfl, rfl, validProg_pure _, hbm, fun _ _ => rfl⟩
  | succ rem ih =>
    intro b₀ s hle hbm
    have hb_lt : b₀ < M := by omega
    have hidx_lt : 16 * b₀ + 4 < 16 * M := by omega
    set p1 := initOmRoleStepProg (rt, b₀)
    set m1 := writePacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
      (16 * b₀ + 4) 1
    have hs1 : (Memory.spec 0).clientState s p1 = { mem := m1, frontier := s.frontier } := by
      dsimp only [p1]; unfold initOmRoleStepProg
      simp only [pure_bind]
      rw [clientState_bind, clientState_writePackedGen, clientState_pure_whp]
      rfl
    have hr1 : (Memory.spec 0).clientResult s p1 = b₀ + 1 := by
      dsimp only [p1]; unfold initOmRoleStepProg
      simp only [pure_bind, clientResult_bind, clientResult_pure_whp]
    have hmc1 : memoryCost p1 s = 4 := by
      dsimp only [p1]; unfold initOmRoleStepProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_writePackedGen, memoryCost_pure]
    have hvp1 : ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold initOmRoleStepProg; simp only [pure_bind]
      exact validProg_bind (validProg_writePacked hw hgk hidx_lt hbm_b) (validProg_pure _)
    set s1 : Memory.State := { mem := m1, frontier := s.frontier }
    have hbm1 : ∀ idx < 16 * M,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s1.mem idx =
          if idx % 16 = 4 ∧ idx / 16 < b₀ + 1 then 1 else 0 := by
      intro idx hidx
      dsimp only [s1, m1]
      by_cases heq : idx = 16 * b₀ + 4
      · subst heq
        rw [readPacked_writePacked_self _ _ _ _ _ h1_lt]
        have hmod : (16 * b₀ + 4) % 16 = 4 := by omega
        have hdiv : (16 * b₀ + 4) / 16 < b₀ + 1 := by omega
        rw [ite_eq_left ⟨hmod, hdiv⟩]
      · rw [readPacked_writePacked_of_ne hw _ heq, hbm idx hidx]
        have hiff : (idx % 16 = 4 ∧ idx / 16 < b₀) ↔ (idx % 16 = 4 ∧ idx / 16 < b₀ + 1) := by
          have hdm := Nat.div_add_mod idx 16
          omega
        by_cases hc : idx % 16 = 4 ∧ idx / 16 < b₀
        · rw [ite_eq_left hc, ite_eq_left (hiff.mp hc)]
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hiff.mpr h))]
    obtain ⟨hf_r, hmc_r, hvp_r, hbm_r, hout_r⟩ := ih (b₀ + 1) s1 (by omega) hbm1
    have hadd : b₀ + 1 + rem = b₀ + (rem + 1) := by omega
    rw [hadd] at hbm_r
    unfold initOmRoleLoopProg at hf_r hmc_r hvp_r hbm_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_, fun a ha => ?_⟩
    · rw [clientState_bind, hs1, hr1]; exact hf_r
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      change memoryCost p1 s + _ = _
      rw [hmc1, hs1, hr1, hmc_r]; omega
    · refine validProg_bind hvp1 ?_; rw [hs1, hr1]; exact hvp_r
    · intro idx hidx; rw [clientState_bind, hs1, hr1]; exact hbm_r idx hidx
    · rw [clientState_bind, hs1, hr1, hout_r a ha]
      exact writePacked_outside hw _ hidx_lt _ (by omega)

/-- Step writing `poolFreeStack j := j` in `offPoolFreeStack` (`d = (rt, j)`). -/
@[irreducible] private def initFreeStackStepProg : InitFastRt × ℕ → Memory.Prog ℕ
  | (rt, j_in) => do
    let j ← pure j_in
    let one_v ← pure 1
    writePackedGenProg ((((ifrBase rt, ifrOffPs rt), (ifrGBits rt, ifrW rt)), j), j)
    pure (j + one_v)

private theorem memoryCost_initFreeStackStep_pos (d : InitFastRt × ℕ) (s : Memory.State) :
    0 < memoryCost (initFreeStackStepProg d) s := by
  rcases d with ⟨rt, j⟩
  unfold initFreeStackStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 4 + 0
  omega

private def InitFreeStackStepPre (w : ℕ) (d : InitFastRt × ℕ) (_s : Memory.State) : Prop :=
  InitFastRtEnv w d.1 ∧ d.2 < ifrPoolSize d.1

private theorem realizes_initFreeStackStep :
    Realizes .exact initFreeStackStepProg
      (WordEncoding.encode (α := InitFastRt × ℕ))
      (WordEncoding.encode (α := ℕ))
      InitFreeStackStepPre
      (fun _ _ => 0) := by
  unfold initFreeStackStepProg
  realize [realizes_writePackedGen]
  all_goals (
    rcases d with ⟨rt, j⟩
    dsimp only [InitFreeStackStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hj_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize ifrBase rt = base at henv heq_rt
    subst heq_rt
    have hps_le : poolSizeWhp n_max ≤ n_max := Nat.sub_le _ _
    have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.1
    have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
    dsimp only [mkInitFastRt, ifrBase, ifrW, ifrPoolSize, ifrGBits, ifrOffPs] at hj_lt ⊢
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.packed_safe_of_le hgk hj_lt hseg
  )

@[irreducible] private def initFreeStackLoopProg : (InitFastRt × ℕ) × ℕ → Memory.Prog ℕ
  | ((rt, j₀), rem) => iterate initFreeStackStepProg rt rem j₀

private theorem realizes_initFreeStackLoop :
    Realizes .exact initFreeStackLoopProg
      (WordEncoding.encode (α := (InitFastRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((rt, j₀), rem) s =>
        iterationSafe initFreeStackStepProg InitFreeStackStepPre w rt rem j₀ s)
      (fun _ _ => 0) := by
  unfold initFreeStackLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := InitFastRt))
    (WordEncoding.encode (α := ℕ))
    realizes_initFreeStackStep
    memoryCost_initFreeStackStep_pos

private theorem initFreeStackLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkInitFastRt c U V w n_max base
    ∀ rem j₀ (s : Memory.State),
      j₀ + rem ≤ poolSizeWhp n_max →
      iterationSafe initFreeStackStepProg InitFreeStackStepPre w rt rem j₀ s := by
  intro rt rem
  induction rem with
  | zero => intro _ _ _; exact trivial
  | succ rem ih =>
    intro j₀ s hle
    refine ⟨⟨⟨c, U, V, w, n_max, henv, rfl⟩, by dsimp [rt, mkInitFastRt, ifrPoolSize]; omega⟩, ?_⟩
    rw [clientState_width, clientResult_width]
    have hr : (Memory.spec 0).clientResult s (initFreeStackStepProg (rt, j₀)) = j₀ + 1 := by
      unfold initFreeStackStepProg
      simp only [pure_bind, clientResult_bind, clientResult_pure_whp]
    rw [hr]
    exact ih (j₀ + 1) _ (by omega)

private theorem initFreeStackLoop_spec {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkInitFastRt c U V w n_max base
    let ps := poolSizeWhp n_max
    ∀ rem j₀ (s : Memory.State),
      j₀ + rem ≤ ps →
      (∀ idx < ps,
        readPacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s.mem idx =
          if idx < j₀ then idx else 0) →
      let prog := initFreeStackLoopProg ((rt, j₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      memoryCost prog s = 4 * rem ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ idx < ps,
        readPacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
          if idx < j₀ + rem then idx else 0) ∧
      (∀ a, (a < base + offPoolFreeStack c U V w n_max ∨
          base + offPoolOwner c U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  intro rt ps rem
  have hw := henv.2.1
  have hps_le : ps ≤ n_max := Nat.sub_le _ _
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.1
  have hps_b : base + offPoolFreeStack c U V w n_max +
      packedWords ps (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  have hps_end : offPoolFreeStack c U V w n_max +
      packedWords ps (globalPtrBits n_max) w = offPoolOwner c U V w n_max := rfl
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  induction rem with
  | zero =>
    intro j₀ s _ hps_rep
    unfold initFreeStackLoopProg iterate
    rw [Nat.add_zero, Nat.mul_zero]
    exact ⟨rfl, rfl, validProg_pure _, hps_rep, fun _ _ => rfl⟩
  | succ rem ih =>
    intro j₀ s hle hps_rep
    have hj_lt : j₀ < ps := by omega
    have hj_pow : j₀ < 2 ^ globalPtrBits n_max :=
      lt_two_pow_globalPtrBits_of_le_n_max (hj_lt.le.trans hps_le)
    set p1 := initFreeStackStepProg (rt, j₀)
    set m1 := writePacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s.mem
      j₀ j₀
    have hs1 : (Memory.spec 0).clientState s p1 = { mem := m1, frontier := s.frontier } := by
      dsimp only [p1]; unfold initFreeStackStepProg
      simp only [pure_bind]
      rw [clientState_bind, clientState_writePackedGen, clientState_pure_whp]
      rfl
    have hr1 : (Memory.spec 0).clientResult s p1 = j₀ + 1 := by
      dsimp only [p1]; unfold initFreeStackStepProg
      simp only [pure_bind, clientResult_bind, clientResult_pure_whp]
    have hmc1 : memoryCost p1 s = 4 := by
      dsimp only [p1]; unfold initFreeStackStepProg
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
        memoryCost_writePackedGen, memoryCost_pure]
    have hvp1 : ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold initFreeStackStepProg; simp only [pure_bind]
      exact validProg_bind (validProg_writePacked hw hgk hj_lt hps_b) (validProg_pure _)
    set s1 : Memory.State := { mem := m1, frontier := s.frontier }
    have hps1 : ∀ idx < ps,
        readPacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s1.mem idx =
          if idx < j₀ + 1 then idx else 0 := by
      intro idx hidx
      dsimp only [s1, m1]
      by_cases heq : idx = j₀
      · subst idx
        rw [readPacked_writePacked_self _ _ _ _ _ hj_pow, ite_eq_left (Nat.lt_succ_self j₀)]
      · rw [readPacked_writePacked_of_ne hw _ heq, hps_rep idx hidx]
        split_ifs <;> omega
    obtain ⟨hf_r, hmc_r, hvp_r, hps_r, hout_r⟩ := ih (j₀ + 1) s1 (by omega) hps1
    have hadd : j₀ + 1 + rem = j₀ + (rem + 1) := by omega
    rw [hadd] at hps_r
    unfold initFreeStackLoopProg at hf_r hmc_r hvp_r hps_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_, fun a ha => ?_⟩
    · rw [clientState_bind, hs1, hr1]; exact hf_r
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      change memoryCost p1 s + _ = _
      rw [hmc1, hs1, hr1, hmc_r]; omega
    · refine validProg_bind hvp1 ?_; rw [hs1, hr1]; exact hvp_r
    · intro idx hidx; rw [clientState_bind, hs1, hr1]; exact hps_r idx hidx
    · rw [clientState_bind, hs1, hr1, hout_r a ha]
      exact writePacked_outside hw _ hj_lt _ (by omega)

/-- Write the five non-zero initial fast-state header words (`d = (base, poolSize)`). -/
@[irreducible] private def initFastHdrsProg : ℕ × ℕ → Memory.Prog Unit
  | (base_in, ps_in) => do
    let base ← pure base_in
    let ps ← pure ps_in
    let one_v ← pure 1
    let five_v ← pure 5
    let a1 ← pure (base + hdrPoolFreeTop)
    let a4 ← pure (base + hdrRebStage)
    let a12 ← pure (base + hdrBuf0NodeAlloc)
    let a14 ← pure (base + hdrBuf1NodeAlloc)
    Memory.write base one_v
    Memory.write a1 ps
    Memory.write a4 five_v
    Memory.write a12 one_v
    Memory.write a14 one_v

private theorem realizes_initFastHdrs :
    Realizes .exact initFastHdrsProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (base, _) _ => 3 ≤ w ∧ Fits w (base + 32))
      (fun _ _ => 0) := by
  unfold initFastHdrsProg
  realize
  all_goals (
    rcases d with ⟨base, ps⟩
    obtain ⟨hw3, hfit32⟩ := h
    have h5_fit : Fits w 5 :=
      (by decide : 5 < 2 ^ 3).trans_le (Nat.pow_le_pow_right two_pos hw3)
    first
    | exact h5_fit.of_le (by decide)
    | (refine hfit32.of_le ?_; dsimp [hdrPoolFreeTop, hdrRebStage, hdrBuf0NodeAlloc,
        hdrBuf1NodeAlloc]; omega)
  )

private theorem initFastHdrsProg_spec {w F base ps : ℕ}
    (h32 : base + 32 ≤ F) (hw3 : 3 ≤ w) (hps_fit : Fits w ps) (s : Memory.State) :
    let prog := initFastHdrsProg (base, ps)
    let s' := (Memory.spec 0).clientState s prog
    s'.mem =
      Function.update
        (Function.update
          (Function.update
            (Function.update (Function.update s.mem base 1) (base + hdrPoolFreeTop) ps)
            (base + hdrRebStage) 5)
          (base + hdrBuf0NodeAlloc) 1)
        (base + hdrBuf1NodeAlloc) 1 ∧
    s'.frontier = s.frontier ∧
    memoryCost prog s = 5 ∧
    ValidProg w F s prog := by
  have h5_fit : Fits w 5 :=
    (by decide : 5 < 2 ^ 3).trans_le (Nat.pow_le_pow_right two_pos hw3)
  have h1_fit : Fits w 1 := h5_fit.of_le (by decide)
  dsimp only
  unfold initFastHdrsProg
  simp only [pure_bind]
  refine ⟨rfl, rfl, rfl, ?_⟩
  refine validProg_bind (validProg_write (by omega) h1_fit) ?_
  refine validProg_bind (validProg_write (by dsimp [hdrPoolFreeTop]; omega) hps_fit) ?_
  refine validProg_bind (validProg_write (by dsimp [hdrRebStage]; omega) h5_fit) ?_
  refine validProg_bind (validProg_write (by dsimp [hdrBuf0NodeAlloc]; omega) h1_fit) ?_
  exact validProg_write (by dsimp [hdrBuf1NodeAlloc]; omega) h1_fit

/-- Initialize `emptyFastState n_max` at `base` (`d = (cp, base)`). -/
@[irreducible] def initFastGenProg : WhpCoreParams × ℕ → Memory.Prog Unit
  | d => do
    let rt ← mkInitFastRtGenProg d
    let zero_v ← pure 0
    let _ ← initOmRoleLoopProg ((rt, zero_v), ifrM rt)
    let _ ← initFreeStackLoopProg ((rt, zero_v), ifrPoolSize rt)
    initFastHdrsProg (ifrBase rt, ifrPoolSize rt)

theorem realizes_initFastGen :
    Realizes .exact initFastGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => WhpLargeEnvGen w d.1 d.2)
      (fun _ _ => 0) := by
  unfold initFastGenProg
  realize [realizes_mkInitFastRtGen, realizes_initOmRoleLoop, realizes_initFreeStackLoop,
      realizes_initFastHdrs]
  all_goals (
    rcases d with ⟨cp, base⟩
    obtain ⟨c, U, V, w₀, n_max, henv, rfl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hw3 := WhpLargeEnv.three_le_w henv
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hmk_st, hmk_res, _, _⟩ := mkInitFastRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    simp only [hmk_st, hmk_res] at *
    try dsimp only [mkInitFastRt, ifrBase, ifrM, ifrPoolSize] at *
    first
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact initOmRoleLoop_safe henv (numBucketsWhp n_max) 0 _ (by omega)
    | exact initFreeStackLoop_safe henv (poolSizeWhp n_max) 0 _ (by omega)
    | exact hw3
    | exact henv.fits_largeSpace.of_le (by omega)
  )

/-- Exact specification of `initFastGenProg`: starting from zeroed headers `[base, base + 32)` and
zeroed body `[base + offQuotWhp c w n_max, base + largeSpaceWhp c U V w n_max)` with
`SeedWhpMemRep` on `[base + 32, base + offQuotWhp c w n_max)`, establishes `FastMemRep` for
`emptyFastState n_max` in `initFastCostWhp n_max` deterministic memory operations. -/
theorem initFastGenProg_spec {c U V w n_max base : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hz_hdr : ∀ a, base ≤ a → a < base + 32 → s.mem a = 0)
    (hz_body : ∀ a, base + offQuotWhp c w n_max ≤ a →
      a < base + largeSpaceWhp c U V w n_max → s.mem a = 0) :
    let prog := initFastGenProg (mkWhpCoreParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    SeedWhpMemRep base c U w n_max θ s'.mem ∧
    FastMemRep base c U V w n_max (emptyFastState n_max) s'.mem ∧
    s'.frontier = s.frontier ∧
    memoryCost prog s = initFastCostWhp n_max ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    (∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  have hw3 := WhpLargeEnv.three_le_w henv
  obtain ⟨hq_end, hv_end, _, hls_end, _, _, hbp_end, _, hpo_end, _, _, _, htc0_end, htc1_end,
    htm0_end, htm1_end, _, _⟩ := WhpLargeEnv.seg_end_le c U V w n_max
  have hch := largeOffsetChain c U V w n_max
  set M := numBucketsWhp n_max
  set ps := poolSizeWhp n_max
  set rt := mkInitFastRt c U V w n_max base
  obtain ⟨hmk_st, hmk_res, hmk_mc, hmk_vp⟩ :=
    mkInitFastRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
      (base := base) hth s
  -- Step 1: `initOmRoleLoopProg`
  have hbm0 : ∀ idx < 16 * M,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx =
        if idx % 16 = 4 ∧ idx / 16 < 0 then 1 else 0 := by
    intro idx hidx
    simp only [Nat.not_lt_zero, and_false, ↓reduceIte]
    exact readPacked_eq_zero_of_zero_range hw hidx fun a ha1 ha2 => hz_body a (by omega) (by omega)
  obtain ⟨hf1, hmc1, hvp1, hbm1, hout1⟩ := initOmRoleLoop_spec henv M 0 s (by omega) hbm0
  rw [Nat.zero_add] at hbm1
  set s1 := (Memory.spec 0).clientState s (initOmRoleLoopProg ((rt, 0), M))
  -- Step 2: `initFreeStackLoopProg`
  have hps0 : ∀ idx < ps,
      readPacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s1.mem idx =
        if idx < 0 then idx else 0 := by
    intro idx hidx
    simp only [Nat.not_lt_zero, ↓reduceIte]
    exact readPacked_eq_zero_of_zero_range hw hidx fun a ha1 ha2 =>
      (hout1 a (Or.inr (by omega))).trans (hz_body a (by omega) (by omega))
  obtain ⟨hf2, hmc2, hvp2, hps2, hout2⟩ := initFreeStackLoop_spec henv ps 0 s1 (by omega) hps0
  rw [Nat.zero_add] at hps2
  set s2 := (Memory.spec 0).clientState s1 (initFreeStackLoopProg ((rt, 0), ps))
  -- Step 3: `initFastHdrsProg`
  have hps_fit : Fits w ps := henv.fits_of_le_n_max (Nat.sub_le _ _)
  obtain ⟨hm3, hf3, hmc3, hvp3⟩ :=
    initFastHdrsProg_spec (F := base + largeSpaceWhp c U V w n_max) (base := base) (ps := ps)
      (by omega) hw3 hps_fit s2
  set s3 := (Memory.spec 0).clientState s2 (initFastHdrsProg (base, ps))
  have hs'_eq : (Memory.spec 0).clientState s
      (initFastGenProg (mkWhpCoreParams c U V w n_max, base)) = s3 := by
    unfold initFastGenProg
    rw [clientState_bind, hmk_st, hmk_res]
    dsimp only [mkInitFastRt, ifrBase, ifrM, ifrPoolSize]
    simp only [pure_bind]
    rw [clientState_bind, clientState_bind]
    rfl
  -- Helper: s3 agrees with s2 everywhere >= base + 32 (and < base)
  have hs3_ge32 : ∀ a, (a < base ∨ base + 32 ≤ a) → s3.mem a = s2.mem a := by
    intro a ha
    rw [hm3]
    dsimp only [hdrPoolFreeTop, hdrRebStage, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]
    repeat rw [Function.update_of_ne (by omega)]
  -- Helper: untouched zero segments in s3
  have hz_seg : ∀ a, base + offQuotWhp c w n_max ≤ a →
      a < base + largeSpaceWhp c U V w n_max →
      (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
      (a < base + offPoolFreeStack c U V w n_max ∨ base + offPoolOwner c U V w n_max ≤ a) →
      s3.mem a = 0 := by
    intro a ha1 ha2 hno_bm hno_ps
    rw [hs3_ge32 a (Or.inr (by omega)), hout2 a hno_ps, hout1 a hno_bm]
    exact hz_body a ha1 ha2
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · -- SeedWhpMemRep
    rw [hs'_eq]
    refine SeedWhpMemRep.congr_hash hw (fun a ha1 ha2 => ?_) hseed
    dsimp only [offHashBkt] at ha1
    exact ((hs3_ge32 a (Or.inr ha1)).trans
      ((hout2 a (Or.inl (by omega))).trans (hout1 a (Or.inl (by omega))))).symm
  · -- FastMemRep for emptyFastState n_max
    rw [hs'_eq]
    have hs2_hdr : ∀ off < 32, s2.mem (base + off) = 0 := fun off hoff =>
      (hout2 _ (Or.inl (by omega))).trans
        ((hout1 _ (Or.inl (by omega))).trans (hz_hdr _ (by omega) (by omega)))
    have hhdr0 : s3.mem (base + hdrMode) = 1 := by
      rw [hm3]; dsimp only [hdrMode, hdrPoolFreeTop, hdrRebStage, hdrBuf0NodeAlloc,
        hdrBuf1NodeAlloc]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Nat.add_zero, Function.update_self]
    have hhdr1 : s3.mem (base + hdrPoolFreeTop) = ps := by
      rw [hm3]; dsimp only [hdrPoolFreeTop, hdrRebStage, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    have hhdr4 : s3.mem (base + hdrRebStage) = 5 := by
      rw [hm3]; dsimp only [hdrRebStage, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    have hhdr12 : s3.mem (base + hdrBuf0NodeAlloc) = 1 := by
      rw [hm3]; dsimp only [hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]
      rw [Function.update_of_ne (by omega), Function.update_self]
    have hhdr14 : s3.mem (base + hdrBuf1NodeAlloc) = 1 := by
      rw [hm3]; exact Function.update_self _ _ _
    have hhdr_z : ∀ off < 32, off ≠ 0 → off ≠ 1 → off ≠ 4 → off ≠ 12 → off ≠ 14 →
        s3.mem (base + off) = 0 := by
      intro off hoff h0 h1 h4 h12 h14
      rw [hm3]; dsimp only [hdrPoolFreeTop, hdrRebStage, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]
      repeat rw [Function.update_of_ne (by omega)]
      exact hs2_hdr off hoff
    have hbm_s3 : ∀ idx < 16 * M,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s3.mem idx =
          if idx % 16 = 4 ∧ idx / 16 < M then 1 else 0 := by
      intro idx hidx
      rw [readPacked_congr hw (fun a ⟨ha1, ha2⟩ =>
        (hs3_ge32 a (Or.inr (by omega))).trans (hout2 a (Or.inl (by omega)))) hidx]
      exact hbm1 idx hidx
    have hps_s3 : ∀ j < ps,
        readPacked (base + offPoolFreeStack c U V w n_max)
          (globalPtrBits n_max) w s3.mem j = j := by
      intro j hj
      rw [readPacked_congr hw (fun a ⟨ha1, ha2⟩ => hs3_ge32 a (Or.inr (by omega))) hj,
        hps2 j hj, ite_eq_left hj]
    have hmt_pos : 1 ≤ maxTrieNodesWhp c n_max := by unfold maxTrieNodesWhp; omega
    dsimp only [FastMemRep, emptyFastState]
    refine ⟨Nat.zero_le _, hhdr0, hhdr1,
      hhdr_z 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hhdr_z 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hhdr4,
      hhdr_z 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hhdr_z 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hhdr_z 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hhdr_z 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hhdr_z 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hhdr_z 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hhdr_z 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    · -- quotArr & valArr
      intro i hi
      exact ⟨readPacked_eq_zero_of_zero_range hw hi fun a ha1 ha2 =>
          hz_seg a (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
        readPacked_eq_zero_of_zero_range hw hi fun a ha1 ha2 =>
          hz_seg a (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))⟩
    · -- locState
      intro b hb loc hloc
      have hidx : b * totalLocalCoordsWhp n_max + loc < M * totalLocalCoordsWhp n_max := by
        calc b * totalLocalCoordsWhp n_max + loc
            < b * totalLocalCoordsWhp n_max + totalLocalCoordsWhp n_max :=
              Nat.add_lt_add_left hloc _
          _ = (b + 1) * totalLocalCoordsWhp n_max := by ring
          _ ≤ M * totalLocalCoordsWhp n_max := Nat.mul_le_mul_right _ hb
      exact readPacked_eq_zero_of_zero_range hw hidx fun a ha1 ha2 =>
        hz_seg a (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    · -- bktMeta fields 0..9
      intro b hb
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hbm_s3 (16 * b + 0) (by omega)]; split_ifs with hc <;> [omega; rfl]
      · rw [hbm_s3 (16 * b + 1) (by omega)]; split_ifs with hc <;> [omega; rfl]
      · rw [hbm_s3 (16 * b + 2) (by omega)]; split_ifs with hc <;> [omega; rfl]
      · rw [hbm_s3 (16 * b + 3) (by omega)]; split_ifs with hc <;> [omega; rfl]
      · rw [hbm_s3 (16 * b + 4) (by omega)]; exact ite_eq_left ⟨by omega, by omega⟩
      · rw [hbm_s3 (16 * b + 5) (by omega)]; split_ifs with hc <;> [omega; rfl]
      · rw [hbm_s3 (16 * b + 6) (by omega)]; split_ifs with hc <;> [omega; rfl]
      · rw [hbm_s3 (16 * b + 7) (by omega)]; split_ifs with hc <;> [omega; rfl]
      · rw [hbm_s3 (16 * b + 8) (by omega)]; split_ifs with hc <;> [omega; rfl]
      · rw [hbm_s3 (16 * b + 9) (by omega)]; split_ifs with hc <;> [omega; rfl]
    · -- backPtr
      intro b hb k hk
      have hidx : b * capBackWhp n_max + k < M * capBackWhp n_max := by
        calc b * capBackWhp n_max + k < b * capBackWhp n_max + capBackWhp n_max :=
              Nat.add_lt_add_left hk _
          _ = (b + 1) * capBackWhp n_max := by ring
          _ ≤ M * capBackWhp n_max := Nat.mul_le_mul_right _ hb
      exact readPacked_eq_zero_of_zero_range hw hidx fun a ha1 ha2 =>
        hz_seg a (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
    · -- poolFreeStack & poolOwner
      intro j hj
      refine ⟨by rw [hps_s3 j hj, ite_eq_left hj], ?_⟩
      exact readPacked_eq_zero_of_zero_range hw hj fun a ha1 ha2 =>
        hz_seg a (by dsimp only [M, ps] at *; omega) (by dsimp only [M, ps] at *; omega)
          (Or.inr (by dsimp only [M, ps] at *; omega))
          (Or.inr (by dsimp only [M, ps] at *; omega))
    · -- slices (zeroBTreeSlice)
      intro sIdx hsIdx
      dsimp only [BTreeSliceMemRep, zeroBTreeSlice]
      refine ⟨Nat.zero_le _, ?_, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · rw [hbm_s3 (16 * (sIdx / 3) + 10 + 2 * (sIdx % 3)) (by omega)]
        split_ifs with hc <;> [omega; rfl]
      · rw [hbm_s3 (16 * (sIdx / 3) + 11 + 2 * (sIdx % 3)) (by omega)]
        split_ifs with hc <;> [omega; rfl]
    · -- BufTrieMemRep 0
      dsimp only [BufTrieMemRep, emptyBufTrie]
      simp only [↓reduceIte]
      refine ⟨hmt_pos, Nat.zero_le _, hhdr12,
        hhdr_z 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        fun u hu ch hch => ?_, fun u h1 hlt => by omega, fun u hu => ⟨?_, fun h => absurd rfl h⟩,
        fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · have hidx : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := by
          unfold trieChildEntriesWhp
          calc u * 2 ^ bCharWhp n_max + ch < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max :=
                Nat.add_lt_add_left hch _
            _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
            _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
        exact readPacked_eq_zero_of_zero_range hw hidx fun a ha1 ha2 =>
          hz_seg a (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      · have hu0 : u = 0 := by omega
        subst hu0
        exact readPacked_eq_zero_of_zero_range hw
          (show 2 < 6 * maxTrieNodesWhp c n_max by omega) fun a ha1 ha2 =>
            hz_seg a (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
    · -- BufTrieMemRep 1
      dsimp only [BufTrieMemRep, emptyBufTrie]
      simp only [Nat.one_ne_zero, ↓reduceIte]
      refine ⟨hmt_pos, Nat.zero_le _, hhdr14,
        hhdr_z 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        fun u hu ch hch => ?_, fun u h1 hlt => by omega, fun u hu => ⟨?_, fun h => absurd rfl h⟩,
        fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · have hidx : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := by
          unfold trieChildEntriesWhp
          calc u * 2 ^ bCharWhp n_max + ch < u * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max :=
                Nat.add_lt_add_left hch _
            _ = (u + 1) * 2 ^ bCharWhp n_max := by ring
            _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hu
        exact readPacked_eq_zero_of_zero_range hw hidx fun a ha1 ha2 =>
          hz_seg a (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      · have hu0 : u = 0 := by omega
        subst hu0
        exact readPacked_eq_zero_of_zero_range hw
          (show 2 < 6 * maxTrieNodesWhp c n_max by omega) fun a ha1 ha2 =>
            hz_seg a (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  · rw [hs'_eq, hf3, hf2, hf1]
  · unfold initFastGenProg
    simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hmk_st, hmk_res, hmk_mc]
    dsimp only [mkInitFastRt, ifrBase, ifrM, ifrPoolSize, s1, s2, rt, M, ps] at hmc1 hmc2 hmc3 ⊢
    rw [hmc1, hmc2, hmc3]; unfold initFastCostWhp; omega
  · unfold initFastGenProg
    refine validProg_bind hmk_vp ?_
    rw [hmk_st, hmk_res]
    dsimp only [mkInitFastRt, ifrBase, ifrM, ifrPoolSize]
    simp only [pure_bind]
    refine validProg_bind hvp1 ?_
    exact validProg_bind hvp2 hvp3
  · rw [hs'_eq]
    rcases ha with ha_lo | ha_hi
    · exact (hs3_ge32 a (Or.inl ha_lo)).trans
        ((hout2 a (Or.inl (by omega))).trans (hout1 a (Or.inl (by omega))))
    · exact (hs3_ge32 a (Or.inr (by omega))).trans
        ((hout2 a (Or.inr (by omega))).trans (hout1 a (Or.inr (by omega))))

/-! ## Section 3: Scratch-Free `checkGoodSeedOnStateGenProg` -/

/-- Compact 11-word runtime bundle for `checkGoodSeedOnStateGenProg`:
`((((base, w), (nMax, M)), ((delta, sMax), (gBits, qBits))), ((offFb, offQ), offBm))`. -/
private abbrev ChkRt : Type :=
  (((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) × ((ℕ × ℕ) × ℕ)

private def ckBase (crt : ChkRt) : ℕ := crt.1.1.1.1
private def ckW (crt : ChkRt) : ℕ := crt.1.1.1.2
private def ckNMax (crt : ChkRt) : ℕ := crt.1.1.2.1
private def ckM (crt : ChkRt) : ℕ := crt.1.1.2.2
private def ckDelta (crt : ChkRt) : ℕ := crt.1.2.1.1
private def ckSMax (crt : ChkRt) : ℕ := crt.1.2.1.2
private def ckGBits (crt : ChkRt) : ℕ := crt.1.2.2.1
private def ckQBits (crt : ChkRt) : ℕ := crt.1.2.2.2
private def ckOffFb (crt : ChkRt) : ℕ := crt.2.1.1
private def ckOffQ (crt : ChkRt) : ℕ := crt.2.1.2
private def ckOffBm (crt : ChkRt) : ℕ := crt.2.2

/-- Construct `ChkRt` for `(c, U, V, w, n_max, base)`. -/
private def mkChkRt (c U V w n_max base : ℕ) : ChkRt :=
  ((((base, w), (n_max, numBucketsWhp n_max)),
    ((deltaWhp n_max, sMaxWhp c n_max), (globalPtrBits n_max, quotBitsWhp U n_max))),
   ((offFbStart c U V w n_max, offQuotWhp c w n_max), offBktMeta c U V w n_max))

/-- Parameter-free `ChkRt` envelope (`crt` only, for subroutines not reading hash tables). -/
private def ChkRtEnvGen (w : ℕ) (crt : ChkRt) : Prop :=
  ∃ c U V w₀ n_max, WhpLargeEnv c U V w₀ n_max w (ckBase crt) ∧
    crt = mkChkRt c U V w₀ n_max (ckBase crt)

/-- Combined `(ChkRt, HashRt)` + `SeedWhpMemRep` envelope. -/
private def ChkHashEnv (w : ℕ) (crt : ChkRt) (hrt : HashRt) (s : Memory.State) : Prop :=
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max),
    WhpLargeEnv c U V w₀ n_max w (ckBase crt) ∧
    crt = mkChkRt c U V w₀ n_max (ckBase crt) ∧
    hrt = mkHashRt c U w₀ n_max (ckBase crt) ∧
    SeedWhpMemRep (ckBase crt) c U w₀ n_max θ s.mem

@[irreducible] private def mkChkRtGenProg : WhpCoreParams × ℕ → Memory.Prog ChkRt
  | (cp, base_in) => do
    let base ← pure base_in
    let p1 ← pure ((base, wpW cp), (wpNMax cp, wpM cp))
    let p2 ← pure ((wpDelta cp, wpSMax cp), (wpGlobalPtrBits cp, wpQuotBits cp))
    let p3 ← pure ((wpOffFbStart cp, wpOffQuot cp), wpOffBktMeta cp)
    pure ((p1, p2), p3)

private theorem realizes_mkChkRtGen :
    Realizes .exact mkChkRtGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := ChkRt))
      (fun w d _ => WhpLargeEnvGen w d.1 d.2)
      (fun _ _ => 0) := by
  unfold mkChkRtGenProg
  realize

private theorem mkChkRtGenProg_spec {c U V w n_max base : ℕ}
    (hth : whpThreshold c ≤ n_max) (s : Memory.State) :
    let prog := mkChkRtGenProg (mkWhpCoreParams c U V w n_max, base)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = mkChkRt c U V w n_max base ∧
    memoryCost prog s = 0 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  dsimp only
  unfold mkChkRtGenProg
  simp only [wp_large_w hth, wp_large_nMax hth, wp_large_M hth,
    wp_large_delta hth, wp_large_sMax hth, wp_large_globalPtrBits hth, wp_large_quotBits hth,
    wp_large_offFbStart hth, wp_large_offQuot hth, wp_large_offBktMeta hth, pure_bind]
  exact ⟨rfl, rfl, rfl, validProg_pure _⟩

private theorem chk_fb_safe {c U V w n_max base idx : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hidx : idx < numBucketsWhp n_max + 1) :
    ∃ N, True ∧ 0 < w ∧ globalPtrBits n_max ≤ w ∧ idx < N ∧
      Fits w (base + offFbStart c U V w n_max + packedWords N (globalPtrBits n_max) w) := by
  obtain ⟨N, _, h1, h2, h3, h4⟩ :=
    henv.packed_safe_of_le (globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1) hidx
      (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.1
  exact ⟨N, trivial, h1, h2, h3, h4⟩

private theorem chk_quot_safe {c U V w n_max base idx : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hidx : idx < n_max) :
    ∃ N, True ∧ 0 < w ∧ quotBitsWhp U n_max ≤ w ∧ idx < N ∧
      Fits w (base + offQuotWhp c w n_max + packedWords N (quotBitsWhp U n_max) w) := by
  obtain ⟨N, _, h1, h2, h3, h4⟩ :=
    henv.packed_safe_of_le ((Nat.sub_le _ _).trans (keyBits_le_w henv.2.2.2.2.2.1)) hidx
      (WhpLargeEnv.seg_end_le c U V w n_max).1
  exact ⟨N, trivial, h1, h2, h3, h4⟩

private theorem chk_bm_safe {c U V w n_max base idx : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hidx : idx < 16 * numBucketsWhp n_max) :
    ∃ N, True ∧ 0 < w ∧ globalPtrBits n_max ≤ w ∧ idx < N ∧
      Fits w (base + offBktMeta c U V w n_max + packedWords N (globalPtrBits n_max) w) := by
  obtain ⟨N, _, h1, h2, h3, h4⟩ :=
    henv.packed_safe_of_le (globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1) hidx
      (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.1
  exact ⟨N, trivial, h1, h2, h3, h4⟩

/-! ### Part 3a: Bucket load-balance loop (`checkAllBalancedCsr`) -/

/-- Step checking `checkBalancedBucketNat M δ N (fbStart (b + 1) - fbStart b)`
(`d = ((crt, N), (b, okAcc))`). -/
@[irreducible] private def chkBalStepProg : (ChkRt × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((crt, N_in), (b_in, ok_in)) => do
    let N ← pure N_in
    let b ← pure b_in
    let okAcc ← pure ok_in
    let M ← pure (ckM crt)
    let δ ← pure (ckDelta crt)
    let zero_v ← pure 0
    let one_v ← pure 1
    let b1 ← pure (b + one_v)
    let lo ← readPackedGenProg (((ckBase crt, ckOffFb crt), (ckGBits crt, ckW crt)), b)
    let hi ← readPackedGenProg (((ckBase crt, ckOffFb crt), (ckGBits crt, ckW crt)), b1)
    let qN ← pure (N / M)
    let rN ← pure (N % M)
    let ub ← pure (qN + δ)
    if okAcc = one_v then
      if lo ≤ hi then
        let xb ← pure (hi - lo)
        if xb ≤ ub then
          if rN = zero_v then
            if δ ≤ qN then
              let lb0 ← pure (qN - δ)
              if lb0 ≤ xb then pure (b1, one_v) else pure (b1, zero_v)
            else
              pure (b1, one_v)
          else
            let q1 ← pure (qN + one_v)
            if δ ≤ q1 then
              let lb1 ← pure (q1 - δ)
              if lb1 ≤ xb then pure (b1, one_v) else pure (b1, zero_v)
            else
              pure (b1, one_v)
        else
          pure (b1, zero_v)
      else
        if zero_v ≤ ub then
          if rN = zero_v then
            if δ ≤ qN then
              let lb0 ← pure (qN - δ)
              if lb0 ≤ zero_v then pure (b1, one_v) else pure (b1, zero_v)
            else
              pure (b1, one_v)
          else
            let q1 ← pure (qN + one_v)
            if δ ≤ q1 then
              let lb1 ← pure (q1 - δ)
              if lb1 ≤ zero_v then pure (b1, one_v) else pure (b1, zero_v)
            else
              pure (b1, one_v)
        else
          pure (b1, zero_v)
    else
      pure (b1, zero_v)

private theorem memoryCost_chkBalStep_pos (d : (ChkRt × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    0 < memoryCost (chkBalStepProg d) s := by
  rcases d with ⟨⟨crt, N⟩, b, okAcc⟩
  unfold chkBalStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

private def ChkBalStepPre (w : ℕ) (d : (ChkRt × ℕ) × (ℕ × ℕ)) (_s : Memory.State) : Prop :=
  ChkRtEnvGen w d.1.1 ∧ d.1.2 ≤ ckNMax d.1.1 ∧ d.2.1 < ckM d.1.1

private theorem realizes_chkBalStep :
    Realizes .exact chkBalStepProg
      (WordEncoding.encode (α := (ChkRt × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      ChkBalStepPre
      (fun _ _ => 0) := by
  unfold chkBalStepProg
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize [realizes_readPackedGen]
  all_goals (
    rcases d with ⟨⟨crt, N⟩, b, okAcc⟩
    dsimp only [ChkBalStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_crt⟩, hN_le, hb_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize ckBase crt = base at henv heq_crt
    subst heq_crt
    have hth := henv.2.2.2.1
    have hM_ge := (large_bounds_lt_n_max hth).1
    have hM_le := henv.numBuckets_le_n_max
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    have hqN_le : N / numBucketsWhp n_max ≤ n_max / 1024 :=
      (Nat.div_le_div_right hN_le).trans (Nat.div_le_div_left hM_ge (by decide))
    have hdel_le : deltaWhp n_max ≤ n_max / 1024 := by
      unfold deltaWhp
      have h8 : 1 ≤ 8 * slabScale n_max := by have := slabScale_pos n_max; omega
      have hprod : 1024 ≤ numBucketsWhp n_max * (8 * slabScale n_max) := by
        calc 1024 = 1024 * 1 := rfl
          _ ≤ numBucketsWhp n_max * (8 * slabScale n_max) := Nat.mul_le_mul hM_ge h8
      exact Nat.div_le_div_left hprod (by decide)
    dsimp only [mkChkRt, ckBase, ckW, ckNMax, ckM, ckDelta, ckGBits, ckOffFb] at *
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact chk_fb_safe henv (by omega)
  )

@[irreducible] private def chkBalLoopProg : ((ChkRt × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cfg, acc), rem) => iterate chkBalStepProg cfg rem acc

private theorem realizes_chkBalLoop :
    Realizes .exact chkBalLoopProg
      (WordEncoding.encode (α := ((ChkRt × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cfg, acc), rem) s =>
        iterationSafe chkBalStepProg ChkBalStepPre w cfg rem acc s)
      (fun _ _ => 0) := by
  unfold chkBalLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := ChkRt × ℕ))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_chkBalStep
    memoryCost_chkBalStep_pos

private theorem chkBalLoop_spec {c U V w n_max base N : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hN_le : N ≤ n_max) (s : Memory.State) :
    let crt := mkChkRt c U V w n_max base
    let M := numBucketsWhp n_max
    let fbMem := fun b => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w
      s.mem b
    ∀ rem b₀ ok₀,
      b₀ + rem ≤ M →
      (ok₀ = if checkAllBalancedCsr M (deltaWhp n_max) N fbMem b₀ then 1 else 0) →
      let prog := chkBalLoopProg (((crt, N), (b₀, ok₀)), rem)
      iterationSafe chkBalStepProg ChkBalStepPre w (crt, N) rem (b₀, ok₀) s ∧
      (Memory.spec 0).clientState s prog = s ∧
      (Memory.spec 0).clientResult s prog =
        (b₀ + rem, if checkAllBalancedCsr M (deltaWhp n_max) N fbMem (b₀ + rem) then 1 else 0) ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro crt M fbMem rem
  have hw := henv.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.1
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  induction rem with
  | zero =>
    intro b₀ ok₀ _ hok
    unfold chkBalLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨trivial, rfl, Prod.ext rfl hok, validProg_pure _⟩
  | succ rem ih =>
    intro b₀ ok₀ hle hok
    have hb_lt : b₀ < M := by omega
    have hpre : ChkBalStepPre w ((crt, N), (b₀, ok₀)) s :=
      ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hN_le, hb_lt⟩
    set p1 := chkBalStepProg ((crt, N), (b₀, ok₀))
    have hs1 : (Memory.spec 0).clientState s p1 = s := by
      dsimp only [p1]; unfold chkBalStepProg
      simp only [pure_bind]
      rw [clientState_bind, clientState_readPackedGen, clientState_bind,
        clientState_readPackedGen]
      split_ifs <;> rfl
    set ok1 := if checkAllBalancedCsr M (deltaWhp n_max) N fbMem (b₀ + 1) then 1 else 0
    have hr1 : (Memory.spec 0).clientResult s p1 = (b₀ + 1, ok1) := by
      dsimp only [p1]; unfold chkBalStepProg
      dsimp only [crt, mkChkRt, ckBase, ckW, ckM, ckDelta, ckGBits, ckOffFb]
      simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedGen, clientResult_readPackedGen,
        clientResult_bind, clientState_readPackedGen, clientResult_readPackedGen]
      dsimp only [ok1, checkAllBalancedCsr, checkBalancedBucketNat]
      rw [hok]
      by_cases hbal0 : checkAllBalancedCsr M (deltaWhp n_max) N fbMem b₀ = true
      · simp only [hbal0, Bool.true_and, ↓reduceIte]
        dsimp only [fbMem, M]
        have hr_beq : (N % numBucketsWhp n_max == 0) = decide (N % numBucketsWhp n_max = 0) := rfl
        rw [hr_beq]
        split_ifs <;>
          simp only [clientResult_pure_whp, Prod.mk.injEq, true_and,
            Bool.and_eq_true, decide_eq_true_eq] at * <;>
          omega
      · have hbal_f : checkAllBalancedCsr M (deltaWhp n_max) N fbMem b₀ = false :=
          Bool.eq_false_iff.mpr hbal0
        simp only [hbal_f, Bool.false_and, Bool.false_eq_true, ↓reduceIte, zero_ne_one,
          clientResult_pure_whp]
    have hvp1 : ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold chkBalStepProg
      simp only [pure_bind]
      refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
      rw [clientState_readPackedGen]
      refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
      rw [clientState_readPackedGen]
      split_ifs <;> exact validProg_pure _
    obtain ⟨hsafe_r, hst_r, hres_r, hvp_r⟩ := ih (b₀ + 1) ok1 (by omega) rfl
    have hadd : b₀ + 1 + rem = b₀ + (rem + 1) := by omega
    unfold chkBalLoopProg at hst_r hres_r hvp_r ⊢
    dsimp only [iterate]
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, ?_⟩
    · rw [clientState_width, clientResult_width, hs1, hr1]; exact hsafe_r
    · rw [clientState_bind, hs1, hr1]; exact hst_r
    · rw [clientResult_bind, hs1, hr1, hres_r, hadd]
    · refine validProg_bind hvp1 ?_; rw [hs1, hr1]; exact hvp_r

/-! ### Part 3b: Pairwise-distinct `rKeyAt` check (`checkPairwiseDistinctOn rKeyAt N`) -/

/-- Compute `rKeyAt i` on raw CSR memory (`d = ((crt, hrt), i)` with `i < ckNMax crt`). -/
@[irreducible] private def csrRKeyAtProg : (ChkRt × HashRt) × ℕ → Memory.Prog ℕ
  | ((crt, hrt), i_in) => do
    let i ← pure i_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let sb ← scanBucketLoopProg
      (((((ckBase crt, ckOffFb crt), (ckGBits crt, ckW crt)), (one_v, i)), (zero_v, zero_v)),
       ckM crt)
    let q ← readPackedGenProg (((ckBase crt, ckOffQ crt), (ckQBits crt, ckW crt)), i)
    rKeyOfQuotRtProg ((hrt, sb.2), q)

private theorem memoryCost_csrRKeyAt_pos (d : (ChkRt × HashRt) × ℕ) (s : Memory.State) :
    0 < memoryCost (csrRKeyAtProg d) s := by
  rcases d with ⟨⟨crt, hrt⟩, i⟩
  unfold csrRKeyAtProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readPackedGen]
  omega

private def CsrRKeyAtPre (w : ℕ) (d : (ChkRt × HashRt) × ℕ) (s : Memory.State) : Prop :=
  ChkHashEnv w d.1.1 d.1.2 s ∧ d.2 < ckNMax d.1.1

private theorem realizes_csrRKeyAt :
    Realizes .exact csrRKeyAtProg
      (WordEncoding.encode (α := (ChkRt × HashRt) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CsrRKeyAtPre
      (fun _ _ => 0) := by
  unfold csrRKeyAtProg
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize [realizes_scanBucketLoop, realizes_readPackedGen, realizes_rKeyOfQuotRt]
  all_goals (
    rcases d with ⟨⟨crt, hrt⟩, i⟩
    dsimp only [CsrRKeyAtPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, θ, henv, heq_crt, heq_hrt, hseed⟩, hi_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize ckBase crt = base at henv heq_crt heq_hrt hseed
    subst heq_crt; subst heq_hrt
    obtain ⟨hsb_sf, hsb_st, _, _⟩ :=
      scanBucketLoop_invariant (target := i) henv (Or.inl ⟨rfl, rfl⟩) (s := s)
    dsimp only [mkChkRt, ckBase, ckW, ckNMax, ckM, ckGBits, ckQBits, ckOffFb, ckOffQ] at hi_lt ⊢
    simp only [hsb_st, hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact hsb_sf
    | exact chk_quot_safe henv hi_lt
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed,
        readPacked_lt (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem i⟩
  )

private theorem csrRKeyAtProg_spec {c U V w n_max base i : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hi : i < n_max) :
    let crt := mkChkRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    let fbMem := fun b => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w
      s.mem b
    let qMem := fun idx => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w
      s.mem idx
    let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
      (csrBucketOfIdx fbMem i (numBucketsWhp n_max)) (qMem i)
    let prog := csrRKeyAtProg ((crt, hrt), i)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if h : kv < U then fpReducedKey c U n_max θ.2 ⟨kv, h⟩ else 0) ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hw := henv.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).1
  have hq_b : base + offQuotWhp c w n_max +
      packedWords n_max (quotBitsWhp U n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  obtain ⟨_, hsb_st, hsb_res, hsb_vp⟩ :=
    scanBucketLoop_invariant (target := i) henv (Or.inl ⟨rfl, rfl⟩) (s := s)
  simp only [Nat.one_mul] at hsb_res
  set fbMem := fun b => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem b
  set qMem := fun idx => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem idx
  obtain ⟨hrk_st, hrk_res, _, hrk_vp⟩ := rKeyOfQuotRtProg_spec
    (b := csrBucketOfIdx fbMem i (numBucketsWhp n_max)) (q := qMem i) henv hseed (s := s)
  dsimp only
  unfold csrRKeyAtProg
  dsimp only [mkChkRt, ckBase, ckW, ckM, ckGBits, ckQBits, ckOffFb, ckOffQ]
  simp only [pure_bind]
  refine ⟨?_, ?_, ?_⟩
  · rw [clientState_bind, hsb_st, hsb_res, clientState_bind, clientState_readPackedGen,
      clientResult_readPackedGen]; exact hrk_st
  · rw [clientResult_bind, hsb_st, hsb_res, clientResult_bind, clientState_readPackedGen,
      clientResult_readPackedGen]; exact hrk_res
  · refine validProg_bind hsb_vp ?_; rw [hsb_st, hsb_res]
    refine validProg_bind (validProg_readPacked hw hi hq_b) ?_
    rw [clientState_readPackedGen, clientResult_readPackedGen]; exact hrk_vp

/-- Inner step of `checkNoEqBefore rKeyAt target` (`d = (((crt, hrt), target), (j, ok))`). -/
@[irreducible] private def chkRKeyInnerStepProg :
    ((ChkRt × HashRt) × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((crt, hrt), target_in), (j_in, ok_in)) => do
    let target ← pure target_in
    let j ← pure j_in
    let ok ← pure ok_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let rkj ← csrRKeyAtProg ((crt, hrt), j)
    let j1 ← pure (j + one_v)
    if ok = one_v then
      if rkj = target then pure (j1, zero_v) else pure (j1, one_v)
    else
      pure (j1, zero_v)

private theorem memoryCost_chkRKeyInnerStep_pos
    (d : ((ChkRt × HashRt) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    0 < memoryCost (chkRKeyInnerStepProg d) s := by
  rcases d with ⟨⟨⟨crt, hrt⟩, target⟩, j, ok⟩
  unfold chkRKeyInnerStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  have hpos := memoryCost_csrRKeyAt_pos ((crt, hrt), j) s
  omega

private def ChkRKeyInnerStepPre (w : ℕ)
    (d : ((ChkRt × HashRt) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  ChkHashEnv w d.1.1.1 d.1.1.2 s ∧ d.2.1 < ckNMax d.1.1.1

private theorem realizes_chkRKeyInnerStep :
    Realizes .exact chkRKeyInnerStepProg
      (WordEncoding.encode (α := ((ChkRt × HashRt) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      ChkRKeyInnerStepPre
      (fun _ _ => 0) := by
  unfold chkRKeyInnerStepProg
  realize [realizes_csrRKeyAt]
  all_goals (
    rcases d with ⟨⟨⟨crt, hrt⟩, target⟩, j, ok⟩
    dsimp only [ChkRKeyInnerStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, θ, henv, heq_crt, heq_hrt, hseed⟩, hj_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize ckBase crt = base at henv heq_crt heq_hrt hseed
    subst heq_crt; subst heq_hrt
    obtain ⟨hrk_st, _, _⟩ := csrRKeyAtProg_spec henv hseed hj_lt (s := s)
    dsimp only [mkChkRt, ckNMax] at hj_lt ⊢
    simp only [hrk_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨⟨c, U, V, w, n_max, θ, henv, rfl, rfl, hseed⟩, hj_lt⟩
  )

@[irreducible] private def chkRKeyInnerLoopProg :
    (((ChkRt × HashRt) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cfg, acc), rem) => iterate chkRKeyInnerStepProg cfg rem acc

private theorem realizes_chkRKeyInnerLoop :
    Realizes .exact chkRKeyInnerLoopProg
      (WordEncoding.encode (α := (((ChkRt × HashRt) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cfg, acc), rem) s =>
        iterationSafe chkRKeyInnerStepProg ChkRKeyInnerStepPre w cfg rem acc s)
      (fun _ _ => 0) := by
  unfold chkRKeyInnerLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := (ChkRt × HashRt) × ℕ))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_chkRKeyInnerStep
    memoryCost_chkRKeyInnerStep_pos

private theorem chkRKeyInnerLoop_spec {c U V w n_max base target : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let crt := mkChkRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    let fbMem := fun b => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w
      s.mem b
    let qMem := fun idx => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w
      s.mem idx
    let rKeyMem : ℕ → ℕ := fun idx =>
      let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
        (csrBucketOfIdx fbMem idx (numBucketsWhp n_max)) (qMem idx)
      if h : kv < U then fpReducedKey c U n_max θ.2 ⟨kv, h⟩ else 0
    ∀ rem j₀ ok₀,
      j₀ + rem ≤ n_max →
      (ok₀ = if checkNoEqBefore rKeyMem target j₀ then 1 else 0) →
      let prog := chkRKeyInnerLoopProg ((((crt, hrt), target), (j₀, ok₀)), rem)
      iterationSafe chkRKeyInnerStepProg ChkRKeyInnerStepPre w ((crt, hrt), target) rem (j₀, ok₀)
        s ∧
      (Memory.spec 0).clientState s prog = s ∧
      (Memory.spec 0).clientResult s prog =
        (j₀ + rem, if checkNoEqBefore rKeyMem target (j₀ + rem) then 1 else 0) ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro crt hrt fbMem qMem rKeyMem rem
  induction rem with
  | zero =>
    intro j₀ ok₀ _ hok
    unfold chkRKeyInnerLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨trivial, rfl, Prod.ext rfl hok, validProg_pure _⟩
  | succ rem ih =>
    intro j₀ ok₀ hle hok
    have hj_lt : j₀ < n_max := by omega
    have hpre : ChkRKeyInnerStepPre w (((crt, hrt), target), (j₀, ok₀)) s :=
      ⟨⟨c, U, V, w, n_max, θ, henv, rfl, rfl, hseed⟩, hj_lt⟩
    obtain ⟨hrk_st, hrk_res, hrk_vp⟩ := csrRKeyAtProg_spec henv hseed hj_lt (s := s)
    set p1 := chkRKeyInnerStepProg (((crt, hrt), target), (j₀, ok₀))
    have hs1 : (Memory.spec 0).clientState s p1 = s := by
      dsimp only [p1]; unfold chkRKeyInnerStepProg
      simp only [pure_bind]
      rw [clientState_bind]; dsimp only [crt, hrt]; rw [hrk_st]
      split_ifs <;> rfl
    set ok1 := if checkNoEqBefore rKeyMem target (j₀ + 1) then 1 else 0
    have hr1 : (Memory.spec 0).clientResult s p1 = (j₀ + 1, ok1) := by
      dsimp only [p1]; unfold chkRKeyInnerStepProg
      simp only [pure_bind]
      rw [clientResult_bind]; dsimp only [crt, hrt]
      have hrk_res' : (Memory.spec 0).clientResult s
          (csrRKeyAtProg ((mkChkRt c U V w n_max base, mkHashRt c U w n_max base), j₀)) =
          rKeyMem j₀ := hrk_res
      rw [hrk_st, hrk_res']
      dsimp only [ok1, checkNoEqBefore]
      rw [hok]
      by_cases hc0 : checkNoEqBefore rKeyMem target j₀ = true
      · by_cases heq : rKeyMem j₀ = target <;> simp [hc0, heq]
      · have hcf : checkNoEqBefore rKeyMem target j₀ = false := Bool.eq_false_iff.mpr hc0
        simp [hcf]
    have hvp1 : ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold chkRKeyInnerStepProg; simp only [pure_bind]
      dsimp only [crt, hrt]
      refine validProg_bind hrk_vp ?_; rw [hrk_st]
      split_ifs <;> exact validProg_pure _
    obtain ⟨hsafe_r, hst_r, hres_r, hvp_r⟩ := ih (j₀ + 1) ok1 (by omega) rfl
    have hadd : j₀ + 1 + rem = j₀ + (rem + 1) := by omega
    unfold chkRKeyInnerLoopProg at hst_r hres_r hvp_r ⊢
    dsimp only [iterate]
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, ?_⟩
    · rw [clientState_width, clientResult_width, hs1, hr1]; exact hsafe_r
    · rw [clientState_bind, hs1, hr1]; exact hst_r
    · rw [clientResult_bind, hs1, hr1, hres_r, hadd]
    · refine validProg_bind hvp1 ?_; rw [hs1, hr1]; exact hvp_r

/-- Outer step of `checkPairwiseDistinctOn rKeyAt N` (`d = ((crt, hrt), (i, ok))`). -/
@[irreducible] private def chkRKeyOuterStepProg :
    (ChkRt × HashRt) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (ch, (i_in, ok_in)) => do
    let i ← pure i_in
    let ok ← pure ok_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let rki ← csrRKeyAtProg (ch, i)
    let inn ← chkRKeyInnerLoopProg (((ch, rki), (zero_v, one_v)), i)
    let i1 ← pure (i + one_v)
    if ok = one_v then pure (i1, inn.2) else pure (i1, zero_v)

private theorem memoryCost_chkRKeyOuterStep_pos
    (d : (ChkRt × HashRt) × (ℕ × ℕ)) (s : Memory.State) :
    0 < memoryCost (chkRKeyOuterStepProg d) s := by
  rcases d with ⟨ch, i, ok⟩
  unfold chkRKeyOuterStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  have hpos := memoryCost_csrRKeyAt_pos (ch, i) s
  omega

private def ChkRKeyOuterStepPre (w : ℕ)
    (d : (ChkRt × HashRt) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  ChkHashEnv w d.1.1 d.1.2 s ∧ d.2.1 < ckNMax d.1.1

private theorem realizes_chkRKeyOuterStep :
    Realizes .exact chkRKeyOuterStepProg
      (WordEncoding.encode (α := (ChkRt × HashRt) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      ChkRKeyOuterStepPre
      (fun _ _ => 0) := by
  unfold chkRKeyOuterStepProg
  realize [realizes_csrRKeyAt, realizes_chkRKeyInnerLoop]
  all_goals (
    rcases d with ⟨⟨crt, hrt⟩, i, ok⟩
    dsimp only [ChkRKeyOuterStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, θ, henv, heq_crt, heq_hrt, hseed⟩, hi_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize ckBase crt = base at henv heq_crt heq_hrt hseed
    subst heq_crt; subst heq_hrt
    dsimp only [mkChkRt, ckNMax] at *
    obtain ⟨hrk_st, _, _⟩ := csrRKeyAtProg_spec henv hseed hi_lt (s := s)
    obtain ⟨hin_sf, hin_st, _, _⟩ := chkRKeyInnerLoop_spec
      (target := (Memory.spec 0).clientResult s
        (csrRKeyAtProg ((mkChkRt c U V w n_max base, mkHashRt c U w n_max base), i)))
      henv hseed i 0 1 (by omega) rfl (s := s)
    have hrt_eta :
        (((mkHashRt c U w n_max base).1.1, (mkHashRt c U w n_max base).1.2),
         ((mkHashRt c U w n_max base).2.1.1, (mkHashRt c U w n_max base).2.1.2),
         ((mkHashRt c U w n_max base).2.2.1.1, (mkHashRt c U w n_max base).2.2.1.2),
         (mkHashRt c U w n_max base).2.2.2.1, (mkHashRt c U w n_max base).2.2.2.2) =
        mkHashRt c U w n_max base := rfl
    dsimp only [mkChkRt] at hrk_st hin_sf hin_st
    simp only [hrt_eta, hrk_st, hin_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨⟨c, U, V, w, n_max, θ, henv, rfl, rfl, hseed⟩, hi_lt⟩
    | exact hin_sf
  )

@[irreducible] private def chkRKeyOuterLoopProg :
    ((ChkRt × HashRt) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((ch, acc), rem) => iterate chkRKeyOuterStepProg ch rem acc

private theorem realizes_chkRKeyOuterLoop :
    Realizes .exact chkRKeyOuterLoopProg
      (WordEncoding.encode (α := ((ChkRt × HashRt) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((ch, acc), rem) s =>
        iterationSafe chkRKeyOuterStepProg ChkRKeyOuterStepPre w ch rem acc s)
      (fun _ _ => 0) := by
  unfold chkRKeyOuterLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := ChkRt × HashRt))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_chkRKeyOuterStep
    memoryCost_chkRKeyOuterStep_pos

private theorem chkRKeyOuterLoop_spec {c U V w n_max base : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let crt := mkChkRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    let fbMem := fun b => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w
      s.mem b
    let qMem := fun idx => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w
      s.mem idx
    let rKeyMem : ℕ → ℕ := fun idx =>
      let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
        (csrBucketOfIdx fbMem idx (numBucketsWhp n_max)) (qMem idx)
      if h : kv < U then fpReducedKey c U n_max θ.2 ⟨kv, h⟩ else 0
    ∀ rem i₀ ok₀,
      i₀ + rem ≤ n_max →
      (ok₀ = if checkPairwiseDistinctOn rKeyMem i₀ then 1 else 0) →
      let prog := chkRKeyOuterLoopProg (((crt, hrt), (i₀, ok₀)), rem)
      iterationSafe chkRKeyOuterStepProg ChkRKeyOuterStepPre w (crt, hrt) rem (i₀, ok₀) s ∧
      (Memory.spec 0).clientState s prog = s ∧
      (Memory.spec 0).clientResult s prog =
        (i₀ + rem, if checkPairwiseDistinctOn rKeyMem (i₀ + rem) then 1 else 0) ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro crt hrt fbMem qMem rKeyMem rem
  induction rem with
  | zero =>
    intro i₀ ok₀ _ hok
    unfold chkRKeyOuterLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨trivial, rfl, Prod.ext rfl hok, validProg_pure _⟩
  | succ rem ih =>
    intro i₀ ok₀ hle hok
    have hi_lt : i₀ < n_max := by omega
    have hpre : ChkRKeyOuterStepPre w ((crt, hrt), (i₀, ok₀)) s :=
      ⟨⟨c, U, V, w, n_max, θ, henv, rfl, rfl, hseed⟩, hi_lt⟩
    obtain ⟨hrk_st, hrk_res, hrk_vp⟩ := csrRKeyAtProg_spec henv hseed hi_lt (s := s)
    obtain ⟨_, hin_st, hin_res, hin_vp⟩ :=
      chkRKeyInnerLoop_spec (target := rKeyMem i₀) henv hseed i₀ 0 1 (by omega) rfl (s := s)
    rw [Nat.zero_add] at hin_res
    set p1 := chkRKeyOuterStepProg ((crt, hrt), (i₀, ok₀))
    have hrk_res' : (Memory.spec 0).clientResult s
        (csrRKeyAtProg ((mkChkRt c U V w n_max base, mkHashRt c U w n_max base), i₀)) =
        rKeyMem i₀ := hrk_res
    have hin_res' : (Memory.spec 0).clientResult s
        (chkRKeyInnerLoopProg
          ((((mkChkRt c U V w n_max base, mkHashRt c U w n_max base), rKeyMem i₀), (0, 1)), i₀)) =
        (i₀, if checkNoEqBefore rKeyMem (rKeyMem i₀) i₀ then 1 else 0) := hin_res
    have hs1 : (Memory.spec 0).clientState s p1 = s := by
      dsimp only [p1]; unfold chkRKeyOuterStepProg
      simp only [pure_bind]
      rw [clientState_bind]; dsimp only [crt, hrt]; rw [hrk_st, hrk_res', clientState_bind,
        hin_st]
      split_ifs <;> rfl
    set ok1 := if checkPairwiseDistinctOn rKeyMem (i₀ + 1) then 1 else 0
    have hr1 : (Memory.spec 0).clientResult s p1 = (i₀ + 1, ok1) := by
      dsimp only [p1]; unfold chkRKeyOuterStepProg
      simp only [pure_bind]
      rw [clientResult_bind]; dsimp only [crt, hrt]
      rw [hrk_st, hrk_res', clientResult_bind, hin_st, hin_res']
      dsimp only [ok1, checkPairwiseDistinctOn]
      rw [hok]
      by_cases hc1 : checkPairwiseDistinctOn rKeyMem i₀ = true <;>
        by_cases hc2 : checkNoEqBefore rKeyMem (rKeyMem i₀) i₀ = true
      · simp [hc1, hc2]
      · simp [hc1, Bool.eq_false_iff.mpr hc2]
      · simp [Bool.eq_false_iff.mpr hc1]
      · simp [Bool.eq_false_iff.mpr hc1]
    have hvp1 : ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold chkRKeyOuterStepProg; simp only [pure_bind]
      dsimp only [crt, hrt]
      refine validProg_bind hrk_vp ?_; rw [hrk_st, hrk_res']
      refine validProg_bind hin_vp ?_; rw [hin_st]
      split_ifs <;> exact validProg_pure _
    obtain ⟨hsafe_r, hst_r, hres_r, hvp_r⟩ := ih (i₀ + 1) ok1 (by omega) rfl
    have hadd : i₀ + 1 + rem = i₀ + (rem + 1) := by omega
    unfold chkRKeyOuterLoopProg at hst_r hres_r hvp_r ⊢
    dsimp only [iterate]
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, ?_⟩
    · rw [clientState_width, clientResult_width, hs1, hr1]; exact hsafe_r
    · rw [clientState_bind, hs1, hr1]; exact hst_r
    · rw [clientResult_bind, hs1, hr1, hres_r, hadd]
    · refine validProg_bind hvp1 ?_; rw [hs1, hr1]; exact hvp_r

/-! ### Part 3c: Per-bucket collision-free salt discovery (`findSaltInRange` into `offBktMeta`) -/

/-- Compute `fpAt salt idx` on raw CSR memory (`d = (((crt, hrt), salt), idx)`). -/
@[irreducible] private def csrFpAtProg : ((ChkRt × HashRt) × ℕ) × ℕ → Memory.Prog ℕ
  | (((crt, hrt), salt_in), idx_in) => do
    let salt ← pure salt_in
    let idx ← pure idx_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let sb ← scanBucketLoopProg
      (((((ckBase crt, ckOffFb crt), (ckGBits crt, ckW crt)), (one_v, idx)), (zero_v, zero_v)),
       ckM crt)
    let q ← readPackedGenProg (((ckBase crt, ckOffQ crt), (ckQBits crt, ckW crt)), idx)
    fpOfQuotRtProg (((hrt, salt), sb.2), q)

private theorem memoryCost_csrFpAt_pos (d : ((ChkRt × HashRt) × ℕ) × ℕ) (s : Memory.State) :
    0 < memoryCost (csrFpAtProg d) s := by
  rcases d with ⟨⟨ch, salt⟩, idx⟩
  unfold csrFpAtProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_readPackedGen]
  omega

private def CsrFpAtPre (w : ℕ) (d : ((ChkRt × HashRt) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  ChkHashEnv w d.1.1.1 d.1.1.2 s ∧ d.2 < ckNMax d.1.1.1

private theorem realizes_csrFpAt :
    Realizes .exact csrFpAtProg
      (WordEncoding.encode (α := ((ChkRt × HashRt) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CsrFpAtPre
      (fun _ _ => 0) := by
  unfold csrFpAtProg
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize [realizes_scanBucketLoop, realizes_readPackedGen, realizes_fpOfQuotRt]
  all_goals (
    rcases d with ⟨⟨⟨crt, hrt⟩, salt⟩, idx⟩
    dsimp only [CsrFpAtPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, θ, henv, heq_crt, heq_hrt, hseed⟩, hidx_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize ckBase crt = base at henv heq_crt heq_hrt hseed
    subst heq_crt; subst heq_hrt
    obtain ⟨hsb_sf, hsb_st, _, _⟩ :=
      scanBucketLoop_invariant (target := idx) henv (Or.inl ⟨rfl, rfl⟩) (s := s)
    dsimp only [mkChkRt, ckBase, ckW, ckNMax, ckM, ckGBits, ckQBits, ckOffFb, ckOffQ] at hidx_lt ⊢
    simp only [hsb_st, hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact hsb_sf
    | exact chk_quot_safe henv hidx_lt
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed,
        readPacked_lt (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem idx⟩
  )

private theorem csrFpAtProg_spec {c U V w n_max base salt idx : ℕ} {θ : SeedWhp c U n_max}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hidx : idx < n_max) :
    let crt := mkChkRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    let fbMem := fun b => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w
      s.mem b
    let qMem := fun k => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem k
    let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
      (csrBucketOfIdx fbMem idx (numBucketsWhp n_max)) (qMem idx)
    let prog := csrFpAtProg (((crt, hrt), salt), idx)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if hs : salt < sMaxWhp c n_max then
        if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
       else 0) ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hw := henv.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).1
  have hq_b : base + offQuotWhp c w n_max +
      packedWords n_max (quotBitsWhp U n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  obtain ⟨_, hsb_st, hsb_res, hsb_vp⟩ :=
    scanBucketLoop_invariant (target := idx) henv (Or.inl ⟨rfl, rfl⟩) (s := s)
  simp only [Nat.one_mul] at hsb_res
  set fbMem := fun b => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem b
  set qMem := fun k => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem k
  obtain ⟨hfp_st, hfp_res, _, hfp_vp⟩ := fpOfQuotRtProg_spec (salt := salt)
    (b := csrBucketOfIdx fbMem idx (numBucketsWhp n_max)) (q := qMem idx) henv hseed (s := s)
  dsimp only
  unfold csrFpAtProg
  dsimp only [mkChkRt, ckBase, ckW, ckM, ckGBits, ckQBits, ckOffFb, ckOffQ]
  simp only [pure_bind]
  refine ⟨?_, ?_, ?_⟩
  · rw [clientState_bind, hsb_st, hsb_res, clientState_bind, clientState_readPackedGen,
      clientResult_readPackedGen]; exact hfp_st
  · rw [clientResult_bind, hsb_st, hsb_res, clientResult_bind, clientState_readPackedGen,
      clientResult_readPackedGen]; exact hfp_res
  · refine validProg_bind hsb_vp ?_; rw [hsb_st, hsb_res]
    refine validProg_bind (validProg_readPacked hw hidx hq_b) ?_
    rw [clientState_readPackedGen, clientResult_readPackedGen]; exact hfp_vp

/-- Inner step of `checkNoEqBefore (fun t => fpAt salt (lo + t)) target`
(`d = (((((crt, hrt), salt), lo), target), (j, ok))`). -/
@[irreducible] private def chkFpInnerStepProg :
    ((((ChkRt × HashRt) × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((((cs, lo_in), target_in)), (j_in, ok_in)) => do
    let lo ← pure lo_in
    let target ← pure target_in
    let j ← pure j_in
    let ok ← pure ok_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let idx ← pure (lo + j)
    let fpj ← csrFpAtProg (cs, idx)
    let j1 ← pure (j + one_v)
    if ok = one_v then
      if fpj = target then pure (j1, zero_v) else pure (j1, one_v)
    else
      pure (j1, zero_v)

private theorem memoryCost_chkFpInnerStep_pos
    (d : ((((ChkRt × HashRt) × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    0 < memoryCost (chkFpInnerStepProg d) s := by
  rcases d with ⟨⟨⟨cs, lo⟩, target⟩, j, ok⟩
  unfold chkFpInnerStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  have hpos := memoryCost_csrFpAt_pos (cs, lo + j) s
  omega

private def ChkFpInnerStepPre (w : ℕ)
    (d : ((((ChkRt × HashRt) × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  ChkHashEnv w d.1.1.1.1.1 d.1.1.1.1.2 s ∧ d.1.1.2 + d.2.1 < ckNMax d.1.1.1.1.1

private theorem realizes_chkFpInnerStep :
    Realizes .exact chkFpInnerStepProg
      (WordEncoding.encode (α := ((((ChkRt × HashRt) × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      ChkFpInnerStepPre
      (fun _ _ => 0) := by
  unfold chkFpInnerStepProg
  realize [realizes_csrFpAt]
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨crt, hrt⟩, salt⟩, lo⟩, target⟩, j, ok⟩
    dsimp only [ChkFpInnerStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, θ, henv, heq_crt, heq_hrt, hseed⟩, hidx_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize ckBase crt = base at henv heq_crt heq_hrt hseed
    subst heq_crt; subst heq_hrt
    obtain ⟨hfp_st, _, _⟩ := csrFpAtProg_spec (salt := salt) henv hseed hidx_lt (s := s)
    dsimp only [mkChkRt, ckNMax] at hidx_lt ⊢
    simp only [hfp_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨⟨c, U, V, w, n_max, θ, henv, rfl, rfl, hseed⟩, hidx_lt⟩
  )

@[irreducible] private def chkFpInnerLoopProg :
    (((((ChkRt × HashRt) × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cfg, acc), rem) => iterate chkFpInnerStepProg cfg rem acc

private theorem realizes_chkFpInnerLoop :
    Realizes .exact chkFpInnerLoopProg
      (WordEncoding.encode (α := (((((ChkRt × HashRt) × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cfg, acc), rem) s =>
        iterationSafe chkFpInnerStepProg ChkFpInnerStepPre w cfg rem acc s)
      (fun _ _ => 0) := by
  unfold chkFpInnerLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := (((ChkRt × HashRt) × ℕ) × ℕ) × ℕ))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_chkFpInnerStep
    memoryCost_chkFpInnerStep_pos

private theorem chkFpInnerLoop_spec {c U V w n_max base salt lo target : ℕ}
    {θ : SeedWhp c U n_max} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let crt := mkChkRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    let fbMem := fun b => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w
      s.mem b
    let qMem := fun k => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem k
    let fpSub : ℕ → ℕ := fun t =>
      let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
        (csrBucketOfIdx fbMem (lo + t) (numBucketsWhp n_max)) (qMem (lo + t))
      if hs : salt < sMaxWhp c n_max then
        if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
      else 0
    ∀ rem j₀ ok₀,
      lo + j₀ + rem ≤ n_max →
      (ok₀ = if checkNoEqBefore fpSub target j₀ then 1 else 0) →
      let prog := chkFpInnerLoopProg ((((((crt, hrt), salt), lo), target), (j₀, ok₀)), rem)
      iterationSafe chkFpInnerStepProg ChkFpInnerStepPre w
        ((((crt, hrt), salt), lo), target) rem (j₀, ok₀) s ∧
      (Memory.spec 0).clientState s prog = s ∧
      (Memory.spec 0).clientResult s prog =
        (j₀ + rem, if checkNoEqBefore fpSub target (j₀ + rem) then 1 else 0) ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro crt hrt fbMem qMem fpSub rem
  induction rem with
  | zero =>
    intro j₀ ok₀ _ hok
    unfold chkFpInnerLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨trivial, rfl, Prod.ext rfl hok, validProg_pure _⟩
  | succ rem ih =>
    intro j₀ ok₀ hle hok
    have hidx_lt : lo + j₀ < n_max := by omega
    have hpre : ChkFpInnerStepPre w ((((((crt, hrt), salt), lo), target), (j₀, ok₀))) s :=
      ⟨⟨c, U, V, w, n_max, θ, henv, rfl, rfl, hseed⟩, hidx_lt⟩
    obtain ⟨hfp_st, hfp_res, hfp_vp⟩ := csrFpAtProg_spec (salt := salt) henv hseed hidx_lt (s := s)
    set p1 := chkFpInnerStepProg ((((((crt, hrt), salt), lo), target), (j₀, ok₀)))
    have hfp_res' : (Memory.spec 0).clientResult s
        (csrFpAtProg (((mkChkRt c U V w n_max base, mkHashRt c U w n_max base), salt), lo + j₀)) =
        fpSub j₀ := hfp_res
    have hs1 : (Memory.spec 0).clientState s p1 = s := by
      dsimp only [p1]; unfold chkFpInnerStepProg
      simp only [pure_bind]
      rw [clientState_bind]; dsimp only [crt, hrt]; rw [hfp_st]
      split_ifs <;> rfl
    set ok1 := if checkNoEqBefore fpSub target (j₀ + 1) then 1 else 0
    have hr1 : (Memory.spec 0).clientResult s p1 = (j₀ + 1, ok1) := by
      dsimp only [p1]; unfold chkFpInnerStepProg
      simp only [pure_bind]
      rw [clientResult_bind]; dsimp only [crt, hrt]; rw [hfp_st, hfp_res']
      dsimp only [ok1, checkNoEqBefore]
      rw [hok]
      by_cases hc0 : checkNoEqBefore fpSub target j₀ = true
      · by_cases heq : fpSub j₀ = target <;> simp [hc0, heq]
      · simp [Bool.eq_false_iff.mpr hc0]
    have hvp1 : ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold chkFpInnerStepProg; simp only [pure_bind]
      dsimp only [crt, hrt]
      refine validProg_bind hfp_vp ?_; rw [hfp_st]
      split_ifs <;> exact validProg_pure _
    obtain ⟨hsafe_r, hst_r, hres_r, hvp_r⟩ := ih (j₀ + 1) ok1 (by omega) rfl
    have hadd : j₀ + 1 + rem = j₀ + (rem + 1) := by omega
    unfold chkFpInnerLoopProg at hst_r hres_r hvp_r ⊢
    dsimp only [iterate]
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, ?_⟩
    · rw [clientState_width, clientResult_width, hs1, hr1]; exact hsafe_r
    · rw [clientState_bind, hs1, hr1]; exact hst_r
    · rw [clientResult_bind, hs1, hr1, hres_r, hadd]
    · refine validProg_bind hvp1 ?_; rw [hs1, hr1]; exact hvp_r

/-- Outer step of `checkPairwiseDistinctOn (fun t => fpAt salt (lo + t)) len`
(`d = ((((crt, hrt), salt), lo), (t, ok))`). -/
@[irreducible] private def chkFpOuterStepProg :
    (((ChkRt × HashRt) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((cs, lo_in), (t_in, ok_in)) => do
    let lo ← pure lo_in
    let t ← pure t_in
    let ok ← pure ok_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let idx ← pure (lo + t)
    let fpt ← csrFpAtProg (cs, idx)
    let inn ← chkFpInnerLoopProg (((((cs, lo), fpt), (zero_v, one_v)), t))
    let t1 ← pure (t + one_v)
    if ok = one_v then pure (t1, inn.2) else pure (t1, zero_v)

private theorem memoryCost_chkFpOuterStep_pos
    (d : (((ChkRt × HashRt) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    0 < memoryCost (chkFpOuterStepProg d) s := by
  rcases d with ⟨⟨cs, lo⟩, t, ok⟩
  unfold chkFpOuterStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  have hpos := memoryCost_csrFpAt_pos (cs, lo + t) s
  omega

private def ChkFpOuterStepPre (w : ℕ)
    (d : (((ChkRt × HashRt) × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  ChkHashEnv w d.1.1.1.1 d.1.1.1.2 s ∧ d.1.2 + d.2.1 < ckNMax d.1.1.1.1

private theorem realizes_chkFpOuterStep :
    Realizes .exact chkFpOuterStepProg
      (WordEncoding.encode (α := (((ChkRt × HashRt) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      ChkFpOuterStepPre
      (fun _ _ => 0) := by
  unfold chkFpOuterStepProg
  realize [realizes_csrFpAt, realizes_chkFpInnerLoop]
  all_goals (
    rcases d with ⟨⟨⟨⟨crt, hrt⟩, salt⟩, lo⟩, t, ok⟩
    dsimp only [ChkFpOuterStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, θ, henv, heq_crt, heq_hrt, hseed⟩, hidx_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize ckBase crt = base at henv heq_crt heq_hrt hseed
    subst heq_crt; subst heq_hrt
    dsimp only [mkChkRt, ckNMax] at *
    obtain ⟨hfp_st, _, _⟩ := csrFpAtProg_spec (salt := salt) henv hseed hidx_lt (s := s)
    obtain ⟨hin_sf, hin_st, _, _⟩ := chkFpInnerLoop_spec (salt := salt) (lo := lo)
      (target := (Memory.spec 0).clientResult s
        (csrFpAtProg (((mkChkRt c U V w n_max base, mkHashRt c U w n_max base), salt), lo + t)))
      henv hseed t 0 1 (by omega) rfl (s := s)
    have hrt_eta :
        (((mkHashRt c U w n_max base).1.1, (mkHashRt c U w n_max base).1.2),
         ((mkHashRt c U w n_max base).2.1.1, (mkHashRt c U w n_max base).2.1.2),
         ((mkHashRt c U w n_max base).2.2.1.1, (mkHashRt c U w n_max base).2.2.1.2),
         (mkHashRt c U w n_max base).2.2.2.1, (mkHashRt c U w n_max base).2.2.2.2) =
        mkHashRt c U w n_max base := rfl
    dsimp only [mkChkRt] at hfp_st hin_sf hin_st
    simp only [hrt_eta, hfp_st, hin_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨⟨c, U, V, w, n_max, θ, henv, rfl, rfl, hseed⟩, hidx_lt⟩
    | exact hin_sf
  )

@[irreducible] private def chkFpOuterLoopProg :
    ((((ChkRt × HashRt) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cfg, acc), rem) => iterate chkFpOuterStepProg cfg rem acc

private theorem realizes_chkFpOuterLoop :
    Realizes .exact chkFpOuterLoopProg
      (WordEncoding.encode (α := ((((ChkRt × HashRt) × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cfg, acc), rem) s =>
        iterationSafe chkFpOuterStepProg ChkFpOuterStepPre w cfg rem acc s)
      (fun _ _ => 0) := by
  unfold chkFpOuterLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := ((ChkRt × HashRt) × ℕ) × ℕ))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_chkFpOuterStep
    memoryCost_chkFpOuterStep_pos

private theorem chkFpOuterLoop_spec {c U V w n_max base salt lo : ℕ}
    {θ : SeedWhp c U n_max} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let crt := mkChkRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    let fbMem := fun b => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w
      s.mem b
    let qMem := fun k => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem k
    let fpSub : ℕ → ℕ := fun t =>
      let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
        (csrBucketOfIdx fbMem (lo + t) (numBucketsWhp n_max)) (qMem (lo + t))
      if hs : salt < sMaxWhp c n_max then
        if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
      else 0
    ∀ rem t₀ ok₀,
      lo + t₀ + rem ≤ n_max →
      (ok₀ = if checkPairwiseDistinctOn fpSub t₀ then 1 else 0) →
      let prog := chkFpOuterLoopProg (((((crt, hrt), salt), lo), (t₀, ok₀)), rem)
      iterationSafe chkFpOuterStepProg ChkFpOuterStepPre w (((crt, hrt), salt), lo) rem
        (t₀, ok₀) s ∧
      (Memory.spec 0).clientState s prog = s ∧
      (Memory.spec 0).clientResult s prog =
        (t₀ + rem, if checkPairwiseDistinctOn fpSub (t₀ + rem) then 1 else 0) ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro crt hrt fbMem qMem fpSub rem
  induction rem with
  | zero =>
    intro t₀ ok₀ _ hok
    unfold chkFpOuterLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨trivial, rfl, Prod.ext rfl hok, validProg_pure _⟩
  | succ rem ih =>
    intro t₀ ok₀ hle hok
    have hidx_lt : lo + t₀ < n_max := by omega
    have hpre : ChkFpOuterStepPre w ((((crt, hrt), salt), lo), (t₀, ok₀)) s :=
      ⟨⟨c, U, V, w, n_max, θ, henv, rfl, rfl, hseed⟩, hidx_lt⟩
    obtain ⟨hfp_st, hfp_res, hfp_vp⟩ := csrFpAtProg_spec (salt := salt) henv hseed hidx_lt (s := s)
    obtain ⟨_, hin_st, hin_res, hin_vp⟩ := chkFpInnerLoop_spec (salt := salt) (lo := lo)
      (target := fpSub t₀) henv hseed t₀ 0 1 (by omega) rfl (s := s)
    rw [Nat.zero_add] at hin_res
    set p1 := chkFpOuterStepProg ((((crt, hrt), salt), lo), (t₀, ok₀))
    have hfp_res' : (Memory.spec 0).clientResult s
        (csrFpAtProg (((mkChkRt c U V w n_max base, mkHashRt c U w n_max base), salt), lo + t₀)) =
        fpSub t₀ := hfp_res
    have hin_res' : (Memory.spec 0).clientResult s
        (chkFpInnerLoopProg
          ((((((mkChkRt c U V w n_max base, mkHashRt c U w n_max base), salt), lo), fpSub t₀),
            (0, 1)), t₀)) =
        (t₀, if checkNoEqBefore fpSub (fpSub t₀) t₀ then 1 else 0) := hin_res
    have hs1 : (Memory.spec 0).clientState s p1 = s := by
      dsimp only [p1]; unfold chkFpOuterStepProg
      simp only [pure_bind]
      rw [clientState_bind]; dsimp only [crt, hrt]; rw [hfp_st, hfp_res', clientState_bind,
        hin_st]
      split_ifs <;> rfl
    set ok1 := if checkPairwiseDistinctOn fpSub (t₀ + 1) then 1 else 0
    have hr1 : (Memory.spec 0).clientResult s p1 = (t₀ + 1, ok1) := by
      dsimp only [p1]; unfold chkFpOuterStepProg
      simp only [pure_bind]
      rw [clientResult_bind]; dsimp only [crt, hrt]
      rw [hfp_st, hfp_res', clientResult_bind, hin_st, hin_res']
      dsimp only [ok1, checkPairwiseDistinctOn]
      rw [hok]
      by_cases hc1 : checkPairwiseDistinctOn fpSub t₀ = true <;>
        by_cases hc2 : checkNoEqBefore fpSub (fpSub t₀) t₀ = true
      · simp [hc1, hc2]
      · simp [hc1, Bool.eq_false_iff.mpr hc2]
      · simp [Bool.eq_false_iff.mpr hc1]
      · simp [Bool.eq_false_iff.mpr hc1]
    have hvp1 : ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold chkFpOuterStepProg; simp only [pure_bind]
      dsimp only [crt, hrt]
      refine validProg_bind hfp_vp ?_; rw [hfp_st, hfp_res']
      refine validProg_bind hin_vp ?_; rw [hin_st]
      split_ifs <;> exact validProg_pure _
    obtain ⟨hsafe_r, hst_r, hres_r, hvp_r⟩ := ih (t₀ + 1) ok1 (by omega) rfl
    have hadd : t₀ + 1 + rem = t₀ + (rem + 1) := by omega
    unfold chkFpOuterLoopProg at hst_r hres_r hvp_r ⊢
    dsimp only [iterate]
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, ?_⟩
    · rw [clientState_width, clientResult_width, hs1, hr1]; exact hsafe_r
    · rw [clientState_bind, hs1, hr1]; exact hst_r
    · rw [clientResult_bind, hs1, hr1, hres_r, hadd]
    · refine validProg_bind hvp1 ?_; rw [hs1, hr1]; exact hvp_r

/-- Step searching candidate salt `salt = 0 .. sMax - 1` (`d = ((ch, (lo, len)), (salt, prev))`). -/
@[irreducible] private def findSaltStepProg :
    ((ChkRt × HashRt) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((ch, (lo_in, len_in)), (salt_in, prev_in)) => do
    let lo ← pure lo_in
    let len ← pure len_in
    let salt ← pure salt_in
    let prev ← pure prev_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let _ ← Memory.read (ckBase ch.1)
    let s1 ← pure (salt + one_v)
    if prev = zero_v then
      let chk ← chkFpOuterLoopProg (((((ch, salt), lo), (zero_v, one_v)), len))
      if chk.2 = one_v then pure (s1, s1) else pure (s1, zero_v)
    else
      pure (s1, prev)

private theorem memoryCost_findSaltStep_pos
    (d : ((ChkRt × HashRt) × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    0 < memoryCost (findSaltStepProg d) s := by
  rcases d with ⟨⟨ch, lo, len⟩, salt, prev⟩
  unfold findSaltStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 1 + _
  omega

private def FindSaltStepPre (w : ℕ)
    (d : ((ChkRt × HashRt) × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  ChkHashEnv w d.1.1.1 d.1.1.2 s ∧
  d.1.2.1 + d.1.2.2 ≤ ckNMax d.1.1.1 ∧
  d.2.1 < ckSMax d.1.1.1

private theorem realizes_findSaltStep :
    Realizes .exact findSaltStepProg
      (WordEncoding.encode (α := ((ChkRt × HashRt) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      FindSaltStepPre
      (fun _ _ => 0) := by
  unfold findSaltStepProg
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  realize [realizes_chkFpOuterLoop]
  all_goals (
    rcases d with ⟨⟨⟨crt, hrt⟩, lo, len⟩, salt, prev⟩
    dsimp only [FindSaltStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, θ, henv, heq_crt, heq_hrt, hseed⟩, hlen_le, hs_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize ckBase crt = base at henv heq_crt heq_hrt hseed
    subst heq_crt; subst heq_hrt
    have hth := henv.2.2.2.1
    have hsMax_lt := (large_bounds_lt_n_max hth).2.2.2.2.1
    dsimp only [mkChkRt, ckBase, ckNMax, ckSMax] at hlen_le hs_lt ⊢
    simp only [hcs_r] at *
    first
    | exact henv.fits_const (by decide)
    | (have := henv.fits_hdr_addr (off := 0) (by decide); simpa using this)
    | exact henv.fits_of_le_n_max (by omega)
    | exact (chkFpOuterLoop_spec (salt := salt) (lo := lo) henv hseed len 0 1 (by omega) rfl).1
  )

@[irreducible] private def findSaltLoopProg :
    (((ChkRt × HashRt) × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cfg, acc), rem) => iterate findSaltStepProg cfg rem acc

private theorem realizes_findSaltLoop :
    Realizes .exact findSaltLoopProg
      (WordEncoding.encode (α := (((ChkRt × HashRt) × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cfg, acc), rem) s =>
        iterationSafe findSaltStepProg FindSaltStepPre w cfg rem acc s)
      (fun _ _ => 0) := by
  unfold findSaltLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := (ChkRt × HashRt) × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_findSaltStep
    memoryCost_findSaltStep_pos

private theorem findSaltLoop_spec {c U V w n_max base lo len : ℕ}
    {θ : SeedWhp c U n_max} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hlen_le : lo + len ≤ n_max) :
    let crt := mkChkRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    let fbMem := fun b => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w
      s.mem b
    let qMem := fun k => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem k
    let fpMem : ℕ → ℕ → ℕ := fun salt idx =>
      let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
        (csrBucketOfIdx fbMem idx (numBucketsWhp n_max)) (qMem idx)
      if hs : salt < sMaxWhp c n_max then
        if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
      else 0
    ∀ rem s₀ prev₀,
      s₀ + rem ≤ sMaxWhp c n_max →
      (prev₀ = findSaltInRange fpMem lo len s₀) →
      let prog := findSaltLoopProg ((((crt, hrt), (lo, len)), (s₀, prev₀)), rem)
      iterationSafe findSaltStepProg FindSaltStepPre w ((crt, hrt), (lo, len)) rem (s₀, prev₀) s ∧
      (Memory.spec 0).clientState s prog = s ∧
      (Memory.spec 0).clientResult s prog =
        (s₀ + rem, findSaltInRange fpMem lo len (s₀ + rem)) ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro crt hrt fbMem qMem fpMem rem
  have hbase_lt : base < base + largeSpaceWhp c U V w n_max := by
    have : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    omega
  induction rem with
  | zero =>
    intro s₀ prev₀ _ hprev
    unfold findSaltLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨trivial, rfl, Prod.ext rfl hprev, validProg_pure _⟩
  | succ rem ih =>
    intro s₀ prev₀ hle hprev
    have hs_lt : s₀ < sMaxWhp c n_max := by omega
    have hpre : FindSaltStepPre w (((crt, hrt), (lo, len)), (s₀, prev₀)) s :=
      ⟨⟨c, U, V, w, n_max, θ, henv, rfl, rfl, hseed⟩, hlen_le, hs_lt⟩
    obtain ⟨_, hfo_st, hfo_res, hfo_vp⟩ := chkFpOuterLoop_spec (salt := s₀) (lo := lo)
      henv hseed len 0 1 (by omega) rfl (s := s)
    rw [Nat.zero_add] at hfo_res
    set p1 := findSaltStepProg (((crt, hrt), (lo, len)), (s₀, prev₀))
    have hs1 : (Memory.spec 0).clientState s p1 = s := by
      dsimp only [p1]; unfold findSaltStepProg
      simp only [pure_bind]
      rw [clientState_bind]
      change (Memory.spec 0).clientState s (if prev₀ = 0 then _ else _) = s
      split_ifs
      · rw [clientState_bind]; dsimp only [crt, hrt]; rw [hfo_st]; split_ifs <;> rfl
      · rfl
    set prev1 := findSaltInRange fpMem lo len (s₀ + 1)
    have hr1 : (Memory.spec 0).clientResult s p1 = (s₀ + 1, prev1) := by
      dsimp only [p1]; unfold findSaltStepProg
      simp only [pure_bind]
      rw [clientResult_bind]
      change (Memory.spec 0).clientResult s (if prev₀ = 0 then _ else _) = _
      dsimp only [prev1, findSaltInRange]
      rw [← hprev]
      by_cases hp0 : prev₀ = 0
      · simp only [hp0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [clientResult_bind]; dsimp only [crt, hrt]
        have hfo_res' : (Memory.spec 0).clientResult s
            (chkFpOuterLoopProg (((((mkChkRt c U V w n_max base, mkHashRt c U w n_max base), s₀),
              lo), (0, 1)), len)) =
            (len, if checkPairwiseDistinctOn (fun t => fpMem s₀ (lo + t)) len then 1 else 0) :=
          hfo_res
        rw [hfo_res']
        by_cases hc : checkPairwiseDistinctOn (fun t => fpMem s₀ (lo + t)) len = true
        · simp [hc]
        · simp [Bool.eq_false_iff.mpr hc]
      · have hp_bne : (prev₀ != 0) = true := bne_iff_ne.mpr hp0
        simp [hp0, hp_bne]
    have hvp1 : ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold findSaltStepProg; simp only [pure_bind]
      refine validProg_bind (validProg_read hbase_lt) ?_
      change ValidProg _ _ s (if prev₀ = 0 then _ else _)
      split_ifs
      · refine validProg_bind hfo_vp ?_; rw [hfo_st]
        split_ifs <;> exact validProg_pure _
      · exact validProg_pure _
    obtain ⟨hsafe_r, hst_r, hres_r, hvp_r⟩ := ih (s₀ + 1) prev1 (by omega) rfl
    have hadd : s₀ + 1 + rem = s₀ + (rem + 1) := by omega
    unfold findSaltLoopProg at hst_r hres_r hvp_r ⊢
    dsimp only [iterate]
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, ?_⟩
    · rw [clientState_width, clientResult_width, hs1, hr1]; exact hsafe_r
    · rw [clientState_bind, hs1, hr1]; exact hst_r
    · rw [clientResult_bind, hs1, hr1, hres_r, hadd]
    · refine validProg_bind hvp1 ?_; rw [hs1, hr1]; exact hvp_r

/-- Compact 8-word helper writing `s1 - 1` into `offBktMeta[16 * b + 1]` and updating `allOk`
(`d = ((((base, offBm), (gBits, w)), (sMax, b)), (allOk, s1))`). Separating this leaf from
51-word `(ChkRt × HashRt) × (ℕ × ℕ)` keeps `realize` width encoding small and fast. -/
@[irreducible] private def writeSaltResultProg :
    (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((((base_in, offBm_in), (gBits_in, w_in)), (sMax_in, b_in)), (ok_in, s1_in)) => do
    let base ← pure base_in
    let offBm ← pure offBm_in
    let gBits ← pure gBits_in
    let w ← pure w_in
    let sMax ← pure sMax_in
    let b ← pure b_in
    let allOk ← pure ok_in
    let s1 ← pure s1_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let b1 ← pure (b + one_v)
    let idxBm ← pure (16 * b + one_v)
    if s1 ≤ sMax then
      if one_v ≤ s1 then
        let sVal ← pure (s1 - one_v)
        writePackedGenProg ((((base, offBm), (gBits, w)), idxBm), sVal)
        if allOk = one_v then pure (b1, one_v) else pure (b1, zero_v)
      else
        writePackedGenProg ((((base, offBm), (gBits, w)), idxBm), zero_v)
        pure (b1, zero_v)
    else
      writePackedGenProg ((((base, offBm), (gBits, w)), idxBm), zero_v)
      pure (b1, zero_v)

private def WriteSaltResultPre (w : ℕ) :
    (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | ((((base, offBm), (gBits, w_in)), (sMax, b)), _), _ =>
    ∃ c U V w₀ n_max,
      WhpLargeEnv c U V w₀ n_max w base ∧
      offBm = offBktMeta c U V w₀ n_max ∧
      gBits = globalPtrBits n_max ∧
      w_in = w₀ ∧
      sMax = sMaxWhp c n_max ∧
      b < numBucketsWhp n_max

private theorem realizes_writeSaltResult :
    Realizes .exact writeSaltResultProg
      (WordEncoding.encode (α := (((ℕ × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      WriteSaltResultPre
      (fun _ _ => 0) := by
  unfold writeSaltResultProg
  realize [realizes_writePackedGen]
  all_goals (
    rcases d with ⟨⟨⟨⟨base, offBm⟩, gBits, w_in⟩, sMax, b⟩, allOk, s1⟩
    dsimp only [WriteSaltResultPre] at h
    obtain ⟨c, U, V, w₀, n_max, henv, rfl, rfl, rfl, rfl, hb_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    have hsMax_lt := (large_bounds_lt_n_max hth).2.2.2.2.1
    dsimp only at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.bktMeta_safe (idx := 16 * b + 1) (by omega)
  )

private theorem writeSaltResultProg_spec {c U V w n_max base b allOk s1 : ℕ}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hs1 : s1 ≤ sMaxWhp c n_max) :
    let prog := writeSaltResultProg
      ((((base, offBktMeta c U V w n_max), (globalPtrBits n_max, w)), (sMaxWhp c n_max, b)),
       (allOk, s1))
    let m' := writePacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
      (16 * b + 1) (s1 - 1)
    (Memory.spec 0).clientState s prog = { mem := m', frontier := s.frontier } ∧
    (Memory.spec 0).clientResult s prog =
      (b + 1, if allOk = 1 ∧ s1 ≠ 0 then 1 else 0) ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hw := henv.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.1
  have hbm_b : base + offBktMeta c U V w n_max +
      packedWords (16 * numBucketsWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  have hidx : 16 * b + 1 < 16 * numBucketsWhp n_max := by omega
  dsimp only
  unfold writeSaltResultProg; dsimp only
  simp only [pure_bind, hs1, ↓reduceIte]
  by_cases h1 : 1 ≤ s1
  · have hne0 : s1 ≠ 0 := by omega
    simp only [h1, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · rw [clientState_bind, clientState_writePackedGen]
      split_ifs <;> rfl
    · rw [clientResult_bind, clientState_writePackedGen]
      by_cases hok : allOk = 1 <;> simp [hok, hne0]
    · refine validProg_bind (validProg_writePacked hw hgk hidx hbm_b) ?_
      split_ifs <;> exact validProg_pure _
  · have hs0 : s1 = 0 := by omega
    subst hs0
    simp only [h1, ne_eq, not_true_eq_false, and_false, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · rw [clientState_bind, clientState_writePackedGen]; rfl
    · rw [clientResult_bind, clientState_writePackedGen]; rfl
    · exact validProg_bind (validProg_writePacked hw hgk hidx hbm_b)
        (validProg_pure _)

/-- Step finding `salt1Of b` for bucket `b` and writing `salt1Of b - 1` into `offBktMeta[16*b + 1]`
(`d = ((crt, hrt), (b, allOk))`). -/
@[irreducible] private def findSaltsBktStepProg :
    (ChkRt × HashRt) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((crt, hrt), (b_in, ok_in)) => do
    let b ← pure b_in
    let allOk ← pure ok_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let b1 ← pure (b + one_v)
    let lo ← readPackedGenProg (((ckBase crt, ckOffFb crt), (ckGBits crt, ckW crt)), b)
    let hi ← readPackedGenProg (((ckBase crt, ckOffFb crt), (ckGBits crt, ckW crt)), b1)
    if lo ≤ hi then
      if hi ≤ ckNMax crt then
        let len ← pure (hi - lo)
        let fsRes ← findSaltLoopProg
          (((((crt, hrt), (lo, len)), (zero_v, zero_v)), ckSMax crt))
        writeSaltResultProg
          ((((ckBase crt, ckOffBm crt), (ckGBits crt, ckW crt)), (ckSMax crt, b)),
           (allOk, fsRes.2))
      else pure (b1, zero_v)
    else pure (b1, zero_v)

private theorem memoryCost_findSaltsBktStep_pos
    (d : (ChkRt × HashRt) × (ℕ × ℕ)) (s : Memory.State) :
    0 < memoryCost (findSaltsBktStepProg d) s := by
  rcases d with ⟨⟨crt, hrt⟩, b, allOk⟩
  unfold findSaltsBktStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

private def FindSaltsBktStepPre (w : ℕ)
    (d : (ChkRt × HashRt) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  ChkHashEnv w d.1.1 d.1.2 s ∧ d.2.1 < ckM d.1.1

private theorem findSaltInRange_le {fpAt : ℕ → ℕ → ℕ} {lo len k : ℕ} :
    findSaltInRange fpAt lo len k ≤ k := by
  induction k with
  | zero => simp [findSaltInRange]
  | succ k ih =>
    dsimp only [findSaltInRange]
    split_ifs <;> omega

private theorem realizes_findSaltsBktStep :
    Realizes .exact findSaltsBktStepProg
      (WordEncoding.encode (α := (ChkRt × HashRt) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      FindSaltsBktStepPre
      (fun _ _ => 0) := by
  unfold findSaltsBktStepProg
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize [realizes_readPackedGen, realizes_findSaltLoop, realizes_writeSaltResult]
  all_goals (
    rcases d with ⟨⟨crt, hrt⟩, b, allOk⟩
    dsimp only [FindSaltsBktStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, θ, henv, heq_crt, heq_hrt, hseed⟩, hb_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize ckBase crt = base at henv heq_crt heq_hrt hseed
    subst heq_crt
    have hth := henv.2.2.2.1
    have hM_le := henv.numBuckets_le_n_max
    have hsMax_lt := (large_bounds_lt_n_max hth).2.2.2.2.1
    dsimp only [mkChkRt, ckBase, ckW, ckNMax, ckM, ckSMax, ckGBits, ckOffFb, ckOffBm] at *
    simp only [hcs, clientResult_readPackedGen] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact chk_fb_safe henv (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl, rfl, rfl, rfl, hb_lt⟩
    | (subst heq_hrt
       set lo := readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem b
       set hi := readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem (b + 1)
       obtain ⟨hfsl_sf, _, _, _⟩ :=
         findSaltLoop_spec (lo := lo) (len := hi - lo) henv hseed (by omega)
           (sMaxWhp c n_max) 0 0 (by omega) rfl (s := s)
       have hrt_eta :
           (((mkHashRt c U w n_max base).1.1, (mkHashRt c U w n_max base).1.2),
            ((mkHashRt c U w n_max base).2.1.1, (mkHashRt c U w n_max base).2.1.2),
            ((mkHashRt c U w n_max base).2.2.1.1, (mkHashRt c U w n_max base).2.2.1.2),
            (mkHashRt c U w n_max base).2.2.2.1, (mkHashRt c U w n_max base).2.2.2.2) =
           mkHashRt c U w n_max base := rfl
       dsimp only [mkChkRt] at hfsl_sf
       simp only [hrt_eta] at *
       exact hfsl_sf)
  )

@[irreducible] private def findSaltsBktLoopProg :
    ((ChkRt × HashRt) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((ch, acc), rem) => iterate findSaltsBktStepProg ch rem acc

private theorem realizes_findSaltsBktLoop :
    Realizes .exact findSaltsBktLoopProg
      (WordEncoding.encode (α := ((ChkRt × HashRt) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((ch, acc), rem) s =>
        iterationSafe findSaltsBktStepProg FindSaltsBktStepPre w ch rem acc s)
      (fun _ _ => 0) := by
  unfold findSaltsBktLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := ChkRt × HashRt))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_findSaltsBktStep
    memoryCost_findSaltsBktStep_pos

private def allSaltsFoundRec (salt1Of : ℕ → ℕ) : ℕ → Bool
  | 0 => true
  | b + 1 => allSaltsFoundRec salt1Of b && (salt1Of b != 0)

private theorem findSaltsBktLoop_spec {c U V w n_max base : ℕ} {θ : SeedWhp c U n_max}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed₀ : SeedWhpMemRep base c U w n_max θ s₀.mem)
    (hfb_adj : ∀ b < numBucketsWhp n_max,
      let fbMem := fun k => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w
        s₀.mem k
      fbMem b ≤ fbMem (b + 1) ∧ fbMem (b + 1) ≤ n_max) :
    let crt := mkChkRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    let M := numBucketsWhp n_max
    let fbMem := fun k => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w
      s₀.mem k
    let qMem := fun k => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s₀.mem k
    let fpMem : ℕ → ℕ → ℕ := fun salt idx =>
      let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
        (csrBucketOfIdx fbMem idx M) (qMem idx)
      if hs : salt < sMaxWhp c n_max then
        if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
      else 0
    let salt1Of : ℕ → ℕ := fun b =>
      findSaltInRange fpMem (fbMem b) (fbMem (b + 1) - fbMem b) (sMaxWhp c n_max)
    ∀ rem b₀ ok₀ (s : Memory.State),
      b₀ + rem ≤ M →
      (∀ a, (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
        s.mem a = s₀.mem a) →
      (∀ b < b₀,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem (16 * b + 1) =
          salt1Of b - 1) →
      (ok₀ = if allSaltsFoundRec salt1Of b₀ then 1 else 0) →
      let prog := findSaltsBktLoopProg (((crt, hrt), (b₀, ok₀)), rem)
      let s' := (Memory.spec 0).clientState s prog
      iterationSafe findSaltsBktStepProg FindSaltsBktStepPre w (crt, hrt) rem (b₀, ok₀) s ∧
      s'.frontier = s.frontier ∧
      (Memory.spec 0).clientResult s prog =
        (b₀ + rem, if allSaltsFoundRec salt1Of (b₀ + rem) then 1 else 0) ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ b < b₀ + rem,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem (16 * b + 1) =
          salt1Of b - 1) ∧
      (∀ a, (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) := by
  intro crt hrt M fbMem qMem fpMem salt1Of rem
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  have hsMax_lt := (large_bounds_lt_n_max hth).2.2.2.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.1 _
  have hbm_end : offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w = offFbStart c U V w n_max := rfl
  have hq_le_bm := offQuot_le_offBktMeta c U V w n_max
  have h32_q : 32 ≤ offQuotWhp c w n_max := by
    change offHashBkt ≤ _; unfold offQuotWhp offHashFp; omega
  have hql_end := hseg.1
  have hl_v : offValWhp c U w n_max =
      offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w := rfl
  have hl_pa : offPermAct c U V w n_max =
      offValWhp c U w n_max + packedWords n_max (valBits V) w := rfl
  have hpa_le_bm : offPermAct c U V w n_max ≤ offBktMeta c U V w n_max := by
    unfold offBktMeta offLocState; omega
  induction rem with
  | zero =>
    intro b₀ ok₀ s _ hout hsalts hok
    unfold findSaltsBktLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨trivial, rfl, Prod.ext rfl hok, validProg_pure _, hsalts, hout⟩
  | succ rem ih =>
    intro b₀ ok₀ s hle hout hsalts hok
    have hb_lt : b₀ < M := by omega
    have hseed_s : SeedWhpMemRep base c U w n_max θ s.mem :=
      SeedWhpMemRep.congr_hash hw (fun a _ ha2 => (hout a (Or.inl (by omega))).symm) hseed₀
    have hpre : FindSaltsBktStepPre w ((crt, hrt), (b₀, ok₀)) s :=
      ⟨⟨c, U, V, w, n_max, θ, henv, rfl, rfl, hseed_s⟩, hb_lt⟩
    have hfb_eq : ∀ k ≤ M,
        readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem k = fbMem k :=
      fun k hk => readPacked_congr hw (fun a ⟨ha1, _⟩ => hout a (Or.inr ha1)) (Nat.lt_succ_of_le hk)
    have hq_eq : ∀ idx < n_max,
        readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem idx = qMem idx :=
      fun idx hidx => readPacked_congr hw (fun a ⟨_, ha2⟩ => hout a (Or.inl (by omega))) hidx
    obtain ⟨hlo_le_hi, hhi_le_n⟩ := hfb_adj b₀ hb_lt
    set lo := fbMem b₀
    set hi := fbMem (b₀ + 1)
    set len := hi - lo
    have hlo_len : lo + len ≤ n_max := by
      dsimp only [lo, hi, len, fbMem] at hlo_le_hi hhi_le_n ⊢; omega
    obtain ⟨_, hfsl_st, hfsl_res, hfsl_vp⟩ := findSaltLoop_spec (lo := lo) (len := len)
      henv hseed_s hlo_len (sMaxWhp c n_max) 0 0 (by omega) rfl (s := s)
    rw [Nat.zero_add] at hfsl_res
    -- Identify `findSaltLoop_spec`'s `fpMem` on `s` with `fpMem` on `s₀`
    have hfp_congr : ∀ salt t, t < len →
        (let fb_s := fun b => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w
           s.mem b
         let q_s := fun k => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w
           s.mem k
         let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
           (csrBucketOfIdx fb_s (lo + t) M) (q_s (lo + t))
         if hs : salt < sMaxWhp c n_max then
           if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
         else 0) = fpMem salt (lo + t) := by
      intro salt t ht
      have hidx_n : lo + t < n_max := by omega
      dsimp only [fpMem]
      simp only [csrBucketOfIdx_congr hfb_eq, hq_eq (lo + t) hidx_n]
    have hfind_congr : ∀ k,
        findSaltInRange
          (fun salt idx =>
            let fb_s := fun b => readPacked (base + offFbStart c U V w n_max)
              (globalPtrBits n_max) w s.mem b
            let q_s := fun j => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w
              s.mem j
            let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
              (csrBucketOfIdx fb_s idx M) (q_s idx)
            if hs : salt < sMaxWhp c n_max then
              if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
            else 0) lo len k =
        findSaltInRange fpMem lo len k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ihk =>
        dsimp only [findSaltInRange]
        rw [ihk]
        have hpd : ∀ m ≤ len,
            checkPairwiseDistinctOn (fun t =>
              let fb_s := fun b => readPacked (base + offFbStart c U V w n_max)
                (globalPtrBits n_max) w s.mem b
              let q_s := fun j => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w
                s.mem j
              let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
                (csrBucketOfIdx fb_s (lo + t) M) (q_s (lo + t))
              if hs : k < sMaxWhp c n_max then
                if hu : kv < U then fpHash c U n_max θ.2 ⟨k, hs⟩ ⟨kv, hu⟩ else 0
              else 0) m =
            checkPairwiseDistinctOn (fun t => fpMem k (lo + t)) m := by
          intro m hm
          induction m with
          | zero => rfl
          | succ m ihm =>
            dsimp only [checkPairwiseDistinctOn]
            rw [ihm (Nat.le_of_succ_le hm), hfp_congr k m (Nat.lt_of_succ_le hm)]
            congr 1
            have hne_eq : ∀ r ≤ m,
                checkNoEqBefore (fun t =>
                  let fb_s := fun b => readPacked (base + offFbStart c U V w n_max)
                    (globalPtrBits n_max) w s.mem b
                  let q_s := fun j => readPacked (base + offQuotWhp c w n_max)
                    (quotBitsWhp U n_max) w s.mem j
                  let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
                    (csrBucketOfIdx fb_s (lo + t) M) (q_s (lo + t))
                  if hs : k < sMaxWhp c n_max then
                    if hu : kv < U then fpHash c U n_max θ.2 ⟨k, hs⟩ ⟨kv, hu⟩ else 0
                  else 0) (fpMem k (lo + m)) r =
                checkNoEqBefore (fun t => fpMem k (lo + t)) (fpMem k (lo + m)) r := by
              intro r hr
              induction r with
              | zero => rfl
              | succ r ihr =>
                dsimp only [checkNoEqBefore]
                rw [ihr (Nat.le_of_succ_le hr),
                  hfp_congr k r (Nat.lt_of_lt_of_le (Nat.lt_of_succ_le hr) (Nat.le_of_succ_le hm))]
            exact hne_eq m le_rfl
        rw [hpd len le_rfl]
    rw [hfind_congr] at hfsl_res
    set s1_val := salt1Of b₀
    have hs1_le : s1_val ≤ sMaxWhp c n_max := findSaltInRange_le
    have hsVal_pow : s1_val - 1 < 2 ^ globalPtrBits n_max :=
      lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    have hidx_bm : 16 * b₀ + 1 < 16 * M := by omega
    set p1 := findSaltsBktStepProg ((crt, hrt), (b₀, ok₀))
    set m1 := writePacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
      (16 * b₀ + 1) (s1_val - 1)
    have hfsl_res' : (Memory.spec 0).clientResult s
        (findSaltLoopProg
          (((((mkChkRt c U V w n_max base, mkHashRt c U w n_max base), (lo, len)), (0, 0)),
            sMaxWhp c n_max))) = (sMaxWhp c n_max, s1_val) := hfsl_res
    obtain ⟨hws_st, hws_res, hws_vp⟩ := writeSaltResultProg_spec (b := b₀) (allOk := ok₀)
      (s1 := s1_val) henv hb_lt hs1_le (s := s)
    have hlo_hi' : fbMem b₀ ≤ fbMem (b₀ + 1) := hlo_le_hi
    have hhi_n' : fbMem (b₀ + 1) ≤ n_max := hhi_le_n
    have hs_step : (Memory.spec 0).clientState s p1 = { mem := m1, frontier := s.frontier } := by
      dsimp only [p1]; unfold findSaltsBktStepProg; dsimp only
      dsimp only [crt, mkChkRt, ckBase, ckW, ckNMax, ckSMax, ckGBits, ckOffFb, ckOffBm]
      simp only [pure_bind]
      rw [clientState_bind, clientState_readPackedGen, clientResult_readPackedGen,
        hfb_eq b₀ hb_lt.le, clientState_bind, clientState_readPackedGen,
        clientResult_readPackedGen, hfb_eq (b₀ + 1) hb_lt]
      simp only [hlo_hi', hhi_n', ↓reduceIte]
      rw [clientState_bind]; dsimp only [mkChkRt, hrt, lo, hi, len] at hfsl_st hfsl_res' ⊢
      rw [hfsl_st, hfsl_res']; exact hws_st
    set ok1 := if allSaltsFoundRec salt1Of (b₀ + 1) then 1 else 0
    have hr_step : (Memory.spec 0).clientResult s p1 = (b₀ + 1, ok1) := by
      dsimp only [p1]; unfold findSaltsBktStepProg; dsimp only
      dsimp only [crt, mkChkRt, ckBase, ckW, ckNMax, ckSMax, ckGBits, ckOffFb, ckOffBm]
      simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedGen, clientResult_readPackedGen,
        hfb_eq b₀ hb_lt.le, clientResult_bind, clientState_readPackedGen,
        clientResult_readPackedGen, hfb_eq (b₀ + 1) hb_lt]
      simp only [hlo_hi', hhi_n', ↓reduceIte]
      rw [clientResult_bind]; dsimp only [mkChkRt, hrt, lo, hi, len] at hfsl_st hfsl_res' ⊢
      rw [hfsl_st, hfsl_res', hws_res]
      dsimp only [ok1, allSaltsFoundRec, s1_val]
      rw [hok]
      by_cases ha0 : allSaltsFoundRec salt1Of b₀ = true
      · by_cases hsz : salt1Of b₀ = 0 <;> simp [ha0, hsz]
      · simp [Bool.eq_false_iff.mpr ha0]
    have hvp_step : ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold findSaltsBktStepProg; dsimp only
      dsimp only [crt, mkChkRt, ckBase, ckW, ckNMax, ckSMax, ckGBits, ckOffFb, ckOffBm]
      simp only [pure_bind]
      refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
      rw [clientState_readPackedGen, clientResult_readPackedGen, hfb_eq b₀ hb_lt.le]
      refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
      rw [clientState_readPackedGen, clientResult_readPackedGen, hfb_eq (b₀ + 1) hb_lt]
      simp only [hlo_hi', hhi_n', ↓reduceIte]
      dsimp only [mkChkRt, hrt, lo, hi, len] at hfsl_vp hfsl_st hfsl_res' ⊢
      refine validProg_bind hfsl_vp ?_; rw [hfsl_st, hfsl_res']
      exact hws_vp
    set s1 : Memory.State := { mem := m1, frontier := s.frontier }
    have hout1 : ∀ a, (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
        s1.mem a = s₀.mem a := by
      intro a ha
      dsimp only [s1, m1]
      rw [writePacked_outside hw _ hidx_bm _ (by omega)]
      exact hout a ha
    have hsalts1 : ∀ b < b₀ + 1,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s1.mem (16 * b + 1) =
          salt1Of b - 1 := by
      intro b hb
      dsimp only [s1, m1]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hlt | rfl
      · rw [readPacked_writePacked_of_ne hw _ (by omega)]; exact hsalts b hlt
      · exact readPacked_writePacked_self _ _ _ _ _ hsVal_pow
    obtain ⟨hsafe_r, hf_r, hres_r, hvp_r, hsalts_r, hout_r⟩ :=
      ih (b₀ + 1) ok1 s1 (by omega) hout1 hsalts1 rfl
    have hadd : b₀ + 1 + rem = b₀ + (rem + 1) := by omega
    rw [hadd] at hsalts_r
    unfold findSaltsBktLoopProg at hf_r hres_r hvp_r hsalts_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨⟨hpre, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [clientState_width, clientResult_width, hs_step, hr_step]; exact hsafe_r
    · rw [clientState_bind, hs_step, hr_step]; exact hf_r
    · rw [clientResult_bind, hs_step, hr_step, hres_r, hadd]
    · refine validProg_bind hvp_step ?_; rw [hs_step, hr_step]; exact hvp_r
    · intro b hb; rw [clientState_bind, hs_step, hr_step]; exact hsalts_r b hb
    · intro a ha; rw [clientState_bind, hs_step, hr_step]; exact hout_r a ha

/-! ### Part 3d: Top-level `checkGoodSeedOnStateGenProg` -/

@[irreducible] private def checkGoodSeedBodyProg : ChkRt × HashRt → Memory.Prog ℕ
  | (crt, hrt) => do
    let zero_v ← pure 0
    let one_v ← pure 1
    let N ← readPackedGenProg (((ckBase crt, ckOffFb crt), (ckGBits crt, ckW crt)), ckM crt)
    if N ≤ ckNMax crt then
      let bal ← chkBalLoopProg (((crt, N), (zero_v, one_v)), ckM crt)
      let inj ← chkRKeyOuterLoopProg (((crt, hrt), (zero_v, one_v)), N)
      let slts ← findSaltsBktLoopProg (((crt, hrt), (zero_v, one_v)), ckM crt)
      if bal.2 = one_v then
        if inj.2 = one_v then pure slts.2 else pure zero_v
      else
        pure zero_v
    else pure zero_v

private theorem findSaltsBktLoop_safe {c U V w n_max base : ℕ} {θ : SeedWhp c U n_max}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let crt := mkChkRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    ∀ rem b₀ ok₀ (s : Memory.State),
      b₀ + rem ≤ numBucketsWhp n_max →
      SeedWhpMemRep base c U w n_max θ s.mem →
      iterationSafe findSaltsBktStepProg FindSaltsBktStepPre w (crt, hrt) rem (b₀, ok₀) s := by
  intro crt hrt rem
  have hw := henv.2.1
  have hq_le_bm := offQuot_le_offBktMeta c U V w n_max
  induction rem with
  | zero => intro _ _ _ _ _; exact trivial
  | succ rem ih =>
    intro b₀ ok₀ s hle hseed
    have hb_lt : b₀ < numBucketsWhp n_max := by omega
    have hpre : FindSaltsBktStepPre w ((crt, hrt), (b₀, ok₀)) s :=
      ⟨⟨c, U, V, w, n_max, θ, henv, rfl, rfl, hseed⟩, hb_lt⟩
    set p1 := findSaltsBktStepProg ((crt, hrt), (b₀, ok₀))
    have hws_fst : ∀ cfg okv sv s',
        ((Memory.spec 0).clientResult s' (writeSaltResultProg (cfg, (okv, sv)))).1 =
          cfg.2.2 + 1 := by
      intro ⟨⟨⟨b0, ob0⟩, gb0, w0⟩, sm0, bk0⟩ okv sv s'
      unfold writeSaltResultProg; dsimp only; simp only [pure_bind]
      by_cases hsm : sv ≤ sm0
      · simp only [hsm, ↓reduceIte]
        by_cases h1s : 1 ≤ sv
        · simp only [h1s, ↓reduceIte]; rw [clientResult_bind]
          split_ifs <;> rfl
        · simp only [h1s, ↓reduceIte]; rw [clientResult_bind]; rfl
      · simp only [hsm, ↓reduceIte]; rw [clientResult_bind]; rfl
    have hws_mem : ∀ okv sv s',
        ∃ vVal,
          ((Memory.spec 0).clientState s'
            (writeSaltResultProg
              ((((base, offBktMeta c U V w n_max), (globalPtrBits n_max, w)),
                (sMaxWhp c n_max, b₀)), (okv, sv)))).mem =
            writePacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem
              (16 * b₀ + 1) vVal := by
      intro okv sv s'
      unfold writeSaltResultProg; dsimp only; simp only [pure_bind]
      by_cases hsm : sv ≤ sMaxWhp c n_max
      · simp only [hsm, ↓reduceIte]
        by_cases h1s : 1 ≤ sv
        · simp only [h1s, ↓reduceIte]
          rw [clientState_bind, clientState_writePackedGen]
          exact ⟨sv - 1, by split_ifs <;> rfl⟩
        · simp only [h1s, ↓reduceIte]
          rw [clientState_bind, clientState_writePackedGen]; exact ⟨0, rfl⟩
      · simp only [hsm, ↓reduceIte]
        rw [clientState_bind, clientState_writePackedGen]; exact ⟨0, rfl⟩
    have hfst : ((Memory.spec 0).clientResult s p1).1 = b₀ + 1 := by
      dsimp only [p1]; unfold findSaltsBktStepProg; dsimp only
      simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedGen, clientResult_bind,
        clientState_readPackedGen]
      split_ifs with h1 h2
      · rw [clientResult_bind]; exact hws_fst _ _ _ _
      · rfl
      · rfl
    have hseed' : SeedWhpMemRep base c U w n_max θ ((Memory.spec 0).clientState s p1).mem := by
      dsimp only [p1]; unfold findSaltsBktStepProg; dsimp only
      simp only [pure_bind]
      rw [clientState_bind, clientState_readPackedGen, clientResult_readPackedGen,
        clientState_bind, clientState_readPackedGen, clientResult_readPackedGen]
      split_ifs with h1 h2
      · rw [clientState_bind]
        set lo := readPacked (ckBase crt + ckOffFb crt) (ckGBits crt) (ckW crt) s.mem b₀
        set hi := readPacked (ckBase crt + ckOffFb crt) (ckGBits crt) (ckW crt) s.mem (b₀ + 1)
        dsimp only [crt, mkChkRt, ckBase, ckW, ckNMax, ckGBits, ckOffFb] at h1 h2 lo hi ⊢
        obtain ⟨_, hfsl_st, _, _⟩ := findSaltLoop_spec (lo := lo) (len := hi - lo)
          henv hseed (by omega) (sMaxWhp c n_max) 0 0 (by omega) rfl (s := s)
        dsimp only [crt, hrt, mkChkRt, ckSMax, ckOffBm] at hfsl_st ⊢
        rw [hfsl_st]
        obtain ⟨vVal, hm_eq⟩ := hws_mem ok₀
          ((Memory.spec 0).clientResult s
            (findSaltLoopProg
              (((((crt, mkHashRt c U w n_max base), (lo, hi - lo)),
                (0, 0)), sMaxWhp c n_max)))).2 s
        dsimp only [crt, mkChkRt] at hm_eq
        rw [hm_eq]
        exact SeedWhpMemRep.congr_hash hw (fun a _ ha2 =>
          (writePacked_outside hw _ (by omega : 16 * b₀ + 1 < 16 * numBucketsWhp n_max) _ (by
            omega)).symm) hseed
      · exact hseed
      · exact hseed
    refine ⟨hpre, ?_⟩
    rw [clientState_width, clientResult_width]
    set res := (Memory.spec 0).clientResult s p1
    have heta : res = (b₀ + 1, res.2) := Prod.ext hfst rfl
    rw [heta]
    exact ih (b₀ + 1) res.2 _ (by omega) hseed'

private theorem realizes_checkGoodSeedBody :
    Realizes .exact checkGoodSeedBodyProg
      (WordEncoding.encode (α := ChkRt × HashRt))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => ChkHashEnv w d.1 d.2 s)
      (fun _ _ => 0) := by
  unfold checkGoodSeedBodyProg
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize [realizes_readPackedGen, realizes_chkBalLoop, realizes_chkRKeyOuterLoop,
      realizes_findSaltsBktLoop]
  all_goals (
    rcases d with ⟨crt, hrt⟩
    obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_crt, heq_hrt, hseed⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize ckBase crt = base at henv heq_crt heq_hrt hseed
    subst heq_crt
    dsimp only [mkChkRt, ckBase, ckW, ckNMax, ckM, ckGBits, ckOffFb] at *
    simp only [hcs, clientResult_readPackedGen] at *
    first
    | exact henv.fits_const (by decide)
    | exact chk_fb_safe henv (Nat.lt_succ_self _)
    | (subst heq_hrt
       set N := readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem
         (numBucketsWhp n_max)
       obtain ⟨hbl_sf, hbl_st, _, _⟩ := chkBalLoop_spec (N := N) henv (by omega) s
         (numBucketsWhp n_max) 0 1 (by omega) rfl
       obtain ⟨hrl_sf, hrl_st, _, _⟩ := chkRKeyOuterLoop_spec henv hseed N 0 1 (by omega) rfl
         (s := s)
       have hsl_sf := findSaltsBktLoop_safe (V := V) henv (numBucketsWhp n_max) 0 1 s
         (by omega) hseed
       dsimp only [mkChkRt] at hbl_sf hbl_st hrl_sf hrl_st hsl_sf
       simp only [hbl_st, hrl_st] at *
       first
       | exact hbl_sf
       | exact hrl_sf
       | exact hsl_sf)
  )

/-- Evaluate `checkGoodSeedOnState c U n_max θ csr` in place on `CsrMemRep` (`d = (wp, base)`),
returning `1` iff `ok = true` and storing `(checkGoodSeedOnState c U n_max θ csr).2 b` at
`offBktMeta[16 * b + 1]` for every `b < numBucketsWhp n_max`. -/
@[irreducible] def checkGoodSeedOnStateGenProg (d : WhpParams × ℕ) : Memory.Prog ℕ := do
  let wp := d.1
  let crt ← mkChkRtGenProg (wp.1, d.2)
  let hrt ← mkHashRtGenProg d
  checkGoodSeedBodyProg (crt, hrt)

theorem realizes_checkGoodSeedOnStateGen :
    Realizes .exact checkGoodSeedOnStateGenProg
      (WordEncoding.encode (α := WhpParams × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (wp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem)
      (fun _ _ => 0) := by
  unfold checkGoodSeedOnStateGenProg
  realize [realizes_mkChkRtGen, realizes_mkHashRtGen, realizes_checkGoodSeedBody]
  all_goals (
    rcases d with ⟨wp, base⟩
    obtain ⟨c, U, V, w₀, n_max, θ, henv, rfl, hseed⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      unfold mkWhpParams; rw [ite_eq_right (Nat.not_lt.mpr hth)]
    obtain ⟨hmc_st, hmc_res, _, _⟩ := mkChkRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    simp only [hwp1, hmc_st, hmc_res, hmh_st, hmh_res] at *
    first
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, rfl, hseed⟩
  )

/-- Exact specification of `checkGoodSeedOnStateGenProg`: evaluates
`checkGoodSeedOnState c U n_max θ csr` on any valid `CsrMemRep`, writes `(checkGoodSeedOnState
c U n_max θ csr).2 b` into `offBktMeta[16 * b + 1]` for all `b < numBucketsWhp n_max`, and preserves
both `SeedWhpMemRep` and `CsrMemRep`. -/
theorem checkGoodSeedOnStateGenProg_spec {c U V w n_max base : ℕ} {θ : SeedWhp c U n_max}
    {csr : CsrState} {dict : Dictionary.State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : CsrMemRep base c U V w n_max csr s.mem)
    (hv : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict) :
    let prog := checkGoodSeedOnStateGenProg (mkWhpParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    let res := checkGoodSeedOnState c U n_max θ csr
    (Memory.spec 0).clientResult s prog = (if res.1 then 1 else 0) ∧
    SeedWhpMemRep base c U w n_max θ s'.mem ∧
    CsrMemRep base c U V w n_max csr s'.mem ∧
    (∀ b < numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem (16 * b + 1) =
        res.2 b) ∧
    s'.frontier = s.frontier ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    (∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hq_le_bm := offQuot_le_offBktMeta c U V w n_max
  have h32_q : 32 ≤ offQuotWhp c w n_max := by
    change offHashBkt ≤ _; unfold offQuotWhp offHashFp; omega
  have hql_end := hseg.1
  have hvl_end := hseg.2.1
  have hl_v : offValWhp c U w n_max =
      offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w := rfl
  have hl_pa : offPermAct c U V w n_max =
      offValWhp c U w n_max + packedWords n_max (valBits V) w := rfl
  have hpa_le_bm : offPermAct c U V w n_max ≤ offBktMeta c U V w n_max := by
    unfold offBktMeta offLocState; omega
  set M := numBucketsWhp n_max
  set N := csr.fbStart M
  have hN_le : N ≤ n_max := hv.2.2.1
  have hmono := fbStart_mono_of_adj hv.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    unfold mkWhpParams; rw [ite_eq_right (Nat.not_lt.mpr hth)]
  obtain ⟨hmc_st, hmc_res, _, hmc_vp⟩ := mkChkRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hmh_st, hmh_res, _, hmh_vp⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) hth s
  set crt := mkChkRt c U V w n_max base
  set hrt := mkHashRt c U w n_max base
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.1 _
  -- Identify `fbMem` and `qMem` on `s` with `csr.fbStart` and `csr.qArr`
  set fbMem := fun b => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem b
  set qMem := fun k => readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem k
  have hfb_eq : ∀ b ≤ M, fbMem b = csr.fbStart b := hrep.2.1
  have hq_eq : ∀ i < n_max, qMem i = csr.qArr i := fun i hi => (hrep.2.2 i hi).1
  -- Loop 1: `chkBalLoopProg`
  obtain ⟨_, hbl_st, hbl_res, hbl_vp⟩ := chkBalLoop_spec henv hN_le s M 0 1 (by omega) rfl
  rw [Nat.zero_add] at hbl_res
  have hbal_congr : ∀ k ≤ M,
      checkAllBalancedCsr M (deltaWhp n_max) N fbMem k =
        checkAllBalancedCsr M (deltaWhp n_max) N csr.fbStart k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ihk =>
      dsimp only [checkAllBalancedCsr]
      rw [ihk (Nat.le_of_succ_le hk), hfb_eq k (Nat.le_of_succ_le hk), hfb_eq (k + 1) hk]
  rw [hbal_congr M le_rfl] at hbl_res
  -- Loop 2: `chkRKeyOuterLoopProg`
  obtain ⟨_, hrl_st, hrl_res, hrl_vp⟩ :=
    chkRKeyOuterLoop_spec henv hseed N 0 1 (by omega) rfl (s := s)
  rw [Nat.zero_add] at hrl_res
  let keyValAt : ℕ → ℕ := fun i =>
    feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) (csrBucketOfIdx csr.fbStart i M)
      (csr.qArr i)
  let rKeyAt : ℕ → ℕ := fun i =>
    if h : keyValAt i < U then fpReducedKey c U n_max θ.2 ⟨keyValAt i, h⟩ else 0
  have hrk_pt : ∀ i < N,
      (let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
         (csrBucketOfIdx fbMem i M) (qMem i)
       if h : kv < U then fpReducedKey c U n_max θ.2 ⟨kv, h⟩ else 0) = rKeyAt i := by
    intro i hi
    dsimp only [rKeyAt, keyValAt]
    rw [csrBucketOfIdx_congr hfb_eq, hq_eq i (hi.trans_le hN_le)]
  have hinj_congr : ∀ k ≤ N,
      checkPairwiseDistinctOn (fun idx =>
        let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
          (csrBucketOfIdx fbMem idx M) (qMem idx)
        if h : kv < U then fpReducedKey c U n_max θ.2 ⟨kv, h⟩ else 0) k =
      checkPairwiseDistinctOn rKeyAt k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ihk =>
      dsimp only [checkPairwiseDistinctOn]
      rw [ihk (Nat.le_of_succ_le hk), hrk_pt k (Nat.lt_of_succ_le hk)]
      congr 1
      have hne_c : ∀ r ≤ k,
          checkNoEqBefore (fun idx =>
            let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
              (csrBucketOfIdx fbMem idx M) (qMem idx)
            if h : kv < U then fpReducedKey c U n_max θ.2 ⟨kv, h⟩ else 0) (rKeyAt k) r =
          checkNoEqBefore rKeyAt (rKeyAt k) r := by
        intro r hr
        induction r with
        | zero => rfl
        | succ r ihr =>
          dsimp only [checkNoEqBefore]
          rw [ihr (Nat.le_of_succ_le hr),
            hrk_pt r (Nat.lt_of_lt_of_le (Nat.lt_of_succ_le hr) (Nat.le_of_succ_le hk))]
      exact hne_c k le_rfl
  rw [hinj_congr N le_rfl] at hrl_res
  -- Loop 3: `findSaltsBktLoopProg`
  have hfb_adj : ∀ b < M, fbMem b ≤ fbMem (b + 1) ∧ fbMem (b + 1) ≤ n_max := fun b hb => by
    rw [hfb_eq b hb.le, hfb_eq (b + 1) hb]
    exact ⟨hv.2.1 b hb, (hmono (b + 1) M hb le_rfl).trans hN_le⟩
  obtain ⟨_, hsl_f, hsl_res, hsl_vp, hsl_salts, hsl_out⟩ :=
    findSaltsBktLoop_spec henv hseed hfb_adj M 0 1 s (by omega) (fun _ _ => rfl)
      (fun _ h => absurd h (Nat.not_lt_zero _)) rfl
  rw [Nat.zero_add] at hsl_res hsl_salts
  set s_sl := (Memory.spec 0).clientState s (findSaltsBktLoopProg (((crt, hrt), (0, 1)), M))
  -- Identify `salt1Of` on `fbMem, qMem` with `checkGoodSeedOnState`'s `salt1Of`
  let fpAt : ℕ → ℕ → ℕ := fun salt i =>
    if hs : salt < sMaxWhp c n_max then
      if hu : keyValAt i < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨keyValAt i, hu⟩ else 0
    else 0
  let salt1Pure : ℕ → ℕ := fun b =>
    findSaltInRange fpAt (csr.fbStart b) (csr.fbStart (b + 1) - csr.fbStart b) (sMaxWhp c n_max)
  have hfp_pt : ∀ salt idx, idx < n_max →
      (let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
         (csrBucketOfIdx fbMem idx M) (qMem idx)
       if hs : salt < sMaxWhp c n_max then
         if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
       else 0) = fpAt salt idx := by
    intro salt idx hidx
    dsimp only [fpAt, keyValAt]
    rw [csrBucketOfIdx_congr hfb_eq, hq_eq idx hidx]
  have hsalt1_eq : ∀ b < M,
      findSaltInRange (fun salt idx =>
        let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
          (csrBucketOfIdx fbMem idx M) (qMem idx)
        if hs : salt < sMaxWhp c n_max then
          if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
        else 0) (fbMem b) (fbMem (b + 1) - fbMem b) (sMaxWhp c n_max) = salt1Pure b := by
    intro b hb
    rw [hfb_eq b hb.le, hfb_eq (b + 1) hb]
    have hhi_le : csr.fbStart (b + 1) ≤ n_max := (hmono (b + 1) M hb le_rfl).trans hN_le
    have hle_b := hv.2.1 b hb
    dsimp only [salt1Pure]
    have hrec : ∀ k,
        findSaltInRange (fun salt idx =>
          let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
            (csrBucketOfIdx fbMem idx M) (qMem idx)
          if hs : salt < sMaxWhp c n_max then
            if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
          else 0) (csr.fbStart b) (csr.fbStart (b + 1) - csr.fbStart b) k =
        findSaltInRange fpAt (csr.fbStart b) (csr.fbStart (b + 1) - csr.fbStart b) k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ihk =>
        dsimp only [findSaltInRange]; rw [ihk]
        set lo_b := csr.fbStart b
        set len_b := csr.fbStart (b + 1) - csr.fbStart b
        have hpd : ∀ m ≤ len_b,
            checkPairwiseDistinctOn (fun t =>
              let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
                (csrBucketOfIdx fbMem (lo_b + t) M) (qMem (lo_b + t))
              if hs : k < sMaxWhp c n_max then
                if hu : kv < U then fpHash c U n_max θ.2 ⟨k, hs⟩ ⟨kv, hu⟩ else 0
              else 0) m =
            checkPairwiseDistinctOn (fun t => fpAt k (lo_b + t)) m := by
          intro m hm
          induction m with
          | zero => rfl
          | succ m ihm =>
            dsimp only [checkPairwiseDistinctOn]
            rw [ihm (Nat.le_of_succ_le hm), hfp_pt k (lo_b + m) (by omega)]
            congr 1
            have hne_c : ∀ r ≤ m,
                checkNoEqBefore (fun t =>
                  let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
                    (csrBucketOfIdx fbMem (lo_b + t) M) (qMem (lo_b + t))
                  if hs : k < sMaxWhp c n_max then
                    if hu : kv < U then fpHash c U n_max θ.2 ⟨k, hs⟩ ⟨kv, hu⟩ else 0
                  else 0) (fpAt k (lo_b + m)) r =
                checkNoEqBefore (fun t => fpAt k (lo_b + t)) (fpAt k (lo_b + m)) r := by
              intro r hr
              induction r with
              | zero => rfl
              | succ r ihr =>
                dsimp only [checkNoEqBefore]
                rw [ihr (Nat.le_of_succ_le hr), hfp_pt k (lo_b + r) (by omega)]
            exact hne_c m le_rfl
        exact congrArg (if _ != 0 then _ else if · then k + 1 else 0) (hpd len_b le_rfl)
    exact hrec (sMaxWhp c n_max)
  have hall_congr : ∀ k ≤ M,
      allSaltsFoundRec (fun b =>
        findSaltInRange (fun salt idx =>
          let kv := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
            (csrBucketOfIdx fbMem idx M) (qMem idx)
          if hs : salt < sMaxWhp c n_max then
            if hu : kv < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv, hu⟩ else 0
          else 0) (fbMem b) (fbMem (b + 1) - fbMem b) (sMaxWhp c n_max)) k =
      (Nat.rec true (fun b prev => prev && (salt1Pure b != 0)) k) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ihk =>
      dsimp only [allSaltsFoundRec]
      rw [ihk (Nat.le_of_succ_le hk), hsalt1_eq k (Nat.lt_of_succ_le hk)]
  rw [hall_congr M le_rfl] at hsl_res
  -- Combine whole body execution
  have hfbM : readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem
      (numBucketsWhp n_max) = csr.fbStart (numBucketsWhp n_max) := hrep.2.1 M le_rfl
  have hst_eq : (Memory.spec 0).clientState s
      (checkGoodSeedOnStateGenProg (mkWhpParams c U V w n_max, base)) = s_sl := by
    unfold checkGoodSeedOnStateGenProg; dsimp only
    rw [hwp1, clientState_bind, hmc_st, hmc_res, clientState_bind, hmh_st, hmh_res]
    unfold checkGoodSeedBodyProg; dsimp only [crt, mkChkRt, ckBase, ckW, ckNMax, ckM, ckGBits,
      ckOffFb]
    simp only [pure_bind]
    rw [clientState_bind, clientState_readPackedGen, clientResult_readPackedGen, hfbM]
    simp only [show csr.fbStart (numBucketsWhp n_max) ≤ n_max from hN_le, ↓reduceIte]
    rw [clientState_bind]; dsimp only [crt, mkChkRt, hrt, M, N] at hbl_st hrl_st s_sl ⊢
    rw [hbl_st, clientState_bind, hrl_st, clientState_bind]
    split_ifs <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · -- clientResult = if (checkGoodSeedOnState ...).1 then 1 else 0
    unfold checkGoodSeedOnStateGenProg; dsimp only
    rw [hwp1, clientResult_bind, hmc_st, hmc_res, clientResult_bind, hmh_st, hmh_res]
    unfold checkGoodSeedBodyProg; dsimp only [crt, mkChkRt, ckBase, ckW, ckNMax, ckM, ckGBits,
      ckOffFb]
    simp only [pure_bind]
    rw [clientResult_bind, clientState_readPackedGen, clientResult_readPackedGen, hfbM]
    simp only [show csr.fbStart (numBucketsWhp n_max) ≤ n_max from hN_le, ↓reduceIte]
    dsimp only [crt, mkChkRt, hrt, M, N] at hbl_st hbl_res hrl_st hrl_res hsl_res ⊢
    rw [clientResult_bind, hbl_st, hbl_res, clientResult_bind, hrl_st, hrl_res,
      clientResult_bind, hsl_res]
    dsimp only [checkGoodSeedOnState]
    by_cases hb1 :
        checkAllBalancedCsr (numBucketsWhp n_max) (deltaWhp n_max)
          (csr.fbStart (numBucketsWhp n_max)) csr.fbStart (numBucketsWhp n_max) = true <;>
      by_cases hb2 : checkPairwiseDistinctOn rKeyAt (csr.fbStart (numBucketsWhp n_max)) = true <;>
      by_cases hb3 : (Nat.rec true (fun b prev => prev && (salt1Pure b != 0))
        (numBucketsWhp n_max) : Bool) = true <;>
      dsimp only [rKeyAt, keyValAt, salt1Pure, fpAt, M] at hb2 hb3 ⊢
    · simp [hb1, hb2, hb3]
    · simp [hb1, hb2, Bool.eq_false_iff.mpr hb3]
    · simp [hb1, Bool.eq_false_iff.mpr hb2]
    · simp [hb1, Bool.eq_false_iff.mpr hb2]
    · simp [Bool.eq_false_iff.mpr hb1]
    · simp [Bool.eq_false_iff.mpr hb1]
    · simp [Bool.eq_false_iff.mpr hb1]
    · simp [Bool.eq_false_iff.mpr hb1]
  · -- SeedWhpMemRep
    rw [hst_eq]
    exact SeedWhpMemRep.congr_hash hw (fun a _ ha2 => (hsl_out a (Or.inl (by omega))).symm) hseed
  · -- CsrMemRep preserved!
    rw [hst_eq]
    refine ⟨?_, fun b hb => ?_, fun i hi => ⟨?_, ?_⟩⟩
    · rw [hsl_out (base + hdrMode) (Or.inl (by dsimp [hdrMode]; omega))]; exact hrep.1
    · rw [readPacked_congr hw (fun a ⟨ha1, _⟩ => hsl_out a (Or.inr ha1)) (Nat.lt_succ_of_le hb)]
      exact hrep.2.1 b hb
    · rw [readPacked_congr hw (fun a ⟨_, ha2⟩ => hsl_out a (Or.inl (by omega))) hi]
      exact (hrep.2.2 i hi).1
    · rw [readPacked_congr hw (fun a ⟨_, ha2⟩ => hsl_out a (Or.inl (by omega))) hi]
      exact (hrep.2.2 i hi).2
  · -- Salts stored at offBktMeta[16 * b + 1]
    intro b hb
    rw [hst_eq, hsl_salts b hb]
    dsimp only [fbMem, qMem, M] at hsalt1_eq ⊢
    rw [hsalt1_eq b hb]
    rfl
  · rw [hst_eq]; exact hsl_f
  · -- ValidProg
    unfold checkGoodSeedOnStateGenProg; dsimp only
    rw [hwp1]
    refine validProg_bind hmc_vp ?_; rw [hmc_st, hmc_res]
    refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
    unfold checkGoodSeedBodyProg; dsimp only [crt, mkChkRt, ckBase, ckW, ckNMax, ckM, ckGBits,
      ckOffFb]
    simp only [pure_bind]
    refine validProg_bind (validProg_readPacked hw (Nat.lt_succ_self _) hfb_b) ?_
    rw [clientState_readPackedGen, clientResult_readPackedGen, hfbM]
    simp only [show csr.fbStart (numBucketsWhp n_max) ≤ n_max from hN_le, ↓reduceIte]
    dsimp only [crt, mkChkRt, hrt, M, N] at hbl_vp hbl_st hrl_vp hrl_st hsl_vp ⊢
    refine validProg_bind hbl_vp ?_; rw [hbl_st]
    refine validProg_bind hrl_vp ?_; rw [hrl_st]
    refine validProg_bind hsl_vp ?_
    split_ifs <;> exact validProg_pure _
  · -- Footprint outside largeSpaceWhp
    rw [hst_eq]
    rcases ha with ha_lo | ha_hi
    · exact hsl_out a (Or.inl (by omega))
    · have hfb_le : base + offFbStart c U V w n_max ≤ base + largeSpaceWhp c U V w n_max :=
        (Nat.le_add_right _ _).trans hfb_b
      exact hsl_out a (Or.inr (by omega))

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
