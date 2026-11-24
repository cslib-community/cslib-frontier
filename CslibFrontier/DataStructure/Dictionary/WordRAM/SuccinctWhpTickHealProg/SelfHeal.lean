/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSeedCheckProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpTickHealProg.HealRt
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpTickHealProg.PrefixBackPtr
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpTickHealProg.PoolLocSlices
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpTickHealProg.BucketRebuild
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpTickHealProg.MetaFinalize
import CslibFrontier.Tactic.Realize

/-!
# In-Place `csrToFastGenProg` and `trySelfHealGenProg` Subroutines for `SuccinctWhp`

This internal module composes the parallel array/slice phase loops into:
* **`csrToFastGenProg`**: converts `CsrMemRep` in place into `FastMemRep` for
  `csrToFast c U n_max θ csr salts` when `GoodSeedOnState` holds and candidate salts occupy
  `offBktMeta[16 * b + 1]`.
* **`trySelfHealGenProg`**: chains `checkGoodSeedOnStateGenProg` with `csrToFastGenProg`,
  refining `trySelfHeal c U n_max θ csr` into `WhpMemRep`.

* **`csrToFastGenProg`** and **`trySelfHealGenProg`**, remaining completely decoupled from
  `SuccinctWhpFastOpProg` and `SuccinctWhpEpochTickProg`, while the four underlying array/slice
  phase modules remain decoupled from `SuccinctWhpSeedCheckProg` and `SuccinctWhpFastBaseProg` as
  well.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.csrToFastGenProg`, `trySelfHealGenProg`,
  `TrySelfHealPre`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_trySelfHealGen`,
  `trySelfHealGenProg_spec`.
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
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ## Section 1: `csrToFastGenProg` (`CsrMemRep → FastMemRep`) -/

@[irreducible] private def csrToFastPart1aProg (d : WhpCoreParams × ℕ) : Memory.Prog ℕ := do
  let cp := d.1
  let base ← pure d.2
  let rt ← mkHealRtGenProg (cp, base)
  let prt ← mkPermRtGenProg (cp, base)
  let zero_v ← pure 0
  let two_v ← pure 2
  let _ ← writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), zero_v), zero_v)
  let _ ← bpPrefixLoopProg ((rt, (zero_v, zero_v)), hlM rt)
  let idxM2 ← pure (2 * hlM rt)
  let totalBack ← readPackedGenProg (((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxM2)
  let _ ← fillBackPtrOuterLoopProg ((rt, zero_v), hlM rt)
  let _ ← permuteByTargetProg (prt, two_v)
  pure totalBack

@[irreducible] private def csrToFastPart1bProg (d : (WhpCoreParams × ℕ) × ℕ) :
    Memory.Prog ℕ := do
  let cp := d.1.1
  let base ← pure d.1.2
  let totalBack ← pure d.2
  let rt ← mkHealRtGenProg (cp, base)
  let zero_v ← pure 0
  let freeTop ← clampSubProg (hlPoolSize rt, totalBack)
  let _ ← fillPoolOwnerLoopProg (((rt, totalBack), zero_v), hlPoolSize rt)
  let _ ← fillFreeStackLoopProg (((rt, (totalBack, freeTop)), zero_v), hlPoolSize rt)
  let _ ← fillLocStateOuterLoopProg ((rt, zero_v), hlM rt)
  let threeM ← pure (3 * hlM rt)
  let _ ← resetAllSlicesLoopProg (((cp, base), zero_v), threeM)
  pure freeTop

@[irreducible] private def csrToFastPart1Prog (d : WhpCoreParams × ℕ) : Memory.Prog ℕ := do
  let cp := d.1
  let base ← pure d.2
  let totalBack ← csrToFastPart1aProg (cp, base)
  csrToFastPart1bProg ((cp, base), totalBack)

/-- Convert `CsrMemRep` in place to `FastMemRep` for `csrToFast c U n_max θ csr salts` when
`GoodSeedOnState` holds and `salts b` is stored at `offBktMeta[16 * b + 1]` (`d = (wp, base)`). -/
@[irreducible] def csrToFastGenProg : WhpParams × ℕ → Memory.Prog Unit
  | (wp, base_in) => do
    let base ← pure base_in
    let cp := wp.1
    let freeTop ← csrToFastPart1Prog (cp, base)
    let rt ← mkHealRtGenProg (cp, base)
    let hrt ← mkHashRtGenProg (wp, base)
    let zero_v ← pure 0
    let _ ← buildAllBucketsOuterLoopProg ((((cp, base), (rt, hrt)), zero_v), hlM rt)
    let _ ← fillFinalBktMetaLoopProg ((rt, zero_v), hlM rt)
    let _ ← zeroTrieChildrenLoopProg
      (((rt, (wpOffTrieChild0 cp, wpOffTrieChild1 cp)), zero_v), hlTcEntries rt)
    writeHealHdrsAndTrieMetaProg ((rt, (wpOffTrieMeta0 cp, wpOffTrieMeta1 cp)), freeTop)

private theorem csrToFast_phases_A_to_E1 {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {csr : CsrState} {dict : Dictionary.State U} {salts : ℕ → ℕ}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : CsrMemRep base c U V w n_max csr s.mem)
    (hcsr : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict)
    (hqv : ∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1)
    (hgood : GoodSeedOnState c U n_max θ dict)
    (hsalts_mem : ∀ b < numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem (16 * b + 1) =
        salts b) :
    let cp := mkWhpCoreParams c U V w n_max
    let rt := mkHealRt c U V w n_max base
    let prt := mkPermRt c U V w n_max base
    let M := numBucketsWhp n_max
    let cf := capFrontWhp n_max
    let cb := capBackWhp n_max
    let gBits := globalPtrBits n_max
    let bp := buildBackPrefix M cf csr.fbStart
    let totalBack := bp M
    let freeTop := poolSizeWhp n_max - totalBack
    let bktCnt : ℕ → ℕ := fun b => if b < M then csr.fbStart (b + 1) - csr.fbStart b else 0
    let backPtr : ℕ → ℕ → ℕ := fun b k =>
      if b < M ∧ k < bktCnt b - cf then bp b + k else 0
    let act₀ : ℕ → Bool := fun i => decide (i < csr.fbStart M)
    let dest : ℕ → ℕ := fun i =>
      let b := csrBucketOfIdx csr.fbStart i M
      let loc := i - csr.fbStart b
      if loc < cf then b * cf + loc else M * cf + backPtr b (loc - cf)
    let pv := permuteByTarget n_max dest act₀ csr.qArr csr.vArr
    let findOwner : ℕ → ℕ := fun poolIdx =>
      let b := csrBucketOfIdx bp poolIdx M
      let k := poolIdx - bp b
      if poolIdx < totalBack then b * cb + k else 0
    let s_w0 := (Memory.spec 0).clientState s
      (writePackedGenProg ((((base, offBktMeta c U V w n_max), (gBits, w)), 0), 0))
    let s_bp := (Memory.spec 0).clientState s_w0 (bpPrefixLoopProg ((rt, (0, 0)), M))
    let s_fbp := (Memory.spec 0).clientState s_bp (fillBackPtrOuterLoopProg ((rt, 0), M))
    let s_pt := (Memory.spec 0).clientState s_fbp (permuteByTargetProg (prt, 2))
    let s_po := (Memory.spec 0).clientState s_pt
      (fillPoolOwnerLoopProg (((rt, totalBack), 0), poolSizeWhp n_max))
    let s_fs := (Memory.spec 0).clientState s_po
      (fillFreeStackLoopProg (((rt, (totalBack, freeTop)), 0), poolSizeWhp n_max))
    let s_ls := (Memory.spec 0).clientState s_fs (fillLocStateOuterLoopProg ((rt, 0), M))
    let s_ras := (Memory.spec 0).clientState s_ls (resetAllSlicesLoopProg (((cp, base), 0), 3 * M))
    totalBack ≤ poolSizeWhp n_max ∧
    readPacked (base + offBktMeta c U V w n_max) gBits w s_bp.mem (2 * M) = totalBack ∧
    s_ras.frontier = s.frontier ∧
    SeedWhpMemRep base c U w n_max θ s_ras.mem ∧
    (∀ x ≤ M, readPacked (base + offFbStart c U V w n_max) gBits w s_ras.mem x = csr.fbStart x) ∧
    (∀ i < n_max,
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s_ras.mem i = pv.1 i ∧
      readPacked (base + offValWhp c U w n_max) (valBits V) w s_ras.mem i = pv.2 i) ∧
    (∀ b < M, ∀ loc < totalLocalCoordsWhp n_max,
      readPacked (base + offLocState c U V w n_max) 2 w s_ras.mem
        (b * totalLocalCoordsWhp n_max + loc) = if loc < bktCnt b then 1 else 0) ∧
    (∀ b < M, ∀ k < cb,
      readPacked (base + offBackPtr c U V w n_max) gBits w s_ras.mem (b * cb + k) = backPtr b k) ∧
    (∀ j < poolSizeWhp n_max,
      readPacked (base + offPoolFreeStack c U V w n_max) gBits w s_ras.mem j =
        (if j < freeTop then totalBack + j else 0) ∧
      readPacked (base + offPoolOwner c U V w n_max) gBits w s_ras.mem j = findOwner j) ∧
    (∀ sIdx < 3 * M, BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice s_ras.mem) ∧
    (∀ b < M,
      readPacked (base + offBktMeta c U V w n_max) gBits w s_ras.mem (16 * b + 1) = salts b) ∧
    (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offBtMeta c U V w n_max ≤ a) →
      s_ras.mem a = s.mem a) ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (writePackedGenProg ((((base, offBktMeta c U V w n_max), (gBits, w)), 0), 0)) ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s_w0
      (bpPrefixLoopProg ((rt, (0, 0)), M)) ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s_bp
      (fillBackPtrOuterLoopProg ((rt, 0), M)) ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s_fbp
      (permuteByTargetProg (prt, 2)) ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s_pt
      (fillPoolOwnerLoopProg (((rt, totalBack), 0), poolSizeWhp n_max)) ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s_po
      (fillFreeStackLoopProg (((rt, (totalBack, freeTop)), 0), poolSizeWhp n_max)) ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s_fs
      (fillLocStateOuterLoopProg ((rt, 0), M)) ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s_ls
      (resetAllSlicesLoopProg (((cp, base), 0), 3 * M)) := by
  intro cp rt prt M cf cb gBits bp totalBack freeTop bktCnt backPtr act₀ dest pv findOwner
    s_w0 s_bp s_fbp s_pt s_po s_fs s_ls s_ras
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  obtain ⟨_, h16M, _, hps_le, _, _, _, hgk⟩ := hl_bounds henv
  obtain ⟨hbnd_good, htb_le⟩ := csrToFast_bounds_of_good hth hcsr hgood
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max + packedWords (16 * M) gBits w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  have hl_v : offValWhp c U w n_max =
      offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w := rfl
  have hl_pa : offPermAct c U V w n_max = offValWhp c U w n_max + packedWords n_max (valBits V) w :=
    rfl
  have hl_ls : offLocState c U V w n_max =
      offPermAct c U V w n_max + packedWords n_max (12 * logLogFactor n_max + 4) w := rfl
  have hl_bm : offBktMeta c U V w n_max =
      offLocState c U V w n_max + packedWords (M * totalLocalCoordsWhp n_max) 2 w := rfl
  have hl_fb : offFbStart c U V w n_max =
      offBktMeta c U V w n_max + packedWords (16 * M) gBits w := rfl
  have hl_bp : offBackPtr c U V w n_max =
      offFbStart c U V w n_max + packedWords (M + 1) gBits w := rfl
  have hl_ba : offBackAux c U V w n_max =
      offBackPtr c U V w n_max + packedWords (M * cb) gBits w := rfl
  have hl_ps : offPoolFreeStack c U V w n_max =
      offBackAux c U V w n_max + packedWords (M * cb) (12 * logLogFactor n_max + 4) w := rfl
  have hl_po : offPoolOwner c U V w n_max =
      offPoolFreeStack c U V w n_max + packedWords (poolSizeWhp n_max) gBits w := rfl
  have hl_btm : offBtMeta c U V w n_max =
      offPoolOwner c U V w n_max + packedWords (poolSizeWhp n_max) gBits w := rfl
  have hM_pos : 0 < M := Nat.two_pow_pos _
  have h0_bm : 0 < 16 * M := by omega
  have hvp_w0 : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (writePackedGenProg ((((base, offBktMeta c U V w n_max), (gBits, w)), 0), 0)) :=
    validProg_writePacked hw hgk h0_bm hbm_b
  have hw0_out : ∀ a, (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
      s_w0.mem a = s.mem a := fun a ha =>
    writePacked_outside hw _ h0_bm _ (by dsimp only [M, gBits] at hl_fb ⊢; omega)
  have hw0_odd : ∀ idx < 16 * M, idx % 2 = 1 →
      readPacked (base + offBktMeta c U V w n_max) gBits w s_w0.mem idx =
        readPacked (base + offBktMeta c U V w n_max) gBits w s.mem idx :=
    fun idx _ hmod => readPacked_writePacked_of_ne hw _ (by omega) 0
  have hw0_ev0 : ∀ x ≤ 0,
      readPacked (base + offBktMeta c U V w n_max) gBits w s_w0.mem (2 * x) = bp x := by
    intro x hx; have hx0 : x = 0 := by omega
    subst hx0; exact readPacked_writePacked_self _ _ _ _ _ (Nat.two_pow_pos _)
  -- Phase A
  obtain ⟨hfr_bp, hvp_bp, hbp_ev, hbp_odd, hout_bp⟩ :=
    bpPrefixLoop_spec (s₀ := s) henv hcsr.2.1 (htb_le.trans hps_le) hrep.2.1 M 0 s_w0
      (by omega) hw0_ev0 hw0_odd hw0_out
  rw [Nat.zero_add] at hbp_ev
  have hfb_bp : ∀ x ≤ M, readPacked (base + offFbStart c U V w n_max) gBits w s_bp.mem x =
      csr.fbStart x := fun x hx =>
    (readPacked_congr hw (hidx := show x < M + 1 by omega)
      (fun a ⟨ha1, _⟩ => hout_bp a (Or.inr ha1))).trans (hrep.2.1 x hx)
  -- Phase B
  obtain ⟨hfr_fbp, hvp_fbp, hfbp_k, hout_fbp⟩ :=
    fillBackPtrOuterLoop_spec (s₀ := s_bp) henv hcsr.2.1 (htb_le.trans hps_le) hfb_bp hbp_ev
      M 0 s_bp (by omega) (fun _ h _ _ => absurd h (Nat.not_lt_zero _)) (fun _ _ => rfl)
  rw [Nat.zero_add] at hfbp_k
  have hfb_fbp : ∀ x ≤ M, readPacked (base + offFbStart c U V w n_max) gBits w s_fbp.mem x =
      csr.fbStart x := fun x hx =>
    (readPacked_congr hw (hidx := show x < M + 1 by omega) (fun a ⟨_, ha2⟩ =>
      hout_fbp a (Or.inl (by dsimp only [M, gBits] at hl_bp ha2; omega)))).trans (hfb_bp x hx)
  -- Phase C
  have hv_pow : ∀ p, csr.vArr p < 2 ^ valBits V := by
    intro p
    have hv_max := (hqv p).2
    by_cases hV0 : V = 0
    · subst hV0; simpa [valBits] using hv_max
    · exact (lt_of_lt_of_le hv_max (max_le le_rfl (Nat.pos_of_ne_zero hV0))).trans_le
        (Nat.le_pow_clog Nat.one_lt_two V)
  have hq_fbp : ∀ i < n_max,
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s_fbp.mem i = csr.qArr i ∧
      csr.qArr i < 2 ^ quotBitsWhp U n_max := fun i hi =>
    ⟨(readPacked_congr hw (hidx := hi) (fun a ⟨_, ha2⟩ =>
        (hout_fbp a (Or.inl (by omega))).trans (hout_bp a (Or.inl (by omega))))).trans
      (hrep.2.2 i hi).1, (hqv i).1⟩
  have hv_fbp : ∀ i < n_max,
      readPacked (base + offValWhp c U w n_max) (valBits V) w s_fbp.mem i = csr.vArr i ∧
      csr.vArr i < 2 ^ valBits V := fun i hi =>
    ⟨(readPacked_congr hw (hidx := hi) (fun a ⟨_, ha2⟩ =>
        (hout_fbp a (Or.inl (by omega))).trans (hout_bp a (Or.inl (by omega))))).trans
      (hrep.2.2 i hi).2, hv_pow i⟩
  have heval := csrPermute_eval_spec (s₀ := s_fbp) henv hcsr.1 hcsr.2.1
    (fun b hb => (hbnd_good b hb).1) htb_le hfb_fbp hfbp_k
  obtain ⟨hpt_qv, hout_pt, hfr_pt, hvp_pt⟩ :=
    permuteByTargetProg_spec (mode := 2) henv hq_fbp hv_fbp heval
  -- Phase D1
  have hbp_ev_pt : ∀ x ≤ M,
      readPacked (base + offBktMeta c U V w n_max) gBits w s_pt.mem (2 * x) = bp x := fun x hx =>
    (readPacked_congr hw (hidx := show 2 * x < 16 * M by omega) (fun a ⟨ha1, ha2⟩ =>
      (hout_pt a (Or.inr (by omega))).trans
        (hout_fbp a (Or.inl (by dsimp only [M, gBits] at hl_fb ha2; omega))))).trans (hbp_ev x hx)
  obtain ⟨hfr_po, hvp_po, hpo_j, hout_po⟩ :=
    fillPoolOwnerLoop_spec (s₀ := s_pt) henv (fun b hb => (hbnd_good b hb).1) hbp_ev_pt
      (poolSizeWhp n_max) 0 s_pt (by omega) (fun _ h => absurd h (Nat.not_lt_zero _))
      (fun _ _ => rfl)
  rw [Nat.zero_add] at hpo_j
  -- Phase D2
  obtain ⟨hfr_fs, hvp_fs, hfs_j, hout_fs⟩ :=
    fillFreeStackLoop_spec (totalBack := totalBack) henv htb_le (poolSizeWhp n_max) 0 s_po
      (by omega) (fun _ h => absurd h (Nat.not_lt_zero _))
  rw [Nat.zero_add] at hfs_j
  -- Phase D3
  have hfb_fs : ∀ x ≤ M,
      readPacked (base + offFbStart c U V w n_max) gBits w s_fs.mem x = csr.fbStart x :=
    fun x hx => (readPacked_congr hw (hidx := show x < M + 1 by omega) (fun a ⟨_, ha2⟩ =>
      (hout_fs a (Or.inl (by dsimp only [M, cb, gBits] at hl_bp hl_ba hl_ps ha2; omega))).trans
        ((hout_po a (Or.inl (by
            dsimp only [M, cb, gBits] at hl_bp hl_ba hl_ps hl_po ha2; omega))).trans
          (hout_pt a (Or.inr (by omega)))))).trans (hfb_fbp x hx)
  obtain ⟨hfr_ls, hvp_ls, hls_loc, hout_ls⟩ :=
    fillLocStateOuterLoop_spec (s₀ := s_fs) henv hcsr.2.1 hfb_fs M 0 s_fs (by omega)
      (fun _ h _ _ => absurd h (Nat.not_lt_zero _)) (fun _ _ => rfl)
  rw [Nat.zero_add] at hls_loc
  -- Phase E1
  obtain ⟨hfr_ras, hvp_ras, hras_sl, hras_salt, hout_ras⟩ :=
    resetAllSlicesLoop_spec henv (3 * M) 0 s_ls (by omega) (fun _ h => absurd h (Nat.not_lt_zero _))
  rw [Nat.zero_add] at hras_sl
  have hras_to_pt : ∀ a,
      (a < base + offLocState c U V w n_max ∨
        (base + offFbStart c U V w n_max ≤ a ∧ a < base + offPoolFreeStack c U V w n_max) ∨
        base + offBtMeta c U V w n_max ≤ a) →
      s_ras.mem a = s_pt.mem a := by
    intro a ha
    rcases ha with ha1 | ⟨ha1, ha2⟩ | ha1
    · exact (hout_ras a (Or.inl (by omega))).trans
        ((hout_ls a (Or.inl ha1)).trans
          ((hout_fs a (Or.inl (by omega))).trans (hout_po a (Or.inl (by omega)))))
    · exact (hout_ras a (Or.inr ha1)).trans
        ((hout_ls a (Or.inr (by omega))).trans
          ((hout_fs a (Or.inl ha2)).trans (hout_po a (Or.inl (by omega)))))
    · exact (hout_ras a (Or.inr (by omega))).trans
        ((hout_ls a (Or.inr (by omega))).trans
          ((hout_fs a (Or.inr (by omega))).trans (hout_po a (Or.inr ha1))))
  have hras_outside : ∀ a, (a < base + offQuotWhp c w n_max ∨ base + offBtMeta c U V w n_max ≤ a) →
      s_ras.mem a = s.mem a := by
    intro a ha
    rcases ha with ha_lo | ha_hi
    · exact (hras_to_pt a (Or.inl (by omega))).trans
        ((hout_pt a (Or.inl ha_lo)).trans
          ((hout_fbp a (Or.inl (by omega))).trans (hout_bp a (Or.inl (by omega)))))
    · exact (hras_to_pt a (Or.inr (Or.inr ha_hi))).trans
        ((hout_pt a (Or.inr (by omega))).trans
          ((hout_fbp a (Or.inr (by omega))).trans (hout_bp a (Or.inr (by omega)))))
  refine ⟨htb_le, hbp_ev M le_rfl,
    hfr_ras.trans (hfr_ls.trans
      (hfr_fs.trans (hfr_po.trans (hfr_pt.trans (hfr_fbp.trans hfr_bp))))),
    SeedWhpMemRep.congr_hash hw (fun a _ ha2 => (hras_outside a (Or.inl ha2)).symm) hseed,
    ?_, ?_, ?_, ?_, ?_, hras_sl, ?_, hras_outside,
    hvp_w0, hvp_bp, hvp_fbp, hvp_pt, hvp_po, hvp_fs, hvp_ls, hvp_ras⟩
  · intro x hx
    have ha_fn : ∀ a, base + offFbStart c U V w n_max ≤ a →
        a < base + offFbStart c U V w n_max + packedWords (M + 1) gBits w →
        s_ras.mem a = s_pt.mem a := by
      intro a ha1 ha2
      refine hras_to_pt a (Or.inr (Or.inl ⟨ha1, ?_⟩))
      dsimp only [M, cb, gBits] at hl_bp hl_ba hl_ps ha2; omega
    exact (readPacked_congr hw (hidx := show x < M + 1 by omega)
        (fun a ⟨ha1, ha2⟩ => ha_fn a ha1 ha2)).trans
      ((readPacked_congr hw (hidx := show x < M + 1 by omega)
        (fun a ⟨ha1, _⟩ => hout_pt a (Or.inr (by omega)))).trans (hfb_fbp x hx))
  · intro i hi
    exact ⟨(readPacked_congr hw (hidx := hi)
        (fun a ⟨_, ha2⟩ => hras_to_pt a (Or.inl (by omega)))).trans (hpt_qv i hi).1,
      (readPacked_congr hw (hidx := hi)
        (fun a ⟨_, ha2⟩ => hras_to_pt a (Or.inl (by omega)))).trans (hpt_qv i hi).2⟩
  · intro b hb loc hloc
    rw [readPacked_congr hw (hidx := mul_add_lt_mul_bound hb hloc)
      (fun a ⟨_, ha2⟩ => hout_ras a (Or.inl (by dsimp only [M] at hl_bm ha2; omega))),
      hls_loc b hb loc hloc]
    dsimp only [bktCnt]; simp only [hb, ↓reduceIte]
  · intro b hb k hk
    have ha_fn : ∀ a, base + offBackPtr c U V w n_max ≤ a →
        a < base + offBackPtr c U V w n_max + packedWords (M * cb) gBits w →
        s_ras.mem a = s_pt.mem a := by
      intro a ha1 ha2
      refine hras_to_pt a (Or.inr (Or.inl ⟨by omega, ?_⟩))
      dsimp only [M, cb, gBits] at hl_ba hl_ps ha2; omega
    rw [readPacked_congr hw (hidx := mul_add_lt_mul_bound hb hk)
        (fun a ⟨ha1, ha2⟩ => ha_fn a ha1 ha2),
      readPacked_congr hw (hidx := mul_add_lt_mul_bound hb hk)
        (fun a ⟨ha1, _⟩ => hout_pt a (Or.inr (by omega))),
      hfbp_k b hb k hk]
    dsimp only [backPtr, bktCnt]
    by_cases hk' : k < (csr.fbStart (b + 1) - csr.fbStart b) - cf
    · rw [ite_eq_left hk', ite_eq_left ⟨hb, by simp only [hb, ↓reduceIte]; exact hk'⟩]
    · have hnot : ¬(b < M ∧ k < (if b < M then csr.fbStart (b + 1) - csr.fbStart b else 0) - cf) :=
        fun h => hk' (by have h2 := h.2; simp only [hb, ↓reduceIte] at h2; exact h2)
      rw [ite_eq_right hk', ite_eq_right hnot]
  · intro j hj
    exact ⟨(readPacked_congr hw (hidx := hj) (fun a ⟨ha1, _⟩ =>
        (hout_ras a (Or.inr (by omega))).trans (hout_ls a (Or.inr (by omega))))).trans
        (hfs_j j hj),
      (readPacked_congr hw (hidx := hj) (fun a ⟨ha1, _⟩ =>
        (hout_ras a (Or.inr (by omega))).trans
          ((hout_ls a (Or.inr (by omega))).trans (hout_fs a (Or.inr ha1))))).trans
        (hpo_j j hj)⟩
  · intro b hb
    have hidx : 16 * b + 1 < 16 * M := by omega
    have ha_ls_bp : ∀ a, base + offBktMeta c U V w n_max ≤ a →
        a < base + offBktMeta c U V w n_max + packedWords (16 * M) gBits w →
        s_ls.mem a = s_bp.mem a := by
      intro a ha1 ha2
      dsimp only [M, cb, gBits] at hl_fb hl_bp hl_ba hl_ps ha2
      exact (hout_ls a (Or.inr ha1)).trans
        ((hout_fs a (Or.inl (by omega))).trans
          ((hout_po a (Or.inl (by omega))).trans
            ((hout_pt a (Or.inr (by omega))).trans (hout_fbp a (Or.inl (by omega))))))
    have hbp0 : buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) csr.fbStart 0 = 0 :=
      (backPrefix_spec _ _ _).1
    rw [hbp0] at hbp_odd
    rw [hras_salt (16 * b + 1) hidx (by omega),
      readPacked_congr hw (hidx := hidx) (fun a ⟨ha1, ha2⟩ => ha_ls_bp a ha1 ha2)]
    dsimp only [s_bp, rt, gBits]
    rw [hbp_odd (16 * b + 1) hidx (by omega)]
    exact hsalts_mem b hb

private def CsrToFastPart1Pre (w : ℕ) (d : WhpCoreParams × ℕ) (_s : Memory.State) : Prop :=
  WhpLargeEnvGen w d.1 d.2

private theorem realizes_csrToFastPart1a :
    Realizes .exact csrToFastPart1aProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := ℕ))
      CsrToFastPart1Pre
      (fun _ _ => 0) := by
  unfold csrToFastPart1aProg
  have hmr := realizes_mkHealRtGen
  have hmp := realizes_mkPermRtGen
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  have hbp := realizes_bpPrefixLoop
  have hfbp := realizes_fillBackPtrOuterLoop
  have hpt := realizes_permuteByTarget
  have hcs_rp : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' :=
    fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨cp, base⟩
    dsimp only [CsrToFastPart1Pre, WhpLargeEnvGen] at h
    obtain ⟨c, U, V, w₀, n_max, henv, rfl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hM_pos : 0 < numBucketsWhp n_max := Nat.two_pow_pos _
    obtain ⟨hM_lt, h16M, _, _, _, _, _, _⟩ := hl_bounds henv
    obtain ⟨hmr_st, hmr_res, _⟩ := mkHealRtGenProg_spec (c := c) (U := U) (V := V) (w := w)
      (n_max := n_max) (base := base) hth s
    obtain ⟨hmp_st, hmp_res, _, _⟩ := mkPermRtGenProg_spec (c := c) (U := U) (V := V) (w := w)
      (n_max := n_max) (base := base) hth s
    simp only [hmr_st, hmr_res, hmp_st, hmp_res, hcs_rp,
      hlBase_mk, hlW_mk, hlM_mk, hlGBits_mk, hlOffBm_mk, Prod.mk.eta] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact to_true_exists (henv.bktMeta_safe (idx := 0) (by omega))
    | exact to_true_exists (henv.bktMeta_safe (idx := 2 * numBucketsWhp n_max) (by omega))
    | exact bpPrefixLoop_safe henv (numBucketsWhp n_max) 0 0 _ (by omega)
    | exact fillBackPtrOuterLoop_safe henv (numBucketsWhp n_max) 0 _ (by omega)
  )

private theorem realizes_csrToFastPart1b :
    Realizes .exact csrToFastPart1bProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => WhpLargeEnvGen w d.1.1 d.1.2)
      (fun _ _ => 0) := by
  unfold csrToFastPart1bProg
  have hmr := realizes_mkHealRtGen
  have hcs := realizes_clampSub
  have hfpo := realizes_fillPoolOwnerLoop
  have hffs := realizes_fillFreeStackLoop
  have hfls := realizes_fillLocStateOuterLoop
  have hras := realizes_resetAllSlicesLoop
  have hcs_cl : ∀ y s', (Memory.spec 0).clientState s' (clampSubProg y) = s' :=
    clientState_clampSubProg
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, tb⟩
    dsimp only [WhpLargeEnvGen] at h
    obtain ⟨c, U, V, w₀, n_max, henv, rfl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    obtain ⟨_, h16M, _, _, _, _, _, _⟩ := hl_bounds henv
    obtain ⟨hmr_st, hmr_res, _⟩ := mkHealRtGenProg_spec (c := c) (U := U) (V := V) (w := w)
      (n_max := n_max) (base := base) hth s
    simp only [hmr_st, hmr_res, hcs_cl, hlM_mk, hlPoolSize_mk, Prod.mk.eta] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact fillPoolOwnerLoop_safe henv (poolSizeWhp n_max) 0 _ (by omega)
    | exact fillFreeStackLoop_safe henv (poolSizeWhp n_max) 0 _ (by omega)
    | exact fillLocStateOuterLoop_safe henv (numBucketsWhp n_max) 0 _ (by omega)
    | exact resetAllSlicesLoop_safe henv (3 * numBucketsWhp n_max) 0 _ (by omega)
  )

private theorem realizes_csrToFastPart1 :
    Realizes .exact csrToFastPart1Prog
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := ℕ))
      CsrToFastPart1Pre
      (fun _ _ => 0) := by
  unfold csrToFastPart1Prog
  have h1a := realizes_csrToFastPart1a
  have h1b := realizes_csrToFastPart1b
  realize
  all_goals (
    rcases d with ⟨cp, base⟩
    exact h
  )

private theorem csrToFastPart1Prog_eq {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {csr : CsrState} {dict : Dictionary.State U} {salts : ℕ → ℕ}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : CsrMemRep base c U V w n_max csr s.mem)
    (hcsr : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict)
    (hqv : ∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1)
    (hgood : GoodSeedOnState c U n_max θ dict)
    (hsalts_mem : ∀ b < numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem (16 * b + 1) =
        salts b) :
    let cp := mkWhpCoreParams c U V w n_max
    let rt := mkHealRt c U V w n_max base
    let prt := mkPermRt c U V w n_max base
    let M := numBucketsWhp n_max
    let gBits := globalPtrBits n_max
    let totalBack := buildBackPrefix M (capFrontWhp n_max) csr.fbStart M
    let freeTop := poolSizeWhp n_max - totalBack
    let s_w0 := (Memory.spec 0).clientState s
      (writePackedGenProg ((((base, offBktMeta c U V w n_max), (gBits, w)), 0), 0))
    let s_bp := (Memory.spec 0).clientState s_w0 (bpPrefixLoopProg ((rt, (0, 0)), M))
    let s_fbp := (Memory.spec 0).clientState s_bp (fillBackPtrOuterLoopProg ((rt, 0), M))
    let s_pt := (Memory.spec 0).clientState s_fbp (permuteByTargetProg (prt, 2))
    let s_po := (Memory.spec 0).clientState s_pt
      (fillPoolOwnerLoopProg (((rt, totalBack), 0), poolSizeWhp n_max))
    let s_fs := (Memory.spec 0).clientState s_po
      (fillFreeStackLoopProg (((rt, (totalBack, freeTop)), 0), poolSizeWhp n_max))
    let s_ls := (Memory.spec 0).clientState s_fs (fillLocStateOuterLoopProg ((rt, 0), M))
    let s_ras := (Memory.spec 0).clientState s_ls (resetAllSlicesLoopProg (((cp, base), 0), 3 * M))
    StepSpec w (base + largeSpaceWhp c U V w n_max) s
      (csrToFastPart1Prog (cp, base)) s_ras freeTop := by
  intro cp rt prt M gBits totalBack freeTop s_w0 s_bp s_fbp s_pt s_po s_fs s_ls s_ras
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  obtain ⟨_, h16M, _, _, _, _, _, _⟩ := hl_bounds henv
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max + packedWords (16 * M) gBits w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  obtain ⟨hmr_st, hmr_res, hmr_vp⟩ := mkHealRtGenProg_spec (c := c) (U := U) (V := V) (w := w)
    (n_max := n_max) (base := base) hth s
  obtain ⟨hmp_st, hmp_res, _, hmp_vp⟩ := mkPermRtGenProg_spec (c := c) (U := U) (V := V) (w := w)
    (n_max := n_max) (base := base) hth s
  obtain ⟨hmr_pt_st, hmr_pt_res, hmr_pt_vp⟩ := mkHealRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) hth s_pt
  obtain ⟨htb_le, htb_rd, _, _, _, _, _, _, _, _, _, _,
    hvp_w0, hvp_bp, hvp_fbp, hvp_pt, hvp_po, hvp_fs, hvp_ls, hvp_ras⟩ :=
    csrToFast_phases_A_to_E1 henv hseed hrep hcsr hqv hgood hsalts_mem
  obtain ⟨hcl_st, hcl_res, hcl_vp⟩ :=
    clampSubProg_spec (w := w) (F := base + largeSpaceWhp c U V w n_max) htb_le s_pt
  have hM_pos : 0 < M := Nat.two_pow_pos _
  dsimp only [cp] at hmr_st hmr_res hmr_vp hmp_st hmp_res hmp_vp hmr_pt_st hmr_pt_res hmr_pt_vp
  have h1a : StepSpec w (base + largeSpaceWhp c U V w n_max) s
      (csrToFastPart1aProg (cp, base)) s_pt totalBack := by
    unfold csrToFastPart1aProg
    simp only [pure_bind]
    refine StepSpec.bind ⟨hmr_st, hmr_res, hmr_vp⟩ ?_
    refine StepSpec.bind ⟨hmp_st, hmp_res, hmp_vp⟩ ?_
    simp only [hlBase_mk, hlW_mk, hlM_mk, hlGBits_mk, hlOffBm_mk]
    refine StepSpec.bind ⟨rfl, rfl, hvp_w0⟩ ?_
    refine StepSpec.bind ⟨rfl, rfl, hvp_bp⟩ ?_
    refine (StepSpec.readPackedGen_eq hw (by omega) hbm_b htb_rd).bind ?_
    refine StepSpec.bind ⟨rfl, rfl, hvp_fbp⟩ ?_
    exact StepSpec.bind ⟨rfl, rfl, hvp_pt⟩ (StepSpec.pure _ _)
  have h1b : StepSpec w (base + largeSpaceWhp c U V w n_max) s_pt
      (csrToFastPart1bProg ((cp, base), totalBack)) s_ras freeTop := by
    unfold csrToFastPart1bProg
    simp only [pure_bind]
    refine StepSpec.bind ⟨hmr_pt_st, hmr_pt_res, hmr_pt_vp⟩ ?_
    simp only [hlM_mk, hlPoolSize_mk]
    refine StepSpec.bind ⟨hcl_st, hcl_res, hcl_vp⟩ ?_
    refine StepSpec.bind ⟨rfl, rfl, hvp_po⟩ ?_
    refine StepSpec.bind ⟨rfl, rfl, hvp_fs⟩ ?_
    refine StepSpec.bind ⟨rfl, rfl, hvp_ls⟩ ?_
    exact StepSpec.bind ⟨rfl, rfl, hvp_ras⟩ (StepSpec.pure _ _)
  unfold csrToFastPart1Prog
  simp only [pure_bind]
  exact h1a.bind h1b

/-- Precondition for `csrToFastGenProg` (`d = (wp, base)`). -/
@[expose] def CsrToFastPre (w : ℕ) (d : WhpParams × ℕ) (s : Memory.State) : Prop :=
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (csr : CsrState) (dict : Dictionary.State U)
      (salts : ℕ → ℕ),
    WhpLargeEnv c U V w₀ n_max w d.2 ∧
    d.1 = mkWhpParams c U V w₀ n_max ∧
    SeedWhpMemRep d.2 c U w₀ n_max θ s.mem ∧
    CsrMemRep d.2 c U V w₀ n_max csr s.mem ∧
    ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict ∧
    (∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1) ∧
    GoodSeedOnState c U n_max θ dict ∧
    (∀ b < numBucketsWhp n_max,
      readPacked (d.2 + offBktMeta c U V w₀ n_max) (globalPtrBits n_max) w s.mem (16 * b + 1) =
        salts b)

/-- `Realizes .exact` certificate for `csrToFastGenProg`. -/
theorem realizes_csrToFastGen :
    Realizes .exact csrToFastGenProg
      (WordEncoding.encode (α := WhpParams × ℕ))
      (WordEncoding.encode (α := Unit))
      CsrToFastPre
      (fun _ _ => 0) := by
  unfold csrToFastGenProg
  have hp1 := realizes_csrToFastPart1
  have hmr := realizes_mkHealRtGen
  have hmh := realizes_mkHashRtGen
  have hbab := realizes_buildAllBucketsOuterLoop
  have hffm := realizes_fillFinalBktMetaLoop
  have hztc := realizes_zeroTrieChildrenLoop
  have hwhd := realizes_writeHealHdrsAndTrieMeta
  realize
  all_goals (
    rcases d with ⟨wp, base⟩
    dsimp only [CsrToFastPre] at h
    obtain ⟨c, U, V, w₀, n_max, θ, csr, dict, salts, henv, rfl, hseed, hrep, hcsr, hqv, hgood,
      hsalts_mem⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      unfold mkWhpParams; rw [ite_eq_right (Nat.not_lt.mpr hth)]
    obtain ⟨hp1_st, hp1_res, _⟩ := csrToFastPart1Prog_eq henv hseed hrep hcsr hqv hgood hsalts_mem
    let s_ras := (Memory.spec 0).clientState s
      (csrToFastPart1Prog (mkWhpCoreParams c U V w n_max, base))
    obtain ⟨hmr_st, hmr_res, _⟩ := mkHealRtGenProg_spec (c := c) (U := U) (V := V) (w := w)
      (n_max := n_max) (base := base) hth s_ras
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w)
      (n_max := n_max) (base := base) hth s_ras
    dsimp only [s_ras] at hmr_st hmr_res hmh_st hmh_res
    obtain ⟨_, _, _, hseed_ras, _, _, _, _, _, hras_sl, _, _,
      _, _, _, _, _, _, _, _⟩ :=
      csrToFast_phases_A_to_E1 henv hseed hrep hcsr hqv hgood hsalts_mem
    rw [← hp1_st] at hseed_ras hras_sl
    simp only [hwp1] at *
    simp only [hp1_res, hmr_st, hmr_res, hmh_st, hmh_res, Prod.mk.eta,
      wp_large_offTrieChild0 hth, wp_large_offTrieChild1 hth,
      wp_large_offTrieMeta0 hth, wp_large_offTrieMeta1 hth] at *
    dsimp only [mkHealRt, hlM, hlTcEntries] at *
    first
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact buildAllBucketsOuterLoop_safe henv (numBucketsWhp n_max) 0 _ (by omega) hseed_ras
        (fun sIdx hsIdx _ => hras_sl sIdx hsIdx)
    | exact fillFinalBktMetaLoop_safe henv (numBucketsWhp n_max) 0 _ (by omega)
    | exact zeroTrieChildrenLoop_safe henv (trieChildEntriesWhp c n_max) 0 _ (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl, rfl, rfl⟩
  )

/-- Exact specification of `csrToFastGenProg`: refines `csrToFast c U n_max θ csr salts` into
`FastMemRep` while preserving `SeedWhpMemRep`, `frontier`, and caller memory outside
`[base, base + largeSpaceWhp c U V w n_max)`. -/
theorem csrToFastGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {csr : CsrState} {dict : Dictionary.State U} {salts : ℕ → ℕ}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : CsrMemRep base c U V w n_max csr s.mem)
    (hcsr : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict)
    (hqv : ∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1)
    (hgood : GoodSeedOnState c U n_max θ dict)
    (hsalts_mem : ∀ b < numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem (16 * b + 1) =
        salts b) :
    let prog := csrToFastGenProg (mkWhpParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    SeedWhpMemRep base c U w n_max θ s'.mem ∧
    FastMemRep base c U V w n_max (csrToFast c U n_max θ csr salts) s'.mem ∧
    s'.frontier = s.frontier ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    (∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  obtain ⟨_, h16M, _, hps_le, _, _, _, _⟩ := hl_bounds henv
  obtain ⟨hbnd_good, _⟩ := csrToFast_bounds_of_good hth hcsr hgood
  obtain ⟨_, hbp_adj, _, hbp_mono⟩ := backPrefix_spec (numBucketsWhp n_max) (capFrontWhp n_max)
    csr.fbStart
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    unfold mkWhpParams; rw [ite_eq_right (Nat.not_lt.mpr hth)]
  set cp := mkWhpCoreParams c U V w n_max
  set rt := mkHealRt c U V w n_max base
  set prt := mkPermRt c U V w n_max base
  set hrt := mkHashRt c U w n_max base
  set M := numBucketsWhp n_max
  set cf := capFrontWhp n_max
  set cb := capBackWhp n_max
  set gBits := globalPtrBits n_max
  set bp := buildBackPrefix M cf csr.fbStart
  set totalBack := bp M
  set freeTop := poolSizeWhp n_max - totalBack
  have hp1_step := csrToFastPart1Prog_eq henv hseed hrep hcsr hqv hgood hsalts_mem
  obtain ⟨htb_le, _, hfr_ras, hseed_ras, hfb_ras, hqv_ras, hls_ras, hbp_ras, hpool_ras,
    hras_sl, hsalts_ras, hout_ras,
    _, _, _, _, _, _, _, _⟩ :=
    csrToFast_phases_A_to_E1 henv hseed hrep hcsr hqv hgood hsalts_mem
  set s_w0 := (Memory.spec 0).clientState s
    (writePackedGenProg ((((base, offBktMeta c U V w n_max), (gBits, w)), 0), 0))
  set s_bp := (Memory.spec 0).clientState s_w0 (bpPrefixLoopProg ((rt, (0, 0)), M))
  set s_fbp := (Memory.spec 0).clientState s_bp (fillBackPtrOuterLoopProg ((rt, 0), M))
  set s_pt := (Memory.spec 0).clientState s_fbp (permuteByTargetProg (prt, 2))
  set s_po := (Memory.spec 0).clientState s_pt
    (fillPoolOwnerLoopProg (((rt, totalBack), 0), poolSizeWhp n_max))
  set s_fs := (Memory.spec 0).clientState s_po
    (fillFreeStackLoopProg (((rt, (totalBack, freeTop)), 0), poolSizeWhp n_max))
  set s_ls := (Memory.spec 0).clientState s_fs (fillLocStateOuterLoopProg ((rt, 0), M))
  set s_ras := (Memory.spec 0).clientState s_ls (resetAllSlicesLoopProg (((cp, base), 0), 3 * M))
  obtain ⟨hmr_st, hmr_res, hmr_vp⟩ := mkHealRtGenProg_spec (c := c) (U := U) (V := V) (w := w)
    (n_max := n_max) (base := base) hth s_ras
  obtain ⟨hmh_st, hmh_res, _, hmh_vp⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w)
    (n_max := n_max) (base := base) hth s_ras
  -- Phase E2: `buildAllBucketsOuterLoopProg`
  let bktCnt : ℕ → ℕ := fun b => if b < M then csr.fbStart (b + 1) - csr.fbStart b else 0
  let backPtr : ℕ → ℕ → ℕ := fun b k =>
    if b < M ∧ k < bktCnt b - cf then bp b + k else 0
  have hbp_ps : ∀ b < M, ∀ k < (csr.fbStart (b + 1) - csr.fbStart b) - cf,
      backPtr b k < poolSizeWhp n_max := by
    intro b hb k hk
    dsimp only [backPtr, bktCnt]
    rw [ite_eq_left ⟨hb, by simp only [hb, ↓reduceIte]; exact hk⟩]
    have h1 : bp (b + 1) = bp b + ((csr.fbStart (b + 1) - csr.fbStart b) - cf) := hbp_adj b hb
    have h2 : bp (b + 1) ≤ totalBack := hbp_mono (b + 1) M hb le_rfl
    omega
  obtain ⟨hfr_bab, hvp_bab, hbab_sl, hbab_salts, hout_bab⟩ :=
    buildAllBucketsOuterLoop_spec (salts := salts) (s₀ := s_ras)
      henv hcsr.2.1 hbnd_good hbp_ps hseed_ras hfb_ras (fun i hi => (hqv_ras i hi).1) hbp_ras
      M 0 s_ras (by omega)
      (fun sIdx hsIdx => by simp only [Nat.not_lt_zero, ↓reduceIte]; exact hras_sl sIdx hsIdx)
      hsalts_ras (fun _ _ => rfl)
  rw [Nat.zero_add] at hbab_sl
  set s_bab := (Memory.spec 0).clientState s_ras
    (buildAllBucketsOuterLoopProg ((((cp, base), (rt, hrt)), 0), M))
  -- Phase F: `fillFinalBktMetaLoopProg`
  have hfb_mono := fbStart_mono_of_adj hcsr.2.1
  have hfb_bab : ∀ x ≤ M, readPacked (base + offFbStart c U V w n_max) gBits w s_bab.mem x =
      csr.fbStart x := fun x hx =>
    (readPacked_congr hw (hidx := show x < M + 1 by omega) (fun a ⟨ha1, ha2⟩ =>
      hout_bab a (Or.inr (Or.inl ⟨ha1, by
        have h6 : offBackPtr c U V w n_max =
          offFbStart c U V w n_max + packedWords (M + 1) gBits w := rfl
        dsimp only [M, gBits] at h6 ha2
        unfold offBtMeta offPoolOwner offPoolFreeStack offBackAux; omega⟩)))).trans (hfb_ras x hx)
  have hfb_adj_n : ∀ b < M, csr.fbStart b ≤ csr.fbStart (b + 1) ∧
      csr.fbStart (b + 1) - csr.fbStart b ≤ n_max := fun b hb =>
    ⟨hcsr.2.1 b hb,
      Nat.sub_le_of_le_add ((hfb_mono (b + 1) M hb le_rfl).trans hcsr.2.2.1 |>.trans
        (Nat.le_add_right _ _))⟩
  obtain ⟨hfr_ffm, hvp_ffm, hffm_bm, hffm_keep, hout_ffm⟩ :=
    fillFinalBktMetaLoop_spec (s₀ := s_bab) henv hfb_adj_n hfb_bab M 0 s_bab (by omega)
      (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ _ _ => rfl) (fun _ _ => rfl)
  rw [Nat.zero_add] at hffm_bm
  set s_ffm := (Memory.spec 0).clientState s_bab (fillFinalBktMetaLoopProg ((rt, 0), M))
  -- Phase G1: `zeroTrieChildrenLoopProg`
  obtain ⟨hfr_ztc, hvp_ztc, hztc_ch, hout_ztc⟩ :=
    zeroTrieChildrenLoop_spec henv (trieChildEntriesWhp c n_max) 0 s_ffm (by omega)
      (fun _ h => absurd h (Nat.not_lt_zero _))
  rw [Nat.zero_add] at hztc_ch
  set s_ztc := (Memory.spec 0).clientState s_ffm
    (zeroTrieChildrenLoopProg
      (((rt, (offTrieChild0 c U V w n_max, offTrieChild1 c U V w n_max)), 0),
       trieChildEntriesWhp c n_max))
  -- Phase G2: `writeHealHdrsAndTrieMetaProg`
  have hft_fit : Fits w freeTop := henv.fits_of_le_n_max ((Nat.sub_le _ _).trans hps_le)
  obtain ⟨hfr_whd, hvp_whd, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
    hm12, hm13, hm14, hm15, htm0_2, htm1_2, hout_whd⟩ :=
    writeHealHdrsAndTrieMetaProg_spec henv hft_fit s_ztc
  set s_fin := (Memory.spec 0).clientState s_ztc
    (writeHealHdrsAndTrieMetaProg
      ((rt, (offTrieMeta0 c U V w n_max, offTrieMeta1 c U V w n_max)), freeTop))
  have hch := largeOffsetChain c U V w n_max
  have h32_q : 32 ≤ offQuotWhp c w n_max := by omega
  have hq_bm : offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w ≤
      offValWhp c U w n_max ∧
      offValWhp c U w n_max + packedWords n_max (valBits V) w ≤ offLocState c U V w n_max ∧
      offLocState c U V w n_max + packedWords (M * totalLocalCoordsWhp n_max) 2 w =
        offBktMeta c U V w n_max ∧
      offBktMeta c U V w n_max + packedWords (16 * M) gBits w = offFbStart c U V w n_max ∧
      offFbStart c U V w n_max ≤ offBackPtr c U V w n_max ∧
      offBackPtr c U V w n_max + packedWords (M * cb) gBits w ≤ offPoolFreeStack c U V w n_max ∧
      offPoolFreeStack c U V w n_max + packedWords (poolSizeWhp n_max) gBits w =
        offPoolOwner c U V w n_max ∧
      offPoolOwner c U V w n_max + packedWords (poolSizeWhp n_max) gBits w =
        offBtMeta c U V w n_max ∧
      offBtMeta c U V w n_max ≤ offTrieChild0 c U V w n_max ∧
      offTrieChild0 c U V w n_max ≤ offTrieMeta0 c U V w n_max ∧
      offTrieItems0 c U V w n_max ≤ largeSpaceWhp c U V w n_max := by
    dsimp only [M, gBits, cb]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega⟩
  have hfin_to_ffm : ∀ a, base + 16 ≤ a → a < base + offTrieChild0 c U V w n_max →
      s_fin.mem a = s_ffm.mem a := fun a ha1 ha2 =>
    (hout_whd a (Or.inr (Or.inl ⟨ha1, by omega⟩))).trans (hout_ztc a (Or.inl ha2))
  have hfin_to_ras_nonBmBt : ∀ a, base + 16 ≤ a →
      (a < base + offBktMeta c U V w n_max ∨
        (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max)) →
      s_fin.mem a = s_ras.mem a := by
    intro a ha16 ha_mid
    rcases ha_mid with ha_lo | ⟨ha_fb, ha_bt⟩
    · exact (hfin_to_ffm a ha16 (by omega)).trans
        ((hout_ffm a (Or.inl ha_lo)).trans (hout_bab a (Or.inl ha_lo)))
    · exact (hfin_to_ffm a ha16 (by omega)).trans
        ((hout_ffm a (Or.inr ha_fb)).trans (hout_bab a (Or.inr (Or.inl ⟨ha_fb, ha_bt⟩))))
  have htot_step : StepSpec w (base + largeSpaceWhp c U V w n_max) s
      (csrToFastGenProg (mkWhpParams c U V w n_max, base)) s_fin () := by
    unfold csrToFastGenProg; dsimp only
    simp only [pure_bind]
    rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    refine hp1_step.bind ?_
    dsimp only [cp] at hmr_st hmr_res hmr_vp ⊢
    refine StepSpec.bind ⟨hmr_st, hmr_res, hmr_vp⟩ ?_
    refine StepSpec.bind ⟨hmh_st, hmh_res, hmh_vp⟩ ?_
    dsimp only [mkHealRt, hlM, hlTcEntries]
    simp only [wp_large_offTrieChild0 hth, wp_large_offTrieChild1 hth,
      wp_large_offTrieMeta0 hth, wp_large_offTrieMeta1 hth]
    dsimp only [cp, rt, hrt, M] at hvp_bab hvp_ffm hvp_ztc hvp_whd s_bab s_ffm s_ztc s_fin ⊢
    refine StepSpec.bind ⟨rfl, rfl, hvp_bab⟩ ?_
    refine StepSpec.bind ⟨rfl, rfl, hvp_ffm⟩ ?_
    exact StepSpec.bind ⟨rfl, rfl, hvp_ztc⟩ ⟨rfl, rfl, hvp_whd⟩
  refine ⟨?_, ?_, ?_, htot_step.2.2, fun a ha => ?_⟩
  · rw [htot_step.1]
    refine SeedWhpMemRep.congr_hash hw (fun a ha1 ha2 => ?_) hseed_ras
    dsimp only [offHashBkt] at ha1
    exact (hfin_to_ras_nonBmBt a (by omega) (Or.inl (by omega))).symm
  · rw [htot_step.1]
    have hmt_pos : 1 ≤ maxTrieNodesWhp c n_max := by unfold maxTrieNodesWhp; omega
    dsimp only [FastMemRep, csrToFast]
    refine ⟨Nat.zero_le _, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    · intro i hi
      exact ⟨(readPacked_congr hw (hidx := hi) (fun a ⟨ha1, ha2⟩ =>
          hfin_to_ras_nonBmBt a (by omega) (Or.inl (by omega)))).trans (hqv_ras i hi).1,
        (readPacked_congr hw (hidx := hi) (fun a ⟨ha1, ha2⟩ =>
          hfin_to_ras_nonBmBt a (by omega) (Or.inl (by omega)))).trans (hqv_ras i hi).2⟩
    · intro b hb loc hloc
      rw [readPacked_congr hw (hidx := mul_add_lt_mul_bound hb hloc) (fun a ⟨ha1, ha2⟩ =>
        hfin_to_ras_nonBmBt a (by omega) (Or.inl (by
          dsimp only [M] at hq_bm ha2; omega))),
        hls_ras b hb loc hloc]
      dsimp only [bktCnt]
      by_cases hlt : loc < csr.fbStart (b + 1) - csr.fbStart b
      · rw [ite_eq_left (by rwa [ite_eq_left hb]),
          ite_eq_left ⟨hb, by rwa [ite_eq_left hb]⟩]
      · have hnot : ¬(b < M ∧ loc < if b < M then csr.fbStart (b + 1) - csr.fbStart b else 0) :=
          fun h => hlt (by have h2 := h.2; rwa [ite_eq_left hb] at h2)
        rw [ite_eq_right (by rwa [ite_eq_left hb]), ite_eq_right hnot]
    · intro b hb
      have hbm_fin_eq : ∀ idx < 16 * M,
          readPacked (base + offBktMeta c U V w n_max) gBits w s_fin.mem idx =
            readPacked (base + offBktMeta c U V w n_max) gBits w s_ffm.mem idx :=
        fun idx hidx => readPacked_congr hw (hidx := hidx)
          (fun a ⟨ha1, ha2⟩ =>
            hfin_to_ffm a (by omega) (by dsimp only [M, gBits] at hq_bm ha2; omega))
      have hf := hffm_bm b hb
      have hs_b : readPacked (base + offBktMeta c U V w n_max) gBits w s_ffm.mem (16 * b + 1) =
          salts b :=
        (hffm_keep (16 * b + 1) (by omega) (Or.inl (by omega))).trans (hbab_salts b hb)
      simp only [hb, ↓reduceIte]
      exact ⟨(hbm_fin_eq _ (by omega)).trans hf.1,
        (hbm_fin_eq _ (by omega)).trans hs_b,
        (hbm_fin_eq _ (by omega)).trans hf.2.1,
        (hbm_fin_eq _ (by omega)).trans hf.2.2.1,
        (hbm_fin_eq _ (by omega)).trans hf.2.2.2.1,
        (hbm_fin_eq _ (by omega)).trans hf.2.2.2.2.1,
        (hbm_fin_eq _ (by omega)).trans hf.2.2.2.2.2.1,
        (hbm_fin_eq _ (by omega)).trans hf.2.2.2.2.2.2.1,
        (hbm_fin_eq _ (by omega)).trans hf.2.2.2.2.2.2.2.1,
        (hbm_fin_eq _ (by omega)).trans hf.2.2.2.2.2.2.2.2⟩
    · intro b hb k hk
      exact (readPacked_congr hw (hidx := mul_add_lt_mul_bound hb hk) (fun a ⟨ha1, ha2⟩ =>
        hfin_to_ras_nonBmBt a (by omega) (Or.inr ⟨by omega, by
          dsimp only [M, cb, gBits] at hq_bm ha2; omega⟩))).trans (hbp_ras b hb k hk)
    · intro j hj
      exact ⟨(readPacked_congr hw (hidx := hj) (fun a ⟨ha1, ha2⟩ =>
          hfin_to_ras_nonBmBt a (by omega) (Or.inr ⟨by omega, by
            dsimp only [gBits] at hq_bm ha2; omega⟩))).trans (hpool_ras j hj).1,
        (readPacked_congr hw (hidx := hj) (fun a ⟨ha1, ha2⟩ =>
          hfin_to_ras_nonBmBt a (by omega) (Or.inr ⟨by omega, by
            dsimp only [gBits] at hq_bm ha2; omega⟩))).trans (hpool_ras j hj).2⟩
    · intro sIdx hsIdx
      have hdiv_lt : sIdx / 3 < M := by omega
      have hrole_lt : sIdx % 3 < 3 := Nat.mod_lt _ (by decide)
      have hsl_bab := hbab_sl sIdx hsIdx
      rw [ite_eq_left hdiv_lt] at hsl_bab
      have hbm_eq_bab : ∀ idx < 16 * M, 10 ≤ idx % 16 →
          readPacked (base + offBktMeta c U V w n_max) gBits w s_fin.mem idx =
            readPacked (base + offBktMeta c U V w n_max) gBits w s_bab.mem idx :=
        fun idx hidx h10 =>
          (readPacked_congr hw (hidx := hidx)
            (fun a ⟨ha1, ha2⟩ => hfin_to_ffm a (by omega)
              (by dsimp only [M, gBits] at hq_bm ha2; omega))).trans
            (hffm_keep idx hidx (Or.inr h10))
      have hbt_eq_bab : ∀ a, base + offBtMeta c U V w n_max ≤ a →
          a < base + offTrieChild0 c U V w n_max → s_fin.mem a = s_bab.mem a :=
        fun a ha1 ha2 => (hfin_to_ffm a (by omega) ha2).trans (hout_ffm a (Or.inr (by omega)))
      have hsl_fin := bTreeSliceMemRep_congr hw hsIdx
        ⟨hbm_eq_bab _ (by omega) (by omega), hbm_eq_bab _ (by omega) (by omega)⟩
        hbt_eq_bab hsl_bab
      have hdiv_lt' : sIdx / 3 < numBucketsWhp n_max := hdiv_lt
      dsimp only [backPtr, bktCnt] at hsl_fin ⊢
      by_cases hr0 : sIdx % 3 = 0
      · have hcond : sIdx / 3 < numBucketsWhp n_max ∧ sIdx % 3 = 0 := ⟨hdiv_lt', hr0⟩
        rw [ite_eq_left hcond] at hsl_fin ⊢
        rw [ite_eq_left hdiv_lt']
        exact hsl_fin
      · have hnr : ¬(sIdx / 3 < numBucketsWhp n_max ∧ sIdx % 3 = 0) := fun h => hr0 h.2
        rw [ite_eq_right hnr] at hsl_fin ⊢
        exact hsl_fin
    · dsimp only [BufTrieMemRep, emptyBufTrie]
      simp only [↓reduceIte]
      refine ⟨hmt_pos, Nat.zero_le _, hm12, hm13, fun u hu ch hch => ?_,
        fun _ h1 h2 => absurd h1 (Nat.not_le.mpr h2), fun u hu => ?_,
        fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · have hidx : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := by
          unfold trieChildEntriesWhp; exact mul_add_lt_mul_bound hu hch
        exact (readPacked_congr hw (hidx := hidx) (fun a ⟨ha1, ha2⟩ =>
          hout_whd a (Or.inr (Or.inl ⟨by omega, by
            have h14 : offTrieChild1 c U V w n_max =
              offTrieChild0 c U V w n_max + packedWords (trieChildEntriesWhp c n_max) gBits w := rfl
            dsimp only [gBits] at h14
            unfold offTrieMeta0; omega⟩)))).trans (hztc_ch _ hidx).1
      · have hu0 : u = 0 := by omega
        subst hu0
        exact ⟨htm0_2, fun h => absurd rfl h⟩
    · dsimp only [BufTrieMemRep, emptyBufTrie]
      simp only [Nat.one_ne_zero, ↓reduceIte]
      refine ⟨hmt_pos, Nat.zero_le _, hm14, hm15, fun u hu ch hch => ?_,
        fun _ h1 h2 => absurd h1 (Nat.not_le.mpr h2), fun u hu => ?_,
        fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · have hidx : u * 2 ^ bCharWhp n_max + ch < trieChildEntriesWhp c n_max := by
          unfold trieChildEntriesWhp; exact mul_add_lt_mul_bound hu hch
        have h14 : offTrieChild1 c U V w n_max =
          offTrieChild0 c U V w n_max + packedWords (trieChildEntriesWhp c n_max) gBits w := rfl
        have h15 : offTrieMeta0 c U V w n_max =
          offTrieChild1 c U V w n_max + packedWords (trieChildEntriesWhp c n_max) gBits w := rfl
        dsimp only [gBits] at h14 h15
        exact (readPacked_congr hw (hidx := hidx) (fun a ⟨ha1, ha2⟩ =>
          hout_whd a (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans (hztc_ch _ hidx).2
      · have hu0 : u = 0 := by omega
        subst hu0
        exact ⟨htm1_2, fun h => absurd rfl h⟩
  · rw [htot_step.1]
    exact hfr_whd.trans (hfr_ztc.trans (hfr_ffm.trans (hfr_bab.trans hfr_ras)))
  · rw [htot_step.1]
    rcases ha with ha_lo | ha_hi
    · exact (hout_whd a (Or.inl ha_lo)).trans
        ((hout_ztc a (Or.inl (by omega))).trans
          ((hout_ffm a (Or.inl (by omega))).trans
            ((hout_bab a (Or.inl (by omega))).trans (hout_ras a (Or.inl (by omega))))))
    · exact (hout_whd a (Or.inr (Or.inr (by omega)))).trans
        ((hout_ztc a (Or.inr (by
            have : offTrieMeta0 c U V w n_max ≤ offTrieItems0 c U V w n_max := by
              unfold offTrieItems0 offTrieMeta1; omega
            omega))).trans
          ((hout_ffm a (Or.inr (by omega))).trans
            ((hout_bab a (Or.inr (Or.inr (by omega)))).trans
              (hout_ras a (Or.inr (by omega))))))

/-! ## Section 2: `trySelfHealGenProg` (`CsrMemRep → WhpMemRep`) -/

/-- Check `GoodSeedOnState` on `CsrMemRep` and immediately convert in place to `FastMemRep` if
`ok = 1` (`d = (wp, base)`). -/
@[irreducible] def trySelfHealGenProg : WhpParams × ℕ → Memory.Prog Unit
  | d => do
    let one_v ← pure 1
    let ok ← checkGoodSeedOnStateGenProg d
    if ok = one_v then
      csrToFastGenProg d
    else
      pure ()

/-- Precondition for `trySelfHealGenProg` (`d = (wp, base)`). -/
@[expose] def TrySelfHealPre (w : ℕ) (d : WhpParams × ℕ) (s : Memory.State) : Prop :=
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (csr : CsrState) (dict : Dictionary.State U),
    WhpLargeEnv c U V w₀ n_max w d.2 ∧
    d.1 = mkWhpParams c U V w₀ n_max ∧
    SeedWhpMemRep d.2 c U w₀ n_max θ s.mem ∧
    CsrMemRep d.2 c U V w₀ n_max csr s.mem ∧
    ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict ∧
    (∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1)

/-- `Realizes .exact` certificate for `trySelfHealGenProg`. -/
theorem realizes_trySelfHealGen :
    Realizes .exact trySelfHealGenProg
      (WordEncoding.encode (α := WhpParams × ℕ))
      (WordEncoding.encode (α := Unit))
      TrySelfHealPre
      (fun _ _ => 0) := by
  unfold trySelfHealGenProg
  have hck := realizes_checkGoodSeedOnStateGen
  have hcf := realizes_csrToFastGen
  realize
  all_goals (
    rcases d with ⟨wp, base⟩
    dsimp only [TrySelfHealPre] at h
    obtain ⟨c, U, V, w₀, n_max, θ, csr, dict, henv, rfl, hseed, hrep, hcsr, hqv⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | (obtain ⟨hck_res, hck_seed, hck_rep, hck_salts, _, _, _⟩ :=
         checkGoodSeedOnStateGenProg_spec henv hseed hrep hcsr (s := s)
       have hok_eq : (checkGoodSeedOnState c U n_max θ csr).1 = true := by
         have h1 : (Memory.spec 0).clientResult s
             (checkGoodSeedOnStateGenProg (mkWhpParams c U V w n_max, base)) = 1 := by assumption
         rw [hck_res] at h1
         cases hok : (checkGoodSeedOnState c U n_max θ csr).1
         · rw [hok] at h1; simp at h1
         · rfl
       have hgood : GoodSeedOnState c U n_max θ dict :=
         (checkGoodSeedOnState_spec hcsr).1.mp hok_eq
       exact ⟨c, U, V, w, n_max, θ, csr, dict, (checkGoodSeedOnState c U n_max θ csr).2,
         henv, rfl, hck_seed, hck_rep, hcsr, hqv, hgood, hck_salts⟩)
  )

/-- Exact specification of `trySelfHealGenProg`: refines `trySelfHeal c U n_max θ csr` into
`WhpMemRep` while preserving `frontier` and memory outside `[base, base + largeSpaceWhp)`. -/
theorem trySelfHealGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {csr : CsrState} {dict : Dictionary.State U}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : CsrMemRep base c U V w n_max csr s.mem)
    (hcsr : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict)
    (hqv : ∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1) :
    let prog := trySelfHealGenProg (mkWhpParams c U V w n_max, base)
    let s' := (Memory.spec 0).clientState s prog
    WhpMemRep base c U V w n_max θ (trySelfHeal c U n_max θ csr) s'.mem ∧
    s'.frontier = s.frontier ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    (∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  have hth := henv.2.2.2.1
  obtain ⟨hck_res, hck_seed, hck_rep, hck_salts, hck_fr, hck_vp, hck_out⟩ :=
    checkGoodSeedOnStateGenProg_spec henv hseed hrep hcsr (s := s)
  set prog := trySelfHealGenProg (mkWhpParams c U V w n_max, base)
  set s1 := (Memory.spec 0).clientState s
    (checkGoodSeedOnStateGenProg (mkWhpParams c U V w n_max, base))
  dsimp only [trySelfHeal]
  by_cases hok : (checkGoodSeedOnState c U n_max θ csr).1 = true
  · have hgood : GoodSeedOnState c U n_max θ dict :=
      (checkGoodSeedOnState_spec hcsr).1.mp hok
    obtain ⟨hcf_seed, hcf_rep, hcf_fr, hcf_vp, hcf_out⟩ :=
      csrToFastGenProg_spec henv hck_seed hck_rep hcsr hqv hgood hck_salts (s := s1)
    rw [hok] at hck_res ⊢
    simp only [↓reduceIte] at hck_res ⊢
    have hstep : StepSpec w (base + largeSpaceWhp c U V w n_max) s prog
        ((Memory.spec 0).clientState s1 (csrToFastGenProg (mkWhpParams c U V w n_max, base)))
        () := by
      dsimp only [prog]; unfold trySelfHealGenProg; simp only [pure_bind]
      refine StepSpec.bind ⟨rfl, hck_res, hck_vp⟩ ?_
      simp only [↓reduceIte]
      exact ⟨rfl, rfl, hcf_vp⟩
    rw [hstep.1]
    exact ⟨⟨hth, hcf_seed, hcf_rep⟩, hcf_fr.trans hck_fr, hstep.2.2,
      fun a ha => (hcf_out a ha).trans (hck_out a ha)⟩
  · have hok_f : (checkGoodSeedOnState c U n_max θ csr).1 = false := Bool.eq_false_iff.mpr hok
    rw [hok_f] at hck_res ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at hck_res ⊢
    have hstep : StepSpec w (base + largeSpaceWhp c U V w n_max) s prog s1 () := by
      dsimp only [prog]; unfold trySelfHealGenProg; simp only [pure_bind]
      refine StepSpec.bind ⟨rfl, hck_res, hck_vp⟩ ?_
      simp only [Nat.zero_ne_one, ↓reduceIte]
      exact StepSpec.pure _ _
    rw [hstep.1]
    exact ⟨⟨hth, hck_seed, hck_rep⟩, hck_fr, hstep.2.2, hck_out⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
