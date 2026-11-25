/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolMetaProg
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `O(1)` `BlockPoolState` Rebalancing and Append/Pop Metadata Programs (`LargeBlockPoolStepProg`)

This module realizes every pure `BlockPoolState` metadata transition (`swapTailCoords`,
`unresRemoveAt`, `unresPush`, `freeTb`, `allocTbFor`, `findPromoteIdx`, `findTopSwapIdx`,
`maybeStartBktJob`, `actStepOne`, `bktTickOne`, `commitTopSwap`, `topSwapStepOne`, `topCleanOne`,
`rawPostAppend`, `prepPopBktBack`, `commitPopBktBack`) as a parameter-free (`¬ReadsWidth`)
`RealizesBounded .exact` `Memory.Prog` with `BpMetaProg` frame preservation and exact
`extractBlockPool` refinement.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.encodeOptSwap`,
  `bpBktTickMetaProg`, `bpTopCleanMetaProg`, `bpRawPostAppendMetaProg`,
  `bpPrepPopMetaProg`, `bpCommitPopMetaProg`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.WordRAM.Resizable.Randomized

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Parameter Getters, Concrete Write Corollaries, and Table Wrappers -/

@[simp] private theorem extractBlockPool_M (mp : BpMetaLayout) (mem : ℕ → ℕ) :
    (extractBlockPool mp mem).M = mp.M := rfl

@[simp] private theorem extractBlockPool_K (mp : BpMetaLayout) (mem : ℕ → ℕ) :
    (extractBlockPool mp mem).K = mp.K := rfl

@[simp] private theorem extractBlockPool_maxSlabs (mp : BpMetaLayout) (mem : ℕ → ℕ) :
    (extractBlockPool mp mem).maxSlabs = mp.maxSlabs := rfl

private theorem ring_add_diff_mod {hd rk K : ℕ} (hhd : hd < 6 * K) (hrk : rk < 6 * K) :
    (hd + (rk + 6 * K - hd) % (6 * K)) % (6 * K) = rk := by
  by_cases hle : hd ≤ rk
  · have hlt_sub : rk - hd < 6 * K := by omega
    rw [show rk + 6 * K - hd = 6 * K + (rk - hd) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt hlt_sub, show hd + (rk - hd) = rk by omega, Nat.mod_eq_of_lt hrk]
  · have hlt_sub : rk + 6 * K - hd < 6 * K := by omega
    rw [Nat.mod_eq_of_lt hlt_sub, show hd + (rk + 6 * K - hd) = 6 * K + rk by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt hrk]

private theorem freeTb_lt_8MK {M K i : ℕ} (hK : 64 ≤ K) (hi : i < 8 * M) :
    6 * M * K + i < 8 * M * K := by
  have h1 : i < M * K := lt_of_lt_of_le hi (by
    rw [Nat.mul_comm 8 M]; exact Nat.mul_le_mul_left M (by omega : 8 ≤ K))
  have h2 : 6 * M * K + M * K ≤ 8 * M * K := by
    have : 6 * (M * K) + M * K ≤ 8 * (M * K) := by omega
    simpa only [Nat.mul_assoc] using this
  omega

private theorem tbPhys_lt_8MK {M K tb : ℕ} (hK : 64 ≤ K) (htb : tb < 8 * M) :
    7 * M * K + tb < 8 * M * K := by
  have h1 : tb < M * K := lt_of_lt_of_le htb (by
    rw [Nat.mul_comm 8 M]; exact Nat.mul_le_mul_left M (by omega : 8 ≤ K))
  have h2 : 7 * M * K + M * K = 8 * M * K := by ring
  omega

private theorem BpMetaLayout.Valid.six_le_w {mp : BpMetaLayout} {w fr : ℕ}
    (hv : mp.Valid w fr) : 6 ≤ w := by
  have hnc := hv.nCap_lt_two_pow_w
  have hK64 := hv.K_ge
  have h12K := hv.twelve_K_le
  have hlt : 2 ^ 6 < 2 ^ w := by omega
  exact (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hlt |>.le

private theorem BpMetaLayout.Valid.param_fits {mp : BpMetaLayout} {w fr : ℕ}
    (hv : mp.Valid w fr) :
    16 < 2 ^ w ∧ mp.M < 2 ^ w ∧ mp.K < 2 ^ w ∧ 6 * mp.K < 2 ^ w ∧
    mp.maxSlabs < 2 ^ w ∧ mp.maxBlocks < 2 ^ w ∧ mp.nCap < 2 ^ w := by
  have hnc := hv.nCap_lt_two_pow_w
  have h16M := hv.sixteen_M_le
  have hM2 := hv.M_ge
  have hK64 := hv.K_ge
  have h12K := hv.twelve_K_le
  have hmsK := hv.maxSlabs_K_le
  have hmb4 := hv.four_maxBlocks_le
  have hms_le : mp.maxSlabs ≤ mp.maxSlabs * mp.K := Nat.le_mul_of_pos_right _ (by omega)
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, hnc⟩

-- Concrete-slot write corollaries (flat record RHS -> 0 nested `if` blowup!)
private theorem writeScalar_1 {mp : BpMetaLayout} {w fr val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hval : val ≤ mp.nCap) :
    extractBlockPool mp ((Memory.spec 0).clientState s (bpWriteScalarProg ((mp.toCtx, 1), val))).mem
      = { extractBlockPool mp s.mem with nSide := val } := by
  rw [extractBlockPool_writeScalar hv (Or.inl rfl) hval, ite_eq_left rfl]

private theorem writeScalar_10 {mp : BpMetaLayout} {w fr val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteScalarProg ((mp.toCtx, 10), val))).mem =
      { extractBlockPool mp s.mem with unresLen := val } := by
  rw [extractBlockPool_writeScalar hv (Or.inr ⟨by decide, by decide⟩) hval]
  repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])

private theorem writeScalar_11 {mp : BpMetaLayout} {w fr val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteScalarProg ((mp.toCtx, 11), val))).mem =
      { extractBlockPool mp s.mem with tbHighWater := val } := by
  rw [extractBlockPool_writeScalar hv (Or.inr ⟨by decide, by decide⟩) hval]
  repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])

private theorem writeScalar_12 {mp : BpMetaLayout} {w fr val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteScalarProg ((mp.toCtx, 12), val))).mem =
      { extractBlockPool mp s.mem with freeTbTop := val } := by
  rw [extractBlockPool_writeScalar hv (Or.inr ⟨by decide, by decide⟩) hval]
  repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])

private theorem writeScalar_13 {mp : BpMetaLayout} {w fr val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteScalarProg ((mp.toCtx, 13), val))).mem =
      { extractBlockPool mp s.mem with topSwapAct := val } := by
  rw [extractBlockPool_writeScalar hv (Or.inr ⟨by decide, by decide⟩) hval]
  repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])

private theorem writeScalar_14 {mp : BpMetaLayout} {w fr val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteScalarProg ((mp.toCtx, 14), val))).mem =
      { extractBlockPool mp s.mem with topSwapSrc := val } := by
  rw [extractBlockPool_writeScalar hv (Or.inr ⟨by decide, by decide⟩) hval]
  repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])

private theorem writeScalar_15 {mp : BpMetaLayout} {w fr val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteScalarProg ((mp.toCtx, 15), val))).mem =
      { extractBlockPool mp s.mem with topSwapDst := val } := by
  rw [extractBlockPool_writeScalar hv (Or.inr ⟨by decide, by decide⟩) hval]
  repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])

private theorem writeScalar_16 {mp : BpMetaLayout} {w fr val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteScalarProg ((mp.toCtx, 16), val))).mem =
      { extractBlockPool mp s.mem with topSwapCur := val } := by
  rw [extractBlockPool_writeScalar hv (Or.inr ⟨by decide, by decide⟩) hval]
  repeat rw [ite_eq_right (by decide)]

private theorem writeBktMeta_0 {mp : BpMetaLayout} {w fr b val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hb : b < mp.M) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteBktMetaProg ((mp.toCtx, (b, 0)), val))).mem =
      { extractBlockPool mp s.mem with
        q := BlockPoolState.set1 (extractBlockPool mp s.mem).q b val } := by
  rw [extractBlockPool_writeBktMeta hv hb (by decide) hval, ite_eq_left rfl]

private theorem writeBktMeta_1 {mp : BpMetaLayout} {w fr b val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hb : b < mp.M) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteBktMetaProg ((mp.toCtx, (b, 1)), val))).mem =
      { extractBlockPool mp s.mem with
        r := BlockPoolState.set1 (extractBlockPool mp s.mem).r b val } := by
  rw [extractBlockPool_writeBktMeta hv hb (by decide) hval]
  repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])

private theorem writeBktMeta_2 {mp : BpMetaLayout} {w fr b val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hb : b < mp.M) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteBktMetaProg ((mp.toCtx, (b, 2)), val))).mem =
      { extractBlockPool mp s.mem with
        head := BlockPoolState.set1 (extractBlockPool mp s.mem).head b val } := by
  rw [extractBlockPool_writeBktMeta hv hb (by decide) hval]
  repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])

private theorem writeBktMeta_3 {mp : BpMetaLayout} {w fr b val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hb : b < mp.M) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteBktMetaProg ((mp.toCtx, (b, 3)), val))).mem =
      { extractBlockPool mp s.mem with
        actCode := BlockPoolState.set1 (extractBlockPool mp s.mem).actCode b val } := by
  rw [extractBlockPool_writeBktMeta hv hb (by decide) hval]
  repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])

private theorem writeBktMeta_4 {mp : BpMetaLayout} {w fr b val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hb : b < mp.M) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteBktMetaProg ((mp.toCtx, (b, 4)), val))).mem =
      { extractBlockPool mp s.mem with
        actBlk := BlockPoolState.set1 (extractBlockPool mp s.mem).actBlk b val } := by
  rw [extractBlockPool_writeBktMeta hv hb (by decide) hval]
  repeat rw [ite_eq_right (by decide)]

private theorem writeSlabOwner_0 {mp : BpMetaLayout} {w fr P val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hP : P < mp.maxBlocks) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteSlabOwnerProg ((mp.toCtx, (P, 0)), val))).mem =
      { extractBlockPool mp s.mem with
        blkTag := BlockPoolState.set1 (extractBlockPool mp s.mem).blkTag P val } := by
  rw [extractBlockPool_writeSlabOwner hv hP (by decide) hval, ite_eq_left rfl]

private theorem writeSlabOwner_1 {mp : BpMetaLayout} {w fr P val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hP : P < mp.maxBlocks) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteSlabOwnerProg ((mp.toCtx, (P, 1)), val))).mem =
      { extractBlockPool mp s.mem with
        blkMeta1 := BlockPoolState.set1 (extractBlockPool mp s.mem).blkMeta1 P val } := by
  rw [extractBlockPool_writeSlabOwner hv hP (by decide) hval]
  repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])

private theorem writeSlabOwner_2 {mp : BpMetaLayout} {w fr P val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hP : P < mp.maxBlocks) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteSlabOwnerProg ((mp.toCtx, (P, 2)), val))).mem =
      { extractBlockPool mp s.mem with
        blkMeta2 := BlockPoolState.set1 (extractBlockPool mp s.mem).blkMeta2 P val } := by
  rw [extractBlockPool_writeSlabOwner hv hP (by decide) hval]
  repeat (first | rw [ite_eq_left rfl] | rw [ite_eq_right (by decide)])

private theorem writeSlabOwner_3 {mp : BpMetaLayout} {w fr P val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hP : P < mp.maxBlocks) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteSlabOwnerProg ((mp.toCtx, (P, 3)), val))).mem =
      { extractBlockPool mp s.mem with
        unresStack := BlockPoolState.set1 (extractBlockPool mp s.mem).unresStack P val } := by
  rw [extractBlockPool_writeSlabOwner hv hP (by decide) hval]
  repeat rw [ite_eq_right (by decide)]

private theorem writeTailOwner_0 {mp : BpMetaLayout} {w fr t val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (ht : t < 8 * mp.M * mp.K) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteTailOwnerProg ((mp.toCtx, (t, 0)), val))).mem =
      { extractBlockPool mp s.mem with
        tailOwnerBkt := BlockPoolState.set1 (extractBlockPool mp s.mem).tailOwnerBkt t val } := by
  rw [extractBlockPool_writeTailOwner hv ht hval, ite_eq_left rfl]

private theorem writeTailOwner_1 {mp : BpMetaLayout} {w fr t val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (ht : t < 8 * mp.M * mp.K) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteTailOwnerProg ((mp.toCtx, (t, 1)), val))).mem =
      { extractBlockPool mp s.mem with
        tailOwnerRing := BlockPoolState.set1 (extractBlockPool mp s.mem).tailOwnerRing t val } := by
  rw [extractBlockPool_writeTailOwner hv ht hval, ite_eq_right (by decide)]

/-- Read `(M, K)` from `BpMetaCtx` (`¬ReadsWidth`). -/
private def bpGetMKProg : BpMetaCtx → Memory.Prog (ℕ × ℕ)
  | (_, (((m, k), _), _)) => pure (m, k)

@[simp] private theorem runClient_state_bpGetMKProg (ctx : BpMetaCtx) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpGetMKProg ctx)).2.1 = s := by
  rcases ctx with ⟨_, ⟨⟨⟨_, _⟩, _⟩, _⟩⟩; rfl

private theorem clientState_bpGetMKProg (ctx : BpMetaCtx) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpGetMKProg ctx) = s :=
  runClient_state_bpGetMKProg ctx s

private theorem realizesBounded_bpGetMK :
    RealizesBounded .exact bpGetMKProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ctx s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  realize

private theorem bpGetMKProg_frame (mp : BpMetaLayout) :
    BpMetaProg mp 0 (bpGetMKProg mp.toCtx) :=
  BpMetaProg.pure_prog (mp.M, mp.K)

@[simp] private theorem runClient_fst_bpGetMKProg (ctx : BpMetaCtx) (st : Memory.State) :
    ((Memory.spec 0).runClient st (bpGetMKProg ctx)).1 =
      ((BpMetaLayout.ofCtx ctx).M, (BpMetaLayout.ofCtx ctx).K) := by
  rw [← BpMetaLayout.toCtx_ofCtx ctx]; rfl

private theorem clientResult_bpGetMK (mp : BpMetaLayout) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpGetMKProg mp.toCtx) = (mp.M, mp.K) :=
  rfl

/-- Read `((maxSlabs, maxBlocks), nCap)` from `BpMetaCtx` (`¬ReadsWidth`). -/
private def bpGetCapsProg : BpMetaCtx → Memory.Prog ((ℕ × ℕ) × ℕ)
  | (_, ((_, (ms, mbk)), (_, nc))) => pure ((ms, mbk), nc)

@[simp] private theorem runClient_state_bpGetCapsProg (ctx : BpMetaCtx) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpGetCapsProg ctx)).2.1 = s := by
  rcases ctx with ⟨_, ⟨⟨_, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩; rfl

private theorem clientState_bpGetCapsProg (ctx : BpMetaCtx) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpGetCapsProg ctx) = s :=
  runClient_state_bpGetCapsProg ctx s

private theorem realizesBounded_bpGetCaps :
    RealizesBounded .exact bpGetCapsProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (fun w ctx s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  realize

private theorem bpGetCapsProg_frame (mp : BpMetaLayout) :
    BpMetaProg mp 0 (bpGetCapsProg mp.toCtx) :=
  BpMetaProg.pure_prog ((mp.maxSlabs, mp.maxBlocks), mp.nCap)

@[simp] private theorem runClient_fst_bpGetCapsProg (ctx : BpMetaCtx) (st : Memory.State) :
    ((Memory.spec 0).runClient st (bpGetCapsProg ctx)).1 =
      (((BpMetaLayout.ofCtx ctx).maxSlabs, (BpMetaLayout.ofCtx ctx).maxBlocks),
       (BpMetaLayout.ofCtx ctx).nCap) := by
  rw [← BpMetaLayout.toCtx_ofCtx ctx]; rfl

private theorem clientResult_bpGetCaps (mp : BpMetaLayout) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpGetCapsProg mp.toCtx) =
      ((mp.maxSlabs, mp.maxBlocks), mp.nCap) :=
  rfl

/-- Safe saturating subtraction `x - y` in `Basis.exact` (`0` queries, `¬ReadsWidth`). -/
private def bpSubProg : ℕ × ℕ → Memory.Prog ℕ
  | (x, y) => if y ≤ x then pure (x - y) else pure 0

@[simp] private theorem runClient_state_bpSubProg (xy : ℕ × ℕ) (st : Memory.State) :
    ((Memory.spec 0).runClient st (bpSubProg xy)).2.1 = st := by
  rcases xy with ⟨x, y⟩; unfold bpSubProg; dsimp only; split_ifs <;> rfl

private theorem clientState_bpSubProg (xy : ℕ × ℕ) (st : Memory.State) :
    (Memory.spec 0).clientState st (bpSubProg xy) = st :=
  runClient_state_bpSubProg xy st

@[simp] private theorem runClient_fst_bpSubProg (xy : ℕ × ℕ) (st : Memory.State) :
    ((Memory.spec 0).runClient st (bpSubProg xy)).1 = xy.1 - xy.2 := by
  rcases xy with ⟨x, y⟩; unfold bpSubProg; dsimp only
  split_ifs <;> [rfl; (change 0 = x - y; omega)]

private theorem clientResult_bpSubProg (x y : ℕ) (st : Memory.State) :
    (Memory.spec 0).clientResult st (bpSubProg (x, y)) = x - y :=
  runClient_fst_bpSubProg (x, y) st

private theorem realizesBounded_bpSub :
    RealizesBounded .exact bpSubProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  omega

private theorem bpSubProg_frame (mp : BpMetaLayout) (x y : ℕ) :
    BpMetaProg mp 0 (bpSubProg (x, y)) := by
  unfold bpSubProg; dsimp only
  exact BpMetaProg.ite_prog (y ≤ x)
    (fun _ => BpMetaProg.pure_prog (x - y))
    (fun _ => BpMetaProg.pure_prog 0)

/-- Register-tuple encoding `(hasSwap, (p₁, p₂))` of `Option PhysSwap`. -/
@[expose] def encodeOptSwap : Option PhysSwap → ℕ × (ℕ × ℕ)
  | none => (0, (0, 0))
  | some sw => (1, (sw.p₁, sw.p₂))

/-- Bundle extracting all table-frame bounds directly from `mp.Valid w fr`. -/
theorem BpMetaLayout.Valid.write_frames {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr) :
    (∀ k val, BpMetaProg mp 1 (bpWriteScalarProg ((mp.toCtx, k), val))) ∧
    (∀ b slot val, BpMetaProg mp 4 (bpWriteBktMetaProg ((mp.toCtx, (b, slot)), val))) ∧
    (∀ b v val, BpMetaProg mp 4 (bpWriteSlabOfProg ((mp.toCtx, (b, v)), val))) ∧
    (∀ idx val, BpMetaProg mp 4 (bpWriteTailDirRawProg ((mp.toCtx, idx), val))) ∧
    (∀ P lane val, BpMetaProg mp 4 (bpWriteSlabOwnerProg ((mp.toCtx, (P, lane)), val))) ∧
    (∀ t isRing val, BpMetaProg mp 4 (bpWriteTailOwnerProg ((mp.toCtx, (t, isRing)), val))) := by
  have hw := hv.w_pos
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge
  have hd2 := hv.offTailDir_ge
  have hd3 := hv.offSlabOwner_ge
  have hd4 := hv.offTailOwner_ge
  have h16le := hv.sixteen_MK_le_maxTail
  exact ⟨bpWriteScalarProg_frame hw ho32,
    bpWriteBktMetaProg_frame hw,
    bpWriteSlabOfProg_frame hw hd1,
    bpWriteTailDirRawProg_frame hw (by omega),
    bpWriteSlabOwnerProg_frame hw (by omega),
    bpWriteTailOwnerProg_frame hw (by omega) h16le⟩

/-- Write `tailRing b rk := val` (`¬ReadsWidth`). -/
private def bpWriteTailRingProg : (BpMetaCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((ctx, (b, rk)), val) => do
    let idx ← bpTailRingIdxProg (ctx, (b, rk))
    bpWriteTailDirRawProg ((ctx, idx), val)

@[simp] private theorem runClient_frontier_bpWriteTailRingProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpWriteTailRingProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, ⟨b, rk⟩⟩, val⟩
  unfold bpWriteTailRingProg; simp

private theorem realizesBounded_bpWriteTailRing :
    RealizesBounded .exact bpWriteTailRingProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hti := realizesBounded_bpTailRingIdx
  have hwtd := realizesBounded_bpWriteTailDirRaw
  realize
  all_goals (
    rcases d with ⟨⟨ctx, ⟨b, rk⟩⟩, val⟩
    simpa using h)

private theorem bpWriteTailRingProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b rk val : ℕ) :
    BpMetaProg mp 4 (bpWriteTailRingProg ((mp.toCtx, (b, rk)), val)) := by
  unfold bpWriteTailRingProg
  exact (BpMetaProg.bind_prog (bpTailRingIdxProg_frame mp b rk) fun idx =>
    hv.write_frames.2.2.2.1 idx val).mono (by decide)

private theorem bpWriteTailRingProg_spec {mp : BpMetaLayout} {w fr b rk val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hb : b < mp.M) (hrk : rk < 6 * mp.K) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteTailRingProg ((mp.toCtx, (b, rk)), val))).mem =
      { extractBlockPool mp s.mem with
        tailRing := BlockPoolState.set2 (extractBlockPool mp s.mem).tailRing b rk val } := by
  unfold bpWriteTailRingProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpTailRingIdxProg,
    clientResult_bpTailRingIdx hb hrk s]
  exact extractBlockPool_writeTailRing hv hb hrk hval

/-- Write `freeTbStack i := val` (`¬ReadsWidth`). -/
private def bpWriteFreeTbStackProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog Unit
  | ((ctx, i), val) => do
    let mk ← bpGetMKProg ctx
    if i < 8 * mk.1 then do
      let idx ← pure (6 * mk.1 * mk.2 + i)
      bpWriteTailDirRawProg ((ctx, idx), val)
    else
      pure ()

@[simp] private theorem runClient_frontier_bpWriteFreeTbStackProg
    (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpWriteFreeTbStackProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, i⟩, val⟩
  unfold bpWriteFreeTbStackProg; dsimp only
  simp only [prog_runClient_state_bind, runClient_state_bpGetMKProg]
  split_ifs <;> simp

private theorem realizesBounded_bpWriteFreeTbStack :
    RealizesBounded .exact bpWriteFreeTbStackProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hg := realizesBounded_bpGetMK
  have hwtd := realizesBounded_bpWriteTailDirRaw
  realize
  all_goals (
    rcases d with ⟨⟨ctx, i⟩, val⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, hnc_w⟩ := hv0.param_fits
    have h16M := hv0.sixteen_M_le
    have hK64 := hv0.K_ge
    have h8MK := hv0.eight_MK_le
    try simp only [runClient_state_bpGetMKProg] at *
    have hmk : ((Memory.spec 0).runClient s (bpGetMKProg ctx)).1 =
        ((BpMetaLayout.ofCtx ctx).M, (BpMetaLayout.ofCtx ctx).K) := by
      rw [← BpMetaLayout.toCtx_ofCtx ctx]; rfl
    try simp only [hmk] at *
    dsimp only [Fits] at *
    try (have hf8 := freeTb_lt_8MK hK64 ‹i < 8 * (BpMetaLayout.ofCtx ctx).M›)
    first | exact hv0 | omega)

private theorem bpWriteFreeTbStackProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (i val : ℕ) :
    BpMetaProg mp 4 (bpWriteFreeTbStackProg ((mp.toCtx, i), val)) := by
  unfold bpWriteFreeTbStackProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.ite_prog (i < 8 * mk.1)
      (fun _ => by simpa only [pure_bind] using hv.write_frames.2.2.2.1 (6 * mk.1 * mk.2 + i) val)
      (fun _ => (BpMetaProg.pure_prog ()).mono (C₂ := 4) (by decide))
  exact hf.mono (by decide)

private theorem bpWriteFreeTbStackProg_spec {mp : BpMetaLayout} {w fr i val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hi : i < 8 * mp.M) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteFreeTbStackProg ((mp.toCtx, i), val))).mem =
      { extractBlockPool mp s.mem with
        freeTbStack := BlockPoolState.set1 (extractBlockPool mp s.mem).freeTbStack i val } := by
  unfold bpWriteFreeTbStackProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg, clientResult_bpGetMK,
    ite_eq_left hi, pure_bind]
  exact extractBlockPool_writeFreeTbStack hv hi hval

/-- Write `tbPhysBlk tb := val` (`¬ReadsWidth`). -/
private def bpWriteTbPhysBlkProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog Unit
  | ((ctx, tb), val) => do
    let mk ← bpGetMKProg ctx
    if tb < 8 * mk.1 then do
      let idx ← pure (7 * mk.1 * mk.2 + tb)
      bpWriteTailDirRawProg ((ctx, idx), val)
    else
      pure ()

@[simp] private theorem runClient_frontier_bpWriteTbPhysBlkProg
    (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpWriteTbPhysBlkProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, tb⟩, val⟩
  unfold bpWriteTbPhysBlkProg; dsimp only
  simp only [prog_runClient_state_bind, runClient_state_bpGetMKProg]
  split_ifs <;> simp

private theorem realizesBounded_bpWriteTbPhysBlk :
    RealizesBounded .exact bpWriteTbPhysBlkProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hg := realizesBounded_bpGetMK
  have hwtd := realizesBounded_bpWriteTailDirRaw
  realize
  all_goals (
    rcases d with ⟨⟨ctx, tb⟩, val⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, hnc_w⟩ := hv0.param_fits
    have h16M := hv0.sixteen_M_le
    have hK64 := hv0.K_ge
    have h8MK := hv0.eight_MK_le
    try simp only [runClient_state_bpGetMKProg] at *
    have hmk : ((Memory.spec 0).runClient s (bpGetMKProg ctx)).1 =
        ((BpMetaLayout.ofCtx ctx).M, (BpMetaLayout.ofCtx ctx).K) := by
      rw [← BpMetaLayout.toCtx_ofCtx ctx]; rfl
    try simp only [hmk] at *
    dsimp only [Fits] at *
    try (have ht8 := tbPhys_lt_8MK hK64 ‹tb < 8 * (BpMetaLayout.ofCtx ctx).M›)
    first | exact hv0 | omega)

private theorem bpWriteTbPhysBlkProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (tb val : ℕ) :
    BpMetaProg mp 4 (bpWriteTbPhysBlkProg ((mp.toCtx, tb), val)) := by
  unfold bpWriteTbPhysBlkProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.ite_prog (tb < 8 * mk.1)
      (fun _ => by simpa only [pure_bind] using hv.write_frames.2.2.2.1 (7 * mk.1 * mk.2 + tb) val)
      (fun _ => (BpMetaProg.pure_prog ()).mono (C₂ := 4) (by decide))
  exact hf.mono (by decide)

private theorem bpWriteTbPhysBlkProg_spec {mp : BpMetaLayout} {w fr tb val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (htb : tb < 8 * mp.M) (hval : val ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpWriteTbPhysBlkProg ((mp.toCtx, tb), val))).mem =
      { extractBlockPool mp s.mem with
        tbPhysBlk := BlockPoolState.set1 (extractBlockPool mp s.mem).tbPhysBlk tb val } := by
  unfold bpWriteTbPhysBlkProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg, clientResult_bpGetMK,
    ite_eq_left htb, pure_bind]
  exact extractBlockPool_writeTbPhysBlk hv htb hval

/-! ## Section 2: Atomic Stack/Tail Metadata Primitives (`≤ 6` Binds Each) -/

/-- Read `(p, (b, rk))` for a live tail coordinate `t` (`3` binds, `¬ReadsWidth`). -/
private def bpReadTailInfoProg : BpMetaCtx × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | (ctx, t) => do
    let p ← bpPhysOfTailProg (ctx, t)
    let b ← bpReadTailOwnerProg (ctx, (t, 0))
    let rk ← bpReadTailOwnerProg (ctx, (t, 1))
    pure (p, (b, rk))

@[simp] private theorem runClient_state_bpReadTailInfoProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpReadTailInfoProg x)).2.1 = s := by
  rcases x with ⟨ctx, t⟩; unfold bpReadTailInfoProg; simp

private theorem clientState_bpReadTailInfoProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpReadTailInfoProg x) = s :=
  runClient_state_bpReadTailInfoProg x s

private theorem realizesBounded_bpReadTailInfo :
    RealizesBounded .exact bpReadTailInfoProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hpot := realizesBounded_bpPhysOfTail
  have hrto := realizesBounded_bpReadTailOwner
  realize
  all_goals (
    rcases d with ⟨ctx, t⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    dsimp only [Fits] at *
    try simp only [runClient_state_bpPhysOfTailProg, runClient_state_bpReadTailOwnerProg] at *
    first | exact hv0 | omega)

private theorem bpReadTailInfoProg_frame (mp : BpMetaLayout) (t : ℕ) :
    BpMetaProg mp 10 (bpReadTailInfoProg (mp.toCtx, t)) := by
  unfold bpReadTailInfoProg
  exact (BpMetaProg.bind_prog (bpPhysOfTailProg_frame mp t) fun p =>
    BpMetaProg.bind_prog (bpReadTailOwnerProg_frame mp t 0) fun b =>
    BpMetaProg.bind_prog (bpReadTailOwnerProg_frame mp t 1) fun rk =>
    BpMetaProg.pure_prog (p, (b, rk))).mono (by decide)

private theorem bpReadTailInfoProg_spec {mp : BpMetaLayout} {t : ℕ} {s : Memory.State}
    (hK64 : 64 ≤ mp.K) (ht : t < 8 * mp.M * mp.K)
    (hp_le : (extractBlockPool mp s.mem).physOfTail t ≤ mp.nCap) :
    (Memory.spec 0).clientResult s (bpReadTailInfoProg (mp.toCtx, t)) =
      ((extractBlockPool mp s.mem).physOfTail t,
       ((extractBlockPool mp s.mem).tailOwnerBkt t,
        (extractBlockPool mp s.mem).tailOwnerRing t)) := by
  unfold bpReadTailInfoProg
  rw [StateTransitionSpec.clientResult_bind, clientState_bpPhysOfTailProg,
    bpPhysOfTailProg_spec hK64 ht hp_le, StateTransitionSpec.clientResult_bind,
    clientState_bpReadTailOwnerProg, clientResult_bpReadTailOwner_bkt,
    StateTransitionSpec.clientResult_bind, clientState_bpReadTailOwnerProg,
    clientResult_bpReadTailOwner_ring]
  rfl

/-- Six-write commit half of `bpSwapTailMetaProg` (`6` binds, `¬ReadsWidth`). -/
private def bpSwapTailWriteProg :
    (BpMetaCtx × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | ((ctx, (t₁, t₂)), ((b₁, rk₁), (b₂, rk₂))) => do
    bpWriteTailRingProg ((ctx, (b₁, rk₁)), t₂)
    bpWriteTailRingProg ((ctx, (b₂, rk₂)), t₁)
    bpWriteTailOwnerProg ((ctx, (t₁, 0)), b₂)
    bpWriteTailOwnerProg ((ctx, (t₂, 0)), b₁)
    bpWriteTailOwnerProg ((ctx, (t₁, 1)), rk₂)
    bpWriteTailOwnerProg ((ctx, (t₂, 1)), rk₁)

@[simp] private theorem runClient_frontier_bpSwapTailWriteProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpSwapTailWriteProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, ⟨t₁, t₂⟩⟩, ⟨⟨b₁, rk₁⟩, ⟨b₂, rk₂⟩⟩⟩
  unfold bpSwapTailWriteProg; simp

private theorem realizesBounded_bpSwapTailWrite :
    RealizesBounded .exact bpSwapTailWriteProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwtr := realizesBounded_bpWriteTailRing
  have hwto := realizesBounded_bpWriteTailOwner
  realize
  all_goals (
    rcases d with ⟨⟨ctx, ⟨t₁, t₂⟩⟩, ⟨⟨b₁, rk₁⟩, ⟨b₂, rk₂⟩⟩⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    dsimp only [Fits] at *
    try simp only [runClient_frontier_bpWriteTailRingProg,
      runClient_frontier_bpWriteTailOwnerProg] at *
    first | exact hv0 | omega)

private theorem bpSwapTailWriteProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (t₁ t₂ b₁ rk₁ b₂ rk₂ : ℕ) :
    BpMetaProg mp 24 (bpSwapTailWriteProg ((mp.toCtx, (t₁, t₂)), ((b₁, rk₁), (b₂, rk₂)))) := by
  obtain ⟨_, _, _, _, _, hwto⟩ := hv.write_frames
  unfold bpSwapTailWriteProg
  exact (BpMetaProg.bind_prog (bpWriteTailRingProg_frame hv b₁ rk₁ t₂) fun _ =>
    BpMetaProg.bind_prog (bpWriteTailRingProg_frame hv b₂ rk₂ t₁) fun _ =>
    BpMetaProg.bind_prog (hwto t₁ 0 b₂) fun _ =>
    BpMetaProg.bind_prog (hwto t₂ 0 b₁) fun _ =>
    BpMetaProg.bind_prog (hwto t₁ 1 rk₂) fun _ =>
    hwto t₂ 1 rk₁).mono (by decide)

/-- Realization of `BlockPoolState.swapTailCoords` (`3` binds, `¬ReadsWidth`). -/
private def bpSwapTailMetaProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog (ℕ × (ℕ × ℕ))
  | (ctx, (t₁, t₂)) =>
    if t₁ = t₂ then
      pure (0, (0, 0))
    else do
      let i₁ ← bpReadTailInfoProg (ctx, t₁)
      let i₂ ← bpReadTailInfoProg (ctx, t₂)
      bpSwapTailWriteProg ((ctx, (t₁, t₂)), (i₁.2, i₂.2))
      pure (1, (i₁.1, i₂.1))

@[simp] private theorem runClient_frontier_bpSwapTailMetaProg
    (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpSwapTailMetaProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, ⟨t₁, t₂⟩⟩
  unfold bpSwapTailMetaProg; dsimp only; split_ifs <;> simp

private theorem realizesBounded_bpSwapTailMeta :
    RealizesBounded .exact bpSwapTailMetaProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrti := realizesBounded_bpReadTailInfo
  have hstw := realizesBounded_bpSwapTailWrite
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨t₁, t₂⟩⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    dsimp only [Fits] at *
    try simp only [runClient_state_bpReadTailInfoProg] at *
    first | exact hv0 | omega)

private theorem bpSwapTailMetaProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (t₁ t₂ : ℕ) :
    BpMetaProg mp 44 (bpSwapTailMetaProg (mp.toCtx, (t₁, t₂))) := by
  unfold bpSwapTailMetaProg; dsimp only
  refine BpMetaProg.ite_prog (t₁ = t₂)
    (fun _ => (BpMetaProg.pure_prog (0, (0, 0))).mono (C₂ := 44) (by decide))
    (fun _ => ?_)
  exact (BpMetaProg.bind_prog (bpReadTailInfoProg_frame mp t₁) fun i₁ =>
    BpMetaProg.bind_prog (bpReadTailInfoProg_frame mp t₂) fun i₂ =>
    BpMetaProg.bind_prog (bpSwapTailWriteProg_frame hv t₁ t₂ i₁.2.1 i₁.2.2 i₂.2.1 i₂.2.2) fun _ =>
    BpMetaProg.pure_prog (1, (i₁.1, i₂.1))).mono (by decide)

private theorem bpSwapTailMetaProg_spec {mp : BpMetaLayout} {w fr t₁ t₂ : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr) (hv : (extractBlockPool mp s.mem).CoreValid)
    (hn_le : (extractBlockPool mp s.mem).nSide ≤ mp.nCap)
    (ht₁ : (extractBlockPool mp s.mem).LiveTail t₁)
    (ht₂ : (extractBlockPool mp s.mem).LiveTail t₂) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s (bpSwapTailMetaProg (mp.toCtx, (t₁, t₂)))
    let res := (Memory.spec 0).clientResult s (bpSwapTailMetaProg (mp.toCtx, (t₁, t₂)))
    extractBlockPool mp s'.mem = (bp.swapTailCoords t₁ t₂).1 ∧
    res = encodeOptSwap (bp.swapTailCoords t₁ t₂).2 := by
  dsimp only
  have hM_eq : (extractBlockPool mp s.mem).M = mp.M := rfl
  have hK_eq : (extractBlockPool mp s.mem).K = mp.K := rfl
  have hK64 : 64 ≤ mp.K := hK_eq ▸ hv.K_ge
  have h8MK_le := hv_mp.eight_MK_le
  have h16M_le := hv_mp.sixteen_M_le
  have h12K_le := hv_mp.twelve_K_le
  unfold bpSwapTailMetaProg BlockPoolState.swapTailCoords; dsimp only
  by_cases heq : t₁ = t₂
  · rw [ite_eq_left heq, ite_eq_left heq]; exact ⟨rfl, rfl⟩
  · rw [ite_eq_right heq, ite_eq_right heq]; dsimp only
    obtain ⟨b₁', hb₁, k₁, hge₁, hlt₁, htr₁⟩ := ht₁
    obtain ⟨b₂', hb₂, k₂, hge₂, hlt₂, htr₂⟩ := ht₂
    have htf₁ := hv.tail_fwd b₁' hb₁ k₁ hge₁ hlt₁; dsimp only at htf₁; rw [htr₁] at htf₁
    have htf₂ := hv.tail_fwd b₂' hb₂ k₂ hge₂ hlt₂; dsimp only at htf₂; rw [htr₂] at htf₂
    have hp₁_le : (extractBlockPool mp s.mem).physOfTail t₁ ≤ mp.nCap :=
      (hv.physOfTail_lt_of_live ⟨b₁', hb₁, k₁, hge₁, hlt₁, htr₁⟩).le.trans hn_le
    have hp₂_le : (extractBlockPool mp s.mem).physOfTail t₂ ≤ mp.nCap :=
      (hv.physOfTail_lt_of_live ⟨b₂', hb₂, k₂, hge₂, hlt₂, htr₂⟩).le.trans hn_le
    have hob₁ : (extractBlockPool mp s.mem).tailOwnerBkt t₁ < mp.M := htf₁.2.2.2.2.1 ▸ hb₁
    have hor₁ : (extractBlockPool mp s.mem).tailOwnerRing t₁ < 6 * mp.K :=
      htf₁.2.2.2.2.2 ▸ Nat.mod_lt _ (by omega)
    have hob₂ : (extractBlockPool mp s.mem).tailOwnerBkt t₂ < mp.M := htf₂.2.2.2.2.1 ▸ hb₂
    have hor₂ : (extractBlockPool mp s.mem).tailOwnerRing t₂ < 6 * mp.K :=
      htf₂.2.2.2.2.2 ▸ Nat.mod_lt _ (by omega)
    have hpure_st : ∀ x (st : Memory.State),
        (Memory.spec 0).clientState st (pure x : Memory.Prog (ℕ × (ℕ × ℕ))) = st :=
      fun _ _ => rfl
    refine ⟨?_, ?_⟩
    · rw [StateTransitionSpec.clientState_bind, clientState_bpReadTailInfoProg,
        bpReadTailInfoProg_spec hK64 htf₁.1 hp₁_le,
        StateTransitionSpec.clientState_bind, clientState_bpReadTailInfoProg,
        bpReadTailInfoProg_spec hK64 htf₂.1 hp₂_le,
        StateTransitionSpec.clientState_bind, hpure_st]
      dsimp only
      unfold bpSwapTailWriteProg
      repeat rw [StateTransitionSpec.clientState_bind]
      have ht₁_lt : t₁ < 8 * mp.M * mp.K := htf₁.1
      have ht₂_lt : t₂ < 8 * mp.M * mp.K := htf₂.1
      rw [writeTailOwner_1 hv_mp ht₂_lt (by omega),
        writeTailOwner_1 hv_mp ht₁_lt (by omega),
        writeTailOwner_0 hv_mp ht₂_lt (by omega),
        writeTailOwner_0 hv_mp ht₁_lt (by omega),
        bpWriteTailRingProg_spec hv_mp hob₂ hor₂ (by omega),
        bpWriteTailRingProg_spec hv_mp hob₁ hor₁ (by omega)]
    · rw [StateTransitionSpec.clientResult_bind, clientState_bpReadTailInfoProg,
        bpReadTailInfoProg_spec hK64 htf₁.1 hp₁_le,
        StateTransitionSpec.clientResult_bind, clientState_bpReadTailInfoProg,
        bpReadTailInfoProg_spec hK64 htf₂.1 hp₂_le,
        StateTransitionSpec.clientResult_bind]
      rfl

/-- Realization of `BlockPoolState.unresRemoveAt` (`6` binds, `¬ReadsWidth`). -/
private def bpUnresRemoveAtProg : BpMetaCtx × ℕ → Memory.Prog Unit
  | (ctx, idx) => do
    let ul ← bpReadScalarProg (ctx, 10)
    let lastIdx ← bpSubProg (ul, 1)
    let P_last ← bpReadSlabOwnerProg (ctx, (lastIdx, 3))
    bpWriteScalarProg ((ctx, 10), lastIdx)
    bpWriteSlabOwnerProg ((ctx, (idx, 3)), P_last)
    if idx < lastIdx then
      bpWriteSlabOwnerProg ((ctx, (P_last, 1)), idx)
    else
      pure ()

@[simp] private theorem runClient_frontier_bpUnresRemoveAtProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpUnresRemoveAtProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, idx⟩
  unfold bpUnresRemoveAtProg
  simp only [prog_runClient_state_bind, runClient_state_bpReadScalarProg,
    runClient_state_bpSubProg, runClient_state_bpReadSlabOwnerProg]
  split_ifs <;> simp

private theorem realizesBounded_bpUnresRemoveAt :
    RealizesBounded .exact bpUnresRemoveAtProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hsub := realizesBounded_bpSub
  have hrso := realizesBounded_bpReadSlabOwner
  have hws := realizesBounded_bpWriteScalar
  have hwso := realizesBounded_bpWriteSlabOwner
  realize
  all_goals (
    rcases d with ⟨ctx, idx⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpUnresRemoveAtProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (idx : ℕ) :
    BpMetaProg mp 12 (bpUnresRemoveAtProg (mp.toCtx, idx)) := by
  obtain ⟨hws, _, _, _, hwso, _⟩ := hv.write_frames
  unfold bpUnresRemoveAtProg; dsimp only
  exact (BpMetaProg.bind_prog (bpReadScalarProg_frame mp 10) fun ul =>
    BpMetaProg.bind_prog (bpSubProg_frame mp ul 1) fun lastIdx =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp lastIdx 3) fun P_last =>
    BpMetaProg.bind_prog (hws 10 lastIdx) fun _ =>
    BpMetaProg.bind_prog (hwso idx 3 P_last) fun _ =>
    BpMetaProg.ite_prog (idx < lastIdx)
      (fun _ => hwso P_last 1 idx)
      (fun _ => (BpMetaProg.pure_prog ()).mono (C₂ := 4) (by decide))).mono (by decide)

private theorem bpUnresRemoveAtProg_spec {mp : BpMetaLayout} {w fr idx : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr)
    (hidx_mb : idx < mp.maxBlocks)
    (hul_mb : (extractBlockPool mp s.mem).unresLen - 1 < mp.maxBlocks)
    (hPlast_mb : (extractBlockPool mp s.mem).unresStack
      ((extractBlockPool mp s.mem).unresLen - 1) < mp.maxBlocks) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpUnresRemoveAtProg (mp.toCtx, idx))).mem =
      (extractBlockPool mp s.mem).unresRemoveAt idx := by
  have hmb4 := hv_mp.four_maxBlocks_le
  unfold bpUnresRemoveAtProg BlockPoolState.unresRemoveAt; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩ : 10 = 1 ∨ 10 ≤ 10 ∧ 10 < 17),
    StateTransitionSpec.clientState_bind, clientState_bpSubProg, clientResult_bpSubProg,
    StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg,
    clientResult_bpReadSlabOwner_unres,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  have hul_eq : s.mem (mp.metaBase + 10) = (extractBlockPool mp s.mem).unresLen := rfl
  rw [hul_eq]
  by_cases hlt : idx < (extractBlockPool mp s.mem).unresLen - 1
  · rw [ite_eq_left hlt, ite_eq_left hlt,
      writeSlabOwner_1 hv_mp hPlast_mb (by omega),
      writeSlabOwner_3 hv_mp hidx_mb (by omega),
      writeScalar_10 hv_mp (by omega)]
  · have hpure : ∀ st : Memory.State, (Memory.spec 0).clientState st (pure ()) = st := fun _ => rfl
    rw [ite_eq_right hlt, ite_eq_right hlt, hpure,
      writeSlabOwner_3 hv_mp hidx_mb (by omega),
      writeScalar_10 hv_mp (by omega)]

/-- Realization of `BlockPoolState.unresPush` (`6` binds, `¬ReadsWidth`). -/
private def bpUnresPushProg : BpMetaCtx × ℕ → Memory.Prog Unit
  | (ctx, P) => do
    let caps ← bpGetCapsProg ctx
    let ul ← bpReadScalarProg (ctx, 10)
    bpWriteSlabOwnerProg ((ctx, (P, 0)), 0)
    bpWriteSlabOwnerProg ((ctx, (P, 1)), ul)
    bpWriteSlabOwnerProg ((ctx, (ul, 3)), P)
    let ul1 ← pure (if ul < caps.2 then ul + 1 else 0)
    bpWriteScalarProg ((ctx, 10), ul1)

@[simp] private theorem runClient_frontier_bpUnresPushProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpUnresPushProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, P⟩; unfold bpUnresPushProg; simp

private theorem realizesBounded_bpUnresPush :
    RealizesBounded .exact bpUnresPushProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgc := realizesBounded_bpGetCaps
  have hrs := realizesBounded_bpReadScalar
  have hws := realizesBounded_bpWriteScalar
  have hwso := realizesBounded_bpWriteSlabOwner
  realize
  all_goals (
    rcases d with ⟨ctx, P⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, hnc_w⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpUnresPushProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr) (P : ℕ) :
    BpMetaProg mp 14 (bpUnresPushProg (mp.toCtx, P)) := by
  obtain ⟨hws, _, _, _, hwso, _⟩ := hv.write_frames
  unfold bpUnresPushProg; simp only [pure_bind]
  exact (BpMetaProg.bind_prog (bpGetCapsProg_frame mp) fun caps =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 10) fun ul =>
    BpMetaProg.bind_prog (hwso P 0 0) fun _ =>
    BpMetaProg.bind_prog (hwso P 1 ul) fun _ =>
    BpMetaProg.bind_prog (hwso ul 3 P) fun _ =>
    hws 10 (if ul < caps.2 then ul + 1 else 0)).mono (by decide)

private theorem bpUnresPushProg_spec {mp : BpMetaLayout} {w fr P : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr) (hP : P < mp.maxBlocks)
    (hul : (extractBlockPool mp s.mem).unresLen < mp.maxBlocks) :
    extractBlockPool mp ((Memory.spec 0).clientState s (bpUnresPushProg (mp.toCtx, P))).mem =
      (extractBlockPool mp s.mem).unresPush P := by
  have hmb4 := hv_mp.four_maxBlocks_le
  have hul_nc : (extractBlockPool mp s.mem).unresLen < mp.nCap := by omega
  unfold bpUnresPushProg BlockPoolState.unresPush; simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_bpGetCapsProg, clientResult_bpGetCaps,
    StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩ : 10 = 1 ∨ 10 ≤ 10 ∧ 10 < 17)]
  dsimp only
  have hul_eq : s.mem (mp.metaBase + 10) = (extractBlockPool mp s.mem).unresLen := rfl
  rw [hul_eq, ite_eq_left hul_nc]
  repeat rw [StateTransitionSpec.clientState_bind]
  rw [writeScalar_10 hv_mp (by omega),
    writeSlabOwner_3 hv_mp hul (by omega),
    writeSlabOwner_1 hv_mp hP (by omega),
    writeSlabOwner_0 hv_mp hP (Nat.zero_le _)]

/-- Realization of `BlockPoolState.freeTb` (`4` binds, `¬ReadsWidth`). -/
private def bpFreeTbProg : BpMetaCtx × ℕ → Memory.Prog Unit
  | (ctx, tb) => do
    let caps ← bpGetCapsProg ctx
    let ftt ← bpReadScalarProg (ctx, 12)
    bpWriteFreeTbStackProg ((ctx, ftt), tb)
    let ftt1 ← pure (if ftt < caps.2 then ftt + 1 else 0)
    bpWriteScalarProg ((ctx, 12), ftt1)

@[simp] private theorem runClient_frontier_bpFreeTbProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpFreeTbProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, tb⟩; unfold bpFreeTbProg; simp

private theorem realizesBounded_bpFreeTb :
    RealizesBounded .exact bpFreeTbProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgc := realizesBounded_bpGetCaps
  have hrs := realizesBounded_bpReadScalar
  have hwf := realizesBounded_bpWriteFreeTbStack
  have hws := realizesBounded_bpWriteScalar
  realize
  all_goals (
    rcases d with ⟨ctx, tb⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, hnc_w⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpFreeTbProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr) (tb : ℕ) :
    BpMetaProg mp 6 (bpFreeTbProg (mp.toCtx, tb)) := by
  obtain ⟨hws, _, _, _, _, _⟩ := hv.write_frames
  unfold bpFreeTbProg; simp only [pure_bind]
  exact (BpMetaProg.bind_prog (bpGetCapsProg_frame mp) fun caps =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 12) fun ftt =>
    BpMetaProg.bind_prog (bpWriteFreeTbStackProg_frame hv ftt tb) fun _ =>
    hws 12 (if ftt < caps.2 then ftt + 1 else 0)).mono (by decide)

private theorem bpFreeTbProg_spec {mp : BpMetaLayout} {w fr tb : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr) (htb : tb < 8 * mp.M)
    (hftt : (extractBlockPool mp s.mem).freeTbTop < 8 * mp.M) :
    extractBlockPool mp ((Memory.spec 0).clientState s (bpFreeTbProg (mp.toCtx, tb))).mem =
      (extractBlockPool mp s.mem).freeTb tb := by
  have h16M := hv_mp.sixteen_M_le
  have hftt_nc : (extractBlockPool mp s.mem).freeTbTop < mp.nCap := by omega
  unfold bpFreeTbProg BlockPoolState.freeTb; simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_bpGetCapsProg, clientResult_bpGetCaps,
    StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩ : 12 = 1 ∨ 10 ≤ 12 ∧ 12 < 17)]
  dsimp only
  have hf_eq : s.mem (mp.metaBase + 12) = (extractBlockPool mp s.mem).freeTbTop := rfl
  rw [hf_eq, ite_eq_left hftt_nc, StateTransitionSpec.clientState_bind,
    writeScalar_12 hv_mp (by omega),
    bpWriteFreeTbStackProg_spec hv_mp hftt (by omega)]

/-- Pop-from-`freeTbStack` branch of `allocTbFor` (`5` binds, `¬ReadsWidth`). -/
private def bpAllocTbPopProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog Unit
  | (ctx, (P, top')) => do
    let mk ← bpGetMKProg ctx
    let idx_ft ← pure (if top' < 8 * mk.1 then 6 * mk.1 * mk.2 + top' else 0)
    let tb ← bpReadTailDirRawProg (ctx, idx_ft)
    bpWriteScalarProg ((ctx, 12), top')
    bpWriteSlabOwnerProg ((ctx, (P, 2)), tb)
    bpWriteTbPhysBlkProg ((ctx, tb), P)

@[simp] private theorem runClient_frontier_bpAllocTbPopProg
    (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpAllocTbPopProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, ⟨P, top'⟩⟩; unfold bpAllocTbPopProg; simp

private theorem realizesBounded_bpAllocTbPop :
    RealizesBounded .exact bpAllocTbPopProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgm := realizesBounded_bpGetMK
  have hrtd := realizesBounded_bpReadTailDirRaw
  have hws := realizesBounded_bpWriteScalar
  have hwso := realizesBounded_bpWriteSlabOwner
  have hwtb := realizesBounded_bpWriteTbPhysBlk
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨P, top'⟩⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, hnc_w⟩ := hv0.param_fits
    have h16M := hv0.sixteen_M_le
    have hK64 := hv0.K_ge
    have h8MK := hv0.eight_MK_le
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first
    | simpa using hv0
    | omega
    | (simp only [runClient_fst_bpGetMKProg] at *
       try (have hf8 := freeTb_lt_8MK hK64 ‹top' < 8 * (BpMetaLayout.ofCtx ctx).M›)
       omega))

private theorem bpAllocTbPopProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (P top' : ℕ) :
    BpMetaProg mp 11 (bpAllocTbPopProg (mp.toCtx, (P, top'))) := by
  obtain ⟨hws, _, _, _, hwso, _⟩ := hv.write_frames
  unfold bpAllocTbPopProg; dsimp only; simp only [pure_bind]
  exact (BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.bind_prog
      (bpReadTailDirRawProg_frame mp (if top' < 8 * mk.1 then 6 * mk.1 * mk.2 + top' else 0))
      fun tb =>
    BpMetaProg.bind_prog (hws 12 top') fun _ =>
    BpMetaProg.bind_prog (hwso P 2 tb) fun _ =>
    bpWriteTbPhysBlkProg_frame hv tb P).mono (by decide)

/-- Fresh `tbHighWater` branch of `allocTbFor` (`5` binds, `¬ReadsWidth`). -/
private def bpAllocTbFreshProg : BpMetaCtx × ℕ → Memory.Prog Unit
  | (ctx, P) => do
    let caps ← bpGetCapsProg ctx
    let tb ← bpReadScalarProg (ctx, 11)
    let tb1 ← pure (if tb < caps.2 then tb + 1 else 0)
    bpWriteScalarProg ((ctx, 11), tb1)
    bpWriteSlabOwnerProg ((ctx, (P, 2)), tb)
    bpWriteTbPhysBlkProg ((ctx, tb), P)

@[simp] private theorem runClient_frontier_bpAllocTbFreshProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpAllocTbFreshProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, P⟩; unfold bpAllocTbFreshProg; simp

private theorem realizesBounded_bpAllocTbFresh :
    RealizesBounded .exact bpAllocTbFreshProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgc := realizesBounded_bpGetCaps
  have hrs := realizesBounded_bpReadScalar
  have hws := realizesBounded_bpWriteScalar
  have hwso := realizesBounded_bpWriteSlabOwner
  have hwtb := realizesBounded_bpWriteTbPhysBlk
  realize
  all_goals (
    rcases d with ⟨ctx, P⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, hnc_w⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpAllocTbFreshProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (P : ℕ) :
    BpMetaProg mp 10 (bpAllocTbFreshProg (mp.toCtx, P)) := by
  obtain ⟨hws, _, _, _, hwso, _⟩ := hv.write_frames
  unfold bpAllocTbFreshProg; dsimp only; simp only [pure_bind]
  exact (BpMetaProg.bind_prog (bpGetCapsProg_frame mp) fun caps =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 11) fun tb =>
    BpMetaProg.bind_prog (hws 11 (if tb < caps.2 then tb + 1 else 0)) fun _ =>
    BpMetaProg.bind_prog (hwso P 2 tb) fun _ =>
    bpWriteTbPhysBlkProg_frame hv tb P).mono (by decide)

/-- Realization of `BlockPoolState.allocTbFor` (`2` binds, `¬ReadsWidth`). -/
private def bpAllocTbForProg : BpMetaCtx × ℕ → Memory.Prog Unit
  | (ctx, P) => do
    let ftt ← bpReadScalarProg (ctx, 12)
    if 0 < ftt then
      bpAllocTbPopProg (ctx, (P, ftt - 1))
    else
      bpAllocTbFreshProg (ctx, P)

@[simp] private theorem runClient_frontier_bpAllocTbForProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpAllocTbForProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, P⟩; unfold bpAllocTbForProg; dsimp only
  simp only [prog_runClient_state_bind, runClient_state_bpReadScalarProg]
  split_ifs <;> simp

private theorem realizesBounded_bpAllocTbFor :
    RealizesBounded .exact bpAllocTbForProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hap := realizesBounded_bpAllocTbPop
  have haf := realizesBounded_bpAllocTbFresh
  realize
  all_goals (
    rcases d with ⟨ctx, P⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpAllocTbForProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr) (P : ℕ) :
    BpMetaProg mp 12 (bpAllocTbForProg (mp.toCtx, P)) := by
  unfold bpAllocTbForProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpReadScalarProg_frame mp 12) fun ftt =>
    BpMetaProg.ite_prog (0 < ftt)
      (fun _ => bpAllocTbPopProg_frame hv P (ftt - 1))
      (fun _ => (bpAllocTbFreshProg_frame hv P).mono (C₂ := 11) (by decide))
  exact hf.mono (by decide)

private theorem bpAllocTbForProg_spec {mp : BpMetaLayout} {w fr P : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr) (hP : P < mp.maxBlocks)
    (hft_lt : 0 < (extractBlockPool mp s.mem).freeTbTop →
      (extractBlockPool mp s.mem).freeTbTop - 1 < 8 * mp.M ∧
      (extractBlockPool mp s.mem).freeTbStack
        ((extractBlockPool mp s.mem).freeTbTop - 1) < 8 * mp.M)
    (hthw_lt : (extractBlockPool mp s.mem).freeTbTop = 0 →
      (extractBlockPool mp s.mem).tbHighWater < 8 * mp.M) :
    extractBlockPool mp ((Memory.spec 0).clientState s (bpAllocTbForProg (mp.toCtx, P))).mem =
      (extractBlockPool mp s.mem).allocTbFor P := by
  have h16M := hv_mp.sixteen_M_le
  have hmb4 := hv_mp.four_maxBlocks_le
  have hK64 := hv_mp.K_ge
  unfold bpAllocTbForProg BlockPoolState.allocTbFor; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩ : 12 = 1 ∨ 10 ≤ 12 ∧ 12 < 17)]
  have hf_eq : s.mem (mp.metaBase + 12) = (extractBlockPool mp s.mem).freeTbTop := rfl
  rw [hf_eq]
  by_cases hft : 0 < (extractBlockPool mp s.mem).freeTbTop
  · obtain ⟨htop_lt, htb_lt⟩ := hft_lt hft
    rw [ite_eq_left hft, ite_eq_left hft]
    unfold bpAllocTbPopProg; dsimp only; simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg, clientResult_bpGetMK]
    dsimp only; rw [ite_eq_left htop_lt]
    rw [StateTransitionSpec.clientState_bind, clientState_bpReadTailDirRawProg,
      clientResult_bpReadTailDir_freeTb hK64 htop_lt s,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      bpWriteTbPhysBlkProg_spec hv_mp htb_lt (by omega),
      writeSlabOwner_2 hv_mp hP (by omega),
      writeScalar_12 hv_mp (by omega)]
  · have hz : (extractBlockPool mp s.mem).freeTbTop = 0 := by omega
    have htb_lt := hthw_lt hz
    have htb_nc : (extractBlockPool mp s.mem).tbHighWater < mp.nCap := by omega
    rw [ite_eq_right hft, ite_eq_right hft]
    unfold bpAllocTbFreshProg; dsimp only; simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_bpGetCapsProg, clientResult_bpGetCaps,
      StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩ : 11 = 1 ∨ 10 ≤ 11 ∧ 11 < 17)]
    dsimp only
    have hthw_eq : s.mem (mp.metaBase + 11) = (extractBlockPool mp s.mem).tbHighWater := rfl
    rw [hthw_eq, ite_eq_left htb_nc,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      bpWriteTbPhysBlkProg_spec hv_mp htb_lt (by omega),
      writeSlabOwner_2 hv_mp hP (by omega),
      writeScalar_11 hv_mp (by omega)]

/-! ## Section 3: Pigeonhole Finders and Rebalancing Step Programs (`≤ 6` Binds Each) -/

/-- Read `((unresLen, B_full), (topSwapAct, (topSwapSrc, topSwapDst)))` (`6` binds,
`¬ReadsWidth`). -/
private def bpReadPromHdrProg : BpMetaCtx → Memory.Prog ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))
  | ctx => do
    let ns ← bpReadScalarProg (ctx, 1)
    let bf_r ← bpDivModKProg (ctx, ns)
    let ul ← bpReadScalarProg (ctx, 10)
    let tsa ← bpReadScalarProg (ctx, 13)
    let tss ← bpReadScalarProg (ctx, 14)
    let tsd ← bpReadScalarProg (ctx, 15)
    pure ((ul, bf_r.1), (tsa, (tss, tsd)))

@[simp] private theorem runClient_state_bpReadPromHdrProg (ctx : BpMetaCtx) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpReadPromHdrProg ctx)).2.1 = s := by
  unfold bpReadPromHdrProg; simp

private theorem clientState_bpReadPromHdrProg (ctx : BpMetaCtx) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpReadPromHdrProg ctx) = s :=
  runClient_state_bpReadPromHdrProg ctx s

private theorem realizesBounded_bpReadPromHdr :
    RealizesBounded .exact bpReadPromHdrProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
      (fun w ctx s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hdm := realizesBounded_bpDivModK
  realize
  all_goals (
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpReadPromHdrProg_frame (mp : BpMetaLayout) :
    BpMetaProg mp 5 (bpReadPromHdrProg mp.toCtx) := by
  unfold bpReadPromHdrProg
  exact (BpMetaProg.bind_prog (bpReadScalarProg_frame mp 1) fun ns =>
    BpMetaProg.bind_prog (bpDivModKProg_frame mp ns) fun bf_r =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 10) fun ul =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 13) fun tsa =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 14) fun tss =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 15) fun tsd =>
    BpMetaProg.pure_prog ((ul, bf_r.1), (tsa, (tss, tsd)))).mono (by decide)

private theorem clientResult_bpReadPromHdr (mp : BpMetaLayout) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpReadPromHdrProg mp.toCtx) =
      (((extractBlockPool mp s.mem).unresLen, (extractBlockPool mp s.mem).B_full),
       ((extractBlockPool mp s.mem).topSwapAct,
        ((extractBlockPool mp s.mem).topSwapSrc, (extractBlockPool mp s.mem).topSwapDst))) := by
  unfold bpReadPromHdrProg
  rw [StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inl rfl),
    StateTransitionSpec.clientResult_bind, clientState_bpDivModKProg, clientResult_bpDivModK,
    StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩),
    StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩),
    StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩),
    StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩)]
  rfl

/-- Check candidate `i` for `findPromoteIdx` without overflowing `2 ^ w` (`1` bind,
`¬ReadsWidth`). -/
private def bpCheckPromCandProg :
    (BpMetaCtx × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))) → Memory.Prog ℕ
  | ((ctx, i), ((ul, bf), (tsa, (tss, tsd)))) => do
    let P ← bpReadSlabOwnerProg (ctx, (i, 3))
    if i < ul ∧ 3 ≤ bf ∧ P ≤ bf - 3 ∧ (tsa = 0 ∨ (P ≠ tsd ∧ P ≠ tss)) then
      pure 1
    else
      pure 0

@[simp] private theorem runClient_state_bpCheckPromCandProg
    (x : (BpMetaCtx × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpCheckPromCandProg x)).2.1 = s := by
  rcases x with ⟨⟨ctx, i⟩, ⟨⟨ul, bf⟩, ⟨tsa, ⟨tss, tsd⟩⟩⟩⟩
  unfold bpCheckPromCandProg; dsimp only
  simp only [prog_runClient_state_bind, runClient_state_bpReadSlabOwnerProg]
  split_ifs <;> rfl

private theorem clientState_bpCheckPromCandProg
    (x : (BpMetaCtx × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpCheckPromCandProg x) = s :=
  runClient_state_bpCheckPromCandProg x s

private theorem realizesBounded_bpCheckPromCand :
    RealizesBounded .exact bpCheckPromCandProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := ℕ))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrso := realizesBounded_bpReadSlabOwner
  realize
  all_goals (
    rcases d with ⟨⟨ctx, i⟩, ⟨⟨ul, bf⟩, ⟨tsa, ⟨tss, tsd⟩⟩⟩⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpCheckPromCandProg_frame (mp : BpMetaLayout) (i : ℕ)
    (hdr : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))) :
    BpMetaProg mp 2 (bpCheckPromCandProg ((mp.toCtx, i), hdr)) := by
  rcases hdr with ⟨⟨ul, bf⟩, ⟨tsa, ⟨tss, tsd⟩⟩⟩
  unfold bpCheckPromCandProg; dsimp only
  exact (BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp i 3) fun P =>
    BpMetaProg.ite_prog _ (fun _ => BpMetaProg.pure_prog 1)
      (fun _ => BpMetaProg.pure_prog 0)).mono (by decide)

private theorem clientResult_bpCheckPromCand (mp : BpMetaLayout) (i : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s
      (bpCheckPromCandProg ((mp.toCtx, i),
        (((extractBlockPool mp s.mem).unresLen, (extractBlockPool mp s.mem).B_full),
         ((extractBlockPool mp s.mem).topSwapAct,
          ((extractBlockPool mp s.mem).topSwapSrc,
           (extractBlockPool mp s.mem).topSwapDst))))) =
      if decide (i < (extractBlockPool mp s.mem).unresLen ∧
          (extractBlockPool mp s.mem).unresStack i + 3 ≤ (extractBlockPool mp s.mem).B_full ∧
          ((extractBlockPool mp s.mem).topSwapAct = 0 ∨
            ((extractBlockPool mp s.mem).unresStack i ≠ (extractBlockPool mp s.mem).topSwapDst ∧
             (extractBlockPool mp s.mem).unresStack i ≠ (extractBlockPool mp s.mem).topSwapSrc)))
      then 1 else 0 := by
  unfold bpCheckPromCandProg; dsimp only
  rw [StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
    clientResult_bpReadSlabOwner_unres]
  have heq : (i < (extractBlockPool mp s.mem).unresLen ∧
      3 ≤ (extractBlockPool mp s.mem).B_full ∧
      (extractBlockPool mp s.mem).unresStack i ≤ (extractBlockPool mp s.mem).B_full - 3 ∧
      ((extractBlockPool mp s.mem).topSwapAct = 0 ∨
        ((extractBlockPool mp s.mem).unresStack i ≠ (extractBlockPool mp s.mem).topSwapDst ∧
         (extractBlockPool mp s.mem).unresStack i ≠ (extractBlockPool mp s.mem).topSwapSrc))) ↔
      (i < (extractBlockPool mp s.mem).unresLen ∧
        (extractBlockPool mp s.mem).unresStack i + 3 ≤ (extractBlockPool mp s.mem).B_full ∧
        ((extractBlockPool mp s.mem).topSwapAct = 0 ∨
          ((extractBlockPool mp s.mem).unresStack i ≠ (extractBlockPool mp s.mem).topSwapDst ∧
           (extractBlockPool mp s.mem).unresStack i ≠ (extractBlockPool mp s.mem).topSwapSrc))) :=
    ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, by omega, h4⟩,
     fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, by omega, h3⟩⟩
  by_cases hc : i < (extractBlockPool mp s.mem).unresLen ∧
      (extractBlockPool mp s.mem).unresStack i + 3 ≤ (extractBlockPool mp s.mem).B_full ∧
      ((extractBlockPool mp s.mem).topSwapAct = 0 ∨
        ((extractBlockPool mp s.mem).unresStack i ≠ (extractBlockPool mp s.mem).topSwapDst ∧
         (extractBlockPool mp s.mem).unresStack i ≠ (extractBlockPool mp s.mem).topSwapSrc))
  · rw [ite_eq_left (heq.mpr hc), decide_eq_true hc, ite_eq_left rfl]; rfl
  · rw [ite_eq_right (fun h => hc (heq.mp h)), decide_eq_false hc]; rfl

/-- Realization of `BlockPoolState.findPromoteIdx` (`5` binds max, `¬ReadsWidth`). -/
private def bpFindPromoteIdxProg : BpMetaCtx → Memory.Prog ℕ
  | ctx => do
    let hdr ← bpReadPromHdrProg ctx
    let c0 ← bpCheckPromCandProg ((ctx, 0), hdr)
    if c0 = 1 then pure 0
    else do
      let c1 ← bpCheckPromCandProg ((ctx, 1), hdr)
      if c1 = 1 then pure 1
      else do
        let c2 ← bpCheckPromCandProg ((ctx, 2), hdr)
        if c2 = 1 then pure 2
        else do
          let c3 ← bpCheckPromCandProg ((ctx, 3), hdr)
          if c3 = 1 then pure 3 else pure 4

@[simp] private theorem runClient_state_bpFindPromoteIdxProg (ctx : BpMetaCtx) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpFindPromoteIdxProg ctx)).2.1 = s := by
  unfold bpFindPromoteIdxProg
  simp only [prog_runClient_state_bind, runClient_state_bpReadPromHdrProg,
    runClient_state_bpCheckPromCandProg]
  split_ifs
  · rfl
  · simp only [prog_runClient_state_bind, runClient_state_bpCheckPromCandProg]
    split_ifs
    · rfl
    · simp only [prog_runClient_state_bind, runClient_state_bpCheckPromCandProg]
      split_ifs
      · rfl
      · simp only [prog_runClient_state_bind, runClient_state_bpCheckPromCandProg]
        split_ifs <;> rfl

private theorem clientState_bpFindPromoteIdxProg (ctx : BpMetaCtx) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpFindPromoteIdxProg ctx) = s :=
  runClient_state_bpFindPromoteIdxProg ctx s

private theorem realizesBounded_bpFindPromoteIdx :
    RealizesBounded .exact bpFindPromoteIdxProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := ℕ))
      (fun w ctx s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrh := realizesBounded_bpReadPromHdr
  have hcc := realizesBounded_bpCheckPromCand
  realize
  all_goals (
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpFindPromoteIdxProg_frame (mp : BpMetaLayout) :
    BpMetaProg mp 13 (bpFindPromoteIdxProg mp.toCtx) := by
  unfold bpFindPromoteIdxProg
  have hf := BpMetaProg.bind_prog (bpReadPromHdrProg_frame mp) fun hdr =>
    BpMetaProg.bind_prog (bpCheckPromCandProg_frame mp 0 hdr) fun c0 =>
    BpMetaProg.ite_prog (c0 = 1)
      (fun _ => (BpMetaProg.pure_prog 0).mono (C₂ := 6) (by decide))
      (fun _ =>
        (BpMetaProg.bind_prog (bpCheckPromCandProg_frame mp 1 hdr) fun c1 =>
          BpMetaProg.ite_prog (c1 = 1)
            (fun _ => (BpMetaProg.pure_prog 1).mono (C₂ := 4) (by decide))
            (fun _ =>
              (BpMetaProg.bind_prog (bpCheckPromCandProg_frame mp 2 hdr) fun c2 =>
                BpMetaProg.ite_prog (c2 = 1)
                  (fun _ => (BpMetaProg.pure_prog 2).mono (C₂ := 2) (by decide))
                  (fun _ =>
                    BpMetaProg.bind_prog (bpCheckPromCandProg_frame mp 3 hdr) fun c3 =>
                      BpMetaProg.ite_prog (c3 = 1)
                        (fun _ => BpMetaProg.pure_prog 3)
                        (fun _ => BpMetaProg.pure_prog 4))).mono (C₂ := 4) (by decide))).mono
          (C₂ := 6) (by decide))
  exact hf.mono (by decide)

private theorem bpFindPromoteIdxProg_spec (mp : BpMetaLayout) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpFindPromoteIdxProg mp.toCtx) =
      (extractBlockPool mp s.mem).findPromoteIdx := by
  unfold bpFindPromoteIdxProg BlockPoolState.findPromoteIdx; dsimp only
  rw [StateTransitionSpec.clientResult_bind, clientState_bpReadPromHdrProg,
    clientResult_bpReadPromHdr, StateTransitionSpec.clientResult_bind,
    clientState_bpCheckPromCandProg, clientResult_bpCheckPromCand]
  set ok : ℕ → Bool := fun i =>
    decide (i < (extractBlockPool mp s.mem).unresLen ∧
      (extractBlockPool mp s.mem).unresStack i + 3 ≤ (extractBlockPool mp s.mem).B_full ∧
      ((extractBlockPool mp s.mem).topSwapAct = 0 ∨
        ((extractBlockPool mp s.mem).unresStack i ≠ (extractBlockPool mp s.mem).topSwapDst ∧
         (extractBlockPool mp s.mem).unresStack i ≠ (extractBlockPool mp s.mem).topSwapSrc)))
  change (Memory.spec 0).clientResult s (if (if ok 0 then 1 else 0) = 1 then _ else _) =
    (if ok 0 then 0 else _)
  by_cases h0 : ok 0 = true
  · simp only [h0, ↓reduceIte]; rfl
  · simp only [h0, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
    rw [StateTransitionSpec.clientResult_bind, clientState_bpCheckPromCandProg,
      clientResult_bpCheckPromCand]
    change (Memory.spec 0).clientResult s (if (if ok 1 then 1 else 0) = 1 then _ else _) =
      (if ok 1 then 1 else _)
    by_cases h1 : ok 1 = true
    · simp only [h1, ↓reduceIte]; rfl
    · simp only [h1, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
      rw [StateTransitionSpec.clientResult_bind, clientState_bpCheckPromCandProg,
        clientResult_bpCheckPromCand]
      change (Memory.spec 0).clientResult s (if (if ok 2 then 1 else 0) = 1 then _ else _) =
        (if ok 2 then 2 else _)
      by_cases h2 : ok 2 = true
      · simp only [h2, ↓reduceIte]; rfl
      · simp only [h2, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
        rw [StateTransitionSpec.clientResult_bind, clientState_bpCheckPromCandProg,
          clientResult_bpCheckPromCand]
        change (Memory.spec 0).clientResult s (if (if ok 3 then 1 else 0) = 1 then _ else _) =
          (if ok 3 then 3 else 4)
        by_cases h3 : ok 3 = true
        · simp only [h3, ↓reduceIte]; rfl
        · simp only [h3, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]; rfl

/-- Realization of `BlockPoolState.findTopSwapIdx` (`5` binds max, `¬ReadsWidth`). -/
private def bpFindTopSwapIdxProg : BpMetaCtx → Memory.Prog ℕ
  | ctx => do
    let ns ← bpReadScalarProg (ctx, 1)
    let bf_r ← bpDivModKProg (ctx, ns)
    let ul ← bpReadScalarProg (ctx, 10)
    let P0 ← bpReadSlabOwnerProg (ctx, (0, 3))
    if 0 < ul ∧ 3 ≤ bf_r.1 ∧ P0 ≤ bf_r.1 - 3 then
      pure 0
    else do
      let P1 ← bpReadSlabOwnerProg (ctx, (1, 3))
      if 1 < ul ∧ 3 ≤ bf_r.1 ∧ P1 ≤ bf_r.1 - 3 then
        pure 1
      else
        pure 2

@[simp] private theorem runClient_state_bpFindTopSwapIdxProg (ctx : BpMetaCtx) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpFindTopSwapIdxProg ctx)).2.1 = s := by
  unfold bpFindTopSwapIdxProg
  simp only [prog_runClient_state_bind, runClient_state_bpReadScalarProg,
    runClient_state_bpDivModKProg, runClient_state_bpReadSlabOwnerProg]
  split_ifs
  · rfl
  · simp only [prog_runClient_state_bind, runClient_state_bpReadSlabOwnerProg]
    split_ifs <;> rfl

private theorem clientState_bpFindTopSwapIdxProg (ctx : BpMetaCtx) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpFindTopSwapIdxProg ctx) = s :=
  runClient_state_bpFindTopSwapIdxProg ctx s

private theorem realizesBounded_bpFindTopSwapIdx :
    RealizesBounded .exact bpFindTopSwapIdxProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := ℕ))
      (fun w ctx s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hdm := realizesBounded_bpDivModK
  have hrso := realizesBounded_bpReadSlabOwner
  realize
  all_goals (
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpFindTopSwapIdxProg_frame (mp : BpMetaLayout) :
    BpMetaProg mp 6 (bpFindTopSwapIdxProg mp.toCtx) := by
  unfold bpFindTopSwapIdxProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpReadScalarProg_frame mp 1) fun ns =>
    BpMetaProg.bind_prog (bpDivModKProg_frame mp ns) fun bf_r =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 10) fun ul =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp 0 3) fun P0 =>
    BpMetaProg.ite_prog (0 < ul ∧ 3 ≤ bf_r.1 ∧ P0 ≤ bf_r.1 - 3)
      (fun _ => (BpMetaProg.pure_prog 0).mono (C₂ := 2) (by decide))
      (fun _ =>
        BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp 1 3) fun P1 =>
          BpMetaProg.ite_prog (1 < ul ∧ 3 ≤ bf_r.1 ∧ P1 ≤ bf_r.1 - 3)
            (fun _ => BpMetaProg.pure_prog 1)
            (fun _ => BpMetaProg.pure_prog 2))
  exact hf.mono (by decide)

private theorem bpFindTopSwapIdxProg_spec (mp : BpMetaLayout) (s : Memory.State) :
    (Memory.spec 0).clientResult s (bpFindTopSwapIdxProg mp.toCtx) =
      (extractBlockPool mp s.mem).findTopSwapIdx := by
  unfold bpFindTopSwapIdxProg BlockPoolState.findTopSwapIdx
  rw [StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inl rfl),
    StateTransitionSpec.clientResult_bind, clientState_bpDivModKProg, clientResult_bpDivModK,
    StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩),
    StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
    clientResult_bpReadSlabOwner_unres]
  dsimp only
  have hns : s.mem (mp.metaBase + 1) / mp.K = (extractBlockPool mp s.mem).B_full := rfl
  have hul : s.mem (mp.metaBase + 10) = (extractBlockPool mp s.mem).unresLen := rfl
  rw [hns, hul]
  have heq0 : (0 < (extractBlockPool mp s.mem).unresLen ∧
      3 ≤ (extractBlockPool mp s.mem).B_full ∧
      (extractBlockPool mp s.mem).unresStack 0 ≤ (extractBlockPool mp s.mem).B_full - 3) ↔
      (0 < (extractBlockPool mp s.mem).unresLen ∧
       (extractBlockPool mp s.mem).unresStack 0 + 3 ≤ (extractBlockPool mp s.mem).B_full) :=
    ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by omega, by omega⟩⟩
  by_cases c0 : 0 < (extractBlockPool mp s.mem).unresLen ∧
      (extractBlockPool mp s.mem).unresStack 0 + 3 ≤ (extractBlockPool mp s.mem).B_full
  · rw [ite_eq_left (heq0.mpr c0), ite_eq_left c0]; rfl
  · rw [ite_eq_right (fun h => c0 (heq0.mp h)), ite_eq_right c0,
      StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
      clientResult_bpReadSlabOwner_unres]
    have heq1 : (1 < (extractBlockPool mp s.mem).unresLen ∧
        3 ≤ (extractBlockPool mp s.mem).B_full ∧
        (extractBlockPool mp s.mem).unresStack 1 ≤ (extractBlockPool mp s.mem).B_full - 3) ↔
        (1 < (extractBlockPool mp s.mem).unresLen ∧
         (extractBlockPool mp s.mem).unresStack 1 + 3 ≤ (extractBlockPool mp s.mem).B_full) :=
      ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by omega, by omega⟩⟩
    by_cases c1 : 1 < (extractBlockPool mp s.mem).unresLen ∧
        (extractBlockPool mp s.mem).unresStack 1 + 3 ≤ (extractBlockPool mp s.mem).B_full
    · rw [ite_eq_left (heq1.mpr c1), ite_eq_left c1]; rfl
    · rw [ite_eq_right (fun h => c1 (heq1.mp h)), ite_eq_right c1]; rfl

/-! ### `bpMaybeStartMetaProg` (`maybeStartBktJob`) -/

/-- Start a `Promote` job on bucket `b` (`6` binds, `¬ReadsWidth`). -/
private def bpStartPromoteProg : BpMetaCtx × ℕ → Memory.Prog Unit
  | (ctx, b) => do
    let idx ← bpFindPromoteIdxProg ctx
    let P_act ← bpReadSlabOwnerProg (ctx, (idx, 3))
    bpUnresRemoveAtProg (ctx, idx)
    bpWriteSlabOwnerProg ((ctx, (P_act, 0)), 2)
    bpWriteSlabOwnerProg ((ctx, (P_act, 1)), b)
    bpWriteBktMetaProg ((ctx, (b, 4)), P_act)
    bpWriteBktMetaProg ((ctx, (b, 3)), 1)

@[simp] private theorem runClient_frontier_bpStartPromoteProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpStartPromoteProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, b⟩; unfold bpStartPromoteProg; simp

private theorem realizesBounded_bpStartPromote :
    RealizesBounded .exact bpStartPromoteProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hfp := realizesBounded_bpFindPromoteIdx
  have hrso := realizesBounded_bpReadSlabOwner
  have hur := realizesBounded_bpUnresRemoveAt
  have hwso := realizesBounded_bpWriteSlabOwner
  have hwbm := realizesBounded_bpWriteBktMeta
  realize
  all_goals (
    rcases d with ⟨ctx, b⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpStartPromoteProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b : ℕ) :
    BpMetaProg mp 43 (bpStartPromoteProg (mp.toCtx, b)) := by
  obtain ⟨_, hwbm, _, _, hwso, _⟩ := hv.write_frames
  unfold bpStartPromoteProg
  exact (BpMetaProg.bind_prog (bpFindPromoteIdxProg_frame mp) fun idx =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp idx 3) fun P_act =>
    BpMetaProg.bind_prog (bpUnresRemoveAtProg_frame hv idx) fun _ =>
    BpMetaProg.bind_prog (hwso P_act 0 2) fun _ =>
    BpMetaProg.bind_prog (hwso P_act 1 b) fun _ =>
    BpMetaProg.bind_prog (hwbm b 4 P_act) fun _ =>
    hwbm b 3 1).mono (by decide)

/-- Read `(P_act, hd_new)` before starting a `Demote` job (`4` binds, `¬ReadsWidth`). -/
private def bpStartDemoteReadProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (ctx, (b, vp)) => do
    let mk ← bpGetMKProg ctx
    let P_act ← bpReadSlabOfProg (ctx, (b, vp))
    let hd ← bpReadBktMetaProg (ctx, (b, 2))
    let hd_new ← bpRingAddProg (ctx, (hd, 5 * mk.2))
    pure (P_act, hd_new)

@[simp] private theorem runClient_state_bpStartDemoteReadProg
    (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpStartDemoteReadProg x)).2.1 = s := by
  rcases x with ⟨ctx, ⟨b, vp⟩⟩; unfold bpStartDemoteReadProg; simp

private theorem clientState_bpStartDemoteReadProg
    (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpStartDemoteReadProg x) = s :=
  runClient_state_bpStartDemoteReadProg x s

private theorem realizesBounded_bpStartDemoteRead :
    RealizesBounded .exact bpStartDemoteReadProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgm := realizesBounded_bpGetMK
  have hrsl := realizesBounded_bpReadSlabOf
  have hrbm := realizesBounded_bpReadBktMeta
  have hra := realizesBounded_bpRingAdd
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨b, vp⟩⟩
    have hv0 := h
    obtain ⟨h16, _, hk, h6k, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpStartDemoteReadProg_frame (mp : BpMetaLayout) (b vp : ℕ) :
    BpMetaProg mp 4 (bpStartDemoteReadProg (mp.toCtx, (b, vp))) := by
  unfold bpStartDemoteReadProg
  exact (BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.bind_prog (bpReadSlabOfProg_frame mp b vp) fun P_act =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 2) fun hd =>
    BpMetaProg.bind_prog (bpRingAddProg_frame mp hd (5 * mk.2)) fun hd_new =>
    BpMetaProg.pure_prog (P_act, hd_new)).mono (by decide)

/-- First write half of starting a `Demote` job (`4` binds, `¬ReadsWidth`). -/
private def bpStartDemoteWriteAProg :
    (BpMetaCtx × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | ((ctx, b), (P_act, (vp, r_b))) => do
    let mk ← bpGetMKProg ctx
    bpAllocTbForProg (ctx, P_act)
    bpWriteBktMetaProg ((ctx, (b, 0)), vp)
    let r_new ← pure (if r_b < 6 * mk.2 then r_b + mk.2 else 0)
    bpWriteBktMetaProg ((ctx, (b, 1)), r_new)

@[simp] private theorem runClient_frontier_bpStartDemoteWriteAProg
    (x : (BpMetaCtx × ℕ) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpStartDemoteWriteAProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, b⟩, ⟨P_act, ⟨vp, r_b⟩⟩⟩; unfold bpStartDemoteWriteAProg; simp

private theorem realizesBounded_bpStartDemoteWriteA :
    RealizesBounded .exact bpStartDemoteWriteAProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgm := realizesBounded_bpGetMK
  have hat := realizesBounded_bpAllocTbFor
  have hwbm := realizesBounded_bpWriteBktMeta
  realize
  all_goals (
    rcases d with ⟨⟨ctx, b⟩, ⟨P_act, ⟨vp, r_b⟩⟩⟩
    have hv0 := h
    obtain ⟨h16, _, hk, h6k, _, _, hnc_w⟩ := hv0.param_fits
    have h12K := hv0.twelve_K_le
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpStartDemoteWriteAProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b P_act vp r_b : ℕ) :
    BpMetaProg mp 20 (bpStartDemoteWriteAProg ((mp.toCtx, b), (P_act, (vp, r_b)))) := by
  obtain ⟨_, hwbm, _, _, _, _⟩ := hv.write_frames
  unfold bpStartDemoteWriteAProg; simp only [pure_bind]
  exact (BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.bind_prog (bpAllocTbForProg_frame hv P_act) fun _ =>
    BpMetaProg.bind_prog (hwbm b 0 vp) fun _ =>
    hwbm b 1 (if r_b < 6 * mk.2 then r_b + mk.2 else 0)).mono (by decide)

/-- Second write half of starting a `Demote` job (`6` binds, `¬ReadsWidth`). -/
private def bpStartDemoteWriteBProg :
    (BpMetaCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((ctx, b), (P_act, hd_new)) => do
    let mk ← bpGetMKProg ctx
    bpWriteBktMetaProg ((ctx, (b, 2)), hd_new)
    bpWriteBktMetaProg ((ctx, (b, 4)), P_act)
    let ac_new ← pure (2 * mk.2)
    bpWriteBktMetaProg ((ctx, (b, 3)), ac_new)
    bpWriteSlabOwnerProg ((ctx, (P_act, 0)), 2)
    bpWriteSlabOwnerProg ((ctx, (P_act, 1)), b)

@[simp] private theorem runClient_frontier_bpStartDemoteWriteBProg
    (x : (BpMetaCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpStartDemoteWriteBProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, b⟩, ⟨P_act, hd_new⟩⟩; unfold bpStartDemoteWriteBProg; simp

private theorem realizesBounded_bpStartDemoteWriteB :
    RealizesBounded .exact bpStartDemoteWriteBProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgm := realizesBounded_bpGetMK
  have hwbm := realizesBounded_bpWriteBktMeta
  have hwso := realizesBounded_bpWriteSlabOwner
  realize
  all_goals (
    rcases d with ⟨⟨ctx, b⟩, ⟨P_act, hd_new⟩⟩
    have hv0 := h
    obtain ⟨h16, _, hk, h6k, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpStartDemoteWriteBProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b P_act hd_new : ℕ) :
    BpMetaProg mp 20 (bpStartDemoteWriteBProg ((mp.toCtx, b), (P_act, hd_new))) := by
  obtain ⟨_, hwbm, _, _, hwso, _⟩ := hv.write_frames
  unfold bpStartDemoteWriteBProg; simp only [pure_bind]
  exact (BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.bind_prog (hwbm b 2 hd_new) fun _ =>
    BpMetaProg.bind_prog (hwbm b 4 P_act) fun _ =>
    BpMetaProg.bind_prog (hwbm b 3 (2 * mk.2)) fun _ =>
    BpMetaProg.bind_prog (hwso P_act 0 2) fun _ =>
    hwso P_act 1 b).mono (by decide)

/-- Start a `Demote` job on bucket `b` (`3` binds, `¬ReadsWidth`). -/
private def bpStartDemoteProg : BpMetaCtx × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (ctx, (b, (q_b, r_b))) => do
    let vp ← bpSubProg (q_b, 1)
    let ph ← bpStartDemoteReadProg (ctx, (b, vp))
    bpStartDemoteWriteAProg ((ctx, b), (ph.1, (vp, r_b)))
    bpStartDemoteWriteBProg ((ctx, b), ph)

@[simp] private theorem runClient_frontier_bpStartDemoteProg
    (x : BpMetaCtx × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpStartDemoteProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, ⟨b, ⟨q_b, r_b⟩⟩⟩; unfold bpStartDemoteProg; simp

private theorem realizesBounded_bpStartDemote :
    RealizesBounded .exact bpStartDemoteProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hsub := realizesBounded_bpSub
  have hsdr := realizesBounded_bpStartDemoteRead
  have hsdwa := realizesBounded_bpStartDemoteWriteA
  have hsdwb := realizesBounded_bpStartDemoteWriteB
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨b, ⟨q_b, r_b⟩⟩⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpStartDemoteProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b q_b r_b : ℕ) :
    BpMetaProg mp 46 (bpStartDemoteProg (mp.toCtx, (b, (q_b, r_b)))) := by
  unfold bpStartDemoteProg; dsimp only
  exact (BpMetaProg.bind_prog (bpSubProg_frame mp q_b 1) fun vp =>
    BpMetaProg.bind_prog (bpStartDemoteReadProg_frame mp b vp) fun ph =>
    BpMetaProg.bind_prog (bpStartDemoteWriteAProg_frame hv b ph.1 vp r_b) fun _ =>
    bpStartDemoteWriteBProg_frame hv b ph.1 ph.2).mono (by decide)

/-- Demote-check fallback of `bpMaybeStartIdleProg` (`1` bind, `1` `if`, `¬ReadsWidth`). -/
private def bpMaybeStartTryDemoteProg : BpMetaCtx × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | (ctx, (b, (q_b, r_b))) => do
    let mk ← bpGetMKProg ctx
    if 0 < q_b ∧ r_b < 6 * mk.2 ∧ 2 * r_b ≤ 7 * mk.2 then
      bpStartDemoteProg (ctx, (b, (q_b, r_b)))
    else
      pure ()

@[simp] private theorem runClient_frontier_bpMaybeStartTryDemoteProg
    (x : BpMetaCtx × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpMaybeStartTryDemoteProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, ⟨b, ⟨q_b, r_b⟩⟩⟩; unfold bpMaybeStartTryDemoteProg; dsimp only
  simp only [prog_runClient_state_bind, runClient_state_bpGetMKProg]
  split_ifs <;> simp

private theorem realizesBounded_bpMaybeStartTryDemote :
    RealizesBounded .exact bpMaybeStartTryDemoteProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgm := realizesBounded_bpGetMK
  have hsd := realizesBounded_bpStartDemote
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨b, ⟨q_b, r_b⟩⟩⟩
    have hv0 := h
    obtain ⟨h16, _, hk, h6k, _, _, hnc_w⟩ := hv0.param_fits
    have h12K := hv0.twelve_K_le
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpMaybeStartTryDemoteProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b q_b r_b : ℕ) :
    BpMetaProg mp 46 (bpMaybeStartTryDemoteProg (mp.toCtx, (b, (q_b, r_b)))) := by
  unfold bpMaybeStartTryDemoteProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.ite_prog (0 < q_b ∧ r_b < 6 * mk.2 ∧ 2 * r_b ≤ 7 * mk.2)
      (fun _ => bpStartDemoteProg_frame hv b q_b r_b)
      (fun _ => (BpMetaProg.pure_prog ()).mono (C₂ := 46) (by decide))
  exact hf.mono (by decide)

/-- Idle-bucket dispatch half of `maybeStartBktJob` (`5` binds, `1` `if`, `¬ReadsWidth`). -/
private def bpMaybeStartIdleProg : BpMetaCtx × ℕ → Memory.Prog Unit
  | (ctx, b) => do
    let mk ← bpGetMKProg ctx
    let caps ← bpGetCapsProg ctx
    let r_b ← bpReadBktMetaProg (ctx, (b, 1))
    let q_b ← bpReadBktMetaProg (ctx, (b, 0))
    let ul ← bpReadScalarProg (ctx, 10)
    if 5 * mk.2 ≤ r_b ∧ q_b < caps.1.1 ∧ 5 ≤ ul then
      bpStartPromoteProg (ctx, b)
    else
      bpMaybeStartTryDemoteProg (ctx, (b, (q_b, r_b)))

@[simp] private theorem runClient_frontier_bpMaybeStartIdleProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpMaybeStartIdleProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, b⟩; unfold bpMaybeStartIdleProg; dsimp only
  simp only [prog_runClient_state_bind, runClient_state_bpGetMKProg,
    runClient_state_bpGetCapsProg, runClient_state_bpReadBktMetaProg,
    runClient_state_bpReadScalarProg]
  split_ifs <;> simp

private theorem realizesBounded_bpMaybeStartIdle :
    RealizesBounded .exact bpMaybeStartIdleProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgm := realizesBounded_bpGetMK
  have hgc := realizesBounded_bpGetCaps
  have hrbm := realizesBounded_bpReadBktMeta
  have hrs := realizesBounded_bpReadScalar
  have hsp := realizesBounded_bpStartPromote
  have htd := realizesBounded_bpMaybeStartTryDemote
  realize
  all_goals (
    rcases d with ⟨ctx, b⟩
    have hv0 := h
    obtain ⟨h16, _, hk, h6k, _, _, hnc_w⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpMaybeStartIdleProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b : ℕ) :
    BpMetaProg mp 51 (bpMaybeStartIdleProg (mp.toCtx, b)) := by
  unfold bpMaybeStartIdleProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.bind_prog (bpGetCapsProg_frame mp) fun caps =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 1) fun r_b =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 0) fun q_b =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 10) fun ul =>
    BpMetaProg.ite_prog (5 * mk.2 ≤ r_b ∧ q_b < caps.1.1 ∧ 5 ≤ ul)
      (fun _ => (bpStartPromoteProg_frame hv b).mono (C₂ := 46) (by decide))
      (fun _ => bpMaybeStartTryDemoteProg_frame hv b q_b r_b)
  exact hf.mono (by decide)

/-- Realization of `BlockPoolState.maybeStartBktJob` (`1` bind, `¬ReadsWidth`). -/
private def bpMaybeStartMetaProg : BpMetaCtx × ℕ → Memory.Prog Unit
  | (ctx, b) => do
    let ac ← bpReadBktMetaProg (ctx, (b, 3))
    if ac ≠ 0 then
      pure ()
    else
      bpMaybeStartIdleProg (ctx, b)

@[simp] private theorem runClient_frontier_bpMaybeStartMetaProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpMaybeStartMetaProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, b⟩; unfold bpMaybeStartMetaProg
  simp only [prog_runClient_state_bind, runClient_state_bpReadBktMetaProg]
  split_ifs <;> simp

private theorem realizesBounded_bpMaybeStartMeta :
    RealizesBounded .exact bpMaybeStartMetaProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrbm := realizesBounded_bpReadBktMeta
  have hmsi := realizesBounded_bpMaybeStartIdle
  realize
  all_goals (
    rcases d with ⟨ctx, b⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpMaybeStartMetaProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b : ℕ) :
    BpMetaProg mp 53 (bpMaybeStartMetaProg (mp.toCtx, b)) := by
  unfold bpMaybeStartMetaProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 3) fun ac =>
    BpMetaProg.ite_prog (ac ≠ 0)
      (fun _ => (BpMetaProg.pure_prog ()).mono (C₂ := 51) (by decide))
      (fun _ => bpMaybeStartIdleProg_frame hv b)
  exact hf.mono (by decide)

private theorem bpMaybeStartMetaProg_spec {mp : BpMetaLayout} {w fr b : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr) (hv : (extractBlockPool mp s.mem).CoreValid)
    (hb : b < mp.M) (hn_le : (extractBlockPool mp s.mem).nSide ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpMaybeStartMetaProg (mp.toCtx, b))).mem =
      (extractBlockPool mp s.mem).maybeStartBktJob b := by
  have hM_eq : (extractBlockPool mp s.mem).M = mp.M := rfl
  have hK_eq : (extractBlockPool mp s.mem).K = mp.K := rfl
  have hms_eq : (extractBlockPool mp s.mem).maxSlabs = mp.maxSlabs := rfl
  have h16M := hv_mp.sixteen_M_le
  have h12K := hv_mp.twelve_K_le
  have hK64 := hv_mp.K_ge
  have hmsK := hv_mp.maxSlabs_K_le
  have hM_eq : (extractBlockPool mp s.mem).M = mp.M := rfl
  have hK_eq : (extractBlockPool mp s.mem).K = mp.K := rfl
  have hmb4 := hv_mp.four_maxBlocks_le
  have hBf_mb : (extractBlockPool mp s.mem).B_full < mp.maxBlocks := by
    have h1 : (extractBlockPool mp s.mem).B_full ≤ mp.nCap / mp.K := Nat.div_le_div_right hn_le
    have := hv_mp.div_K_add_two_le; omega
  unfold bpMaybeStartMetaProg BlockPoolState.maybeStartBktJob
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadBktMetaProg,
    clientResult_bpReadBktMeta_actCode]
  by_cases hac : (extractBlockPool mp s.mem).actCode b ≠ 0
  · rw [ite_eq_left hac, ite_eq_left hac]; rfl
  · rw [ite_eq_right hac, ite_eq_right hac]
    unfold bpMaybeStartIdleProg
    rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg, clientResult_bpGetMK,
      StateTransitionSpec.clientState_bind, clientState_bpGetCapsProg, clientResult_bpGetCaps,
      StateTransitionSpec.clientState_bind, clientState_bpReadBktMetaProg,
      clientResult_bpReadBktMeta_r, StateTransitionSpec.clientState_bind,
      clientState_bpReadBktMetaProg, clientResult_bpReadBktMeta_q,
      StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩)]
    dsimp only
    have hul_eq : s.mem (mp.metaBase + 10) = (extractBlockPool mp s.mem).unresLen := rfl
    rw [hul_eq]
    by_cases hprom : 5 * mp.K ≤ (extractBlockPool mp s.mem).r b ∧
        (extractBlockPool mp s.mem).q b < mp.maxSlabs ∧
        5 ≤ (extractBlockPool mp s.mem).unresLen
    · have hprom' : 5 * (extractBlockPool mp s.mem).K ≤ (extractBlockPool mp s.mem).r b ∧
          (extractBlockPool mp s.mem).q b < (extractBlockPool mp s.mem).maxSlabs ∧
          5 ≤ (extractBlockPool mp s.mem).unresLen := hprom
      rw [ite_eq_left hprom, ite_eq_left hprom']
      obtain ⟨_, hidx_ul, _, _⟩ := hv.findPromoteIdx_spec hprom.2.2
      have hul_le := hv.unresLen_le_B_full
      have hidx_mb : (extractBlockPool mp s.mem).findPromoteIdx < mp.maxBlocks := by omega
      have hP_lt := (hv.unres_fwd _ hidx_ul).1
      have hPl_lt := (hv.unres_fwd ((extractBlockPool mp s.mem).unresLen - 1) (by omega)).1
      unfold bpStartPromoteProg
      rw [StateTransitionSpec.clientState_bind, clientState_bpFindPromoteIdxProg,
        bpFindPromoteIdxProg_spec, StateTransitionSpec.clientState_bind,
        clientState_bpReadSlabOwnerProg, clientResult_bpReadSlabOwner_unres]
      repeat rw [StateTransitionSpec.clientState_bind]
      rw [writeBktMeta_3 hv_mp hb (by omega),
        writeBktMeta_4 hv_mp hb (by omega),
        writeSlabOwner_1 hv_mp (by omega) (by omega),
        writeSlabOwner_0 hv_mp (by omega) (by omega),
        bpUnresRemoveAtProg_spec hv_mp hidx_mb (by omega) (by omega)]
    · have hprom' : ¬(5 * (extractBlockPool mp s.mem).K ≤ (extractBlockPool mp s.mem).r b ∧
          (extractBlockPool mp s.mem).q b < (extractBlockPool mp s.mem).maxSlabs ∧
          5 ≤ (extractBlockPool mp s.mem).unresLen) := hprom
      rw [ite_eq_right hprom, ite_eq_right hprom']
      unfold bpMaybeStartTryDemoteProg; dsimp only
      rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg, clientResult_bpGetMK]
      dsimp only
      obtain ⟨hq_le, hr_lt, hhd_lt, _, _⟩ := hv.bkt_bounds b hb
      rw [hK_eq] at hr_lt hhd_lt
      by_cases hdem : 0 < (extractBlockPool mp s.mem).q b ∧
          2 * (extractBlockPool mp s.mem).r b ≤ 7 * mp.K
      · have hdem_prog : 0 < (extractBlockPool mp s.mem).q b ∧
            (extractBlockPool mp s.mem).r b < 6 * mp.K ∧
            2 * (extractBlockPool mp s.mem).r b ≤ 7 * mp.K := ⟨hdem.1, hr_lt, hdem.2⟩
        have hdem' : 0 < (extractBlockPool mp s.mem).q b ∧
            2 * (extractBlockPool mp s.mem).r b ≤ 7 * (extractBlockPool mp s.mem).K := hdem
        rw [ite_eq_left hdem_prog, ite_eq_left hdem']
        unfold bpStartDemoteProg; dsimp only
        rw [StateTransitionSpec.clientState_bind, clientState_bpSubProg, clientResult_bpSubProg]
        have hP_lt := (hv.slab_fwd b hb ((extractBlockPool mp s.mem).q b - 1) (by omega)).1
        have hres_dr : (Memory.spec 0).clientResult s
            (bpStartDemoteReadProg (mp.toCtx, (b, (extractBlockPool mp s.mem).q b - 1))) =
            ((extractBlockPool mp s.mem).slabOf b ((extractBlockPool mp s.mem).q b - 1),
             ((extractBlockPool mp s.mem).head b + 5 * mp.K) % (6 * mp.K)) := by
          unfold bpStartDemoteReadProg
          rw [StateTransitionSpec.clientResult_bind, clientState_bpGetMKProg, clientResult_bpGetMK,
            StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOfProg,
            clientResult_bpReadSlabOf, StateTransitionSpec.clientResult_bind,
            clientState_bpReadBktMetaProg, clientResult_bpReadBktMeta_head,
            StateTransitionSpec.clientResult_bind, clientState_bpRingAddProg,
            clientResult_bpRingAdd hhd_lt (by omega)]
          rfl
        rw [StateTransitionSpec.clientState_bind, clientState_bpStartDemoteReadProg, hres_dr,
          StateTransitionSpec.clientState_bind]
        dsimp only
        have hft_bds : 0 < (extractBlockPool mp s.mem).freeTbTop →
            (extractBlockPool mp s.mem).freeTbTop - 1 < 8 * mp.M ∧
            (extractBlockPool mp s.mem).freeTbStack
              ((extractBlockPool mp s.mem).freeTbTop - 1) < 8 * mp.M := fun hpos => by
          have h1 := hv.freeTbTop_lt_tbHighWater
          have h2 := hv.tbHighWater_le_max
          have h3 := (hv.freeTb_valid ((extractBlockPool mp s.mem).freeTbTop - 1) (by omega)).1
          exact ⟨by omega, by omega⟩
        have hms_le : mp.maxSlabs ≤ mp.maxSlabs * mp.K := Nat.le_mul_of_pos_right _ (by omega)
        set P_act := (extractBlockPool mp s.mem).slabOf b ((extractBlockPool mp s.mem).q b - 1)
        set bp₁ := (extractBlockPool mp s.mem).allocTbFor P_act
        set s_wa := (Memory.spec 0).clientState s
          (bpStartDemoteWriteAProg
            ((mp.toCtx, b), (P_act, ((extractBlockPool mp s.mem).q b - 1,
              (extractBlockPool mp s.mem).r b))))
        have hex_wa : extractBlockPool mp s_wa.mem =
            { bp₁ with
              q := BlockPoolState.set1 bp₁.q b ((extractBlockPool mp s.mem).q b - 1)
              r := BlockPoolState.set1 bp₁.r b
                ((extractBlockPool mp s.mem).r b + (extractBlockPool mp s.mem).K) } := by
          dsimp only [s_wa]; unfold bpStartDemoteWriteAProg; dsimp only; simp only [pure_bind]
          rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg, clientResult_bpGetMK]
          dsimp only; rw [ite_eq_left hr_lt]
          repeat rw [StateTransitionSpec.clientState_bind]
          rw [writeBktMeta_1 hv_mp hb (by omega),
            writeBktMeta_0 hv_mp hb (by omega),
            bpAllocTbForProg_spec hv_mp (by omega) hft_bds hv.tbHighWater_lt_of_freeTbTop_zero]
          rfl
        unfold bpStartDemoteWriteBProg; dsimp only; simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg, clientResult_bpGetMK]
        dsimp only
        repeat rw [StateTransitionSpec.clientState_bind]
        have hhd_mod : ((extractBlockPool mp s.mem).head b + 5 * mp.K) % (6 * mp.K) <
            6 * mp.K := Nat.mod_lt _ (by omega)
        rw [writeSlabOwner_1 hv_mp (by omega) (by omega),
          writeSlabOwner_0 hv_mp (by omega) (by omega),
          writeBktMeta_3 hv_mp hb (by omega),
          writeBktMeta_4 hv_mp hb (by omega),
          writeBktMeta_2 hv_mp hb (by omega), hex_wa]
        rfl
      · have hdem_prog : ¬(0 < (extractBlockPool mp s.mem).q b ∧
            (extractBlockPool mp s.mem).r b < 6 * mp.K ∧
            2 * (extractBlockPool mp s.mem).r b ≤ 7 * mp.K) := fun h => hdem ⟨h.1, h.2.2⟩
        have hdem' : ¬(0 < (extractBlockPool mp s.mem).q b ∧
            2 * (extractBlockPool mp s.mem).r b ≤ 7 * (extractBlockPool mp s.mem).K) := hdem
        rw [ite_eq_right hdem_prog, ite_eq_right hdem']; rfl

/-! ### `bpActStepMetaProg` (`actStepOne`) and `bpBktTickMetaProg` (`bktTickOne`) -/

/-- Read `(P_act, (t_cur, t_act))` for an active `Promote` step (`6` binds, `¬ReadsWidth`). -/
private def bpActPromCoordsProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((ctx, b), cur) => do
    let P_act ← bpReadBktMetaProg (ctx, (b, 4))
    let tb ← bpReadSlabOwnerProg (ctx, (P_act, 2))
    let hd ← bpReadBktMetaProg (ctx, (b, 2))
    let rk_cur ← bpRingAddProg (ctx, (hd, cur))
    let idx_tr ← bpTailRingIdxProg (ctx, (b, rk_cur))
    let t_cur ← bpReadTailDirRawProg (ctx, idx_tr)
    let t_act ← bpTbSlotProg (ctx, (tb, cur))
    pure (P_act, (t_cur, t_act))

@[simp] private theorem runClient_state_bpActPromCoordsProg
    (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpActPromCoordsProg x)).2.1 = s := by
  rcases x with ⟨⟨ctx, b⟩, cur⟩; unfold bpActPromCoordsProg; simp

private theorem clientState_bpActPromCoordsProg (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpActPromCoordsProg x) = s :=
  runClient_state_bpActPromCoordsProg x s

private theorem realizesBounded_bpActPromCoords :
    RealizesBounded .exact bpActPromCoordsProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrbm := realizesBounded_bpReadBktMeta
  have hrso := realizesBounded_bpReadSlabOwner
  have hra := realizesBounded_bpRingAdd
  have htri := realizesBounded_bpTailRingIdx
  have hrtd := realizesBounded_bpReadTailDirRaw
  have hts := realizesBounded_bpTbSlot
  realize
  all_goals (
    rcases d with ⟨⟨ctx, b⟩, cur⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpActPromCoordsProg_frame (mp : BpMetaLayout) (b cur : ℕ) :
    BpMetaProg mp 8 (bpActPromCoordsProg ((mp.toCtx, b), cur)) := by
  unfold bpActPromCoordsProg
  exact (BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 4) fun P_act =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp P_act 2) fun tb =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 2) fun hd =>
    BpMetaProg.bind_prog (bpRingAddProg_frame mp hd cur) fun rk_cur =>
    BpMetaProg.bind_prog (bpTailRingIdxProg_frame mp b rk_cur) fun idx_tr =>
    BpMetaProg.bind_prog (bpReadTailDirRawProg_frame mp idx_tr) fun t_cur =>
    BpMetaProg.bind_prog (bpTbSlotProg_frame mp tb cur) fun t_act =>
    BpMetaProg.pure_prog (P_act, (t_cur, t_act))).mono (by decide)

/-- First commit half when finishing a `Promote` job (`5` binds, `¬ReadsWidth`). -/
private def bpActPromFinAProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((ctx, b), P_act) => do
    let caps ← bpGetCapsProg ctx
    let vp ← bpReadBktMetaProg (ctx, (b, 0))
    let tb_old ← bpReadSlabOwnerProg (ctx, (P_act, 2))
    bpFreeTbProg (ctx, tb_old)
    let vp1 ← pure (if vp < caps.1.1 then vp + 1 else 0)
    bpWriteBktMetaProg ((ctx, (b, 0)), vp1)
    pure vp

@[simp] private theorem runClient_frontier_bpActPromFinAProg
    (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpActPromFinAProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, b⟩, P_act⟩; unfold bpActPromFinAProg; simp

private theorem realizesBounded_bpActPromFinA :
    RealizesBounded .exact bpActPromFinAProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgc := realizesBounded_bpGetCaps
  have hrbm := realizesBounded_bpReadBktMeta
  have hrso := realizesBounded_bpReadSlabOwner
  have hft := realizesBounded_bpFreeTb
  have hwbm := realizesBounded_bpWriteBktMeta
  realize
  all_goals (
    rcases d with ⟨⟨ctx, b⟩, P_act⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, hms, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpActPromFinAProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b P_act : ℕ) :
    BpMetaProg mp 14 (bpActPromFinAProg ((mp.toCtx, b), P_act)) := by
  obtain ⟨_, hwbm, _, _, _, _⟩ := hv.write_frames
  unfold bpActPromFinAProg; simp only [pure_bind]
  exact (BpMetaProg.bind_prog (bpGetCapsProg_frame mp) fun caps =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 0) fun vp =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp P_act 2) fun tb_old =>
    BpMetaProg.bind_prog (bpFreeTbProg_frame hv tb_old) fun _ =>
    BpMetaProg.bind_prog (hwbm b 0 (if vp < caps.1.1 then vp + 1 else 0)) fun _ =>
    BpMetaProg.pure_prog vp).mono (by decide)

/-- Final slab/block writes when finishing a `Promote` job (`4` binds, `¬ReadsWidth`). -/
private def bpActPromFinCProg : (BpMetaCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((ctx, b), (P_act, vp)) => do
    bpWriteBktMetaProg ((ctx, (b, 3)), 0)
    bpWriteSlabOfProg ((ctx, (b, vp)), P_act)
    bpWriteSlabOwnerProg ((ctx, (P_act, 0)), 1)
    bpWriteSlabOwnerProg ((ctx, (P_act, 2)), vp)

@[simp] private theorem runClient_frontier_bpActPromFinCProg
    (x : (BpMetaCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpActPromFinCProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, b⟩, ⟨P_act, vp⟩⟩; unfold bpActPromFinCProg; simp

private theorem realizesBounded_bpActPromFinC :
    RealizesBounded .exact bpActPromFinCProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwbm := realizesBounded_bpWriteBktMeta
  have hwsl := realizesBounded_bpWriteSlabOf
  have hwso := realizesBounded_bpWriteSlabOwner
  realize
  all_goals (
    rcases d with ⟨⟨ctx, b⟩, ⟨P_act, vp⟩⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpActPromFinCProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b P_act vp : ℕ) :
    BpMetaProg mp 16 (bpActPromFinCProg ((mp.toCtx, b), (P_act, vp))) := by
  obtain ⟨_, hwbm, hwsl, _, hwso, _⟩ := hv.write_frames
  unfold bpActPromFinCProg
  exact (BpMetaProg.bind_prog (hwbm b 3 0) fun _ =>
    BpMetaProg.bind_prog (hwsl b vp P_act) fun _ =>
    BpMetaProg.bind_prog (hwso P_act 0 1) fun _ =>
    hwso P_act 2 vp).mono (by decide)

/-- Second commit half when finishing a `Promote` job (`6` binds, `¬ReadsWidth`). -/
private def bpActPromFinBProg : (BpMetaCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((ctx, b), (P_act, vp)) => do
    let mk ← bpGetMKProg ctx
    let r_b ← bpReadBktMetaProg (ctx, (b, 1))
    let hd ← bpReadBktMetaProg (ctx, (b, 2))
    let hd_new ← bpRingAddProg (ctx, (hd, mk.2))
    let r_new ← bpSubProg (r_b, mk.2)
    bpWriteBktMetaProg ((ctx, (b, 1)), r_new)
    bpWriteBktMetaProg ((ctx, (b, 2)), hd_new)
    bpActPromFinCProg ((ctx, b), (P_act, vp))

@[simp] private theorem runClient_frontier_bpActPromFinBProg
    (x : (BpMetaCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpActPromFinBProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, b⟩, ⟨P_act, vp⟩⟩; unfold bpActPromFinBProg; simp

private theorem realizesBounded_bpActPromFinB :
    RealizesBounded .exact bpActPromFinBProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgm := realizesBounded_bpGetMK
  have hrbm := realizesBounded_bpReadBktMeta
  have hra := realizesBounded_bpRingAdd
  have hsub := realizesBounded_bpSub
  have hwbm := realizesBounded_bpWriteBktMeta
  have hfc := realizesBounded_bpActPromFinC
  realize
  all_goals (
    rcases d with ⟨⟨ctx, b⟩, ⟨P_act, vp⟩⟩
    have hv0 := h
    obtain ⟨h16, _, hk, h6k, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpActPromFinBProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b P_act vp : ℕ) :
    BpMetaProg mp 28 (bpActPromFinBProg ((mp.toCtx, b), (P_act, vp))) := by
  obtain ⟨_, hwbm, _, _, _, _⟩ := hv.write_frames
  unfold bpActPromFinBProg; dsimp only
  exact (BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 1) fun r_b =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 2) fun hd =>
    BpMetaProg.bind_prog (bpRingAddProg_frame mp hd mk.2) fun hd_new =>
    BpMetaProg.bind_prog (bpSubProg_frame mp r_b mk.2) fun r_new =>
    BpMetaProg.bind_prog (hwbm b 1 r_new) fun _ =>
    BpMetaProg.bind_prog (hwbm b 2 hd_new) fun _ =>
    bpActPromFinCProg_frame hv b P_act vp).mono (by decide)

/-- Inner `cur < r_b` execution of `Promote` (`5` binds max, `¬ReadsWidth`). -/
private def bpActPromoteRunProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((ctx, b), ac) => do
    let mk ← bpGetMKProg ctx
    let cur ← bpSubProg (ac, 1)
    let coords ← bpActPromCoordsProg ((ctx, b), cur)
    let osw ← bpSwapTailMetaProg (ctx, coords.2)
    if cur < mk.2 - 1 then do
      let ac1 ← pure (if ac < mk.2 then ac + 1 else 0)
      bpWriteBktMetaProg ((ctx, (b, 3)), ac1)
      pure osw
    else do
      let vp ← bpActPromFinAProg ((ctx, b), coords.1)
      bpActPromFinBProg ((ctx, b), (coords.1, vp))
      pure osw

@[simp] private theorem runClient_frontier_bpActPromoteRunProg
    (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpActPromoteRunProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, b⟩, ac⟩; unfold bpActPromoteRunProg; dsimp only; simp only [pure_bind]
  simp only [prog_runClient_state_bind, runClient_state_bpGetMKProg, runClient_fst_bpGetMKProg,
    runClient_state_bpSubProg, runClient_fst_bpSubProg, runClient_state_bpActPromCoordsProg]
  split_ifs <;> simp

private theorem realizesBounded_bpActPromoteRun :
    RealizesBounded .exact bpActPromoteRunProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgm := realizesBounded_bpGetMK
  have hsub := realizesBounded_bpSub
  have hapc := realizesBounded_bpActPromCoords
  have hstm := realizesBounded_bpSwapTailMeta
  have hwbm := realizesBounded_bpWriteBktMeta
  have hfa := realizesBounded_bpActPromFinA
  have hfb := realizesBounded_bpActPromFinB
  realize
  all_goals (
    rcases d with ⟨⟨ctx, b⟩, ac⟩
    have hv0 := h
    obtain ⟨h16, _, hk, h6k, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpActPromoteRunProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b ac : ℕ) :
    BpMetaProg mp 94 (bpActPromoteRunProg ((mp.toCtx, b), ac)) := by
  obtain ⟨_, hwbm, _, _, _, _⟩ := hv.write_frames
  unfold bpActPromoteRunProg; dsimp only; simp only [pure_bind]
  have hf := BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.bind_prog (bpSubProg_frame mp ac 1) fun cur =>
    BpMetaProg.bind_prog (bpActPromCoordsProg_frame mp b cur) fun coords =>
    BpMetaProg.bind_prog (bpSwapTailMetaProg_frame hv coords.2.1 coords.2.2) fun osw =>
    BpMetaProg.ite_prog (cur < mk.2 - 1)
      (fun _ =>
        (BpMetaProg.bind_prog (hwbm b 3 (if ac < mk.2 then ac + 1 else 0)) fun _ =>
          BpMetaProg.pure_prog osw).mono (C₂ := 42) (by decide))
      (fun _ =>
        (BpMetaProg.bind_prog (bpActPromFinAProg_frame hv b coords.1) fun vp =>
          BpMetaProg.bind_prog (bpActPromFinBProg_frame hv b coords.1 vp) fun _ =>
          BpMetaProg.pure_prog osw).mono (C₂ := 42) (by decide))
  exact hf.mono (by decide)

/-- Active `Promote` branch of `actStepOne` (`2` binds, `¬ReadsWidth`). -/
private def bpActPromoteStepProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((ctx, b), ac) => do
    let r_b ← bpReadBktMetaProg (ctx, (b, 1))
    let cur ← bpSubProg (ac, 1)
    if r_b ≤ cur then
      pure (0, (0, 0))
    else
      bpActPromoteRunProg ((ctx, b), ac)

@[simp] private theorem runClient_frontier_bpActPromoteStepProg
    (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpActPromoteStepProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, b⟩, ac⟩; unfold bpActPromoteStepProg; dsimp only
  simp only [prog_runClient_state_bind, runClient_state_bpReadBktMetaProg,
    runClient_state_bpSubProg]
  split_ifs <;> simp

private theorem realizesBounded_bpActPromoteStep :
    RealizesBounded .exact bpActPromoteStepProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrbm := realizesBounded_bpReadBktMeta
  have hsub := realizesBounded_bpSub
  have hapr := realizesBounded_bpActPromoteRun
  realize
  all_goals (
    rcases d with ⟨⟨ctx, b⟩, ac⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpActPromoteStepProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b ac : ℕ) :
    BpMetaProg mp 96 (bpActPromoteStepProg ((mp.toCtx, b), ac)) := by
  unfold bpActPromoteStepProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 1) fun r_b =>
    BpMetaProg.bind_prog (bpSubProg_frame mp ac 1) fun cur =>
    BpMetaProg.ite_prog (r_b ≤ cur)
      (fun _ => (BpMetaProg.pure_prog (0, (0, 0))).mono (C₂ := 94) (by decide))
      (fun _ => bpActPromoteRunProg_frame hv b ac)
  exact hf.mono (by decide)

/-- Read `(P_act, (rk, tIdx))` and write the 3 tail-ring updates for a `Demote` step (`6` binds,
`¬ReadsWidth`). -/
private def bpActDemoteBaseProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((ctx, b), cur') => do
    let P_act ← bpReadBktMetaProg (ctx, (b, 4))
    let tb ← bpReadSlabOwnerProg (ctx, (P_act, 2))
    let hd ← bpReadBktMetaProg (ctx, (b, 2))
    let rk ← bpRingAddProg (ctx, (hd, cur'))
    let tIdx ← bpTbSlotProg (ctx, (tb, cur'))
    bpWriteTailRingProg ((ctx, (b, rk)), tIdx)
    bpWriteTailOwnerProg ((ctx, (tIdx, 0)), b)
    bpWriteTailOwnerProg ((ctx, (tIdx, 1)), rk)
    pure P_act

@[simp] private theorem runClient_frontier_bpActDemoteBaseProg
    (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpActDemoteBaseProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, b⟩, cur'⟩; unfold bpActDemoteBaseProg; simp

private theorem realizesBounded_bpActDemoteBase :
    RealizesBounded .exact bpActDemoteBaseProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrbm := realizesBounded_bpReadBktMeta
  have hrso := realizesBounded_bpReadSlabOwner
  have hra := realizesBounded_bpRingAdd
  have hts := realizesBounded_bpTbSlot
  have hwtr := realizesBounded_bpWriteTailRing
  have hwto := realizesBounded_bpWriteTailOwner
  realize
  all_goals (
    rcases d with ⟨⟨ctx, b⟩, cur'⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpActDemoteBaseProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b cur' : ℕ) :
    BpMetaProg mp 18 (bpActDemoteBaseProg ((mp.toCtx, b), cur')) := by
  obtain ⟨_, _, _, _, _, hwto⟩ := hv.write_frames
  unfold bpActDemoteBaseProg
  exact (BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 4) fun P_act =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp P_act 2) fun tb =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 2) fun hd =>
    BpMetaProg.bind_prog (bpRingAddProg_frame mp hd cur') fun rk =>
    BpMetaProg.bind_prog (bpTbSlotProg_frame mp tb cur') fun tIdx =>
    BpMetaProg.bind_prog (bpWriteTailRingProg_frame hv b rk tIdx) fun _ =>
    BpMetaProg.bind_prog (hwto tIdx 0 b) fun _ =>
    BpMetaProg.bind_prog (hwto tIdx 1 rk) fun _ =>
    BpMetaProg.pure_prog P_act).mono (by decide)

/-- Active `Demote` branch of `actStepOne` (`4` binds max, `¬ReadsWidth`). -/
private def bpActDemoteStepProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((ctx, b), ac) => do
    let mk ← bpGetMKProg ctx
    let cur ← bpSubProg (ac, mk.2)
    let cm1 ← bpSubProg (cur, 1)
    let P_act ← bpActDemoteBaseProg ((ctx, b), cm1)
    if 1 < cur then do
      let acm1 ← bpSubProg (ac, 1)
      bpWriteBktMetaProg ((ctx, (b, 3)), acm1)
      pure (0, (0, 0))
    else do
      bpUnresPushProg (ctx, P_act)
      bpWriteBktMetaProg ((ctx, (b, 3)), 0)
      pure (0, (0, 0))

@[simp] private theorem runClient_frontier_bpActDemoteStepProg
    (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpActDemoteStepProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, b⟩, ac⟩; unfold bpActDemoteStepProg
  simp only [prog_runClient_state_bind, runClient_state_bpGetMKProg, runClient_state_bpSubProg]
  split_ifs <;> simp

private theorem realizesBounded_bpActDemoteStep :
    RealizesBounded .exact bpActDemoteStepProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgm := realizesBounded_bpGetMK
  have hsub := realizesBounded_bpSub
  have hadb := realizesBounded_bpActDemoteBase
  have hwbm := realizesBounded_bpWriteBktMeta
  have hup := realizesBounded_bpUnresPush
  realize
  all_goals (
    rcases d with ⟨⟨ctx, b⟩, ac⟩
    have hv0 := h
    obtain ⟨h16, _, hk, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpActDemoteStepProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b ac : ℕ) :
    BpMetaProg mp 36 (bpActDemoteStepProg ((mp.toCtx, b), ac)) := by
  obtain ⟨_, hwbm, _, _, _, _⟩ := hv.write_frames
  unfold bpActDemoteStepProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.bind_prog (bpSubProg_frame mp ac mk.2) fun cur =>
    BpMetaProg.bind_prog (bpSubProg_frame mp cur 1) fun cm1 =>
    BpMetaProg.bind_prog (bpActDemoteBaseProg_frame hv b cm1) fun P_act =>
    BpMetaProg.ite_prog (1 < cur)
      (fun _ =>
        (BpMetaProg.bind_prog (bpSubProg_frame mp ac 1) fun acm1 =>
          BpMetaProg.bind_prog (hwbm b 3 acm1) fun _ =>
          BpMetaProg.pure_prog (0, (0, 0))).mono (C₂ := 18) (by decide))
      (fun _ =>
        (BpMetaProg.bind_prog (bpUnresPushProg_frame hv P_act) fun _ =>
          BpMetaProg.bind_prog (hwbm b 3 0) fun _ =>
          BpMetaProg.pure_prog (0, (0, 0))).mono (C₂ := 18) (by decide))
  exact hf.mono (by decide)

/-- Realization of `BlockPoolState.actStepOne` (`3` binds, `¬ReadsWidth`). -/
private def bpActStepMetaProg : BpMetaCtx × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | (ctx, b) => do
    let mk ← bpGetMKProg ctx
    let ac ← bpReadBktMetaProg (ctx, (b, 3))
    if ac = 0 then
      pure (0, (0, 0))
    else if ac ≤ mk.2 then
      bpActPromoteStepProg ((ctx, b), ac)
    else
      bpActDemoteStepProg ((ctx, b), ac)

@[simp] private theorem runClient_frontier_bpActStepMetaProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpActStepMetaProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, b⟩; unfold bpActStepMetaProg
  simp only [prog_runClient_state_bind, runClient_state_bpGetMKProg,
    runClient_state_bpReadBktMetaProg]
  split_ifs <;> simp

private theorem realizesBounded_bpActStepMeta :
    RealizesBounded .exact bpActStepMetaProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgm := realizesBounded_bpGetMK
  have hrbm := realizesBounded_bpReadBktMeta
  have haps := realizesBounded_bpActPromoteStep
  have hads := realizesBounded_bpActDemoteStep
  realize
  all_goals (
    rcases d with ⟨ctx, b⟩
    have hv0 := h
    obtain ⟨h16, _, hk, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpActStepMetaProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b : ℕ) :
    BpMetaProg mp 98 (bpActStepMetaProg (mp.toCtx, b)) := by
  unfold bpActStepMetaProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 3) fun ac =>
    BpMetaProg.ite_prog (ac = 0)
      (fun _ => (BpMetaProg.pure_prog (0, (0, 0))).mono (C₂ := 96) (by decide))
      (fun _ =>
        BpMetaProg.ite_prog (ac ≤ mk.2)
          (fun _ => bpActPromoteStepProg_frame hv b ac)
          (fun _ => (bpActDemoteStepProg_frame hv b ac).mono (C₂ := 96) (by decide)))
  exact hf.mono (by decide)

private theorem bpActStepMetaProg_spec {mp : BpMetaLayout} {w fr b : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr) (hv : (extractBlockPool mp s.mem).CoreValid)
    (hb : b < mp.M) (hn_le : (extractBlockPool mp s.mem).nSide ≤ mp.nCap)
    (hprom_q : (extractBlockPool mp s.mem).actCode b = mp.K →
      (extractBlockPool mp s.mem).q b < mp.maxSlabs) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s (bpActStepMetaProg (mp.toCtx, b))
    let res := (Memory.spec 0).clientResult s (bpActStepMetaProg (mp.toCtx, b))
    extractBlockPool mp s'.mem = (bp.actStepOne b).1 ∧
    res = encodeOptSwap (bp.actStepOne b).2 := by
  dsimp only
  have h16M := hv_mp.sixteen_M_le
  have h12K := hv_mp.twelve_K_le
  have hK64 := hv_mp.K_ge
  have hmsK := hv_mp.maxSlabs_K_le
  have h8MK := hv_mp.eight_MK_le
  have hmb4 := hv_mp.four_maxBlocks_le
  have hms_le : mp.maxSlabs ≤ mp.maxSlabs * mp.K := Nat.le_mul_of_pos_right _ (by omega)
  have hBf_mb : (extractBlockPool mp s.mem).B_full < mp.maxBlocks := by
    have h1 : (extractBlockPool mp s.mem).B_full ≤ mp.nCap / mp.K := Nat.div_le_div_right hn_le
    have := hv_mp.div_K_add_two_le; omega
  obtain ⟨hq_le, hr_lt, hhd_lt, hc_le, _⟩ := hv.bkt_bounds b hb
  have hpure_st : ∀ {α : Type} (x : α) (st : Memory.State),
      (Memory.spec 0).clientState st (pure x) = st :=
    fun _ _ => rfl
  unfold bpActStepMetaProg BlockPoolState.actStepOne
  rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg,
    StateTransitionSpec.clientResult_bind, clientState_bpGetMKProg, clientResult_bpGetMK,
    StateTransitionSpec.clientState_bind, clientState_bpReadBktMetaProg,
    StateTransitionSpec.clientResult_bind, clientState_bpReadBktMetaProg,
    clientResult_bpReadBktMeta_actCode]
  dsimp only
  have hM_eq : (extractBlockPool mp s.mem).M = mp.M := rfl
  have hK_eq : (extractBlockPool mp s.mem).K = mp.K := rfl
  rw [hK_eq] at hr_lt hhd_lt hc_le
  by_cases hc0 : (extractBlockPool mp s.mem).actCode b = 0
  · simp only [hc0, ↓reduceIte]; exact ⟨rfl, rfl⟩
  · simp only [hc0, ↓reduceIte]
    obtain ⟨hP_lt, hP_tag2, hP_m1⟩ := hv.act_fwd b hb hc0
    obtain ⟨htb_lt, _⟩ := hv.tb_fwd ((extractBlockPool mp s.mem).actBlk b) hP_lt.le (Or.inr hP_tag2)
    have htb_8M : (extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).actBlk b) <
        8 * mp.M := htb_lt.trans_le hv.tbHighWater_le_max
    by_cases hcK : (extractBlockPool mp s.mem).actCode b ≤ mp.K
    · have hcK' : (extractBlockPool mp s.mem).actCode b ≤ (extractBlockPool mp s.mem).K := hcK
      simp only [hcK, hcK', ↓reduceIte]
      unfold bpActPromoteStepProg; dsimp only
      rw [StateTransitionSpec.clientState_bind, clientState_bpReadBktMetaProg,
        StateTransitionSpec.clientResult_bind, clientState_bpReadBktMetaProg,
        clientResult_bpReadBktMeta_r,
        StateTransitionSpec.clientState_bind, clientState_bpSubProg,
        StateTransitionSpec.clientResult_bind, clientState_bpSubProg, clientResult_bpSubProg]
      by_cases hr_le : (extractBlockPool mp s.mem).r b ≤ (extractBlockPool mp s.mem).actCode b - 1
      · simp only [hr_le, ↓reduceIte]; exact ⟨rfl, rfl⟩
      · simp only [hr_le, ↓reduceIte]
        unfold bpActPromoteRunProg; dsimp only; simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg,
          StateTransitionSpec.clientResult_bind, clientState_bpGetMKProg, clientResult_bpGetMK,
          StateTransitionSpec.clientState_bind, clientState_bpSubProg,
          StateTransitionSpec.clientResult_bind, clientState_bpSubProg, clientResult_bpSubProg]
        dsimp only
        have hcur_lt_K : (extractBlockPool mp s.mem).actCode b - 1 < mp.K := by omega
        have hcur_eq : (extractBlockPool mp s.mem).actCur b =
            (extractBlockPool mp s.mem).actCode b - 1 := by
          unfold BlockPoolState.actCur; rw [ite_eq_right hc0, ite_eq_left hcK']
        have hcoords : (Memory.spec 0).clientResult s
            (bpActPromCoordsProg ((mp.toCtx, b), (extractBlockPool mp s.mem).actCode b - 1)) =
            ((extractBlockPool mp s.mem).actBlk b,
             ((extractBlockPool mp s.mem).tailRing b
                (((extractBlockPool mp s.mem).head b +
                  ((extractBlockPool mp s.mem).actCode b - 1)) % (6 * mp.K)),
              (extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).actBlk b) * mp.K +
                ((extractBlockPool mp s.mem).actCode b - 1))) := by
          unfold bpActPromCoordsProg
          rw [StateTransitionSpec.clientResult_bind, clientState_bpReadBktMetaProg,
            clientResult_bpReadBktMeta_actBlk,
            StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
            clientResult_bpReadSlabOwner_m2,
            StateTransitionSpec.clientResult_bind, clientState_bpReadBktMetaProg,
            clientResult_bpReadBktMeta_head,
            StateTransitionSpec.clientResult_bind, clientState_bpRingAddProg,
            clientResult_bpRingAdd hhd_lt (by omega),
            StateTransitionSpec.clientResult_bind, clientState_bpTailRingIdxProg,
            clientResult_bpTailRingIdx hb (Nat.mod_lt _ (by omega)),
            StateTransitionSpec.clientResult_bind, clientState_bpReadTailDirRawProg,
            clientResult_bpReadTailDir_ring hb (Nat.mod_lt _ (by omega)),
            StateTransitionSpec.clientResult_bind, clientState_bpTbSlotProg,
            clientResult_bpTbSlot htb_8M hcur_lt_K]
          rfl
        have hlive_c : (extractBlockPool mp s.mem).LiveTail
            ((extractBlockPool mp s.mem).tailRing b
              (((extractBlockPool mp s.mem).head b +
                ((extractBlockPool mp s.mem).actCode b - 1)) % (6 * mp.K))) :=
          ⟨b, hb, (extractBlockPool mp s.mem).actCode b - 1, hcur_eq.le, by omega, rfl⟩
        have hlive_a : (extractBlockPool mp s.mem).LiveTail
            ((extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).actBlk b) * mp.K +
              ((extractBlockPool mp s.mem).actCode b - 1)) := by
          obtain ⟨bo, hrko, hk_ge, hk_lt, htr⟩ := hv.tail_bwd
            ((extractBlockPool mp s.mem).actBlk b) hP_lt.le
            ((extractBlockPool mp s.mem).actCode b - 1) hcur_lt_K (Or.inl hP_lt)
            (Or.inr ⟨hP_tag2, by rw [hP_m1, hcur_eq]⟩)
          obtain ⟨_, _, hhdo, _, _⟩ := hv.bkt_bounds _ bo
          exact ⟨_, bo, _, hk_ge, hk_lt, by rwa [ring_add_diff_mod hhdo hrko]⟩
        have hsw_meta := bpSwapTailMetaProg_spec hv_mp hv hn_le hlive_c hlive_a
        dsimp only at hsw_meta
        rw [StateTransitionSpec.clientState_bind, clientState_bpActPromCoordsProg,
          StateTransitionSpec.clientResult_bind, clientState_bpActPromCoordsProg, hcoords]
        dsimp only
        rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
          hsw_meta.2]
        set s_sw := (Memory.spec 0).clientState s
          (bpSwapTailMetaProg (mp.toCtx,
            ((extractBlockPool mp s.mem).tailRing b
              (((extractBlockPool mp s.mem).head b +
                ((extractBlockPool mp s.mem).actCode b - 1)) % (6 * mp.K)),
             (extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).actBlk b) * mp.K +
              ((extractBlockPool mp s.mem).actCode b - 1))))
        have hex_sw : extractBlockPool mp s_sw.mem =
            ((extractBlockPool mp s.mem).swapTailCoords
              ((extractBlockPool mp s.mem).tailRing b
                (((extractBlockPool mp s.mem).head b +
                  ((extractBlockPool mp s.mem).actCode b - 1)) % (6 * mp.K)))
              ((extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).actBlk b) * mp.K +
                ((extractBlockPool mp s.mem).actCode b - 1))).1 := hsw_meta.1
        have hsw_flds : (extractBlockPool mp s_sw.mem).q b = (extractBlockPool mp s.mem).q b ∧
            (extractBlockPool mp s_sw.mem).r b = (extractBlockPool mp s.mem).r b ∧
            (extractBlockPool mp s_sw.mem).head b = (extractBlockPool mp s.mem).head b ∧
            (extractBlockPool mp s_sw.mem).blkMeta2 ((extractBlockPool mp s.mem).actBlk b) =
              (extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).actBlk b) ∧
            (extractBlockPool mp s_sw.mem).freeTbTop = (extractBlockPool mp s.mem).freeTbTop := by
          rw [hex_sw]; unfold BlockPoolState.swapTailCoords
          split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        by_cases hmid : (extractBlockPool mp s.mem).actCode b - 1 < mp.K - 1
        · have hmid' : ((extractBlockPool mp s.mem).actCode b - 1) + 1 <
              (extractBlockPool mp s.mem).K := by
            change ((extractBlockPool mp s.mem).actCode b - 1) + 1 < mp.K; omega
          have hac_lt_K : (extractBlockPool mp s.mem).actCode b < mp.K := by omega
          simp only [hmid, hmid', ↓reduceIte, ite_eq_left hac_lt_K]
          rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
            hpure_st, writeBktMeta_3 hv_mp hb (by omega), hex_sw]
          exact ⟨rfl, rfl⟩
        · have hmid' : ¬(((extractBlockPool mp s.mem).actCode b - 1) + 1 <
              (extractBlockPool mp s.mem).K) := by
            change ¬(((extractBlockPool mp s.mem).actCode b - 1) + 1 < mp.K); omega
          have hac_eq_K : (extractBlockPool mp s.mem).actCode b = mp.K := by omega
          have hq_lt_ms := hprom_q hac_eq_K
          simp only [hmid, hmid', ↓reduceIte]
          have hftt_lt : (extractBlockPool mp s.mem).freeTbTop < 8 * mp.M :=
            hv.freeTbTop_lt_tbHighWater.trans_le hv.tbHighWater_le_max
          have hfa_res : (Memory.spec 0).clientResult s_sw
              (bpActPromFinAProg ((mp.toCtx, b), (extractBlockPool mp s.mem).actBlk b)) =
              (extractBlockPool mp s_sw.mem).q b := by
            unfold bpActPromFinAProg; simp only [pure_bind]
            rw [StateTransitionSpec.clientResult_bind, clientState_bpGetCapsProg,
              clientResult_bpGetCaps, StateTransitionSpec.clientResult_bind,
              clientState_bpReadBktMetaProg, clientResult_bpReadBktMeta_q,
              StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
              StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind]
            rfl
          set bp_ft := (extractBlockPool mp s_sw.mem).freeTb
            ((extractBlockPool mp s_sw.mem).blkMeta2 ((extractBlockPool mp s.mem).actBlk b))
          have hfa_st : extractBlockPool mp ((Memory.spec 0).clientState s_sw
              (bpActPromFinAProg ((mp.toCtx, b), (extractBlockPool mp s.mem).actBlk b))).mem =
              { bp_ft with
                q := BlockPoolState.set1 bp_ft.q b
                  ((extractBlockPool mp s_sw.mem).q b + 1) } := by
            unfold bpActPromFinAProg; simp only [pure_bind]
            rw [StateTransitionSpec.clientState_bind, clientState_bpGetCapsProg,
              clientResult_bpGetCaps, StateTransitionSpec.clientState_bind,
              clientState_bpReadBktMetaProg, clientResult_bpReadBktMeta_q,
              StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg,
              clientResult_bpReadSlabOwner_m2,
              StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
              hpure_st]
            dsimp only
            have hvp_lt : (extractBlockPool mp s_sw.mem).q b < mp.maxSlabs :=
              hsw_flds.1 ▸ hq_lt_ms
            rw [ite_eq_left hvp_lt,
              writeBktMeta_0 hv_mp hb (by omega),
              bpFreeTbProg_spec hv_mp (hsw_flds.2.2.2.1 ▸ htb_8M) (hsw_flds.2.2.2.2 ▸ hftt_lt)]
          rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hfa_res,
            StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hpure_st]
          set s_fa := (Memory.spec 0).clientState s_sw
            (bpActPromFinAProg ((mp.toCtx, b), (extractBlockPool mp s.mem).actBlk b))
          unfold bpActPromFinBProg bpActPromFinCProg; dsimp only
          rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg, clientResult_bpGetMK]
          dsimp only
          rw [StateTransitionSpec.clientState_bind, clientState_bpReadBktMetaProg,
            clientResult_bpReadBktMeta_r, StateTransitionSpec.clientState_bind,
            clientState_bpReadBktMetaProg, clientResult_bpReadBktMeta_head,
            StateTransitionSpec.clientState_bind, clientState_bpRingAddProg]
          have hhd_fa : (extractBlockPool mp s_fa.mem).head b = bp_ft.head b := by
            rw [hfa_st]
          have hr_fa : (extractBlockPool mp s_fa.mem).r b = bp_ft.r b := by
            rw [hfa_st]
          have hhd_ft_lt : bp_ft.head b < 6 * mp.K := hsw_flds.2.2.1 ▸ hhd_lt
          have hr_ft_lt : bp_ft.r b < 6 * mp.K := hsw_flds.2.1 ▸ hr_lt
          rw [hhd_fa, hr_fa, clientResult_bpRingAdd hhd_ft_lt (by omega),
            StateTransitionSpec.clientState_bind, clientState_bpSubProg, clientResult_bpSubProg]
          repeat rw [StateTransitionSpec.clientState_bind]
          have hvp_lt_ms : (extractBlockPool mp s_sw.mem).q b < mp.maxSlabs :=
            hsw_flds.1 ▸ hq_lt_ms
          rw [writeSlabOwner_2 hv_mp (by omega) (by omega),
            writeSlabOwner_0 hv_mp (by omega) (by omega),
            extractBlockPool_writeSlabOf hv_mp hb hvp_lt_ms (by omega),
            writeBktMeta_3 hv_mp hb (Nat.zero_le _),
            writeBktMeta_2 hv_mp hb (le_trans (Nat.mod_lt _ (by omega)).le (by omega)),
            writeBktMeta_1 hv_mp hb (by omega),
            hfa_st]
          dsimp only [bp_ft]
          rw [hex_sw]
          exact ⟨rfl, rfl⟩
    · -- Demote step (`mp.K < actCode b`)
      have hcK' : ¬((extractBlockPool mp s.mem).actCode b ≤ (extractBlockPool mp s.mem).K) := hcK
      simp only [hcK, hcK', ↓reduceIte]
      have hcur'_lt_K : (extractBlockPool mp s.mem).actCode b - mp.K - 1 < mp.K := by omega
      have htIdx_8MK : (extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).actBlk b) *
          mp.K + ((extractBlockPool mp s.mem).actCode b - mp.K - 1) < 8 * mp.M * mp.K := by
        have hle1 : ((extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).actBlk b) +
            1) * mp.K ≤ (8 * mp.M) * mp.K := Nat.mul_le_mul_right mp.K htb_8M
        rw [Nat.add_one_mul] at hle1; omega
      have hbase_res : (Memory.spec 0).clientResult s
          (bpActDemoteBaseProg ((mp.toCtx, b),
            (extractBlockPool mp s.mem).actCode b - mp.K - 1)) =
          (extractBlockPool mp s.mem).actBlk b := by
        unfold bpActDemoteBaseProg
        rw [StateTransitionSpec.clientResult_bind, clientState_bpReadBktMetaProg,
          clientResult_bpReadBktMeta_actBlk,
          StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
          StateTransitionSpec.clientResult_bind, clientState_bpReadBktMetaProg,
          StateTransitionSpec.clientResult_bind, clientState_bpRingAddProg,
          StateTransitionSpec.clientResult_bind, clientState_bpTbSlotProg,
          StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
          StateTransitionSpec.clientResult_bind]
        rfl
      have hbase_st : extractBlockPool mp ((Memory.spec 0).clientState s
          (bpActDemoteBaseProg ((mp.toCtx, b),
            (extractBlockPool mp s.mem).actCode b - mp.K - 1))).mem =
          { extractBlockPool mp s.mem with
            tailRing := BlockPoolState.set2 (extractBlockPool mp s.mem).tailRing b
              (((extractBlockPool mp s.mem).head b +
                ((extractBlockPool mp s.mem).actCode b - mp.K - 1)) % (6 * mp.K))
              ((extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).actBlk b) * mp.K +
                ((extractBlockPool mp s.mem).actCode b - mp.K - 1))
            tailOwnerBkt := BlockPoolState.set1 (extractBlockPool mp s.mem).tailOwnerBkt
              ((extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).actBlk b) * mp.K +
                ((extractBlockPool mp s.mem).actCode b - mp.K - 1)) b
            tailOwnerRing := BlockPoolState.set1 (extractBlockPool mp s.mem).tailOwnerRing
              ((extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).actBlk b) * mp.K +
                ((extractBlockPool mp s.mem).actCode b - mp.K - 1))
              (((extractBlockPool mp s.mem).head b +
                ((extractBlockPool mp s.mem).actCode b - mp.K - 1)) % (6 * mp.K)) } := by
        unfold bpActDemoteBaseProg
        rw [StateTransitionSpec.clientState_bind, clientState_bpReadBktMetaProg,
          clientResult_bpReadBktMeta_actBlk,
          StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg,
          clientResult_bpReadSlabOwner_m2,
          StateTransitionSpec.clientState_bind, clientState_bpReadBktMetaProg,
          clientResult_bpReadBktMeta_head,
          StateTransitionSpec.clientState_bind, clientState_bpRingAddProg,
          clientResult_bpRingAdd hhd_lt (by omega),
          StateTransitionSpec.clientState_bind, clientState_bpTbSlotProg,
          clientResult_bpTbSlot htb_8M hcur'_lt_K]
        repeat rw [StateTransitionSpec.clientState_bind]
        rw [hpure_st,
          writeTailOwner_1 hv_mp htIdx_8MK (le_trans (Nat.mod_lt _ (by omega)).le (by omega)),
          writeTailOwner_0 hv_mp htIdx_8MK (by omega),
          bpWriteTailRingProg_spec hv_mp hb (Nat.mod_lt _ (by omega)) (by omega)]
      unfold bpActDemoteStepProg; dsimp only
      rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg,
        StateTransitionSpec.clientResult_bind, clientState_bpGetMKProg, clientResult_bpGetMK]
      dsimp only
      rw [StateTransitionSpec.clientState_bind, clientState_bpSubProg,
        StateTransitionSpec.clientResult_bind, clientState_bpSubProg, clientResult_bpSubProg,
        StateTransitionSpec.clientState_bind, clientState_bpSubProg,
        StateTransitionSpec.clientResult_bind, clientState_bpSubProg, clientResult_bpSubProg,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hbase_res]
      by_cases hgt1 : 1 < (extractBlockPool mp s.mem).actCode b - mp.K
      · have hgt1' : 1 < (extractBlockPool mp s.mem).actCode b - (extractBlockPool mp s.mem).K :=
          hgt1
        simp only [hgt1, hgt1', ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, clientState_bpSubProg,
          StateTransitionSpec.clientResult_bind, clientState_bpSubProg, clientResult_bpSubProg,
          StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hpure_st,
          writeBktMeta_3 hv_mp hb (by omega), hbase_st]
        exact ⟨rfl, rfl⟩
      · have hgt1' : ¬(1 < (extractBlockPool mp s.mem).actCode b -
            (extractBlockPool mp s.mem).K) := hgt1
        simp only [hgt1, hgt1', ↓reduceIte]
        rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
          StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hpure_st]
        have hul_le := hv.unresLen_le_B_full
        have hul_b : (extractBlockPool mp ((Memory.spec 0).clientState s
            (bpActDemoteBaseProg ((mp.toCtx, b),
              (extractBlockPool mp s.mem).actCode b - mp.K - 1))).mem).unresLen < mp.maxBlocks := by
          rw [hbase_st]; dsimp only; omega
        rw [writeBktMeta_3 hv_mp hb (Nat.zero_le _),
          bpUnresPushProg_spec hv_mp (by omega) hul_b, hbase_st]
        exact ⟨rfl, rfl⟩

/-- Realization of `BlockPoolState.bktTickOne` (`maybeStartBktJob` + `actStepOne`,
`¬ReadsWidth`). -/
def bpBktTickMetaProg : BpMetaCtx × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | (ctx, b) => do
    bpMaybeStartMetaProg (ctx, b)
    bpActStepMetaProg (ctx, b)

@[simp] theorem runClient_frontier_bpBktTickMetaProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (bpBktTickMetaProg x))).frontier =
      s.frontier := by
  rcases x with ⟨ctx, b⟩; unfold bpBktTickMetaProg; simp

theorem realizesBounded_bpBktTickMeta :
    RealizesBounded .exact bpBktTickMetaProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hms := realizesBounded_bpMaybeStartMeta
  have has := realizesBounded_bpActStepMeta
  realize
  all_goals (
    rcases d with ⟨ctx, b⟩
    have hv0 := h
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0)

theorem bpBktTickMetaProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr) (b : ℕ) :
    BpMetaProg mp 152 (bpBktTickMetaProg (mp.toCtx, b)) := by
  unfold bpBktTickMetaProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpMaybeStartMetaProg_frame hv b) fun _ =>
    bpActStepMetaProg_frame hv b
  exact hf.mono (by decide)

theorem bpBktTickMetaProg_spec {mp : BpMetaLayout} {w fr b : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr) (hv : (extractBlockPool mp s.mem).CoreValid)
    (hb : b < mp.M) (hn_le : (extractBlockPool mp s.mem).nSide ≤ mp.nCap)
    (hbkt_le : (extractBlockPool mp s.mem).bktCount b ≤ mp.maxSlabs * mp.K) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s (bpBktTickMetaProg (mp.toCtx, b))
    let res := (Memory.spec 0).clientResult s (bpBktTickMetaProg (mp.toCtx, b))
    extractBlockPool mp s'.mem = (bp.bktTickOne b).1 ∧
    res = encodeOptSwap (bp.bktTickOne b).2 := by
  dsimp only
  unfold bpBktTickMetaProg BlockPoolState.bktTickOne
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
  set s₁ := (Memory.spec 0).clientState s (bpMaybeStartMetaProg (mp.toCtx, b))
  have hex₁ := bpMaybeStartMetaProg_spec hv_mp hv hb hn_le
  obtain ⟨hv₁, hn₁, hbc₁, _⟩ := hv.maybeStartBktJob_spec hb
  have hv_s₁ : (extractBlockPool mp s₁.mem).CoreValid := hex₁ ▸ hv₁
  have hn_s₁ : (extractBlockPool mp s₁.mem).nSide ≤ mp.nCap := by rw [hex₁, hn₁]; exact hn_le
  have hprom_s₁ : (extractBlockPool mp s₁.mem).actCode b = mp.K →
      (extractBlockPool mp s₁.mem).q b < mp.maxSlabs := fun hac => by
    have hbc_le₁ : (extractBlockPool mp s₁.mem).bktCount b ≤ mp.maxSlabs * mp.K := by
      rw [hex₁, hbc₁]; exact hbkt_le
    exact hv_s₁.prom_q_lt_of_bktCount_le hb hbc_le₁ (Or.inr hac)
  have has := bpActStepMetaProg_spec hv_mp hv_s₁ hb hn_s₁ hprom_s₁
  dsimp only at has
  rw [hex₁] at has
  exact has

/-! ### `bpCommitTopSwapMetaProg`, `bpTopSwapStepMetaProg`, and `bpTopCleanMetaProg` -/

/-- Read `((S, D), ((tagS, m1S), (m2S, (posD, tbD))))` for `commitTopSwap` (`5` binds,
`¬ReadsWidth`). -/
private def bpCommitTopSwapReadProg :
    BpMetaCtx → Memory.Prog ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))))
  | ctx => do
    let S ← bpReadScalarProg (ctx, 14)
    let D ← bpReadScalarProg (ctx, 15)
    let tagS ← bpReadSlabOwnerProg (ctx, (S, 0))
    let m1S ← bpReadSlabOwnerProg (ctx, (S, 1))
    let m2S ← bpReadSlabOwnerProg (ctx, (S, 2))
    let posD ← bpReadSlabOwnerProg (ctx, (D, 1))
    let tbD ← bpReadSlabOwnerProg (ctx, (D, 2))
    pure ((S, D), ((tagS, m1S), (m2S, (posD, tbD))))

@[simp] private theorem runClient_state_bpCommitTopSwapReadProg
    (ctx : BpMetaCtx) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpCommitTopSwapReadProg ctx)).2.1 = s := by
  unfold bpCommitTopSwapReadProg; simp

private theorem clientState_bpCommitTopSwapReadProg (ctx : BpMetaCtx) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpCommitTopSwapReadProg ctx) = s :=
  runClient_state_bpCommitTopSwapReadProg ctx s

private theorem realizesBounded_bpCommitTopSwapRead :
    RealizesBounded .exact bpCommitTopSwapReadProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))))
      (fun w ctx s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hrso := realizesBounded_bpReadSlabOwner
  realize
  all_goals (
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpCommitTopSwapReadProg_frame (mp : BpMetaLayout) :
    BpMetaProg mp 12 (bpCommitTopSwapReadProg mp.toCtx) := by
  unfold bpCommitTopSwapReadProg
  exact (BpMetaProg.bind_prog (bpReadScalarProg_frame mp 14) fun S =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 15) fun D =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp S 0) fun tagS =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp S 1) fun m1S =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp S 2) fun m2S =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp D 1) fun posD =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp D 2) fun tbD =>
    BpMetaProg.pure_prog ((S, D), ((tagS, m1S), (m2S, (posD, tbD))))).mono (by decide)

/-- First base-write half of `commitTopSwap` (`4` binds, `¬ReadsWidth`). -/
private def bpCommitTopSwapBaseAProg : BpMetaCtx × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | (ctx, ((S, D), tagS)) => do
    bpWriteScalarProg ((ctx, 13), 0)
    bpWriteScalarProg ((ctx, 16), 0)
    bpWriteSlabOwnerProg ((ctx, (S, 0)), 0)
    bpWriteSlabOwnerProg ((ctx, (D, 0)), tagS)

@[simp] private theorem runClient_frontier_bpCommitTopSwapBaseAProg
    (x : BpMetaCtx × ((ℕ × ℕ) × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpCommitTopSwapBaseAProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, ⟨⟨S, D⟩, tagS⟩⟩; unfold bpCommitTopSwapBaseAProg; simp

private theorem realizesBounded_bpCommitTopSwapBaseA :
    RealizesBounded .exact bpCommitTopSwapBaseAProg
      (WordEncoding.encode (α := BpMetaCtx × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hws := realizesBounded_bpWriteScalar
  have hwso := realizesBounded_bpWriteSlabOwner
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨⟨S, D⟩, tagS⟩⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpCommitTopSwapBaseAProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (S D tagS : ℕ) :
    BpMetaProg mp 10 (bpCommitTopSwapBaseAProg (mp.toCtx, ((S, D), tagS))) := by
  obtain ⟨hws, _, _, _, hwso, _⟩ := hv.write_frames
  unfold bpCommitTopSwapBaseAProg
  exact (BpMetaProg.bind_prog (hws 13 0) fun _ =>
    BpMetaProg.bind_prog (hws 16 0) fun _ =>
    BpMetaProg.bind_prog (hwso S 0 0) fun _ =>
    hwso D 0 tagS).mono (by decide)

/-- Second base-write half of `commitTopSwap` (`4` binds, `¬ReadsWidth`). -/
private def bpCommitTopSwapBaseBProg :
    BpMetaCtx × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) → Memory.Prog Unit
  | (ctx, ((S, D), ((m1S, m2S), (posD, tbD)))) => do
    bpWriteSlabOwnerProg ((ctx, (S, 1)), posD)
    bpWriteSlabOwnerProg ((ctx, (D, 1)), m1S)
    bpWriteSlabOwnerProg ((ctx, (S, 2)), tbD)
    bpWriteSlabOwnerProg ((ctx, (D, 2)), m2S)

@[simp] private theorem runClient_frontier_bpCommitTopSwapBaseBProg
    (x : BpMetaCtx × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)))) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpCommitTopSwapBaseBProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, ⟨⟨S, D⟩, ⟨⟨m1S, m2S⟩, ⟨posD, tbD⟩⟩⟩⟩
  unfold bpCommitTopSwapBaseBProg; simp

private theorem realizesBounded_bpCommitTopSwapBaseB :
    RealizesBounded .exact bpCommitTopSwapBaseBProg
      (WordEncoding.encode (α := BpMetaCtx × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)))))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwso := realizesBounded_bpWriteSlabOwner
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨⟨S, D⟩, ⟨⟨m1S, m2S⟩, ⟨posD, tbD⟩⟩⟩⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpCommitTopSwapBaseBProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (S D m1S m2S posD tbD : ℕ) :
    BpMetaProg mp 16
      (bpCommitTopSwapBaseBProg (mp.toCtx, ((S, D), ((m1S, m2S), (posD, tbD))))) := by
  obtain ⟨_, _, _, _, hwso, _⟩ := hv.write_frames
  unfold bpCommitTopSwapBaseBProg
  exact (BpMetaProg.bind_prog (hwso S 1 posD) fun _ =>
    BpMetaProg.bind_prog (hwso D 1 m1S) fun _ =>
    BpMetaProg.bind_prog (hwso S 2 tbD) fun _ =>
    hwso D 2 m2S).mono (by decide)

/-- Tag-specific pointer updates of `commitTopSwap` (`4` binds max, `¬ReadsWidth`). -/
private def bpCommitTopSwapPtrsProg :
    BpMetaCtx × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) → Memory.Prog Unit
  | (ctx, ((S, D), ((tagS, m1S), (m2S, (posD, tbD))))) =>
    if tagS = 0 then do
      bpWriteSlabOwnerProg ((ctx, (posD, 3)), S)
      bpWriteSlabOwnerProg ((ctx, (m1S, 3)), D)
      bpWriteTbPhysBlkProg ((ctx, tbD), S)
      bpWriteTbPhysBlkProg ((ctx, m2S), D)
    else if tagS = 1 then do
      bpWriteSlabOfProg ((ctx, (m1S, m2S)), D)
      bpWriteSlabOwnerProg ((ctx, (posD, 3)), S)
      bpWriteTbPhysBlkProg ((ctx, tbD), S)
    else do
      bpWriteBktMetaProg ((ctx, (m1S, 4)), D)
      bpWriteSlabOwnerProg ((ctx, (posD, 3)), S)
      bpWriteTbPhysBlkProg ((ctx, tbD), S)
      bpWriteTbPhysBlkProg ((ctx, m2S), D)

@[simp] private theorem runClient_frontier_bpCommitTopSwapPtrsProg
    (x : BpMetaCtx × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))))) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpCommitTopSwapPtrsProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, ⟨⟨S, D⟩, ⟨⟨tagS, m1S⟩, ⟨m2S, ⟨posD, tbD⟩⟩⟩⟩⟩
  unfold bpCommitTopSwapPtrsProg; dsimp only; split_ifs <;> simp

private theorem realizesBounded_bpCommitTopSwapPtrs :
    RealizesBounded .exact bpCommitTopSwapPtrsProg
      (WordEncoding.encode (α := BpMetaCtx × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ))))))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hwso := realizesBounded_bpWriteSlabOwner
  have hwtb := realizesBounded_bpWriteTbPhysBlk
  have hwsl := realizesBounded_bpWriteSlabOf
  have hwbm := realizesBounded_bpWriteBktMeta
  realize
  all_goals (
    rcases d with ⟨ctx, ⟨⟨S, D⟩, ⟨⟨tagS, m1S⟩, ⟨m2S, ⟨posD, tbD⟩⟩⟩⟩⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpCommitTopSwapPtrsProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (info : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × (ℕ × ℕ)))) :
    BpMetaProg mp 16 (bpCommitTopSwapPtrsProg (mp.toCtx, info)) := by
  rcases info with ⟨⟨S, D⟩, ⟨⟨tagS, m1S⟩, ⟨m2S, ⟨posD, tbD⟩⟩⟩⟩
  obtain ⟨_, hwbm, hwsl, _, hwso, _⟩ := hv.write_frames
  unfold bpCommitTopSwapPtrsProg; dsimp only
  refine BpMetaProg.ite_prog (tagS = 0)
    (fun _ =>
      (BpMetaProg.bind_prog (hwso posD 3 S) fun _ =>
        BpMetaProg.bind_prog (hwso m1S 3 D) fun _ =>
        BpMetaProg.bind_prog (bpWriteTbPhysBlkProg_frame hv tbD S) fun _ =>
        bpWriteTbPhysBlkProg_frame hv m2S D).mono (C₂ := 16) (by decide))
    (fun _ =>
      BpMetaProg.ite_prog (tagS = 1)
        (fun _ =>
          (BpMetaProg.bind_prog (hwsl m1S m2S D) fun _ =>
            BpMetaProg.bind_prog (hwso posD 3 S) fun _ =>
            bpWriteTbPhysBlkProg_frame hv tbD S).mono (C₂ := 16) (by decide))
        (fun _ =>
          (BpMetaProg.bind_prog (hwbm m1S 4 D) fun _ =>
            BpMetaProg.bind_prog (hwso posD 3 S) fun _ =>
            BpMetaProg.bind_prog (bpWriteTbPhysBlkProg_frame hv tbD S) fun _ =>
            bpWriteTbPhysBlkProg_frame hv m2S D).mono (C₂ := 16) (by decide)))

/-- Realization of `BlockPoolState.commitTopSwap` (`4` binds, `¬ReadsWidth`). -/
private def bpCommitTopSwapMetaProg : BpMetaCtx → Memory.Prog Unit
  | ctx => do
    let info ← bpCommitTopSwapReadProg ctx
    bpCommitTopSwapBaseAProg (ctx, (info.1, info.2.1.1))
    bpCommitTopSwapBaseBProg (ctx, (info.1, ((info.2.1.2, info.2.2.1), info.2.2.2)))
    bpCommitTopSwapPtrsProg (ctx, info)

@[simp] private theorem runClient_frontier_bpCommitTopSwapMetaProg
    (ctx : BpMetaCtx) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpCommitTopSwapMetaProg ctx)).2.1.frontier = s.frontier := by
  unfold bpCommitTopSwapMetaProg; simp

private theorem realizesBounded_bpCommitTopSwapMeta :
    RealizesBounded .exact bpCommitTopSwapMetaProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := Unit))
      (fun w ctx s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hcr := realizesBounded_bpCommitTopSwapRead
  have hcba := realizesBounded_bpCommitTopSwapBaseA
  have hcbb := realizesBounded_bpCommitTopSwapBaseB
  have hcp := realizesBounded_bpCommitTopSwapPtrs
  realize
  all_goals (
    have hv0 := h
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0)

private theorem bpCommitTopSwapMetaProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr) :
    BpMetaProg mp 54 (bpCommitTopSwapMetaProg mp.toCtx) := by
  unfold bpCommitTopSwapMetaProg
  exact (BpMetaProg.bind_prog (bpCommitTopSwapReadProg_frame mp) fun info =>
    BpMetaProg.bind_prog (bpCommitTopSwapBaseAProg_frame hv info.1.1 info.1.2 info.2.1.1) fun _ =>
    BpMetaProg.bind_prog
      (bpCommitTopSwapBaseBProg_frame hv info.1.1 info.1.2 info.2.1.2 info.2.2.1
        info.2.2.2.1 info.2.2.2.2) fun _ =>
    bpCommitTopSwapPtrsProg_frame hv info).mono (by decide)

private theorem bpCommitTopSwapMetaProg_spec {mp : BpMetaLayout} {w fr : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr) (hv : (extractBlockPool mp s.mem).CoreValid)
    (hn_le : (extractBlockPool mp s.mem).nSide ≤ mp.nCap)
    (ha1 : (extractBlockPool mp s.mem).topSwapAct = 1) :
    extractBlockPool mp ((Memory.spec 0).clientState s (bpCommitTopSwapMetaProg mp.toCtx)).mem =
      (extractBlockPool mp s.mem).commitTopSwap := by
  have hM_eq : (extractBlockPool mp s.mem).M = mp.M := rfl
  have hK_eq : (extractBlockPool mp s.mem).K = mp.K := rfl
  have hms_eq : (extractBlockPool mp s.mem).maxSlabs = mp.maxSlabs := rfl
  have h16M := hv_mp.sixteen_M_le
  have hmb4 := hv_mp.four_maxBlocks_le
  have hmsK := hv_mp.maxSlabs_K_le
  have hK64 := hv_mp.K_ge
  have hms_le : mp.maxSlabs ≤ mp.maxSlabs * mp.K := Nat.le_mul_of_pos_right _ (by omega)
  have hBf_mb : (extractBlockPool mp s.mem).B_full < mp.maxBlocks := by
    have h1 : (extractBlockPool mp s.mem).B_full ≤ mp.nCap / mp.K := Nat.div_le_div_right hn_le
    have := hv_mp.div_K_add_two_le; omega
  obtain ⟨_, hS_lt, hD_lt, hD_tag0, _⟩ := hv.topSwap_valid ha1
  have htagS_lt3 := hv.blkTag_lt _ hS_lt
  obtain ⟨hposD_ul, _⟩ := hv.unres_bwd _ hD_lt hD_tag0
  obtain ⟨htbD_hw, _⟩ := hv.tb_fwd _ hD_lt.le (Or.inl hD_tag0)
  have hul_le := hv.unresLen_le_B_full
  have hhw_le := hv.tbHighWater_le_max
  have hm1S_le : (extractBlockPool mp s.mem).blkMeta1
      ((extractBlockPool mp s.mem).topSwapSrc) ≤ mp.nCap := by
    rcases (by omega : (extractBlockPool mp s.mem).blkTag
        ((extractBlockPool mp s.mem).topSwapSrc) = 0 ∨
      (extractBlockPool mp s.mem).blkTag ((extractBlockPool mp s.mem).topSwapSrc) = 1 ∨
      (extractBlockPool mp s.mem).blkTag ((extractBlockPool mp s.mem).topSwapSrc) = 2) with
      h0 | h1 | h2
    · have := (hv.unres_bwd _ hS_lt h0).1; omega
    · have := (hv.slab_bwd _ hS_lt h1).1; omega
    · have := (hv.act_bwd _ hS_lt h2).1; omega
  have hm2S_le : (extractBlockPool mp s.mem).blkMeta2
      ((extractBlockPool mp s.mem).topSwapSrc) ≤ mp.nCap := by
    rcases (by omega : (extractBlockPool mp s.mem).blkTag
        ((extractBlockPool mp s.mem).topSwapSrc) = 0 ∨
      (extractBlockPool mp s.mem).blkTag ((extractBlockPool mp s.mem).topSwapSrc) = 1 ∨
      (extractBlockPool mp s.mem).blkTag ((extractBlockPool mp s.mem).topSwapSrc) = 2) with
      h0 | h1 | h2
    · have := (hv.tb_fwd _ hS_lt.le (Or.inl h0)).1; omega
    · obtain ⟨hbS, hvpS, _⟩ := hv.slab_bwd _ hS_lt h1
      have hqS := (hv.bkt_bounds _ hbS).1; omega
    · have := (hv.tb_fwd _ hS_lt.le (Or.inr h2)).1; omega
  have hread_res : (Memory.spec 0).clientResult s (bpCommitTopSwapReadProg mp.toCtx) =
      (((extractBlockPool mp s.mem).topSwapSrc, (extractBlockPool mp s.mem).topSwapDst),
       (((extractBlockPool mp s.mem).blkTag ((extractBlockPool mp s.mem).topSwapSrc),
         (extractBlockPool mp s.mem).blkMeta1 ((extractBlockPool mp s.mem).topSwapSrc)),
        ((extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).topSwapSrc),
         ((extractBlockPool mp s.mem).blkMeta1 ((extractBlockPool mp s.mem).topSwapDst),
          (extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).topSwapDst))))) := by
    unfold bpCommitTopSwapReadProg
    rw [StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩),
      StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩),
      StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
      clientResult_bpReadSlabOwner_tag,
      StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
      clientResult_bpReadSlabOwner_m1,
      StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
      clientResult_bpReadSlabOwner_m2,
      StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
      clientResult_bpReadSlabOwner_m1,
      StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
      clientResult_bpReadSlabOwner_m2]
    rfl
  unfold bpCommitTopSwapMetaProg BlockPoolState.commitTopSwap
  rw [StateTransitionSpec.clientState_bind, clientState_bpCommitTopSwapReadProg, hread_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  dsimp only
  set S := (extractBlockPool mp s.mem).topSwapSrc
  set D := (extractBlockPool mp s.mem).topSwapDst
  set tagS := (extractBlockPool mp s.mem).blkTag S
  set m1S := (extractBlockPool mp s.mem).blkMeta1 S
  set m2S := (extractBlockPool mp s.mem).blkMeta2 S
  set posD := (extractBlockPool mp s.mem).blkMeta1 D
  set tbD := (extractBlockPool mp s.mem).blkMeta2 D
  set s_a := (Memory.spec 0).clientState s (bpCommitTopSwapBaseAProg (mp.toCtx, ((S, D), tagS)))
  have hex_a : extractBlockPool mp s_a.mem =
      { extractBlockPool mp s.mem with
        topSwapAct := 0
        topSwapCur := 0
        blkTag := BlockPoolState.set1
          (BlockPoolState.set1 (extractBlockPool mp s.mem).blkTag S 0) D tagS } := by
    dsimp only [s_a]; unfold bpCommitTopSwapBaseAProg; dsimp only
    repeat rw [StateTransitionSpec.clientState_bind]
    rw [writeSlabOwner_0 hv_mp (by omega) (by omega),
      writeSlabOwner_0 hv_mp (by omega) (Nat.zero_le _),
      writeScalar_16 hv_mp (Nat.zero_le _),
      writeScalar_13 hv_mp (Nat.zero_le _)]
  set s_b := (Memory.spec 0).clientState s_a
    (bpCommitTopSwapBaseBProg (mp.toCtx, ((S, D), ((m1S, m2S), (posD, tbD)))))
  set bp_base : BlockPoolState :=
    { extractBlockPool mp s.mem with
      topSwapAct := 0
      topSwapCur := 0
      blkTag := BlockPoolState.set1
        (BlockPoolState.set1 (extractBlockPool mp s.mem).blkTag S 0) D tagS
      blkMeta1 := BlockPoolState.set1
        (BlockPoolState.set1 (extractBlockPool mp s.mem).blkMeta1 S posD) D m1S
      blkMeta2 := BlockPoolState.set1
        (BlockPoolState.set1 (extractBlockPool mp s.mem).blkMeta2 S tbD) D m2S }
  have hex_b : extractBlockPool mp s_b.mem = bp_base := by
    dsimp only [s_b]; unfold bpCommitTopSwapBaseBProg; dsimp only
    repeat rw [StateTransitionSpec.clientState_bind]
    rw [writeSlabOwner_2 hv_mp (by omega) hm2S_le,
      writeSlabOwner_2 hv_mp (by omega) (by omega),
      writeSlabOwner_1 hv_mp (by omega) hm1S_le,
      writeSlabOwner_1 hv_mp (by omega) (by omega), hex_a]
  change extractBlockPool mp
    ((Memory.spec 0).clientState s_b
      (bpCommitTopSwapPtrsProg (mp.toCtx, ((S, D), ((tagS, m1S), (m2S, (posD, tbD))))))).mem = _
  unfold bpCommitTopSwapPtrsProg; dsimp only
  by_cases ht0 : tagS = 0
  · obtain ⟨hposS_ul, _⟩ := hv.unres_bwd _ hS_lt ht0
    obtain ⟨htbS_hw, _⟩ := hv.tb_fwd _ hS_lt.le (Or.inl ht0)
    rw [ite_eq_left ht0, ite_eq_left ht0]
    repeat rw [StateTransitionSpec.clientState_bind]
    rw [bpWriteTbPhysBlkProg_spec hv_mp (by omega) (by omega),
      bpWriteTbPhysBlkProg_spec hv_mp (by omega) (by omega),
      writeSlabOwner_3 hv_mp (by omega) (by omega),
      writeSlabOwner_3 hv_mp (by omega) (by omega), hex_b]
  · rw [ite_eq_right ht0, ite_eq_right ht0]
    by_cases ht1 : tagS = 1
    · obtain ⟨hbS, hvpS, _⟩ := hv.slab_bwd _ hS_lt ht1
      have hqS := (hv.bkt_bounds _ hbS).1
      rw [ite_eq_left ht1, ite_eq_left ht1]
      repeat rw [StateTransitionSpec.clientState_bind]
      rw [bpWriteTbPhysBlkProg_spec hv_mp (by omega) (by omega),
        writeSlabOwner_3 hv_mp (by omega) (by omega),
        extractBlockPool_writeSlabOf hv_mp (hM_eq ▸ hbS) (hvpS.trans_le (hms_eq ▸ hqS)) (by omega),
        hex_b]
    · have ht2 : tagS = 2 := by omega
      obtain ⟨hbS, _, _⟩ := hv.act_bwd _ hS_lt ht2
      obtain ⟨htbS_hw, _⟩ := hv.tb_fwd _ hS_lt.le (Or.inr ht2)
      rw [ite_eq_right ht1, ite_eq_right ht1]
      repeat rw [StateTransitionSpec.clientState_bind]
      rw [bpWriteTbPhysBlkProg_spec hv_mp (by omega) (by omega),
        bpWriteTbPhysBlkProg_spec hv_mp (by omega) (by omega),
        writeSlabOwner_3 hv_mp (by omega) (by omega),
        writeBktMeta_4 hv_mp (hM_eq ▸ hbS) (by omega), hex_b]

/-- Read `(cur, (p₁, p₂))` for an active `topSwapStepOne` (`5` binds, `¬ReadsWidth`). -/
private def bpTopSwapReadSwProg : BpMetaCtx → Memory.Prog (ℕ × (ℕ × ℕ))
  | ctx => do
    let S ← bpReadScalarProg (ctx, 14)
    let D ← bpReadScalarProg (ctx, 15)
    let cur ← bpReadScalarProg (ctx, 16)
    let p₁ ← bpBlkSlotProg (ctx, (S, cur))
    let p₂ ← bpBlkSlotProg (ctx, (D, cur))
    pure (cur, (p₁, p₂))

@[simp] private theorem runClient_state_bpTopSwapReadSwProg (ctx : BpMetaCtx) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpTopSwapReadSwProg ctx)).2.1 = s := by
  unfold bpTopSwapReadSwProg; simp

private theorem clientState_bpTopSwapReadSwProg (ctx : BpMetaCtx) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpTopSwapReadSwProg ctx) = s :=
  runClient_state_bpTopSwapReadSwProg ctx s

private theorem realizesBounded_bpTopSwapReadSw :
    RealizesBounded .exact bpTopSwapReadSwProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ctx s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hbs := realizesBounded_bpBlkSlot
  realize
  all_goals (
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpTopSwapReadSwProg_frame (mp : BpMetaLayout) :
    BpMetaProg mp 3 (bpTopSwapReadSwProg mp.toCtx) := by
  unfold bpTopSwapReadSwProg
  exact (BpMetaProg.bind_prog (bpReadScalarProg_frame mp 14) fun S =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 15) fun D =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 16) fun cur =>
    BpMetaProg.bind_prog (bpBlkSlotProg_frame mp S cur) fun p₁ =>
    BpMetaProg.bind_prog (bpBlkSlotProg_frame mp D cur) fun p₂ =>
    BpMetaProg.pure_prog (cur, (p₁, p₂))).mono (by decide)

/-- Realization of `BlockPoolState.topSwapStepOne` (`4` binds max, `¬ReadsWidth`). -/
private def bpTopSwapStepMetaProg : BpMetaCtx → Memory.Prog (ℕ × (ℕ × ℕ))
  | ctx => do
    let tsa ← bpReadScalarProg (ctx, 13)
    if tsa = 0 then
      pure (0, (0, 0))
    else do
      let mk ← bpGetMKProg ctx
      let csw ← bpTopSwapReadSwProg ctx
      if csw.1 < mk.2 - 1 then do
        bpWriteScalarProg ((ctx, 16), csw.1 + 1)
        pure (1, csw.2)
      else do
        bpCommitTopSwapMetaProg ctx
        pure (1, csw.2)

@[simp] private theorem runClient_frontier_bpTopSwapStepMetaProg
    (ctx : BpMetaCtx) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpTopSwapStepMetaProg ctx)).2.1.frontier = s.frontier := by
  unfold bpTopSwapStepMetaProg
  simp only [prog_runClient_state_bind, runClient_state_bpReadScalarProg]
  split_ifs
  · rfl
  · simp only [prog_runClient_state_bind, runClient_state_bpGetMKProg,
      runClient_state_bpTopSwapReadSwProg]
    split_ifs <;> simp

private theorem realizesBounded_bpTopSwapStepMeta :
    RealizesBounded .exact bpTopSwapStepMetaProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ctx s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hgm := realizesBounded_bpGetMK
  have hrsw := realizesBounded_bpTopSwapReadSw
  have hws := realizesBounded_bpWriteScalar
  have hcts := realizesBounded_bpCommitTopSwapMeta
  realize
  all_goals (
    have hv0 := h
    obtain ⟨h16, _, hk, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpTopSwapStepMetaProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr) :
    BpMetaProg mp 58 (bpTopSwapStepMetaProg mp.toCtx) := by
  obtain ⟨hws, _, _, _, _, _⟩ := hv.write_frames
  unfold bpTopSwapStepMetaProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpReadScalarProg_frame mp 13) fun tsa =>
    BpMetaProg.ite_prog (tsa = 0)
      (fun _ => (BpMetaProg.pure_prog (0, (0, 0))).mono (C₂ := 57) (by decide))
      (fun _ =>
        BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
        BpMetaProg.bind_prog (bpTopSwapReadSwProg_frame mp) fun csw =>
        BpMetaProg.ite_prog (csw.1 < mk.2 - 1)
          (fun _ =>
            (BpMetaProg.bind_prog (hws 16 (csw.1 + 1)) fun _ =>
              BpMetaProg.pure_prog (1, csw.2)).mono (C₂ := 54) (by decide))
          (fun _ =>
            (BpMetaProg.bind_prog (bpCommitTopSwapMetaProg_frame hv) fun _ =>
              BpMetaProg.pure_prog (1, csw.2)).mono (C₂ := 54) (by decide)))
  exact hf.mono (by decide)

private theorem bpTopSwapStepMetaProg_spec {mp : BpMetaLayout} {w fr : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr) (hv : (extractBlockPool mp s.mem).CoreValid)
    (hn_le : (extractBlockPool mp s.mem).nSide ≤ mp.nCap) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s (bpTopSwapStepMetaProg mp.toCtx)
    let res := (Memory.spec 0).clientResult s (bpTopSwapStepMetaProg mp.toCtx)
    extractBlockPool mp s'.mem = bp.topSwapStepOne.1 ∧
    res = encodeOptSwap bp.topSwapStepOne.2 := by
  dsimp only
  have h12K := hv_mp.twelve_K_le
  have hK64 := hv_mp.K_ge
  have hpure_st : ∀ {α : Type} (x : α) (st : Memory.State),
      (Memory.spec 0).clientState st (pure x) = st :=
    fun _ _ => rfl
  unfold bpTopSwapStepMetaProg BlockPoolState.topSwapStepOne
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩)]
  have htsa_eq : s.mem (mp.metaBase + 13) = (extractBlockPool mp s.mem).topSwapAct := rfl
  rw [htsa_eq]
  have hK_eq : (extractBlockPool mp s.mem).K = mp.K := rfl
  by_cases ha0 : (extractBlockPool mp s.mem).topSwapAct = 0
  · simp only [ha0, ↓reduceIte]; exact ⟨rfl, rfl⟩
  · simp only [ha0, ↓reduceIte]
    have ha1 : (extractBlockPool mp s.mem).topSwapAct = 1 := by
      have := hv.topSwap_act_le; omega
    obtain ⟨hcur_lt, hS_lt, hD_lt, _, _⟩ := hv.topSwap_valid ha1
    rw [hK_eq] at hcur_lt
    have hS_cap : (extractBlockPool mp s.mem).topSwapSrc * mp.K +
        (extractBlockPool mp s.mem).topSwapCur ≤ mp.nCap := by
      have h1 : ((extractBlockPool mp s.mem).topSwapSrc + 1) * mp.K ≤
          (extractBlockPool mp s.mem).B_full * mp.K := Nat.mul_le_mul_right mp.K hS_lt
      rw [Nat.add_one_mul] at h1
      have h2 := hv.nSide_eq; rw [hK_eq] at h2; omega
    have hD_cap : (extractBlockPool mp s.mem).topSwapDst * mp.K +
        (extractBlockPool mp s.mem).topSwapCur ≤ mp.nCap := by
      have h1 : ((extractBlockPool mp s.mem).topSwapDst + 1) * mp.K ≤
          (extractBlockPool mp s.mem).B_full * mp.K := Nat.mul_le_mul_right mp.K hD_lt
      rw [Nat.add_one_mul] at h1
      have h2 := hv.nSide_eq; rw [hK_eq] at h2; omega
    have hrsw : (Memory.spec 0).clientResult s (bpTopSwapReadSwProg mp.toCtx) =
        ((extractBlockPool mp s.mem).topSwapCur,
         ((extractBlockPool mp s.mem).topSwapSrc * mp.K + (extractBlockPool mp s.mem).topSwapCur,
          (extractBlockPool mp s.mem).topSwapDst * mp.K +
            (extractBlockPool mp s.mem).topSwapCur)) := by
      unfold bpTopSwapReadSwProg
      rw [StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
        clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩),
        StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
        clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩),
        StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
        clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩),
        StateTransitionSpec.clientResult_bind, clientState_bpBlkSlotProg]
      have h14 : s.mem (mp.metaBase + 14) = (extractBlockPool mp s.mem).topSwapSrc := rfl
      have h15 : s.mem (mp.metaBase + 15) = (extractBlockPool mp s.mem).topSwapDst := rfl
      have h16 : s.mem (mp.metaBase + 16) = (extractBlockPool mp s.mem).topSwapCur := rfl
      rw [h14, h15, h16, clientResult_bpBlkSlot (by omega) hcur_lt hS_cap,
        StateTransitionSpec.clientResult_bind, clientState_bpBlkSlotProg,
        clientResult_bpBlkSlot (by omega) hcur_lt hD_cap]
      rfl
    rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg,
      StateTransitionSpec.clientResult_bind, clientState_bpGetMKProg, clientResult_bpGetMK,
      StateTransitionSpec.clientState_bind, clientState_bpTopSwapReadSwProg,
      StateTransitionSpec.clientResult_bind, clientState_bpTopSwapReadSwProg, hrsw]
    dsimp only
    by_cases hmid : (extractBlockPool mp s.mem).topSwapCur < mp.K - 1
    · have hmid' : (extractBlockPool mp s.mem).topSwapCur + 1 < (extractBlockPool mp s.mem).K := by
        change (extractBlockPool mp s.mem).topSwapCur + 1 < mp.K; omega
      simp only [hmid, hmid', ↓reduceIte]
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hpure_st,
        writeScalar_16 hv_mp (by omega)]
      exact ⟨rfl, rfl⟩
    · have hmid' : ¬((extractBlockPool mp s.mem).topSwapCur + 1 <
          (extractBlockPool mp s.mem).K) := by
        change ¬((extractBlockPool mp s.mem).topSwapCur + 1 < mp.K); omega
      simp only [hmid, hmid', ↓reduceIte]
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hpure_st,
        bpCommitTopSwapMetaProg_spec hv_mp hv hn_le ha1]
      exact ⟨rfl, rfl⟩

/-- Active `topSwapAct = 1` branch of `topCleanOne` (`4` binds, `¬ReadsWidth`). -/
private def bpTopCleanActProg : BpMetaCtx × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | (ctx, P) => do
    let tss ← bpReadScalarProg (ctx, 14)
    let tsd ← bpReadScalarProg (ctx, 15)
    let tagP ← bpReadSlabOwnerProg (ctx, (P, 0))
    if tss = P ∨ tsd = P ∨ tagP ≠ 0 then
      bpTopSwapStepMetaProg ctx
    else
      pure (0, (0, 0))

@[simp] private theorem runClient_frontier_bpTopCleanActProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpTopCleanActProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, P⟩; unfold bpTopCleanActProg
  simp only [prog_runClient_state_bind, runClient_state_bpReadScalarProg,
    runClient_state_bpReadSlabOwnerProg]
  split_ifs <;> simp

private theorem realizesBounded_bpTopCleanAct :
    RealizesBounded .exact bpTopCleanActProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hrso := realizesBounded_bpReadSlabOwner
  have hts := realizesBounded_bpTopSwapStepMeta
  realize
  all_goals (
    rcases d with ⟨ctx, P⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpTopCleanActProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (P : ℕ) :
    BpMetaProg mp 62 (bpTopCleanActProg (mp.toCtx, P)) := by
  unfold bpTopCleanActProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpReadScalarProg_frame mp 14) fun tss =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 15) fun tsd =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp P 0) fun tagP =>
    BpMetaProg.ite_prog (tss = P ∨ tsd = P ∨ tagP ≠ 0)
      (fun _ => bpTopSwapStepMetaProg_frame hv)
      (fun _ => (BpMetaProg.pure_prog (0, (0, 0))).mono (C₂ := 58) (by decide))
  exact hf.mono (by decide)

/-- Initiate `topSwapAct := 1` on `P = B_full - 2` and execute 1 `topSwapStepOne` (`6` binds,
`¬ReadsWidth`). -/
private def bpStartTopSwapProg : BpMetaCtx × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | (ctx, P) => do
    let idx ← bpFindTopSwapIdxProg ctx
    let D ← bpReadSlabOwnerProg (ctx, (idx, 3))
    bpWriteScalarProg ((ctx, 13), 1)
    bpWriteScalarProg ((ctx, 14), P)
    bpWriteScalarProg ((ctx, 15), D)
    bpWriteScalarProg ((ctx, 16), 0)
    bpTopSwapStepMetaProg ctx

@[simp] private theorem runClient_frontier_bpStartTopSwapProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpStartTopSwapProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, P⟩; unfold bpStartTopSwapProg; simp

private theorem realizesBounded_bpStartTopSwap :
    RealizesBounded .exact bpStartTopSwapProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hft := realizesBounded_bpFindTopSwapIdx
  have hrso := realizesBounded_bpReadSlabOwner
  have hws := realizesBounded_bpWriteScalar
  have hts := realizesBounded_bpTopSwapStepMeta
  realize
  all_goals (
    rcases d with ⟨ctx, P⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpStartTopSwapProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (P : ℕ) :
    BpMetaProg mp 70 (bpStartTopSwapProg (mp.toCtx, P)) := by
  obtain ⟨hws, _, _, _, _, _⟩ := hv.write_frames
  unfold bpStartTopSwapProg
  exact (BpMetaProg.bind_prog (bpFindTopSwapIdxProg_frame mp) fun idx =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp idx 3) fun D =>
    BpMetaProg.bind_prog (hws 13 1) fun _ =>
    BpMetaProg.bind_prog (hws 14 P) fun _ =>
    BpMetaProg.bind_prog (hws 15 D) fun _ =>
    BpMetaProg.bind_prog (hws 16 0) fun _ =>
    bpTopSwapStepMetaProg_frame hv).mono (by decide)

/-- Idle `topSwapAct = 0` branch of `topCleanOne` (`3` binds max, `¬ReadsWidth`). -/
private def bpTopCleanIdleProg : BpMetaCtx × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | (ctx, P) => do
    let tagP ← bpReadSlabOwnerProg (ctx, (P, 0))
    if tagP = 0 then
      pure (0, (0, 0))
    else if tagP = 2 then do
      let m1P ← bpReadSlabOwnerProg (ctx, (P, 1))
      bpActStepMetaProg (ctx, m1P)
    else do
      let ul ← bpReadScalarProg (ctx, 10)
      if 3 ≤ ul then
        bpStartTopSwapProg (ctx, P)
      else
        pure (0, (0, 0))

@[simp] private theorem runClient_frontier_bpTopCleanIdleProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpTopCleanIdleProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, P⟩; unfold bpTopCleanIdleProg
  simp only [prog_runClient_state_bind, runClient_state_bpReadSlabOwnerProg]
  split_ifs
  · rfl
  · simp
  · simp only [prog_runClient_state_bind, runClient_state_bpReadScalarProg]
    split_ifs <;> simp

private theorem realizesBounded_bpTopCleanIdle :
    RealizesBounded .exact bpTopCleanIdleProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrso := realizesBounded_bpReadSlabOwner
  have has := realizesBounded_bpActStepMeta
  have hrs := realizesBounded_bpReadScalar
  have hsts := realizesBounded_bpStartTopSwap
  realize
  all_goals (
    rcases d with ⟨ctx, P⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpTopCleanIdleProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (P : ℕ) :
    BpMetaProg mp 102 (bpTopCleanIdleProg (mp.toCtx, P)) := by
  unfold bpTopCleanIdleProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp P 0) fun tagP =>
    BpMetaProg.ite_prog (tagP = 0)
      (fun _ => (BpMetaProg.pure_prog (0, (0, 0))).mono (C₂ := 100) (by decide))
      (fun _ =>
        BpMetaProg.ite_prog (tagP = 2)
          (fun _ =>
            (BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp P 1) fun m1P =>
              bpActStepMetaProg_frame hv m1P).mono (C₂ := 100) (by decide))
          (fun _ =>
            (BpMetaProg.bind_prog (bpReadScalarProg_frame mp 10) fun ul =>
              BpMetaProg.ite_prog (3 ≤ ul)
                (fun _ => bpStartTopSwapProg_frame hv P)
                (fun _ => (BpMetaProg.pure_prog (0, (0, 0))).mono (C₂ := 70) (by decide))).mono
              (C₂ := 100) (by decide)))
  exact hf.mono (by decide)

/-- Realization of `BlockPoolState.topCleanOne` (`3` binds, `¬ReadsWidth`). -/
def bpTopCleanMetaProg : BpMetaCtx → Memory.Prog (ℕ × (ℕ × ℕ))
  | ctx => do
    let ns ← bpReadScalarProg (ctx, 1)
    let bf_r ← bpDivModKProg (ctx, ns)
    if bf_r.1 < 2 then
      pure (0, (0, 0))
    else do
      let P ← pure (bf_r.1 - 2)
      let tsa ← bpReadScalarProg (ctx, 13)
      if tsa = 1 then
        bpTopCleanActProg (ctx, P)
      else
        bpTopCleanIdleProg (ctx, P)

@[simp] theorem runClient_frontier_bpTopCleanMetaProg (ctx : BpMetaCtx) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (bpTopCleanMetaProg ctx))).frontier =
      s.frontier := by
  unfold bpTopCleanMetaProg
  simp only [prog_runClient_state_bind, runClient_state_bpReadScalarProg,
    runClient_state_bpDivModKProg]
  split_ifs
  · rfl
  · simp only [pure_bind, prog_runClient_state_bind, runClient_state_bpReadScalarProg]
    split_ifs <;> simp

theorem realizesBounded_bpTopCleanMeta :
    RealizesBounded .exact bpTopCleanMetaProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ctx s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hdm := realizesBounded_bpDivModK
  have htca := realizesBounded_bpTopCleanAct
  have htci := realizesBounded_bpTopCleanIdle
  realize
  all_goals (
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

theorem bpTopCleanMetaProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr) :
    BpMetaProg mp 105 (bpTopCleanMetaProg mp.toCtx) := by
  unfold bpTopCleanMetaProg; dsimp only; simp only [pure_bind]
  have hf := BpMetaProg.bind_prog (bpReadScalarProg_frame mp 1) fun ns =>
    BpMetaProg.bind_prog (bpDivModKProg_frame mp ns) fun bf_r =>
    BpMetaProg.ite_prog (bf_r.1 < 2)
      (fun _ => (BpMetaProg.pure_prog (0, (0, 0))).mono (C₂ := 103) (by decide))
      (fun _ =>
        (BpMetaProg.bind_prog (bpReadScalarProg_frame mp 13) fun tsa =>
          BpMetaProg.ite_prog (tsa = 1)
            (fun _ => (bpTopCleanActProg_frame hv (bf_r.1 - 2)).mono (C₂ := 102) (by decide))
            (fun _ => bpTopCleanIdleProg_frame hv (bf_r.1 - 2))).mono (C₂ := 103) (by decide))
  exact hf.mono (by decide)

theorem bpTopCleanMetaProg_spec {mp : BpMetaLayout} {w fr : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr) (hv : (extractBlockPool mp s.mem).CoreValid)
    (hn_le : (extractBlockPool mp s.mem).nSide ≤ mp.nCap)
    (hbkt_le : ∀ b < mp.M, (extractBlockPool mp s.mem).bktCount b ≤ mp.maxSlabs * mp.K) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s (bpTopCleanMetaProg mp.toCtx)
    let res := (Memory.spec 0).clientResult s (bpTopCleanMetaProg mp.toCtx)
    extractBlockPool mp s'.mem = bp.topCleanOne.1 ∧
    res = encodeOptSwap bp.topCleanOne.2 := by
  dsimp only
  have hmb4 := hv_mp.four_maxBlocks_le
  have hBf_mb : (extractBlockPool mp s.mem).B_full < mp.maxBlocks := by
    have h1 : (extractBlockPool mp s.mem).B_full ≤ mp.nCap / mp.K := Nat.div_le_div_right hn_le
    have := hv_mp.div_K_add_two_le; omega
  unfold bpTopCleanMetaProg BlockPoolState.topCleanOne
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inl rfl),
    StateTransitionSpec.clientState_bind, clientState_bpDivModKProg,
    StateTransitionSpec.clientResult_bind, clientState_bpDivModKProg, clientResult_bpDivModK]
  dsimp only
  have hbf_eq : s.mem (mp.metaBase + 1) / mp.K = (extractBlockPool mp s.mem).B_full := rfl
  rw [hbf_eq]
  by_cases hlt2 : (extractBlockPool mp s.mem).B_full < 2
  · simp only [hlt2, ↓reduceIte]; exact ⟨rfl, rfl⟩
  · simp only [hlt2, ↓reduceIte]; simp only [pure_bind]
    have hP_lt : (extractBlockPool mp s.mem).B_full - 2 < (extractBlockPool mp s.mem).B_full := by
      omega
    rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
      StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩)]
    have htsa_eq : s.mem (mp.metaBase + 13) = (extractBlockPool mp s.mem).topSwapAct := rfl
    rw [htsa_eq]
    by_cases ha1 : (extractBlockPool mp s.mem).topSwapAct = 1
    · simp only [ha1, ↓reduceIte]
      unfold bpTopCleanActProg
      rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
        StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
        clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩),
        StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
        StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
        clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩),
        StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg,
        StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_tag]
      have htss_eq : s.mem (mp.metaBase + 14) = (extractBlockPool mp s.mem).topSwapSrc := rfl
      have htsd_eq : s.mem (mp.metaBase + 15) = (extractBlockPool mp s.mem).topSwapDst := rfl
      rw [htss_eq, htsd_eq]
      by_cases hact_cond : (extractBlockPool mp s.mem).topSwapSrc =
          (extractBlockPool mp s.mem).B_full - 2 ∨
          (extractBlockPool mp s.mem).topSwapDst = (extractBlockPool mp s.mem).B_full - 2 ∨
          (extractBlockPool mp s.mem).blkTag ((extractBlockPool mp s.mem).B_full - 2) ≠ 0
      · simp only [hact_cond, ↓reduceIte]
        exact bpTopSwapStepMetaProg_spec hv_mp hv hn_le
      · simp only [hact_cond, ↓reduceIte]
        exact ⟨rfl, rfl⟩
    · simp only [ha1, ↓reduceIte]
      unfold bpTopCleanIdleProg
      rw [StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg,
        StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_tag]
      by_cases ht0 : (extractBlockPool mp s.mem).blkTag
          ((extractBlockPool mp s.mem).B_full - 2) = 0
      · simp only [ht0, ↓reduceIte]; exact ⟨rfl, rfl⟩
      · simp only [ht0, ↓reduceIte]
        by_cases ht2 : (extractBlockPool mp s.mem).blkTag
            ((extractBlockPool mp s.mem).B_full - 2) = 2
        · simp only [ht2, ↓reduceIte]
          obtain ⟨hbP, _, _⟩ := hv.act_bwd _ hP_lt ht2
          rw [StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg,
            StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
            clientResult_bpReadSlabOwner_m1]
          exact bpActStepMetaProg_spec hv_mp hv hbP hn_le
            (fun hac => hv.prom_q_lt_of_bktCount_le hbP (hbkt_le _ hbP) (Or.inr hac))
        · simp only [ht2, ↓reduceIte]
          have ht1 : (extractBlockPool mp s.mem).blkTag
              ((extractBlockPool mp s.mem).B_full - 2) = 1 := by
            have := hv.blkTag_lt _ hP_lt; omega
          rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
            StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
            clientResult_bpReadScalar s (Or.inr ⟨by decide, by decide⟩)]
          have hul_eq : s.mem (mp.metaBase + 10) = (extractBlockPool mp s.mem).unresLen := rfl
          rw [hul_eq]
          by_cases h3 : 3 ≤ (extractBlockPool mp s.mem).unresLen
          · simp only [h3, ↓reduceIte]
            obtain ⟨_, hidx_ul, _⟩ := hv.findTopSwapIdx_spec h3
            obtain ⟨hD_lt, hD_tag0, _⟩ := hv.unres_fwd _ hidx_ul
            have hPD : (extractBlockPool mp s.mem).B_full - 2 ≠
                (extractBlockPool mp s.mem).unresStack
                  ((extractBlockPool mp s.mem).findTopSwapIdx) := fun he => by
              rw [he, hD_tag0] at ht1; exact absurd ht1 (by decide)
            unfold bpStartTopSwapProg
            rw [StateTransitionSpec.clientState_bind, clientState_bpFindTopSwapIdxProg,
              StateTransitionSpec.clientResult_bind, clientState_bpFindTopSwapIdxProg,
              bpFindTopSwapIdxProg_spec,
              StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg,
              StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
              clientResult_bpReadSlabOwner_unres]
            repeat rw [StateTransitionSpec.clientState_bind]
            repeat rw [StateTransitionSpec.clientResult_bind]
            set s_st := (Memory.spec 0).clientState
              ((Memory.spec 0).clientState
                ((Memory.spec 0).clientState
                  ((Memory.spec 0).clientState s
                    (bpWriteScalarProg ((mp.toCtx, 13), 1)))
                  (bpWriteScalarProg ((mp.toCtx, 14), (extractBlockPool mp s.mem).B_full - 2)))
                (bpWriteScalarProg ((mp.toCtx, 15),
                  (extractBlockPool mp s.mem).unresStack
                    ((extractBlockPool mp s.mem).findTopSwapIdx))))
              (bpWriteScalarProg ((mp.toCtx, 16), 0))
            have hex_st : extractBlockPool mp s_st.mem =
                { extractBlockPool mp s.mem with
                  topSwapAct := 1
                  topSwapSrc := (extractBlockPool mp s.mem).B_full - 2
                  topSwapDst := (extractBlockPool mp s.mem).unresStack
                    ((extractBlockPool mp s.mem).findTopSwapIdx)
                  topSwapCur := 0 } := by
              dsimp only [s_st]
              rw [writeScalar_16 hv_mp (Nat.zero_le _),
                writeScalar_15 hv_mp (by omega),
                writeScalar_14 hv_mp (by omega),
                writeScalar_13 hv_mp (by omega)]
            have hv_st : (extractBlockPool mp s_st.mem).CoreValid := by
              rw [hex_st]
              exact
                { M_pos := hv.M_pos
                  K_ge := hv.K_ge
                  bkt_bounds := hv.bkt_bounds
                  blkTag_lt := hv.blkTag_lt
                  blkTag_top := hv.blkTag_top
                  unres_fwd := hv.unres_fwd
                  unres_bwd := hv.unres_bwd
                  slab_fwd := hv.slab_fwd
                  slab_bwd := hv.slab_bwd
                  act_fwd := hv.act_fwd
                  act_bwd := hv.act_bwd
                  tb_fwd := hv.tb_fwd
                  freeTb_valid := hv.freeTb_valid
                  freeTb_inj := hv.freeTb_inj
                  tbHighWater_supply := hv.tbHighWater_supply
                  tbHighWater_le_max := hv.tbHighWater_le_max
                  topSwap_act_le := le_rfl
                  topSwap_valid := fun _ => ⟨hv.K_pos, hP_lt, hD_lt, hD_tag0, hPD⟩
                  tail_fwd := hv.tail_fwd
                  tail_bwd := hv.tail_bwd }
            have hn_st : (extractBlockPool mp s_st.mem).nSide ≤ mp.nCap := by
              rw [hex_st]; exact hn_le
            have hts := bpTopSwapStepMetaProg_spec hv_mp hv_st hn_st
            dsimp only at hts
            rw [hex_st] at hts
            exact hts
          · simp only [h3, ↓reduceIte]; exact ⟨rfl, rfl⟩

/-! ## Section 4: `bpRawPostAppendMetaProg`, `bpPrepPopMetaProg`, and `bpCommitPopMetaProg` -/

/-- Read `((ns, (bf, rem)), t_new)` for `rawPostAppend` (`4` binds, `¬ReadsWidth`). -/
private def bpAppendReadTopProg : BpMetaCtx → Memory.Prog ((ℕ × (ℕ × ℕ)) × ℕ)
  | ctx => do
    let ns ← bpReadScalarProg (ctx, 1)
    let bf_r ← bpDivModKProg (ctx, ns)
    let tb_top ← bpReadSlabOwnerProg (ctx, (bf_r.1, 2))
    let t_new ← bpTbSlotProg (ctx, (tb_top, bf_r.2))
    pure ((ns, bf_r), t_new)

@[simp] private theorem runClient_state_bpAppendReadTopProg (ctx : BpMetaCtx) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpAppendReadTopProg ctx)).2.1 = s := by
  unfold bpAppendReadTopProg; simp

private theorem clientState_bpAppendReadTopProg (ctx : BpMetaCtx) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpAppendReadTopProg ctx) = s :=
  runClient_state_bpAppendReadTopProg ctx s

private theorem realizesBounded_bpAppendReadTop :
    RealizesBounded .exact bpAppendReadTopProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × ℕ))
      (fun w ctx s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hdm := realizesBounded_bpDivModK
  have hrso := realizesBounded_bpReadSlabOwner
  have hts := realizesBounded_bpTbSlot
  realize
  all_goals (
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpAppendReadTopProg_frame (mp : BpMetaLayout) :
    BpMetaProg mp 3 (bpAppendReadTopProg mp.toCtx) := by
  unfold bpAppendReadTopProg
  exact (BpMetaProg.bind_prog (bpReadScalarProg_frame mp 1) fun ns =>
    BpMetaProg.bind_prog (bpDivModKProg_frame mp ns) fun bf_r =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp bf_r.1 2) fun tb_top =>
    BpMetaProg.bind_prog (bpTbSlotProg_frame mp tb_top bf_r.2) fun t_new =>
    BpMetaProg.pure_prog ((ns, bf_r), t_new)).mono (by decide)

/-- Base 5-write commit of `rawPostAppend` (`6` binds, `¬ReadsWidth`). -/
private def bpAppendWriteBaseProg :
    (BpMetaCtx × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog Unit
  | ((ctx, b), ((ns, r_b), (t_new, rk_new))) => do
    let mk ← bpGetMKProg ctx
    let caps ← bpGetCapsProg ctx
    let ns1 ← pure (if ns < caps.2 then ns + 1 else 0)
    let r1 ← pure (if r_b < 6 * mk.2 then r_b + 1 else 0)
    bpWriteScalarProg ((ctx, 1), ns1)
    bpWriteBktMetaProg ((ctx, (b, 1)), r1)
    bpWriteTailRingProg ((ctx, (b, rk_new)), t_new)
    bpWriteTailOwnerProg ((ctx, (t_new, 0)), b)
    bpWriteTailOwnerProg ((ctx, (t_new, 1)), rk_new)

@[simp] private theorem runClient_frontier_bpAppendWriteBaseProg
    (x : (BpMetaCtx × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpAppendWriteBaseProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, b⟩, ⟨⟨ns, r_b⟩, ⟨t_new, rk_new⟩⟩⟩
  unfold bpAppendWriteBaseProg; simp

private theorem realizesBounded_bpAppendWriteBase :
    RealizesBounded .exact bpAppendWriteBaseProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgm := realizesBounded_bpGetMK
  have hgc := realizesBounded_bpGetCaps
  have hws := realizesBounded_bpWriteScalar
  have hwbm := realizesBounded_bpWriteBktMeta
  have hwtr := realizesBounded_bpWriteTailRing
  have hwto := realizesBounded_bpWriteTailOwner
  realize
  all_goals (
    rcases d with ⟨⟨ctx, b⟩, ⟨⟨ns, r_b⟩, ⟨t_new, rk_new⟩⟩⟩
    have hv0 := h
    obtain ⟨h16, _, hk, h6k, _, _, hnc_w⟩ := hv0.param_fits
    have h12K := hv0.twelve_K_le
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpAppendWriteBaseProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b ns r_b t_new rk_new : ℕ) :
    BpMetaProg mp 17 (bpAppendWriteBaseProg ((mp.toCtx, b), ((ns, r_b), (t_new, rk_new)))) := by
  obtain ⟨hws, hwbm, _, _, _, hwto⟩ := hv.write_frames
  unfold bpAppendWriteBaseProg; simp only [pure_bind]
  exact (BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.bind_prog (bpGetCapsProg_frame mp) fun caps =>
    BpMetaProg.bind_prog (hws 1 (if ns < caps.2 then ns + 1 else 0)) fun _ =>
    BpMetaProg.bind_prog (hwbm b 1 (if r_b < 6 * mk.2 then r_b + 1 else 0)) fun _ =>
    BpMetaProg.bind_prog (bpWriteTailRingProg_frame hv b rk_new t_new) fun _ =>
    BpMetaProg.bind_prog (hwto t_new 0 b) fun _ =>
    hwto t_new 1 rk_new).mono (by decide)

/-- Boundary-crossing tail-block advancement when `rem + 1 = K` (`5` binds, `¬ReadsWidth`). -/
private def bpAdvanceTopBlkProg : BpMetaCtx × ℕ → Memory.Prog Unit
  | (ctx, bf) => do
    let caps ← bpGetCapsProg ctx
    let bf1 ← pure (if bf < caps.1.2 then bf + 1 else 0)
    bpUnresPushProg (ctx, bf)
    bpAllocTbForProg (ctx, bf1)
    bpWriteSlabOwnerProg ((ctx, (bf1, 0)), 0)

@[simp] private theorem runClient_frontier_bpAdvanceTopBlkProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpAdvanceTopBlkProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, bf⟩; unfold bpAdvanceTopBlkProg; simp

private theorem realizesBounded_bpAdvanceTopBlk :
    RealizesBounded .exact bpAdvanceTopBlkProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgc := realizesBounded_bpGetCaps
  have hup := realizesBounded_bpUnresPush
  have hat := realizesBounded_bpAllocTbFor
  have hwso := realizesBounded_bpWriteSlabOwner
  realize
  all_goals (
    rcases d with ⟨ctx, bf⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, hmbk, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpAdvanceTopBlkProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (bf : ℕ) :
    BpMetaProg mp 30 (bpAdvanceTopBlkProg (mp.toCtx, bf)) := by
  obtain ⟨_, _, _, _, hwso, _⟩ := hv.write_frames
  unfold bpAdvanceTopBlkProg; simp only [pure_bind]
  exact (BpMetaProg.bind_prog (bpGetCapsProg_frame mp) fun caps =>
    BpMetaProg.bind_prog (bpUnresPushProg_frame hv bf) fun _ =>
    BpMetaProg.bind_prog (bpAllocTbForProg_frame hv (if bf < caps.1.2 then bf + 1 else 0)) fun _ =>
    hwso (if bf < caps.1.2 then bf + 1 else 0) 0 0).mono (by decide)

private abbrev bpTopBase (t : (ℕ × (ℕ × ℕ)) × ℕ) : ℕ := t.1.1
private abbrev bpTopBlk (t : (ℕ × (ℕ × ℕ)) × ℕ) : ℕ := t.1.2.1
private abbrev bpTopOff (t : (ℕ × (ℕ × ℕ)) × ℕ) : ℕ := t.1.2.2

/-- Realization of `BlockPoolState.rawPostAppend` (`6` binds, `¬ReadsWidth`). -/
def bpRawPostAppendMetaProg : BpMetaCtx × ℕ → Memory.Prog Unit
  | (ctx, b) => do
    let mk ← bpGetMKProg ctx
    let top ← bpAppendReadTopProg ctx
    let r_b ← bpReadBktMetaProg (ctx, (b, 1))
    let hd ← bpReadBktMetaProg (ctx, (b, 2))
    let rk_new ← bpRingAddProg (ctx, (hd, r_b))
    bpAppendWriteBaseProg ((ctx, b), ((bpTopBase top, r_b), (top.2, rk_new)))
    if bpTopOff top < mk.2 - 1 then
      pure ()
    else
      bpAdvanceTopBlkProg (ctx, bpTopBlk top)

@[simp] theorem runClient_frontier_bpRawPostAppendMetaProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (bpRawPostAppendMetaProg x))).frontier =
      s.frontier := by
  rcases x with ⟨ctx, b⟩; unfold bpRawPostAppendMetaProg
  simp only [prog_runClient_state_bind, runClient_state_bpGetMKProg,
    runClient_state_bpAppendReadTopProg, runClient_state_bpReadBktMetaProg]
  split_ifs <;> simp

theorem realizesBounded_bpRawPostAppendMeta :
    RealizesBounded .exact bpRawPostAppendMetaProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgm := realizesBounded_bpGetMK
  have hart := realizesBounded_bpAppendReadTop
  have hrbm := realizesBounded_bpReadBktMeta
  have hra := realizesBounded_bpRingAdd
  have hawb := realizesBounded_bpAppendWriteBase
  have hatb := realizesBounded_bpAdvanceTopBlk
  realize
  all_goals (
    rcases d with ⟨ctx, b⟩
    have hv0 := h
    obtain ⟨h16, _, hk, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

theorem bpRawPostAppendMetaProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b : ℕ) :
    BpMetaProg mp 54 (bpRawPostAppendMetaProg (mp.toCtx, b)) := by
  unfold bpRawPostAppendMetaProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.bind_prog (bpAppendReadTopProg_frame mp) fun top =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 1) fun r_b =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 2) fun hd =>
    BpMetaProg.bind_prog (bpRingAddProg_frame mp hd r_b) fun rk_new =>
    BpMetaProg.bind_prog
      (bpAppendWriteBaseProg_frame hv b top.1.1 r_b top.2 rk_new) fun _ =>
    BpMetaProg.ite_prog (top.1.2.2 < mk.2 - 1)
      (fun _ => (BpMetaProg.pure_prog ()).mono (C₂ := 30) (by decide))
      (fun _ => bpAdvanceTopBlkProg_frame hv top.1.2.1)
  exact hf.mono (by decide)

theorem bpRawPostAppendMetaProg_spec {mp : BpMetaLayout} {w fr b : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr) (hv : (extractBlockPool mp s.mem).CoreValid)
    (hb : b < mp.M) (hn_lt : (extractBlockPool mp s.mem).nSide < mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpRawPostAppendMetaProg (mp.toCtx, b))).mem =
      (extractBlockPool mp s.mem).rawPostAppend b := by
  have hM_eq : (extractBlockPool mp s.mem).M = mp.M := rfl
  have hK_eq : (extractBlockPool mp s.mem).K = mp.K := rfl
  have h16M := hv_mp.sixteen_M_le
  have h12K := hv_mp.twelve_K_le
  have hK64 := hv_mp.K_ge
  have h8MK := hv_mp.eight_MK_le
  have hBf1_mb : (extractBlockPool mp s.mem).B_full + 1 < mp.maxBlocks := by
    have h1 : (extractBlockPool mp s.mem).B_full ≤ mp.nCap / mp.K :=
      Nat.div_le_div_right hn_lt.le
    have := hv_mp.div_K_add_two_le; omega
  obtain ⟨_, hr_lt, hhd_lt, _, _⟩ := hv.bkt_bounds b hb
  rw [hK_eq] at hr_lt hhd_lt
  have hrem_lt : (extractBlockPool mp s.mem).rem < mp.K := Nat.mod_lt _ (by omega)
  obtain ⟨htb_top_hw, _⟩ := hv.tb_fwd (extractBlockPool mp s.mem).B_full le_rfl
    (Or.inl hv.blkTag_top)
  have htb_top_8M : (extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full <
      8 * mp.M := htb_top_hw.trans_le hv.tbHighWater_le_max
  have ht_new_8MK : (extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full *
      mp.K + (extractBlockPool mp s.mem).rem < 8 * mp.M * mp.K := by
    have hle1 : ((extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full + 1) *
        mp.K ≤ (8 * mp.M) * mp.K := Nat.mul_le_mul_right mp.K htb_top_8M
    rw [Nat.add_one_mul] at hle1; omega
  have htop_res : (Memory.spec 0).clientResult s (bpAppendReadTopProg mp.toCtx) =
      (((extractBlockPool mp s.mem).nSide,
        ((extractBlockPool mp s.mem).B_full, (extractBlockPool mp s.mem).rem)),
       (extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full * mp.K +
         (extractBlockPool mp s.mem).rem) := by
    unfold bpAppendReadTopProg
    rw [StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inl rfl),
      StateTransitionSpec.clientResult_bind, clientState_bpDivModKProg, clientResult_bpDivModK,
      StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
      clientResult_bpReadSlabOwner_m2,
      StateTransitionSpec.clientResult_bind, clientState_bpTbSlotProg]
    have hns : s.mem (mp.metaBase + 1) = (extractBlockPool mp s.mem).nSide := rfl
    have hbf : s.mem (mp.metaBase + 1) / mp.K = (extractBlockPool mp s.mem).B_full := rfl
    have hrm : s.mem (mp.metaBase + 1) % mp.K = (extractBlockPool mp s.mem).rem := rfl
    rw [hbf, hrm, hns, clientResult_bpTbSlot htb_top_8M hrem_lt]
    rfl
  rw [BlockPoolState.rawPostAppend_apply]
  unfold bpRawPostAppendMetaProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg, clientResult_bpGetMK,
    StateTransitionSpec.clientState_bind, clientState_bpAppendReadTopProg, htop_res,
    StateTransitionSpec.clientState_bind, clientState_bpReadBktMetaProg,
    clientResult_bpReadBktMeta_r,
    StateTransitionSpec.clientState_bind, clientState_bpReadBktMetaProg,
    clientResult_bpReadBktMeta_head,
    StateTransitionSpec.clientState_bind, clientState_bpRingAddProg,
    clientResult_bpRingAdd hhd_lt hr_lt,
    StateTransitionSpec.clientState_bind]
  dsimp only
  set s_wb := (Memory.spec 0).clientState s
    (bpAppendWriteBaseProg ((mp.toCtx, b),
      (((extractBlockPool mp s.mem).nSide, (extractBlockPool mp s.mem).r b),
       ((extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full * mp.K +
          (extractBlockPool mp s.mem).rem,
        ((extractBlockPool mp s.mem).head b + (extractBlockPool mp s.mem).r b) % (6 * mp.K)))))
  have hex_wb : extractBlockPool mp s_wb.mem =
      { extractBlockPool mp s.mem with
        nSide := (extractBlockPool mp s.mem).nSide + 1
        r := BlockPoolState.set1 (extractBlockPool mp s.mem).r b
          ((extractBlockPool mp s.mem).r b + 1)
        tailRing := BlockPoolState.set2 (extractBlockPool mp s.mem).tailRing b
          (((extractBlockPool mp s.mem).head b + (extractBlockPool mp s.mem).r b) % (6 * mp.K))
          ((extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full * mp.K +
            (extractBlockPool mp s.mem).rem)
        tailOwnerBkt := BlockPoolState.set1 (extractBlockPool mp s.mem).tailOwnerBkt
          ((extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full * mp.K +
            (extractBlockPool mp s.mem).rem) b
        tailOwnerRing := BlockPoolState.set1 (extractBlockPool mp s.mem).tailOwnerRing
          ((extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full * mp.K +
            (extractBlockPool mp s.mem).rem)
          (((extractBlockPool mp s.mem).head b + (extractBlockPool mp s.mem).r b) % (6 * mp.K)) } :=
    by
    dsimp only [s_wb]
    unfold bpAppendWriteBaseProg; dsimp only; simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_bpGetMKProg, clientResult_bpGetMK,
      StateTransitionSpec.clientState_bind, clientState_bpGetCapsProg, clientResult_bpGetCaps]
    dsimp only
    rw [ite_eq_left hn_lt, ite_eq_left hr_lt]
    repeat rw [StateTransitionSpec.clientState_bind]
    rw [writeTailOwner_1 hv_mp ht_new_8MK (le_trans (Nat.mod_lt _ (by omega)).le (by omega)),
      writeTailOwner_0 hv_mp ht_new_8MK (by omega),
      bpWriteTailRingProg_spec hv_mp hb (Nat.mod_lt _ (by omega)) (by omega),
      writeBktMeta_1 hv_mp hb (by omega),
      writeScalar_1 hv_mp (by omega)]
  by_cases hmid : (extractBlockPool mp s.mem).rem < mp.K - 1
  · have hmid' : (extractBlockPool mp s.mem).rem + 1 < (extractBlockPool mp s.mem).K := by
      change (extractBlockPool mp s.mem).rem + 1 < mp.K; omega
    simp only [hmid, hmid', ↓reduceIte]; exact hex_wb
  · have hmid' : ¬((extractBlockPool mp s.mem).rem + 1 < (extractBlockPool mp s.mem).K) := by
      change ¬((extractBlockPool mp s.mem).rem + 1 < mp.K); omega
    simp only [hmid, hmid', ↓reduceIte]
    unfold bpAdvanceTopBlkProg; dsimp only; simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_bpGetCapsProg, clientResult_bpGetCaps]
    dsimp only
    have hbf_lt : (extractBlockPool mp s.mem).B_full < mp.maxBlocks := by omega
    rw [ite_eq_left hbf_lt, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind]
    have hul_wb : (extractBlockPool mp s_wb.mem).unresLen < mp.maxBlocks := by
      rw [hex_wb]; dsimp only; have := hv.unresLen_le_B_full; omega
    set s_up := (Memory.spec 0).clientState s_wb
      (bpUnresPushProg (mp.toCtx, (extractBlockPool mp s.mem).B_full))
    have hex_up := bpUnresPushProg_spec hv_mp hbf_lt hul_wb
    have hft_up : 0 < (extractBlockPool mp s_up.mem).freeTbTop →
        (extractBlockPool mp s_up.mem).freeTbTop - 1 < 8 * mp.M ∧
        (extractBlockPool mp s_up.mem).freeTbStack
          ((extractBlockPool mp s_up.mem).freeTbTop - 1) < 8 * mp.M := fun hpos => by
      rw [hex_up, hex_wb] at hpos ⊢; dsimp only [BlockPoolState.unresPush] at hpos ⊢
      have h1 := hv.freeTbTop_lt_tbHighWater
      have h2 := hv.tbHighWater_le_max
      have h3 := (hv.freeTb_valid ((extractBlockPool mp s.mem).freeTbTop - 1) (by omega)).1
      exact ⟨by omega, by omega⟩
    have hthw_up : (extractBlockPool mp s_up.mem).freeTbTop = 0 →
        (extractBlockPool mp s_up.mem).tbHighWater < 8 * mp.M := fun hz => by
      rw [hex_up, hex_wb] at hz ⊢; dsimp only [BlockPoolState.unresPush] at hz ⊢
      exact hv.tbHighWater_lt_of_freeTbTop_zero hz
    rw [writeSlabOwner_0 hv_mp hBf1_mb (Nat.zero_le _),
      bpAllocTbForProg_spec hv_mp hBf1_mb hft_up hthw_up, hex_up, hex_wb]
    rfl

/-- Read `popEndCoord b` (`5` binds, `¬ReadsWidth`). -/
private def bpPrepPopEndProg : BpMetaCtx × ℕ → Memory.Prog ℕ
  | (ctx, b) => do
    let r_b ← bpReadBktMetaProg (ctx, (b, 1))
    let hd ← bpReadBktMetaProg (ctx, (b, 2))
    let rm1 ← bpSubProg (r_b, 1)
    let rk_e ← bpRingAddProg (ctx, (hd, rm1))
    let idx_tr ← bpTailRingIdxProg (ctx, (b, rk_e))
    bpReadTailDirRawProg (ctx, idx_tr)

@[simp] private theorem runClient_state_bpPrepPopEndProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpPrepPopEndProg x)).2.1 = s := by
  rcases x with ⟨ctx, b⟩; unfold bpPrepPopEndProg; simp

private theorem clientState_bpPrepPopEndProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpPrepPopEndProg x) = s :=
  runClient_state_bpPrepPopEndProg x s

private theorem realizesBounded_bpPrepPopEnd :
    RealizesBounded .exact bpPrepPopEndProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrbm := realizesBounded_bpReadBktMeta
  have hsub := realizesBounded_bpSub
  have hra := realizesBounded_bpRingAdd
  have htri := realizesBounded_bpTailRingIdx
  have hrtd := realizesBounded_bpReadTailDirRaw
  realize
  all_goals (
    rcases d with ⟨ctx, b⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpPrepPopEndProg_frame (mp : BpMetaLayout) (b : ℕ) :
    BpMetaProg mp 6 (bpPrepPopEndProg (mp.toCtx, b)) := by
  unfold bpPrepPopEndProg
  exact (BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 1) fun r_b =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 2) fun hd =>
    BpMetaProg.bind_prog (bpSubProg_frame mp r_b 1) fun rm1 =>
    BpMetaProg.bind_prog (bpRingAddProg_frame mp hd rm1) fun rk_e =>
    BpMetaProg.bind_prog (bpTailRingIdxProg_frame mp b rk_e) fun idx_tr =>
    bpReadTailDirRawProg_frame mp idx_tr).mono (by decide)

/-- Read `popTopCoord` (`4` binds, `¬ReadsWidth`). -/
private def bpPrepPopTopProg : BpMetaCtx → Memory.Prog ℕ
  | ctx => do
    let mk ← bpGetMKProg ctx
    let ns ← bpReadScalarProg (ctx, 1)
    let bf_r ← bpDivModKProg (ctx, ns)
    if 0 < bf_r.2 then do
      let tb ← bpReadSlabOwnerProg (ctx, (bf_r.1, 2))
      bpTbSlotProg (ctx, (tb, bf_r.2 - 1))
    else do
      let bfm1 ← bpSubProg (bf_r.1, 1)
      let tb ← bpReadSlabOwnerProg (ctx, (bfm1, 2))
      bpTbSlotProg (ctx, (tb, mk.2 - 1))

@[simp] private theorem runClient_state_bpPrepPopTopProg (ctx : BpMetaCtx) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpPrepPopTopProg ctx)).2.1 = s := by
  unfold bpPrepPopTopProg
  simp only [prog_runClient_state_bind, runClient_state_bpGetMKProg,
    runClient_state_bpReadScalarProg, runClient_state_bpDivModKProg]
  split_ifs <;> simp

private theorem clientState_bpPrepPopTopProg (ctx : BpMetaCtx) (s : Memory.State) :
    (Memory.spec 0).clientState s (bpPrepPopTopProg ctx) = s :=
  runClient_state_bpPrepPopTopProg ctx s

private theorem realizesBounded_bpPrepPopTop :
    RealizesBounded .exact bpPrepPopTopProg
      (WordEncoding.encode (α := BpMetaCtx))
      (WordEncoding.encode (α := ℕ))
      (fun w ctx s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hgm := realizesBounded_bpGetMK
  have hsub := realizesBounded_bpSub
  have hrs := realizesBounded_bpReadScalar
  have hdm := realizesBounded_bpDivModK
  have hrso := realizesBounded_bpReadSlabOwner
  have hts := realizesBounded_bpTbSlot
  realize
  all_goals (
    have hv0 := h
    obtain ⟨h16, _, hk, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpPrepPopTopProg_frame (mp : BpMetaLayout) :
    BpMetaProg mp 3 (bpPrepPopTopProg mp.toCtx) := by
  unfold bpPrepPopTopProg
  have hf := BpMetaProg.bind_prog (bpGetMKProg_frame mp) fun mk =>
    BpMetaProg.bind_prog (bpReadScalarProg_frame mp 1) fun ns =>
    BpMetaProg.bind_prog (bpDivModKProg_frame mp ns) fun bf_r =>
    BpMetaProg.ite_prog (0 < bf_r.2)
      (fun _ =>
        BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp bf_r.1 2) fun tb =>
          bpTbSlotProg_frame mp tb (bf_r.2 - 1))
      (fun _ =>
        (BpMetaProg.bind_prog (bpSubProg_frame mp bf_r.1 1) fun bfm1 =>
          BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp bfm1 2) fun tb =>
            bpTbSlotProg_frame mp tb (mk.2 - 1)).mono (C₂ := 2) (by decide))
  exact hf.mono (by decide)

/-- Realization of `BlockPoolState.prepPopBktBack` (`3` binds, `¬ReadsWidth`). -/
def bpPrepPopMetaProg : BpMetaCtx × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | (ctx, b) => do
    let t_end ← bpPrepPopEndProg (ctx, b)
    let t_top ← bpPrepPopTopProg ctx
    bpSwapTailMetaProg (ctx, (t_end, t_top))

@[simp] theorem runClient_frontier_bpPrepPopMetaProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (bpPrepPopMetaProg x))).frontier =
      s.frontier := by
  rcases x with ⟨ctx, b⟩; unfold bpPrepPopMetaProg; simp

theorem realizesBounded_bpPrepPopMeta :
    RealizesBounded .exact bpPrepPopMetaProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hppe := realizesBounded_bpPrepPopEnd
  have hppt := realizesBounded_bpPrepPopTop
  have hstm := realizesBounded_bpSwapTailMeta
  realize
  all_goals (
    rcases d with ⟨ctx, b⟩
    have hv0 := h
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0)

theorem bpPrepPopMetaProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr) (b : ℕ) :
    BpMetaProg mp 53 (bpPrepPopMetaProg (mp.toCtx, b)) := by
  unfold bpPrepPopMetaProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpPrepPopEndProg_frame mp b) fun t_end =>
    BpMetaProg.bind_prog (bpPrepPopTopProg_frame mp) fun t_top =>
    bpSwapTailMetaProg_frame hv t_end t_top
  exact hf.mono (by decide)

theorem bpPrepPopMetaProg_spec {mp : BpMetaLayout} {w fr b : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr) (hbal : (extractBlockPool mp s.mem).Balanced)
    (hb : b < mp.M) (hcnt : 0 < (extractBlockPool mp s.mem).bktCount b)
    (hn_le : (extractBlockPool mp s.mem).nSide ≤ mp.nCap) :
    let bp := extractBlockPool mp s.mem
    let s' := (Memory.spec 0).clientState s (bpPrepPopMetaProg (mp.toCtx, b))
    let res := (Memory.spec 0).clientResult s (bpPrepPopMetaProg (mp.toCtx, b))
    extractBlockPool mp s'.mem = (bp.prepPopBktBack b).1 ∧
    res = encodeOptSwap (bp.prepPopBktBack b).2 := by
  dsimp only
  have hM_eq : (extractBlockPool mp s.mem).M = mp.M := rfl
  have hK_eq : (extractBlockPool mp s.mem).K = mp.K := rfl
  have hv := hbal.core
  have hK64 := hv_mp.K_ge
  obtain ⟨_, hr_lt, hhd_lt, hc_le, _⟩ := hv.bkt_bounds b hb
  obtain ⟨hr_pos, hcur_le_rm1⟩ := (hbal.hyst b hb).pos_r_and_actCur_lt hK64 hc_le hcnt
  rw [hK_eq] at hr_lt hhd_lt hc_le
  have hn_pos := (hbal.prepPopBktBack_spec.{0} hb hcnt).2.2.2.2.2.1
  have hend_res : (Memory.spec 0).clientResult s (bpPrepPopEndProg (mp.toCtx, b)) =
      (extractBlockPool mp s.mem).tailRing b
        (((extractBlockPool mp s.mem).head b + ((extractBlockPool mp s.mem).r b - 1)) %
          (6 * mp.K)) := by
    unfold bpPrepPopEndProg; dsimp only
    rw [StateTransitionSpec.clientResult_bind, clientState_bpReadBktMetaProg,
      clientResult_bpReadBktMeta_r,
      StateTransitionSpec.clientResult_bind, clientState_bpReadBktMetaProg,
      clientResult_bpReadBktMeta_head,
      StateTransitionSpec.clientResult_bind, clientState_bpSubProg, clientResult_bpSubProg,
      StateTransitionSpec.clientResult_bind, clientState_bpRingAddProg,
      clientResult_bpRingAdd hhd_lt (by omega),
      StateTransitionSpec.clientResult_bind, clientState_bpTailRingIdxProg,
      clientResult_bpTailRingIdx hb (Nat.mod_lt _ (by omega)),
      clientResult_bpReadTailDir_ring hb (Nat.mod_lt _ (by omega))]
  have hlive_end : (extractBlockPool mp s.mem).LiveTail
      ((extractBlockPool mp s.mem).tailRing b
        (((extractBlockPool mp s.mem).head b + ((extractBlockPool mp s.mem).r b - 1)) %
          (6 * mp.K))) :=
    ⟨b, hb, (extractBlockPool mp s.mem).r b - 1, hcur_le_rm1, by omega, rfl⟩
  have htop_res_and_live :
      (Memory.spec 0).clientResult s (bpPrepPopTopProg mp.toCtx) =
        (if 0 < (extractBlockPool mp s.mem).rem then
           (extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full * mp.K +
             ((extractBlockPool mp s.mem).rem - 1)
         else
           (extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).B_full - 1) * mp.K +
             (mp.K - 1)) ∧
      (extractBlockPool mp s.mem).LiveTail
        (if 0 < (extractBlockPool mp s.mem).rem then
           (extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full * mp.K +
             ((extractBlockPool mp s.mem).rem - 1)
         else
           (extractBlockPool mp s.mem).blkMeta2 ((extractBlockPool mp s.mem).B_full - 1) * mp.K +
             (mp.K - 1)) := by
    unfold bpPrepPopTopProg
    rw [StateTransitionSpec.clientResult_bind, clientState_bpGetMKProg, clientResult_bpGetMK,
      StateTransitionSpec.clientResult_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inl rfl),
      StateTransitionSpec.clientResult_bind, clientState_bpDivModKProg, clientResult_bpDivModK]
    dsimp only
    have hbf : s.mem (mp.metaBase + 1) / mp.K = (extractBlockPool mp s.mem).B_full := rfl
    have hrm : s.mem (mp.metaBase + 1) % mp.K = (extractBlockPool mp s.mem).rem := rfl
    rw [hbf, hrm]
    by_cases hrem : 0 < (extractBlockPool mp s.mem).rem
    · rw [ite_eq_left hrem, ite_eq_left hrem]
      have hrem_lt : (extractBlockPool mp s.mem).rem < mp.K := Nat.mod_lt _ (by omega)
      have htb_8M : (extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full <
          8 * mp.M :=
        (hv.tb_fwd _ le_rfl (Or.inl hv.blkTag_top)).1.trans_le hv.tbHighWater_le_max
      rw [StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_m2, clientResult_bpTbSlot htb_8M (by omega)]
      obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ := hv.tail_bwd (extractBlockPool mp s.mem).B_full
        le_rfl ((extractBlockPool mp s.mem).rem - 1) (by omega) (Or.inr (by omega))
        (Or.inl hv.blkTag_top)
      obtain ⟨_, _, hhdo, _, _⟩ := hv.bkt_bounds _ hbo
      exact ⟨rfl, _, hbo, _, hk_ge, hk_lt, by rwa [ring_add_diff_mod hhdo hrko]⟩
    · rw [ite_eq_right hrem, ite_eq_right hrem]
      have hrem0 : (extractBlockPool mp s.mem).rem = 0 := by omega
      have hBf_pos : 1 ≤ (extractBlockPool mp s.mem).B_full := by
        have hns := hv.nSide_eq; rw [hrem0, add_zero] at hns
        by_contra h0; have he0 : (extractBlockPool mp s.mem).B_full = 0 := by omega
        rw [he0, zero_mul] at hns; omega
      have hP_lt : (extractBlockPool mp s.mem).B_full - 1 < (extractBlockPool mp s.mem).B_full :=
        by omega
      have hP_tag0 : (extractBlockPool mp s.mem).blkTag
          ((extractBlockPool mp s.mem).B_full - 1) = 0 := by
        by_contra hne0; have := hbal.low_blk _ hne0; omega
      have htb_8M : (extractBlockPool mp s.mem).blkMeta2
          ((extractBlockPool mp s.mem).B_full - 1) < 8 * mp.M :=
        (hv.tb_fwd _ hP_lt.le (Or.inl hP_tag0)).1.trans_le hv.tbHighWater_le_max
      rw [StateTransitionSpec.clientResult_bind, clientState_bpSubProg, clientResult_bpSubProg,
        StateTransitionSpec.clientResult_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_m2, clientResult_bpTbSlot htb_8M (by omega)]
      obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ := hv.tail_bwd
        ((extractBlockPool mp s.mem).B_full - 1) hP_lt.le (mp.K - 1) (by omega) (Or.inl hP_lt)
        (Or.inl hP_tag0)
      obtain ⟨_, _, hhdo, _, _⟩ := hv.bkt_bounds _ hbo
      exact ⟨rfl, _, hbo, _, hk_ge, hk_lt, by rwa [ring_add_diff_mod hhdo hrko]⟩
  rw [BlockPoolState.prepPopBktBack_apply]
  unfold bpPrepPopMetaProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpPrepPopEndProg,
    StateTransitionSpec.clientResult_bind, clientState_bpPrepPopEndProg, hend_res,
    StateTransitionSpec.clientState_bind, clientState_bpPrepPopTopProg,
    StateTransitionSpec.clientResult_bind, clientState_bpPrepPopTopProg, htop_res_and_live.1]
  exact bpSwapTailMetaProg_spec hv_mp hv hn_le hlive_end htop_res_and_live.2

/-- Shrink `(nSide, r b)` by `1` in `commitPopBktBack` (`2` binds, `¬ReadsWidth`). -/
private def bpCommitPopShrinkProg : (BpMetaCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((ctx, b), (ns, r_b)) => do
    let nsm1 ← bpSubProg (ns, 1)
    let rm1 ← bpSubProg (r_b, 1)
    bpWriteScalarProg ((ctx, 1), nsm1)
    bpWriteBktMetaProg ((ctx, (b, 1)), rm1)

@[simp] private theorem runClient_frontier_bpCommitPopShrinkProg
    (x : (BpMetaCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpCommitPopShrinkProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨⟨ctx, b⟩, ⟨ns, r_b⟩⟩; unfold bpCommitPopShrinkProg; simp

private theorem realizesBounded_bpCommitPopShrink :
    RealizesBounded .exact bpCommitPopShrinkProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((ctx, _), _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hsub := realizesBounded_bpSub
  have hws := realizesBounded_bpWriteScalar
  have hwbm := realizesBounded_bpWriteBktMeta
  realize
  all_goals (
    rcases d with ⟨⟨ctx, b⟩, ⟨ns, r_b⟩⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpCommitPopShrinkProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (b ns r_b : ℕ) :
    BpMetaProg mp 5 (bpCommitPopShrinkProg ((mp.toCtx, b), (ns, r_b))) := by
  obtain ⟨hws, hwbm, _, _, _, _⟩ := hv.write_frames
  unfold bpCommitPopShrinkProg; dsimp only
  exact (BpMetaProg.bind_prog (bpSubProg_frame mp ns 1) fun nsm1 =>
    BpMetaProg.bind_prog (bpSubProg_frame mp r_b 1) fun rm1 =>
    BpMetaProg.bind_prog (hws 1 nsm1) fun _ =>
    hwbm b 1 rm1).mono (by decide)

/-- Boundary-crossing `rem = 0` cleanup in `commitPopBktBack` (`4` binds, `¬ReadsWidth`). -/
private def bpCommitPopCase2CleanProg : BpMetaCtx × ℕ → Memory.Prog Unit
  | (ctx, bf) => do
    let tb_e ← bpReadSlabOwnerProg (ctx, (bf, 2))
    let bfm1 ← bpSubProg (bf, 1)
    let idx_p ← bpReadSlabOwnerProg (ctx, (bfm1, 1))
    bpFreeTbProg (ctx, tb_e)
    bpUnresRemoveAtProg (ctx, idx_p)

@[simp] private theorem runClient_frontier_bpCommitPopCase2CleanProg
    (x : BpMetaCtx × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (bpCommitPopCase2CleanProg x)).2.1.frontier = s.frontier := by
  rcases x with ⟨ctx, bf⟩; unfold bpCommitPopCase2CleanProg; simp

private theorem realizesBounded_bpCommitPopCase2Clean :
    RealizesBounded .exact bpCommitPopCase2CleanProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrso := realizesBounded_bpReadSlabOwner
  have hsub := realizesBounded_bpSub
  have hft := realizesBounded_bpFreeTb
  have hur := realizesBounded_bpUnresRemoveAt
  realize
  all_goals (
    rcases d with ⟨ctx, bf⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

private theorem bpCommitPopCase2CleanProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr)
    (bf : ℕ) :
    BpMetaProg mp 22 (bpCommitPopCase2CleanProg (mp.toCtx, bf)) := by
  unfold bpCommitPopCase2CleanProg; dsimp only
  exact (BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp bf 2) fun tb_e =>
    BpMetaProg.bind_prog (bpSubProg_frame mp bf 1) fun bfm1 =>
    BpMetaProg.bind_prog (bpReadSlabOwnerProg_frame mp bfm1 1) fun idx_p =>
    BpMetaProg.bind_prog (bpFreeTbProg_frame hv tb_e) fun _ =>
    bpUnresRemoveAtProg_frame hv idx_p).mono (by decide)

/-- Realization of `BlockPoolState.commitPopBktBack` (`4` binds, `¬ReadsWidth`). -/
def bpCommitPopMetaProg : BpMetaCtx × ℕ → Memory.Prog Unit
  | (ctx, b) => do
    let ns ← bpReadScalarProg (ctx, 1)
    let bf_r ← bpDivModKProg (ctx, ns)
    let r_b ← bpReadBktMetaProg (ctx, (b, 1))
    if 0 < bf_r.2 then
      bpCommitPopShrinkProg ((ctx, b), (ns, r_b))
    else do
      bpCommitPopCase2CleanProg (ctx, bf_r.1)
      bpCommitPopShrinkProg ((ctx, b), (ns, r_b))

@[simp] theorem runClient_frontier_bpCommitPopMetaProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (clientOutState ((Memory.spec 0).runClient s (bpCommitPopMetaProg x))).frontier =
      s.frontier := by
  rcases x with ⟨ctx, b⟩; unfold bpCommitPopMetaProg
  simp only [prog_runClient_state_bind, runClient_state_bpReadScalarProg,
    runClient_state_bpDivModKProg, runClient_state_bpReadBktMetaProg]
  split_ifs <;> simp

theorem realizesBounded_bpCommitPopMeta :
    RealizesBounded .exact bpCommitPopMetaProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (ctx, _) s => (BpMetaLayout.ofCtx ctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hdm := realizesBounded_bpDivModK
  have hrbm := realizesBounded_bpReadBktMeta
  have hcps := realizesBounded_bpCommitPopShrink
  have hcpc := realizesBounded_bpCommitPopCase2Clean
  realize
  all_goals (
    rcases d with ⟨ctx, b⟩
    have hv0 := h
    obtain ⟨h16, _, _, _, _, _, _⟩ := hv0.param_fits
    have hw6 := hv0.six_le_w
    have hK64_v := hv0.K_ge
    dsimp only [Fits, StateTransitionSpec.clientResult,
      StateTransitionSpec.clientState] at *
    first | simpa using hv0 | (simp at *; omega))

theorem bpCommitPopMetaProg_frame {mp : BpMetaLayout} {w fr : ℕ} (hv : mp.Valid w fr) (b : ℕ) :
    BpMetaProg mp 30 (bpCommitPopMetaProg (mp.toCtx, b)) := by
  unfold bpCommitPopMetaProg; dsimp only
  have hf := BpMetaProg.bind_prog (bpReadScalarProg_frame mp 1) fun ns =>
    BpMetaProg.bind_prog (bpDivModKProg_frame mp ns) fun bf_r =>
    BpMetaProg.bind_prog (bpReadBktMetaProg_frame mp b 1) fun r_b =>
    BpMetaProg.ite_prog (0 < bf_r.2)
      (fun _ => (bpCommitPopShrinkProg_frame hv b ns r_b).mono (C₂ := 27) (by decide))
      (fun _ =>
        BpMetaProg.bind_prog (bpCommitPopCase2CleanProg_frame hv bf_r.1) fun _ =>
          bpCommitPopShrinkProg_frame hv b ns r_b)
  exact hf.mono (by decide)

theorem bpCommitPopMetaProg_spec {mp : BpMetaLayout} {w fr b : ℕ} {s : Memory.State}
    (hv_mp : mp.Valid w fr) (hbal : (extractBlockPool mp s.mem).Balanced)
    (hb : b < mp.M) (hn_pos : 0 < (extractBlockPool mp s.mem).nSide)
    (hn_le : (extractBlockPool mp s.mem).nSide ≤ mp.nCap) :
    extractBlockPool mp
      ((Memory.spec 0).clientState s (bpCommitPopMetaProg (mp.toCtx, b))).mem =
      (extractBlockPool mp s.mem).commitPopBktBack b := by
  have hM_eq : (extractBlockPool mp s.mem).M = mp.M := rfl
  have hK_eq : (extractBlockPool mp s.mem).K = mp.K := rfl
  have hv := hbal.core
  have h12K := hv_mp.twelve_K_le
  have hK64 := hv_mp.K_ge
  have hBf_mb : (extractBlockPool mp s.mem).B_full < mp.maxBlocks := by
    have h1 : (extractBlockPool mp s.mem).B_full ≤ mp.nCap / mp.K := Nat.div_le_div_right hn_le
    have := hv_mp.div_K_add_two_le; omega
  obtain ⟨_, hr_lt, _, _, _⟩ := hv.bkt_bounds b hb
  rw [hK_eq] at hr_lt
  rw [BlockPoolState.commitPopBktBack_apply]
  unfold bpCommitPopMetaProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    clientResult_bpReadScalar s (Or.inl rfl),
    StateTransitionSpec.clientState_bind, clientState_bpDivModKProg, clientResult_bpDivModK,
    StateTransitionSpec.clientState_bind, clientState_bpReadBktMetaProg,
    clientResult_bpReadBktMeta_r]
  dsimp only
  have hns : s.mem (mp.metaBase + 1) = (extractBlockPool mp s.mem).nSide := rfl
  have hbf : s.mem (mp.metaBase + 1) / mp.K = (extractBlockPool mp s.mem).B_full := rfl
  have hrm : s.mem (mp.metaBase + 1) % mp.K = (extractBlockPool mp s.mem).rem := rfl
  rw [hbf, hrm, hns]
  by_cases hrem : 0 < (extractBlockPool mp s.mem).rem
  · rw [ite_eq_left hrem, ite_eq_left hrem]
    unfold bpCommitPopShrinkProg; dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_bpSubProg, clientResult_bpSubProg,
      StateTransitionSpec.clientState_bind, clientState_bpSubProg, clientResult_bpSubProg,
      StateTransitionSpec.clientState_bind,
      writeBktMeta_1 hv_mp hb (by omega),
      writeScalar_1 hv_mp (by omega)]
  · rw [ite_eq_right hrem, ite_eq_right hrem, StateTransitionSpec.clientState_bind]
    have hrem0 : (extractBlockPool mp s.mem).rem = 0 := by omega
    have hBf_pos : 1 ≤ (extractBlockPool mp s.mem).B_full := by
      have h1 := hv.nSide_eq; rw [hrem0, add_zero] at h1
      by_contra h0; have he0 : (extractBlockPool mp s.mem).B_full = 0 := by omega
      rw [he0, zero_mul] at h1; omega
    have hP_lt : (extractBlockPool mp s.mem).B_full - 1 < (extractBlockPool mp s.mem).B_full := by
      omega
    have hP_tag0 : (extractBlockPool mp s.mem).blkTag
        ((extractBlockPool mp s.mem).B_full - 1) = 0 := by
      by_contra hne0; have := hbal.low_blk _ hne0; omega
    obtain ⟨hidx_ul, _⟩ := hv.unres_bwd _ hP_lt hP_tag0
    have hul_le := hv.unresLen_le_B_full
    have hPl_lt := (hv.unres_fwd ((extractBlockPool mp s.mem).unresLen - 1) (by omega)).1
    have htb_8M : (extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full <
        8 * mp.M :=
      (hv.tb_fwd _ le_rfl (Or.inl hv.blkTag_top)).1.trans_le hv.tbHighWater_le_max
    have hftt_8M : (extractBlockPool mp s.mem).freeTbTop < 8 * mp.M :=
      hv.freeTbTop_lt_tbHighWater.trans_le hv.tbHighWater_le_max
    set s_cl := (Memory.spec 0).clientState s
      (bpCommitPopCase2CleanProg (mp.toCtx, (extractBlockPool mp s.mem).B_full))
    have hex_cl : extractBlockPool mp s_cl.mem =
        ((extractBlockPool mp s.mem).freeTb
          ((extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full)).unresRemoveAt
          ((extractBlockPool mp s.mem).blkMeta1 ((extractBlockPool mp s.mem).B_full - 1)) := by
      dsimp only [s_cl]; unfold bpCommitPopCase2CleanProg; dsimp only
      rw [StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_m2,
        StateTransitionSpec.clientState_bind, clientState_bpSubProg, clientResult_bpSubProg,
        StateTransitionSpec.clientState_bind, clientState_bpReadSlabOwnerProg,
        clientResult_bpReadSlabOwner_m1,
        StateTransitionSpec.clientState_bind]
      set s_ft := (Memory.spec 0).clientState s
        (bpFreeTbProg (mp.toCtx,
          (extractBlockPool mp s.mem).blkMeta2 (extractBlockPool mp s.mem).B_full))
      have hex_ft := bpFreeTbProg_spec hv_mp htb_8M hftt_8M
      have hul_ft : (extractBlockPool mp s_ft.mem).unresLen - 1 < mp.maxBlocks := by
        rw [hex_ft]; dsimp only [BlockPoolState.freeTb]; omega
      have hPl_ft : (extractBlockPool mp s_ft.mem).unresStack
          ((extractBlockPool mp s_ft.mem).unresLen - 1) < mp.maxBlocks := by
        rw [hex_ft]; dsimp only [BlockPoolState.freeTb]; omega
      rw [bpUnresRemoveAtProg_spec hv_mp (by omega) hul_ft hPl_ft, hex_ft]
    unfold bpCommitPopShrinkProg; dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_bpSubProg, clientResult_bpSubProg,
      StateTransitionSpec.clientState_bind, clientState_bpSubProg, clientResult_bpSubProg,
      StateTransitionSpec.clientState_bind,
      writeBktMeta_1 hv_mp hb (by omega),
      writeScalar_1 hv_mp (by omega), hex_cl]

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
