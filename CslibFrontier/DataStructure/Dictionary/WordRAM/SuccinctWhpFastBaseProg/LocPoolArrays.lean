/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Frame
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Internal
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpPermHealProg
import CslibFrontier.Tactic.Realize

/-!
# Fast-Mode `locState` and Backyard-Pool Packed-Array Subroutines

This module implements the parameter-free `Memory.Prog` subroutines and `Realizes .exact`
certificates for the 2-bit `locState` array and backyard free-pool arrays on `FastMemRep`:

1. `readFastLocGenProg`, `writeFastLocGenProg`: overflow-free 2-bit coordinate state accessors.
2. `readPoolFreeStackGenProg`, `writePoolFreeStackGenProg`, `writePoolOwnerGenProg`: backyard
   pool free-stack and reverse-owner accessors.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.readFastLocGenProg`, `writeFastLocGenProg`,
  `readPoolFreeStackGenProg`, `writePoolFreeStackGenProg`, `writePoolOwnerGenProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.writeFastLocGenProg_fastStep`,
  `writePoolFreeStackGenProg_fastStep`, `writePoolOwnerGenProg_fastStep`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ## Section 1: `locState` Accessors -/

private theorem fastLoc_pre_safe {w base b loc : ℕ} {cp : WhpCoreParams} {s : Memory.State}
    (h : WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ loc < wpTotalLoc cp) :
    ReadLocStatePre w (((base, wpOffLocState cp), (wpTotalLoc cp, wpW cp)), (b, loc)) s := by
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hloc⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hlog_w := henv.log_lt_w
  have hlog_ge := log_ge_mul_ell hth
  have hell := one_le_logLogFactor n_max
  have h2tl := (large_index_bounds hth).2.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.1
  dsimp only [ReadLocStatePre]
  simp only [wp_large_M hth, wp_large_totalLoc hth, wp_large_offLocState hth, wp_large_w hth]
    at hb hloc ⊢
  exact ⟨numBucketsWhp n_max, trivial, by omega, henv.fits_of_le_n_max (by omega),
    hb, hloc, henv.fits_largeSpace.of_le (by omega)⟩

/-- Read `fs.locState b loc` (`d = (((cp, base), b), loc)`). -/
@[irreducible] def readFastLocGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, base), b), loc) =>
    readLocStateGenProg (((base, wpOffLocState cp), (wpTotalLoc cp, wpW cp)), (b, loc))

theorem realizes_readFastLocGen :
    Realizes .exact readFastLocGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((cp, base), b), loc) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ loc < wpTotalLoc cp)
      (fun _ _ => 0) := by
  unfold readFastLocGenProg
  realize [realizes_readLocStateGen]
  rcases d with ⟨⟨⟨cp, base⟩, b⟩, loc⟩
  exact fastLoc_pre_safe h

theorem readFastLocGenProg_spec {c U V w n_max base b loc : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readFastLocGenProg (((mkWhpCoreParams c U V w n_max, base), b), loc)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.locState b loc ∧
    memoryCost prog s = 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  obtain ⟨hst, hres, hmc, hvp⟩ := readLocStateGenProg_spec henv hb hloc (s := s)
  unfold readFastLocGenProg
  simp only [wp_large_offLocState hth, wp_large_totalLoc hth, wp_large_w hth]
  exact ⟨hst, hres.trans (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb loc hloc), hmc, hvp⟩

/-- Write `fs.locState b loc := tag` (`tag < 4`, `d = ((((cp, base), b), loc), tag)`). -/
@[irreducible] def writeFastLocGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), loc), tag) =>
    writeLocStateGenProg ((((base, wpOffLocState cp), (wpTotalLoc cp, wpW cp)), (b, loc)), tag)

theorem realizes_writeFastLocGen :
    Realizes .exact writeFastLocGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), loc), _) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ loc < wpTotalLoc cp)
      (fun _ _ => 0) := by
  unfold writeFastLocGenProg
  realize [realizes_writeLocStateGen]
  rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, loc⟩, tag⟩
  exact fastLoc_pre_safe h

theorem writeFastLocGenProg_fastStep {c U V w n_max base b loc tag : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max) (htag : tag < 4)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writeFastLocGenProg ((((mkWhpCoreParams c U V w n_max, base), b), loc), tag)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        locState := Function.update fs.locState b (Function.update (fs.locState b) loc tag) }
      s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  obtain ⟨hst, hmc, hvp⟩ := writeLocStateGenProg_spec henv hb hloc (val := tag) (s := s)
  unfold writeFastLocGenProg
  simp only [wp_large_offLocState hth, wp_large_totalLoc hth, wp_large_w hth]
  rw [hst]
  set idxW := b * totalLocalCoordsWhp n_max + loc
  have hidxW : idxW < numBucketsWhp n_max * totalLocalCoordsWhp n_max :=
    mul_add_lt_mul_bound hb hloc
  obtain ⟨hqv0, hloc0, -, hbptr0, hpool0, -⟩ := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨hmc, hvp, fastStep_pureArray hw hidxW (by omega) (by omega) (Or.inl (by omega))
    hseed hrep ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun i hi => ⟨(readPacked_writePacked_disjoint hw hi hidxW (Or.inl (by omega))).trans
        (hqv0 i hi).1,
      (readPacked_writePacked_disjoint hw hi hidxW (Or.inl (by omega))).trans (hqv0 i hi).2⟩)
    (fun b' hb' loc' hl' => ?_)
    (fun b' hb' k hk =>
      (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb' hk) hidxW
        (Or.inr (by omega))).trans (hbptr0 b' hb' k hk))
    (fun j hj => ⟨(readPacked_writePacked_disjoint hw hj hidxW (Or.inr (by omega))).trans
        (hpool0 j hj).1,
      (readPacked_writePacked_disjoint hw hj hidxW (Or.inr (by omega))).trans
        (hpool0 j hj).2⟩)⟩
  dsimp only
  rcases eq_or_ne b' b with rfl | hbb
  · rcases eq_or_ne loc' loc with rfl | hll
    · simpa only [Function.update_self] using readPacked_writePacked_self _ _ _ s.mem idxW htag
    · simpa only [Function.update_self, Function.update_of_ne hll] using
        (readPacked_writePacked_of_ne hw s.mem (by omega) tag).trans (hloc0 b' hb' loc' hl')
  · simpa only [Function.update_of_ne hbb] using (readPacked_writePacked_of_ne hw s.mem
      (fun heq => hbb (mul_add_inj_right hl' hloc heq).1) tag).trans (hloc0 b' hb' loc' hl')

/-! ## Section 2: `poolFreeStack` and `poolOwner` Accessors -/

private theorem poolFreeStack_pre_safe {w base j : ℕ} {cp : WhpCoreParams}
    (h : WhpLargeEnvGen w cp base ∧ j < wpPoolSize cp) :
    ∃ N', w = wpW cp ∧ 0 < w ∧ wpGlobalPtrBits cp ≤ w ∧ j < N' ∧
      Fits w (base + wpOffPoolFreeStack cp + packedWords N' (wpGlobalPtrBits cp) w) := by
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hj⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  simp only [wp_large_poolSize hth, wp_large_offPoolFreeStack hth, wp_large_globalPtrBits hth,
    wp_large_w hth] at hj ⊢
  exact henv.packed_safe_true hgk hj (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.1

/-- Read `fs.poolFreeStack j` (`j < poolSizeWhp n_max`, `d = ((cp, base), j)`). -/
@[irreducible] def readPoolFreeStackGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), j) =>
    readPackedGenProg (((base, wpOffPoolFreeStack cp), (wpGlobalPtrBits cp, wpW cp)), j)

theorem realizes_readPoolFreeStackGen :
    Realizes .exact readPoolFreeStackGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), j) _ => WhpLargeEnvGen w cp base ∧ j < wpPoolSize cp)
      (fun _ _ => 0) := by
  unfold readPoolFreeStackGenProg
  realize [realizes_readPackedGen]
  rcases d with ⟨⟨cp, base⟩, j⟩
  exact poolFreeStack_pre_safe h

theorem readPoolFreeStackGenProg_spec {c U V w n_max base j : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hj : j < poolSizeWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readPoolFreeStackGenProg ((mkWhpCoreParams c U V w n_max, base), j)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.poolFreeStack j ∧
    memoryCost prog s = 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  unfold readPoolFreeStackGenProg
  simp only [wp_large_offPoolFreeStack hth, wp_large_globalPtrBits hth, wp_large_w hth]
  exact ⟨rfl, (clientResult_readPackedGen _ _ _ _ _ _).trans
    (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj).1, rfl, validProg_readPacked henv.2.1 hj
      (seg_add_le (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.1)⟩

/-- Write `fs.poolFreeStack j := pSlot`
(`j < poolSizeWhp n_max`, `d = (((cp, base), j), pSlot)`). -/
@[irreducible] def writePoolFreeStackGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), j), pSlot) =>
    writePackedGenProg ((((base, wpOffPoolFreeStack cp), (wpGlobalPtrBits cp, wpW cp)), j), pSlot)

theorem realizes_writePoolFreeStackGen :
    Realizes .exact writePoolFreeStackGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), j), _) _ => WhpLargeEnvGen w cp base ∧ j < wpPoolSize cp)
      (fun _ _ => 0) := by
  unfold writePoolFreeStackGenProg
  realize [realizes_writePackedGen]
  rcases d with ⟨⟨⟨cp, base⟩, j⟩, pSlot⟩
  exact poolFreeStack_pre_safe h

theorem writePoolFreeStackGenProg_fastStep {c U V w n_max base j pSlot : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hj : j < poolSizeWhp n_max) (hp_le : pSlot ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writePoolFreeStackGenProg (((mkWhpCoreParams c U V w n_max, base), j), pSlot)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with poolFreeStack := Function.update fs.poolFreeStack j pSlot } s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have hp_g : pSlot < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max hp_le
  unfold writePoolFreeStackGenProg
  simp only [wp_large_offPoolFreeStack hth, wp_large_globalPtrBits hth, wp_large_w hth]
  rw [clientState_writePackedGen]
  obtain ⟨hqv0, hloc0, -, hbptr0, hpool0, -⟩ := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨rfl, validProg_writePacked hw (globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1) hj
      (seg_add_le (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.1),
    fastStep_pureArray hw hj (by omega) (by omega) (Or.inr (by omega)) hseed hrep
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun i hi => ⟨(readPacked_writePacked_disjoint hw hi hj (Or.inl (by omega))).trans
          (hqv0 i hi).1,
        (readPacked_writePacked_disjoint hw hi hj (Or.inl (by omega))).trans (hqv0 i hi).2⟩)
      (fun b hb loc hl =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hl) hj
          (Or.inl (by omega))).trans (hloc0 b hb loc hl))
      (fun b hb k hk =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hk) hj
          (Or.inl (by omega))).trans (hbptr0 b hb k hk))
      (fun j' hj' => ⟨?_,
        (readPacked_writePacked_disjoint hw hj' hj (Or.inr (by omega))).trans (hpool0 j' hj').2⟩)⟩
  simp only [Function.update_apply]; split_ifs with hjj
  · subst hjj; exact readPacked_writePacked_self _ _ _ s.mem j' hp_g
  · exact (readPacked_writePacked_of_ne hw s.mem hjj pSlot).trans (hpool0 j' hj').1

/-- Write `fs.poolOwner j := enc` (`j < poolSizeWhp n_max`, `d = (((cp, base), j), enc)`). -/
@[irreducible] def writePoolOwnerGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), j), enc) =>
    writePackedGenProg ((((base, wpOffPoolOwner cp), (wpGlobalPtrBits cp, wpW cp)), j), enc)

theorem realizes_writePoolOwnerGen :
    Realizes .exact writePoolOwnerGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), j), _) _ => WhpLargeEnvGen w cp base ∧ j < wpPoolSize cp)
      (fun _ _ => 0) := by
  unfold writePoolOwnerGenProg
  realize [realizes_writePackedGen]
  rcases d with ⟨⟨⟨cp, base⟩, j⟩, enc⟩
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hj⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  simp only [wp_large_poolSize hth, wp_large_offPoolOwner hth, wp_large_globalPtrBits hth,
    wp_large_w hth] at hj ⊢
  exact henv.packed_safe_true hgk hj (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.2.1

theorem writePoolOwnerGenProg_fastStep {c U V w n_max base j enc : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hj : j < poolSizeWhp n_max) (henc_le : enc ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writePoolOwnerGenProg (((mkWhpCoreParams c U V w n_max, base), j), enc)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with poolOwner := Function.update fs.poolOwner j enc } s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have henc_g : enc < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max henc_le
  unfold writePoolOwnerGenProg
  simp only [wp_large_offPoolOwner hth, wp_large_globalPtrBits hth, wp_large_w hth]
  rw [clientState_writePackedGen]
  obtain ⟨hqv0, hloc0, -, hbptr0, hpool0, -⟩ := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨rfl, validProg_writePacked hw (globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1) hj
      (seg_add_le (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.2.1),
    fastStep_pureArray hw hj (by omega) (by omega) (Or.inr (by omega)) hseed hrep
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun i hi => ⟨(readPacked_writePacked_disjoint hw hi hj (Or.inl (by omega))).trans
          (hqv0 i hi).1,
        (readPacked_writePacked_disjoint hw hi hj (Or.inl (by omega))).trans (hqv0 i hi).2⟩)
      (fun b hb loc hl =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hl) hj
          (Or.inl (by omega))).trans (hloc0 b hb loc hl))
      (fun b hb k hk =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hk) hj
          (Or.inl (by omega))).trans (hbptr0 b hb k hk))
      (fun j' hj' => ⟨(readPacked_writePacked_disjoint hw hj' hj (Or.inl (by omega))).trans
          (hpool0 j' hj').1, ?_⟩)⟩
  simp only [Function.update_apply]; split_ifs with hjj
  · subst hjj; exact readPacked_writePacked_self _ _ _ s.mem j' henc_g
  · exact (readPacked_writePacked_of_ne hw s.mem hjj enc).trans (hpool0 j' hj').2

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
