/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpHashProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Frame
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Internal
import CslibFrontier.Tactic.Realize

/-!
# Fast-Mode Slot-Array Accessors (`quotArr`, `valArr`, `backPtr`) and Coordinate Hashing

This module implements the parameter-free `Memory.Prog` subroutines and `Realizes .exact`
certificates for slot-indexed packed arrays and coordinate-hash evaluation on `FastMemRep`:

1. Quotient and value array accessors (`readQuotGenProg`, `writeQuotGenProg`, `readValGenProg`,
   `writeValGenProg`).
2. Backyard pointer array accessors (`readBackPtrGenProg`, `writeBackPtrGenProg`).
3. Composite coordinate address and hash helpers (`physSlotGenProg`, `rKeyAtGenProg`,
   `fpAtGenProg`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.readQuotGenProg`, `writeQuotGenProg`,
  `readValGenProg`, `writeValGenProg`, `readBackPtrGenProg`, `writeBackPtrGenProg`,
  `physSlotGenProg`, `PhysSlotPre`, `rKeyAtGenProg`, `CoordHashPre`, `fpAtGenProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.writeQuotGenProg_fastStep`,
  `writeValGenProg_fastStep`, `writeBackPtrGenProg_fastStep`, `physSlotGenProg_spec`,
  `rKeyAtGenProg_spec`, `fpAtGenProg_spec`.
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
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-! ## Section 1: `quotArr` and `valArr` Accessors -/

private theorem quot_pre_safe {w base p : ℕ} {cp : WhpCoreParams}
    (h : WhpLargeEnvGen w cp base ∧ p < wpNMax cp) :
    ∃ N', w = wpW cp ∧ 0 < w ∧ wpQuotBits cp ≤ w ∧ p < N' ∧
      Fits w (base + wpOffQuot cp + packedWords N' (wpQuotBits cp) w) := by
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hp⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hqb : quotBitsWhp U n_max ≤ w := (Nat.sub_le _ _).trans (keyBits_le_w henv.2.2.2.2.2.1)
  simp only [wp_large_nMax hth, wp_large_offQuot hth, wp_large_quotBits hth, wp_large_w hth] at hp ⊢
  exact henv.packed_safe_true hqb hp (WhpLargeEnv.seg_end_le c U V w n_max).1

/-- Read `fs.quotArr p` (`p < n_max`, `d = ((cp, base), p)`). -/
@[irreducible] def readQuotGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), p) =>
    readPackedGenProg (((base, wpOffQuot cp), (wpQuotBits cp, wpW cp)), p)

theorem realizes_readQuotGen :
    Realizes .exact readQuotGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), p) _ => WhpLargeEnvGen w cp base ∧ p < wpNMax cp)
      (fun _ _ => 0) := by
  unfold readQuotGenProg
  realize [realizes_readPackedGen]
  rcases d with ⟨⟨cp, base⟩, p⟩
  exact quot_pre_safe h

theorem readQuotGenProg_spec {c U V w n_max base p : ℕ} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hp : p < n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readQuotGenProg ((mkWhpCoreParams c U V w n_max, base), p)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.quotArr p ∧
    memoryCost prog s = 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hle := seg_add_le (base := base) (WhpLargeEnv.seg_end_le c U V w n_max).1
  unfold readQuotGenProg
  simp only [wp_large_offQuot hth, wp_large_quotBits hth, wp_large_w hth]
  exact ⟨rfl, (clientResult_readPackedGen _ _ _ _ _ _).trans
    (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp).1, rfl, validProg_readPacked hw hp hle⟩

/-- Write `fs.quotArr p := q_val` (`p < n_max`, `d = (((cp, base), p), q_val)`). -/
@[irreducible] def writeQuotGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), p), q_val) =>
    writePackedGenProg ((((base, wpOffQuot cp), (wpQuotBits cp, wpW cp)), p), q_val)

theorem realizes_writeQuotGen :
    Realizes .exact writeQuotGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), p), _) _ => WhpLargeEnvGen w cp base ∧ p < wpNMax cp)
      (fun _ _ => 0) := by
  unfold writeQuotGenProg
  realize [realizes_writePackedGen]
  rcases d with ⟨⟨⟨cp, base⟩, p⟩, q_val⟩
  exact quot_pre_safe h

theorem writeQuotGenProg_fastStep {c U V w n_max base p q_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hp : p < n_max) (hq_lt : q_val < 2 ^ quotBitsWhp U n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writeQuotGenProg (((mkWhpCoreParams c U V w n_max, base), p), q_val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with quotArr := Function.update fs.quotArr p q_val } s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have hqb : quotBitsWhp U n_max ≤ w := (Nat.sub_le _ _).trans (keyBits_le_w henv.2.2.2.2.2.1)
  have hle := seg_add_le (base := base) (WhpLargeEnv.seg_end_le c U V w n_max).1
  unfold writeQuotGenProg
  simp only [wp_large_offQuot hth, wp_large_quotBits hth, wp_large_w hth]
  rw [clientState_writePackedGen]
  have hqv0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbptr0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpool0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨rfl, validProg_writePacked hw hqb hp hle,
    fastStep_pureArray hw hp le_rfl (by omega) (Or.inl (by omega)) hseed hrep
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun i hi => ⟨?_,
        (readPacked_writePacked_disjoint hw hi hp (Or.inr (by omega))).trans (hqv0 i hi).2⟩)
      (fun b hb loc hl =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hl) hp
          (Or.inr (by omega))).trans (hloc0 b hb loc hl))
      (fun b hb k hk =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hk) hp
          (Or.inr (by omega))).trans (hbptr0 b hb k hk))
      (fun j hj => ⟨(readPacked_writePacked_disjoint hw hj hp (Or.inr (by omega))).trans
          (hpool0 j hj).1,
        (readPacked_writePacked_disjoint hw hj hp (Or.inr (by omega))).trans (hpool0 j hj).2⟩)⟩
  simp only [Function.update_apply]; split_ifs with hip
  · subst hip; exact readPacked_writePacked_self _ _ _ s.mem i hq_lt
  · exact (readPacked_writePacked_of_ne hw s.mem hip q_val).trans (hqv0 i hi).1

private theorem val_pre_safe {w base p : ℕ} {cp : WhpCoreParams}
    (h : WhpLargeEnvGen w cp base ∧ p < wpNMax cp) :
    ∃ N', w = wpW cp ∧ 0 < w ∧ wpValBits cp ≤ w ∧ p < N' ∧
      Fits w (base + wpOffVal cp + packedWords N' (wpValBits cp) w) := by
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hp⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hvb : valBits V ≤ w := valBits_le_w henv.2.2.2.2.2.2.1
  simp only [wp_large_nMax hth, wp_large_offVal hth, wp_large_valBits hth, wp_large_w hth] at hp ⊢
  exact henv.packed_safe_true hvb hp (WhpLargeEnv.seg_end_le c U V w n_max).2.1

/-- Read `fs.valArr p` (`p < n_max`, `d = ((cp, base), p)`). -/
@[irreducible] def readValGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base), p) =>
    readPackedGenProg (((base, wpOffVal cp), (wpValBits cp, wpW cp)), p)

theorem realizes_readValGen :
    Realizes .exact readValGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cp, base), p) _ => WhpLargeEnvGen w cp base ∧ p < wpNMax cp)
      (fun _ _ => 0) := by
  unfold readValGenProg
  realize [realizes_readPackedGen]
  rcases d with ⟨⟨cp, base⟩, p⟩
  exact val_pre_safe h

theorem readValGenProg_spec {c U V w n_max base p : ℕ} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hp : p < n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readValGenProg ((mkWhpCoreParams c U V w n_max, base), p)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.valArr p ∧
    memoryCost prog s = 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hle := seg_add_le (base := base) (WhpLargeEnv.seg_end_le c U V w n_max).2.1
  unfold readValGenProg
  simp only [wp_large_offVal hth, wp_large_valBits hth, wp_large_w hth]
  exact ⟨rfl, (clientResult_readPackedGen _ _ _ _ _ _).trans
    (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp).2, rfl, validProg_readPacked hw hp hle⟩

/-- Write `fs.valArr p := v_val` (`p < n_max`, `d = (((cp, base), p), v_val)`). -/
@[irreducible] def writeValGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), p), v_val) =>
    writePackedGenProg ((((base, wpOffVal cp), (wpValBits cp, wpW cp)), p), v_val)

theorem realizes_writeValGen :
    Realizes .exact writeValGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), p), _) _ => WhpLargeEnvGen w cp base ∧ p < wpNMax cp)
      (fun _ _ => 0) := by
  unfold writeValGenProg
  realize [realizes_writePackedGen]
  rcases d with ⟨⟨⟨cp, base⟩, p⟩, v_val⟩
  exact val_pre_safe h

theorem writeValGenProg_fastStep {c U V w n_max base p v_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hp : p < n_max) (hv_lt : v_val < 2 ^ valBits V)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writeValGenProg (((mkWhpCoreParams c U V w n_max, base), p), v_val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with valArr := Function.update fs.valArr p v_val } s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have hvb : valBits V ≤ w := valBits_le_w henv.2.2.2.2.2.2.1
  have hle := seg_add_le (base := base) (WhpLargeEnv.seg_end_le c U V w n_max).2.1
  unfold writeValGenProg
  simp only [wp_large_offVal hth, wp_large_valBits hth, wp_large_w hth]
  rw [clientState_writePackedGen]
  have hqv0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbptr0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpool0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨rfl, validProg_writePacked hw hvb hp hle,
    fastStep_pureArray hw hp (by omega) (by omega) (Or.inl (by omega)) hseed hrep
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun i hi => ⟨(readPacked_writePacked_disjoint hw hi hp (Or.inl (by omega))).trans
          (hqv0 i hi).1, ?_⟩)
      (fun b hb loc hl =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hl) hp
          (Or.inr (by omega))).trans (hloc0 b hb loc hl))
      (fun b hb k hk =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb hk) hp
          (Or.inr (by omega))).trans (hbptr0 b hb k hk))
      (fun j hj => ⟨(readPacked_writePacked_disjoint hw hj hp (Or.inr (by omega))).trans
          (hpool0 j hj).1,
        (readPacked_writePacked_disjoint hw hj hp (Or.inr (by omega))).trans (hpool0 j hj).2⟩)⟩
  simp only [Function.update_apply]; split_ifs with hip
  · subst hip; exact readPacked_writePacked_self _ _ _ s.mem i hv_lt
  · exact (readPacked_writePacked_of_ne hw s.mem hip v_val).trans (hqv0 i hi).2

/-! ## Section 2: `backPtr` Accessors -/

private theorem backPtr_realize_bounds {w base b k : ℕ} {cp : WhpCoreParams}
    (h : WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ k < wpCapBack cp) :
    Fits w (b * wpCapBack cp + k) ∧
    ∃ N', w = wpW cp ∧ 0 < w ∧ wpGlobalPtrBits cp ≤ w ∧ b * wpCapBack cp + k < N' ∧
      Fits w (base + wpOffBackPtr cp + packedWords N' (wpGlobalPtrBits cp) w) := by
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hk⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  have hmcb := (large_index_bounds hth).1
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  simp only [wp_large_M hth, wp_large_capBack hth, wp_large_offBackPtr hth,
    wp_large_globalPtrBits hth, wp_large_w hth] at hb hk ⊢
  have hidx := mul_add_lt_mul_bound hb hk
  exact ⟨henv.fits_of_le_n_max (by omega),
    henv.packed_safe_true hgk hidx (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.1⟩

private theorem backPtr_seg_le (c U V w n_max base : ℕ) :
    base + offBackPtr c U V w n_max +
      packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max :=
  seg_add_le (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.1

/-- Read `fs.backPtr b k` (`b < M`, `k < capBackWhp n_max`, `d = (((cp, base), b), k)`). -/
@[irreducible] def readBackPtrGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, base), b), k) => do
    let idx ← pure (b * wpCapBack cp + k)
    readPackedGenProg (((base, wpOffBackPtr cp), (wpGlobalPtrBits cp, wpW cp)), idx)

theorem realizes_readBackPtrGen :
    Realizes .exact readBackPtrGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((cp, base), b), k) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ k < wpCapBack cp)
      (fun _ _ => 0) := by
  unfold readBackPtrGenProg
  realize [realizes_readPackedGen]
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, k⟩
    obtain ⟨h2, h3⟩ := backPtr_realize_bounds h
    first | exact h2 | exact h3
  )

theorem readBackPtrGenProg_spec {c U V w n_max base b k : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hk : k < capBackWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := readBackPtrGenProg (((mkWhpCoreParams c U V w n_max, base), b), k)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.backPtr b k ∧
    memoryCost prog s = 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  unfold readBackPtrGenProg
  simp only [wp_large_capBack hth, wp_large_offBackPtr hth, wp_large_globalPtrBits hth,
    wp_large_w hth, pure_bind]
  exact ⟨rfl, (clientResult_readPackedGen _ _ _ _ _ _).trans
    (hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb k hk), rfl,
    validProg_readPacked henv.2.1 (mul_add_lt_mul_bound hb hk)
      (backPtr_seg_le c U V w n_max base)⟩

/-- Write `fs.backPtr b k := pSlot` (`d = ((((cp, base), b), k), pSlot)`). -/
@[irreducible] def writeBackPtrGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), k), pSlot) => do
    let idx ← pure (b * wpCapBack cp + k)
    writePackedGenProg ((((base, wpOffBackPtr cp), (wpGlobalPtrBits cp, wpW cp)), idx), pSlot)

theorem realizes_writeBackPtrGen :
    Realizes .exact writeBackPtrGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), k), _) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ k < wpCapBack cp)
      (fun _ _ => 0) := by
  unfold writeBackPtrGenProg
  realize [realizes_writePackedGen]
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, k⟩, pSlot⟩
    obtain ⟨h2, h3⟩ := backPtr_realize_bounds h
    first | exact h2 | exact h3
  )

theorem writeBackPtrGenProg_fastStep {c U V w n_max base b k pSlot : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hk : k < capBackWhp n_max) (hp_le : pSlot ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := writeBackPtrGenProg ((((mkWhpCoreParams c U V w n_max, base), b), k), pSlot)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with backPtr := Function.update fs.backPtr b (Function.update (fs.backPtr b) k pSlot) }
      s s' := by
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hch := largeOffsetChain c U V w n_max
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hp_g : pSlot < 2 ^ globalPtrBits n_max := lt_two_pow_globalPtrBits_of_le_n_max hp_le
  set idxW := b * capBackWhp n_max + k
  have hidxW := mul_add_lt_mul_bound hb hk
  unfold writeBackPtrGenProg
  simp only [wp_large_capBack hth, wp_large_offBackPtr hth, wp_large_globalPtrBits hth,
    wp_large_w hth, pure_bind]
  rw [clientState_writePackedGen]
  have hqv0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbptr0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpool0 := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨rfl, validProg_writePacked hw hgk hidxW (backPtr_seg_le c U V w n_max base),
    fastStep_pureArray hw hidxW (by omega) (by omega) (Or.inr (by omega)) hseed hrep
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun i hi => ⟨(readPacked_writePacked_disjoint hw hi hidxW (Or.inl (by omega))).trans
          (hqv0 i hi).1,
        (readPacked_writePacked_disjoint hw hi hidxW (Or.inl (by omega))).trans (hqv0 i hi).2⟩)
      (fun b' hb' loc hl =>
        (readPacked_writePacked_disjoint hw (mul_add_lt_mul_bound hb' hl) hidxW
          (Or.inl (by omega))).trans (hloc0 b' hb' loc hl))
      (fun b' hb' k' hk' => ?_)
      (fun j hj => ⟨(readPacked_writePacked_disjoint hw hj hidxW (Or.inr (by omega))).trans
          (hpool0 j hj).1,
        (readPacked_writePacked_disjoint hw hj hidxW (Or.inr (by omega))).trans
          (hpool0 j hj).2⟩)⟩
  dsimp only
  by_cases hbk : b' = b ∧ k' = k
  · rcases hbk with ⟨rfl, rfl⟩
    simp only [Function.update_self]
    exact readPacked_writePacked_self _ _ _ s.mem idxW hp_g
  · have hne : b' * capBackWhp n_max + k' ≠ idxW :=
      fun heq => hbk (mul_add_inj_right hk' hk heq)
    rw [readPacked_writePacked_of_ne hw s.mem hne pSlot, hbptr0 b' hb' k' hk']
    by_cases hbb : b' = b
    · subst hbb; simp [show k' ≠ k from fun h => hbk ⟨rfl, h⟩]
    · simp [hbb]

/-! ## Section 3: Composite Coordinate Helpers (`physSlot`, `rKeyAt`, `fpAt`) -/

/-- Compute `fs.physSlot n_max b loc` (`d = (((cp, base), b), loc)`). -/
@[irreducible] def physSlotGenProg : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, base), b), loc) => do
    let cf ← pure (wpCapFront cp)
    if loc < cf then
      pure (b * cf + loc)
    else do
      let k ← pure (loc - cf)
      let pSlot ← readBackPtrGenProg (((cp, base), b), k)
      pure (wpFrontTotal cp + pSlot)

/-- Precondition for `physSlotGenProg`: `(b, loc)` in bounds and backyard pointer `< poolSize`. -/
@[expose] def PhysSlotPre (w : ℕ) : ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, base), b), loc), s =>
    ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      b < numBucketsWhp n_max ∧
      loc < totalLocalCoordsWhp n_max ∧
      (capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max)

theorem realizes_physSlotGen :
    Realizes .exact physSlotGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      PhysSlotPre
      (fun _ _ => 0) := by
  unfold physSlotGenProg
  realize [realizes_readBackPtrGen]
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, loc⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hloc, hbp_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hps_eq := (large_index_bounds hth).2.1
    have hcb : capFrontWhp n_max ≤ loc → loc - capFrontWhp n_max < capBackWhp n_max := by
      unfold totalLocalCoordsWhp at hloc; omega
    simp only [wp_large_capFront hth, wp_large_frontTotal hth, wp_large_M hth,
      wp_large_capBack hth] at *
    first
    | (have hlt : b * capFrontWhp n_max + loc < numBucketsWhp n_max * capFrontWhp n_max :=
         mul_add_lt_mul_bound hb (by omega)
       exact henv.fits_of_le_n_max (by omega))
    | omega
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (obtain ⟨_, hres, _, _⟩ := readBackPtrGenProg_spec henv hb (hcb (by omega)) hrep (s := s)
       rw [hres]
       have hp := hbp_lt (by omega)
       exact henv.fits_of_le_n_max (by omega))
  )

theorem physSlotGenProg_spec {c U V w n_max base b loc : ℕ} {fs : FastState}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max)
    (hbp_lt : capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := physSlotGenProg (((mkWhpCoreParams c U V w n_max, base), b), loc)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.physSlot n_max b loc ∧
    fs.physSlot n_max b loc < n_max ∧
    memoryCost prog s ≤ 2 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hps_eq := (large_index_bounds hth).2.1
  unfold physSlotGenProg FastState.physSlot
  simp only [wp_large_capFront hth, wp_large_frontTotal hth, pure_bind]
  split_ifs with hcf
  · have hlt := mul_add_lt_mul_bound hb hcf
    exact ⟨rfl, rfl, by omega, Nat.zero_le 2, validProg_pure _⟩
  · have hk : loc - capFrontWhp n_max < capBackWhp n_max := by
      unfold totalLocalCoordsWhp at hloc; omega
    obtain ⟨hst, hres, hmc, hvp⟩ := readBackPtrGenProg_spec henv hb hk hrep (s := s)
    have hp := hbp_lt (Nat.not_lt.mp hcf)
    have hstep := CostBoundedStep.bind
      (g := fun pSlot => pure (numBucketsWhp n_max * capFrontWhp n_max + pSlot))
      ⟨hst, hres, hmc.le, hvp⟩ (.pure _ _)
    exact ⟨hstep.clientState_eq, hstep.clientResult_eq, by omega, hstep.memoryCost_le,
      hstep.validProg⟩

/-- Compute `fs.rKeyAt c U n_max θ b loc` (`d = (((wp, base), b), loc)`). -/
@[irreducible] def rKeyAtGenProg : ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((wp, base), b), loc) => do
    let (cp, _) := wp
    let p ← physSlotGenProg (((cp, base), b), loc)
    let q ← readQuotGenProg ((cp, base), p)
    let hrt ← mkHashRtGenProg (wp, base)
    rKeyOfQuotRtProg ((hrt, b), q)

/-- Precondition for `rKeyAtGenProg` and `fpAtGenProg` on coordinate `(b, loc)`. -/
@[expose] def CoordHashPre (w : ℕ) : ((WhpParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((wp, base), b), loc), s =>
    ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
      WhpLargeEnv c U V w₀ n_max w base ∧
      wp = mkWhpParams c U V w₀ n_max ∧
      SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      (∀ p < n_max, fs.quotArr p < 2 ^ quotBitsWhp U n_max) ∧
      b < numBucketsWhp n_max ∧
      loc < totalLocalCoordsWhp n_max ∧
      (capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max)

private theorem coordHashPrefix_spec {c U V w n_max base b loc : ℕ}
    {fs : FastState} {s : Memory.State} {β : Type}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max)
    (hbp : capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max)
    (cont : HashRt → ℕ → Memory.Prog β)
    {res : β} {C : ℕ}
    (hcont :
      let q := fs.quotArr (fs.physSlot n_max b loc)
      let prog := cont (mkHashRt c U w n_max base) q
      (Memory.spec 0).clientState s prog = s ∧
      (Memory.spec 0).clientResult s prog = res ∧
      memoryCost prog s ≤ C ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog) :
    let wp := mkWhpParams c U V w n_max
    let prog : Memory.Prog β := do
      let p ← physSlotGenProg (((wp.1, base), b), loc)
      let q ← readQuotGenProg ((wp.1, base), p)
      let hrt ← mkHashRtGenProg (wp, base)
      cont hrt q
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = res ∧
    memoryCost prog s ≤ C + 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro wp prog
  have hth := henv.2.2.2.1
  have hwp1 : mkWhpCoreParams c U V w n_max = wp.1 := by
    simp [wp, mkWhpParams, Nat.not_lt.mpr hth]
  obtain ⟨hps_st, hps_res, hps_lt, hps_mc, hps_vp⟩ :=
    physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
  obtain ⟨hrq_st, hrq_res, hrq_mc, hrq_vp⟩ := readQuotGenProg_spec henv hps_lt hrep (s := s)
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hc_st, hc_res, hc_mc, hc_vp⟩ := hcont
  rw [hwp1] at hps_st hps_res hps_mc hps_vp hrq_st hrq_res hrq_mc hrq_vp
  have hstep : CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s prog s res (C + 4) :=
    .mono (.bind ⟨hps_st, hps_res, hps_mc, hps_vp⟩ <|
      .bind ⟨hrq_st, hrq_res, hrq_mc.le, hrq_vp⟩ <|
      .bind ⟨hmh_st, hmh_res, hmh_mc.le, hmh_vp⟩ ⟨hc_st, hc_res, hc_mc, hc_vp⟩) (by omega)
  exact ⟨hstep.clientState_eq, hstep.clientResult_eq, hstep.memoryCost_le, hstep.validProg⟩

private theorem coordHashPre_goals {w base b loc : ℕ} {wp : WhpParams} {s : Memory.State}
    (h : CoordHashPre w (((wp, base), b), loc) s) :
    let cp := wp.1
    let p := (Memory.spec 0).clientResult s (physSlotGenProg (((cp, base), b), loc))
    let s1 := (Memory.spec 0).clientState s (physSlotGenProg (((cp, base), b), loc))
    let q := (Memory.spec 0).clientResult s1 (readQuotGenProg ((cp, base), p))
    let s2 := (Memory.spec 0).clientState s1 (readQuotGenProg ((cp, base), p))
    let hrt := (Memory.spec 0).clientResult s2 (mkHashRtGenProg (wp, base))
    let s3 := (Memory.spec 0).clientState s2 (mkHashRtGenProg (wp, base))
    PhysSlotPre w (((cp, base), b), loc) s ∧
    (WhpLargeEnvGen w cp base ∧ p < wpNMax cp) ∧
    QuotHashRtEnv w hrt q s3 := by
  obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hloc, hbp⟩ := h
  obtain rfl := henv.2.2.1
  have hth := henv.2.2.2.1
  have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  obtain ⟨hps_st, hps_res, hps_lt, _, _⟩ := physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
  obtain ⟨hrq_st, hrq_res, _, _⟩ := readQuotGenProg_spec henv hps_lt hrep (s := s)
  obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) hth s
  dsimp only
  simp only [hcp_eq, hps_st, hps_res, hrq_st, hrq_res, hmh_st, hmh_res, wp_large_nMax hth]
  exact ⟨⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hloc, hbp⟩,
    ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hps_lt⟩,
    ⟨c, U, V, w, n_max, θ, henv, rfl, hseed, hq_all _ hps_lt⟩⟩

theorem realizes_rKeyAtGen :
    Realizes .exact rKeyAtGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CoordHashPre
      (fun _ _ => 0) := by
  unfold rKeyAtGenProg
  realize [realizes_physSlotGen, realizes_readQuotGen, realizes_mkHashRtGen, realizes_rKeyOfQuotRt]
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc⟩
    obtain ⟨h1, ⟨h2a, h2b⟩, h3⟩ := coordHashPre_goals h
    first | exact h1 | exact h2a | exact h2b | exact h3
  )

theorem rKeyAtGenProg_spec {c U V w n_max base b loc : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max)
    (hbp : capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max) :
    let prog := rKeyAtGenProg (((mkWhpParams c U V w n_max, base), b), loc)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.rKeyAt c U n_max θ b loc ∧
    memoryCost prog s ≤ hashEvalCostWhp c + 5 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  unfold rKeyAtGenProg
  exact coordHashPrefix_spec henv hrep hb hloc hbp
    (fun hrt q => rKeyOfQuotRtProg ((hrt, b), q))
    (rKeyOfQuotRtProg_spec (b := b) (q := fs.quotArr (fs.physSlot n_max b loc)) henv hseed
      (s := s))

/-- Compute `fs.fpAt c U n_max θ salt b loc` (`d = ((((wp, base), salt), b), loc)`). -/
@[irreducible] def fpAtGenProg : (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((((wp, base), salt), b), loc) => do
    let (cp, _) := wp
    let p ← physSlotGenProg (((cp, base), b), loc)
    let q ← readQuotGenProg ((cp, base), p)
    let hrt ← mkHashRtGenProg (wp, base)
    fpOfQuotRtProg (((hrt, salt), b), q)

theorem realizes_fpAtGen :
    Realizes .exact fpAtGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((wp, base), _), b), loc) s => CoordHashPre w (((wp, base), b), loc) s)
      (fun _ _ => 0) := by
  unfold fpAtGenProg
  realize [realizes_physSlotGen, realizes_readQuotGen, realizes_mkHashRtGen, realizes_fpOfQuotRt]
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, salt⟩, b⟩, loc⟩
    obtain ⟨h1, ⟨h2a, h2b⟩, h3⟩ := coordHashPre_goals h
    first | exact h1 | exact h2a | exact h2b | exact h3
  )

theorem fpAtGenProg_spec {c U V w n_max base salt b loc : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max)
    (hbp : capFrontWhp n_max ≤ loc → fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max) :
    let prog := fpAtGenProg ((((mkWhpParams c U V w n_max, base), salt), b), loc)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fs.fpAt c U n_max θ salt b loc ∧
    memoryCost prog s ≤ 2 * hashEvalCostWhp c + 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  unfold fpAtGenProg
  exact coordHashPrefix_spec henv hrep hb hloc hbp
    (fun hrt q => fpOfQuotRtProg (((hrt, salt), b), q))
    (fpOfQuotRtProg_spec (salt := salt) (b := b) (q := fs.quotArr (fs.physSlot n_max b loc))
      henv hseed (s := s))

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
