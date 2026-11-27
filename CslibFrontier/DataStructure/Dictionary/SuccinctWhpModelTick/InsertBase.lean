/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep
-- `import all`: reads private buffer-skip helper `BufMapRel.insert_skip` from `Common`.
import all CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Backyard-Pool Allocation and Shared Fresh-Insertion Invariants

Internal backyard-pool slot allocation (`pool_alloc_new`) and common `CoreFastInv` field proofs
(`FastInsertFreshBase`, `fastInsertFresh_base`) shared by both the colliding-fingerprint buffer
branch and the collision-free live-slice branch of `fastInsert`
[BenderFarachColtonKuszmaulKuszmaul2024].

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.FastInsertFreshBase`: bundle of common `CoreFastInv`
  and coordinate-preservation properties of `fastInsertFresh` independent of `hasFpCollision`.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.fastInsertFresh_base`: establishes
  `FastInsertFreshBase` whenever `fastFindLoc` misses and capacity/buffer-lookup guards pass.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators

/-- Allocating coordinate `X = fs.bktCount b` (`X < totalLocalCoordsWhp n_max`, with
`0 < fs.poolFreeTop` whenever `capFrontWhp n_max ≤ X`) preserves all backyard-pool invariants,
preserves `physSlot` on all existing active coordinates `loc < fs.bktCount b'`, and yields a fresh
physical slot `fs'.physSlot n_max b X` disjoint from all existing active slots. -/
private theorem pool_alloc_new {c U V n_max b : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hX_lt : fs.bktCount b < totalLocalCoordsWhp n_max)
    (htop_pos : capFrontWhp n_max ≤ fs.bktCount b → 0 < fs.poolFreeTop)
    (hbkt' : fs'.bktCount = Function.update fs.bktCount b (fs.bktCount b + 1))
    (hstk' : fs'.poolFreeStack = fs.poolFreeStack)
    (htop' : fs'.poolFreeTop =
      if capFrontWhp n_max ≤ fs.bktCount b then fs.poolFreeTop - 1 else fs.poolFreeTop)
    (hbp' : fs'.backPtr =
      if capFrontWhp n_max ≤ fs.bktCount b then
        Function.update fs.backPtr b
          (Function.update (fs.backPtr b) (fs.bktCount b - capFrontWhp n_max)
            (fs.poolFreeStack (fs.poolFreeTop - 1)))
      else fs.backPtr)
    (hown' : fs'.poolOwner =
      if capFrontWhp n_max ≤ fs.bktCount b then
        Function.update fs.poolOwner (fs.poolFreeStack (fs.poolFreeTop - 1))
          (b * capBackWhp n_max + (fs.bktCount b - capFrontWhp n_max))
      else fs.poolOwner) :
    (∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
      fs'.physSlot n_max b' loc = fs.physSlot n_max b' loc ∧
      fs'.physSlot n_max b' loc ≠ fs'.physSlot n_max b (fs.bktCount b)) ∧
    fs'.poolFreeTop ≤ poolSizeWhp n_max ∧
    (∀ b' < numBucketsWhp n_max, ∀ k < fs'.bktCount b' - capFrontWhp n_max,
      fs'.backPtr b' k < poolSizeWhp n_max ∧
      fs'.poolOwner (fs'.backPtr b' k) = b' * capBackWhp n_max + k) ∧
    (∀ j < fs'.poolFreeTop, fs'.poolFreeStack j < poolSizeWhp n_max) ∧
    (∀ b₁ < numBucketsWhp n_max, ∀ k₁ < fs'.bktCount b₁ - capFrontWhp n_max,
     ∀ b₂ < numBucketsWhp n_max, ∀ k₂ < fs'.bktCount b₂ - capFrontWhp n_max,
       fs'.backPtr b₁ k₁ = fs'.backPtr b₂ k₂ → b₁ = b₂ ∧ k₁ = k₂) ∧
    (∀ j₁ < fs'.poolFreeTop, ∀ j₂ < fs'.poolFreeTop,
      fs'.poolFreeStack j₁ = fs'.poolFreeStack j₂ → j₁ = j₂) ∧
    (∀ b' < numBucketsWhp n_max, ∀ k < fs'.bktCount b' - capFrontWhp n_max,
     ∀ j < fs'.poolFreeTop, fs'.backPtr b' k ≠ fs'.poolFreeStack j) ∧
    fs'.poolFreeTop +
      ∑ b' ∈ range (numBucketsWhp n_max), (fs'.bktCount b' - capFrontWhp n_max) =
      poolSizeWhp n_max := by
  set X := fs.bktCount b
  let cf := capFrontWhp n_max
  have hbp_pres : ∀ b' < numBucketsWhp n_max, ∀ k < fs.bktCount b' - cf,
      fs'.backPtr b' k = fs.backPtr b' k := by
    intro b' _ k hk
    rw [hbp']
    split_ifs with hcf
    · by_cases hbb : b' = b
      · subst hbb
        rw [Function.update_self, Function.update_of_ne (by omega)]
      · rw [Function.update_of_ne hbb]
    · rfl
  have hk_old : ∀ b' k, k < Function.update fs.bktCount b (X + 1) b' - cf →
      (b' = b → cf ≤ X → k ≠ X - cf) → k < fs.bktCount b' - cf := by
    intro b' k hk hbk
    rcases eq_or_ne b' b with rfl | hbb
    · rw [Function.update_self] at hk
      by_cases hcf : cf ≤ X
      · have := hbk rfl hcf; omega
      · omega
    · rwa [Function.update_of_ne hbb] at hk
  have hphys_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
      fs'.physSlot n_max b' loc = fs.physSlot n_max b' loc := by
    intro b' hb' loc hloc
    dsimp only [FastState.physSlot]
    split_ifs with hlt
    · rfl
    · rw [hbp_pres b' hb' (loc - cf) (by omega)]
  have hphys_ne : ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
      fs'.physSlot n_max b' loc ≠ fs'.physSlot n_max b X := by
    intro b' hb' loc hloc
    rw [hphys_pres b' hb' loc hloc]
    dsimp only [FastState.physSlot]
    change (if loc < cf then b' * cf + loc
        else numBucketsWhp n_max * cf + fs.backPtr b' (loc - cf)) ≠
      (if X < cf then b * cf + X else numBucketsWhp n_max * cf + fs'.backPtr b (X - cf))
    by_cases hcf : cf ≤ X
    · have hp : ¬(X < cf) := by omega
      have htop0 := htop_pos hcf
      rw [ite_eq_right hp, hbp', ite_eq_left hcf, Function.update_self, Function.update_self]
      split_ifs with hlt
      · have : b' * cf + loc < numBucketsWhp n_max * cf := by
          calc b' * cf + loc < b' * cf + cf := by omega
            _ = (b' + 1) * cf := by ring
            _ ≤ numBucketsWhp n_max * cf := Nat.mul_le_mul_right cf hb'
        omega
      · intro heq
        have hbp_eq : fs.backPtr b' (loc - cf) = fs.poolFreeStack (fs.poolFreeTop - 1) := by omega
        exact hc.back_free_disj b' hb' (loc - cf) (by omega) (fs.poolFreeTop - 1) (by omega) hbp_eq
    · have hp : X < cf := by omega
      rw [ite_eq_left hp]
      split_ifs with hlt
      · intro heq
        have hcf_pos : 0 < cf := by omega
        have h1 : (b' * cf + loc) / cf = b' := by
          rw [Nat.mul_comm b' cf, Nat.mul_add_div hcf_pos, Nat.div_eq_of_lt hlt, add_zero]
        have h2 : (b * cf + X) / cf = b := by
          rw [Nat.mul_comm b cf, Nat.mul_add_div hcf_pos, Nat.div_eq_of_lt hp, add_zero]
        have hbb : b' = b := by rw [← h1, heq, h2]
        subst hbb
        omega
      · have : b * cf + X < numBucketsWhp n_max * cf := by
          calc b * cf + X < b * cf + cf := by omega
            _ = (b + 1) * cf := by ring
            _ ≤ numBucketsWhp n_max * cf := Nat.mul_le_mul_right cf hb
        omega
  have hsum_split_old := Finset.add_sum_erase (range (numBucketsWhp n_max))
    (fun b' => fs.bktCount b' - cf) (Finset.mem_range.mpr hb)
  have hsum_split_new := Finset.add_sum_erase (range (numBucketsWhp n_max))
    (fun b' => fs'.bktCount b' - cf) (Finset.mem_range.mpr hb)
  have herase_eq :
      ∑ x ∈ (range (numBucketsWhp n_max)).erase b, (fs'.bktCount x - cf) =
        ∑ x ∈ (range (numBucketsWhp n_max)).erase b, (fs.bktCount x - cf) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hbkt', Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  have hcons : fs'.poolFreeTop +
      ∑ b' ∈ range (numBucketsWhp n_max), (fs'.bktCount b' - cf) = poolSizeWhp n_max := by
    have hpc := hc.pool_conservation
    rw [← hsum_split_old] at hpc
    rw [← hsum_split_new, herase_eq, hbkt', Function.update_self, htop']
    split_ifs with hcf
    · have := htop_pos hcf; omega
    · omega
  refine ⟨fun b' hb' loc hloc => ⟨hphys_pres b' hb' loc hloc, hphys_ne b' hb' loc hloc⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, hcons⟩
  · rw [htop']; have := hc.poolFreeTop_le; split_ifs <;> omega
  · intro b' hb' k hk
    rw [hbkt'] at hk
    by_cases hcf : cf ≤ X
    · have htop0 := htop_pos hcf
      by_cases hbk : b' = b ∧ k = X - cf
      · rcases hbk with ⟨rfl, rfl⟩
        rw [hbp', hown', ite_eq_left hcf, ite_eq_left hcf, Function.update_self,
          Function.update_self, Function.update_self]
        exact ⟨hc.freeStack_lt _ (by omega), rfl⟩
      · have hk0 := hk_old b' k hk fun h _ hk' => hbk ⟨h, hk'⟩
        rw [hbp_pres b' hb' k hk0, hown', ite_eq_left hcf,
          Function.update_of_ne (hc.back_free_disj b' hb' k hk0 (fs.poolFreeTop - 1) (by omega))]
        exact hc.backPtr_valid b' hb' k hk0
    · have hk0 := hk_old b' k hk fun _ h => absurd h hcf
      rw [hbp_pres b' hb' k hk0, hown', ite_eq_right hcf]
      exact hc.backPtr_valid b' hb' k hk0
  · intro j hj
    rw [htop'] at hj; rw [hstk']
    exact hc.freeStack_lt j (by split_ifs at hj <;> omega)
  · intro b₁ hb₁ k₁ hk₁ b₂ hb₂ k₂ hk₂ heq
    rw [hbkt'] at hk₁ hk₂
    by_cases hcf : cf ≤ X
    · have htop0 := htop_pos hcf
      have eval_bp : ∀ b' < numBucketsWhp n_max,
          ∀ k < Function.update fs.bktCount b (X + 1) b' - cf,
          (b' = b ∧ k = X - cf ∧ fs'.backPtr b' k = fs.poolFreeStack (fs.poolFreeTop - 1)) ∨
          (k < fs.bktCount b' - cf ∧ fs'.backPtr b' k = fs.backPtr b' k) := by
        intro b' hb' k hk
        by_cases hbk : b' = b ∧ k = X - cf
        · rcases hbk with ⟨rfl, rfl⟩
          left; refine ⟨rfl, rfl, ?_⟩
          rw [hbp', ite_eq_left hcf, Function.update_self, Function.update_self]
        · have hk0 := hk_old b' k hk fun h _ hk' => hbk ⟨h, hk'⟩
          exact .inr ⟨hk0, hbp_pres b' hb' k hk0⟩
      rcases eval_bp b₁ hb₁ k₁ hk₁ with ⟨rfl, rfl, he1⟩ | ⟨hk1_0, he1⟩ <;>
        rcases eval_bp b₂ hb₂ k₂ hk₂ with ⟨rfl, rfl, he2⟩ | ⟨hk2_0, he2⟩
      · exact ⟨rfl, rfl⟩
      · rw [he1, he2] at heq
        exact absurd heq.symm (hc.back_free_disj b₂ hb₂ k₂ hk2_0 _ (by omega))
      · rw [he1, he2] at heq
        exact absurd heq (hc.back_free_disj b₁ hb₁ k₁ hk1_0 _ (by omega))
      · rw [he1, he2] at heq
        exact hc.backPtr_inj b₁ hb₁ k₁ hk1_0 b₂ hb₂ k₂ hk2_0 heq
    · rw [hbp', ite_eq_right hcf] at heq
      exact hc.backPtr_inj b₁ hb₁ k₁ (hk_old b₁ k₁ hk₁ fun _ h => absurd h hcf)
        b₂ hb₂ k₂ (hk_old b₂ k₂ hk₂ fun _ h => absurd h hcf) heq
  · intro j₁ hj₁ j₂ hj₂ heq
    rw [htop'] at hj₁ hj₂; rw [hstk'] at heq
    exact hc.freeStack_inj j₁ (by split_ifs at hj₁ <;> omega)
      j₂ (by split_ifs at hj₂ <;> omega) heq
  · intro b' hb' k hk j hj
    rw [hbkt'] at hk; rw [htop'] at hj; rw [hstk']
    by_cases hcf : cf ≤ X
    · rw [ite_eq_left hcf] at hj
      have htop0 := htop_pos hcf
      by_cases hbk : b' = b ∧ k = X - cf
      · rcases hbk with ⟨rfl, rfl⟩
        rw [hbp', ite_eq_left hcf, Function.update_self, Function.update_self]
        intro heq
        have := hc.freeStack_inj (fs.poolFreeTop - 1) (by omega) j (by omega) heq
        omega
      · have hk0 := hk_old b' k hk fun h _ hk' => hbk ⟨h, hk'⟩
        rw [hbp_pres b' hb' k hk0]
        exact hc.back_free_disj b' hb' k hk0 j (by omega)
    · rw [ite_eq_right hcf] at hj
      have hk0 := hk_old b' k hk fun _ h => absurd h hcf
      rw [hbp_pres b' hb' k hk0]
      exact hc.back_free_disj b' hb' k hk0 j hj


/-- Common coordinate-preservation, dictionary-refinement, backyard-pool, and reduced-key
non-collision properties of `fastInsertFresh` shared by both `hasFpCollision` branches. -/
structure FastInsertFreshBase (c U V n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs : FastState) (dict : State U) (u : Fin U) (v : ℕ) (hasFpCollision : Bool) : Prop where
  /-- Updated `bktCount` increments bucket `b` by `1`. -/
  hfsIns_bkt :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    fsIns.bktCount = Function.update fs.bktCount b (X + 1)
  /-- Fingerprints at all pre-existing active coordinates are preserved. -/
  hfp_pres :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ salt, ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
      fsIns.fpAt c U n_max θ salt b' loc = fs.fpAt c U n_max θ salt b' loc
  /-- Reduced keys at all pre-existing active coordinates are preserved. -/
  hrk_pres :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
      fsIns.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc
  /-- Fingerprint at the newly allocated coordinate `(b, X)` equals `fpOfSalt`. -/
  hfp_new :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ salt, fsIns.fpAt c U n_max θ salt b X = fpOfSalt c U n_max θ.2 salt u
  /-- Reduced key at the newly allocated coordinate `(b, X)` equals `fpReducedKey`. -/
  hrk_new :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    fsIns.rKeyAt c U n_max θ b X = fpReducedKey c U n_max θ.2 u
  /-- No pre-existing `curEp`-buffered coordinate shares `u`'s reduced key. -/
  hno_rk_cur : ∀ b' < numBucketsWhp n_max, ∀ l' < fs.bktCount b',
    fs.locState b' l' = 2 + fs.curEp → fs.rKeyAt c U n_max θ b' l' ≠ fpReducedKey c U n_max θ.2 u
  /-- No pre-existing buffered coordinate (`2 ≤ locState`) shares `u`'s reduced key. -/
  hno_rk_any : ∀ b' < numBucketsWhp n_max, ∀ l' < fs.bktCount b',
    2 ≤ fs.locState b' l' → fs.rKeyAt c U n_max θ b' l' ≠ fpReducedKey c U n_max θ.2 u
  /-- Global quotient/value word bounds on `fsIns`. -/
  hqv_glob' :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ p, fsIns.quotArr p < 2 ^ quotBitsWhp U n_max ∧ fsIns.valArr p < max V 1
  /-- Active coordinate count bound on `fsIns`. -/
  hbkt_le' :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ b' < numBucketsWhp n_max, fsIns.bktCount b' ≤ totalLocalCoordsWhp n_max
  /-- Out-of-range bucket counts remain `0` on `fsIns`. -/
  hbkt_ge0' :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ b', numBucketsWhp n_max ≤ b' → fsIns.bktCount b' = 0
  /-- Active item reconstruction validity on `fsIns`. -/
  hact_item' :
    let h1 := bktHash c U n_max θ.1
    let b := feistelBucket (bWhp n_max) h1 u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ b' < numBucketsWhp n_max, ∀ l' < fsIns.bktCount b',
      let kv := fsIns.keyValAt c U n_max θ.1 b' l'
      kv < U ∧ feistelBucket (bWhp n_max) h1 kv = b' ∧
      keyQuotient (bWhp n_max) kv = fsIns.quotArr (fsIns.physSlot n_max b' l') ∧
      fsIns.valArr (fsIns.physSlot n_max b' l') < V
  /-- Intra-bucket quotient injectivity on `fsIns`. -/
  hquot_inj' :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ b' < numBucketsWhp n_max, ∀ l₁ < fsIns.bktCount b', ∀ l₂ < fsIns.bktCount b',
      fsIns.quotArr (fsIns.physSlot n_max b' l₁) = fsIns.quotArr (fsIns.physSlot n_max b' l₂) →
      l₁ = l₂
  /-- Exact `Function.update dict u (some v)` refinement on `fsIns`. -/
  hdict_map' :
    let h1 := bktHash c U n_max θ.1
    let b := feistelBucket (bWhp n_max) h1 u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ u' : Fin U,
      let b' := feistelBucket (bWhp n_max) h1 u'.val
      let q' := keyQuotient (bWhp n_max) u'.val
      (Function.update dict u (some v) u' = none ↔
        ∀ loc < fsIns.bktCount b', fsIns.quotArr (fsIns.physSlot n_max b' loc) ≠ q') ∧
      (∀ v', Function.update dict u (some v) u' = some v' ↔
        ∃ loc < fsIns.bktCount b',
          fsIns.quotArr (fsIns.physSlot n_max b' loc) = q' ∧
          fsIns.valArr (fsIns.physSlot n_max b' loc) = v')
  /-- Backyard pool top bound on `fsIns`. -/
  hpoolTop' :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    fsIns.poolFreeTop ≤ poolSizeWhp n_max
  /-- Backyard pointer/owner correspondence on `fsIns`. -/
  hbp_val' :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ b' < numBucketsWhp n_max, ∀ k < fsIns.bktCount b' - capFrontWhp n_max,
      fsIns.backPtr b' k < poolSizeWhp n_max ∧
      fsIns.poolOwner (fsIns.backPtr b' k) = b' * capBackWhp n_max + k
  /-- Free-stack slot bounds on `fsIns`. -/
  hfree_lt' :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ j < fsIns.poolFreeTop, fsIns.poolFreeStack j < poolSizeWhp n_max
  /-- Backyard pointer injectivity on `fsIns`. -/
  hbp_inj' :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ b₁ < numBucketsWhp n_max, ∀ k₁ < fsIns.bktCount b₁ - capFrontWhp n_max,
    ∀ b₂ < numBucketsWhp n_max, ∀ k₂ < fsIns.bktCount b₂ - capFrontWhp n_max,
      fsIns.backPtr b₁ k₁ = fsIns.backPtr b₂ k₂ → b₁ = b₂ ∧ k₁ = k₂
  /-- Free-stack injectivity on `fsIns`. -/
  hfree_inj' :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ j₁ < fsIns.poolFreeTop, ∀ j₂ < fsIns.poolFreeTop,
      fsIns.poolFreeStack j₁ = fsIns.poolFreeStack j₂ → j₁ = j₂
  /-- Disjointness of allocated backyard slots and free-stack slots on `fsIns`. -/
  hdisj' :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    ∀ b' < numBucketsWhp n_max, ∀ k < fsIns.bktCount b' - capFrontWhp n_max,
    ∀ j < fsIns.poolFreeTop, fsIns.backPtr b' k ≠ fsIns.poolFreeStack j
  /-- Backyard pool slot conservation on `fsIns`. -/
  hcons' :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let X := fs.bktCount b
    let fsIns := fastInsertFresh c n_max b X (keyQuotient (bWhp n_max) u.val) v
      (fpReducedKey c U n_max θ.2 u) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
      (fs.liveSliceIdx b) hasFpCollision (fastInsertAlloc n_max b X fs)
    fsIns.poolFreeTop +
      ∑ b' ∈ range (numBucketsWhp n_max), (fsIns.bktCount b' - capFrontWhp n_max) =
      poolSizeWhp n_max

/-- Establishes `FastInsertFreshBase` when `u` is absent from `fs` and all fresh-insertion capacity
and buffer-collision guards pass. -/
theorem fastInsertFresh_base {c U V n_max : ℕ} (hnU : n_max ≤ U)
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U}
    (hv : ValidFastState c U V n_max θ fs dict) {u : Fin U} {v : ℕ}
    (hv_lt : v < V)
    (hno_q : ∀ loc < fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val),
      fs.quotArr (fs.physSlot n_max
        (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) loc) ≠
        keyQuotient (bWhp n_max) u.val)
    (hX_lt : fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) <
      totalLocalCoordsWhp n_max)
    (htop_pos : capFrontWhp n_max ≤
      fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) →
      0 < fs.poolFreeTop)
    (hcur_lk_none : bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
      (fpReducedKey c U n_max θ.2 u) = none)
    (hold_lk_none : fs.rebStage ≤ 3 →
      bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp)
        (fpReducedKey c U n_max θ.2 u) = none)
    (hasFpCollision : Bool) :
    FastInsertFreshBase c U V n_max θ fs dict u v hasFpCollision := by
  have hv_max : v < max V 1 := hv_lt.trans_le (le_max_left V 1)
  set h1 := bktHash c U n_max θ.1
  set b := feistelBucket (bWhp n_max) h1 u.val
  set q_val := keyQuotient (bWhp n_max) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  set X := fs.bktCount b
  set cf := capFrontWhp n_max
  set rKey := fpReducedKey c U n_max θ.2 u
  have hrk_lt : rKey < 2 ^ (cTabWhp c * bCharWhp n_max) := fpReducedKey_lt c U n_max θ.2 u
  set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  set lIdx := fs.liveSliceIdx b
  set fsAlloc := fastInsertAlloc n_max b X fs
  set fsIns := fastInsertFresh c n_max b X q_val v rKey fp lIdx hasFpCollision fsAlloc
  set p_new := fsAlloc.physSlot n_max b X
  obtain ⟨hfsIns_bkt, hfsIns_stk, hfsIns_top, hfsIns_bp, hfsIns_own, hp_new_eq, hfsIns_q,
      hfsIns_v⟩ :
      fsIns.bktCount = Function.update fs.bktCount b (X + 1) ∧
      fsIns.poolFreeStack = fs.poolFreeStack ∧
      fsIns.poolFreeTop = (if cf ≤ X then fs.poolFreeTop - 1 else fs.poolFreeTop) ∧
      fsIns.backPtr = (if cf ≤ X then
        Function.update fs.backPtr b
          (Function.update (fs.backPtr b) (X - cf) (fs.poolFreeStack (fs.poolFreeTop - 1)))
        else fs.backPtr) ∧
      fsIns.poolOwner = (if cf ≤ X then
        Function.update fs.poolOwner (fs.poolFreeStack (fs.poolFreeTop - 1))
          (b * capBackWhp n_max + (X - cf))
        else fs.poolOwner) ∧
      fsIns.physSlot n_max b X = p_new ∧
      fsIns.quotArr = Function.update fs.quotArr p_new q_val ∧
      fsIns.valArr = Function.update fs.valArr p_new v := by
    dsimp only [fsIns, fastInsertFresh, p_new, FastState.physSlot, fsAlloc, fastInsertAlloc, cf]
    by_cases hc : hasFpCollision = true <;> by_cases hcap : capFrontWhp n_max ≤ X <;>
      simp only [hc, hcap, Bool.false_eq_true, ↓reduceIte, true_and]
  obtain ⟨hphys_pair, hpoolTop', hbp_val', hfree_lt', hbp_inj', hfree_inj', hdisj', hcons'⟩ :=
    pool_alloc_new hv.toCore hb hX_lt htop_pos hfsIns_bkt hfsIns_stk hfsIns_top hfsIns_bp
      hfsIns_own
  have hqv_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
      fsIns.quotArr (fsIns.physSlot n_max b' loc) = fs.quotArr (fs.physSlot n_max b' loc) ∧
      fsIns.valArr (fsIns.physSlot n_max b' loc) = fs.valArr (fs.physSlot n_max b' loc) := by
    intro b' hb' loc hloc
    obtain ⟨hp_eq, hp_ne⟩ := hphys_pair b' hb' loc hloc
    rw [hp_new_eq] at hp_ne
    rw [hp_eq] at hp_ne ⊢
    rw [hfsIns_q, hfsIns_v, Function.update_of_ne hp_ne, Function.update_of_ne hp_ne]
    exact ⟨rfl, rfl⟩
  have hkv_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
      fsIns.keyValAt c U n_max θ.1 b' loc = fs.keyValAt c U n_max θ.1 b' loc := by
    intro b' hb' loc hloc
    dsimp only [FastState.keyValAt]
    rw [(hqv_pres b' hb' loc hloc).1]
  have hfp_pres : ∀ salt, ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
      fsIns.fpAt c U n_max θ salt b' loc = fs.fpAt c U n_max θ salt b' loc := by
    intro salt b' hb' loc hloc
    dsimp only [FastState.fpAt]
    rw [hkv_pres b' hb' loc hloc]
  have hrk_pres : ∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b',
      fsIns.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc := by
    intro b' hb' loc hloc
    dsimp only [FastState.rKeyAt]
    rw [hkv_pres b' hb' loc hloc]
  have hkv_new : fsIns.keyValAt c U n_max θ.1 b X = u.val := by
    dsimp only [FastState.keyValAt]
    rw [hp_new_eq, hfsIns_q, Function.update_self]
    exact feistelReconstruct_feistelBucket (bWhp n_max) h1 u.val
  have hfp_new : ∀ salt, fsIns.fpAt c U n_max θ salt b X = fpOfSalt c U n_max θ.2 salt u := by
    intro salt
    dsimp only [FastState.fpAt, fpOfSalt]
    rw [hkv_new]
    split_ifs with hs hu
    · rfl
    · exact absurd u.isLt hu
    · rfl
  have hrk_new : fsIns.rKeyAt c U n_max θ b X = rKey := by
    dsimp only [FastState.rKeyAt, rKey]
    rw [hkv_new]
    simp [u.isLt]
  -- `rKey` does not collide with any existing buffered item (`2 ≤ fs.locState b' l'`)
  obtain ⟨hia_cur, hna_cur, curMap, hv_cur, hrel_cur⟩ := hv.bufCur_valid
  have hcur_map_none : curMap rKey = none :=
    (hv_cur.lookup_eq hrk_lt).symm.trans hcur_lk_none
  have hno_rk_cur : ∀ b' < numBucketsWhp n_max, ∀ l' < fs.bktCount b',
      fs.locState b' l' = 2 + fs.curEp → fs.rKeyAt c U n_max θ b' l' ≠ rKey :=
    (hrel_cur.1 rKey).mp hcur_map_none
  have hno_rk_old : ∀ b' < numBucketsWhp n_max, ∀ l' < fs.bktCount b',
      fs.locState b' l' = 2 + fs.oldEp → fs.rKeyAt c U n_max θ b' l' ≠ rKey := by
    have hbo := hv.bufOld_valid
    by_cases hle3 : fs.rebStage ≤ 3
    · rw [ite_eq_left hle3] at hbo
      obtain ⟨_, _, oldMap, hv_old, hrel_old⟩ := hbo
      exact (hrel_old.1 rKey).mp ((hv_old.lookup_eq hrk_lt).symm.trans (hold_lk_none hle3))
    · rw [ite_eq_right hle3] at hbo
      split_ifs at hbo <;> exact fun b' hb' l' hl' hst => absurd hst (hbo.1 b' hb' l' hl')
  have hno_rk_any : ∀ b' < numBucketsWhp n_max, ∀ l' < fs.bktCount b',
      2 ≤ fs.locState b' l' → fs.rKeyAt c U n_max θ b' l' ≠ rKey := by
    intro b' hb' l' hl' h2
    have hact := hv.locState_active b' hb' l' hl'
    have hst_or : fs.locState b' l' = 2 + fs.curEp ∨ fs.locState b' l' = 2 + fs.oldEp := by
      rcases hv.curEp_or with hc | hc <;> (simp only [FastState.oldEp, hc]; omega)
    rcases hst_or with hsc | hso
    · exact hno_rk_cur b' hb' l' hl' hsc
    · exact hno_rk_old b' hb' l' hl' hso
  -- Common dictionary-map, active-item, and quotient-injectivity proofs for `fsIns`
  have hqv_glob' : ∀ p, fsIns.quotArr p < 2 ^ quotBitsWhp U n_max ∧
      fsIns.valArr p < max V 1 := by
    intro p
    rw [hfsIns_q, hfsIns_v]
    by_cases hp : p = p_new
    · subst hp
      rw [Function.update_self, Function.update_self]
      exact ⟨keyQuotient_lt_two_pow_quotBitsWhp hnU u, hv_max⟩
    · rw [Function.update_of_ne hp, Function.update_of_ne hp]
      exact hv.qv_global p
  have hbkt_le' : ∀ b' < numBucketsWhp n_max, fsIns.bktCount b' ≤ totalLocalCoordsWhp n_max := by
    intro b' hb'
    rw [hfsIns_bkt]
    by_cases hbb : b' = b
    · subst hbb; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hbb]; exact hv.bktCount_le b' hb'
  have hbkt_ge0' : ∀ b', numBucketsWhp n_max ≤ b' → fsIns.bktCount b' = 0 := by
    intro b' hb'
    rw [hfsIns_bkt, Function.update_of_ne (by omega)]
    exact hv.bktCount_ge_zero b' hb'
  -- Active coordinates of `fsIns`: the old ones and the new `(b, X)`
  have hlt_new : ∀ b' loc, loc < fsIns.bktCount b' ↔ loc < fs.bktCount b' ∨ (b' = b ∧ loc = X) := by
    intro b' loc
    rw [hfsIns_bkt]
    rcases eq_or_ne b' b with rfl | hbb
    · rw [Function.update_self, Nat.lt_succ_iff_lt_or_eq]
      exact ⟨fun h => h.imp_right fun h => ⟨rfl, h⟩, fun h => h.imp_right And.right⟩
    · rw [Function.update_of_ne hbb]
      exact ⟨.inl, fun h => h.resolve_right fun h' => hbb h'.1⟩
  have hact_item' : ∀ b' < numBucketsWhp n_max, ∀ l' < fsIns.bktCount b',
      let kv := fsIns.keyValAt c U n_max θ.1 b' l'
      kv < U ∧ feistelBucket (bWhp n_max) h1 kv = b' ∧
      keyQuotient (bWhp n_max) kv = fsIns.quotArr (fsIns.physSlot n_max b' l') ∧
      fsIns.valArr (fsIns.physSlot n_max b' l') < V := by
    intro b' hb' l' hl'
    dsimp only
    rcases (hlt_new b' l').mp hl' with hlt | ⟨rfl, rfl⟩
    · rw [hkv_pres b' hb' l' hlt, (hqv_pres b' hb' l' hlt).1, (hqv_pres b' hb' l' hlt).2]
      exact hv.active_item b' hb' l' hlt
    · rw [hkv_new, hp_new_eq, hfsIns_q, hfsIns_v, Function.update_self, Function.update_self]
      exact ⟨u.isLt, rfl, rfl, hv_lt⟩
  have hquot_inj' : ∀ b' < numBucketsWhp n_max, ∀ l₁ < fsIns.bktCount b',
      ∀ l₂ < fsIns.bktCount b',
      fsIns.quotArr (fsIns.physSlot n_max b' l₁) = fsIns.quotArr (fsIns.physSlot n_max b' l₂) →
      l₁ = l₂ := by
    intro b' hb' l₁ hl₁ l₂ hl₂ heq
    rcases (hlt_new b' l₁).mp hl₁ with hl₁' | ⟨hbb, rfl⟩ <;>
      rcases (hlt_new b' l₂).mp hl₂ with hl₂' | ⟨hbb, rfl⟩
    · rw [(hqv_pres b' hb' l₁ hl₁').1, (hqv_pres b' hb' l₂ hl₂').1] at heq
      exact hv.quot_inj b' hb' l₁ hl₁' l₂ hl₂' heq
    · subst hbb
      rw [(hqv_pres b hb l₁ hl₁').1, hp_new_eq, hfsIns_q, Function.update_self] at heq
      exact absurd heq (hno_q l₁ hl₁')
    · subst hbb
      rw [(hqv_pres b hb l₂ hl₂').1, hp_new_eq, hfsIns_q, Function.update_self] at heq
      exact absurd heq.symm (hno_q l₂ hl₂')
    · rfl
  have hdict_map' : ∀ u' : Fin U,
      let b' := feistelBucket (bWhp n_max) h1 u'.val
      let q' := keyQuotient (bWhp n_max) u'.val
      (Function.update dict u (some v) u' = none ↔
        ∀ loc < fsIns.bktCount b', fsIns.quotArr (fsIns.physSlot n_max b' loc) ≠ q') ∧
      (∀ v', Function.update dict u (some v) u' = some v' ↔
        ∃ loc < fsIns.bktCount b',
          fsIns.quotArr (fsIns.physSlot n_max b' loc) = q' ∧
          fsIns.valArr (fsIns.physSlot n_max b' loc) = v') := by
    intro u'
    dsimp only
    set b' := feistelBucket (bWhp n_max) h1 u'.val
    set q' := keyQuotient (bWhp n_max) u'.val
    have hb' : b' < numBucketsWhp n_max := feistelBucket_lt _ _ _
    by_cases hu' : u' = u
    · subst hu'
      have hb'_eq : b' = b := rfl
      have hq'_eq : q' = q_val := rfl
      rw [Function.update_self, hb'_eq, hq'_eq, hfsIns_bkt, Function.update_self]
      have hqX : fsIns.quotArr (fsIns.physSlot n_max b X) = q_val := by
        rw [hp_new_eq, hfsIns_q, Function.update_self]
      have hvX : fsIns.valArr (fsIns.physSlot n_max b X) = v := by
        rw [hp_new_eq, hfsIns_v, Function.update_self]
      refine ⟨⟨fun h => (by cases h), fun hall => absurd hqX (hall X (Nat.lt_succ_self X))⟩,
        fun v' => ⟨fun h => ?_, fun ⟨l', hl', hql, hvl⟩ => ?_⟩⟩
      · injection h with hv_eq; subst hv_eq
        exact ⟨X, Nat.lt_succ_self X, hqX, hvX⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hl' with hlt | rfl
        · rw [(hqv_pres b hb l' hlt).1] at hql
          exact absurd hql (hno_q l' hlt)
        · rw [hvX] at hvl
          exact congrArg some hvl
    · rw [Function.update_of_ne hu']
      obtain ⟨hn_iff, hs_iff⟩ := hv.dict_map u'
      change (dict u' = none ↔ ∀ loc < fs.bktCount b',
        fs.quotArr (fs.physSlot n_max b' loc) ≠ q') at hn_iff
      have hs_iff' : ∀ v', dict u' = some v' ↔ ∃ loc < fs.bktCount b',
          fs.quotArr (fs.physSlot n_max b' loc) = q' ∧
          fs.valArr (fs.physSlot n_max b' loc) = v' := hs_iff
      have hnot_bq : ¬(b' = b ∧ q' = q_val) := by
        rintro ⟨hbb, hqq⟩
        apply hu'; apply Fin.ext
        rw [← feistelReconstruct_feistelBucket (bWhp n_max) h1 u'.val,
          ← feistelReconstruct_feistelBucket (bWhp n_max) h1 u.val]
        change feistelReconstruct (bWhp n_max) h1 b' q' =
          feistelReconstruct (bWhp n_max) h1 b q_val
        rw [hbb, hqq]
      refine ⟨hn_iff.trans ⟨fun hall loc hloc => ?_, fun hall loc hloc => ?_⟩,
        fun v' => (hs_iff' v').trans
          ⟨fun ⟨loc, hloc, hql, hvl⟩ => ?_, fun ⟨loc, hloc, hql, hvl⟩ => ?_⟩⟩
      · rcases (hlt_new b' loc).mp hloc with hlt | ⟨hbb, rfl⟩
        · rw [(hqv_pres b' hb' loc hlt).1]; exact hall loc hlt
        · rw [hbb, hp_new_eq, hfsIns_q, Function.update_self]
          exact fun heq => hnot_bq ⟨hbb, heq.symm⟩
      · have := hall loc ((hlt_new b' loc).mpr (.inl hloc))
        rwa [(hqv_pres b' hb' loc hloc).1] at this
      · exact ⟨loc, (hlt_new b' loc).mpr (.inl hloc), (hqv_pres b' hb' loc hloc).1.trans hql,
          (hqv_pres b' hb' loc hloc).2.trans hvl⟩
      · rcases (hlt_new b' loc).mp hloc with hlt | ⟨hbb, rfl⟩
        · rw [(hqv_pres b' hb' loc hlt).1] at hql
          rw [(hqv_pres b' hb' loc hlt).2] at hvl
          exact ⟨loc, hlt, hql, hvl⟩
        · rw [hbb, hp_new_eq, hfsIns_q, Function.update_self] at hql
          exact absurd ⟨hbb, hql.symm⟩ hnot_bq
  exact
    { hfsIns_bkt := hfsIns_bkt
      hfp_pres := hfp_pres
      hrk_pres := hrk_pres
      hfp_new := hfp_new
      hrk_new := hrk_new
      hno_rk_cur := hno_rk_cur
      hno_rk_any := hno_rk_any
      hqv_glob' := hqv_glob'
      hbkt_le' := hbkt_le'
      hbkt_ge0' := hbkt_ge0'
      hact_item' := hact_item'
      hquot_inj' := hquot_inj'
      hdict_map' := hdict_map'
      hpoolTop' := hpoolTop'
      hbp_val' := hbp_val'
      hfree_lt' := hfree_lt'
      hbp_inj' := hbp_inj'
      hfree_inj' := hfree_inj'
      hdisj' := hdisj'
      hcons' := hcons' }

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
