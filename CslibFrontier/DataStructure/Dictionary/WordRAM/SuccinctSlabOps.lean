/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.WramOmega

/-!
# Amortized `O(1)` Slot Allocation and Deallocation in `Memory.Prog`

This module combines the tail-item operations (`appendTailItemProg`, `removeLastTailItemProg`) and
the `K`-step slab promotion/demotion loops (`promoteSlabProg`, `demoteSlabProg`) into the high-level
bucket-local slot operations:
* `lastSlotOfProg`: resolves the last logical slot `bCount n_max gm b - 1` of a non-empty bucket `b`
  in `O(1)` worst-case memory accesses;
* `pushBackSlotProg`: appends `(q_val, v_val)` at logical slot `bCount n_max gm b` of bucket `b`,
  promoting `K` tail items into a full slab when `r_b + 1 = 2 * K`, with `O(1)` amortized cost
  against `66 * slotPotential n_max gm`;
* `popBackSlotProg`: removes the last logical slot `bCount n_max gm b - 1` of bucket `b`, demoting
  the top full slab into `K` tail items when `r_b' = 0 ∧ 0 < q_b`, with `O(1)` amortized cost
  against `66 * slotPotential n_max gm`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.totalSlots`: total active slots across all
  buckets (`gm 0` in the single-bucket regime, `gm 0 * slabSize n_max + gm 1` in the multi-bucket
  regime).
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.lastSlotOfProg`: `Memory.Prog` operation
  resolving `slotOf n_max gm b (bCount n_max gm b - 1)`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.pushBackSlotProg`: `Memory.Prog` operation
  appending `(q_val, v_val)` to bucket `b` with hysteresis promotion.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.popBackSlotProg`: `Memory.Prog` operation
  removing the last item of bucket `b` with hysteresis demotion.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.slotPotential_pushBack_le`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.slotPotential_popBack_le`: global hysteresis
  potential bounds under `pushBackCounts` and `popBackCounts`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.totalSlots_eq_sum_bCount`: `totalSlots` equals
  the sum of `bCount` across all buckets.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.pushBackSlotProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_pushBackSlotGen`: effect, amortized
  `memoryCost` bound, and `Realizes` certificate for `pushBackSlotProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.popBackSlotProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_popBackSlotGen`: effect, amortized
  `memoryCost` bound, and `Realizes` certificate for `popBackSlotProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Finset

/-! ## Section 1: `totalSlots`, hysteresis potential bounds, and `lastSlotOfProg` -/

/-- Total number of active slots across all buckets in `GlobalMeta`:
* `gm 0` in the single-bucket regime (`bucketBits n_max = 0`);
* `gm 0 * slabSize n_max + gm 1` in the multi-bucket regime (`0 < bucketBits n_max`). -/
@[expose]
def totalSlots (n_max : ℕ) (gm : ℕ → ℕ) : ℕ :=
  if bucketBits n_max = 0 then gm 0
  else gm 0 * slabSize n_max + gm 1

private theorem bucket_eq_zero_of_bits_eq_zero {n_max b : ℕ}
    (hb0 : bucketBits n_max = 0) (hb : b < numBuckets n_max) : b = 0 := by
  simpa [numBuckets, hb0] using hb

private theorem slotStoreInv_single {n_max : ℕ} {gm : ℕ → ℕ}
    (hb0 : bucketBits n_max = 0) (hle : gm 0 ≤ n_max) : SlotStoreInv n_max gm :=
  ⟨fun _ => hle, fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega⟩

private theorem slotStoreInv_multi_of_bucket {n_max b : ℕ} {gm₀ gm₁ : ℕ → ℕ}
    (hb_pos : 0 < bucketBits n_max) (hinv : SlotStoreInv n_max gm₀)
    (htail : TailBijection n_max gm₁ (fun b' => gm₁ (gmRIdx b')) (gm₁ 1))
    (hslab : SlabBijection n_max gm₁ (fun b' => gm₁ (gmQIdx b')) (gm₁ 0))
    (hb_bounds : gm₁ (gmRIdx b) < tailCapPerBucket n_max ∧
      (0 < gm₁ (gmQIdx b) → 1 ≤ gm₁ (gmRIdx b)))
    (hother : ∀ b' < numBuckets n_max, b' ≠ b →
      gm₁ (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm₁ (gmRIdx b') = gm₀ (gmRIdx b'))
    (htot : gm₁ 0 * slabSize n_max + gm₁ 1 ≤ n_max) :
    SlotStoreInv n_max gm₁ := by
  refine ⟨fun _ => by omega, fun _ => htail, fun _ => hslab, fun _ b' hb' => ?_, fun _ => htot⟩
  by_cases hbeq : b' = b
  · exact hbeq ▸ hb_bounds
  · rw [(hother b' hb' hbeq).1, (hother b' hb' hbeq).2]
    exact hinv.multi_r_bounds hb_pos b' hb'

private theorem r_lt_two_slabSize {n_max b : ℕ} {gm : ℕ → ℕ}
    (hb_pos : 0 < bucketBits n_max) (hinv : SlotStoreInv n_max gm)
    (hb : b < numBuckets n_max) : gm (gmRIdx b) < 2 * slabSize n_max := by
  have h := (hinv.multi_r_bounds hb_pos b hb).1
  unfold tailCapPerBucket at h
  rwa [ite_eq_right (by omega)] at h

private theorem readGM_r_result {U V w n_max h_space base b : ℕ}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max) (s : Memory.State) :
    (Memory.spec 0).clientResult s (readGMProg U V w n_max h_space (base, 4 + 3 * b + 1)) =
      gmAt base U V w n_max h_space s.mem (gmRIdx b) :=
  clientResult_readGMProg s (gmRIdx_lt hb_pos hb : 4 + 3 * b + 1 < globalMetaLen n_max)

private theorem readGM_q_result {U V w n_max h_space base b : ℕ}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max) (s : Memory.State) :
    (Memory.spec 0).clientResult s (readGMProg U V w n_max h_space (base, 4 + 3 * b)) =
      gmAt base U V w n_max h_space s.mem (gmQIdx b) :=
  clientResult_readGMProg s (gmQIdx_lt hb_pos hb : 4 + 3 * b < globalMetaLen n_max)

private theorem gmRIdx_fits {U V w₀ n_max h_space w base b : ℕ}
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb_pos : 0 < bucketBits n_max) (hw : 0 < w₀) (hnU : n_max ≤ U) (hU : U < 2 ^ w₀)
    (hb : b < numBuckets n_max) : Fits w (4 + 3 * b + 1) :=
  fits_of_le_globalMetaLen henv hb_pos hw hnU hU (le_of_lt (gmRIdx_lt hb_pos hb))

private theorem lastTailPtrIdx_lt {n_max b : ℕ} {gm : ℕ → ℕ}
    (hb_pos : 0 < bucketBits n_max) (hinv : SlotStoreInv n_max gm)
    (hb : b < numBuckets n_max) :
    gmTailPtrBase n_max + (b * tailCapPerBucket n_max + (gm (gmRIdx b) - 1)) <
      globalMetaLen n_max :=
  gmTailPtrIdx_lt hb_pos hb (Nat.sub_lt_of_lt (hinv.multi_r_bounds hb_pos b hb).1)

private theorem bCount_multi_eq {n_max b : ℕ} {gm : ℕ → ℕ}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max) :
    bCount n_max gm b = gm (gmQIdx b) * slabSize n_max + gm (gmRIdx b) := by
  unfold bCount; simp [Nat.ne_of_gt hb_pos, hb]

private theorem totalSlots_multi_eq {n_max : ℕ} {gm : ℕ → ℕ}
    (hb_pos : 0 < bucketBits n_max) :
    totalSlots n_max gm = gm 0 * slabSize n_max + gm 1 := by
  unfold totalSlots; exact ite_eq_right (Nat.ne_of_gt hb_pos)

theorem totalSlots_of_zero (n_max : ℕ) {gm : ℕ → ℕ} (hzero : ∀ i, gm i = 0) :
    totalSlots n_max gm = 0 := by
  unfold totalSlots
  split_ifs <;> simp [hzero]

theorem totalSlots_le {n_max : ℕ} {gm : ℕ → ℕ} (hinv : SlotStoreInv n_max gm) :
    totalSlots n_max gm ≤ n_max := by
  rcases Nat.eq_zero_or_pos (bucketBits n_max) with hb0 | hb_pos
  · simpa [totalSlots, hb0] using hinv.single_valid hb0
  · simpa [totalSlots_multi_eq hb_pos] using hinv.multi_total_le hb_pos

theorem bCount_le_totalSlots {n_max : ℕ} {gm : ℕ → ℕ} (hinv : SlotStoreInv n_max gm)
    (b : ℕ) (hb : b < numBuckets n_max) :
    bCount n_max gm b ≤ totalSlots n_max gm := by
  rcases Nat.eq_zero_or_pos (bucketBits n_max) with hb0 | hb_pos
  · unfold bCount totalSlots; simp only [hb0, ↓reduceIte]; split_ifs <;> omega
  · rw [bCount_multi_eq hb_pos hb, totalSlots_multi_eq hb_pos]
    stride_omega [q_le_nslabs_of_slabBijection (hinv.multi_slab hb_pos) hb,
      r_le_ntails_of_tailBijection (hinv.multi_tail hb_pos) hb]

theorem pos_gmRIdx_of_pos_bCount {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb_pos : 0 < bucketBits n_max) (hinv : SlotStoreInv n_max gm)
    (hb : b < numBuckets n_max) (hbc : 1 ≤ bCount n_max gm b) :
    1 ≤ gm (gmRIdx b) := by
  rw [bCount_multi_eq hb_pos hb] at hbc
  by_cases hq : 0 < gm (gmQIdx b)
  · exact (hinv.multi_r_bounds hb_pos b hb).2 hq
  · simpa [show gm (gmQIdx b) = 0 by omega] using hbc

private theorem slotPotential_single_bucket_le {n_max b work : ℕ} {gm gm' : ℕ → ℕ}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (hother : ∀ b' < numBuckets n_max, b' ≠ b →
      gm' (gmQIdx b') = gm (gmQIdx b') ∧ gm' (gmRIdx b') = gm (gmRIdx b'))
    (hpt : bucketPotential (slabSize n_max) (gm' (gmQIdx b)) (gm' (gmRIdx b)) + work ≤
      bucketPotential (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b)) + 1) :
    slotPotential n_max gm' + work ≤ slotPotential n_max gm + 1 := by
  unfold slotPotential
  rw [ite_eq_right (Nat.ne_of_gt hb_pos), ite_eq_right (Nat.ne_of_gt hb_pos)]
  have hmem : b ∈ Finset.range (numBuckets n_max) := Finset.mem_range.mpr hb
  rw [← Finset.add_sum_erase _ _ hmem,
    ← Finset.add_sum_erase (Finset.range (numBuckets n_max))
      (fun b' => bucketPotential (slabSize n_max) (gm (gmQIdx b')) (gm (gmRIdx b'))) hmem]
  have hsum_eq := Finset.sum_congr (s₁ := (Finset.range (numBuckets n_max)).erase b) rfl
    (f := fun x => bucketPotential (slabSize n_max) (gm' (gmQIdx x)) (gm' (gmRIdx x)))
    (g := fun x => bucketPotential (slabSize n_max) (gm (gmQIdx x)) (gm (gmRIdx x)))
    fun x hx => by
      obtain ⟨hne, hlt⟩ := Finset.mem_erase.mp hx
      rw [(hother x (Finset.mem_range.mp hlt) hne).1, (hother x (Finset.mem_range.mp hlt) hne).2]
  omega

/-- Global potential bound when bucket `b` transitions according to `pushBackCounts`. -/
theorem slotPotential_pushBack_le {n_max b : ℕ} {gm gm' : ℕ → ℕ}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (hb_upd : gm' (gmQIdx b) = (pushBackCounts (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b))).1 ∧
      gm' (gmRIdx b) = (pushBackCounts (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b))).2)
    (hother : ∀ b' < numBuckets n_max, b' ≠ b →
      gm' (gmQIdx b') = gm (gmQIdx b') ∧ gm' (gmRIdx b') = gm (gmRIdx b')) :
    slotPotential n_max gm' + pushBackWork (slabSize n_max) (gm (gmRIdx b)) ≤
      slotPotential n_max gm + 1 :=
  slotPotential_single_bucket_le hb_pos hb hother <| by
    rw [hb_upd.1, hb_upd.2]
    exact bucketPotential_pushBack_le (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b))

/-- Global potential bound when bucket `b` transitions according to `popBackCounts`. -/
theorem slotPotential_popBack_le {n_max b : ℕ} {gm gm' : ℕ → ℕ}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (hr1 : 1 ≤ gm (gmRIdx b)) (hr2 : gm (gmRIdx b) < 2 * slabSize n_max)
    (hb_upd : gm' (gmQIdx b) = (popBackCounts (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b))).1 ∧
      gm' (gmRIdx b) = (popBackCounts (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b))).2)
    (hother : ∀ b' < numBuckets n_max, b' ≠ b →
      gm' (gmQIdx b') = gm (gmQIdx b') ∧ gm' (gmRIdx b') = gm (gmRIdx b')) :
    slotPotential n_max gm' + popBackWork (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b)) ≤
      slotPotential n_max gm + 1 :=
  slotPotential_single_bucket_le hb_pos hb hother <| by
    rw [hb_upd.1, hb_upd.2]
    exact bucketPotential_popBack_le (slabSize n_max) (gm (gmQIdx b)) (gm (gmRIdx b)) hr1 hr2

private theorem card_range_eq_sum_of_bij {B n : ℕ} {f : ℕ → ℕ}
    (ptr : ℕ → ℕ → ℕ) (invB invR : ℕ → ℕ)
    (hptr_lt : ∀ b < B, ∀ r < f b, ptr b r < n)
    (hleft : ∀ b < B, ∀ r < f b, invB (ptr b r) = b ∧ invR (ptr b r) = r)
    (hright : ∀ p < n, invB p < B ∧ invR p < f (invB p) ∧ ptr (invB p) (invR p) = p) :
    n = ∑ b ∈ Finset.range B, f b := by
  have hcard := Finset.card_bij (s := (Finset.range B).sigma fun b => Finset.range (f b))
    (t := Finset.range n) (fun x _ => ptr x.1 x.2)
    (fun x hx => by
      simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
      exact hptr_lt x.1 hx.1 x.2 hx.2)
    (fun x₁ hx₁ x₂ hx₂ heq => by
      simp only [Finset.mem_sigma, Finset.mem_range] at hx₁ hx₂
      have h1 := hleft x₁.1 hx₁.1 x₁.2 hx₁.2
      have h2 := hleft x₂.1 hx₂.1 x₂.2 hx₂.2
      ext
      · exact h1.1.symm.trans (heq ▸ h2.1)
      · exact heq_of_eq (h1.2.symm.trans (heq ▸ h2.2)))
    (fun p hp =>
      let ⟨hb, hr, heq⟩ := hright p (Finset.mem_range.mp hp)
      ⟨⟨invB p, invR p⟩,
        Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hb, Finset.mem_range.mpr hr⟩, heq⟩)
  simpa [Finset.card_sigma] using hcard.symm

/-- Under `SlabBijection`, `n_slabs` equals the sum of per-bucket slab counts `q_fn b`. -/
theorem nslabs_eq_sum {n_max : ℕ} {gm : ℕ → ℕ} {q_fn : ℕ → ℕ} {n_slabs : ℕ}
    (hslab : SlabBijection n_max gm q_fn n_slabs) :
    n_slabs = ∑ b ∈ Finset.range (numBuckets n_max), q_fn b :=
  card_range_eq_sum_of_bij (slabPtrOf n_max gm)
    (fun p => gm (gmSlabOwnerBIdx n_max p)) (fun p => gm (gmSlabOwnerSIdx n_max p))
    hslab.ptr_lt
    (fun b hb s hs => ⟨hslab.ownerB_ptr b hb s hs, hslab.ownerS_ptr b hb s hs⟩)
    hslab.owner_valid

/-- Under `TailBijection`, `n_tails` equals the sum of per-bucket tail counts `r_fn b`. -/
theorem ntails_eq_sum {n_max : ℕ} {gm : ℕ → ℕ} {r_fn : ℕ → ℕ} {n_tails : ℕ}
    (htail : TailBijection n_max gm r_fn n_tails) :
    n_tails = ∑ b ∈ Finset.range (numBuckets n_max), r_fn b :=
  card_range_eq_sum_of_bij (fun b r => gm (gmTailPtrIdx n_max b r))
    (fun t => gm (gmTailOwnerIdx n_max t) / tailCapPerBucket n_max)
    (fun t => gm (gmTailOwnerIdx n_max t) % tailCapPerBucket n_max)
    htail.ptr_lt
    (fun b hb r hr => by
      rw [htail.owner_ptr b hb r hr]
      exact mul_add_div_mod_of_lt (lt_of_lt_of_le hr (htail.r_le b hb)))
    (fun t ht => by
      obtain ⟨hb, hr, hptr⟩ := htail.owner_valid t ht
      refine ⟨hb, hr, ?_⟩
      dsimp only [gmTailPtrIdx]
      rwa [Nat.div_add_mod' (gm (gmTailOwnerIdx n_max t)) (tailCapPerBucket n_max)])

/-- In the multi-bucket regime (`0 < bucketBits n_max`), the total active slot count
`gm 0 * slabSize n_max + gm 1` equals the sum of per-bucket item counts `bCount n_max gm b`. -/
theorem total_eq_sum_bCount {n_max : ℕ} {gm : ℕ → ℕ}
    (hb_pos : 0 < bucketBits n_max)
    (htail : TailBijection n_max gm (fun b => gm (gmRIdx b)) (gm 1))
    (hslab : SlabBijection n_max gm (fun b => gm (gmQIdx b)) (gm 0)) :
    gm 0 * slabSize n_max + gm 1 =
      ∑ b ∈ Finset.range (numBuckets n_max), bCount n_max gm b := by
  rw [nslabs_eq_sum hslab, ntails_eq_sum htail, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b hb =>
    (bCount_multi_eq hb_pos (Finset.mem_range.mp hb)).symm

/-- Under `SlotStoreInv n_max gm`, `totalSlots n_max gm` equals the sum of `bCount n_max gm b`
over all buckets `b < numBuckets n_max`. -/
theorem totalSlots_eq_sum_bCount {n_max : ℕ} {gm : ℕ → ℕ}
    (hinv : SlotStoreInv n_max gm) :
    totalSlots n_max gm =
      ∑ b ∈ Finset.range (numBuckets n_max), bCount n_max gm b := by
  rcases Nat.eq_zero_or_pos (bucketBits n_max) with hb0 | hb_pos
  · have hB1 : numBuckets n_max = 1 := by simp [numBuckets, hb0]
    simp [totalSlots, hb0, hB1, bCount]
  · rw [totalSlots_multi_eq hb_pos]
    exact total_eq_sum_bCount hb_pos (hinv.multi_tail hb_pos) (hinv.multi_slab hb_pos)

/-- `promoteSlabProg` preserves `gm 0 * slabSize n_max + gm 1`. -/
theorem promoteSlabProg_tot_eq {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (s : Memory.State)
    (hpre : PromoteSlabInv U V w n_max h_space base b s) :
    gmAt base U V w n_max h_space
        ((Memory.spec 0).clientState s (promoteSlabProg U V w n_max h_space (base, b))).mem 0 *
        slabSize n_max +
      gmAt base U V w n_max h_space
        ((Memory.spec 0).clientState s (promoteSlabProg U V w n_max h_space (base, b))).mem 1 =
      gmAt base U V w n_max h_space s.mem 0 * slabSize n_max +
        gmAt base U V w n_max h_space s.mem 1 := by
  obtain ⟨_, _, _, hinv', _, _, _, hbc, _, _⟩ := promoteSlabProg_effect hw hb_pos s hpre
  rw [total_eq_sum_bCount hb_pos (hinv'.multi_tail hb_pos) (hinv'.multi_slab hb_pos),
    total_eq_sum_bCount hb_pos hpre.2.1 hpre.2.2.1]
  exact Finset.sum_congr rfl fun b' hb' => hbc b' (Finset.mem_range.mp hb')

/-- `demoteSlabProg` preserves `gm 0 * slabSize n_max + gm 1`. -/
theorem demoteSlabProg_tot_eq {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (s : Memory.State)
    (hpre : DemoteSlabInv U V w n_max h_space base b s) :
    gmAt base U V w n_max h_space
        ((Memory.spec 0).clientState s (demoteSlabProg U V w n_max h_space (base, b))).mem 0 *
        slabSize n_max +
      gmAt base U V w n_max h_space
        ((Memory.spec 0).clientState s (demoteSlabProg U V w n_max h_space (base, b))).mem 1 =
      gmAt base U V w n_max h_space s.mem 0 * slabSize n_max +
        gmAt base U V w n_max h_space s.mem 1 := by
  obtain ⟨_, _, _, hinv', _, _, _, hbc, _, _⟩ := demoteSlabProg_effect hw hb_pos s hpre
  rw [total_eq_sum_bCount hb_pos (hinv'.multi_tail hb_pos) (hinv'.multi_slab hb_pos),
    total_eq_sum_bCount hb_pos hpre.2.1 hpre.2.2.1]
  exact Finset.sum_congr rfl fun b' hb' => hbc b' (Finset.mem_range.mp hb')

/-- Parameter-free `Memory.Prog` operation resolving the physical slot
`slotOf n_max gm b (bCount n_max gm b - 1)` of the last item in a non-empty bucket `b = d.2.2`
at `base = d.2.1` (`1 ≤ bCount n_max gm b`). -/
@[expose]
def lastSlotOfGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog ℕ :=
  if dpBucketBits d.1 = 0 then do
    let c ← readGMGenProg (d.1, (d.2.1, 0))
    pure (c - 1)
  else do
    let r_b ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2 + 1))
    let t_last ← readGMGenProg
      (d.1, (d.2.1, dpGmTailPtrBase d.1 + (d.2.2 * dpTailCap d.1 + (r_b - 1))))
    pure (dpNMaxSubOne d.1 - t_last)

/-- `Memory.Prog` operation resolving the physical slot `slotOf n_max gm b (bCount n_max gm b - 1)`
of the last item in a non-empty bucket `b = d.2` at `base = d.1` (`1 ≤ bCount n_max gm b`). -/
@[expose]
def lastSlotOfProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ :=
  lastSlotOfGenProg (mkDictParams U V w n_max h_space, d)

@[simp] theorem lastSlotOfGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    lastSlotOfGenProg (mkDictParams U V w n_max h_space, d) =
      lastSlotOfProg U V w n_max h_space d := by
  rfl

/-- Parameter-free precondition for `lastSlotOfGenProg`. -/
@[expose]
def LastSlotOfGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let gm := gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  DictEnvGen w d.1 d.2.1 ∧
  SlotStoreInv (dpNMax d.1) gm ∧
  d.2.2 < numBuckets (dpNMax d.1) ∧
  1 ≤ bCount (dpNMax d.1) gm d.2.2

@[simp] theorem lastSlotOfGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    LastSlotOfGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      (DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1 ∧
        SlotStoreInv n_max (gmAt d.1 U V w₀ n_max h_space s.mem) ∧
        d.2 < numBuckets n_max ∧
        1 ≤ bCount n_max (gmAt d.1 U V w₀ n_max h_space s.mem) d.2) := Iff.rfl

/-- Specialize a packed bucket guard together with its decision instance. -/
theorem ite_bucketBits_mk {α : Sort*} (U V w n_max h_space : ℕ) (t e : α) :
    (if dpBucketBits (mkDictParams U V w n_max h_space) = 0 then t else e) =
      (if bucketBits n_max = 0 then t else e) := rfl

theorem clientState_lastSlotOfProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (lastSlotOfProg U V w n_max h_space d) = s := by
  simp only [lastSlotOfProg, lastSlotOfGenProg, ite_bucketBits_mk, readGMGenProg_mk,
    p_gmTailPtrBase_mk, p_tailCap_mk, p_nMaxSubOne_mk]
  split_ifs <;> rfl

theorem memoryCost_lastSlotOfProg_le (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (lastSlotOfProg U V w n_max h_space d) s ≤ 4 := by
  simp only [lastSlotOfProg, lastSlotOfGenProg, ite_bucketBits_mk, readGMGenProg_mk,
    p_gmTailPtrBase_mk, p_tailCap_mk, p_nMaxSubOne_mk]
  split_ifs <;> exact Nat.le_of_ble_eq_true rfl

theorem clientResult_lastSlotOfProg {U V w n_max h_space : ℕ} (d : ℕ × ℕ) (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt d.1 U V w n_max h_space s.mem))
    (hb : d.2 < numBuckets n_max)
    (hbc : 1 ≤ bCount n_max (gmAt d.1 U V w n_max h_space s.mem) d.2) :
    (Memory.spec 0).clientResult s (lastSlotOfProg U V w n_max h_space d) =
      slotOf n_max (gmAt d.1 U V w n_max h_space s.mem) d.2
        (bCount n_max (gmAt d.1 U V w n_max h_space s.mem) d.2 - 1) := by
  let gm := gmAt d.1 U V w n_max h_space s.mem
  simp only [lastSlotOfProg, lastSlotOfGenProg, ite_bucketBits_mk, readGMGenProg_mk,
    p_gmTailPtrBase_mk, p_tailCap_mk, p_nMaxSubOne_mk]
  rcases Nat.eq_zero_or_pos (bucketBits n_max) with hb0 | hb_pos
  · simp only [hb0, ↓reduceIte, StateTransitionSpec.clientResult_bind,
      clientResult_readGMProg s (by wram_omega : 0 < globalMetaLen n_max)]
    unfold slotOf bCount
    simp only [hb0, ↓reduceIte, bucket_eq_zero_of_bits_eq_zero hb0 hb]
    rfl
  · have hr_pos := pos_gmRIdx_of_pos_bCount hb_pos hinv hb hbc
    have hnot_zero : bucketBits n_max ≠ 0 := Nat.ne_of_gt hb_pos
    simp only [hnot_zero, ↓reduceIte]
    rw [StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      readGM_r_result hb_pos hb s,
      StateTransitionSpec.clientResult_bind, clientState_readGMProg,
      clientResult_readGMProg s (lastTailPtrIdx_lt hb_pos hinv hb), bCount_multi_eq hb_pos hb]
    unfold slotOf
    have hsub : gm (gmQIdx d.2) * slabSize n_max + gm (gmRIdx d.2) - 1 -
        gm (gmQIdx d.2) * slabSize n_max = gm (gmRIdx d.2) - 1 := by omega
    rw [ite_eq_right hnot_zero, ite_eq_right (by omega), hsub]
    rfl

private theorem single_gm0_pos_of_bCount {U V w₀ n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hb0 : bucketBits n_max = 0) (hb : d.2 < numBuckets n_max)
    (hbc : 1 ≤ bCount n_max (gmAt d.1 U V w₀ n_max h_space s.mem) d.2) :
    1 ≤ (Memory.spec 0).clientResult s (readGMProg U V w₀ n_max h_space (d.1, 0)) := by
  rw [clientResult_readGMProg _ (by wram_omega : 0 < globalMetaLen n_max)]
  have hd2 := bucket_eq_zero_of_bits_eq_zero hb0 hb
  unfold bCount at hbc; simpa only [hb0, ↓reduceIte, hd2] using hbc

theorem realizes_lastSlotOfGen :
    Realizes .exact lastSlotOfGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      LastSlotOfGenPre
      (fun _ _ => 0) := by
  realizeDictWith [lastSlotOfGenPre_mk] using [realizes_readGMGen]
  · exact h.1
  · wram_omega
  · exact single_gm0_pos_of_bCount hc h.2.2.1 h.2.2.2
  · exact gmRIdx_fits h.1 (Nat.pos_of_ne_zero hc) hw hnU hU h.2.2.1
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact gmRIdx_lt (Nat.pos_of_ne_zero hc) h.2.2.1
  · rw [readGM_r_result (Nat.pos_of_ne_zero hc) h.2.2.1 s]
    exact pos_gmRIdx_of_pos_bCount (Nat.pos_of_ne_zero hc) h.2.1 h.2.2.1 h.2.2.2
  · rw [readGM_r_result (Nat.pos_of_ne_zero hc) h.2.2.1 s]
    exact fits_of_le_globalMetaLen h.1 (Nat.pos_of_ne_zero hc) hw hnU hU
      (le_of_lt (lastTailPtrIdx_lt (Nat.pos_of_ne_zero hc) h.2.1 h.2.2.1))
  · rw [readGM_r_result (Nat.pos_of_ne_zero hc) h.2.2.1 s]
    exact lastTailPtrIdx_lt (Nat.pos_of_ne_zero hc) h.2.1 h.2.2.1
  · have hb_pos := Nat.pos_of_ne_zero hc
    have hr_pos := pos_gmRIdx_of_pos_bCount hb_pos h.2.1 h.2.2.1 h.2.2.2
    rw [clientState_readGMProg, readGM_r_result hb_pos h.2.2.1 s,
      clientResult_readGMProg s (lastTailPtrIdx_lt hb_pos h.2.1 h.2.2.1)]
    have ht_lt := (h.2.1.multi_tail hb_pos).ptr_lt d.2 h.2.2.1
      (gmAt d.1 U V w₀ n_max h_space s.mem (gmRIdx d.2) - 1) (by omega)
    have htot := h.2.1.multi_total_le hb_pos
    wram_omega [ht_lt]

/-! ## Section 2: `pushBackSlotProg` via `realize` -/

/-- Parameter-free helper `Memory.Prog` for the multi-bucket prefix of `pushBackSlotGenProg`. -/
@[expose]
def pushBackTailWriteGenProg (d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ) : Memory.Prog ℕ := do
  let dp := d.1.1.1
  let base := d.1.1.2.1
  let b := d.1.1.2.2
  let q_val := d.1.2
  let v_val := d.2
  let t_new ← appendTailItemGenProg (dp, (base, b))
  let g_new := dpNMaxSubOne dp - t_new
  writeQuotGenProg (dp, ((base, g_new), q_val))
  writeValGenProg (dp, ((base, g_new), v_val))
  readGMGenProg (dp, (base, 4 + 3 * b + 1))

/-- Helper `Memory.Prog` for the multi-bucket prefix of `pushBackSlotProg`: appends one tail item
to bucket `b = d.1.1.2` at `base = d.1.1.1`, writes `(q_val, v_val) = (d.1.2, d.2)` into its
physical slot, and returns the updated tail count `r_b_new = gm' (gmRIdx b)`. -/
@[expose]
def pushBackTailWriteProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog ℕ :=
  pushBackTailWriteGenProg (((mkDictParams U V w n_max h_space, d.1.1), d.1.2), d.2)

@[simp] theorem pushBackTailWriteGenProg_mk (U V w n_max h_space : ℕ)
    (d1 : ℕ × ℕ) (d2 d3 : ℕ) :
    pushBackTailWriteGenProg (((mkDictParams U V w n_max h_space, d1), d2), d3) =
      pushBackTailWriteProg U V w n_max h_space ((d1, d2), d3) := by
  rfl

@[simp]
theorem memoryCost_pushBackTailWriteProg (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (pushBackTailWriteProg U V w n_max h_space d) s = 30 := by
  simp [pushBackTailWriteProg, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    pushBackTailWriteGenProg, p_nMaxSubOne_mk, appendTailItemGenProg_mk, writeQuotGenProg_mk,
    writeValGenProg_mk, readGMGenProg_mk]

private theorem slotOf_ne_freshTail {n_max : ℕ} {gm : ℕ → ℕ}
    (hb_pos : 0 < bucketBits n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (htot : gm 0 * slabSize n_max + gm 1 < n_max)
    {b' j : ℕ} (hb' : b' < numBuckets n_max) (hj : j < bCount n_max gm b') :
    slotOf n_max gm b' j ≠ n_max - 1 - gm 1 := by
  rw [bCount_multi_eq hb_pos hb'] at hj
  unfold slotOf; rw [ite_eq_right (Nat.ne_of_gt hb_pos)]
  split_ifs with hj_slab
  · have hp_lt := hslab.ptr_lt b' hb' (j / slabSize n_max) (by stride_omega [slabSize_pos n_max])
    stride_omega [slabSize_pos n_max]
  · have ht'_lt := htail.ptr_lt b' hb' (j - gm (gmQIdx b') * slabSize n_max) (by omega)
    omega

/-- Pure state effect and return value of `pushBackTailWriteProg`. -/
theorem pushBackTailWriteProg_effect {U V w n_max h_space base b q_val v_val : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max)
    (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space s.mem))
    (hb : b < numBuckets n_max)
    (htot : totalSlots n_max (gmAt base U V w n_max h_space s.mem) < n_max)
    (hq_lt : q_val < 2 ^ quotientBits U n_max)
    (hv_lt : v_val < 2 ^ valBits V) :
    let gm₀ := gmAt base U V w n_max h_space s.mem
    let d := (((base, b), q_val), v_val)
    let s₁ := (Memory.spec 0).clientState s (pushBackTailWriteProg U V w n_max h_space d)
    let gm₁ := gmAt base U V w n_max h_space s₁.mem
    (Memory.spec 0).clientResult s (pushBackTailWriteProg U V w n_max h_space d) =
      gm₀ (gmRIdx b) + 1 ∧
    s₁.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s₁.mem a = s.mem a) ∧
    lmAt base U V w n_max h_space s₁.mem = lmAt base U V w n_max h_space s.mem ∧
    gm₁ = gmAppendTail n_max gm₀ b ∧
    TailBijection n_max gm₁ (fun b' => gm₁ (gmRIdx b')) (gm₁ 1) ∧
    SlabBijection n_max gm₁ (fun b' => gm₁ (gmQIdx b')) (gm₁ 0) ∧
    gm₁ 0 * slabSize n_max + gm₁ 1 = gm₀ 0 * slabSize n_max + gm₀ 1 + 1 ∧
    gm₁ (gmQIdx b) = gm₀ (gmQIdx b) ∧
    gm₁ (gmRIdx b) = gm₀ (gmRIdx b) + 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b →
      gm₁ (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm₁ (gmRIdx b') = gm₀ (gmRIdx b')) ∧
    bCount n_max gm₁ b = bCount n_max gm₀ b + 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm₁ b' = bCount n_max gm₀ b') ∧
    quotAt base U w n_max h_space s₁.mem (slotOf n_max gm₁ b (bCount n_max gm₀ b)) = q_val ∧
    valAt base U V w n_max h_space s₁.mem (slotOf n_max gm₁ b (bCount n_max gm₀ b)) = v_val ∧
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm₀ b',
      quotAt base U w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) =
        quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
      valAt base U V w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) =
        valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j)) := by
  intro gm₀ d s₁ gm₁
  rw [totalSlots_multi_eq hb_pos] at htot
  have htail₀ := hinv.multi_tail hb_pos
  have hslab₀ := hinv.multi_slab hb_pos
  have hr_lt := (hinv.multi_r_bounds hb_pos b hb).1
  have ht_lt := ntails_lt_maxTailItems_of_r_lt hb hr_lt htail₀
  obtain ⟨hres_app, hf_app, hout_app, hq_app, hv_app, hl_app, hgm_app⟩ :=
    appendTailItemProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hb s htail₀ hr_lt
  let s_app := (Memory.spec 0).clientState s (appendTailItemProg U V w n_max h_space (base, b))
  let g_new := (n_max - 1) - gm₀ 1
  obtain ⟨hf_wq, hout_wq, hq_wq, hv_wq, hl_wq, hgm_wq⟩ :=
    writeQuotProg_effect (base := base) (V := V) (h_space := h_space) hw (by omega : g_new < n_max)
      hq_lt s_app
  let s_wq := (Memory.spec 0).clientState s_app
    (writeQuotProg U w n_max h_space ((base, g_new), q_val))
  obtain ⟨hf_wv, hout_wv, hq_wv, hv_wv, hl_wv, hgm_wv⟩ :=
    writeValProg_effect (base := base) (h_space := h_space) hw (by omega : g_new < n_max)
      hv_lt s_wq
  let s_wv := (Memory.spec 0).clientState s_wq
    (writeValProg U V w n_max h_space ((base, g_new), v_val))
  have hst : s₁ = s_wv := by
    simp only [s₁, pushBackTailWriteProg, pushBackTailWriteGenProg, p_nMaxSubOne_mk,
      appendTailItemGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk, readGMGenProg_mk, d]
    rw [StateTransitionSpec.clientState_bind, hres_app,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_readGMProg]
  have hgm1_eq : gm₁ = gmAppendTail n_max gm₀ b := by
    dsimp only [gm₁]; rw [hst, hgm_wv, hgm_wq, hgm_app]
  rcases gmAppendTail_preserves_nonTail gm₀ hb hr_lt ht_lt with
    ⟨hp0, hp1, hpR, hpOther, hpQ, -⟩
  have hres : (Memory.spec 0).clientResult s (pushBackTailWriteProg U V w n_max h_space d) =
      gm₀ (gmRIdx b) + 1 := by
    simp only [pushBackTailWriteProg, pushBackTailWriteGenProg, p_nMaxSubOne_mk,
      appendTailItemGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk, readGMGenProg_mk, d]
    rw [StateTransitionSpec.clientResult_bind, hres_app,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      readGM_r_result hb_pos hb s_wv, ← hst]
    exact congrFun hgm1_eq (gmRIdx b) |>.trans hpR
  have hslot_app := slotOf_gmAppendTail hb_pos hb hr_lt ht_lt htail₀ hslab₀
  have hslot_new : slotOf n_max gm₁ b (bCount n_max gm₀ b) = g_new := by
    rw [hgm1_eq, bCount_multi_eq hb_pos hb, hslot_app.1]
  refine ⟨hres, by rw [hst, hf_wv, hf_wq, hf_app],
    fun a ha => by
      rw [hst, hout_wv a (by wram_omega [ha]), hout_wq a (by wram_omega [ha]),
        hout_app a (by wram_omega [ha])],
    by rw [hst, hl_wv, hl_wq, hl_app],
    hgm1_eq,
    hgm1_eq ▸ tailBijection_gmAppendTail hb hr_lt ht_lt htail₀,
    hgm1_eq ▸ (slabBijection_gmAppendTail hb hr_lt ht_lt hslab₀).2,
    by rw [hgm1_eq, hp0, hp1]; omega,
    by rw [hgm1_eq, hpQ b hb],
    by rw [hgm1_eq, hpR],
    fun b' hb' hne => ⟨by rw [hgm1_eq, hpQ b' hb'], by rw [hgm1_eq, hpOther b' hb' hne]⟩,
    by rw [bCount_multi_eq hb_pos hb, bCount_multi_eq hb_pos hb, hgm1_eq, hpQ b hb, hpR]; omega,
    fun b' hb' hne => by
      rw [bCount_multi_eq hb_pos hb', bCount_multi_eq hb_pos hb', hgm1_eq, hpQ b' hb',
        hpOther b' hb' hne],
    by rw [hst, hq_wv, hq_wq, hslot_new]; update_simp,
    by rw [hst, hv_wv, hslot_new]; update_simp,
    fun b' hb' j hj => ?_⟩
  have hne := slotOf_ne_freshTail hb_pos htail₀ hslab₀ htot hb' hj
  exact ⟨by rw [hst, hq_wv, hq_wq, hq_app, hgm1_eq, hslot_app.2 b' hb' j hj]; update_simp,
    by rw [hst, hv_wv, hv_wq, hv_app, hgm1_eq, hslot_app.2 b' hb' j hj]; update_simp⟩

/-- Precondition for `pushBackSlotProg` in `Realizes`. -/
@[expose]
def PushBackSlotPre (U V w₀ n_max h_space w : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ)
    (s : Memory.State) : Prop :=
  let base := d.1.1.1
  let b := d.1.1.2
  let q_val := d.1.2
  let v_val := d.2
  let gm := gmAt base U V w₀ n_max h_space s.mem
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  SlotStoreInv n_max gm ∧
  b < numBuckets n_max ∧
  totalSlots n_max gm < n_max ∧
  q_val < 2 ^ quotientBits U n_max ∧
  v_val < 2 ^ valBits V

/-- Parameter-free precondition for `pushBackSlotGenProg`. -/
@[expose]
def PushBackSlotGenPre (w : ℕ) (d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ)
    (s : Memory.State) : Prop :=
  let dp := d.1.1.1
  let base := d.1.1.2.1
  let b := d.1.1.2.2
  let q_val := d.1.2
  let v_val := d.2
  let gm := gmAt base (dpU dp) (dpV dp) (dpW dp) (dpNMax dp) (dpHSpace dp) s.mem
  DictEnvGen w dp base ∧
  SlotStoreInv (dpNMax dp) gm ∧
  b < numBuckets (dpNMax dp) ∧
  totalSlots (dpNMax dp) gm < dpNMax dp ∧
  q_val < 2 ^ quotientBits (dpU dp) (dpNMax dp) ∧
  v_val < 2 ^ valBits (dpV dp)

@[simp] theorem pushBackSlotGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d1 : ℕ × ℕ) (d2 d3 : ℕ) (s : Memory.State) :
    PushBackSlotGenPre w (((mkDictParams U V w₀ n_max h_space, d1), d2), d3) s ↔
      PushBackSlotPre U V w₀ n_max h_space w ((d1, d2), d3) s := Iff.rfl

/-- Parameter-free precondition for `pushBackTailWriteGenProg`. -/
@[expose]
def PushBackTailWriteGenPre (w : ℕ) (d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ)
    (s : Memory.State) : Prop :=
  PushBackSlotGenPre w d s ∧ 0 < bucketBits (dpNMax d.1.1.1)

@[simp] theorem pushBackTailWriteGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d1 : ℕ × ℕ) (d2 d3 : ℕ) (s : Memory.State) :
    PushBackTailWriteGenPre w (((mkDictParams U V w₀ n_max h_space, d1), d2), d3) s ↔
      (PushBackSlotPre U V w₀ n_max h_space w ((d1, d2), d3) s ∧ 0 < bucketBits n_max) := Iff.rfl

private theorem appendTailItem_lt_n_max {U V w₀ n_max h_space w : ℕ}
    (hw : 0 < w₀) (hb_pos : 0 < bucketBits n_max)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State)
    (h : PushBackSlotPre U V w₀ n_max h_space w d s) :
    (Memory.spec 0).clientResult s (appendTailItemProg U V w₀ n_max h_space d.1.1) < n_max := by
  have hres := (appendTailItemProg_effect hw hb_pos h.2.2.1 s (h.2.1.multi_tail hb_pos)
    (h.2.1.multi_r_bounds hb_pos d.1.1.2 h.2.2.1).1).1
  have htot := h.2.2.2.1
  rw [totalSlots_multi_eq hb_pos] at htot
  rcases d with ⟨⟨⟨base, b⟩, q_val⟩, v_val⟩
  dsimp only at hres htot ⊢; omega

theorem realizes_pushBackTailWriteGen :
    Realizes .exact pushBackTailWriteGenProg
      (WordEncoding.encode (α := ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      PushBackTailWriteGenPre
      (fun _ _ => 0) := by
  realize
    [realizes_appendTailItemGen, realizes_writeQuotGen, realizes_writeValGen,
      realizes_readGMGen]
  all_goals (
    rcases d with ⟨⟨⟨dp, base, b⟩, q_val⟩, v_val⟩
    let d : ((ℕ × ℕ) × ℕ) × ℕ := (((base, b), q_val), v_val)
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1.1
    simpDictParamsWith [pushBackTailWriteGenPre_mk, pushBackSlotGenPre_mk,
      appendTailItemGenPre_mk, appendTailItemGenProg_mk]
    dsimp only [d, PushBackSlotPre] at *
  )
  · exact ⟨h.1.1, h.1.2.1.multi_tail h.2, h.1.2.2.1,
      (h.1.2.1.multi_r_bounds h.2 d.1.1.2 h.1.2.2.1).1, h.2⟩
  · have hlt := appendTailItem_lt_n_max hw h.2 d s h.1; dsimp only [d] at hlt; omega
  · exact h.1.1
  · have hlt := appendTailItem_lt_n_max hw h.2 d s h.1; dsimp only [d] at hlt; omega
  · exact gmRIdx_fits h.1.1 h.2 hw hnU hU h.1.2.2.1
  · refine fits_of_le_globalMetaLen h.1.1 h.2 hw hnU hU ?_
    have := gmRIdx_lt h.2 h.1.2.2.1; wram_omega [this]
  · exact gmRIdx_lt h.2 h.1.2.2.1

/-- Parameter-free `Memory.Prog` operation appending `(q_val, v_val) = (d.1.2, d.2)` at logical
slot `bCount n_max gm b` of bucket `b = d.1.1.2.2` at `base = d.1.1.2.1`. -/
@[expose]
def pushBackSlotGenProg (d : ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ) : Memory.Prog Unit :=
  if dpBucketBits d.1.1.1 = 0 then do
    let dp := d.1.1.1
    let base := d.1.1.2.1
    let q_val := d.1.2
    let v_val := d.2
    let c ← readGMGenProg (dp, (base, 0))
    writeQuotGenProg (dp, ((base, c), q_val))
    writeValGenProg (dp, ((base, c), v_val))
    writeGMGenProg (dp, ((base, 0), c + 1))
  else do
    let r_b_new ← pushBackTailWriteGenProg d
    if r_b_new = dpTwoSlabSize d.1.1.1 then
      promoteSlabGenProg d.1.1
    else
      pure ()

/-- `Memory.Prog` operation appending `(q_val, v_val) = (d.1.2, d.2)` at logical slot
`bCount n_max gm b` of bucket `b = d.1.1.2` at `base = d.1.1.1`, promoting `K` tail items into a
new full slab when `r_b + 1 = 2 * K`. -/
@[expose]
def pushBackSlotProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog Unit :=
  pushBackSlotGenProg (((mkDictParams U V w n_max h_space, d.1.1), d.1.2), d.2)

@[simp] theorem pushBackSlotGenProg_mk (U V w n_max h_space : ℕ)
    (d1 : ℕ × ℕ) (d2 d3 : ℕ) :
    pushBackSlotGenProg (((mkDictParams U V w n_max h_space, d1), d2), d3) =
      pushBackSlotProg U V w n_max h_space ((d1, d2), d3) := by
  rfl

-- Readback and state equations keep packed writes out of execution normalization.
private theorem pushBackSlotProg_execution {U V w n_max h_space base b q_val v_val : ℕ}
    (s s₁ : Memory.State) (hb0 : bucketBits n_max ≠ 0)
    (hs1 : (Memory.spec 0).clientState s
      (pushBackTailWriteProg U V w n_max h_space (((base, b), q_val), v_val)) = s₁)
    (r : ℕ)
    (hres : (Memory.spec 0).clientResult s
      (pushBackTailWriteProg U V w n_max h_space (((base, b), q_val), v_val)) = r) :
    (Memory.spec 0).clientState s
      (pushBackSlotProg U V w n_max h_space (((base, b), q_val), v_val)) =
      (if r = 2 * slabSize n_max then
        (Memory.spec 0).clientState s₁ (promoteSlabProg U V w n_max h_space (base, b))
      else s₁) ∧
    memoryCost (pushBackSlotProg U V w n_max h_space (((base, b), q_val), v_val)) s =
      30 + (if r = 2 * slabSize n_max then
        memoryCost (promoteSlabProg U V w n_max h_space (base, b)) s₁ else 0) := by
  simp only [pushBackSlotProg, pushBackSlotGenProg, ite_bucketBits_mk, p_twoSlabSize_mk,
    readGMGenProg_mk, writeQuotGenProg_mk, writeValGenProg_mk, writeGMGenProg_mk,
    pushBackTailWriteGenProg_mk, promoteSlabGenProg_mk, hb0, ↓reduceIte]
  constructor
  · rw [StateTransitionSpec.clientState_bind, hs1, hres]; split_ifs <;> rfl
  · rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pushBackTailWriteProg,
      hs1, hres]; split_ifs <;> rfl

private theorem promoteSlabInv_of_other_and_tail {U V w n_max h_space base b : ℕ}
    {s₀ s₁ : Memory.State} (hb_pos : 0 < bucketBits n_max)
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space s₀.mem))
    (hb : b < numBuckets n_max)
    (htail1 : TailBijection n_max (gmAt base U V w n_max h_space s₁.mem)
      (fun b' => gmAt base U V w n_max h_space s₁.mem (gmRIdx b'))
      (gmAt base U V w n_max h_space s₁.mem 1))
    (hslab1 : SlabBijection n_max (gmAt base U V w n_max h_space s₁.mem)
      (fun b' => gmAt base U V w n_max h_space s₁.mem (gmQIdx b'))
      (gmAt base U V w n_max h_space s₁.mem 0))
    (hrb1 : gmAt base U V w n_max h_space s₁.mem (gmRIdx b) = 2 * slabSize n_max)
    (hother : ∀ b' < numBuckets n_max, b' ≠ b →
      gmAt base U V w n_max h_space s₁.mem (gmQIdx b') =
        gmAt base U V w n_max h_space s₀.mem (gmQIdx b') ∧
      gmAt base U V w n_max h_space s₁.mem (gmRIdx b') =
        gmAt base U V w n_max h_space s₀.mem (gmRIdx b'))
    (htot1 : gmAt base U V w n_max h_space s₁.mem 0 * slabSize n_max +
      gmAt base U V w n_max h_space s₁.mem 1 ≤ n_max) :
    PromoteSlabInv U V w n_max h_space base b s₁ :=
  ⟨hb, htail1, hslab1, hrb1, fun b' hb' hne => by
    rw [(hother b' hb' hne).1, (hother b' hb' hne).2]
    exact hinv.multi_r_bounds hb_pos b' hb', htot1⟩

private abbrev PushBackSlotPost (U V w n_max h_space base b q_val v_val : ℕ)
    (s s' : Memory.State) : Prop :=
  let gm₀ := gmAt base U V w n_max h_space s.mem
  let gm' := gmAt base U V w n_max h_space s'.mem
  s'.frontier = s.frontier ∧
  (∀ a, ¬(base + offQuot h_space ≤ a ∧
      a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
  lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
  SlotStoreInv n_max gm' ∧
  totalSlots n_max gm' = totalSlots n_max gm₀ + 1 ∧
  bCount n_max gm' b = bCount n_max gm₀ b + 1 ∧
  (∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm' b' = bCount n_max gm₀ b') ∧
  quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b (bCount n_max gm₀ b)) = q_val ∧
  valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b (bCount n_max gm₀ b)) = v_val ∧
  (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm₀ b',
    quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b' j) =
      quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
    valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b' j) =
      valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j)) ∧
  memoryCost (pushBackSlotProg U V w n_max h_space (((base, b), q_val), v_val)) s +
      66 * slotPotential n_max gm' ≤
    66 * slotPotential n_max gm₀ + 134

private theorem pushBackSlotProg_effect_single {U V w n_max h_space base b q_val v_val : ℕ}
    (hw : 0 < w) (hb0 : bucketBits n_max = 0) (s : Memory.State)
    (hb : b < numBuckets n_max)
    (htot : totalSlots n_max (gmAt base U V w n_max h_space s.mem) < n_max)
    (hq_lt : q_val < 2 ^ quotientBits U n_max) (hv_lt : v_val < 2 ^ valBits V) :
    PushBackSlotPost U V w n_max h_space base b q_val v_val s
      ((Memory.spec 0).clientState s
        (pushBackSlotProg U V w n_max h_space (((base, b), q_val), v_val))) := by
  have hb_eq := bucket_eq_zero_of_bits_eq_zero hb0 hb
  subst hb_eq
  unfold totalSlots at htot; rw [ite_eq_left hb0] at htot
  have h0_lt : 0 < globalMetaLen n_max := by wram_omega
  have hc1_lt := lt_two_pow_globalPtrBits_of_le_n_max (n_max := n_max)
    (x := gmAt base U V w n_max h_space s.mem 0 + 1) (by omega)
  obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
    writeQuotProg_effect (base := base) (V := V) (h_space := h_space) hw htot hq_lt s
  let s₁ := (Memory.spec 0).clientState s
    (writeQuotProg U w n_max h_space ((base, gmAt base U V w n_max h_space s.mem 0), q_val))
  obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ :=
    writeValProg_effect (base := base) (h_space := h_space) hw htot hv_lt s₁
  let s₂ := (Memory.spec 0).clientState s₁
    (writeValProg U V w n_max h_space ((base, gmAt base U V w n_max h_space s.mem 0), v_val))
  obtain ⟨hf3, hout3, hq3, hv3, hl3, hg3⟩ :=
    writeGMProg_effect (base := base) (V := V) (h_space := h_space) hw h0_lt hc1_lt s₂
  have hst : (Memory.spec 0).clientState s
      (pushBackSlotProg U V w n_max h_space (((base, 0), q_val), v_val)) =
      (Memory.spec 0).clientState s₂ (writeGMProg U V w n_max h_space
        ((base, 0), gmAt base U V w n_max h_space s.mem 0 + 1)) := by
    simp only [pushBackSlotProg, pushBackSlotGenProg, ite_bucketBits_mk, readGMGenProg_mk,
      writeQuotGenProg_mk, writeValGenProg_mk, writeGMGenProg_mk, hb0, ↓reduceIte]
    rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s h0_lt, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind]
  have hgm' : gmAt base U V w n_max h_space ((Memory.spec 0).clientState s
      (pushBackSlotProg U V w n_max h_space (((base, 0), q_val), v_val))).mem =
      Function.update (gmAt base U V w n_max h_space s.mem) 0
        (gmAt base U V w n_max h_space s.mem 0 + 1) := by rw [hst, hg3, hg2, hg1]
  have hcost : memoryCost (pushBackSlotProg U V w n_max h_space (((base, 0), q_val), v_val)) s =
      14 := by
    simp [pushBackSlotProg, pushBackSlotGenProg,
      writeQuotGenProg_mk, writeValGenProg_mk, writeGMGenProg_mk, hb0,
      ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  refine ⟨by rw [hst, hf3, hf2, hf1],
    fun a ha => by
      rw [hst, hout3 a (by wram_omega [ha]), hout2 a (by wram_omega [ha]),
        hout1 a (by wram_omega [ha])],
    by rw [hst, hl3, hl2, hl1],
    slotStoreInv_single hb0 (by rw [hgm']; update_simp; omega),
    by unfold totalSlots; simp only [hb0, ↓reduceIte, hgm']; update_simp,
    by unfold bCount; simp only [hb0, ↓reduceIte, hgm']; update_simp,
    fun b' hb' hne => absurd (bucket_eq_zero_of_bits_eq_zero hb0 hb') hne,
    by rw [hst, hq3, hq2, hq1]; simp only [slotOf, bCount, hb0, ↓reduceIte]; update_simp,
    by rw [hst, hv3, hv2]; simp only [slotOf, bCount, hb0, ↓reduceIte]; update_simp,
    fun b' hb' j hj => ?_, by unfold slotPotential; simp [hb0, hcost]⟩
  obtain rfl := bucket_eq_zero_of_bits_eq_zero hb0 hb'
  simp only [bCount, hb0, ↓reduceIte] at hj
  simp only [slotOf, hb0, ↓reduceIte]
  exact ⟨by rw [hst, hq3, hq2, hq1]; update_simp, by rw [hst, hv3, hv2, hv1]; update_simp⟩

private theorem pushBackSlotProg_effect_multi {U V w n_max h_space base b q_val v_val : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space s.mem))
    (hb : b < numBuckets n_max)
    (htot : totalSlots n_max (gmAt base U V w n_max h_space s.mem) < n_max)
    (hq_lt : q_val < 2 ^ quotientBits U n_max) (hv_lt : v_val < 2 ^ valBits V)
    (s' : Memory.State)
    (hrun : (Memory.spec 0).clientState s
      (pushBackSlotProg U V w n_max h_space (((base, b), q_val), v_val)) = s') :
    PushBackSlotPost U V w n_max h_space base b q_val v_val s s' := by
  unfold PushBackSlotPost
  intro gm₀ gm'
  let d := (((base, b), q_val), v_val)
  have hr0_lt : gm₀ (gmRIdx b) < 2 * slabSize n_max := r_lt_two_slabSize hb_pos hinv hb
  have htot0 : gm₀ 0 * slabSize n_max + gm₀ 1 < n_max := by
    have h := htot; rw [totalSlots_multi_eq hb_pos] at h; exact h
  obtain ⟨hres1, hf1, hout1, hl1, -, htail1, hslab1, htot1, hqb1, hrb1, hother1,
      hbc_b1, hbc_other1, hq_new1, hv_new1, hold1⟩ :=
    pushBackTailWriteProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos s hinv hb htot hq_lt hv_lt
  obtain ⟨hexec, hcharge⟩ := pushBackSlotProg_execution s _ (Nat.ne_of_gt hb_pos) rfl _ hres1
  generalize hs₁ : (Memory.spec 0).clientState s
    (pushBackTailWriteProg U V w n_max h_space d) = s₁ at *
  have hexec' := hrun.symm.trans hexec
  by_cases hprom : gmAt base U V w n_max h_space s.mem (gmRIdx b) + 1 = 2 * slabSize n_max
  · have hst : s' = (Memory.spec 0).clientState s₁
        (promoteSlabProg U V w n_max h_space (base, b)) := hexec'.trans (ite_eq_left hprom)
    have htot1_le : gmAt base U V w n_max h_space s₁.mem 0 * slabSize n_max +
        gmAt base U V w n_max h_space s₁.mem 1 ≤ n_max := by
      dsimp only [gm₀] at htot0; omega
    have hpre : PromoteSlabInv U V w n_max h_space base b s₁ :=
      promoteSlabInv_of_other_and_tail hb_pos hinv hb htail1 hslab1 (by rw [hrb1, hprom])
        hother1 htot1_le
    obtain ⟨hf2, hout2, hl2, hinv2, hqb2, hrb2, hother2, hbc2, hslot2, hcost2⟩ :=
      promoteSlabProg_effect hw hb_pos s₁ hpre
    have htot2 := promoteSlabProg_tot_eq hw hb_pos s₁ hpre
    rw [← hst] at hf2 hout2 hl2 hinv2 hqb2 hrb2 hother2 hbc2 hslot2 htot2
    have hpot := slotPotential_pushBack_le hb_pos hb
      ⟨by unfold pushBackCounts; rw [ite_eq_left hprom, hqb2, hqb1],
       by unfold pushBackCounts; rw [ite_eq_left hprom, hrb2]⟩
      fun b' hb' hne => ⟨(hother2 b' hb' hne).1.trans (hother1 b' hb' hne).1,
        (hother2 b' hb' hne).2.trans (hother1 b' hb' hne).2⟩
    unfold pushBackWork at hpot; rw [ite_eq_left hprom] at hpot hcharge
    have hbc_lt : bCount n_max gm' b = bCount n_max gm₀ b + 1 := (hbc2 b hb).trans hbc_b1
    have hbc_old_lt : bCount n_max gm₀ b < bCount n_max gm' b := by rw [hbc_lt]; omega
    refine ⟨hf2.trans hf1, fun a ha => (hout2 a ha).trans (hout1 a ha), hl2.trans hl1, hinv2,
      by rw [totalSlots_multi_eq hb_pos, totalSlots_multi_eq hb_pos, htot2, htot1],
      hbc_lt, fun b' hb' hne => (hbc2 b' hb').trans (hbc_other1 b' hb' hne),
      by rw [(hslot2 b hb _ hbc_old_lt).1, hq_new1],
      by rw [(hslot2 b hb _ hbc_old_lt).2, hv_new1],
      fun b' hb' j hj => ?_, ?_⟩
    · have hj' : j < bCount n_max gm' b' := by
        by_cases hbeq : b' = b
        · subst b'; rw [hbc_lt]; omega
        · rw [hbc2 b' hb', hbc_other1 b' hb' hbeq]; exact hj
      exact ⟨(hslot2 b' hb' j hj').1.trans (hold1 b' hb' j hj).1,
        (hslot2 b' hb' j hj').2.trans (hold1 b' hb' j hj).2⟩
    · dsimp only [d, gm₀, gm'] at hcharge hcost2 hpot ⊢; omega
  · have hst : s' = s₁ := hexec'.trans (ite_eq_right hprom)
    subst hst
    have hinv1 := slotStoreInv_multi_of_bucket hb_pos hinv htail1 hslab1
      (by rw [hqb1, hrb1]; unfold tailCapPerBucket; rw [ite_eq_right (Nat.ne_of_gt hb_pos)]
          dsimp only [gm₀] at hr0_lt; omega)
      hother1 (by dsimp only [gm₀] at htot0; omega)
    have hpot := slotPotential_pushBack_le hb_pos hb
      ⟨by unfold pushBackCounts; rw [ite_eq_right hprom, hqb1],
       by unfold pushBackCounts; rw [ite_eq_right hprom, hrb1]⟩ hother1
    unfold pushBackWork at hpot; rw [ite_eq_right hprom] at hpot hcharge
    exact ⟨hf1, hout1, hl1, hinv1,
      by rw [totalSlots_multi_eq hb_pos, totalSlots_multi_eq hb_pos, htot1],
      hbc_b1, hbc_other1, hq_new1, hv_new1, hold1,
      by dsimp only [d, gm₀, gm'] at hcharge hpot ⊢; omega⟩

/-- Pure state effect and amortized `memoryCost` bound of `pushBackSlotProg`. -/
theorem pushBackSlotProg_effect {U V w n_max h_space base b q_val v_val : ℕ}
    (hw : 0 < w) (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space s.mem))
    (hb : b < numBuckets n_max)
    (htot : totalSlots n_max (gmAt base U V w n_max h_space s.mem) < n_max)
    (hq_lt : q_val < 2 ^ quotientBits U n_max)
    (hv_lt : v_val < 2 ^ valBits V) :
    let gm₀ := gmAt base U V w n_max h_space s.mem
    let d := (((base, b), q_val), v_val)
    let s' := (Memory.spec 0).clientState s (pushBackSlotProg U V w n_max h_space d)
    let gm' := gmAt base U V w n_max h_space s'.mem
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    SlotStoreInv n_max gm' ∧
    totalSlots n_max gm' = totalSlots n_max gm₀ + 1 ∧
    bCount n_max gm' b = bCount n_max gm₀ b + 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm' b' = bCount n_max gm₀ b') ∧
    quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b (bCount n_max gm₀ b)) = q_val ∧
    valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b (bCount n_max gm₀ b)) = v_val ∧
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm₀ b',
      quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
      valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j)) ∧
    memoryCost (pushBackSlotProg U V w n_max h_space d) s + 66 * slotPotential n_max gm' ≤
      66 * slotPotential n_max gm₀ + 134 := by
  rcases Nat.eq_zero_or_pos (bucketBits n_max) with hb0 | hb_pos
  · exact pushBackSlotProg_effect_single hw hb0 s hb htot hq_lt hv_lt
  · exact pushBackSlotProg_effect_multi hw hb_pos s hinv hb htot hq_lt hv_lt _ rfl

theorem realizes_pushBackSlotGen :
    Realizes .exact pushBackSlotGenProg
      (WordEncoding.encode (α := ((DictParams × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      PushBackSlotGenPre
      (fun _ _ => 0) := by
  realize
    [realizes_readGMGen, realizes_writeQuotGen, realizes_writeValGen, realizes_writeGMGen,
      realizes_pushBackTailWriteGen, realizes_promoteSlabGen]
  all_goals (
    rcases d with ⟨⟨⟨dp, base, b⟩, q_val⟩, v_val⟩
    let d : ((ℕ × ℕ) × ℕ) × ℕ := (((base, b), q_val), v_val)
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
    simpDictParamsWith [pushBackSlotGenPre_mk, pushBackTailWriteGenPre_mk,
      pushBackTailWriteGenProg_mk, promoteSlabGenPre_mk, promoteSlabGenProg_mk]
    dsimp only [d, PushBackSlotPre] at *
  )
  · exact h.1
  · wram_omega
  · rw [clientResult_readGMProg _ (by wram_omega : 0 < globalMetaLen n_max)]
    have htot := h.2.2.2.1; unfold totalSlots at htot; rwa [ite_eq_left hc] at htot
  · rw [clientResult_readGMProg _ (by wram_omega : 0 < globalMetaLen n_max)]
    have htot := h.2.2.2.1; unfold totalSlots at htot; rw [ite_eq_left hc] at htot
    exact fits_of_le_max_n_one h.1 hw hnU hU (by omega)
  · exact ⟨h, Nat.pos_of_ne_zero hc⟩
  · rename_i hc0
    have hb_pos := Nat.pos_of_ne_zero hc0
    rcases h with ⟨hdict, hinv, hb, htot, hq_lt, hv_lt⟩
    obtain ⟨hres1, _, _, _, _, htail1, hslab1, htot1, _, hrb1, hother1, _⟩ :=
      pushBackTailWriteProg_effect (U := U) (V := V) (h_space := h_space)
        hw hb_pos s hinv hb htot hq_lt hv_lt
    rw [totalSlots_multi_eq hb_pos] at htot
    rw [hres1] at hc
    exact ⟨hdict, promoteSlabInv_of_other_and_tail hb_pos hinv hb htail1 hslab1
      (by rw [hrb1, hc]) hother1 (by omega), hb_pos⟩

/-! ## Section 3: `popBackSlotProg` via `realize` -/

/-- Parameter-free `Memory.Prog` operation removing the last logical slot `bCount n_max gm b - 1`
of a non-empty bucket `b = d.2.2` at `base = d.2.1`. -/
@[expose]
def popBackSlotGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog Unit :=
  if dpBucketBits d.1 = 0 then do
    let c ← readGMGenProg (d.1, (d.2.1, 0))
    writeGMGenProg (d.1, ((d.2.1, 0), c - 1))
  else do
    removeLastTailItemGenProg d
    let r_b_new ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2 + 1))
    let q_b ← readGMGenProg (d.1, (d.2.1, 4 + 3 * d.2.2))
    if r_b_new = 0 then
      if 0 < q_b then
        demoteSlabGenProg d
      else
        pure ()
    else
      pure ()

/-- `Memory.Prog` operation removing the last logical slot `bCount n_max gm b - 1` of a non-empty
bucket `b = d.2` at `base = d.1`, demoting the top full slab into `K = slabSize n_max` tail items
when `r_b - 1 = 0 ∧ 0 < q_b`. -/
@[expose]
def popBackSlotProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog Unit :=
  popBackSlotGenProg (mkDictParams U V w n_max h_space, d)

@[simp] theorem popBackSlotGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    popBackSlotGenProg (mkDictParams U V w n_max h_space, d) =
      popBackSlotProg U V w n_max h_space d := by
  rfl

/-- Precondition for `popBackSlotProg` in `Realizes`. -/
@[expose]
def PopBackSlotPre (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ) (s : Memory.State) : Prop :=
  let base := d.1
  let b := d.2
  let gm := gmAt base U V w₀ n_max h_space s.mem
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  SlotStoreInv n_max gm ∧
  b < numBuckets n_max ∧
  1 ≤ bCount n_max gm b

/-- Parameter-free precondition for `popBackSlotGenProg`. -/
@[expose]
def PopBackSlotGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let gm := gmAt d.2.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  DictEnvGen w d.1 d.2.1 ∧
  SlotStoreInv (dpNMax d.1) gm ∧
  d.2.2 < numBuckets (dpNMax d.1) ∧
  1 ≤ bCount (dpNMax d.1) gm d.2.2

@[simp] theorem popBackSlotGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    PopBackSlotGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      PopBackSlotPre U V w₀ n_max h_space w d s := Iff.rfl

-- Readback and state equations keep packed writes out of execution normalization.
private theorem popBackSlotProg_execution {U V w n_max h_space base b : ℕ}
    (s s₁ : Memory.State) (hb0 : bucketBits n_max ≠ 0)
    (hs1 : (Memory.spec 0).clientState s
      (removeLastTailItemProg U V w n_max h_space (base, b)) = s₁)
    (r q : ℕ)
    (hr : (Memory.spec 0).clientResult s₁
      (readGMProg U V w n_max h_space (base, 4 + 3 * b + 1)) = r)
    (hq : (Memory.spec 0).clientResult s₁
      (readGMProg U V w n_max h_space (base, 4 + 3 * b)) = q) :
    (Memory.spec 0).clientState s (popBackSlotProg U V w n_max h_space (base, b)) =
      (if r = 0 ∧ 0 < q then
        (Memory.spec 0).clientState s₁ (demoteSlabProg U V w n_max h_space (base, b))
      else s₁) ∧
    memoryCost (popBackSlotProg U V w n_max h_space (base, b)) s =
      40 + (if r = 0 ∧ 0 < q then
        memoryCost (demoteSlabProg U V w n_max h_space (base, b)) s₁ else 0) := by
  simp only [popBackSlotProg, popBackSlotGenProg, ite_bucketBits_mk, readGMGenProg_mk,
    writeGMGenProg_mk, removeLastTailItemGenProg_mk, demoteSlabGenProg_mk, hb0, ↓reduceIte]
  constructor
  · rw [StateTransitionSpec.clientState_bind, hs1,
      StateTransitionSpec.clientState_bind, clientState_readGMProg, hr,
      StateTransitionSpec.clientState_bind, clientState_readGMProg, hq]
    by_cases hr0 : r = 0 <;> by_cases hq0 : 0 < q <;> simp [hr0, hq0] <;> rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind]
    rw [memoryCost_bind, memoryCost_removeLastTailItemProg, hs1,
      memoryCost_bind, memoryCost_readGMProg, clientState_readGMProg, hr,
      memoryCost_bind, memoryCost_readGMProg, clientState_readGMProg, hq]
    by_cases hr0 : r = 0 <;> by_cases hq0 : 0 < q
    all_goals simp [hr0, hq0, memoryCost_pure]
    omega

private theorem popBackTailRemove_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space s.mem))
    (hb : b < numBuckets n_max)
    (hbc : 1 ≤ bCount n_max (gmAt base U V w n_max h_space s.mem) b) :
    let gm₀ := gmAt base U V w n_max h_space s.mem
    let s₁ := (Memory.spec 0).clientState s (removeLastTailItemProg U V w n_max h_space (base, b))
    let gm₁ := gmAt base U V w n_max h_space s₁.mem
    s₁.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s₁.mem a = s.mem a) ∧
    lmAt base U V w n_max h_space s₁.mem = lmAt base U V w n_max h_space s.mem ∧
    TailBijection n_max gm₁ (fun b' => gm₁ (gmRIdx b')) (gm₁ 1) ∧
    SlabBijection n_max gm₁ (fun b' => gm₁ (gmQIdx b')) (gm₁ 0) ∧
    gm₁ 0 * slabSize n_max + gm₁ 1 + 1 = gm₀ 0 * slabSize n_max + gm₀ 1 ∧
    gm₁ (gmQIdx b) = gm₀ (gmQIdx b) ∧
    gm₁ (gmRIdx b) = gm₀ (gmRIdx b) - 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b →
      gm₁ (gmQIdx b') = gm₀ (gmQIdx b') ∧ gm₁ (gmRIdx b') = gm₀ (gmRIdx b')) ∧
    bCount n_max gm₁ b = bCount n_max gm₀ b - 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm₁ b' = bCount n_max gm₀ b') ∧
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm₁ b',
      quotAt base U w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) =
        quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
      valAt base U V w n_max h_space s₁.mem (slotOf n_max gm₁ b' j) =
        valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j)) := by
  intro gm₀ s₁ gm₁
  have hr0_pos := pos_gmRIdx_of_pos_bCount hb_pos hinv hb hbc
  have htail₀ := hinv.multi_tail hb_pos
  have hslab₀ := hinv.multi_slab hb_pos
  have htot₀ := hinv.multi_total_le hb_pos
  obtain ⟨hf1, hout1, hq1, hv1, hl1, hgm1_eq⟩ :=
    removeLastTailItemProg_effect (U := U) (V := V) (h_space := h_space)
      hw hb_pos hb s htail₀ hr0_pos
  change gm₁ = gmRemoveTail n_max gm₀ b at hgm1_eq
  rcases gmRemoveTail_preserves_nonTail hb hr0_pos htail₀ with ⟨hp0, hp1, hpR, hpOther, hpQ, -⟩
  have hgm1_pos : 1 ≤ gm₀ 1 := le_trans hr0_pos (r_le_ntails_of_tailBijection htail₀ hb)
  have hq_slot := (update_slotOf_gmRemoveTail (quotAt base U w n_max h_space s.mem)
    hb_pos hb hr0_pos htail₀ hslab₀ htot₀).1
  have hv_slot := (update_slotOf_gmRemoveTail (valAt base U V w n_max h_space s.mem)
    hb_pos hb hr0_pos htail₀ hslab₀ htot₀).1
  refine ⟨hf1, hout1, hl1,
    by rw [hgm1_eq]
       exact tailBijection_gmRemoveTail hb hr0_pos htail₀,
    by rw [hgm1_eq]
       exact (slabBijection_gmRemoveTail hb hr0_pos htail₀ hslab₀).2,
    by rw [hgm1_eq, hp0, hp1, Nat.add_assoc, Nat.sub_add_cancel hgm1_pos],
    by rw [hgm1_eq, hpQ b hb],
    by rw [hgm1_eq, hpR],
    fun b' hb' hne => ⟨by rw [hgm1_eq, hpQ b' hb'],
      by rw [hgm1_eq, hpOther b' hb' hne]⟩,
    by rw [bCount_multi_eq hb_pos hb, bCount_multi_eq hb_pos hb, hgm1_eq, hpQ b hb, hpR]
       change 1 ≤ gm₀ (gmRIdx b) at hr0_pos
       dsimp only [gm₀] at *
       omega,
    fun b' hb' hne => by
      rw [bCount_multi_eq hb_pos hb', bCount_multi_eq hb_pos hb', hgm1_eq, hpQ b' hb',
        hpOther b' hb' hne],
    fun b' hb' j hj => ?_⟩
  rw [hq1, hv1, hgm1_eq]
  rw [hgm1_eq] at hj
  exact ⟨hq_slot b' hb' j hj, hv_slot b' hb' j hj⟩

private abbrev PopBackSlotPost (U V w n_max h_space base b : ℕ)
    (s s' : Memory.State) : Prop :=
  let gm₀ := gmAt base U V w n_max h_space s.mem
  let gm' := gmAt base U V w n_max h_space s'.mem
  s'.frontier = s.frontier ∧
  (∀ a, ¬(base + offQuot h_space ≤ a ∧
      a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
  lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
  SlotStoreInv n_max gm' ∧
  totalSlots n_max gm' + 1 = totalSlots n_max gm₀ ∧
  bCount n_max gm' b = bCount n_max gm₀ b - 1 ∧
  (∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm' b' = bCount n_max gm₀ b') ∧
  (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm' b',
    quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b' j) =
      quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
    valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b' j) =
      valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j)) ∧
  memoryCost (popBackSlotProg U V w n_max h_space (base, b)) s + 66 * slotPotential n_max gm' ≤
    66 * slotPotential n_max gm₀ + 174

private theorem popBackSlotProg_effect_single {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb0 : bucketBits n_max = 0) (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space s.mem))
    (hb : b < numBuckets n_max)
    (hbc : 1 ≤ bCount n_max (gmAt base U V w n_max h_space s.mem) b) :
    PopBackSlotPost U V w n_max h_space base b s
      ((Memory.spec 0).clientState s (popBackSlotProg U V w n_max h_space (base, b))) := by
  have hb_eq := bucket_eq_zero_of_bits_eq_zero hb0 hb
  subst hb_eq
  unfold bCount at hbc; simp only [hb0, ↓reduceIte] at hbc
  let gm₀ := gmAt base U V w n_max h_space s.mem
  have hc_le : gm₀ 0 ≤ n_max := hinv.single_valid hb0
  have h0_lt : 0 < globalMetaLen n_max := by wram_omega
  have hc1_lt := lt_two_pow_globalPtrBits_of_le_n_max (n_max := n_max) (x := gm₀ 0 - 1) (by omega)
  obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
    writeGMProg_effect (base := base) (V := V) (h_space := h_space) hw h0_lt hc1_lt s
  have hst : (Memory.spec 0).clientState s (popBackSlotProg U V w n_max h_space (base, 0)) =
      (Memory.spec 0).clientState s (writeGMProg U V w n_max h_space ((base, 0), gm₀ 0 - 1)) := by
    simp only [popBackSlotProg, popBackSlotGenProg, ite_bucketBits_mk, readGMGenProg_mk,
      writeGMGenProg_mk, hb0, ↓reduceIte]
    rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s h0_lt]
  have hgm' : gmAt base U V w n_max h_space ((Memory.spec 0).clientState s
      (popBackSlotProg U V w n_max h_space (base, 0))).mem =
      Function.update gm₀ 0 (gm₀ 0 - 1) := by rw [hst, hg1]
  have hcost : memoryCost (popBackSlotProg U V w n_max h_space (base, 0)) s = 6 := by
    simp [popBackSlotProg, popBackSlotGenProg, writeGMGenProg_mk, hb0,
      ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  refine ⟨by rw [hst, hf1],
    fun a ha => by rw [hst, hout1 a (by wram_omega [ha])],
    by rw [hst, hl1],
    slotStoreInv_single hb0 (by rw [hgm']; update_simp; omega),
    by unfold totalSlots
       simp only [hb0, ↓reduceIte, hgm']; update_simp
       change 1 ≤ gmAt base U V w n_max h_space s.mem 0 at hbc
       dsimp only [gm₀]; omega,
    by unfold bCount; simp only [hb0, ↓reduceIte, hgm']; update_simp,
    fun b' hb' hne => absurd (bucket_eq_zero_of_bits_eq_zero hb0 hb') hne,
    fun b' _ j _ => by simp only [slotOf, hb0, ↓reduceIte]; rw [hst, hq1, hv1]; exact ⟨rfl, rfl⟩,
    by unfold slotPotential; simp [hb0, hcost]⟩

private theorem popBackSlotProg_effect_multi {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space s.mem))
    (hb : b < numBuckets n_max)
    (hbc : 1 ≤ bCount n_max (gmAt base U V w n_max h_space s.mem) b)
    (s' : Memory.State)
    (hrun : (Memory.spec 0).clientState s
      (popBackSlotProg U V w n_max h_space (base, b)) = s') :
    PopBackSlotPost U V w n_max h_space base b s s' := by
  unfold PopBackSlotPost
  intro gm₀ gm'
  have hr0_pos := pos_gmRIdx_of_pos_bCount hb_pos hinv hb hbc
  have hr0_lt := r_lt_two_slabSize hb_pos hinv hb
  have htot₀ := hinv.multi_total_le hb_pos
  obtain ⟨hf1, hout1, hl1, htail1, hslab1, htot1, hqb1, hrb1, hother1,
      hbc_b1, hbc_other1, hold1⟩ := popBackTailRemove_effect hw hb_pos s hinv hb hbc
  obtain ⟨hexec, hcharge⟩ := popBackSlotProg_execution s _ (Nat.ne_of_gt hb_pos) rfl _ _ rfl rfl
  generalize hs₁ : (Memory.spec 0).clientState s
    (removeLastTailItemProg U V w n_max h_space (base, b)) = s₁ at *
  rw [readGM_r_result hb_pos hb s₁, readGM_q_result hb_pos hb s₁] at hexec hcharge
  have hexec' := hrun.symm.trans hexec
  have hguard : (gmAt base U V w n_max h_space s₁.mem (gmRIdx b) = 0 ∧
      0 < gmAt base U V w n_max h_space s₁.mem (gmQIdx b)) ↔
      (gmAt base U V w n_max h_space s.mem (gmRIdx b) = 1 ∧
        0 < gmAt base U V w n_max h_space s.mem (gmQIdx b)) := by
    rw [hrb1, hqb1]; omega
  simp only [hguard] at hexec' hcharge
  by_cases hdem : gmAt base U V w n_max h_space s.mem (gmRIdx b) = 1 ∧
      0 < gmAt base U V w n_max h_space s.mem (gmQIdx b)
  · have hst : s' = (Memory.spec 0).clientState s₁
        (demoteSlabProg U V w n_max h_space (base, b)) := hexec'.trans (ite_eq_left hdem)
    have hpre : DemoteSlabInv U V w n_max h_space base b s₁ :=
      ⟨hb, htail1, hslab1, by rw [hrb1, hdem.1], by rw [hqb1]; exact hdem.2,
        fun b' hb' hne => by
          rw [(hother1 b' hb' hne).1, (hother1 b' hb' hne).2]
          exact hinv.multi_r_bounds hb_pos b' hb',
        by omega⟩
    obtain ⟨hf2, hout2, hl2, hinv2, hqb2, hrb2, hother2, hbc2, hslot2, hcost2⟩ :=
      demoteSlabProg_effect hw hb_pos s₁ hpre
    have htot2 := demoteSlabProg_tot_eq hw hb_pos s₁ hpre
    rw [← hst] at hf2 hout2 hl2 hinv2 hqb2 hrb2 hother2 hbc2 hslot2 htot2
    have hpot := slotPotential_popBack_le hb_pos hb hr0_pos hr0_lt
      ⟨by unfold popBackCounts; rw [ite_eq_left hdem, hqb2, hqb1],
       by unfold popBackCounts; rw [ite_eq_left hdem, hrb2]⟩
      fun b' hb' hne => ⟨(hother2 b' hb' hne).1.trans (hother1 b' hb' hne).1,
        (hother2 b' hb' hne).2.trans (hother1 b' hb' hne).2⟩
    unfold popBackWork at hpot; rw [ite_eq_left hdem] at hpot hcharge
    refine ⟨hf2.trans hf1, fun a ha => (hout2 a ha).trans (hout1 a ha), hl2.trans hl1, hinv2,
      by rw [totalSlots_multi_eq hb_pos, totalSlots_multi_eq hb_pos, htot2, htot1],
      (hbc2 b hb).trans hbc_b1, fun b' hb' hne => (hbc2 b' hb').trans (hbc_other1 b' hb' hne),
      fun b' hb' j hj => ⟨(hslot2 b' hb' j hj).1.trans (hold1 b' hb' j (hbc2 b' hb' ▸ hj)).1,
        (hslot2 b' hb' j hj).2.trans (hold1 b' hb' j (hbc2 b' hb' ▸ hj)).2⟩,
      by dsimp only [gm₀, gm'] at hcharge hcost2 hpot ⊢; omega⟩
  · have hst : s' = s₁ := hexec'.trans (ite_eq_right hdem)
    subst hst
    have hinv1 := slotStoreInv_multi_of_bucket hb_pos hinv htail1 hslab1
      (by rw [hqb1, hrb1]; unfold tailCapPerBucket; rw [ite_eq_right (Nat.ne_of_gt hb_pos)]
          refine ⟨by omega, fun hq => ?_⟩; by_contra hlt; exact hdem ⟨by omega, hq⟩)
      hother1 (by omega)
    have hpot := slotPotential_popBack_le hb_pos hb hr0_pos hr0_lt
      ⟨by unfold popBackCounts; rw [ite_eq_right hdem, hqb1],
       by unfold popBackCounts; rw [ite_eq_right hdem, hrb1]⟩ hother1
    unfold popBackWork at hpot; rw [ite_eq_right hdem] at hpot hcharge
    exact ⟨hf1, hout1, hl1, hinv1,
      by rw [totalSlots_multi_eq hb_pos, totalSlots_multi_eq hb_pos, htot1],
      hbc_b1, hbc_other1, hold1, by dsimp only [gm₀, gm'] at hcharge hpot ⊢; omega⟩

/-- Pure state effect and amortized `memoryCost` bound of `popBackSlotProg`. -/
theorem popBackSlotProg_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt base U V w n_max h_space s.mem))
    (hb : b < numBuckets n_max)
    (hbc : 1 ≤ bCount n_max (gmAt base U V w n_max h_space s.mem) b) :
    let gm₀ := gmAt base U V w n_max h_space s.mem
    let d := (base, b)
    let s' := (Memory.spec 0).clientState s (popBackSlotProg U V w n_max h_space d)
    let gm' := gmAt base U V w n_max h_space s'.mem
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    SlotStoreInv n_max gm' ∧
    totalSlots n_max gm' + 1 = totalSlots n_max gm₀ ∧
    bCount n_max gm' b = bCount n_max gm₀ b - 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b → bCount n_max gm' b' = bCount n_max gm₀ b') ∧
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm' b',
      quotAt base U w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        quotAt base U w n_max h_space s.mem (slotOf n_max gm₀ b' j) ∧
      valAt base U V w n_max h_space s'.mem (slotOf n_max gm' b' j) =
        valAt base U V w n_max h_space s.mem (slotOf n_max gm₀ b' j)) ∧
    memoryCost (popBackSlotProg U V w n_max h_space d) s + 66 * slotPotential n_max gm' ≤
      66 * slotPotential n_max gm₀ + 174 := by
  rcases Nat.eq_zero_or_pos (bucketBits n_max) with hb0 | hb_pos
  · exact popBackSlotProg_effect_single hw hb0 s hinv hb hbc
  · exact popBackSlotProg_effect_multi hw hb_pos s hinv hb hbc _ rfl

theorem realizes_popBackSlotGen :
    Realizes .exact popBackSlotGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      PopBackSlotGenPre
      (fun _ _ => 0) := by
  realizeDictWith [popBackSlotGenPre_mk, removeLastTailItemGenPre_mk, removeLastTailItemGenProg_mk,
    demoteSlabGenPre_mk, demoteSlabGenProg_mk] using
    [realizes_readGMGen, realizes_writeGMGen, realizes_removeLastTailItemGen,
      realizes_demoteSlabGen]
  · exact h.1
  · wram_omega
  · exact single_gm0_pos_of_bCount hc h.2.2.1 h.2.2.2
  · have hb_pos := Nat.pos_of_ne_zero hc
    exact ⟨h.1, h.2.1.multi_tail hb_pos, h.2.2.1,
      pos_gmRIdx_of_pos_bCount hb_pos h.2.1 h.2.2.1 h.2.2.2, hb_pos⟩
  · exact gmRIdx_fits h.1 (Nat.pos_of_ne_zero hc) hw hnU hU h.2.2.1
  · exact fits_const_of_dictEnv h.1 (by omega)
  · exact h.1
  · exact gmRIdx_lt (Nat.pos_of_ne_zero hc) h.2.2.1
  · exact fits_of_le_globalMetaLen h.1 (Nat.pos_of_ne_zero hc) hw hnU hU
      (le_of_lt (gmQIdx_lt (Nat.pos_of_ne_zero hc) h.2.2.1))
  · exact gmQIdx_lt (Nat.pos_of_ne_zero hc) h.2.2.1
  · rename_i hc0 hc1
    have hb_pos := Nat.pos_of_ne_zero hc0
    rcases d with ⟨base, b⟩
    rcases h with ⟨hdict, hinv, hb, hbc⟩
    dsimp only at hdict hinv hb hbc hc1 hc ⊢
    have htot₀ := hinv.multi_total_le hb_pos
    obtain ⟨_, _, _, htail1, hslab1, htot1, _, _, hother1, _⟩ :=
      popBackTailRemove_effect (U := U) (V := V) (h_space := h_space) hw hb_pos s hinv hb hbc
    rw [clientState_readGMProg] at hc
    rw [clientState_readGMProg, clientState_readGMProg]
    rw [readGM_r_result hb_pos hb] at hc1
    rw [readGM_q_result hb_pos hb] at hc
    exact ⟨hdict, ⟨hb, htail1, hslab1, hc1, hc, fun b' hb' hne => by
      rw [(hother1 b' hb' hne).1, (hother1 b' hb' hne).2]
      exact hinv.multi_r_bounds hb_pos b' hb', by omega⟩, hb_pos⟩

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
