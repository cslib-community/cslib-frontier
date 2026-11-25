/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctProg
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.StrideOmega
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.WramOmega

/-!
# Tail Pool Allocation and Compaction Operations

This module defines the pure `GlobalMeta` updates (`gmAppendTail`, `gmRemoveTail`) and the
corresponding branch-free `Memory.Prog` operations (`appendTailItemProg`, `removeLastTailItemProg`,
realized to Word-RAM code via `realize`) that allocate and compact tail items while preserving
`TailBijection` and `SlabBijection`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmAppendTail`: pure `GlobalMeta` update
  appending one tail item to bucket `b`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmRemoveTail`: pure `GlobalMeta` update
  removing the last tail item of bucket `b` and compacting the tail pool.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.appendTailItemProg`: `Memory.Prog` subroutine
  realizing `gmAppendTail`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.removeLastTailItemProg`: `Memory.Prog`
  subroutine realizing `gmRemoveTail` and relocating the compacted payload.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.tailBijection_gmAppendTail`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.slabBijection_gmAppendTail`: `gmAppendTail`
  preserves `TailBijection` and `SlabBijection`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.tailBijection_gmRemoveTail`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.slabBijection_gmRemoveTail`: `gmRemoveTail`
  preserves `TailBijection` and `SlabBijection`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.appendTailItemProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_appendTailItemGen`: effect and
  `Realizes` certificate for `appendTailItemProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.removeLastTailItemProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_removeLastTailItemGen`: effect and
  `Realizes` certificate for `removeLastTailItemProg`.
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

/-! ## Section 1: Pure `gmAppendTail` and `gmRemoveTail` updates -/

/-- Pure `GlobalMeta` update appending one tail item to bucket `b`: assigns physical tail offset
`t_new = gm 1` to descriptor `d_new = b * tailCapPerBucket n_max + gm (gmRIdx b)` and increments
`gm (gmRIdx b)` and `gm 1`. -/
@[expose]
def gmAppendTail (n_max : ℕ) (gm : ℕ → ℕ) (b : ℕ) : ℕ → ℕ :=
  let r_b := gm (gmRIdx b)
  let t_new := gm 1
  let d_new := b * tailCapPerBucket n_max + r_b
  Function.update
    (Function.update
      (Function.update
        (Function.update gm (gmTailPtrFlatIdx n_max d_new) t_new)
        (gmTailOwnerIdx n_max t_new) d_new)
      (gmRIdx b) (r_b + 1))
    1 (t_new + 1)

/-- Pure `GlobalMeta` update removing the last tail item `r_del = gm (gmRIdx b) - 1` of bucket `b`
by relocating the last physical tail `t_last = gm 1 - 1` into
`t_del = gm (gmTailPtrIdx n_max b r_del)` and decrementing `gm (gmRIdx b)` and `gm 1`. When
`t_del = t_last`, the pointer updates are idempotent. -/
@[expose]
def gmRemoveTail (n_max : ℕ) (gm : ℕ → ℕ) (b : ℕ) : ℕ → ℕ :=
  let r_del := gm (gmRIdx b) - 1
  let t_del := gm (gmTailPtrIdx n_max b r_del)
  let t_last := gm 1 - 1
  let d_last := gm (gmTailOwnerIdx n_max t_last)
  Function.update
    (Function.update
      (Function.update
        (Function.update gm (gmTailPtrFlatIdx n_max d_last) t_del)
        (gmTailOwnerIdx n_max t_del) d_last)
      (gmRIdx b) r_del)
    1 t_last

/-- Quotient and remainder of a flat two-dimensional index `b * c + r` when `r < c`. -/
theorem mul_add_div_mod_of_lt {b c r : ℕ} (hr : r < c) :
    (b * c + r) / c = b ∧ (b * c + r) % c = r :=
  ⟨by rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero],
    by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]⟩

theorem flat_descriptor_inj {n_max b₁ r₁ b₂ r₂ : ℕ}
    (hr₁ : r₁ < tailCapPerBucket n_max) (hr₂ : r₂ < tailCapPerBucket n_max)
    (heq : b₁ * tailCapPerBucket n_max + r₁ = b₂ * tailCapPerBucket n_max + r₂) :
    b₁ = b₂ ∧ r₁ = r₂ := by
  have h1 := mul_add_div_mod_of_lt (b := b₁) hr₁
  have h2 := mul_add_div_mod_of_lt (b := b₂) hr₂
  exact ⟨by rw [← h1.1, heq, h2.1], by rw [← h1.2, heq, h2.2]⟩

/-- The four-cell `GlobalMeta` write shared by `gmAppendTail` and `gmRemoveTail`: point descriptor
`d` at physical tail `t`, record `d` as the owner of `t`, set bucket `b`'s tail count to `r` and the
total tail count to `nt`. -/
private def gmTailWrite (n_max : ℕ) (gm : ℕ → ℕ) (b d t r nt : ℕ) : ℕ → ℕ :=
  Function.update
    (Function.update
      (Function.update
        (Function.update gm (gmTailPtrFlatIdx n_max d) t)
        (gmTailOwnerIdx n_max t) d)
      (gmRIdx b) r)
    1 nt

/-- `gmTailWrite` changes no cell outside the tail-pointer and tail-owner arrays other than the
total and bucket-`b` tail counts. -/
private theorem gmTailWrite_preserves_nonTail {n_max : ℕ} (gm : ℕ → ℕ) {b d t : ℕ} (r nt : ℕ)
    (hb : b < numBuckets n_max) (hd : d < maxTailItems n_max) (ht : t < maxTailItems n_max) :
    gmTailWrite n_max gm b d t r nt 0 = gm 0 ∧
    gmTailWrite n_max gm b d t r nt 1 = nt ∧
    gmTailWrite n_max gm b d t r nt (gmRIdx b) = r ∧
    (∀ b' < numBuckets n_max, b' ≠ b →
      gmTailWrite n_max gm b d t r nt (gmRIdx b') = gm (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max, gmTailWrite n_max gm b d t r nt (gmQIdx b') = gm (gmQIdx b')) ∧
    (∀ b' < numBuckets n_max,
      gmTailWrite n_max gm b d t r nt (gmSlabTopIdx b') = gm (gmSlabTopIdx b')) ∧
    (∀ b' < numBuckets n_max, ∀ s < dirSlabsPerBucket n_max,
      gmTailWrite n_max gm b d t r nt (gmSlabDirIdx n_max b' s) = gm (gmSlabDirIdx n_max b' s)) ∧
    (∀ idx, gmSlabMetaBase n_max ≤ idx → gmTailWrite n_max gm b d t r nt idx = gm idx) := by
  unfold gmTailWrite gmQIdx gmRIdx gmSlabTopIdx gmSlabDirIdx gmTailPtrFlatIdx gmTailOwnerIdx
    gmSlabMetaBase gmTailOwnerBase gmTailPtrBase gmSlabDirBase
  exact ⟨by update_simp, by update_simp, by update_simp,
    fun b' hb' hne => by update_simp, fun b' hb' => by update_simp,
    fun b' hb' => by update_simp, fun b' hb' s hs => by update_simp,
    fun idx hidx => by update_simp⟩

/-- `gmTailWrite` points descriptor `d` at `t` and makes `d` the owner of `t`, leaving the other
tail pointers and owners unchanged. -/
private theorem gmTailWrite_tail {n_max : ℕ} (gm : ℕ → ℕ) {b d : ℕ} (t r nt : ℕ)
    (hb : b < numBuckets n_max) (hd : d < maxTailItems n_max) :
    (∀ d' < maxTailItems n_max,
      gmTailWrite n_max gm b d t r nt (gmTailPtrFlatIdx n_max d') =
        if d' = d then t else gm (gmTailPtrFlatIdx n_max d')) ∧
    (∀ t' < maxTailItems n_max,
      gmTailWrite n_max gm b d t r nt (gmTailOwnerIdx n_max t') =
        if t' = t then d else gm (gmTailOwnerIdx n_max t')) := by
  unfold gmTailWrite gmRIdx gmTailPtrFlatIdx gmTailOwnerIdx gmTailOwnerBase gmTailPtrBase
    gmSlabDirBase
  exact ⟨fun d' hd' => by split_ifs <;> update_simp, fun t' ht' => by split_ifs <;> update_simp⟩

theorem gmAppendTail_preserves_nonTail {n_max : ℕ} (gm : ℕ → ℕ) {b : ℕ}
    (hb : b < numBuckets n_max) (hr : gm (gmRIdx b) < tailCapPerBucket n_max)
    (ht : gm 1 < maxTailItems n_max) :
    gmAppendTail n_max gm b 0 = gm 0 ∧
    gmAppendTail n_max gm b 1 = gm 1 + 1 ∧
    gmAppendTail n_max gm b (gmRIdx b) = gm (gmRIdx b) + 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b → gmAppendTail n_max gm b (gmRIdx b') = gm (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max, gmAppendTail n_max gm b (gmQIdx b') = gm (gmQIdx b')) ∧
    (∀ b' < numBuckets n_max, gmAppendTail n_max gm b (gmSlabTopIdx b') = gm (gmSlabTopIdx b')) ∧
    (∀ b' < numBuckets n_max, ∀ s < dirSlabsPerBucket n_max,
      gmAppendTail n_max gm b (gmSlabDirIdx n_max b' s) = gm (gmSlabDirIdx n_max b' s)) ∧
    (∀ idx, gmSlabMetaBase n_max ≤ idx → gmAppendTail n_max gm b idx = gm idx) := by
  have hd_lt : b * tailCapPerBucket n_max + gm (gmRIdx b) < maxTailItems n_max :=
    mul_tailCapPerBucket_add_lt_maxTailItems hb hr
  exact gmTailWrite_preserves_nonTail gm (gm (gmRIdx b) + 1) (gm 1 + 1) hb hd_lt ht

theorem gmAppendTail_tail {n_max : ℕ} (gm : ℕ → ℕ) {b : ℕ}
    (hb : b < numBuckets n_max) (hr : gm (gmRIdx b) < tailCapPerBucket n_max)
    (_ht : gm 1 < maxTailItems n_max) :
    (∀ d < maxTailItems n_max,
      gmAppendTail n_max gm b (gmTailPtrFlatIdx n_max d) =
        if d = b * tailCapPerBucket n_max + gm (gmRIdx b) then gm 1
        else gm (gmTailPtrFlatIdx n_max d)) ∧
    (∀ t < maxTailItems n_max,
      gmAppendTail n_max gm b (gmTailOwnerIdx n_max t) =
        if t = gm 1 then b * tailCapPerBucket n_max + gm (gmRIdx b)
        else gm (gmTailOwnerIdx n_max t)) := by
  have hd_lt : b * tailCapPerBucket n_max + gm (gmRIdx b) < maxTailItems n_max :=
    mul_tailCapPerBucket_add_lt_maxTailItems hb hr
  exact gmTailWrite_tail gm (gm 1) (gm (gmRIdx b) + 1) (gm 1 + 1) hb hd_lt

theorem tailBijection_gmAppendTail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hr : gm (gmRIdx b) < tailCapPerBucket n_max)
    (ht : gm 1 < maxTailItems n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    TailBijection n_max (gmAppendTail n_max gm b)
      (fun b' => gmAppendTail n_max gm b (gmRIdx b')) (gmAppendTail n_max gm b 1) := by
  have hpres := gmAppendTail_preserves_nonTail gm hb hr ht
  obtain ⟨hptr_val, hown_val⟩ := gmAppendTail_tail gm hb hr ht
  set d_new := b * tailCapPerBucket n_max + gm (gmRIdx b)
  have hd_lt : d_new < maxTailItems n_max := mul_tailCapPerBucket_add_lt_maxTailItems hb hr
  have hr_fn (b' : ℕ) (hb' : b' < numBuckets n_max) :
      gmAppendTail n_max gm b (gmRIdx b') =
        if b' = b then gm (gmRIdx b) + 1 else gm (gmRIdx b') := by
    split_ifs with heq
    exacts [heq ▸ hpres.2.2.1, hpres.2.2.2.1 b' hb' heq]
  have hslot_info (b' : ℕ) (hb' : b' < numBuckets n_max) (r' : ℕ)
      (hr' : r' < gmAppendTail n_max gm b (gmRIdx b')) :
      b' * tailCapPerBucket n_max + r' < maxTailItems n_max ∧
      (b' * tailCapPerBucket n_max + r' ≠ d_new → r' < gm (gmRIdx b')) := by
    rw [hr_fn b' hb'] at hr'
    split_ifs at hr' with heq
    · subst heq
      refine ⟨mul_tailCapPerBucket_add_lt_maxTailItems hb' (by omega), fun hne => ?_⟩
      have : r' ≠ gm (gmRIdx b') := fun h => hne (by simp [d_new, h])
      omega
    · exact ⟨mul_tailCapPerBucket_add_lt_maxTailItems hb' (hr'.trans_le (htail.r_le b' hb')),
        fun _ => hr'⟩
  refine ⟨rfl, by rw [hpres.2.1]; omega,
    fun b' hb' => by
      rw [hr_fn b' hb']
      split_ifs
      exacts [by omega, htail.r_le b' hb'],
    fun b' hb' r' hr' => ?_, fun b' hb' r' hr' => ?_, fun t ht' => ?_⟩
  · obtain ⟨hd'_lt, hold⟩ := hslot_info b' hb' r' hr'
    rw [gmTailPtrIdx, hptr_val _ hd'_lt, hpres.2.1]
    split_ifs with hdeq
    · omega
    · have hlt := htail.ptr_lt b' hb' r' (hold hdeq)
      wram_omega [hlt]
  · obtain ⟨hd'_lt, hold⟩ := hslot_info b' hb' r' hr'
    rw [gmTailPtrIdx, hptr_val _ hd'_lt]
    split_ifs with hdeq
    · rw [hown_val (gm 1) ht]
      simp [hdeq]
    · have ht'_lt := htail.ptr_lt b' hb' r' (hold hdeq)
      rw [← gmTailPtrIdx, hown_val _ (lt_trans ht'_lt ht), ite_eq_right (by omega)]
      exact htail.owner_ptr b' hb' r' (hold hdeq)
  · dsimp only
    rw [hpres.2.1] at ht'
    rw [hown_val t (by omega)]
    split_ifs with hteq
    · have ⟨hd, hm⟩ := mul_add_div_mod_of_lt (b := b) hr
      rw [hd, hm, hr_fn b hb, hptr_val _ hd_lt]
      simp [hb, hteq.symm]
    · have ht_old : t < gm 1 := by omega
      obtain ⟨hb_d, hr_d, hptr_d⟩ := htail.owner_valid t ht_old
      set d := gm (gmTailOwnerIdx n_max t)
      have hd_ne : d ≠ d_new := fun heq => by
        obtain ⟨hb_eq, hr_eq⟩ := flat_descriptor_inj
          (hr_d.trans_le (htail.r_le _ hb_d)) hr ((Nat.div_add_mod' d _).trans heq)
        rw [hb_eq, hr_eq] at hr_d
        omega
      refine ⟨hb_d, ?_, ?_⟩
      · rw [hr_fn _ hb_d]
        split_ifs with hbeq
        exacts [Nat.lt_succ_of_lt (hbeq ▸ hr_d), hr_d]
      · rw [hptr_val d (htail.owner_lt_maxTailItems ht_old), ite_eq_right hd_ne, hptr_d]

theorem slabBijection_gmAppendTail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hr : gm (gmRIdx b) < tailCapPerBucket n_max)
    (ht : gm 1 < maxTailItems n_max)
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0)) :
    (∀ b' s, slabPtrOf n_max (gmAppendTail n_max gm b) b' s = slabPtrOf n_max gm b' s) ∧
    SlabBijection n_max (gmAppendTail n_max gm b)
      (fun b' => gmAppendTail n_max gm b (gmQIdx b')) (gmAppendTail n_max gm b 0) := by
  obtain ⟨h0, -, -, -, hq, htop, hdir, hmeta⟩ := gmAppendTail_preserves_nonTail gm hb hr ht
  exact ⟨slabPtrOf_congr_of_slabMeta h0 hmeta, hslab.congr h0 hq htop hdir hmeta⟩

theorem slotOf_gmAppendTail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb_pos : 0 < bucketBits n_max)
    (hb : b < numBuckets n_max)
    (hr : gm (gmRIdx b) < tailCapPerBucket n_max)
    (ht : gm 1 < maxTailItems n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0)) :
    slotOf n_max (gmAppendTail n_max gm b) b (gm (gmQIdx b) * slabSize n_max + gm (gmRIdx b)) =
      n_max - 1 - gm 1 ∧
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max gm b',
      slotOf n_max (gmAppendTail n_max gm b) b' j = slotOf n_max gm b' j) := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hpres := gmAppendTail_preserves_nonTail gm hb hr ht
  obtain ⟨hptr_val, _⟩ := gmAppendTail_tail gm hb hr ht
  have ⟨hptr, _⟩ := slabBijection_gmAppendTail hb hr ht hslab
  refine ⟨?_, fun b' hb' j hj => ?_⟩
  · unfold slotOf
    rw [ite_eq_right hb0, hpres.2.2.2.2.1 b hb, ite_eq_right (by omega),
      Nat.add_sub_cancel_left, gmTailPtrIdx,
      hptr_val _ (mul_tailCapPerBucket_add_lt_maxTailItems hb hr)]
    simp only [↓reduceIte]
  · unfold bCount at hj
    simp only [hb0, ↓reduceIte, hb'] at hj
    unfold slotOf
    rw [ite_eq_right hb0, ite_eq_right hb0, hpres.2.2.2.2.1 b' hb']
    split_ifs with hj_slab
    · rw [hptr]
    · have hr'_cap : j - gm (gmQIdx b') * slabSize n_max < tailCapPerBucket n_max :=
        lt_of_lt_of_le (by omega) (htail.r_le b' hb')
      rw [gmTailPtrIdx, hptr_val _ (mul_tailCapPerBucket_add_lt_maxTailItems hb' hr'_cap),
        ite_eq_right fun heq => by obtain ⟨rfl, _⟩ := flat_descriptor_inj hr'_cap hr heq; omega]

/-- The relocated tail `t_del` and the relinked descriptor `d_last` of `gmRemoveTail` are in
range. -/
private theorem gmRemoveTail_indices_lt {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max) (hr_pos : 1 ≤ gm (gmRIdx b))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)) < maxTailItems n_max ∧
    gm (gmTailOwnerIdx n_max (gm 1 - 1)) < maxTailItems n_max := by
  have hr_del_lt : gm (gmRIdx b) - 1 < gm (gmRIdx b) := by omega
  have ht_del_lt : gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)) < gm 1 :=
    htail.ptr_lt b hb _ hr_del_lt
  exact ⟨lt_of_lt_of_le ht_del_lt htail.ntails_le, htail.owner_lt_maxTailItems (by omega)⟩

theorem gmRemoveTail_preserves_nonTail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max) (hr_pos : 1 ≤ gm (gmRIdx b))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    gmRemoveTail n_max gm b 0 = gm 0 ∧
    gmRemoveTail n_max gm b 1 = gm 1 - 1 ∧
    gmRemoveTail n_max gm b (gmRIdx b) = gm (gmRIdx b) - 1 ∧
    (∀ b' < numBuckets n_max, b' ≠ b → gmRemoveTail n_max gm b (gmRIdx b') = gm (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max, gmRemoveTail n_max gm b (gmQIdx b') = gm (gmQIdx b')) ∧
    (∀ b' < numBuckets n_max, gmRemoveTail n_max gm b (gmSlabTopIdx b') = gm (gmSlabTopIdx b')) ∧
    (∀ b' < numBuckets n_max, ∀ s < dirSlabsPerBucket n_max,
      gmRemoveTail n_max gm b (gmSlabDirIdx n_max b' s) = gm (gmSlabDirIdx n_max b' s)) ∧
    (∀ idx, gmSlabMetaBase n_max ≤ idx → gmRemoveTail n_max gm b idx = gm idx) := by
  obtain ⟨ht_del_max, hd_last_max⟩ := gmRemoveTail_indices_lt hb hr_pos htail
  exact gmTailWrite_preserves_nonTail gm (gm (gmRIdx b) - 1) (gm 1 - 1) hb hd_last_max ht_del_max

theorem gmRemoveTail_tail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max) (hr_pos : 1 ≤ gm (gmRIdx b))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    (∀ d < maxTailItems n_max,
      gmRemoveTail n_max gm b (gmTailPtrFlatIdx n_max d) =
        if d = gm (gmTailOwnerIdx n_max (gm 1 - 1)) then
          gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1))
        else gm (gmTailPtrFlatIdx n_max d)) ∧
    (∀ t < maxTailItems n_max,
      gmRemoveTail n_max gm b (gmTailOwnerIdx n_max t) =
        if t = gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)) then
          gm (gmTailOwnerIdx n_max (gm 1 - 1))
        else gm (gmTailOwnerIdx n_max t)) := by
  obtain ⟨ht_del_max, hd_last_max⟩ := gmRemoveTail_indices_lt hb hr_pos htail
  exact gmTailWrite_tail gm (gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1))) (gm (gmRIdx b) - 1)
    (gm 1 - 1) hb hd_last_max

theorem tailBijection_gmRemoveTail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max) (hr_pos : 1 ≤ gm (gmRIdx b))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    TailBijection n_max (gmRemoveTail n_max gm b)
      (fun b' => gmRemoveTail n_max gm b (gmRIdx b')) (gmRemoveTail n_max gm b 1) := by
  have hpres := gmRemoveTail_preserves_nonTail hb hr_pos htail
  obtain ⟨hptr_val, hown_val⟩ := gmRemoveTail_tail hb hr_pos htail
  set r_del := gm (gmRIdx b) - 1
  set d_del := b * tailCapPerBucket n_max + r_del
  set t_del := gm (gmTailPtrIdx n_max b r_del)
  set t_last := gm 1 - 1
  set d_last := gm (gmTailOwnerIdx n_max t_last)
  have hr_del_cap : r_del < tailCapPerBucket n_max := lt_of_lt_of_le (by omega) (htail.r_le b hb)
  have ht_del_lt : t_del < gm 1 := htail.ptr_lt b hb r_del (by omega)
  have ht_del_max : t_del < maxTailItems n_max := lt_of_lt_of_le ht_del_lt htail.ntails_le
  have ht_last_lt : t_last < gm 1 := by omega
  obtain ⟨hb_last, hr_last, hptr_last⟩ := htail.owner_valid t_last ht_last_lt
  have hown_del : gm (gmTailOwnerIdx n_max t_del) = d_del := htail.owner_ptr b hb r_del (by omega)
  have hr_fn (b' : ℕ) (hb' : b' < numBuckets n_max) :
      gmRemoveTail n_max gm b (gmRIdx b') = if b' = b then r_del else gm (gmRIdx b') := by
    split_ifs with heq
    exacts [heq ▸ hpres.2.2.1, hpres.2.2.2.1 b' hb' heq]
  have hslot_info {b' r' : ℕ} (hb' : b' < numBuckets n_max)
      (hr' : r' < gmRemoveTail n_max gm b (gmRIdx b')) :
      r' < gm (gmRIdx b') ∧ b' * tailCapPerBucket n_max + r' < maxTailItems n_max ∧
      b' * tailCapPerBucket n_max + r' ≠ d_del := by
    rw [hr_fn b' hb'] at hr'
    split_ifs at hr' with heq
    · subst heq
      exact ⟨by omega, mul_tailCapPerBucket_add_lt_maxTailItems hb' (by omega), fun h => by omega⟩
    · have hr'_cap := hr'.trans_le (htail.r_le b' hb')
      exact ⟨hr', mul_tailCapPerBucket_add_lt_maxTailItems hb' hr'_cap,
        fun h => heq (flat_descriptor_inj hr'_cap hr_del_cap h).1⟩
  have howner_r (d : ℕ) (hbd : d / tailCapPerBucket n_max < numBuckets n_max)
      (hrd : d % tailCapPerBucket n_max < gm (gmRIdx (d / tailCapPerBucket n_max)))
      (hne : d ≠ d_del) :
      d % tailCapPerBucket n_max <
        gmRemoveTail n_max gm b (gmRIdx (d / tailCapPerBucket n_max)) := by
    rw [hr_fn _ hbd]
    split_ifs with hbeq
    · rw [hbeq] at hrd
      have : d % tailCapPerBucket n_max ≠ r_del :=
        fun h => hne (by rw [← Nat.div_add_mod' d (tailCapPerBucket n_max), hbeq, h])
      omega
    · exact hrd
  refine ⟨rfl, by rw [hpres.2.1]; have := htail.ntails_le; omega,
    fun b' hb' => by
      rw [hr_fn b' hb']
      split_ifs
      exacts [by have := htail.r_le b hb; omega, htail.r_le b' hb'],
    fun b' hb' r' hr' => ?_, fun b' hb' r' hr' => ?_, fun t ht' => ?_⟩
  · obtain ⟨hr'_old, hd'_lt, hne_del⟩ := hslot_info hb' hr'
    rw [gmTailPtrIdx, hptr_val _ hd'_lt, hpres.2.1]
    split_ifs with hdeq
    · have : t_del ≠ t_last := fun h => hne_del (by rw [hdeq, ← hown_del, h])
      omega
    · have ht'_lt := htail.ptr_lt b' hb' r' hr'_old
      have ht'_ne : gm (gmTailPtrIdx n_max b' r') ≠ t_last := fun h =>
        hdeq (by rw [← htail.owner_ptr b' hb' r' hr'_old, h])
      wram_omega [ht'_lt, ht'_ne]
  · obtain ⟨hr'_old, hd'_lt, hne_del⟩ := hslot_info hb' hr'
    rw [gmTailPtrIdx, hptr_val _ hd'_lt]
    split_ifs with hdeq
    · rw [hown_val t_del ht_del_max]
      simp [hdeq]
    · have ht'_lt := htail.ptr_lt b' hb' r' hr'_old
      have ht'_ne : gm (gmTailPtrIdx n_max b' r') ≠ t_del := fun h =>
        hne_del (by rw [← htail.owner_ptr b' hb' r' hr'_old, h, hown_del])
      rw [← gmTailPtrIdx, hown_val _ (ht'_lt.trans_le htail.ntails_le), ite_eq_right ht'_ne]
      exact htail.owner_ptr b' hb' r' hr'_old
  · dsimp only
    rw [hpres.2.1] at ht'
    have ht_old : t < gm 1 := by omega
    rw [hown_val t (ht_old.trans_le htail.ntails_le)]
    split_ifs with hteq
    · have hne : d_last ≠ d_del := fun heq => by
        have : t_last = t_del :=
          hptr_last.symm.trans (congrArg (fun x => gm (gmTailPtrFlatIdx n_max x)) heq)
        omega
      exact ⟨hb_last, howner_r d_last hb_last hr_last hne,
        by rw [hptr_val d_last (htail.owner_lt_maxTailItems ht_last_lt)]; simp [hteq.symm]⟩
    · obtain ⟨hb_t, hr_t, hptr_t⟩ := htail.owner_valid t ht_old
      set d_t := gm (gmTailOwnerIdx n_max t)
      have hne_del : d_t ≠ d_del := fun heq =>
        hteq (hptr_t.symm.trans (congrArg (fun x => gm (gmTailPtrFlatIdx n_max x)) heq))
      have hne_last : d_t ≠ d_last := fun heq => by
        have : t = t_last := by rw [← hptr_t, heq, hptr_last]
        omega
      exact ⟨hb_t, howner_r d_t hb_t hr_t hne_del,
        by rw [hptr_val d_t (htail.owner_lt_maxTailItems ht_old), ite_eq_right hne_last, hptr_t]⟩

theorem slabBijection_gmRemoveTail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max) (hr_pos : 1 ≤ gm (gmRIdx b))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0)) :
    (∀ b' s, slabPtrOf n_max (gmRemoveTail n_max gm b) b' s = slabPtrOf n_max gm b' s) ∧
    SlabBijection n_max (gmRemoveTail n_max gm b)
      (fun b' => gmRemoveTail n_max gm b (gmQIdx b')) (gmRemoveTail n_max gm b 0) := by
  obtain ⟨h0, -, -, -, hq, htop, hdir, hmeta⟩ := gmRemoveTail_preserves_nonTail hb hr_pos htail
  exact ⟨slabPtrOf_congr_of_slabMeta h0 hmeta, hslab.congr h0 hq htop hdir hmeta⟩

theorem update_slotOf_gmRemoveTail {α : Type*} (arr : ℕ → α) {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb_pos : 0 < bucketBits n_max)
    (hb : b < numBuckets n_max) (hr_pos : 1 ≤ gm (gmRIdx b))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (htot : gm 0 * slabSize n_max + gm 1 ≤ n_max) :
    (∀ b' < numBuckets n_max, ∀ j < bCount n_max (gmRemoveTail n_max gm b) b',
      Function.update arr (n_max - 1 - gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)))
        (arr (n_max - 1 - (gm 1 - 1)))
        (slotOf n_max (gmRemoveTail n_max gm b) b' j) = arr (slotOf n_max gm b' j)) ∧
    (∀ g < n_max - gm 1,
      Function.update arr (n_max - 1 - gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)))
        (arr (n_max - 1 - (gm 1 - 1))) g = arr g) := by
  have hb0 : bucketBits n_max ≠ 0 := by omega
  have hpres := gmRemoveTail_preserves_nonTail hb hr_pos htail
  obtain ⟨hptr_val, _⟩ := gmRemoveTail_tail hb hr_pos htail
  have ⟨hptr, _⟩ := slabBijection_gmRemoveTail hb hr_pos htail hslab
  set r_del := gm (gmRIdx b) - 1
  set t_del := gm (gmTailPtrIdx n_max b r_del)
  set t_last := gm 1 - 1
  have hr_del_cap : r_del < tailCapPerBucket n_max := lt_of_lt_of_le (by omega) (htail.r_le b hb)
  have ht_del_lt : t_del < gm 1 := htail.ptr_lt b hb r_del (by omega)
  have hown_del : gm (gmTailOwnerIdx n_max t_del) = b * tailCapPerBucket n_max + r_del :=
    htail.owner_ptr b hb r_del (by omega)
  have hptr_last := (htail.owner_valid t_last (by omega)).2.2
  refine ⟨fun b' hb' j hj => ?_, fun g hg => Function.update_of_ne (by omega) ..⟩
  unfold bCount at hj; simp only [hb0, ↓reduceIte, hb', hpres.2.2.2.2.1 b' hb'] at hj
  unfold slotOf; rw [ite_eq_right hb0, ite_eq_right hb0, hpres.2.2.2.2.1 b' hb']
  split_ifs with hj_slab
  · rw [hptr]
    have hp_lt : slabPtrOf n_max gm b' (j / slabSize n_max) < gm 0 :=
      hslab.ptr_lt b' hb' _ (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm]))
    exact Function.update_of_ne (by stride_omega [slabSize_pos n_max]) ..
  · set r' := j - gm (gmQIdx b') * slabSize n_max
    have hr'_new : r' < gmRemoveTail n_max gm b (gmRIdx b') := by omega
    have hr'_old : r' < gm (gmRIdx b') := by
      rcases eq_or_ne b' b with rfl | hne
      · rw [hpres.2.2.1] at hr'_new; omega
      · rwa [hpres.2.2.2.1 b' hb' hne] at hr'_new
    have hr'_cap := lt_of_lt_of_le hr'_old (htail.r_le b' hb')
    have hd'_lt := mul_tailCapPerBucket_add_lt_maxTailItems hb' hr'_cap
    rw [gmTailPtrIdx, hptr_val _ hd'_lt]
    split_ifs with hdeq
    · rw [Function.update_self, ← hptr_last, ← hdeq, ← gmTailPtrIdx]
    · have ht'_lt := htail.ptr_lt b' hb' r' hr'_old
      have hne_del : b' * tailCapPerBucket n_max + r' ≠ b * tailCapPerBucket n_max + r_del := by
        intro heq; obtain ⟨rfl, _⟩ := flat_descriptor_inj hr'_cap hr_del_cap heq
        rw [hpres.2.2.1] at hr'_new; omega
      have ht'_ne : gm (gmTailPtrIdx n_max b' r') ≠ t_del := fun heq =>
        hne_del (by rw [← htail.owner_ptr b' hb' r' hr'_old, heq, hown_del])
      exact Function.update_of_ne (by unfold gmTailPtrIdx at ht'_lt ht'_ne; omega) ..

/-! ## Section 2: `Memory.Prog` tail allocation and compaction operations (`realize`) -/

theorem lt_two_pow_globalPtrBits_of_le_n_max {n_max x : ℕ} (hx : x ≤ n_max) :
    x < 2 ^ globalPtrBits n_max := by
  unfold globalPtrBits
  have hpow : n_max + 1 ≤ 2 ^ Nat.clog 2 (n_max + 1) :=
    Nat.le_pow_clog (by decide : 1 < 2) (n_max + 1)
  omega

theorem lt_two_pow_globalPtrBits_of_le_globalMetaLen {n_max x : ℕ}
    (hb_pos : 0 < bucketBits n_max) (hx : x ≤ globalMetaLen n_max) :
    x < 2 ^ globalPtrBits n_max :=
  lt_two_pow_globalPtrBits_of_le_n_max (hx.trans (globalMetaLen_le_of_bucketBits_pos hb_pos))

theorem ntails_lt_maxTailItems_of_r_lt {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hr_lt : gm (gmRIdx b) < tailCapPerBucket n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    gm 1 < maxTailItems n_max := by
  classical
  let d_new := b * tailCapPerBucket n_max + gm (gmRIdx b)
  have hd_new_lt := mul_tailCapPerBucket_add_lt_maxTailItems hb hr_lt
  have hinj : Set.InjOn (fun t => gm (gmTailOwnerIdx n_max t)) (Finset.range (gm 1)) :=
    fun t₁ ht₁ t₂ ht₂ heq =>
      (htail.owner_valid t₁ (Finset.mem_range.mp ht₁)).2.2.symm.trans
        ((congrArg (fun x => gm (gmTailPtrFlatIdx n_max x)) heq).trans
          (htail.owner_valid t₂ (Finset.mem_range.mp ht₂)).2.2)
  have hsub : (Finset.range (gm 1)).image (fun t => gm (gmTailOwnerIdx n_max t)) ⊆
      (Finset.range (maxTailItems n_max)).erase d_new := fun d hd => by
    rcases Finset.mem_image.mp hd with ⟨t, ht, rfl⟩
    rw [Finset.mem_range] at ht
    refine Finset.mem_erase.mpr ⟨fun heq => ?_,
      Finset.mem_range.mpr (htail.owner_lt_maxTailItems ht)⟩
    have hr_t := (htail.owner_valid t ht).2.1
    obtain ⟨hd_eq, hm_eq⟩ := mul_add_div_mod_of_lt (b := b) hr_lt
    rw [heq, hd_eq, hm_eq] at hr_t
    exact Nat.lt_irrefl _ hr_t
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range,
    Finset.card_erase_of_mem (Finset.mem_range.mpr hd_new_lt), Finset.card_range] at hcard
  omega

/-- Base address `d.2.1` in a parameter-free `(DictParams, (base, b))` bucket call. -/
abbrev tailCallBase (d : DictParams × (ℕ × ℕ)) : ℕ := d.2.1

/-- Bucket index `d.2.2` in a parameter-free `(DictParams, (base, b))` bucket call. -/
abbrev tailCallBucket (d : DictParams × (ℕ × ℕ)) : ℕ := d.2.2

/-- Parameter-free `Memory.Prog` operation appending one tail item to bucket `b = tailCallBucket d`
at `base = tailCallBase d`. -/
@[expose]
def appendTailItemGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog ℕ := do
  let r_b ← readGMGenProg (d.1, (tailCallBase d, 4 + 3 * tailCallBucket d + 1))
  let t_new ← readGMGenProg (d.1, (tailCallBase d, 1))
  let d_new := tailCallBucket d * dpTailCap d.1 + r_b
  writeGMGenProg (d.1, ((tailCallBase d, dpGmTailPtrBase d.1 + d_new), t_new))
  writeGMGenProg (d.1, ((tailCallBase d, dpGmTailOwnerBase d.1 + t_new), d_new))
  writeGMGenProg (d.1, ((tailCallBase d, 4 + 3 * tailCallBucket d + 1), r_b + 1))
  let _ ← writeGMGenProg (d.1, ((tailCallBase d, 1), t_new + 1))
  pure t_new

/-- `Memory.Prog` operation appending one tail item to bucket `b = d.2` at `base = d.1`
(`0 < bucketBits n_max`) and returning the newly allocated physical tail offset `t_new = gm 1`. -/
@[expose]
def appendTailItemProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog ℕ :=
  appendTailItemGenProg (mkDictParams U V w n_max h_space, d)

@[simp] theorem appendTailItemGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    appendTailItemGenProg (mkDictParams U V w n_max h_space, d) =
      appendTailItemProg U V w n_max h_space d := by   rfl

@[simp]
theorem memoryCost_appendTailItemProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (appendTailItemProg U V w n_max h_space d) s = 20 := by
  simp [appendTailItemProg, -bind_pure_comp, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    appendTailItemGenProg]

/-- Effect of the four consecutive `writeGMProg` writes corresponding to `gmTailWrite`. -/
private theorem writeGM_tailWrite_effect {U V w n_max h_space base b d t r nt : ℕ}
    (hw : 0 < w) (s : Memory.State)
    (hptr : gmTailPtrBase n_max + d < globalMetaLen n_max) (ht : t < 2 ^ globalPtrBits n_max)
    (hown : gmTailOwnerBase n_max + t < globalMetaLen n_max) (hd : d < 2 ^ globalPtrBits n_max)
    (hri : 4 + 3 * b + 1 < globalMetaLen n_max) (hr : r < 2 ^ globalPtrBits n_max)
    (h1 : 1 < globalMetaLen n_max) (hnt : nt < 2 ^ globalPtrBits n_max) :
    let s₁ := (Memory.spec 0).clientState s
      (writeGMProg U V w n_max h_space ((base, gmTailPtrBase n_max + d), t))
    let s₂ := (Memory.spec 0).clientState s₁
      (writeGMProg U V w n_max h_space ((base, gmTailOwnerBase n_max + t), d))
    let s₃ := (Memory.spec 0).clientState s₂
      (writeGMProg U V w n_max h_space ((base, 4 + 3 * b + 1), r))
    let s₄ := (Memory.spec 0).clientState s₃
      (writeGMProg U V w n_max h_space ((base, 1), nt))
    s₄.frontier = s.frontier ∧
    (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s₄.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s₄.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s₄.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s₄.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s₄.mem =
      gmTailWrite n_max (gmAt base U V w n_max h_space s.mem) b d t r nt := by
  intro s₁ s₂ s₃ s₄
  refine ((gmFrame_writeGMProg hw hptr s).trans ((gmFrame_writeGMProg hw hown s₁).trans
    ((gmFrame_writeGMProg hw hri s₂).trans (gmFrame_writeGMProg hw h1 s₃)))).effect hw ?_
  rw [gmAt_writeGMProg hw h1 hnt s₃, gmAt_writeGMProg hw hri hr s₂,
    gmAt_writeGMProg hw hown hd s₁, gmAt_writeGMProg hw hptr ht s]
  rfl

/-- Pure state effect and return value of `appendTailItemProg`. -/
theorem appendTailItemProg_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (s : Memory.State)
    (htail : TailBijection n_max (gmAt base U V w n_max h_space s.mem)
      (fun b => gmAt base U V w n_max h_space s.mem (gmRIdx b))
      (gmAt base U V w n_max h_space s.mem 1))
    (hr_lt : gmAt base U V w n_max h_space s.mem (gmRIdx b) < tailCapPerBucket n_max) :
    let s' := (Memory.spec 0).clientState s (appendTailItemProg U V w n_max h_space (base, b))
    (Memory.spec 0).clientResult s (appendTailItemProg U V w n_max h_space (base, b)) =
      gmAt base U V w n_max h_space s.mem 1 ∧
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem =
      gmAppendTail n_max (gmAt base U V w n_max h_space s.mem) b := by
  intro s'
  set gm := gmAt base U V w n_max h_space s.mem
  have hr_idx : 4 + 3 * b + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
  have h1_lt : 1 < globalMetaLen n_max := by wram_omega
  have hptr_lt := gmTailPtrIdx_lt hb_pos hb hr_lt
  have ht_cap := ntails_lt_maxTailItems_of_r_lt hb hr_lt htail
  have hmax_le := maxTailItems_le n_max
  have hown_lt := gmTailOwnerIdx_lt hb_pos ht_cap
  have eff := writeGM_tailWrite_effect (U := U) (V := V) (w := w) (h_space := h_space)
    (base := base) (b := b) (d := b * tailCapPerBucket n_max + gm (gmRIdx b)) (t := gm 1)
    (r := gm (gmRIdx b) + 1) (nt := gm 1 + 1) hw s hptr_lt
    (lt_two_pow_globalPtrBits_of_le_n_max (by omega)) hown_lt
    (lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos (by wram_omega [hptr_lt]))
    hr_idx (lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos (by wram_omega [hptr_lt]))
    h1_lt (lt_two_pow_globalPtrBits_of_le_n_max (by omega))
  simp only [s', appendTailItemProg, appendTailItemGenProg, readGMGenProg_mk, writeGMGenProg_mk,
    p_tailCap_mk, p_gmTailPtrBase_mk, p_gmTailOwnerBase_mk]
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    clientState_readGMProg, clientResult_readGMProg s hr_idx,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    clientState_readGMProg, clientResult_readGMProg s h1_lt]
  simp only [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
  exact ⟨rfl, eff⟩

/-- Precondition for `appendTailItemProg`. -/
@[expose]
def AppendTailItemPre (U V w₀ n_max h_space w base b : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  TailBijection n_max (gmAt base U V w₀ n_max h_space s.mem)
    (fun b' => gmAt base U V w₀ n_max h_space s.mem (gmRIdx b'))
    (gmAt base U V w₀ n_max h_space s.mem 1) ∧
  b < numBuckets n_max ∧
  gmAt base U V w₀ n_max h_space s.mem (gmRIdx b) < tailCapPerBucket n_max ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `appendTailItemGenProg`. -/
@[expose]
def AppendTailItemGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let base := tailCallBase d
  let b := tailCallBucket d
  let gm := gmAt base (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  DictEnvGen w d.1 base ∧
  TailBijection (dpNMax d.1) gm (fun b' => gm (gmRIdx b')) (gm 1) ∧
  b < numBuckets (dpNMax d.1) ∧
  gm (gmRIdx b) < tailCapPerBucket (dpNMax d.1) ∧
  0 < bucketBits (dpNMax d.1)

@[simp] theorem appendTailItemGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ)
    (s : Memory.State) :
    AppendTailItemGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      AppendTailItemPre U V w₀ n_max h_space w d.1 d.2 s := Iff.rfl

/-- Bounds for the reads and writes of `appendTailItemProg`, stated on the results of its reads;
shared by `realizes_appendTailItemGen` and `validProg_appendTailItem`. -/
private theorem appendTailItem_bounds {U V w₀ n_max h_space : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (h : TailBijection n_max (gmAt d.1 U V w₀ n_max h_space s.mem)
        (fun b' => gmAt d.1 U V w₀ n_max h_space s.mem (gmRIdx b'))
        (gmAt d.1 U V w₀ n_max h_space s.mem 1) ∧
      d.2 < numBuckets n_max ∧
      gmAt d.1 U V w₀ n_max h_space s.mem (gmRIdx d.2) < tailCapPerBucket n_max ∧
      0 < bucketBits n_max) :
    let r_b := (Memory.spec 0).clientResult s
      (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2 + 1))
    let t_new := (Memory.spec 0).clientResult
      ((Memory.spec 0).clientState s (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2 + 1)))
      (readGMProg U V w₀ n_max h_space (d.1, 1))
    4 + 3 * d.2 + 1 < globalMetaLen n_max ∧
    1 < globalMetaLen n_max ∧
    gmTailPtrBase n_max + (d.2 * tailCapPerBucket n_max + r_b) < globalMetaLen n_max ∧
    gmTailOwnerBase n_max + t_new < globalMetaLen n_max ∧
    r_b + 1 ≤ globalMetaLen n_max ∧
    t_new + 1 ≤ max n_max 1 := by
  rcases h with ⟨htail, hb, hr_lt, hb_pos⟩
  have hr_idx : 4 + 3 * d.2 + 1 < globalMetaLen n_max := gmRIdx_lt hb_pos hb
  have h1_idx : 1 < globalMetaLen n_max := by wram_omega
  have ht_cap := ntails_lt_maxTailItems_of_r_lt hb hr_lt htail
  have hmax_le := maxTailItems_le n_max
  have hcap_le := tailCapPerBucket_le_globalMetaLen hb_pos
  intro r_b t_new; dsimp only [r_b, t_new]
  rw [clientState_readGMProg, clientResult_readGMProg s hr_idx, clientResult_readGMProg s h1_idx]
  exact ⟨hr_idx, h1_idx, gmTailPtrIdx_lt hb_pos hb hr_lt, gmTailOwnerIdx_lt hb_pos ht_cap,
    by change gmAt d.1 U V w₀ n_max h_space s.mem (gmRIdx d.2) + 1 ≤ _; omega, by omega⟩

theorem realizes_appendTailItemGen :
    Realizes .exact appendTailItemGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      AppendTailItemGenPre
      (fun _ _ => 0) := by
  realizeDictWith [appendTailItemGenPre_mk, tailCallBase, tailCallBucket] using
    [realizes_readGMGen, realizes_writeGMGen]
  all_goals
    obtain ⟨hdict, h2⟩ := h
    have hb_pos := h2.2.2.2
    rcases appendTailItem_bounds h2 with ⟨hr_i, h1_i, hptr_i, hown_i, hr1_le, ht1_le⟩
    first
    | dictSide
    | exact fits_of_le_globalMetaLen hdict hb_pos hw hnU hU (by omega)

/-- Parameter-free `Memory.Prog` operation removing the last tail item of bucket
`b = tailCallBucket d` at `base = tailCallBase d`. -/
@[expose]
def removeLastTailItemGenProg (d : DictParams × (ℕ × ℕ)) : Memory.Prog Unit := do
  let r_b ← readGMGenProg (d.1, (tailCallBase d, 4 + 3 * tailCallBucket d + 1))
  let r_del := r_b - 1
  let t_del ← readGMGenProg (d.1,
    (tailCallBase d, dpGmTailPtrBase d.1 + (tailCallBucket d * dpTailCap d.1 + r_del)))
  let n_tails ← readGMGenProg (d.1, (tailCallBase d, 1))
  let t_last := n_tails - 1
  let d_last ← readGMGenProg (d.1, (tailCallBase d, dpGmTailOwnerBase d.1 + t_last))
  let g_last := dpNMaxSubOne d.1 - t_last
  let g_del := dpNMaxSubOne d.1 - t_del
  let q_move ← readQuotGenProg (d.1, (tailCallBase d, g_last))
  writeQuotGenProg (d.1, ((tailCallBase d, g_del), q_move))
  let v_move ← readValGenProg (d.1, (tailCallBase d, g_last))
  writeValGenProg (d.1, ((tailCallBase d, g_del), v_move))
  writeGMGenProg (d.1, ((tailCallBase d, dpGmTailPtrBase d.1 + d_last), t_del))
  writeGMGenProg (d.1, ((tailCallBase d, dpGmTailOwnerBase d.1 + t_del), d_last))
  writeGMGenProg (d.1, ((tailCallBase d, 4 + 3 * tailCallBucket d + 1), r_del))
  writeGMGenProg (d.1, ((tailCallBase d, 1), t_last))

/-- `Memory.Prog` operation removing the last tail item of bucket `b = d.2` at `base = d.1`
(`0 < bucketBits n_max`, `1 ≤ gm (gmRIdx b)`), compacting the tail pool by moving the payload at
physical slot `(n_max - 1) - (gm 1 - 1)` into `(n_max - 1) - t_del` and updating `GlobalMeta` via
`gmRemoveTail`. -/
@[expose]
def removeLastTailItemProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ) : Memory.Prog Unit :=
  removeLastTailItemGenProg (mkDictParams U V w n_max h_space, d)

@[simp] theorem removeLastTailItemGenProg_mk (U V w n_max h_space : ℕ) (d : ℕ × ℕ) :
    removeLastTailItemGenProg (mkDictParams U V w n_max h_space, d) =
      removeLastTailItemProg U V w n_max h_space d := by   rfl

@[simp]
theorem memoryCost_removeLastTailItemProg (U V w n_max h_space : ℕ) (d : ℕ × ℕ)
    (s : Memory.State) :
    memoryCost (removeLastTailItemProg U V w n_max h_space d) s = 36 := by
  simp [removeLastTailItemProg, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    removeLastTailItemGenProg]

/-- Shared index-range facts for `gmRemoveTail` in `removeLastTailItemProg_effect` and
`removeLastTailItem_bounds`. -/
private theorem gmRemoveTail_idxBounds {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max) (hr_pos : 1 ≤ gm (gmRIdx b))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    let r_del := gm (gmRIdx b) - 1
    let t_del := gm (gmTailPtrIdx n_max b r_del)
    let t_last := gm 1 - 1
    let d_last := gm (gmTailOwnerIdx n_max t_last)
    4 + 3 * b + 1 < globalMetaLen n_max ∧
    gmTailPtrBase n_max + (b * tailCapPerBucket n_max + r_del) < globalMetaLen n_max ∧
    1 < globalMetaLen n_max ∧
    1 ≤ gm 1 ∧ gm 1 ≤ n_max ∧ t_del < gm 1 ∧
    gmTailOwnerBase n_max + t_last < globalMetaLen n_max ∧
    gmTailPtrBase n_max + d_last < globalMetaLen n_max ∧
    gmTailOwnerBase n_max + t_del < globalMetaLen n_max := by
  have ht_del_lt : gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)) < gm 1 :=
    htail.ptr_lt b hb _ (by omega)
  have ht_del_max : _ < maxTailItems n_max := lt_of_lt_of_le ht_del_lt htail.ntails_le
  have ht_last_max : gm 1 - 1 < maxTailItems n_max := lt_of_lt_of_le (by omega) htail.ntails_le
  exact ⟨gmRIdx_lt hb_pos hb,
    gmTailPtrIdx_lt hb_pos hb (lt_of_lt_of_le (by omega) (htail.r_le b hb)),
    by wram_omega, by omega, htail.ntails_le.trans (maxTailItems_le n_max), ht_del_lt,
    gmTailOwnerIdx_lt hb_pos ht_last_max,
    gmTailPtrFlatIdx_lt hb_pos (htail.owner_lt_maxTailItems (by omega)),
    gmTailOwnerIdx_lt hb_pos ht_del_max⟩

/-- Pure state effect of `removeLastTailItemProg`. -/
theorem removeLastTailItemProg_effect {U V w n_max h_space base b : ℕ}
    (hw : 0 < w) (hb_pos : 0 < bucketBits n_max) (hb : b < numBuckets n_max)
    (s : Memory.State)
    (htail : TailBijection n_max (gmAt base U V w n_max h_space s.mem)
      (fun b => gmAt base U V w n_max h_space s.mem (gmRIdx b))
      (gmAt base U V w n_max h_space s.mem 1))
    (hr_pos : 1 ≤ gmAt base U V w n_max h_space s.mem (gmRIdx b)) :
    let gm := gmAt base U V w n_max h_space s.mem
    let s' := (Memory.spec 0).clientState s (removeLastTailItemProg U V w n_max h_space (base, b))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offQuot h_space ≤ a ∧
        a < base + totalSpace U V w n_max h_space) → s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem =
      Function.update (quotAt base U w n_max h_space s.mem)
        (n_max - 1 - gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)))
        (quotAt base U w n_max h_space s.mem (n_max - 1 - (gm 1 - 1))) ∧
    valAt base U V w n_max h_space s'.mem =
      Function.update (valAt base U V w n_max h_space s.mem)
        (n_max - 1 - gm (gmTailPtrIdx n_max b (gm (gmRIdx b) - 1)))
        (valAt base U V w n_max h_space s.mem (n_max - 1 - (gm 1 - 1))) ∧
    lmAt base U V w n_max h_space s'.mem = lmAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmRemoveTail n_max gm b := by
  intro gm s'
  have ⟨hr_idx, hptr_del, h1_lt, hgm1_pos, hnt_le, ht_del_lt, hown_last, hptr_last, hown_del⟩ :=
    gmRemoveTail_idxBounds hb_pos hb hr_pos htail
  set r_del := gm (gmRIdx b) - 1
  set t_del := gm (gmTailPtrIdx n_max b r_del)
  set t_last := gm 1 - 1
  set d_last := gm (gmTailOwnerIdx n_max t_last)
  set g_last := n_max - 1 - t_last
  set g_del := n_max - 1 - t_del
  obtain ⟨hf1, hout1, hq1, hv1, hl1, hg1⟩ :=
    writeQuotProg_effect (base := base) (U := U) (V := V) (w := w) (h_space := h_space)
      hw (by omega : g_del < n_max) (quotAt_lt ..) s
  let s₁ := (Memory.spec 0).clientState s
    (writeQuotProg U w n_max h_space ((base, g_del), quotAt base U w n_max h_space s.mem g_last))
  obtain ⟨hf2, hout2, hq2, hv2, hl2, hg2⟩ :=
    writeValProg_effect (base := base) (U := U) (V := V) (w := w) (h_space := h_space)
      hw (by omega : g_del < n_max) (valAt_lt (mem := s₁.mem) (idx := g_last) ..) s₁
  let s₂ := (Memory.spec 0).clientState s₁
    (writeValProg U V w n_max h_space ((base, g_del), valAt base U V w n_max h_space s₁.mem g_last))
  have ht_del_le : t_del ≤ n_max := le_trans (le_of_lt ht_del_lt) hnt_le
  have ht_last_le : t_last ≤ n_max := le_trans (Nat.sub_le _ _) hnt_le
  obtain ⟨hf3, hout3, hq3, hv3, hl3, hg3⟩ :=
    writeGM_tailWrite_effect (U := U) (V := V) (w := w) (h_space := h_space) (base := base)
      (b := b) (d := d_last) (t := t_del) (r := r_del) (nt := t_last) hw s₂ hptr_last
      (lt_two_pow_globalPtrBits_of_le_n_max ht_del_le) hown_del
      (lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos (by wram_omega [hptr_last])) hr_idx
      (lt_two_pow_globalPtrBits_of_le_globalMetaLen hb_pos (by wram_omega [hptr_del])) h1_lt
      (lt_two_pow_globalPtrBits_of_le_n_max ht_last_le)
  let wGM idx val := writeGMProg U V w n_max h_space ((base, idx), val)
  have hst : s' = (Memory.spec 0).clientState
      ((Memory.spec 0).clientState
        ((Memory.spec 0).clientState ((Memory.spec 0).clientState s₂
          (wGM (gmTailPtrBase n_max + d_last) t_del)) (wGM (gmTailOwnerBase n_max + t_del) d_last))
        (wGM (4 + 3 * b + 1) r_del)) (wGM 1 t_last) := by
    simp only [s', wGM, removeLastTailItemProg, removeLastTailItemGenProg, readGMGenProg_mk,
      writeGMGenProg_mk, readQuotGenProg_mk, writeQuotGenProg_mk, readValGenProg_mk,
      writeValGenProg_mk, p_tailCap_mk, p_gmTailPtrBase_mk, p_gmTailOwnerBase_mk, p_nMaxSubOne_mk]
    have hptr_del' : gmTailPtrBase n_max +
        (b * tailCapPerBucket n_max + (gm (4 + 3 * b + 1) - 1)) < _ := hptr_del
    rw [StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s hr_idx, StateTransitionSpec.clientState_bind,
      clientState_readGMProg, clientResult_readGMProg s hptr_del',
      StateTransitionSpec.clientState_bind, clientState_readGMProg, clientResult_readGMProg s h1_lt,
      StateTransitionSpec.clientState_bind, clientState_readGMProg,
      clientResult_readGMProg s hown_last, StateTransitionSpec.clientState_bind,
      clientState_readQuotProg, clientResult_readQuotProg s (by omega : g_last < n_max),
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      clientState_readValProg, clientResult_readValProg _ (by omega : g_last < n_max)]
    repeat rw [StateTransitionSpec.clientState_bind]
    rfl
  rw [hst]
  exact ⟨by rw [hf3, hf2, hf1],
    fun a ha => by
      rw [hout3 a (by wram_omega [ha]), hout2 a (by wram_omega [ha]), hout1 a (by wram_omega [ha])],
    by rw [hq3, hq2, hq1], by rw [hv3, hv2, hv1], by rw [hl3, hl2, hl1],
    by rw [hg3, hg2, hg1]; rfl⟩

/-- Precondition for `removeLastTailItemProg`. -/
@[expose]
def RemoveLastTailItemPre (U V w₀ n_max h_space w base b : ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) base ∧
  TailBijection n_max (gmAt base U V w₀ n_max h_space s.mem)
    (fun b' => gmAt base U V w₀ n_max h_space s.mem (gmRIdx b'))
    (gmAt base U V w₀ n_max h_space s.mem 1) ∧
  b < numBuckets n_max ∧
  1 ≤ gmAt base U V w₀ n_max h_space s.mem (gmRIdx b) ∧
  0 < bucketBits n_max

/-- Parameter-free precondition for `removeLastTailItemGenProg`. -/
@[expose]
def RemoveLastTailItemGenPre (w : ℕ) (d : DictParams × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let base := tailCallBase d
  let b := tailCallBucket d
  let gm := gmAt base (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem
  DictEnvGen w d.1 base ∧
  TailBijection (dpNMax d.1) gm (fun b' => gm (gmRIdx b')) (gm 1) ∧
  b < numBuckets (dpNMax d.1) ∧
  1 ≤ gm (gmRIdx b) ∧
  0 < bucketBits (dpNMax d.1)

@[simp] theorem removeLastTailItemGenPre_mk (U V w₀ n_max h_space w : ℕ) (d : ℕ × ℕ)
    (s : Memory.State) :
    RemoveLastTailItemGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      RemoveLastTailItemPre U V w₀ n_max h_space w d.1 d.2 s := Iff.rfl

/-- Bounds for the reads and writes of `removeLastTailItemProg`, stated on the results of its
reads; shared by `realizes_removeLastTailItemGen` and `validProg_removeLastTailItem`. -/
private theorem removeLastTailItem_bounds {U V w₀ n_max h_space : ℕ} {d : ℕ × ℕ}
    {s : Memory.State}
    (h : TailBijection n_max (gmAt d.1 U V w₀ n_max h_space s.mem)
        (fun b' => gmAt d.1 U V w₀ n_max h_space s.mem (gmRIdx b'))
        (gmAt d.1 U V w₀ n_max h_space s.mem 1) ∧
      d.2 < numBuckets n_max ∧
      1 ≤ gmAt d.1 U V w₀ n_max h_space s.mem (gmRIdx d.2) ∧
      0 < bucketBits n_max) :
    let e_rb := (Memory.spec 0).clientResult s
      (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2 + 1))
    let s1 := (Memory.spec 0).clientState s
      (readGMProg U V w₀ n_max h_space (d.1, 4 + 3 * d.2 + 1))
    let e_ptr_del_idx := gmTailPtrBase n_max + (d.2 * tailCapPerBucket n_max + (e_rb - 1))
    let e_tdel := (Memory.spec 0).clientResult s1
      (readGMProg U V w₀ n_max h_space (d.1, e_ptr_del_idx))
    let s2 := (Memory.spec 0).clientState s1
      (readGMProg U V w₀ n_max h_space (d.1, e_ptr_del_idx))
    let e_ntails := (Memory.spec 0).clientResult s2
      (readGMProg U V w₀ n_max h_space (d.1, 1))
    let s3 := (Memory.spec 0).clientState s2
      (readGMProg U V w₀ n_max h_space (d.1, 1))
    let e_own_last_idx := gmTailOwnerBase n_max + (e_ntails - 1)
    let e_dlast := (Memory.spec 0).clientResult s3
      (readGMProg U V w₀ n_max h_space (d.1, e_own_last_idx))
    4 + 3 * d.2 + 1 < globalMetaLen n_max ∧
    1 ≤ e_rb ∧
    e_ptr_del_idx < globalMetaLen n_max ∧
    1 < globalMetaLen n_max ∧
    1 ≤ e_ntails ∧
    e_own_last_idx < globalMetaLen n_max ∧
    e_ntails - 1 ≤ n_max - 1 ∧
    e_tdel ≤ n_max - 1 ∧
    n_max - 1 - (e_ntails - 1) < n_max ∧
    n_max - 1 - e_tdel < n_max ∧
    gmTailPtrBase n_max + e_dlast < globalMetaLen n_max ∧
    gmTailOwnerBase n_max + e_tdel < globalMetaLen n_max := by
  rcases h with ⟨htail, hb, hr_pos, hb_pos⟩
  have ⟨hr_idx, hptr_del, h1_lt, hgm1_pos, hnt_le, ht_del_lt, hown_last, hptr_last, hown_del⟩ :=
    gmRemoveTail_idxBounds hb_pos hb hr_pos htail
  intro e_rb s1 e_ptr_del_idx e_tdel s2 e_ntails s3 e_own_last_idx e_dlast
  dsimp only [e_dlast, e_own_last_idx, s3, e_ntails, s2, e_tdel, e_ptr_del_idx, s1, e_rb]
  unfold gmTailPtrIdx gmTailPtrFlatIdx gmRIdx at ht_del_lt
  unfold gmRIdx at hptr_del
  repeat rw [clientState_readGMProg]
  rw [clientResult_readGMProg s hr_idx, clientResult_readGMProg s hptr_del,
    clientResult_readGMProg s h1_lt, clientResult_readGMProg s hown_last]
  exact ⟨hr_idx, hr_pos, hptr_del, h1_lt, hgm1_pos, hown_last,
    by omega, by omega, by omega, by omega, hptr_last, hown_del⟩

theorem realizes_removeLastTailItemGen :
    Realizes .exact removeLastTailItemGenProg
      (WordEncoding.encode (α := DictParams × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      RemoveLastTailItemGenPre
      (fun _ _ => 0) := by
  realizeDictWith [removeLastTailItemGenPre_mk, tailCallBase, tailCallBucket] using
    [realizes_readGMGen, realizes_writeGMGen, realizes_readQuotGen, realizes_writeQuotGen,
      realizes_readValGen, realizes_writeValGen]
  all_goals
    obtain ⟨hdict, h2⟩ := h
    have hb_pos := h2.2.2.2
    rcases removeLastTailItem_bounds h2 with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩
    dictSide

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
