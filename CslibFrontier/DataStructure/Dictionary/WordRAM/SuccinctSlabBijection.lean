/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.WramOmega

/-!
# Pure Slab Bijection Preservation (`gmPushSlab`, `gmPopSlab`)

This module defines the pure `GlobalMeta` slab-stack updates (`gmPushSlab`, `gmUnlinkTopSlab`,
`gmCompactSlab`, `gmPopSlab`) and proves that they preserve `SlabBijection` and `TailBijection`
when promoting or demoting a full slab of `K = slabSize n_max` items.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmPushSlab`: pure `GlobalMeta` update
  allocating a new full slab as the top slab of bucket `b`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmUnlinkTopSlab`: Stage A of slab pop,
  unlinking the top slab of bucket `b`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmCompactSlab`: Stage B of slab pop,
  compacting the physical slab pool into the vacated slab `p_del`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmPopSlab`: composite `GlobalMeta` update
  popping the top slab of bucket `b` and compacting the slab pool.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmPushSlab_fields`: field-by-field description
  of `gmPushSlab`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.tailBijection_gmPushSlab`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.slabBijection_gmPushSlab`: `gmPushSlab`
  preserves `TailBijection` and `SlabBijection`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmUnlinkTopSlab_fields`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.gmCompactSlab_fields_lt`: field-by-field
  descriptions of the two stages of `gmPopSlab`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.tailBijection_gmPopSlab`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.slabBijection_gmPopSlab`: `gmPopSlab`
  preserves `TailBijection` and `SlabBijection`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Finset

theorem nslabs_lt_maxFullSlabs_of_mul_le {n_max n_slabs : ℕ}
    (hb_pos : 0 < bucketBits n_max)
    (hle : (n_slabs + 1) * slabSize n_max ≤ n_max) :
    n_slabs < maxFullSlabs n_max := by
  unfold maxFullSlabs
  rw [ite_eq_right (by omega)]
  stride_omega [slabSize_pos n_max]

theorem slabPtrOf_inj {n_max : ℕ} {gm q_fn : ℕ → ℕ} {n_slabs : ℕ}
    (hslab : SlabBijection n_max gm q_fn n_slabs)
    {b₁ : ℕ} (hb₁ : b₁ < numBuckets n_max) {s₁ : ℕ} (hs₁ : s₁ < q_fn b₁)
    {b₂ : ℕ} (hb₂ : b₂ < numBuckets n_max) {s₂ : ℕ} (hs₂ : s₂ < q_fn b₂)
    (heq : slabPtrOf n_max gm b₁ s₁ = slabPtrOf n_max gm b₂ s₂) :
    b₁ = b₂ ∧ s₁ = s₂ :=
  ⟨by rw [← hslab.ownerB_ptr b₁ hb₁ s₁ hs₁, heq, hslab.ownerB_ptr b₂ hb₂ s₂ hs₂],
   by rw [← hslab.ownerS_ptr b₁ hb₁ s₁ hs₁, heq, hslab.ownerS_ptr b₂ hb₂ s₂ hs₂]⟩

private theorem slabBijection_of_ptr {n_max : ℕ} {gm : ℕ → ℕ} (f : ℕ → ℕ → ℕ)
    (hle : gm 0 ≤ maxFullSlabs n_max)
    (hf_lt : ∀ b < numBuckets n_max, ∀ s < gm (gmQIdx b), f b s < gm 0)
    (hf_ownB : ∀ b < numBuckets n_max, ∀ s < gm (gmQIdx b),
      gm (gmSlabOwnerBIdx n_max (f b s)) = b)
    (hf_ownS : ∀ b < numBuckets n_max, ∀ s < gm (gmQIdx b),
      gm (gmSlabOwnerSIdx n_max (f b s)) = s)
    (hown_valid : ∀ p < gm 0,
      gm (gmSlabOwnerBIdx n_max p) < numBuckets n_max ∧
      gm (gmSlabOwnerSIdx n_max p) < gm (gmQIdx (gm (gmSlabOwnerBIdx n_max p))) ∧
      f (gm (gmSlabOwnerBIdx n_max p)) (gm (gmSlabOwnerSIdx n_max p)) = p)
    (hdir : ∀ b < numBuckets n_max, ∀ s < gm (gmQIdx b),
      s < dirSlabsPerBucket n_max → gm (gmSlabDirIdx n_max b s) = f b s)
    (htop : ∀ b < numBuckets n_max, ∀ s < gm (gmQIdx b),
      s + 1 = gm (gmQIdx b) → gm (gmSlabTopIdx b) = f b s)
    (hbel : ∀ b < numBuckets n_max, ∀ s < gm (gmQIdx b),
      0 < s → gm (gmSlabBelowIdx n_max (f b s)) = f b (s - 1))
    (habv : ∀ b < numBuckets n_max, ∀ s < gm (gmQIdx b),
      s + 1 < gm (gmQIdx b) → gm (gmSlabAboveIdx n_max (f b s)) = f b (s + 1)) :
    (∀ b < numBuckets n_max, ∀ s < gm (gmQIdx b), slabPtrOf n_max gm b s = f b s) ∧
    SlabBijection n_max gm (fun b => gm (gmQIdx b)) (gm 0) := by
  have hinj : ∀ p₁ < gm 0, ∀ p₂ < gm 0,
      gm (gmSlabOwnerBIdx n_max p₁) = gm (gmSlabOwnerBIdx n_max p₂) →
      gm (gmSlabOwnerSIdx n_max p₁) = gm (gmSlabOwnerSIdx n_max p₂) → p₁ = p₂ := by
    intro p₁ hp₁ p₂ hp₂ hB hS
    rw [← (hown_valid p₁ hp₁).2.2, ← (hown_valid p₂ hp₂).2.2, hB, hS]
  have hptr : ∀ b < numBuckets n_max, ∀ s < gm (gmQIdx b), slabPtrOf n_max gm b s = f b s :=
    fun b hb s hs =>
      slabPtrOf_eq_of_owner (hf_lt b hb s hs) (hf_ownB b hb s hs) (hf_ownS b hb s hs) hinj
  refine ⟨hptr, ⟨rfl, hle,
    fun b hb s hs => hptr b hb s hs ▸ hf_lt b hb s hs,
    fun b hb s hs => hptr b hb s hs ▸ hf_ownB b hb s hs,
    fun b hb s hs => hptr b hb s hs ▸ hf_ownS b hb s hs,
    fun p hp =>
      let ⟨hb, hs, heq⟩ := hown_valid p hp
      ⟨hb, hs, (hptr _ hb _ hs).trans heq⟩,
    fun b hb s hs hd => (hdir b hb s hs hd).trans (hptr b hb s hs).symm,
    fun b hb s hs ht => (htop b hb s hs ht).trans (hptr b hb s hs).symm,
    fun b hb s hs hpos =>
      hptr b hb s hs ▸ hptr b hb (s - 1) ((Nat.sub_le s 1).trans_lt hs) ▸ hbel b hb s hs hpos,
    fun b hb s hs ha => hptr b hb s hs ▸ hptr b hb (s + 1) ha ▸ habv b hb s hs ha⟩⟩

/-- Shared verification step for `below_eq` and `above_eq` after relocating `p_last` to `p_del`. -/
private theorem gmCompactSlab_link_eq {n_max : ℕ} {gm : ℕ → ℕ}
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    {b_last s_last p_last p_del : ℕ}
    (hb_last : b_last < numBuckets n_max) (hs_last : s_last < gm (gmQIdx b_last))
    (hptr_last : slabPtrOf n_max gm b_last s_last = p_last)
    {fwd' fwd : ℕ → ℕ} {adjCond : Prop} [Decidable adjCond] {bwd_last : ℕ}
    (hfwd' : ∀ p, fwd' p = if p = p_del then fwd p_last
      else if adjCond ∧ p = bwd_last then p_del else fwd p)
    {b' s₁ s₂ : ℕ} (hb' : b' < numBuckets n_max)
    (hs₁ : s₁ < gm (gmQIdx b')) (hs₂ : s₂ < gm (gmQIdx b')) (hne_s : s₁ ≠ s₂)
    (hne_del : slabPtrOf n_max gm b' s₁ ≠ p_del)
    (hfwd_old : fwd (slabPtrOf n_max gm b' s₁) = slabPtrOf n_max gm b' s₂)
    (hadj_of : b' = b_last → s₂ = s_last → adjCond)
    (hbwd : adjCond → ∃ s_a < gm (gmQIdx b_last),
      bwd_last = slabPtrOf n_max gm b_last s_a ∧ (s₁ = s_a ↔ s₂ = s_last)) :
    fwd' (if slabPtrOf n_max gm b' s₁ = p_last then p_del else slabPtrOf n_max gm b' s₁) =
      if slabPtrOf n_max gm b' s₂ = p_last then p_del else slabPtrOf n_max gm b' s₂ := by
  have hiff : ∀ s < gm (gmQIdx b'),
      slabPtrOf n_max gm b' s = p_last ↔ b' = b_last ∧ s = s_last := fun s hs =>
    ⟨fun h => slabPtrOf_inj hslab hb' hs hb_last hs_last (h.trans hptr_last.symm),
     by rintro ⟨rfl, rfl⟩; exact hptr_last⟩
  by_cases h1 : slabPtrOf n_max gm b' s₁ = p_last
  · obtain ⟨rfl, rfl⟩ := (hiff s₁ hs₁).mp h1
    have hne2 : slabPtrOf n_max gm b' s₂ ≠ p_last := fun h =>
      hne_s ((hiff s₂ hs₂).mp h).2.symm
    rw [ite_eq_left h1, ite_eq_right hne2, hfwd', ite_eq_left rfl, ← hptr_last, hfwd_old]
  · rw [ite_eq_right h1, hfwd', ite_eq_right hne_del]
    by_cases h2 : slabPtrOf n_max gm b' s₂ = p_last
    · obtain ⟨rfl, hs2⟩ := (hiff s₂ hs₂).mp h2
      have hcond := hadj_of rfl hs2
      obtain ⟨s_a, -, hbwd_eq, heqv⟩ := hbwd hcond
      rw [ite_eq_left h2, ite_eq_left ⟨hcond, by rw [hbwd_eq, heqv.mpr hs2]⟩]
    · have hnot : ¬(adjCond ∧ slabPtrOf n_max gm b' s₁ = bwd_last) := by
        rintro ⟨hc, heq⟩
        obtain ⟨s_a, hsa, hbwd_eq, heqv⟩ := hbwd hc
        obtain ⟨rfl, hs1⟩ := slabPtrOf_inj hslab hb' hs₁ hb_last hsa (heq.trans hbwd_eq)
        exact h2 ((hiff s₂ hs₂).mpr ⟨rfl, heqv.mp hs1⟩)
      rw [ite_eq_right h2, ite_eq_right hnot, hfwd_old]

/-! ## Section 1: Pure `gmPushSlab` and `SlabBijection` preservation -/

/-- Pure `GlobalMeta` update allocating a new full slab `p_new = gm 0` as the new top slab
`s_new = gm (gmQIdx b)` of bucket `b`. -/
@[expose]
def gmPushSlab (n_max : ℕ) (gm : ℕ → ℕ) (b : ℕ) : ℕ → ℕ :=
  let q_b := gm (gmQIdx b)
  let p_new := gm 0
  let top_old := gm (gmSlabTopIdx b)
  let gm₁ := Function.update
    (Function.update
      (Function.update gm (gmSlabOwnerBIdx n_max p_new) b)
      (gmSlabOwnerSIdx n_max p_new) q_b)
    (gmSlabBelowIdx n_max p_new) top_old
  let gm₂ := if 0 < q_b then Function.update gm₁ (gmSlabAboveIdx n_max top_old) p_new else gm₁
  let gm₃ := if q_b < dirSlabsPerBucket n_max then
    Function.update gm₂ (gmSlabDirIdx n_max b q_b) p_new else gm₂
  Function.update
    (Function.update
      (Function.update gm₃ (gmSlabTopIdx b) p_new)
      (gmQIdx b) (q_b + 1))
    0 (p_new + 1)

/-- Field-by-field description of `gmPushSlab` across all `GlobalMeta` sub-arrays. -/
theorem gmPushSlab_fields {n_max : ℕ} (gm : ℕ → ℕ) {b : ℕ} (hb : b < numBuckets n_max) :
    gmPushSlab n_max gm b 0 = gm 0 + 1 ∧
    gmPushSlab n_max gm b 1 = gm 1 ∧
    (∀ b' < numBuckets n_max, gmPushSlab n_max gm b (gmRIdx b') = gm (gmRIdx b')) ∧
    (∀ idx, gmTailPtrBase n_max ≤ idx → idx < gmSlabMetaBase n_max →
      gmPushSlab n_max gm b idx = gm idx) ∧
    (∀ b' < numBuckets n_max,
      gmPushSlab n_max gm b (gmQIdx b') =
        if b' = b then gm (gmQIdx b) + 1 else gm (gmQIdx b')) ∧
    (∀ b' < numBuckets n_max,
      gmPushSlab n_max gm b (gmSlabTopIdx b') =
        if b' = b then gm 0 else gm (gmSlabTopIdx b')) ∧
    (∀ b' < numBuckets n_max, ∀ s < dirSlabsPerBucket n_max,
      gmPushSlab n_max gm b (gmSlabDirIdx n_max b' s) =
        if b' = b ∧ s = gm (gmQIdx b) then gm 0 else gm (gmSlabDirIdx n_max b' s)) ∧
    (∀ p, gmPushSlab n_max gm b (gmSlabOwnerBIdx n_max p) =
      if p = gm 0 then b else gm (gmSlabOwnerBIdx n_max p)) ∧
    (∀ p, gmPushSlab n_max gm b (gmSlabOwnerSIdx n_max p) =
      if p = gm 0 then gm (gmQIdx b) else gm (gmSlabOwnerSIdx n_max p)) ∧
    (∀ p, gmPushSlab n_max gm b (gmSlabBelowIdx n_max p) =
      if p = gm 0 then gm (gmSlabTopIdx b) else gm (gmSlabBelowIdx n_max p)) ∧
    (∀ p, gmPushSlab n_max gm b (gmSlabAboveIdx n_max p) =
      if 0 < gm (gmQIdx b) ∧ p = gm (gmSlabTopIdx b) then gm 0
      else gm (gmSlabAboveIdx n_max p)) :=
  ⟨by update_simp [gmPushSlab], by update_simp [gmPushSlab],
    fun _ _ => by update_simp [gmPushSlab],
    fun _ _ _ => by update_simp [gmPushSlab],
    fun b' _ => by by_cases h : b' = b <;> update_simp [gmPushSlab],
    fun b' _ => by by_cases h : b' = b <;> update_simp [gmPushSlab],
    fun b' _ s _ => by by_cases h : b' = b ∧ s = gm (gmQIdx b) <;> update_simp [gmPushSlab],
    fun p => by by_cases h : p = gm 0 <;> update_simp [gmPushSlab],
    fun p => by by_cases h : p = gm 0 <;> update_simp [gmPushSlab],
    fun p => by by_cases h : p = gm 0 <;> update_simp [gmPushSlab],
    fun p => by
      by_cases h : 0 < gm (gmQIdx b) ∧ p = gm (gmSlabTopIdx b) <;> update_simp [gmPushSlab]⟩

/-- `gmPushSlab` preserves `TailBijection`. -/
theorem tailBijection_gmPushSlab {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    TailBijection n_max (gmPushSlab n_max gm b)
      (fun b' => gmPushSlab n_max gm b (gmRIdx b')) (gmPushSlab n_max gm b 1) := by
  obtain ⟨-, h1, hr, hmeta, -⟩ := gmPushSlab_fields gm hb
  exact htail.congr h1 hr hmeta

/-- `gmPushSlab` assigns physical slab `gm 0` to `(b, gm (gmQIdx b))` and preserves
`SlabBijection`. -/
theorem slabBijection_gmPushSlab {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hp_lt : gm 0 < maxFullSlabs n_max)
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0)) :
    let gm' := gmPushSlab n_max gm b
    (∀ b' < numBuckets n_max, ∀ s < gm' (gmQIdx b'),
      slabPtrOf n_max gm' b' s =
        if b' = b ∧ s = gm (gmQIdx b) then gm 0 else slabPtrOf n_max gm b' s) ∧
    SlabBijection n_max gm' (fun b' => gm' (gmQIdx b')) (gm' 0) := by
  rcases gmPushSlab_fields gm hb with
    ⟨h0, -, -, -, hQ, hTop, hDir, hOwnB, hOwnS, hBel, hAbv⟩
  have hs_old_of_ne : ∀ b' < numBuckets n_max,
      ∀ s < gmPushSlab n_max gm b (gmQIdx b'),
      ¬(b' = b ∧ s = gm (gmQIdx b)) → s < gm (gmQIdx b') := by
    intro b' hb' s hs hne
    rw [hQ b' hb'] at hs
    split_ifs at hs with hbeq
    · subst hbeq; have : s ≠ gm (gmQIdx b') := fun h => hne ⟨rfl, h⟩; omega
    · exact hs
  refine slabBijection_of_ptr (gm := gmPushSlab n_max gm b)
    (fun b' s => if b' = b ∧ s = gm (gmQIdx b) then gm 0 else slabPtrOf n_max gm b' s)
    (by rw [h0]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro b' hb' s hs
    rw [h0]
    split_ifs with hc
    · omega
    · have := hslab.ptr_lt b' hb' s (hs_old_of_ne b' hb' s hs hc); omega
  · intro b' hb' s hs
    split_ifs with hc
    · rw [hOwnB, ite_eq_left rfl, hc.1]
    · have ho := hs_old_of_ne b' hb' s hs hc
      rw [hOwnB, ite_eq_right (hslab.ptr_lt b' hb' s ho).ne]; exact hslab.ownerB_ptr b' hb' s ho
  · intro b' hb' s hs
    split_ifs with hc
    · rw [hOwnS, ite_eq_left rfl, hc.2]
    · have ho := hs_old_of_ne b' hb' s hs hc
      rw [hOwnS, ite_eq_right (hslab.ptr_lt b' hb' s ho).ne]; exact hslab.ownerS_ptr b' hb' s ho
  · intro p hp
    rw [h0] at hp
    rw [hOwnB p, hOwnS p]
    by_cases hp_eq : p = gm 0
    · simp only [hp_eq, ↓reduceIte]
      exact ⟨hb, by rw [hQ b hb, ite_eq_left rfl]; omega, by simp⟩
    · simp only [hp_eq, ↓reduceIte]
      obtain ⟨hb_p, hs_p, hptr_p⟩ := hslab.owner_valid p (by omega)
      refine ⟨hb_p, ?_, ?_⟩
      · rw [hQ _ hb_p]; split_ifs with hbeq <;> [rw [hbeq] at hs_p; skip] <;> omega
      · rw [ite_eq_right (by rintro ⟨h1, h2⟩; rw [h1, h2] at hs_p; omega), hptr_p]
  · intro b' hb' s hs hdir
    rw [hDir b' hb' s hdir]
    split_ifs with hc
    exacts [rfl, hslab.dir_eq b' hb' s (hs_old_of_ne b' hb' s hs hc) hdir]
  · intro b' hb' s hs htop
    rw [hTop b' hb']
    rw [hQ b' hb'] at hs htop
    split_ifs at hs htop ⊢ with hbeq hc hc
    · rfl
    · exact absurd ⟨hbeq, by omega⟩ hc
    · exact absurd hc.1 hbeq
    · exact hslab.top_eq b' hb' s hs htop
  · intro b' hb' s hs hpos
    by_cases hc : b' = b ∧ s = gm (gmQIdx b)
    · rcases hc with ⟨rfl, rfl⟩
      rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_right (by omega), hBel, ite_eq_left rfl]
      exact hslab.top_eq b' hb' (gm (gmQIdx b') - 1) (by omega) (by omega)
    · have ho := hs_old_of_ne b' hb' s hs hc
      have hc1 : ¬(b' = b ∧ s - 1 = gm (gmQIdx b)) := by rintro ⟨rfl, heq⟩; omega
      rw [ite_eq_right hc, ite_eq_right hc1, hBel, ite_eq_right (hslab.ptr_lt b' hb' s ho).ne]
      exact hslab.below_eq b' hb' s ho hpos
  · intro b' hb' s hs habv
    have hnot1 : ¬(b' = b ∧ s = gm (gmQIdx b)) := by
      rintro ⟨rfl, rfl⟩; rw [hQ b' hb', ite_eq_left rfl] at habv; omega
    rw [ite_eq_right hnot1]
    by_cases hc2 : b' = b ∧ s + 1 = gm (gmQIdx b)
    · rcases hc2 with ⟨rfl, heq⟩
      have htop_old := hslab.top_eq b' hb' s (by omega) heq
      rw [ite_eq_left ⟨rfl, heq⟩, hAbv, ite_eq_left ⟨by omega, htop_old.symm⟩]
    · have hs1_old := hs_old_of_ne b' hb' (s + 1) habv hc2
      have hne_top : ¬(0 < gm (gmQIdx b) ∧ slabPtrOf n_max gm b' s = gm (gmSlabTopIdx b)) := by
        rintro ⟨hq_pos, heq_p⟩
        rw [hslab.top_eq b hb (gm (gmQIdx b) - 1) (by omega) (by omega)] at heq_p
        obtain ⟨rfl, heq_s⟩ := slabPtrOf_inj hslab hb' (by omega) hb (by omega) heq_p
        omega
      rw [ite_eq_right hc2, hAbv, ite_eq_right hne_top]
      exact hslab.above_eq b' hb' s (by omega) hs1_old

/-! ## Section 2: Pure `gmUnlinkTopSlab`, `gmCompactSlab`, `gmPopSlab` and `SlabBijection` -/

/-- Stage A of slab pop: unlink the top slab `p_del = gm (gmSlabTopIdx b)` of bucket `b` by setting
`gmSlabTopIdx b ↦ gm (gmSlabBelowIdx n_max p_del)` and decrementing `gmQIdx b`. -/
@[expose]
def gmUnlinkTopSlab (n_max : ℕ) (gm : ℕ → ℕ) (b : ℕ) : ℕ → ℕ :=
  let q_b := gm (gmQIdx b)
  let p_del := gm (gmSlabTopIdx b)
  let p_below := gm (gmSlabBelowIdx n_max p_del)
  Function.update
    (Function.update gm (gmSlabTopIdx b) p_below)
    (gmQIdx b) (q_b - 1)

/-- Stage B of slab pop: compact the physical slab pool by relocating `p_last = gmA 0 - 1` into the
vacated physical slab `p_del` (when `p_del < p_last`) and decrementing `gmA 0`. -/
@[expose]
def gmCompactSlab (n_max : ℕ) (gmA : ℕ → ℕ) (p_del : ℕ) : ℕ → ℕ :=
  let p_last := gmA 0 - 1
  if p_del < p_last then
    let b_last := gmA (gmSlabOwnerBIdx n_max p_last)
    let s_last := gmA (gmSlabOwnerSIdx n_max p_last)
    let bel_last := gmA (gmSlabBelowIdx n_max p_last)
    let abv_last := gmA (gmSlabAboveIdx n_max p_last)
    let q_last := gmA (gmQIdx b_last)
    let gm₁ := if s_last < dirSlabsPerBucket n_max then
      Function.update gmA (gmSlabDirIdx n_max b_last s_last) p_del else gmA
    let gm₂ := if s_last + 1 = q_last then
      Function.update gm₁ (gmSlabTopIdx b_last) p_del else gm₁
    let gm₃ := if 0 < s_last then
      Function.update gm₂ (gmSlabAboveIdx n_max bel_last) p_del else gm₂
    let gm₄ := if s_last + 1 < q_last then
      Function.update gm₃ (gmSlabBelowIdx n_max abv_last) p_del else gm₃
    let gm₅ := Function.update
      (Function.update
        (Function.update
          (Function.update gm₄ (gmSlabOwnerBIdx n_max p_del) b_last)
          (gmSlabOwnerSIdx n_max p_del) s_last)
        (gmSlabBelowIdx n_max p_del) bel_last)
      (gmSlabAboveIdx n_max p_del) abv_last
    Function.update gm₅ 0 p_last
  else
    Function.update gmA 0 p_last

/-- Pure `GlobalMeta` update popping the top slab of bucket `b` and compacting the physical slab
pool. -/
@[expose]
def gmPopSlab (n_max : ℕ) (gm : ℕ → ℕ) (b : ℕ) : ℕ → ℕ :=
  gmCompactSlab n_max (gmUnlinkTopSlab n_max gm b) (gm (gmSlabTopIdx b))

/-- Field-by-field description of `gmUnlinkTopSlab` (Stage A of slab pop). -/
theorem gmUnlinkTopSlab_fields {n_max : ℕ} (gm : ℕ → ℕ) {b : ℕ} (hb : b < numBuckets n_max) :
    gmUnlinkTopSlab n_max gm b 0 = gm 0 ∧
    gmUnlinkTopSlab n_max gm b 1 = gm 1 ∧
    (∀ b' < numBuckets n_max, gmUnlinkTopSlab n_max gm b (gmRIdx b') = gm (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max,
      gmUnlinkTopSlab n_max gm b (gmQIdx b') =
        if b' = b then gm (gmQIdx b) - 1 else gm (gmQIdx b')) ∧
    (∀ b' < numBuckets n_max,
      gmUnlinkTopSlab n_max gm b (gmSlabTopIdx b') =
        if b' = b then gm (gmSlabBelowIdx n_max (gm (gmSlabTopIdx b)))
        else gm (gmSlabTopIdx b')) ∧
    (∀ idx, gmSlabDirBase n_max ≤ idx → gmUnlinkTopSlab n_max gm b idx = gm idx) ∧
    (∀ b' s, slabPtrOf n_max (gmUnlinkTopSlab n_max gm b) b' s = slabPtrOf n_max gm b' s) :=
  ⟨by update_simp [gmUnlinkTopSlab], by update_simp [gmUnlinkTopSlab],
    fun _ _ => by update_simp [gmUnlinkTopSlab],
    fun b' _ => by by_cases h : b' = b <;> update_simp [gmUnlinkTopSlab],
    fun b' _ => by by_cases h : b' = b <;> update_simp [gmUnlinkTopSlab],
    fun _ _ => by update_simp [gmUnlinkTopSlab],
    slabPtrOf_congr (by update_simp [gmUnlinkTopSlab])
      (fun _ _ => by update_simp [gmUnlinkTopSlab])
      (fun _ _ => by update_simp [gmUnlinkTopSlab])⟩

/-- Field-by-field description of `gmCompactSlab` when `p_del < gmA 0 - 1` (Stage B of slab pop). -/
theorem gmCompactSlab_fields_lt {n_max : ℕ} (gmA : ℕ → ℕ) {p_del : ℕ}
    (hlt : p_del < gmA 0 - 1)
    (hb_last : gmA (gmSlabOwnerBIdx n_max (gmA 0 - 1)) < numBuckets n_max) :
    let p_last := gmA 0 - 1
    let b_last := gmA (gmSlabOwnerBIdx n_max p_last)
    let s_last := gmA (gmSlabOwnerSIdx n_max p_last)
    let bel_last := gmA (gmSlabBelowIdx n_max p_last)
    let abv_last := gmA (gmSlabAboveIdx n_max p_last)
    let q_last := gmA (gmQIdx b_last)
    gmCompactSlab n_max gmA p_del 0 = p_last ∧
    gmCompactSlab n_max gmA p_del 1 = gmA 1 ∧
    (∀ b' < numBuckets n_max, gmCompactSlab n_max gmA p_del (gmRIdx b') = gmA (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max, gmCompactSlab n_max gmA p_del (gmQIdx b') = gmA (gmQIdx b')) ∧
    (∀ idx, gmTailPtrBase n_max ≤ idx → idx < gmSlabMetaBase n_max →
      gmCompactSlab n_max gmA p_del idx = gmA idx) ∧
    (∀ b' < numBuckets n_max,
      gmCompactSlab n_max gmA p_del (gmSlabTopIdx b') =
        if b' = b_last ∧ s_last + 1 = q_last then p_del else gmA (gmSlabTopIdx b')) ∧
    (∀ b' < numBuckets n_max, ∀ s < dirSlabsPerBucket n_max,
      gmCompactSlab n_max gmA p_del (gmSlabDirIdx n_max b' s) =
        if b' = b_last ∧ s = s_last then p_del else gmA (gmSlabDirIdx n_max b' s)) ∧
    (∀ p, gmCompactSlab n_max gmA p_del (gmSlabOwnerBIdx n_max p) =
      if p = p_del then b_last else gmA (gmSlabOwnerBIdx n_max p)) ∧
    (∀ p, gmCompactSlab n_max gmA p_del (gmSlabOwnerSIdx n_max p) =
      if p = p_del then s_last else gmA (gmSlabOwnerSIdx n_max p)) ∧
    (∀ p, gmCompactSlab n_max gmA p_del (gmSlabBelowIdx n_max p) =
      if p = p_del then bel_last
      else if s_last + 1 < q_last ∧ p = abv_last then p_del
      else gmA (gmSlabBelowIdx n_max p)) ∧
    (∀ p, gmCompactSlab n_max gmA p_del (gmSlabAboveIdx n_max p) =
      if p = p_del then abv_last
      else if 0 < s_last ∧ p = bel_last then p_del
      else gmA (gmSlabAboveIdx n_max p)) := by
  dsimp only
  refine ⟨by update_simp [gmCompactSlab], by update_simp [gmCompactSlab],
    fun _ _ => by update_simp [gmCompactSlab],
    fun _ _ => by update_simp [gmCompactSlab],
    fun _ _ _ => by update_simp [gmCompactSlab],
    fun b' _ => by
      by_cases h : b' = gmA (gmSlabOwnerBIdx n_max (gmA 0 - 1)) ∧
        gmA (gmSlabOwnerSIdx n_max (gmA 0 - 1)) + 1 =
          gmA (gmQIdx (gmA (gmSlabOwnerBIdx n_max (gmA 0 - 1)))) <;>
        update_simp [gmCompactSlab],
    fun b' _ s _ => by
      by_cases h : b' = gmA (gmSlabOwnerBIdx n_max (gmA 0 - 1)) ∧
        s = gmA (gmSlabOwnerSIdx n_max (gmA 0 - 1)) <;>
        update_simp [gmCompactSlab],
    fun p => by by_cases h : p = p_del <;> update_simp [gmCompactSlab],
    fun p => by by_cases h : p = p_del <;> update_simp [gmCompactSlab],
    fun p => by
      by_cases hp : p = p_del
      · update_simp [gmCompactSlab]
      · by_cases h : gmA (gmSlabOwnerSIdx n_max (gmA 0 - 1)) + 1 <
          gmA (gmQIdx (gmA (gmSlabOwnerBIdx n_max (gmA 0 - 1)))) ∧
          p = gmA (gmSlabAboveIdx n_max (gmA 0 - 1)) <;>
          update_simp [gmCompactSlab],
    fun p => by
      by_cases hp : p = p_del
      · update_simp [gmCompactSlab]
      · by_cases h : 0 < gmA (gmSlabOwnerSIdx n_max (gmA 0 - 1)) ∧
          p = gmA (gmSlabBelowIdx n_max (gmA 0 - 1)) <;>
          update_simp [gmCompactSlab]⟩

/-- `gmPopSlab` decrements `gm 0` and `gm (gmQIdx b)` while preserving all tail fields. -/
theorem gmPopSlab_preserves_tail {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0)) :
    gmPopSlab n_max gm b 0 = gm 0 - 1 ∧
    gmPopSlab n_max gm b 1 = gm 1 ∧
    (∀ b' < numBuckets n_max, gmPopSlab n_max gm b (gmRIdx b') = gm (gmRIdx b')) ∧
    (∀ b' < numBuckets n_max,
      gmPopSlab n_max gm b (gmQIdx b') =
        if b' = b then gm (gmQIdx b) - 1 else gm (gmQIdx b')) ∧
    (∀ idx, gmTailPtrBase n_max ≤ idx → idx < gmSlabMetaBase n_max →
      gmPopSlab n_max gm b idx = gm idx) := by
  rcases gmUnlinkTopSlab_fields gm hb with ⟨hu0, hu1, huR, huQ, -, huGe, -⟩
  unfold gmPopSlab
  by_cases hlt : gm (gmSlabTopIdx b) < gmUnlinkTopSlab n_max gm b 0 - 1
  · have hb_last : gmUnlinkTopSlab n_max gm b
        (gmSlabOwnerBIdx n_max (gmUnlinkTopSlab n_max gm b 0 - 1)) < numBuckets n_max := by
      rw [hu0, huGe _ (by wram_omega)]
      exact (hslab.owner_valid (gm 0 - 1) (by rw [hu0] at hlt; omega)).1
    rcases gmCompactSlab_fields_lt (gmUnlinkTopSlab n_max gm b) hlt hb_last with
      ⟨hc0, hc1, hcR, hcQ, hcMid, -⟩
    exact ⟨hc0.trans (by rw [hu0]), hc1.trans hu1,
      fun b' hb' => (hcR b' hb').trans (huR b' hb'),
      fun b' hb' => (hcQ b' hb').trans (huQ b' hb'),
      fun idx hlo hhi => (hcMid idx hlo hhi).trans (huGe idx (by wram_omega [hlo]))⟩
  · exact ⟨by update_simp [gmCompactSlab]; rw [hu0],
      by update_simp [gmCompactSlab]; exact hu1,
      fun b' hb' => by update_simp [gmCompactSlab]; exact huR b' hb',
      fun b' hb' => by update_simp [gmCompactSlab]; exact huQ b' hb',
      fun idx hlo _ => by
        update_simp [gmCompactSlab]; exact huGe idx (by wram_omega [hlo])⟩

/-- `gmPopSlab` preserves `TailBijection`. -/
theorem tailBijection_gmPopSlab {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (htail : TailBijection n_max gm (fun b' => gm (gmRIdx b')) (gm 1)) :
    TailBijection n_max (gmPopSlab n_max gm b)
      (fun b' => gmPopSlab n_max gm b (gmRIdx b')) (gmPopSlab n_max gm b 1) := by
  obtain ⟨-, h1, hr, -, hmeta⟩ := gmPopSlab_preserves_tail hb hslab
  exact htail.congr h1 hr hmeta

private theorem gmUnlinkTopSlab_active {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max) (hq_pos : 1 ≤ gm (gmQIdx b))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0)) :
    (∀ b' < numBuckets n_max, ∀ s < gmUnlinkTopSlab n_max gm b (gmQIdx b'),
      s < gm (gmQIdx b') ∧ slabPtrOf n_max gm b' s ≠ gm (gmSlabTopIdx b)) ∧
    (∀ p < gm 0, p ≠ gm (gmSlabTopIdx b) →
      gm (gmSlabOwnerSIdx n_max p) <
        gmUnlinkTopSlab n_max gm b (gmQIdx (gm (gmSlabOwnerBIdx n_max p)))) ∧
    (∀ b' < numBuckets n_max, ∀ s < gmUnlinkTopSlab n_max gm b (gmQIdx b'),
      s + 1 = gmUnlinkTopSlab n_max gm b (gmQIdx b') →
      gmUnlinkTopSlab n_max gm b (gmSlabTopIdx b') = slabPtrOf n_max gm b' s) := by
  rcases gmUnlinkTopSlab_fields gm hb with ⟨-, -, -, huQ, huTop, -, -⟩
  have htop_b := hslab.top_eq b hb (gm (gmQIdx b) - 1) (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro b' hb' s hs
    rw [huQ b' hb'] at hs
    have hs_old : s < gm (gmQIdx b') := by
      split_ifs at hs with hbeq <;> [subst hbeq; skip] <;> omega
    refine ⟨hs_old, fun heq => ?_⟩
    obtain ⟨rfl, rfl⟩ := slabPtrOf_inj hslab hb' hs_old hb (by omega) (heq.trans htop_b)
    simp only [↓reduceIte] at hs; omega
  · intro p hp hne
    obtain ⟨hb_p, hs_p, hptr_p⟩ := hslab.owner_valid p hp
    rw [huQ _ hb_p]
    split_ifs with hbeq
    · have : gm (gmSlabOwnerSIdx n_max p) ≠ gm (gmQIdx b) - 1 := fun heq =>
        hne (by rw [← hptr_p, htop_b, hbeq, heq])
      rw [hbeq] at hs_p; omega
    · exact hs_p
  · intro b' hb' s hs htop
    rw [huTop b' hb']
    rw [huQ b' hb'] at hs htop
    split_ifs with hbeq
    · subst hbeq
      simp only [↓reduceIte] at hs htop
      rw [htop_b, hslab.below_eq b' hb' (gm (gmQIdx b') - 1) (by omega) (by omega)]
      congr 1; omega
    · simp only [hbeq, ↓reduceIte] at hs htop
      exact hslab.top_eq b' hb' s hs htop

private theorem slabBijection_gmPopSlab_eq {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max) (hq_pos : 1 ≤ gm (gmQIdx b))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (hnot_lt : ¬ gm (gmSlabTopIdx b) < gm 0 - 1) :
    (∀ b' < numBuckets n_max, ∀ s < gmPopSlab n_max gm b (gmQIdx b'),
      slabPtrOf n_max (gmPopSlab n_max gm b) b' s =
        if slabPtrOf n_max gm b' s = gm 0 - 1 then gm (gmSlabTopIdx b)
        else slabPtrOf n_max gm b' s) ∧
    SlabBijection n_max (gmPopSlab n_max gm b)
      (fun b' => gmPopSlab n_max gm b (gmQIdx b')) (gmPopSlab n_max gm b 0) := by
  rcases gmUnlinkTopSlab_fields gm hb with ⟨hu0, -, -, -, -, huGe, -⟩
  obtain ⟨hact_s, hact_own, hact_top⟩ := gmUnlinkTopSlab_active hb hq_pos hslab
  have htop_lt : gm (gmSlabTopIdx b) < gm 0 := hslab.top_lt hb (by omega)
  have hlt' : ¬ gm (gmSlabTopIdx b) < gmUnlinkTopSlab n_max gm b 0 - 1 := by rwa [hu0]
  have hpop {i} (hi : i ≠ 0) : gmPopSlab n_max gm b i = gmUnlinkTopSlab n_max gm b i := by
    rw [gmPopSlab, gmCompactSlab, ite_eq_right hlt', Function.update_of_ne hi]
  have h0 : gmPopSlab n_max gm b 0 = gm 0 - 1 := by
    rw [gmPopSlab, gmCompactSlab, ite_eq_right hlt', Function.update_self, hu0]
  have hQ (b') := hpop (i := gmQIdx b') (by wram_omega)
  have htop (b') := hpop (i := gmSlabTopIdx b') (by wram_omega)
  have hhi (idx) (hidx : gmSlabDirBase n_max ≤ idx) :=
    (hpop (by wram_omega)).trans (huGe idx hidx)
  obtain ⟨hptr, hbij⟩ := slabBijection_of_ptr (n_max := n_max) (gm := gmPopSlab n_max gm b)
    (fun b' s => slabPtrOf n_max gm b' s)
    (by rw [h0]; have := hslab.nslabs_le; omega)
    (fun b' hb' s hs => by
      rw [hQ] at hs; obtain ⟨hs_old, hne⟩ := hact_s b' hb' s hs
      have := hslab.ptr_lt b' hb' s hs_old; rw [h0]; omega)
    (fun b' hb' s hs => (hhi _ (by wram_omega)).trans
      (hslab.ownerB_ptr b' hb' s (hact_s b' hb' s (hQ b' ▸ hs)).1))
    (fun b' hb' s hs => (hhi _ (by wram_omega)).trans
      (hslab.ownerS_ptr b' hb' s (hact_s b' hb' s (hQ b' ▸ hs)).1))
    (fun p hp => by
      rw [h0] at hp
      rw [hhi _ (by wram_omega), hhi _ (by wram_omega), hQ]
      obtain ⟨hb_p, -, hptr_p⟩ := hslab.owner_valid p (by omega)
      exact ⟨hb_p, hact_own p (by omega) (by omega), hptr_p⟩)
    (fun b' hb' s hs hd => (hhi _ (by wram_omega)).trans
      (hslab.dir_eq b' hb' s (hact_s b' hb' s (hQ b' ▸ hs)).1 hd))
    (fun b' hb' s hs ht => (htop b').trans (hact_top b' hb' s (hQ b' ▸ hs) (hQ b' ▸ ht)))
    (fun b' hb' s hs hpos => (hhi _ (by wram_omega)).trans
      (hslab.below_eq b' hb' s (hact_s b' hb' s (hQ b' ▸ hs)).1 hpos))
    (fun b' hb' s hs ha => (hhi _ (by wram_omega)).trans
      (hslab.above_eq b' hb' s (hact_s b' hb' s (hQ b' ▸ hs)).1
        (hact_s b' hb' (s + 1) (hQ b' ▸ ha)).1))
  refine ⟨fun b' hb' s hs => ?_, hbij⟩
  have hne := (hact_s b' hb' s (hQ b' ▸ hs)).2
  rw [hptr b' hb' s hs, ite_eq_right (by omega)]

private theorem slabBijection_gmPopSlab_lt {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max) (hq_pos : 1 ≤ gm (gmQIdx b))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0))
    (hlt : gm (gmSlabTopIdx b) < gm 0 - 1) :
    (∀ b' < numBuckets n_max, ∀ s < gmPopSlab n_max gm b (gmQIdx b'),
      slabPtrOf n_max (gmPopSlab n_max gm b) b' s =
        if slabPtrOf n_max gm b' s = gm 0 - 1 then gm (gmSlabTopIdx b)
        else slabPtrOf n_max gm b' s) ∧
    SlabBijection n_max (gmPopSlab n_max gm b)
      (fun b' => gmPopSlab n_max gm b (gmQIdx b')) (gmPopSlab n_max gm b 0) := by
  let p_del := gm (gmSlabTopIdx b)
  let p_last := gm 0 - 1
  let b_last := gm (gmSlabOwnerBIdx n_max p_last)
  let s_last := gm (gmSlabOwnerSIdx n_max p_last)
  rcases gmUnlinkTopSlab_fields gm hb with ⟨hu0, -, -, -, -, huGe, -⟩
  obtain ⟨hact_s, hact_own, hact_top⟩ := gmUnlinkTopSlab_active hb hq_pos hslab
  obtain ⟨hb_last, hs_last_old, hptr_last⟩ := hslab.owner_valid p_last (by omega)
  have hlast_iff : ∀ b' < numBuckets n_max, ∀ s < gm (gmQIdx b'),
      slabPtrOf n_max gm b' s = p_last ↔ b' = b_last ∧ s = s_last :=
    fun b' hb' s hs =>
      ⟨fun h => slabPtrOf_inj hslab hb' hs hb_last hs_last_old (h.trans hptr_last.symm),
       by rintro ⟨rfl, rfl⟩; exact hptr_last⟩
  have hB (p) := huGe (gmSlabOwnerBIdx n_max p) (by wram_omega)
  have hS (p) := huGe (gmSlabOwnerSIdx n_max p) (by wram_omega)
  have hBel (p) := huGe (gmSlabBelowIdx n_max p) (by wram_omega)
  have hAbv (p) := huGe (gmSlabAboveIdx n_max p) (by wram_omega)
  have hDir (b' s) := huGe (gmSlabDirIdx n_max b' s) (by wram_omega)
  have hc := gmCompactSlab_fields_lt (n_max := n_max) (gmUnlinkTopSlab n_max gm b) (by rwa [hu0])
    (by simpa only [hu0, hB] using hb_last)
  dsimp only at hc
  have hgm' : gmCompactSlab n_max (gmUnlinkTopSlab n_max gm b) p_del = gmPopSlab n_max gm b := rfl
  rw [hu0, hB, hS, hBel, hAbv, hgm'] at hc
  rcases hc with ⟨hc0, -, -, hcQ, -, hcTop, hcDir, hcOwnB, hcOwnS, hcBel, hcAbv⟩
  refine slabBijection_of_ptr (n_max := n_max) (gm := gmPopSlab n_max gm b)
    (fun b' s => if slabPtrOf n_max gm b' s = p_last then p_del else slabPtrOf n_max gm b' s)
    (by rw [hc0]; have := hslab.nslabs_le; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro b' hb' s hs
    rw [hc0]
    split_ifs with heq
    · exact hlt
    · have := hslab.ptr_lt b' hb' s (hact_s b' hb' s (hcQ b' hb' ▸ hs)).1; omega
  · intro b' hb' s hs
    obtain ⟨hs_old, hne_del⟩ := hact_s b' hb' s (hcQ b' hb' ▸ hs)
    by_cases h1 : slabPtrOf n_max gm b' s = p_last
    · rw [ite_eq_left h1, hcOwnB, ite_eq_left rfl]
      exact ((hlast_iff b' hb' s hs_old).mp h1).1.symm
    · rw [ite_eq_right h1, hcOwnB, ite_eq_right hne_del, hB]
      exact hslab.ownerB_ptr b' hb' s hs_old
  · intro b' hb' s hs
    obtain ⟨hs_old, hne_del⟩ := hact_s b' hb' s (hcQ b' hb' ▸ hs)
    by_cases h1 : slabPtrOf n_max gm b' s = p_last
    · rw [ite_eq_left h1, hcOwnS, ite_eq_left rfl]
      exact ((hlast_iff b' hb' s hs_old).mp h1).2.symm
    · rw [ite_eq_right h1, hcOwnS, ite_eq_right hne_del, hS]
      exact hslab.ownerS_ptr b' hb' s hs_old
  · intro p hp
    rw [hc0] at hp
    rw [hcOwnB p, hcOwnS p, hB p, hS p]
    rcases eq_or_ne p p_del with rfl | hp_eq
    · rw [ite_eq_left rfl, ite_eq_left rfl]
      exact ⟨hb_last, hcQ _ hb_last ▸ hact_own p_last (by omega) (by omega),
        ite_eq_left hptr_last⟩
    · rw [ite_eq_right hp_eq, ite_eq_right hp_eq]
      obtain ⟨hb_p, -, hptr_p⟩ := hslab.owner_valid p (by omega)
      exact ⟨hb_p, hcQ _ hb_p ▸ hact_own p (by omega) hp_eq,
        by rw [hptr_p, ite_eq_right (by omega)]⟩
  · intro b' hb' s hs hdir
    have hs_old := (hact_s b' hb' s (hcQ b' hb' ▸ hs)).1
    rw [hcDir b' hb' s hdir, hDir b' s]
    by_cases h1 : b' = b_last ∧ s = s_last
    · rw [ite_eq_left h1, ite_eq_left ((hlast_iff b' hb' s hs_old).mpr h1)]
    · rw [ite_eq_right h1, ite_eq_right (fun h => h1 ((hlast_iff b' hb' s hs_old).mp h))]
      exact hslab.dir_eq b' hb' s hs_old hdir
  · intro b' hb' s hs htop
    rw [hcQ b' hb'] at hs htop
    have hs_old := (hact_s b' hb' s hs).1
    rw [hcTop b' hb']
    by_cases heq : b' = b_last ∧ s = s_last
    · have hp_eq := (hlast_iff b' hb' s hs_old).mpr heq
      rcases heq with ⟨rfl, rfl⟩
      rw [ite_eq_left ⟨rfl, htop⟩, ite_eq_left hp_eq]
    · have hntop : ¬(b' = b_last ∧ s_last + 1 = gmUnlinkTopSlab n_max gm b (gmQIdx b_last)) := by
        rintro ⟨rfl, h⟩; exact heq ⟨rfl, by omega⟩
      rw [ite_eq_right hntop, ite_eq_right (fun h => heq ((hlast_iff b' hb' s hs_old).mp h))]
      exact hact_top b' hb' s hs htop
  · intro b' hb' s hs hpos
    rw [hcQ b' hb'] at hs
    obtain ⟨hs_old, hne_del⟩ := hact_s b' hb' s hs
    obtain ⟨hs1_old, _⟩ := hact_s b' hb' (s - 1) (by omega)
    refine gmCompactSlab_link_eq hslab hb_last hs_last_old hptr_last
      (fwd' := fun p => gmPopSlab n_max gm b (gmSlabBelowIdx n_max p))
      (fwd := fun p => gm (gmSlabBelowIdx n_max p))
      (adjCond := s_last + 1 < gmUnlinkTopSlab n_max gm b (gmQIdx b_last))
      (bwd_last := gm (gmSlabAboveIdx n_max p_last))
      (fun p => by rw [hcBel p, hBel p]) hb' hs_old hs1_old (by omega) hne_del
      (hslab.below_eq b' hb' s hs_old hpos)
      (fun hbeq hseq => ((congrArg (· + 1) hseq.symm).trans (Nat.sub_add_cancel hpos)).trans_lt
        (hs.trans_eq (congrArg (gmUnlinkTopSlab n_max gm b ∘ gmQIdx) hbeq)))
      (fun hq_lt => ⟨s_last + 1, (hact_s _ hb_last _ hq_lt).1,
        (congrArg (fun p => gm (gmSlabAboveIdx n_max p)) hptr_last.symm).trans
          (hslab.above_eq _ hb_last _ hs_last_old (hact_s _ hb_last _ hq_lt).1),
        by omega⟩)
  · intro b' hb' s hs habv
    rw [hcQ b' hb'] at hs habv
    obtain ⟨hs_old, hne_del⟩ := hact_s b' hb' s hs
    obtain ⟨hs1_old, _⟩ := hact_s b' hb' (s + 1) habv
    refine gmCompactSlab_link_eq hslab hb_last hs_last_old hptr_last
      (fwd' := fun p => gmPopSlab n_max gm b (gmSlabAboveIdx n_max p))
      (fwd := fun p => gm (gmSlabAboveIdx n_max p))
      (adjCond := 0 < s_last)
      (bwd_last := gm (gmSlabBelowIdx n_max p_last))
      (fun p => by rw [hcAbv p, hAbv p]) hb' hs_old hs1_old (by omega) hne_del
      (hslab.above_eq b' hb' s hs_old hs1_old)
      (fun _ hseq => by omega)
      (fun hpos => ⟨s_last - 1, by omega,
        (congrArg (fun p => gm (gmSlabBelowIdx n_max p)) hptr_last.symm).trans
          (hslab.below_eq _ hb_last _ hs_last_old hpos),
        by omega⟩)

/-- `gmPopSlab` relocates the last physical slab `gm 0 - 1` into `gm (gmSlabTopIdx b)` and
preserves `SlabBijection`. -/
theorem slabBijection_gmPopSlab {n_max : ℕ} {gm : ℕ → ℕ} {b : ℕ}
    (hb : b < numBuckets n_max)
    (hq_pos : 1 ≤ gm (gmQIdx b))
    (hslab : SlabBijection n_max gm (fun b' => gm (gmQIdx b')) (gm 0)) :
    (∀ b' < numBuckets n_max, ∀ s < gmPopSlab n_max gm b (gmQIdx b'),
      slabPtrOf n_max (gmPopSlab n_max gm b) b' s =
        if slabPtrOf n_max gm b' s = gm 0 - 1 then gm (gmSlabTopIdx b)
        else slabPtrOf n_max gm b' s) ∧
    SlabBijection n_max (gmPopSlab n_max gm b)
      (fun b' => gmPopSlab n_max gm b (gmQIdx b')) (gmPopSlab n_max gm b 0) := by
  by_cases hlt : gm (gmSlabTopIdx b) < gm 0 - 1
  · exact slabBijection_gmPopSlab_lt hb hq_pos hslab hlt
  · exact slabBijection_gmPopSlab_eq hb hq_pos hslab hlt

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
