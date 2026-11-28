/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap

/-!
# Worked Word-RAM Soft Heap examples

These kernel-checked tests exercise `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap`:

1. Pure rank thresholds (`rankThresholdForEps`), `targetSize`, `shFuelBound`,
   `corrupt_sum_bound`, `corrupt_sum_bound_eps`, and `itemPhi_sub_succ`.
2. Uniform `Realizes .exact` (`work := 0`) certificate types for pool allocation, `defill`,
   `shInsert`, `shExtractMin` (`SHExtractResult`), `shCollectCorrupted`, and `shBatchProg`.
3. End-to-end stateful pool lifecycle at `r = 8` using `allocPool_spec`, `shInit_inv`, empty &
   non-empty `shExtractMin_spec`, multiple `shInsert_spec` calls, amortized telescoping total
   memory cost (`≤ 5130`), `shInv_corrupted_le`, and `shCollectCorrupted_spec`.
4. Concrete rank-9 corrupted heap witness at `r = 8` (`rankThresholdForEps (1 / 16)`) exercising
   `SHInv.origKey_le_ckey`, `shInv_corrupted_le_eps`, `shInv_corrupted_le`, and non-empty
   `shCollectCorrupted_spec`.
5. Non-vacuous concrete `w = 16` instantiations of
   `exists_singleSoftHeap_batch_standard_program` and
   `exists_singleSoftHeap_batch_standard_program_eps` (`ε = 1 / 4`) verifying `Runs`, `.halt`,
   exact memory output arrays via `SHBatchExtract.readFrom`, corruption bounds, and step bounds.
-/

public section

namespace CslibFrontierTests.SoftHeap

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

example :
    targetSize 8 8 = 1 ∧ targetSize 8 9 = 2 ∧ targetSize 8 11 = 4 ∧
      rankThresholdForEps (1 / 4 : ℚ) = 6 ∧ shFuelBound 8 2 = 1500 := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · simp [targetSize]
  · simp [targetSize]
  · simp [targetSize]
  · have hceil : Nat.ceil (12 / (1 / 4 : ℚ)) = 48 := by
      rw [show (12 / (1 / 4 : ℚ) : ℚ) = ((48 : ℕ) : ℚ) by norm_num, Nat.ceil_natCast]
    rw [rankThresholdForEps, hceil, show Nat.log 2 48 = 5 by decide]

example :
    16 * ∑ k ∈ Finset.Icc 9 10,
        (fun j => if j ≤ 10 then 2 ^ (10 - j) else 0) k * sizeCap 8 k ≤
      (if 0 ≤ 10 then 2 ^ (10 - 0) else 0) := by
  have hb := corrupt_sum_bound 8 (fun j => if j ≤ 10 then 2 ^ (10 - j) else 0) 10 ?_
  · change 256 * (∑ k ∈ Finset.Icc 9 10,
        (fun j => if j ≤ 10 then 2 ^ (10 - j) else 0) k * sizeCap 8 k) ≤
        12 * (if 0 ≤ 10 then 2 ^ (10 - 0) else 0) at hb
    omega
  intro k
  by_cases hk10 : k + 1 ≤ 10
  · have hk : k ≤ 10 := by omega
    simp only [hk10, hk, ↓reduceIte]
    have heq : 10 - k = (10 - (k + 1)) + 1 := by omega
    rw [heq, Nat.pow_succ, Nat.mul_comm]
  · by_cases hk : k ≤ 10
    · simp only [hk10, hk, ↓reduceIte, mul_zero, Nat.zero_le]
    · simp only [hk10, hk, ↓reduceIte, mul_zero, le_rfl]

example :
    ((∑ k ∈ Finset.Icc (rankThresholdForEps (1 / 4 : ℚ) + 1) 8,
        (fun j => if j ≤ 8 then 2 ^ (8 - j) else 0) k *
          sizeCap (rankThresholdForEps (1 / 4 : ℚ)) k : ℕ) : ℚ) ≤
      (1 / 4 : ℚ) * ((if 0 ≤ 8 then 2 ^ (8 - 0) else 0 : ℕ) : ℚ) := by
  refine corrupt_sum_bound_eps (ε := (1 / 4 : ℚ)) (by norm_num)
    (fun j => if j ≤ 8 then 2 ^ (8 - j) else 0) 8 ?_
  intro k
  by_cases hk8 : k + 1 ≤ 8
  · have hk : k ≤ 8 := by omega
    simp only [hk8, hk, ↓reduceIte]
    have heq : 8 - k = (8 - (k + 1)) + 1 := by omega
    rw [heq, Nat.pow_succ, Nat.mul_comm]
  · by_cases hk : k ≤ 8
    · simp only [hk8, hk, ↓reduceIte, mul_zero, Nat.zero_le]
    · simp only [hk8, hk, ↓reduceIte, mul_zero, le_rfl]

example :
    itemPhi 8 7 - itemPhi 8 8 = 1 / (targetSize 8 7 : ℚ) ∧
      itemPhi 8 8 - itemPhi 8 9 = 1 / (targetSize 8 8 : ℚ) ∧
      itemPhi 8 9 - itemPhi 8 10 = 1 / (targetSize 8 9 : ℚ) :=
  ⟨itemPhi_sub_succ 8 7, itemPhi_sub_succ 8 8, itemPhi_sub_succ 8 9⟩

example :
    Realizes .exact (fun d : Fin 2 → ℕ => allocPool (d 0) (d 1)) (.refl _)
        (WordEncoding.encode (α := ℕ × ℕ))
        (fun w d s => Fits w (s.frontier + 3 * (d 0 + 1) + 12 * (d 1 + 1) + 16))
        (fun _ _ => 0) ∧
      Realizes .exact defill (.refl _) (WordEncoding.encode (α := Unit)) defillSafe
        (fun _ _ => 0) ∧
      Realizes .exact shInsert (WordEncoding.encode (α := SHHandle × ℕ × ℕ × ℕ))
        (WordEncoding.encode (α := SHHandle)) shInsertSafe (fun _ _ => 0) ∧
      Realizes .exact shExtractMin (WordEncoding.encode (α := SHHandle × ℕ))
        (WordEncoding.encode (α := SHExtractResult)) shExtractMinSafe (fun _ _ => 0) ∧
      Realizes .exact shCollectCorrupted
        (WordEncoding.encode (α := SHHandle × ℕ × ℕ × ℕ × ℕ))
        (WordEncoding.encode (α := ℕ)) shCollectCorruptedSafe (fun _ _ => 0) ∧
      Realizes .exact shBatchProg (WordEncoding.encode (α := ℕ × ℕ))
        (WordEncoding.encode (α := SHBatchResult)) SHBatchProgSafe (fun _ _ => 0) :=
  ⟨realizes_allocPool, realizes_defill, realizes_shInsert, realizes_shExtractMin,
    realizes_shCollectCorrupted, realizes_shBatchProg⟩

-- End-to-end stateful Soft Heap run (`r = 8`, `fuel = shFuelBound 8 2 = 1500`):
-- `allocPool` -> empty `extractMin` -> two inserts -> amortized telescoping bound (`≤ 5130`) ->
-- non-empty `extractMin` -> `shCollectCorrupted`.
example :
    ∃ (s₀ s₁ s₂ s₃ s₄ s₅ : Memory.State) (h₀ h₁ h₂ : SHHandle)
      (extRes : SHExtractResult) (newOut : ℕ),
      s₀ = ⟨fun _ => 0, 16⟩ ∧
      s₁ = (Memory.spec 0).clientState s₀ (allocPool 2 4) ∧
      h₀ = ⟨((Memory.spec 0).clientResult s₀ (allocPool 2 4)).1,
        ((Memory.spec 0).clientResult s₀ (allocPool 2 4)).2, 0, 0, 0, 8⟩ ∧
      h₁ = (Memory.spec 0).clientResult s₁ (shInsert (h₀, 42, 100, 1500)) ∧
      s₂ = (Memory.spec 0).clientState s₁ (shInsert (h₀, 42, 100, 1500)) ∧
      h₂ = (Memory.spec 0).clientResult s₂ (shInsert (h₁, 7, 50, 1500)) ∧
      s₃ = (Memory.spec 0).clientState s₂ (shInsert (h₁, 7, 50, 1500)) ∧
      extRes = (Memory.spec 0).clientResult s₃ (shExtractMin (h₂, 1500)) ∧
      s₄ = (Memory.spec 0).clientState s₃ (shExtractMin (h₂, 1500)) ∧
      newOut = (Memory.spec 0).clientResult s₄ (shCollectCorrupted (extRes.handle, 0, 0, 0, 2)) ∧
      s₅ = (Memory.spec 0).clientState s₄ (shCollectCorrupted (extRes.handle, 0, 0, 0, 2)) ∧
      memoryCost (allocPool 2 4) s₀ = 2 ∧
      memoryCost (shExtractMin (h₀, 1500)) s₁ = 0 ∧
      memoryCost (shInsert (h₀, 42, 100, 1500)) s₁ +
        memoryCost (shInsert (h₁, 7, 50, 1500)) s₂ +
        memoryCost (shExtractMin (h₂, 1500)) s₃ ≤ 5130 ∧
      extRes.found = 1 ∧
      extRes.key = 50 ∧
      newOut = 0 ∧
      memoryCost (shCollectCorrupted (extRes.handle, 0, 0, 0, 2)) s₄ ≤ 16 ∧
      s₅.frontier = 85 := by
  let s₀ : Memory.State := ⟨fun _ => 0, 16⟩
  have hwf₀ : Memory.WellFormed 16 s₀ :=
    { mem_fits := fun _ => Nat.two_pow_pos 16, frontier_fits := by decide }
  obtain ⟨_, hm_alloc, hres1, hres2, hfr₁, _, hwf₁⟩ :=
    allocPool_spec (maxItems := 2) (maxNodes := 4) hwf₀ (by decide)
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ = (Memory.spec 0).clientState s₀ (allocPool 2 4) := ⟨_, rfl⟩
  rw [← hs₁] at hfr₁ hwf₁
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : SHHandle,
      h₀ = ⟨((Memory.spec 0).clientResult s₀ (allocPool 2 4)).1,
        ((Memory.spec 0).clientResult s₀ (allocPool 2 4)).2, 0, 0, 0, 8⟩ := ⟨_, rfl⟩
  have h₀_ib : h₀.itemBase = 16 := by rw [hh₀]; exact hres1
  have h₀_nb : h₀.nodeBase = 25 := by rw [hh₀]; exact hres2
  have h₀_ic : h₀.itemCount = 0 := by rw [hh₀]
  have h₀_rt : h₀.rankThreshold = 8 := by rw [hh₀]
  have hinv₀ : SHInv 16 0 0 2 4 h₀ [] (fun _ => 0) s₁ := by
    rw [hh₀]
    exact shInit_inv (w := 16)
      (itemBase := ((Memory.spec 0).clientResult s₀ (allocPool 2 4)).1)
      (nodeBase := ((Memory.spec 0).clientResult s₀ (allocPool 2 4)).2)
      (ic₀ := 0) (nc₀ := 0) (maxItems := 2) (maxNodes := 4) (rankThreshold := 8)
      (by decide) hwf₁ (by decide) (by decide)
      (by rw [hres1, hfr₁]; omega)
      (by rw [hres2, hfr₁])
      (Or.inl (by rw [hres1, hres2]))
      (by decide)
  obtain ⟨_, _, _, _, _, _, _, _, _, hempty_fn, _⟩ :=
    shExtractMin_spec (fuel := 1500) hinv₀ (by rw [h₀_rt]; decide) (by decide)
  have hempty := hempty_fn rfl
  obtain ⟨_, _, hib1, hnb1, hic1, _, hrt1, hfr₂, _, roots₁, created₁,
      hinv₁, hp₁, hent₁, hphi₁⟩ :=
    shInsert_spec (val := 42) (origKey := 100) (fuel := 1500)
      hinv₀ (by rw [h₀_ic]; decide) (by decide) (by decide) (by rw [h₀_rt]; decide) (by decide)
  obtain ⟨h₁, hh₁⟩ : ∃ h₁,
      h₁ = (Memory.spec 0).clientResult s₁ (shInsert (h₀, 42, 100, 1500)) := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s₂,
      s₂ = (Memory.spec 0).clientState s₁ (shInsert (h₀, 42, 100, 1500)) := ⟨_, rfl⟩
  rw [← hh₁] at hib1 hnb1 hic1 hrt1 hinv₁
  rw [← hs₂] at hfr₂ hinv₁
  have hib1' : h₁.itemBase = 16 := hib1.trans h₀_ib
  have hnb1' : h₁.nodeBase = 25 := hnb1.trans h₀_nb
  have hic1' : h₁.itemCount = 1 := hic1.trans (by rw [h₀_ic])
  have hrt1' : h₁.rankThreshold = 8 := hrt1.trans h₀_rt
  obtain ⟨_, _, hib2, hnb2, hic2, _, hrt2, hfr₃, _, roots₂, created₂,
      hinv₂, hp₂, hent₂, hphi₂⟩ :=
    shInsert_spec (val := 7) (origKey := 50) (fuel := 1500)
      hinv₁ (by rw [hic1']; decide) (by decide) (by decide) (by rw [hrt1']; decide) (by decide)
  obtain ⟨h₂, hh₂⟩ : ∃ h₂,
      h₂ = (Memory.spec 0).clientResult s₂ (shInsert (h₁, 7, 50, 1500)) := ⟨_, rfl⟩
  obtain ⟨s₃, hs₃⟩ : ∃ s₃,
      s₃ = (Memory.spec 0).clientState s₂ (shInsert (h₁, 7, 50, 1500)) := ⟨_, rfl⟩
  rw [← hh₂] at hib2 hnb2 hic2 hrt2 hinv₂
  rw [← hs₃] at hfr₃ hinv₂
  have hib2' : h₂.itemBase = 16 := hib2.trans hib1'
  have hnb2' : h₂.nodeBase = 25 := hnb2.trans hnb1'
  have hic2' : h₂.itemCount = 2 := hic2.trans (by rw [hic1'])
  have hrt2' : h₂.rankThreshold = 8 := hrt2.trans hrt1'
  have hne₂ : roots₂ ≠ [] := by
    intro hemp
    have hlen := hp₂.length_eq
    rw [hemp] at hlen
    simp [forestItems, forestEntries] at hlen
  obtain ⟨_, _, hib3, hnb3, hic3, _, hrt3, hfr₄, _, _, hne_ext⟩ :=
    shExtractMin_spec (fuel := 1500) hinv₂ (by rw [hrt2']; decide) (by decide)
  obtain ⟨hfound, it₀, roots₃, hit₀_in, _, horig_le_pop, hmin_all,
      hinv₃, _, _, hphi₃⟩ := hne_ext hne₂
  obtain ⟨extRes, hext⟩ : ∃ extRes,
      extRes = (Memory.spec 0).clientResult s₃ (shExtractMin (h₂, 1500)) := ⟨_, rfl⟩
  obtain ⟨s₄, hs₄⟩ : ∃ s₄,
      s₄ = (Memory.spec 0).clientState s₃ (shExtractMin (h₂, 1500)) := ⟨_, rfl⟩
  rw [← hext] at hib3 hnb3 hic3 hrt3 hfound hit₀_in horig_le_pop hmin_all hinv₃
  rw [← hs₄] at hfr₄ hinv₃
  have htele :
      memoryCost (shInsert (h₀, 42, 100, 1500)) s₁ +
        memoryCost (shInsert (h₁, 7, 50, 1500)) s₂ +
        memoryCost (shExtractMin (h₂, 1500)) s₃ ≤ 5130 := by
    have h0 := totalPhi_nil 8
    have hnon := totalPhi_nonneg 8 roots₃
    rw [h₀_rt] at hphi₁
    rw [hrt1'] at hphi₂
    rw [hrt2'] at hphi₃
    norm_num at hphi₁ hphi₂
    have hq :
        ((memoryCost (shInsert (h₀, 42, 100, 1500)) s₁ +
          memoryCost (shInsert (h₁, 7, 50, 1500)) s₂ +
          memoryCost (shExtractMin (h₂, 1500)) s₃ : ℕ) : ℚ) ≤ 5130 := by
      push_cast
      linarith
    exact_mod_cast hq
  have hcor₂ :
      ((forestEntries roots₂).filter (fun p => decide (p.1.origKey < p.2))).length = 0 := by
    have hb := shInv_corrupted_le hinv₂
    rw [hrt2', hic2', show (2 ^ 8 : ℕ) = 256 by decide] at hb
    omega
  have hno_cor₂ : ∀ p ∈ forestEntries roots₂, p.2 ≤ p.1.origKey := by
    intro p hp
    have hnil : (forestEntries roots₂).filter (fun q => decide (q.1.origKey < q.2)) = [] :=
      List.length_eq_zero_iff.mp hcor₂
    have hnot := (List.filter_eq_nil_iff.mp hnil) p hp
    simp only [decide_eq_true_eq, Nat.not_lt] at hnot
    exact hnot
  have hitem_min : (⟨2, 7, 50⟩ : SHItem) ∈ forestItems roots₂ := by
    refine hp₂.symm.mem_iff.mp ?_
    rw [hic1']
    exact List.mem_cons_self
  have hpop_le_50 : extRes.key ≤ 50 := by
    rcases List.mem_map.mp hitem_min with ⟨p, hp_in, hp_fst⟩
    have hle1 : extRes.key ≤ p.2 := hmin_all p hp_in
    have hle2 := hno_cor₂ p hp_in
    have hok : p.1.origKey = 50 := by rw [hp_fst]
    omega
  have h50_le_orig : 50 ≤ it₀.origKey := by
    have hit₀_item : it₀ ∈ forestItems roots₂ :=
      List.mem_map.mpr ⟨(it₀, extRes.key), hit₀_in, rfl⟩
    rcases List.mem_cons.mp (hp₂.mem_iff.mp hit₀_item) with rfl | h_in1
    · exact le_rfl
    · have hsub1 : (forestItems roots₁).Perm [⟨1, 42, 100⟩] := by
        simpa [forestItems, forestEntries, h₀_ic] using hp₁
      have h_eq1 : it₀ = ⟨1, 42, 100⟩ := List.mem_singleton.mp (hsub1.mem_iff.mp h_in1)
      rw [h_eq1]
      decide
  have h50_le_pop : 50 ≤ extRes.key := h50_le_orig.trans horig_le_pop
  have hib3' : extRes.handle.itemBase = 16 := hib3.trans hib2'
  have hnb3' : extRes.handle.nodeBase = 25 := hnb3.trans hnb2'
  have hic3' : extRes.handle.itemCount = 2 := hic3.trans hic2'
  have hrt3' : extRes.handle.rankThreshold = 8 := hrt3.trans hrt2'
  have hcor₃ :
      ((forestEntries roots₃).filter (fun p => decide (p.1.origKey < p.2))).length = 0 := by
    have hb := shInv_corrupted_le hinv₃
    rw [hrt3', hic3', show (2 ^ 8 : ℕ) = 256 by decide] at hb
    omega
  have hs4_fr : s₄.frontier = 85 := by rw [hfr₄, hfr₃, hfr₂, hfr₁]
  have hout_disj : ∀ a, 0 + 0 ≤ a → a < 0 + 2 → ¬ InSHPool 0 0 2 4 extRes.handle a := by
    intro a _ ha hin
    rcases hin with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  obtain ⟨_, _, hnewOut, hfr₅, _, _, _, hm_cor⟩ :=
    shCollectCorrupted_spec (outBase := 0) (outCount := 0) (outCap := 2) (fuel := 2)
      hinv₃ (by rw [hic3']) (by rw [hcor₃]; decide)
      (by rw [hs4_fr]; decide) (by decide) hout_disj
  obtain ⟨newOut, hnew⟩ : ∃ newOut,
      newOut = (Memory.spec 0).clientResult s₄ (shCollectCorrupted (extRes.handle, 0, 0, 0, 2)) :=
    ⟨_, rfl⟩
  obtain ⟨s₅, hs₅⟩ : ∃ s₅,
      s₅ = (Memory.spec 0).clientState s₄ (shCollectCorrupted (extRes.handle, 0, 0, 0, 2)) :=
    ⟨_, rfl⟩
  rw [← hnew] at hnewOut
  rw [← hs₅] at hfr₅
  refine ⟨s₀, s₁, s₂, s₃, s₄, s₅, h₀, h₁, h₂, extRes, newOut,
    rfl, hs₁, hh₀, hh₁, hs₂, hh₂, hs₃, hext, hs₄, hnew, hs₅,
    hm_alloc, hempty.2.2.2.2.2, htele, hfound, by omega, ?_, ?_, ?_⟩
  · rw [hnewOut, hcor₃]
  · rw [hic3'] at hm_cor; omega
  · rw [hfr₅, hs4_fr]

private theorem rankThresholdForEps_one_sixteenth :
    rankThresholdForEps (1 / 16 : ℚ) = 8 := by
  have hceil : Nat.ceil (12 / (1 / 16 : ℚ)) = 192 := by
    rw [show (12 / (1 / 16 : ℚ) : ℚ) = ((192 : ℕ) : ℚ) by norm_num, Nat.ceil_natCast]
  rw [rankThresholdForEps, hceil, show Nat.log 2 192 = 7 by decide]

-- Concrete rank-9 corrupted soft heap (`r = 8`, `origKey = 10 < ckey = 20`): exercises
-- `SHInv.origKey_le_ckey`, `shInv_corrupted_le_eps`, `shInv_corrupted_le`, and
-- non-empty `shCollectCorrupted_spec`.
example :
    ∃ (s' : Memory.State) (newOut : ℕ),
      let corMem : ℕ → ℕ := fun a =>
        if a = 19 then 99
        else if a = 20 then 10
        else if a = 1612 then 20
        else if a = 1613 then 9
        else if a = 1614 then 2
        else if a = 1615 then 1
        else if a = 1616 then 1
        else if a = 1617 then 1
        else if a = 1623 then 1
        else 0
      let hCor : SHHandle := ⟨16, 1600, 1, 512, 9, 8⟩
      let sCor : Memory.State := ⟨corMem, 14000⟩
      newOut = (Memory.spec 0).clientResult sCor (shCollectCorrupted (hCor, 0, 0, 0, 512)) ∧
      s' = (Memory.spec 0).clientState sCor (shCollectCorrupted (hCor, 0, 0, 0, 512)) ∧
      newOut = 1 ∧
      s'.mem 0 = 99 ∧
      memoryCost (shCollectCorrupted (hCor, 0, 0, 0, 512)) sCor ≤ 4096 := by
  let corMem : ℕ → ℕ := fun a =>
    if a = 19 then 99
    else if a = 20 then 10
    else if a = 1612 then 20
    else if a = 1613 then 9
    else if a = 1614 then 2
    else if a = 1615 then 1
    else if a = 1616 then 1
    else if a = 1617 then 1
    else if a = 1623 then 1
    else 0
  let itCor : SHItem := ⟨1, 99, 10⟩
  let tCor : SHTree := .node 1 9 20 [itCor] none none
  let hCor : SHHandle := ⟨16, 1600, 1, 512, 9, 8⟩
  let created : ℕ → ℕ := fun k => if k ≤ 9 then 512 / 2 ^ k else 0
  let sCor : Memory.State := ⟨corMem, 14000⟩
  have hwf : Memory.WellFormed 20 sCor := by
    refine { frontier_fits := by decide, mem_fits := fun a => ?_ }
    dsimp only [sCor, corMem]
    split_ifs <;> decide
  have hval : tCor.Valid 8 0 := by
    refine .node (by decide) (by simp [sizeCap, targetSize]) (by decide)
      (fun it hit => ?_) (fun hr => absurd hr (by decide)) (fun hlr => by simp at hlr)
      (fun c hc => by cases hc) (fun c hc => by cases hc)
      (fun c hc => by cases hc) (fun c hc => by cases hc)
    simp only [List.mem_singleton] at hit
    rw [hit]
    decide
  have hitem_rep : ItemListRep 16 corMem (corMem (1600 + 12 * 1 + 4))
      (corMem (1600 + 12 * 1 + 5)) [itCor] := by
    dsimp only [ItemListRep, corMem, itCor]
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  have htree_rep : TreeMemRep 8 16 1600 corMem tCor := by
    refine .node (by decide) (by dsimp only [corMem]; decide) (by dsimp only [corMem]; decide)
      ?_ (by dsimp only [corMem]; decide) hitem_rep
      (by dsimp only [corMem]; decide) (by dsimp only [corMem]; decide)
      (fun c hc => by cases hc) (fun c hc => by cases hc)
    simp [corMem, targetSize]
  have hroot_rep : RootListRep 1600 corMem 0 [tCor] :=
    ⟨fun _ hu => by simp at hu, by dsimp only [corMem]; decide, by dsimp only [corMem]; decide,
      by simp [suffixMinTree, corMem, tCor, SHTree.rootId], trivial⟩
  have hcreated_step : ∀ k,
      2 * created (k + 1) + [tCor].countP (fun t => decide (t.rank = k)) ≤ created k := by
    intro k
    by_cases hk9 : k = 9
    · subst hk9; simp [created, tCor, SHTree.rank]
    · have hcp : [tCor].countP (fun t => decide (t.rank = k)) = 0 := by
        simp [tCor, SHTree.rank, Ne.symm hk9]
      rw [hcp, Nat.add_zero]
      by_cases hklt : k < 9
      · have hk : k ≤ 9 := by omega
        have hk1 : k + 1 ≤ 9 := by omega
        simp only [created, hk, hk1, ↓reduceIte, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
        exact Nat.mul_div_le _ 2
      · have hnot : ¬ k ≤ 9 := by omega
        have hnot1 : ¬ k + 1 ≤ 9 := by omega
        simp [created, hnot, hnot1]
  have hlive_le : ∀ k, ([tCor].map (SHTree.countRank k)).sum ≤ created k := by
    intro k
    by_cases hk : k = 9
    · subst hk; simp [created, tCor, SHTree.countRank]
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, tCor,
        SHTree.countRank, Ne.symm hk, ↓reduceIte]
      exact Nat.zero_le _
  have hinv : SHInv 20 0 0 512 1024 hCor [tCor] created sCor := by
    refine ⟨by decide, hwf, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, Or.inl (by decide), by decide,
      by simp [forestNodeIds, tCor],
      fun id hid => by
        have : id = 1 := by simpa [forestNodeIds, tCor] using hid
        dsimp only [hCor]
        omega,
      by simp [forestItemIds, SHTree.itemIds, SHTree.allItems, tCor, itCor],
      fun id hid => by
        have : id = 1 := by
          simpa [forestItemIds, SHTree.itemIds, SHTree.allItems, tCor, itCor] using hid
        dsimp only [hCor]
        omega,
      ?_, fun t ht => ?_, fun t ht => ?_, hroot_rep, rfl, by decide,
      hcreated_step, hlive_le, fun t ht => ?_⟩
    · intro idx hpos hle hnot
      have hne : idx ≠ 1 := by simpa [forestNodeIds, tCor] using hnot
      dsimp only [sCor, corMem, hCor] at hle ⊢
      split_ifs <;> omega
    · simp only [List.mem_singleton] at ht; subst ht; exact hval
    · simp only [List.mem_singleton] at ht; subst ht; exact htree_rep
    · simp only [List.mem_singleton] at ht; subst ht; decide
  have hbound_eps :=
    shInv_corrupted_le_eps (ε := (1 / 16 : ℚ)) (by norm_num) hinv
      rankThresholdForEps_one_sixteenth.symm
  have hbound_gen : 2 ^ 8 * ((forestEntries [tCor]).filter
      (fun p => decide (p.1.origKey < p.2))).length ≤ 12 * 512 :=
    shInv_corrupted_le hinv
  have horig : itCor.origKey ≤ 20 :=
    hinv.origKey_le_ckey (itCor, 20) (by simp [forestEntries, tCor])
  have hout_disj : ∀ a, 0 + 0 ≤ a → a < 0 + 4 → ¬ InSHPool 0 0 512 1024 hCor a := by
    intro a _ ha hin
    dsimp only [InSHPool, hCor] at hin
    rcases hin with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  obtain ⟨_, _, hnew, _, _, _, hperm, hm⟩ :=
    shCollectCorrupted_spec (outBase := 0) (outCount := 0) (outCap := 4) (fuel := 512)
      hinv (by decide) (by simp [forestEntries, tCor, itCor]) (by decide) (by decide) hout_disj
  have hnew_val :
      (Memory.spec 0).clientResult sCor (shCollectCorrupted (hCor, 0, 0, 0, 512)) = 1 := by
    simpa [forestEntries, tCor, itCor] using hnew
  rw [hnew_val] at hperm
  have hperm_single :
      [((Memory.spec 0).clientState sCor
        (shCollectCorrupted (hCor, 0, 0, 0, 512))).mem 0].Perm [99] := by
    simpa [forestEntries, tCor, itCor] using hperm
  have hmem0 :
      ((Memory.spec 0).clientState sCor
        (shCollectCorrupted (hCor, 0, 0, 0, 512))).mem 0 = 99 := by
    simpa using (List.perm_singleton.mp hperm_single)
  have hm' :
      memoryCost (shCollectCorrupted (hCor, 0, 0, 0, 512)) sCor ≤ 4096 := by
    dsimp only [hCor] at hm
    omega
  exact ⟨_, _, rfl, rfl, hnew_val, hmem0, hm'⟩

private theorem entry_ckey_eq_of_zero_corrupted {st : List SHBatchEntry}
    (horig : ∀ e ∈ st, e.origKey ≤ e.ckey)
    (hcor0 : (st.filter (fun e => decide (e.origKey < e.ckey))).length = 0) :
    ∀ e ∈ st, e.ckey = e.origKey := by
  intro e he
  have hfilter_nil : st.filter (fun x => decide (x.origKey < x.ckey)) = [] :=
    List.length_eq_zero_iff.mp hcor0
  by_contra hne
  have hlt : decide (e.origKey < e.ckey) = true :=
    decide_eq_true (Nat.lt_of_le_of_ne (horig e he) (Ne.symm hne))
  have hmem : e ∈ st.filter (fun x => decide (x.origKey < x.ckey)) :=
    List.mem_filter.mpr ⟨he, hlt⟩
  rw [hfilter_nil] at hmem
  exact List.not_mem_nil hmem

private theorem forall₂_map_val_origKey :
    ∀ {xs ys : List SHBatchEntry},
      List.Forall₂
        (fun a b : SHBatchEntry => a.val = b.val ∧ a.origKey = b.origKey ∧ a.ckey ≤ b.ckey)
        xs ys →
      ys.map (fun e => (e.val, e.origKey)) = xs.map (fun e => (e.val, e.origKey))
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h hl => by
    simp only [List.map_cons, h.1, h.2.1, forall₂_map_val_origKey hl]

/-- Concrete batch soft-heap input (`r = 5`, 2 inserts, 3 extract-mins). -/
@[expose] def batchEx1 : SHBatchInput :=
  ⟨5, [.insert 42 100, .insert 7 50, .extractMin, .extractMin, .extractMin]⟩

/-- Concrete `w = 16` instantiation of `exists_singleSoftHeap_batch_standard_program`:
inserts `(42, 100)` and `(7, 50)` at `rankThreshold = 5`, performs 3 `extractMin`s, and checks
exact extracted `(found, val, key)` records (`⟨1, 7, 50⟩`, `⟨1, 42, 100⟩`, `⟨0, 0, 0⟩`),
`corCount = 0`, `WellFormed`, and steps. -/
theorem softHeap_standard_concrete :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ frontier : Fin r, ∃ out : Fin 3 → Fin r,
      ∃ y n, Runs 16 prog (State.init batchEx1.encode) ⟨pc, y⟩ n ∧
        let res : SHBatchResult := ⟨y.regs (out 0), y.regs (out 1), y.regs (out 2)⟩
        step 16 prog ⟨pc, y⟩ = .halt res.extBase ∧
        Memory.WellFormed 16 (memoryState frontier y) ∧
        res.corCount = 0 ∧
        SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase 0 = ⟨1, 7, 50⟩ ∧
        SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase 1 = ⟨1, 42, 100⟩ ∧
        SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase 2 = ⟨0, 0, 0⟩ ∧
        n + 1 ≤ C * 16 := by
  obtain ⟨r, C, pc, prog, hnw, hrf, frontier, out, hmain⟩ :=
    exists_singleSoftHeap_batch_standard_program
  have hw : Fits 16 batchEx1.wordBound := by decide
  obtain ⟨y, n, hruns, hhalt, hwf, _, _,
      ⟨trace, hexts, _, hcor_len, hcor_bnd⟩, hsteps⟩ := hmain batchEx1 hw
  let res : SHBatchResult := ⟨y.regs (out 0), y.regs (out 1), y.regs (out 2)⟩
  have hcor0 : res.corCount = 0 := by
    change 2 ^ 5 * res.corCount ≤ 12 * 2 at hcor_bnd
    omega
  obtain ⟨st0, st1, hst0, hst1, hsp0⟩ := trace.step_spec 0 (by decide)
  have hst0_nil : st0 = [] := by
    have hh := trace.states_head
    rw [List.head?_eq_getElem?] at hh
    rw [hh] at hst0
    exact (Option.some.inj hst0).symm
  dsimp only [SHBatchStepRel] at hsp0
  simp only [batchEx1, List.getElem?_cons_zero] at hsp0
  rcases hsp0 with ⟨e42, st1_r, hv42, hk42, hperm1, hf2_1, _⟩
  have hp1_pair : (st1.map (fun e => (e.val, e.origKey))).Perm [(42, 100)] := by
    have hpm := hperm1.map (fun e => (e.val, e.origKey))
    rw [List.map_cons, hv42, hk42, forall₂_map_val_origKey hf2_1, hst0_nil, List.map_nil] at hpm
    exact hpm
  obtain ⟨st1', st2, hst1', hst2, hsp1⟩ := trace.step_spec 1 (by decide)
  rw [hst1] at hst1'
  cases Option.some.inj hst1'
  dsimp only [SHBatchStepRel] at hsp1
  simp only [batchEx1, List.getElem?_cons_succ, List.getElem?_cons_zero] at hsp1
  rcases hsp1 with ⟨e7, st2_r, hv7, hk7, hperm2, hf2_2, _⟩
  have hp2_pair : (st2.map (fun e => (e.val, e.origKey))).Perm [(7, 50), (42, 100)] := by
    have hpm := hperm2.map (fun e => (e.val, e.origKey))
    rw [List.map_cons, hv7, hk7, forall₂_map_val_origKey hf2_2] at hpm
    exact hpm.trans (List.Perm.cons (7, 50) hp1_pair)
  have hck2 : ∀ e ∈ st2, e.ckey = e.origKey := by
    have hcb := trace.states_corrupted_bound 2 (by decide) st2 hst2
    have hc_cnt : (batchEx1.ops.take 2).countP SHOp.isInsert = 2 := by decide
    change 2 ^ 5 * (st2.filter (fun e => decide (e.origKey < e.ckey))).length ≤
      12 * (batchEx1.ops.take 2).countP SHOp.isInsert at hcb
    rw [hc_cnt] at hcb
    exact entry_ckey_eq_of_zero_corrupted
      (trace.states_origKey_le 2 (by decide) st2 hst2) (by omega)
  have he7_mem : (⟨7, 50, 50⟩ : SHBatchEntry) ∈ st2 := by
    have hm : (7, 50) ∈ st2.map (fun e => (e.val, e.origKey)) :=
      hp2_pair.mem_iff.mpr List.mem_cons_self
    rcases List.mem_map.mp hm with ⟨e, he_in, hpair⟩
    have hck := hck2 e he_in
    obtain ⟨h1v, h1k⟩ := Prod.ext_iff.mp hpair
    cases e; simp only at h1v h1k hck; subst h1v h1k hck; exact he_in
  have hst2_mem : ∀ e ∈ st2, e = ⟨7, 50, 50⟩ ∨ e = ⟨42, 100, 100⟩ := by
    intro e he
    have hm : (e.val, e.origKey) ∈ [(7, 50), (42, 100)] :=
      hp2_pair.mem_iff.mp (List.mem_map_of_mem he)
    have hck := hck2 e he
    rcases List.mem_cons.mp hm with h1 | h2
    · left
      obtain ⟨h1v, h1k⟩ := Prod.ext_iff.mp h1
      cases e; simp only at h1v h1k hck; subst h1v h1k hck; rfl
    · right
      obtain ⟨h2v, h2k⟩ := Prod.ext_iff.mp (List.mem_singleton.mp h2)
      cases e; simp only at h2v h2k hck; subst h2v h2k hck; rfl
  obtain ⟨st2', st3, hst2', hst3, hsp2⟩ := trace.step_spec 2 (by decide)
  rw [hst2] at hst2'
  cases Option.some.inj hst2'
  dsimp only [SHBatchStepRel] at hsp2
  have hop2 : batchEx1.ops[2]? = some .extractMin := rfl
  rw [hop2] at hsp2
  rcases hsp2 with ⟨ex0, hex0, _, hne2⟩
  have hst2_ne : st2 ≠ [] := List.ne_nil_of_mem he7_mem
  obtain ⟨e0, st2_rest, st3_perm, hst2_perm, hex0_eq, _, hmin0, hst3_perm, hf2_3⟩ :=
    hne2 hst2_ne
  have he0_in : e0 ∈ st2 := hst2_perm.mem_iff.mpr List.mem_cons_self
  have he0_eq : e0 = ⟨7, 50, 50⟩ := by
    have hle50 : e0.ckey ≤ 50 := hmin0 ⟨7, 50, 50⟩ he7_mem
    rcases hst2_mem e0 he0_in with rfl | rfl
    · rfl
    · simp only at hle50; omega
  have hex0_val : ex0 = ⟨1, 7, 50⟩ := by rw [hex0_eq, he0_eq]
  have hp3_pair : (st3.map (fun e => (e.val, e.origKey))).Perm [(42, 100)] := by
    have hpm : ((7, 50) :: st2_rest.map (fun e => (e.val, e.origKey))).Perm
        [(7, 50), (42, 100)] := by
      have h1 := (hst2_perm.symm.map (fun e => (e.val, e.origKey))).trans hp2_pair
      simpa only [List.map_cons, he0_eq] using h1
    have hrest_pair := hpm.cons_inv
    have h3 := hst3_perm.map (fun e => (e.val, e.origKey))
    rw [forall₂_map_val_origKey hf2_3] at h3
    exact h3.trans hrest_pair
  have hck3 : ∀ e ∈ st3, e.ckey = e.origKey := by
    have hcb := trace.states_corrupted_bound 3 (by decide) st3 hst3
    have hc_cnt : (batchEx1.ops.take 3).countP SHOp.isInsert = 2 := by decide
    change 2 ^ 5 * (st3.filter (fun e => decide (e.origKey < e.ckey))).length ≤
      12 * (batchEx1.ops.take 3).countP SHOp.isInsert at hcb
    rw [hc_cnt] at hcb
    exact entry_ckey_eq_of_zero_corrupted
      (trace.states_origKey_le 3 (by decide) st3 hst3) (by omega)
  have hlen3 : st3.length = 1 := by
    have hl := hp3_pair.length_eq
    simp only [List.length_map, List.length_singleton] at hl
    exact hl
  obtain ⟨st3', st4, hst3', hst4, hsp3⟩ := trace.step_spec 3 (by decide)
  rw [hst3] at hst3'
  cases Option.some.inj hst3'
  dsimp only [SHBatchStepRel] at hsp3
  have hop3 : batchEx1.ops[3]? = some .extractMin := rfl
  rw [hop3] at hsp3
  rcases hsp3 with ⟨ex1, hex1, _, hne3⟩
  have hst3_ne : st3 ≠ [] := by intro h; rw [h, List.length_nil] at hlen3; omega
  obtain ⟨e1, st3_rest, st4_perm, hst3_perm2, hex1_eq, _, _, hst4_perm, hf2_4⟩ :=
    hne3 hst3_ne
  have he1_in : e1 ∈ st3 := hst3_perm2.mem_iff.mpr List.mem_cons_self
  have he1_eq : e1 = ⟨42, 100, 100⟩ := by
    have hm : (e1.val, e1.origKey) ∈ [(42, 100)] :=
      hp3_pair.mem_iff.mp (List.mem_map_of_mem he1_in)
    have hck := hck3 e1 he1_in
    obtain ⟨h1v, h1k⟩ := Prod.ext_iff.mp (List.mem_singleton.mp hm)
    cases e1; simp only at h1v h1k hck; subst h1v h1k hck; rfl
  have hex1_val : ex1 = ⟨1, 42, 100⟩ := by rw [hex1_eq, he1_eq]
  have hlen4 : st4.length = 0 := by
    have hl1 := hst3_perm2.length_eq
    have hl2 := hst4_perm.length_eq
    have hl3 := hf2_4.length_eq
    simp only [List.length_cons] at hl1
    omega
  have hst4_nil : st4 = [] := List.length_eq_zero_iff.mp hlen4
  obtain ⟨st4', st5, hst4', _, hsp4⟩ := trace.step_spec 4 (by decide)
  rw [hst4] at hst4'
  cases Option.some.inj hst4'
  dsimp only [SHBatchStepRel] at hsp4
  have hop4 : batchEx1.ops[4]? = some .extractMin := rfl
  rw [hop4] at hsp4
  rcases hsp4 with ⟨ex2, hex2, hemp4, _⟩
  have hex2_eq : ex2 = ⟨0, 0, 0⟩ := (hemp4 hst4_nil).1
  have hread : ∀ k < 3,
      trace.extracts[k]? =
        some (SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase k) := by
    intro k hk
    have hmap := congrArg (fun xs => xs[k]?) hexts
    have hne_val : batchEx1.numExtracts = 3 := by decide
    change (List.map (SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase)
      (List.range batchEx1.numExtracts))[k]? = trace.extracts[k]? at hmap
    rw [hne_val] at hmap
    simpa only [List.getElem?_map, List.getElem?_range, hk, ↓reduceIte, Option.map_some] using
      hmap.symm
  have hcnt0 : (batchEx1.ops.take 2).countP SHOp.isExtract = 0 := by decide
  have hcnt1 : (batchEx1.ops.take 3).countP SHOp.isExtract = 1 := by decide
  have hcnt2 : (batchEx1.ops.take 4).countP SHOp.isExtract = 2 := by decide
  have hr0 : SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase 0 = ex0 := by
    rw [hcnt0] at hex0
    exact Option.some.inj ((hread 0 (by decide)).symm.trans hex0)
  have hr1 : SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase 1 = ex1 := by
    rw [hcnt1] at hex1
    exact Option.some.inj ((hread 1 (by decide)).symm.trans hex1)
  have hr2 : SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase 2 = ex2 := by
    rw [hcnt2] at hex2
    exact Option.some.inj ((hread 2 (by decide)).symm.trans hex2)
  have hni : batchEx1.numInserts = 2 := by decide
  have hne : batchEx1.numExtracts = 3 := by decide
  have hrt : batchEx1.rankThreshold = 5 := rfl
  have hsteps' : n + 1 ≤ C * 16 := by
    rw [hni, hne, hrt] at hsteps
    exact hsteps
  refine ⟨r, C, pc, prog, hnw, hrf, frontier, out, y, n, hruns, hhalt, hwf, hcor0,
    ?_, ?_, ?_, hsteps'⟩
  · rw [hr0, hex0_val]
  · rw [hr1, hex1_val]
  · rw [hr2, hex2_eq]

/-- Concrete batch soft-heap input (`ε = 1 / 4`, 3 inserts, 1 extract-min). -/
@[expose] def batchExEps : SHBatchInput :=
  ⟨rankThresholdForEps (1 / 4 : ℚ),
    [.insert 11 30, .insert 22 10, .insert 33 20, .extractMin]⟩

/-- Concrete `w = 16` instantiation of `exists_singleSoftHeap_batch_standard_program_eps` at
`ε = 1 / 4`: verifies `rankThresholdForEps (1 / 4) = 6`, `(res.corCount : ℚ) ≤ (1 / 4 : ℚ) * 3`,
`res.corCount = 0`, exact extracted record `⟨1, 22, 10⟩`, and `n + 1 ≤ C * 23`. -/
theorem softHeap_standard_eps_concrete :
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ frontier : Fin r, ∃ out : Fin 3 → Fin r,
      ∃ y n, Runs 16 prog (State.init batchExEps.encode) ⟨pc, y⟩ n ∧
        let res : SHBatchResult := ⟨y.regs (out 0), y.regs (out 1), y.regs (out 2)⟩
        step 16 prog ⟨pc, y⟩ = .halt res.extBase ∧
        Memory.WellFormed 16 (memoryState frontier y) ∧
        (res.corCount : ℚ) ≤ (1 / 4 : ℚ) * 3 ∧
        res.corCount = 0 ∧
        SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase 0 = ⟨1, 22, 10⟩ ∧
        n + 1 ≤ C * 23 := by
  obtain ⟨r, C, pc, prog, hnw, hrf, frontier, out, hmain⟩ :=
    exists_singleSoftHeap_batch_standard_program_eps
  have hrt6 : rankThresholdForEps (1 / 4 : ℚ) = 6 := by
    have hceil : Nat.ceil (12 / (1 / 4 : ℚ)) = 48 := by
      rw [show (12 / (1 / 4 : ℚ) : ℚ) = ((48 : ℕ) : ℚ) by norm_num, Nat.ceil_natCast]
    rw [rankThresholdForEps, hceil, show Nat.log 2 48 = 5 by decide]
  have hwb : batchExEps.wordBound = 2203 := by
    dsimp only [batchExEps, SHBatchInput.wordBound, shFuelBound, SHBatchInput.maxWord]
    rw [hrt6]
    decide
  have hw : Fits 16 batchExEps.wordBound := by rw [hwb]; decide
  obtain ⟨y, n, hruns, hhalt, hwf, _, _,
      ⟨trace, hexts, _, _, hcor_eps, hper_step⟩, hsteps⟩ :=
    hmain (1 / 4 : ℚ) (by norm_num) batchExEps rfl hw
  let res : SHBatchResult := ⟨y.regs (out 0), y.regs (out 1), y.regs (out 2)⟩
  have hni : batchExEps.numInserts = 3 := by decide
  have hne : batchExEps.numExtracts = 1 := by decide
  have hcor_eps' : (res.corCount : ℚ) ≤ (1 / 4 : ℚ) * 3 := by
    change (res.corCount : ℚ) ≤ (1 / 4 : ℚ) * (batchExEps.numInserts : ℚ) at hcor_eps
    rw [hni] at hcor_eps
    exact hcor_eps
  have hcor0 : res.corCount = 0 := by
    by_contra hne0
    have h1 : (1 : ℚ) ≤ (res.corCount : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hne0
    linarith
  obtain ⟨st0, st1, hst0, hst1, hsp0⟩ := trace.step_spec 0 (by decide)
  have hst0_nil : st0 = [] := by
    have hh := trace.states_head
    rw [List.head?_eq_getElem?] at hh
    rw [hh] at hst0
    exact (Option.some.inj hst0).symm
  dsimp only [SHBatchStepRel] at hsp0
  simp only [batchExEps, List.getElem?_cons_zero] at hsp0
  rcases hsp0 with ⟨e1, st1_r, hv1, hk1, hperm1, hf2_1, _⟩
  have hp1_pair : (st1.map (fun e => (e.val, e.origKey))).Perm [(11, 30)] := by
    have hpm := hperm1.map (fun e => (e.val, e.origKey))
    rw [List.map_cons, hv1, hk1, forall₂_map_val_origKey hf2_1, hst0_nil, List.map_nil] at hpm
    exact hpm
  obtain ⟨st1', st2, hst1', hst2, hsp1⟩ := trace.step_spec 1 (by decide)
  rw [hst1] at hst1'
  cases Option.some.inj hst1'
  dsimp only [SHBatchStepRel] at hsp1
  simp only [batchExEps, List.getElem?_cons_succ, List.getElem?_cons_zero] at hsp1
  rcases hsp1 with ⟨e2, st2_r, hv2, hk2, hperm2, hf2_2, _⟩
  have hp2_pair : (st2.map (fun e => (e.val, e.origKey))).Perm [(22, 10), (11, 30)] := by
    have hpm := hperm2.map (fun e => (e.val, e.origKey))
    rw [List.map_cons, hv2, hk2, forall₂_map_val_origKey hf2_2] at hpm
    exact hpm.trans (List.Perm.cons (22, 10) hp1_pair)
  obtain ⟨st2', st3, hst2', hst3, hsp2⟩ := trace.step_spec 2 (by decide)
  rw [hst2] at hst2'
  cases Option.some.inj hst2'
  dsimp only [SHBatchStepRel] at hsp2
  simp only [batchExEps, List.getElem?_cons_succ, List.getElem?_cons_zero] at hsp2
  rcases hsp2 with ⟨e3, st3_r, hv3, hk3, hperm3, hf2_3, _⟩
  have hp3_pair :
      (st3.map (fun e => (e.val, e.origKey))).Perm [(33, 20), (22, 10), (11, 30)] := by
    have hpm := hperm3.map (fun e => (e.val, e.origKey))
    rw [List.map_cons, hv3, hk3, forall₂_map_val_origKey hf2_3] at hpm
    exact hpm.trans (List.Perm.cons (33, 20) hp2_pair)
  have hck3 : ∀ e ∈ st3, e.ckey = e.origKey := by
    have hps := hper_step 3 (by decide) st3 hst3
    have hc_cnt : (batchExEps.ops.take 3).countP SHOp.isInsert = 3 := by decide
    rw [hc_cnt] at hps
    have hlen_cor0 : (st3.filter (fun e => decide (e.origKey < e.ckey))).length = 0 := by
      by_contra hne_cor
      have h1 : (1 : ℚ) ≤ ((st3.filter (fun e => decide (e.origKey < e.ckey))).length : ℚ) := by
        exact_mod_cast Nat.pos_of_ne_zero hne_cor
      norm_num at hps
      linarith
    exact entry_ckey_eq_of_zero_corrupted
      (trace.states_origKey_le 3 (by decide) st3 hst3) hlen_cor0
  have he22_mem : (⟨22, 10, 10⟩ : SHBatchEntry) ∈ st3 := by
    have hm : (22, 10) ∈ st3.map (fun e => (e.val, e.origKey)) :=
      hp3_pair.mem_iff.mpr (List.mem_cons_of_mem _ List.mem_cons_self)
    rcases List.mem_map.mp hm with ⟨e, he_in, hpair⟩
    have hck := hck3 e he_in
    obtain ⟨h1v, h1k⟩ := Prod.ext_iff.mp hpair
    cases e; simp only at h1v h1k hck; subst h1v h1k hck; exact he_in
  obtain ⟨st3', st4, hst3', _, hsp3⟩ := trace.step_spec 3 (by decide)
  rw [hst3] at hst3'
  cases Option.some.inj hst3'
  dsimp only [SHBatchStepRel] at hsp3
  have hop3 : batchExEps.ops[3]? = some .extractMin := rfl
  rw [hop3] at hsp3
  rcases hsp3 with ⟨ex0, hex0, _, hne3⟩
  have hst3_ne : st3 ≠ [] := List.ne_nil_of_mem he22_mem
  obtain ⟨e0, _, _, hst3_perm, hex0_eq, _, hmin0, _, _⟩ := hne3 hst3_ne
  have he0_in : e0 ∈ st3 := hst3_perm.mem_iff.mpr List.mem_cons_self
  have he0_eq : e0 = ⟨22, 10, 10⟩ := by
    have hle10 : e0.ckey ≤ 10 := hmin0 ⟨22, 10, 10⟩ he22_mem
    have hm : (e0.val, e0.origKey) ∈ [(33, 20), (22, 10), (11, 30)] :=
      hp3_pair.mem_iff.mp (List.mem_map_of_mem he0_in)
    have hck := hck3 e0 he0_in
    rcases List.mem_cons.mp hm with h33 | hrest
    · obtain ⟨hv, hk⟩ := Prod.ext_iff.mp h33; cases e0; simp only at hv hk hck hle10; omega
    · rcases List.mem_cons.mp hrest with h22 | h11
      · obtain ⟨hv, hk⟩ := Prod.ext_iff.mp h22
        cases e0; simp only at hv hk hck; subst hv hk hck; rfl
      · obtain ⟨hv, hk⟩ := Prod.ext_iff.mp (List.mem_singleton.mp h11)
        cases e0; simp only at hv hk hck hle10; omega
  have hread0 :
      trace.extracts[0]? =
        some (SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase 0) := by
    have hmap := congrArg (fun xs => xs[0]?) hexts
    change (List.map (SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase)
      (List.range batchExEps.numExtracts))[0]? = trace.extracts[0]? at hmap
    rw [hne] at hmap
    simpa only [List.range_one, List.map_cons, List.map_nil, List.getElem?_cons_zero] using
      hmap.symm
  have hcnt0 : (batchExEps.ops.take 3).countP SHOp.isExtract = 0 := by decide
  have hr0 : SHBatchExtract.readFrom (memoryState frontier y).mem res.extBase 0 = ex0 := by
    rw [hcnt0] at hex0
    exact Option.some.inj (hread0.symm.trans hex0)
  have hsteps' : n + 1 ≤ C * 23 := by
    rw [hni, hne, hrt6] at hsteps
    exact hsteps
  refine ⟨r, C, pc, prog, hnw, hrf, frontier, out, y, n, hruns, hhalt, hwf,
    hcor_eps', hcor0, ?_, hsteps'⟩
  rw [hr0, hex0_eq, he0_eq]

end CslibFrontierTests.SoftHeap
