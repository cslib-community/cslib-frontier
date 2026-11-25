/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpTickHealProg.HealRt
import CslibFrontier.Tactic.Realize

/-!
# Final Bucket Metadata, Trie-Child Zeroing, and Header Finalization for `csrToFastGenProg`

This internal module implements Phases F and G of `csrToFastGenProg`:
* **`fillFinalBktMetaLoopProg`** (Phase F): writes final per-bucket scalar fields `0` and `2..9`
  in `offBktMeta` while preserving candidate salts at `16 * b + 1` and B+-tree root/alloc metadata
  at `16 * b + 10..15`.
* **`zeroTrieChildrenLoopProg`** (Phase G1): clears both epoch buffer tries' child arrays
  `offTrieChild0` and `offTrieChild1`.
* **`writeHealHdrsAndTrieMetaProg`** (Phase G2): clears root `nodeActive` flags in `offTrieMeta0`
  and `offTrieMeta1` and writes the fast-mode header words `base .. base + 15`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fillFinalBktMetaLoopProg`,
  `zeroTrieChildrenLoopProg`, `writeHealHdrsAndTrieMetaProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fillFinalBktMetaLoop`,
  `fillFinalBktMetaLoop_safe`, `fillFinalBktMetaLoop_spec`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_zeroTrieChildrenLoop`,
  `zeroTrieChildrenLoop_safe`, `zeroTrieChildrenLoop_spec`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_writeHealHdrsAndTrieMeta`,
  `writeHealHdrsAndTrieMetaProg_spec`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ## Phase F: `fillFinalBktMetaLoopProg` (write final bucket scalar fields `0, 2..9`) -/

/-- Single bucket step of `fillFinalBktMetaLoopProg`. -/
@[irreducible] def fillFinalBktMetaStepProg : HealRt × ℕ → Memory.Prog ℕ
  | (rt, b_in) => do
    let b ← pure b_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let b1 ← pure (b + one_v)
    let lo ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b)
    let hi ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b1)
    let i0 ← pure (16 * b)
    let i2 ← pure (16 * b + 2)
    let i3 ← pure (16 * b + 3)
    let i4 ← pure (16 * b + 4)
    let i5 ← pure (16 * b + 5)
    let i6 ← pure (16 * b + 6)
    let i7 ← pure (16 * b + 7)
    let i8 ← pure (16 * b + 8)
    let i9 ← pure (16 * b + 9)
    writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), i2), zero_v)
    writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), i4), one_v)
    writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), i5), zero_v)
    writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), i6), zero_v)
    writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), i7), zero_v)
    writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), i8), zero_v)
    writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), i9), zero_v)
    if lo ≤ hi then
      let d_cnt ← pure (hi - lo)
      if d_cnt ≤ hlNMax rt then
        writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), i0), d_cnt)
        writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), i3), d_cnt)
        pure b1
      else
        writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), i0), zero_v)
        writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), i3), zero_v)
        pure b1
    else
      writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), i0), zero_v)
      writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), i3), zero_v)
      pure b1

private theorem memoryCost_fillFinalBktMetaStep_pos (d : HealRt × ℕ) (s : Memory.State) :
    0 < memoryCost (fillFinalBktMetaStepProg d) s := by
  rcases d with ⟨rt, b⟩
  unfold fillFinalBktMetaStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

private theorem realizes_fillFinalBktMetaStep :
    Realizes .exact fillFinalBktMetaStepProg
      (WordEncoding.encode (α := HealRt × ℕ))
      (WordEncoding.encode (α := ℕ))
      HealBktStepPre
      (fun _ _ => 0) := by
  unfold fillFinalBktMetaStepProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨rt, b⟩
    dsimp only [HealBktStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hb_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨hM_lt, h16M, _, _, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := WhpLargeEnv.seg_end_le c U V w n_max
    dsimp only [mkHealRt, hlBase, hlW, hlNMax, hlM, hlGBits, hlOffBm, hlOffFb] at *
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact to_true_exists (henv.packed_safe_of_le hgk (idx := b) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists (henv.packed_safe_of_le hgk (idx := b + 1) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists (henv.bktMeta_safe (idx := _) (by omega))
  )

/-- Loop writing final bucket scalar metadata across `rem` buckets. -/
@[irreducible] def fillFinalBktMetaLoopProg : (HealRt × ℕ) × ℕ → Memory.Prog ℕ
  | ((rt, b₀), rem) => iterate fillFinalBktMetaStepProg rt rem b₀

/-- `Realizes .exact` certificate for `fillFinalBktMetaLoopProg`. -/
theorem realizes_fillFinalBktMetaLoop :
    Realizes .exact fillFinalBktMetaLoopProg
      (WordEncoding.encode (α := (HealRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((rt, b₀), rem) s =>
        iterationSafe fillFinalBktMetaStepProg HealBktStepPre w rt rem b₀ s)
      (fun _ _ => 0) := by
  unfold fillFinalBktMetaLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt))
    (WordEncoding.encode (α := ℕ))
    realizes_fillFinalBktMetaStep
    memoryCost_fillFinalBktMetaStep_pos

/-- Loop-safety invariant for `fillFinalBktMetaLoopProg`. -/
theorem fillFinalBktMetaLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ numBucketsWhp n_max →
      iterationSafe fillFinalBktMetaStepProg HealBktStepPre w rt rem b₀ s :=
  iterationSafe_of_stateless_step fillFinalBktMetaStepProg HealBktStepPre
    (fun _ hb _ => ⟨⟨c, U, V, w, n_max, henv, rfl⟩, hb⟩)
    (fun _ _ _ => by
      unfold fillFinalBktMetaStepProg; dsimp only [readPackedGenProg, writePackedGenProg]
      simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedProg,
        clientResult_bind, clientState_readPackedProg]
      repeat rw [clientResult_bind, clientState_writePackedProg]
      split_ifs <;>
        (rw [clientResult_bind, clientState_writePackedProg, clientResult_bind]; rfl))

/-- Exact memory specification of `fillFinalBktMetaLoopProg`. -/
theorem fillFinalBktMetaLoop_spec {c U V w n_max base : ℕ} {fbStart : ℕ → ℕ}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hfb_adj : ∀ b < numBucketsWhp n_max,
      fbStart b ≤ fbStart (b + 1) ∧ fbStart (b + 1) - fbStart b ≤ n_max)
    (hfb_mem : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s₀.mem x = fbStart x) :
    let rt := mkHealRt c U V w n_max base
    let M := numBucketsWhp n_max
    let gBits := globalPtrBits n_max
    let bm := offBktMeta c U V w n_max
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ M →
      (∀ b < b₀,
        let cnt := fbStart (b + 1) - fbStart b
        readPacked (base + bm) gBits w s.mem (16 * b + 0) = cnt ∧
        readPacked (base + bm) gBits w s.mem (16 * b + 2) = 0 ∧
        readPacked (base + bm) gBits w s.mem (16 * b + 3) = cnt ∧
        readPacked (base + bm) gBits w s.mem (16 * b + 4) = 1 ∧
        readPacked (base + bm) gBits w s.mem (16 * b + 5) = 0 ∧
        readPacked (base + bm) gBits w s.mem (16 * b + 6) = 0 ∧
        readPacked (base + bm) gBits w s.mem (16 * b + 7) = 0 ∧
        readPacked (base + bm) gBits w s.mem (16 * b + 8) = 0 ∧
        readPacked (base + bm) gBits w s.mem (16 * b + 9) = 0) →
      (∀ idx < 16 * M, (idx % 16 = 1 ∨ 10 ≤ idx % 16) →
        readPacked (base + bm) gBits w s.mem idx = readPacked (base + bm) gBits w s₀.mem idx) →
      (∀ a, (a < base + bm ∨ base + offFbStart c U V w n_max ≤ a) → s.mem a = s₀.mem a) →
      let prog := fillFinalBktMetaLoopProg ((rt, b₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ b < b₀ + rem,
        let cnt := fbStart (b + 1) - fbStart b
        readPacked (base + bm) gBits w s'.mem (16 * b + 0) = cnt ∧
        readPacked (base + bm) gBits w s'.mem (16 * b + 2) = 0 ∧
        readPacked (base + bm) gBits w s'.mem (16 * b + 3) = cnt ∧
        readPacked (base + bm) gBits w s'.mem (16 * b + 4) = 1 ∧
        readPacked (base + bm) gBits w s'.mem (16 * b + 5) = 0 ∧
        readPacked (base + bm) gBits w s'.mem (16 * b + 6) = 0 ∧
        readPacked (base + bm) gBits w s'.mem (16 * b + 7) = 0 ∧
        readPacked (base + bm) gBits w s'.mem (16 * b + 8) = 0 ∧
        readPacked (base + bm) gBits w s'.mem (16 * b + 9) = 0) ∧
      (∀ idx < 16 * M, (idx % 16 = 1 ∨ 10 ≤ idx % 16) →
        readPacked (base + bm) gBits w s'.mem idx = readPacked (base + bm) gBits w s₀.mem idx) ∧
      (∀ a, (a < base + bm ∨ base + offFbStart c U V w n_max ≤ a) → s'.mem a = s₀.mem a) := by
  intro rt M gBits bm rem
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  obtain ⟨_, _, _, _, _, _, _, hgk⟩ := hl_bounds henv
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + bm + packedWords (16 * M) gBits w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  have hfb_b : base + offFbStart c U V w n_max + packedWords (M + 1) gBits w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.1 _
  have hbm_end : bm + packedWords (16 * M) gBits w = offFbStart c U V w n_max := rfl
  have h0_pow : 0 < 2 ^ gBits := Nat.two_pow_pos _
  have h1_pow : 1 < 2 ^ gBits := Nat.one_lt_two_pow (globalPtrBits_pos_of_large hth).ne'
  induction rem with
  | zero =>
    intro b₀ s _ hprev hkeep hout
    unfold fillFinalBktMetaLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, hkeep, hout⟩
  | succ rem ih =>
    intro b₀ s hle hprev hkeep hout
    have hb_lt : b₀ < M := by omega
    have hfb_s : ∀ x ≤ M,
        readPacked (base + offFbStart c U V w n_max) gBits w s.mem x = fbStart x :=
      fun x hx => (readPacked_congr hw (fun a ⟨ha1, _⟩ => hout a (Or.inr ha1))
        (Nat.lt_succ_of_le hx)).trans (hfb_mem x hx)
    obtain ⟨hlo_hi, hcnt_le⟩ := hfb_adj b₀ hb_lt
    set cnt := fbStart (b₀ + 1) - fbStart b₀
    have hcnt_pow : cnt < 2 ^ gBits := lt_two_pow_globalPtrBits_of_le_n_max hcnt_le
    let wpAt := fun m idx v => writePacked (base + bm) gBits w m idx v
    set m1 := wpAt (wpAt (wpAt (wpAt (wpAt (wpAt (wpAt (wpAt (wpAt s.mem
      (16 * b₀ + 2) 0) (16 * b₀ + 4) 1) (16 * b₀ + 5) 0) (16 * b₀ + 6) 0)
      (16 * b₀ + 7) 0) (16 * b₀ + 8) 0) (16 * b₀ + 9) 0) (16 * b₀) cnt) (16 * b₀ + 3) cnt
    set p1 := fillFinalBktMetaStepProg (rt, b₀)
    have hs1 : StepSpec w (base + largeSpaceWhp c U V w n_max) s p1
        { mem := m1, frontier := s.frontier } (b₀ + 1) := by
      dsimp only [p1]; unfold fillFinalBktMetaStepProg
      dsimp only [rt, mkHealRt, hlBase, hlW, hlNMax, hlGBits, hlOffBm, hlOffFb]
      simp only [pure_bind]
      refine (StepSpec.readPackedGen_eq hw (by omega) hfb_b (hfb_s b₀ hb_lt.le)).bind ?_
      refine (StepSpec.readPackedGen_eq hw (by omega) hfb_b (hfb_s (b₀ + 1) hb_lt)).bind ?_
      refine (StepSpec.writePackedGen (N := 16 * M) hw hgk (by omega) hbm_b).bind ?_
      refine (StepSpec.writePackedGen (N := 16 * M) hw hgk (by omega) hbm_b).bind ?_
      refine (StepSpec.writePackedGen (N := 16 * M) hw hgk (by omega) hbm_b).bind ?_
      refine (StepSpec.writePackedGen (N := 16 * M) hw hgk (by omega) hbm_b).bind ?_
      refine (StepSpec.writePackedGen (N := 16 * M) hw hgk (by omega) hbm_b).bind ?_
      refine (StepSpec.writePackedGen (N := 16 * M) hw hgk (by omega) hbm_b).bind ?_
      refine (StepSpec.writePackedGen (N := 16 * M) hw hgk (by omega) hbm_b).bind ?_
      simp only [hlo_hi, show fbStart (b₀ + 1) - fbStart b₀ ≤ n_max from hcnt_le, ↓reduceIte]
      refine (StepSpec.writePackedGen (N := 16 * M) hw hgk (by omega) hbm_b).bind ?_
      exact (StepSpec.writePackedGen (N := 16 * M) hw hgk (by omega) hbm_b).bind
        (StepSpec.pure _ _)
    set s1 : Memory.State := { mem := m1, frontier := s.frontier }
    have hne_m1 : ∀ idx, idx ≠ 16 * b₀ → idx ≠ 16 * b₀ + 2 → idx ≠ 16 * b₀ + 3 →
        idx ≠ 16 * b₀ + 4 → idx ≠ 16 * b₀ + 5 → idx ≠ 16 * b₀ + 6 →
        idx ≠ 16 * b₀ + 7 → idx ≠ 16 * b₀ + 8 → idx ≠ 16 * b₀ + 9 →
        readPacked (base + bm) gBits w m1 idx = readPacked (base + bm) gBits w s.mem idx := by
      intro idx h0 h2 h3 h4 h5 h6 h7 h8 h9
      dsimp only [m1, wpAt]
      rw [readPacked_writePacked_of_ne hw _ h3, readPacked_writePacked_of_ne hw _ h0,
        readPacked_writePacked_of_ne hw _ h9, readPacked_writePacked_of_ne hw _ h8,
        readPacked_writePacked_of_ne hw _ h7, readPacked_writePacked_of_ne hw _ h6,
        readPacked_writePacked_of_ne hw _ h5, readPacked_writePacked_of_ne hw _ h4,
        readPacked_writePacked_of_ne hw _ h2]
    have hprev1 : ∀ b < b₀ + 1,
        let c_b := fbStart (b + 1) - fbStart b
        readPacked (base + bm) gBits w s1.mem (16 * b + 0) = c_b ∧
        readPacked (base + bm) gBits w s1.mem (16 * b + 2) = 0 ∧
        readPacked (base + bm) gBits w s1.mem (16 * b + 3) = c_b ∧
        readPacked (base + bm) gBits w s1.mem (16 * b + 4) = 1 ∧
        readPacked (base + bm) gBits w s1.mem (16 * b + 5) = 0 ∧
        readPacked (base + bm) gBits w s1.mem (16 * b + 6) = 0 ∧
        readPacked (base + bm) gBits w s1.mem (16 * b + 7) = 0 ∧
        readPacked (base + bm) gBits w s1.mem (16 * b + 8) = 0 ∧
        readPacked (base + bm) gBits w s1.mem (16 * b + 9) = 0 := by
      intro b hb
      rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hlt | rfl
      · have hp := hprev b hlt
        have hne_b : ∀ r < 10,
            readPacked (base + bm) gBits w m1 (16 * b + r) =
              readPacked (base + bm) gBits w s.mem (16 * b + r) :=
          fun r hr => hne_m1 _ (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)
        exact ⟨(hne_b 0 (by omega)).trans hp.1,
          (hne_b 2 (by omega)).trans hp.2.1,
          (hne_b 3 (by omega)).trans hp.2.2.1,
          (hne_b 4 (by omega)).trans hp.2.2.2.1,
          (hne_b 5 (by omega)).trans hp.2.2.2.2.1,
          (hne_b 6 (by omega)).trans hp.2.2.2.2.2.1,
          (hne_b 7 (by omega)).trans hp.2.2.2.2.2.2.1,
          (hne_b 8 (by omega)).trans hp.2.2.2.2.2.2.2.1,
          (hne_b 9 (by omega)).trans hp.2.2.2.2.2.2.2.2⟩
      · dsimp only [s1, m1, wpAt]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (
          repeat rw [readPacked_writePacked_of_ne hw _ (by omega)]
          exact readPacked_writePacked_self _ _ _ _ _
            (by first | exact hcnt_pow | exact h1_pow | exact h0_pow))
    have hkeep1 : ∀ idx < 16 * M, (idx % 16 = 1 ∨ 10 ≤ idx % 16) →
        readPacked (base + bm) gBits w s1.mem idx = readPacked (base + bm) gBits w s₀.mem idx := by
      intro idx hidx hmod
      dsimp only [s1]
      rw [hne_m1 idx (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)]
      exact hkeep idx hidx hmod
    have hout1 : ∀ a, (a < base + bm ∨ base + offFbStart c U V w n_max ≤ a) →
        s1.mem a = s₀.mem a := by
      intro a ha
      dsimp only [s1, m1, wpAt]
      have hdisj : a < base + bm ∨ base + bm + packedWords (16 * M) gBits w ≤ a := by
        dsimp only [M, gBits, bm] at ha hbm_end ⊢; omega
      repeat rw [writePacked_outside hw (N := 16 * M) _ (by omega) _ (by cases hdisj <;> omega)]
      exact hout a ha
    obtain ⟨hf_r, hvp_r, hp_r, hkeep_r, hout_r⟩ := ih (b₀ + 1) s1 (by omega) hprev1 hkeep1 hout1
    have hadd : b₀ + 1 + rem = b₀ + (rem + 1) := by omega
    rw [hadd] at hp_r
    unfold fillFinalBktMetaLoopProg at hf_r hvp_r hp_r hkeep_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hf_r
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro b hb; rw [clientState_bind, hs1.1, hs1.2.1]; exact hp_r b hb
    · intro idx hidx hmod
      rw [clientState_bind, hs1.1, hs1.2.1]; exact hkeep_r idx hidx hmod
    · intro a ha; rw [clientState_bind, hs1.1, hs1.2.1]; exact hout_r a ha

/-! ## Phase G: `zeroTrieChildrenLoopProg` and `writeHealHdrsAndTrieMetaProg` -/

/-- Single index step of `zeroTrieChildrenLoopProg`. -/
@[irreducible] def zeroTrieChildrenStepProg :
    (HealRt × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | ((rt, (tc0_in, tc1_in)), idx_in) => do
    let tc0 ← pure tc0_in
    let tc1 ← pure tc1_in
    let idx ← pure idx_in
    let zero_v ← pure 0
    let one_v ← pure 1
    writePackedGenProg ((((hlBase rt, tc0), (hlGBits rt, hlW rt)), idx), zero_v)
    writePackedGenProg ((((hlBase rt, tc1), (hlGBits rt, hlW rt)), idx), zero_v)
    pure (idx + one_v)

private theorem memoryCost_zeroTrieChildrenStep_pos
    (d : (HealRt × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    0 < memoryCost (zeroTrieChildrenStepProg d) s := by
  rcases d with ⟨⟨rt, tc0, tc1⟩, idx⟩
  unfold zeroTrieChildrenStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 4 + (4 + 0)
  omega

/-- Precondition for `zeroTrieChildrenStepProg`. -/
@[expose] def ZeroTrieChildrenPre (w : ℕ) :
    (HealRt × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((rt, (tc0, tc1)), idx), _s =>
    ∃ c U V w₀ n_max,
      WhpLargeEnv c U V w₀ n_max w (hlBase rt) ∧
      rt = mkHealRt c U V w₀ n_max (hlBase rt) ∧
      tc0 = offTrieChild0 c U V w₀ n_max ∧
      tc1 = offTrieChild1 c U V w₀ n_max ∧
      idx < trieChildEntriesWhp c n_max

private theorem realizes_zeroTrieChildrenStep :
    Realizes .exact zeroTrieChildrenStepProg
      (WordEncoding.encode (α := (HealRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      ZeroTrieChildrenPre
      (fun _ _ => 0) := by
  unfold zeroTrieChildrenStepProg
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨rt, tc0, tc1⟩, idx⟩
    dsimp only [ZeroTrieChildrenPre] at h
    obtain ⟨c, U, V, w₀, n_max, henv, heq_rt, rfl, rfl, hidx_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨_, _, _, _, _, htc_le, _, hgk⟩ := hl_bounds henv
    have hseg := WhpLargeEnv.seg_end_le c U V w n_max
    dsimp only [mkHealRt, hlBase, hlW, hlGBits] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.packed_safe_of_le hgk hidx_lt hseg.2.2.2.2.2.2.2.2.2.2.2.2.1
    | exact henv.packed_safe_of_le hgk hidx_lt hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  )

/-- Loop zeroing `offTrieChild0` and `offTrieChild1`. -/
@[irreducible] def zeroTrieChildrenLoopProg :
    ((HealRt × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, i₀), rem) => iterate zeroTrieChildrenStepProg cfg rem i₀

/-- `Realizes .exact` certificate for `zeroTrieChildrenLoopProg`. -/
theorem realizes_zeroTrieChildrenLoop :
    Realizes .exact zeroTrieChildrenLoopProg
      (WordEncoding.encode (α := ((HealRt × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, i₀), rem) s =>
        iterationSafe zeroTrieChildrenStepProg ZeroTrieChildrenPre w cfg rem i₀ s)
      (fun _ _ => 0) := by
  unfold zeroTrieChildrenLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ))
    realizes_zeroTrieChildrenStep
    memoryCost_zeroTrieChildrenStep_pos

/-- Loop-safety invariant for `zeroTrieChildrenLoopProg`. -/
theorem zeroTrieChildrenLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    let tc0 := offTrieChild0 c U V w n_max
    let tc1 := offTrieChild1 c U V w n_max
    ∀ rem i₀ (s : Memory.State),
      i₀ + rem ≤ trieChildEntriesWhp c n_max →
      iterationSafe zeroTrieChildrenStepProg ZeroTrieChildrenPre w (rt, (tc0, tc1)) rem i₀ s :=
  iterationSafe_of_stateless_step zeroTrieChildrenStepProg ZeroTrieChildrenPre
    (fun _ hi _ => ⟨c, U, V, w, n_max, henv, rfl, rfl, rfl, hi⟩)
    (fun _ _ _ => by
      unfold zeroTrieChildrenStepProg; dsimp only [writePackedGenProg]; simp only [pure_bind]
      rw [clientResult_bind, clientState_writePackedProg, clientResult_bind]; rfl)

/-- Exact memory specification of `zeroTrieChildrenLoopProg`. -/
theorem zeroTrieChildrenLoop_spec {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    let tc0 := offTrieChild0 c U V w n_max
    let tc1 := offTrieChild1 c U V w n_max
    let tce := trieChildEntriesWhp c n_max
    let gBits := globalPtrBits n_max
    ∀ rem i₀ (s : Memory.State),
      i₀ + rem ≤ tce →
      (∀ idx < i₀,
        readPacked (base + tc0) gBits w s.mem idx = 0 ∧
        readPacked (base + tc1) gBits w s.mem idx = 0) →
      let prog := zeroTrieChildrenLoopProg (((rt, (tc0, tc1)), i₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ idx < i₀ + rem,
        readPacked (base + tc0) gBits w s'.mem idx = 0 ∧
        readPacked (base + tc1) gBits w s'.mem idx = 0) ∧
      (∀ a, (a < base + tc0 ∨ base + offTrieMeta0 c U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  intro rt tc0 tc1 tce gBits rem
  have hw := henv.2.1
  obtain ⟨_, _, _, _, _, _, _, hgk⟩ := hl_bounds henv
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have htc0_b : base + tc0 + packedWords tce gBits w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.2.2.2.2.2.2.2.1 _
  have htc1_b : base + tc1 + packedWords tce gBits w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
  have htc0_end : tc0 + packedWords tce gBits w = tc1 := rfl
  have htc1_end : tc1 + packedWords tce gBits w = offTrieMeta0 c U V w n_max := rfl
  have h0_pow : 0 < 2 ^ gBits := Nat.two_pow_pos _
  induction rem with
  | zero =>
    intro i₀ s _ hprev
    unfold zeroTrieChildrenLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, fun _ _ => rfl⟩
  | succ rem ih =>
    intro i₀ s hle hprev
    have hi_lt : i₀ < tce := by omega
    set m1 := writePacked (base + tc0) gBits w s.mem i₀ 0
    set m2 := writePacked (base + tc1) gBits w m1 i₀ 0
    set p1 := zeroTrieChildrenStepProg ((rt, (tc0, tc1)), i₀)
    have hs1 : StepSpec w (base + largeSpaceWhp c U V w n_max) s p1
        { mem := m2, frontier := s.frontier } (i₀ + 1) := by
      dsimp only [p1]; unfold zeroTrieChildrenStepProg
      dsimp only [rt, mkHealRt, hlBase, hlW, hlGBits]
      simp only [pure_bind]
      refine (StepSpec.writePackedGen hw hgk hi_lt htc0_b).bind ?_
      exact (StepSpec.writePackedGen hw hgk hi_lt htc1_b).bind (StepSpec.pure _ _)
    set s1 : Memory.State := { mem := m2, frontier := s.frontier }
    have hprev1 : ∀ idx < i₀ + 1,
        readPacked (base + tc0) gBits w s1.mem idx = 0 ∧
        readPacked (base + tc1) gBits w s1.mem idx = 0 := by
      intro idx hidx
      dsimp only [s1, m2, m1]
      have hidx_tce : idx < tce := by omega
      have hdisj01 : base + tc0 + packedWords tce gBits w ≤ base + tc1 ∨
          base + tc1 + packedWords tce gBits w ≤ base + tc0 := Or.inl (by omega)
      have hdisj10 : base + tc1 + packedWords tce gBits w ≤ base + tc0 ∨
          base + tc0 + packedWords tce gBits w ≤ base + tc1 := Or.inr (by omega)
      rw [readPacked_writePacked_disjoint hw hidx_tce hi_lt hdisj01]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hidx with hlt | rfl
      · refine ⟨(readPacked_writePacked_of_ne hw _ (by omega) _).trans (hprev idx hlt).1, ?_⟩
        rw [readPacked_writePacked_of_ne hw _ (by omega),
          readPacked_writePacked_disjoint hw hidx_tce hi_lt hdisj10]
        exact (hprev idx hlt).2
      · exact ⟨readPacked_writePacked_self _ _ _ _ _ h0_pow,
          readPacked_writePacked_self _ _ _ _ _ h0_pow⟩
    obtain ⟨hf_r, hvp_r, hp_r, hout_r⟩ := ih (i₀ + 1) s1 (by omega) hprev1
    have hadd : i₀ + 1 + rem = i₀ + (rem + 1) := by omega
    rw [hadd] at hp_r
    unfold zeroTrieChildrenLoopProg at hf_r hvp_r hp_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hf_r
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro idx hidx; rw [clientState_bind, hs1.1, hs1.2.1]; exact hp_r idx hidx
    · intro a ha
      rw [clientState_bind, hs1.1, hs1.2.1, hout_r a ha]
      dsimp only [s1, m2, m1]
      dsimp only [tc0, tc1, tce, gBits] at hi_lt htc0_end htc1_end ha ⊢
      rw [writePacked_outside hw _ hi_lt _ (by omega),
        writePacked_outside hw _ hi_lt _ (by omega)]

/-- Clear root `nodeActive` flags in `offTrieMeta0`/`offTrieMeta1` and write the 16 fast-mode
header words at `base .. base + 15`. -/
@[irreducible] def writeHealHdrsAndTrieMetaProg :
    (HealRt × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((rt, (tm0_in, tm1_in)), freeTop_in) => do
    let base ← pure (hlBase rt)
    let tm0 ← pure tm0_in
    let tm1 ← pure tm1_in
    let freeTop ← pure freeTop_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let two_v ← pure 2
    let five_v ← pure 5
    writePackedGenProg ((((base, tm0), (hlGBits rt, hlW rt)), two_v), zero_v)
    writePackedGenProg ((((base, tm1), (hlGBits rt, hlW rt)), two_v), zero_v)
    let a1 ← pure (base + 1)
    let a2 ← pure (base + 2)
    let a3 ← pure (base + 3)
    let a4 ← pure (base + 4)
    let a5 ← pure (base + 5)
    let a6 ← pure (base + 6)
    let a7 ← pure (base + 7)
    let a8 ← pure (base + 8)
    let a9 ← pure (base + 9)
    let a10 ← pure (base + 10)
    let a11 ← pure (base + 11)
    let a12 ← pure (base + 12)
    let a13 ← pure (base + 13)
    let a14 ← pure (base + 14)
    let a15 ← pure (base + 15)
    Memory.write base one_v
    Memory.write a1 freeTop
    Memory.write a2 zero_v
    Memory.write a3 zero_v
    Memory.write a4 five_v
    Memory.write a5 zero_v
    Memory.write a6 zero_v
    Memory.write a7 zero_v
    Memory.write a8 zero_v
    Memory.write a9 zero_v
    Memory.write a10 zero_v
    Memory.write a11 zero_v
    Memory.write a12 one_v
    Memory.write a13 zero_v
    Memory.write a14 one_v
    Memory.write a15 zero_v

/-- Precondition for `writeHealHdrsAndTrieMetaProg`. -/
@[expose] def WriteHealHdrsPre (w : ℕ) :
    (HealRt × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((rt, (tm0, tm1)), _freeTop), _s =>
    ∃ c U V w₀ n_max,
      WhpLargeEnv c U V w₀ n_max w (hlBase rt) ∧
      rt = mkHealRt c U V w₀ n_max (hlBase rt) ∧
      tm0 = offTrieMeta0 c U V w₀ n_max ∧
      tm1 = offTrieMeta1 c U V w₀ n_max

/-- `Realizes .exact` certificate for `writeHealHdrsAndTrieMetaProg`. -/
theorem realizes_writeHealHdrsAndTrieMeta :
    Realizes .exact writeHealHdrsAndTrieMetaProg
      (WordEncoding.encode (α := (HealRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      WriteHealHdrsPre
      (fun _ _ => 0) := by
  unfold writeHealHdrsAndTrieMetaProg
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨rt, tm0, tm1⟩, freeTop⟩
    dsimp only [WriteHealHdrsPre] at h
    obtain ⟨c, U, V, w₀, n_max, henv, heq_rt, rfl, rfl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨_, _, _, _, _, _, hw3, hgk⟩ := hl_bounds henv
    have hmt_pos : 1 ≤ maxTrieNodesWhp c n_max := by unfold maxTrieNodesWhp; omega
    have h2_lt : 2 < 6 * maxTrieNodesWhp c n_max := by omega
    have hseg := WhpLargeEnv.seg_end_le c U V w n_max
    have h5_fit : Fits w 5 :=
      (by decide : 5 < 2 ^ 3).trans_le (Nat.pow_le_pow_right two_pos hw3)
    dsimp only [mkHealRt, hlBase, hlW, hlGBits] at *
    first
    | exact h5_fit
    | exact h5_fit.of_le (by decide)
    | exact henv.fits_hdr_addr (off := _) (by decide)
    | exact henv.packed_safe_of_le hgk h2_lt hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    | exact henv.packed_safe_of_le hgk h2_lt hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  )

/-- Exact memory specification of `writeHealHdrsAndTrieMetaProg`. -/
theorem writeHealHdrsAndTrieMetaProg_spec {c U V w n_max base freeTop : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hft_fit : Fits w freeTop) (s : Memory.State) :
    let rt := mkHealRt c U V w n_max base
    let tm0 := offTrieMeta0 c U V w n_max
    let tm1 := offTrieMeta1 c U V w n_max
    let gBits := globalPtrBits n_max
    let prog := writeHealHdrsAndTrieMetaProg ((rt, (tm0, tm1)), freeTop)
    let s' := (Memory.spec 0).clientState s prog
    s'.frontier = s.frontier ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    s'.mem (base + hdrMode) = 1 ∧
    s'.mem (base + hdrPoolFreeTop) = freeTop ∧
    s'.mem (base + hdrCurEp) = 0 ∧
    s'.mem (base + hdrEpochClock) = 0 ∧
    s'.mem (base + hdrRebStage) = 5 ∧
    s'.mem (base + hdrStageCursor) = 0 ∧
    s'.mem (base + hdrDirtyCount) = 0 ∧
    s'.mem (base + hdrDirtyIdx) = 0 ∧
    s'.mem (base + hdrRebCandSalt) = 0 ∧
    s'.mem (base + hdrRebScanCursor) = 0 ∧
    s'.mem (base + hdrRebInsCount) = 0 ∧
    s'.mem (base + hdrRebCollision) = 0 ∧
    s'.mem (base + hdrBuf0NodeAlloc) = 1 ∧
    s'.mem (base + hdrBuf0ItemAlloc) = 0 ∧
    s'.mem (base + hdrBuf1NodeAlloc) = 1 ∧
    s'.mem (base + hdrBuf1ItemAlloc) = 0 ∧
    readPacked (base + tm0) gBits w s'.mem 2 = 0 ∧
    readPacked (base + tm1) gBits w s'.mem 2 = 0 ∧
    (∀ a, (a < base ∨ (base + 16 ≤ a ∧ a < base + tm0) ∨
        base + offTrieItems0 c U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  intro rt tm0 tm1 gBits
  have hw := henv.2.1
  obtain ⟨_, _, _, _, _, _, hw3, hgk⟩ := hl_bounds henv
  have hmt_pos : 1 ≤ maxTrieNodesWhp c n_max := by unfold maxTrieNodesWhp; omega
  have h2_lt : 2 < 6 * maxTrieNodesWhp c n_max := by omega
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have htm0_b : base + tm0 + packedWords (6 * maxTrieNodesWhp c n_max) gBits w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
  have htm1_b : base + tm1 + packedWords (6 * maxTrieNodesWhp c n_max) gBits w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _
  have htm0_end : tm0 + packedWords (6 * maxTrieNodesWhp c n_max) gBits w = tm1 := rfl
  have htm1_end : tm1 + packedWords (6 * maxTrieNodesWhp c n_max) gBits w =
      offTrieItems0 c U V w n_max := rfl
  have h32_tm0 : 32 ≤ tm0 := by
    have : offHashBkt = 32 := rfl
    unfold tm0 offTrieMeta0 offTrieChild1 offTrieChild0 offBtVals offBtKeys offBtMeta
      offPoolOwner offPoolFreeStack offBackAux offBackPtr offFbStart offBktMeta offLocState
      offPermAct offValWhp offQuotWhp offHashFp
    omega
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have h5_fit : Fits w 5 :=
    (by decide : 5 < 2 ^ 3).trans_le (Nat.pow_le_pow_right two_pos hw3)
  have h1_fit : Fits w 1 := h5_fit.of_le (by decide)
  have h0_fit : Fits w 0 := h5_fit.of_le (by decide)
  set m_tm0 := writePacked (base + tm0) gBits w s.mem 2 0
  set m_tm1 := writePacked (base + tm1) gBits w m_tm0 2 0
  let upd : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ) := Function.update
  set m_fin :=
    upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd
      m_tm1 base 1) (base + 1) freeTop) (base + 2) 0) (base + 3) 0) (base + 4) 5)
      (base + 5) 0) (base + 6) 0) (base + 7) 0) (base + 8) 0) (base + 9) 0)
      (base + 10) 0) (base + 11) 0) (base + 12) 1) (base + 13) 0) (base + 14) 1) (base + 15) 0
  have hstep : StepSpec w (base + largeSpaceWhp c U V w n_max) s
      (writeHealHdrsAndTrieMetaProg ((rt, (tm0, tm1)), freeTop))
      { mem := m_fin, frontier := s.frontier } () := by
    have htm0_step : StepSpec w (base + largeSpaceWhp c U V w n_max) s
        (writePackedGenProg ((((base, tm0), (gBits, w)), 2), 0))
        { mem := m_tm0, frontier := s.frontier } () :=
      StepSpec.writePackedGen hw hgk h2_lt htm0_b
    have htm1_step : StepSpec w (base + largeSpaceWhp c U V w n_max)
        { mem := m_tm0, frontier := s.frontier }
        (writePackedGenProg ((((base, tm1), (gBits, w)), 2), 0))
        { mem := m_tm1, frontier := s.frontier } () :=
      StepSpec.writePackedGen hw hgk h2_lt htm1_b
    have hw_mk : ∀ {m : ℕ → ℕ} {a v : ℕ}, a < base + largeSpaceWhp c U V w n_max → Fits w v →
        StepSpec w (base + largeSpaceWhp c U V w n_max)
          { mem := m, frontier := s.frontier } (Memory.write a v)
          { mem := upd m a v, frontier := s.frontier } () :=
      fun ha hfit => ⟨rfl, rfl, validProg_write ha hfit⟩
    unfold writeHealHdrsAndTrieMetaProg
    dsimp only [rt, mkHealRt, hlBase, hlW, hlGBits]
    simp only [pure_bind]
    refine StepSpec.bind htm0_step ?_
    refine StepSpec.bind htm1_step ?_
    repeat refine StepSpec.bind (hw_mk (by omega)
      (by first | exact hft_fit | exact h5_fit | exact h1_fit | exact h0_fit)) ?_
    exact StepSpec.pure _ _
  have hm_ge16 : ∀ a, (a < base ∨ base + 16 ≤ a) → m_fin a = m_tm1 a := by
    intro a ha; dsimp only [m_fin, upd]
    repeat rw [Function.update_of_ne (by omega)]
  have h0_pow : 0 < 2 ^ gBits := Nat.two_pow_pos _
  have hhdrs :
      m_fin (base + hdrMode) = 1 ∧
      m_fin (base + hdrPoolFreeTop) = freeTop ∧
      m_fin (base + hdrCurEp) = 0 ∧
      m_fin (base + hdrEpochClock) = 0 ∧
      m_fin (base + hdrRebStage) = 5 ∧
      m_fin (base + hdrStageCursor) = 0 ∧
      m_fin (base + hdrDirtyCount) = 0 ∧
      m_fin (base + hdrDirtyIdx) = 0 ∧
      m_fin (base + hdrRebCandSalt) = 0 ∧
      m_fin (base + hdrRebScanCursor) = 0 ∧
      m_fin (base + hdrRebInsCount) = 0 ∧
      m_fin (base + hdrRebCollision) = 0 ∧
      m_fin (base + hdrBuf0NodeAlloc) = 1 ∧
      m_fin (base + hdrBuf0ItemAlloc) = 0 ∧
      m_fin (base + hdrBuf1NodeAlloc) = 1 ∧
      m_fin (base + hdrBuf1ItemAlloc) = 0 := by
    dsimp only [m_fin, upd, hdrMode, hdrPoolFreeTop, hdrCurEp, hdrEpochClock, hdrRebStage,
      hdrStageCursor, hdrDirtyCount, hdrDirtyIdx, hdrRebCandSalt, hdrRebScanCursor,
      hdrRebInsCount, hdrRebCollision, hdrBuf0NodeAlloc, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc,
      hdrBuf1ItemAlloc]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _)
  refine ⟨by rw [hstep.1], hstep.2.2, ?_⟩
  rw [hstep.1]; dsimp only
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hhdrs
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, ?_, ?_,
    fun a ha => ?_⟩
  · rw [readPacked_congr hw (fun a ⟨ha1, _⟩ => hm_ge16 a (Or.inr (by omega))) h2_lt]
    dsimp only [m_tm1, m_tm0]
    have hdisj : base + tm0 + packedWords (6 * maxTrieNodesWhp c n_max) gBits w ≤ base + tm1 ∨
        base + tm1 + packedWords (6 * maxTrieNodesWhp c n_max) gBits w ≤ base + tm0 :=
      Or.inl (by omega)
    rw [readPacked_writePacked_disjoint hw h2_lt h2_lt hdisj]
    exact readPacked_writePacked_self _ _ _ _ _ h0_pow
  · rw [readPacked_congr hw (fun a ⟨ha1, _⟩ => hm_ge16 a (Or.inr (by omega))) h2_lt]
    exact readPacked_writePacked_self _ _ _ _ _ h0_pow
  · have h16 : a < base ∨ base + 16 ≤ a := by
      rcases ha with h1 | ⟨h1, _⟩ | h1
      · exact Or.inl h1
      · exact Or.inr h1
      · exact Or.inr (by omega)
    rw [hm_ge16 a h16]
    dsimp only [m_tm1, m_tm0]
    dsimp only [tm0, tm1, gBits] at htm0_end htm1_end ha ⊢
    rw [writePacked_outside hw _ h2_lt _ (by omega),
      writePacked_outside hw _ h2_lt _ (by omega)]

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
