/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSeedCheckProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg
import CslibFrontier.Tactic.Realize

/-!
# Self-Healing `csrToFast` / `trySelfHeal` and Top-Level `whpStepPureGenProg`

This module completes the `Memory.Prog` realization of the SOSA 2024 fixed-capacity high-probability
succinct dynamic dictionary (`[BenderFarachColtonKuszmaulKuszmaul2024]`,
`DOI: 10.1137/1.9781611977936.33`) strictly inside genuine `whpSpace c U V w n_max` words:

1. **`csrToFastGenProg`**: converts `CsrMemRep` in place into `FastMemRep` for
   `csrToFast c U n_max θ csr salts` when `GoodSeedOnState` holds and candidate salts occupy the odd
   `offBktMeta` entries `16 * b + 1`, using even `offBktMeta` entries `2 * x` (`x ≤ M`) for
   `buildBackPrefix` before writing final bucket metadata.
2. **`trySelfHealGenProg`**: chains `checkGoodSeedOnStateGenProg` with `csrToFastGenProg`,
   refining `trySelfHeal c U n_max θ csr` into `WhpMemRep`.
3. **`whpStepPureGenProg`**: top-level parameter-free `Memory.Prog` step dispatcher across `.small`,
   `.fast` (both `O_c(1)` fast-branch hits and fallback transitions), and `.fallback`, refining
   `whpStepPure c U n_max θ st op` with `memoryCost ≤ whpFastBranchCost c` whenever
   `IsFastStepHit c U n_max ops_prev op θ` holds.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.whpFastBranchCost`, `whpStepPureGenProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_whpStepPureGen`,
  `whpStepPureGenProg_spec`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Finset
open scoped BigOperators
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ## Section 1: Pure Capacity Bounds and `HealRt` Runtime Bundle -/

private theorem backPrefix_spec (M cf : ℕ) (fbStart : ℕ → ℕ) :
    let bp := buildBackPrefix M cf fbStart
    bp 0 = 0 ∧
    (∀ b < M, bp (b + 1) = bp b + ((fbStart (b + 1) - fbStart b) - cf)) ∧
    (∀ k ≤ M, bp k = ∑ b ∈ range k, ((fbStart (b + 1) - fbStart b) - cf)) ∧
    (∀ x y, x ≤ y → y ≤ M → bp x ≤ bp y) := by
  have hadj : ∀ b < M,
      buildBackPrefix M cf fbStart (b + 1) =
        buildBackPrefix M cf fbStart b + ((fbStart (b + 1) - fbStart b) - cf) := fun b hb => by
    dsimp only [buildBackPrefix]; simp only [hb, ↓reduceIte]
  refine ⟨rfl, hadj, fun k hk => ?_, fbStart_mono_of_adj fun b hb => by
    rw [hadj b hb]; exact Nat.le_add_right _ _⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk_lt : k < M := Nat.lt_of_succ_le hk
    rw [Finset.sum_range_succ, ← ih hk_lt.le, hadj k hk_lt]

private theorem csrToFast_bounds_of_good {c U V n_max : ℕ}
    (hth : whpThreshold c ≤ n_max)
    {θ : SeedWhp c U n_max} {csr : CsrState} {dict : Dictionary.State U}
    (hcsr : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict)
    (hgood : GoodSeedOnState c U n_max θ dict) :
    let M := numBucketsWhp n_max
    let cf := capFrontWhp n_max
    let cb := capBackWhp n_max
    let bp := buildBackPrefix M cf csr.fbStart
    (∀ b < M,
      (csr.fbStart (b + 1) - csr.fbStart b) - cf < cb ∧
      csr.fbStart (b + 1) - csr.fbStart b ≤ totalLocalCoordsWhp n_max) ∧
    bp M ≤ poolSizeWhp n_max := by
  obtain ⟨hcard_b, hcard_dom⟩ := hcsr.bucket_and_dom_card
  obtain ⟨_, _, hfbM_le, _, _, _⟩ := hcsr
  obtain ⟨_, _, hbp_sum, _⟩ := backPrefix_spec (numBucketsWhp n_max) (capFrontWhp n_max)
    csr.fbStart
  let X_fin : Fin (numBucketsWhp n_max) → ℕ :=
    fun b => csr.fbStart (b.val + 1) - csr.fbStart b.val
  have hsum_X : ∑ b : Fin (numBucketsWhp n_max), X_fin b = csr.fbStart (numBucketsWhp n_max) := by
    have hdom_sum : #(Dictionary.dom dict) = ∑ b : Fin (numBucketsWhp n_max), X_fin b := by
      rw [Finset.card_eq_sum_ones]
      have h1_sum : ∀ u ∈ Dictionary.dom dict,
          (1 : ℕ) = ∑ b : Fin (numBucketsWhp n_max),
            if feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val then 1
            else 0 := by
        intro u _
        let b₀ : Fin (numBucketsWhp n_max) :=
          ⟨feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val,
            feistelBucket_lt (bWhp n_max) (bktHash c U n_max θ.1) u.val⟩
        rw [Fintype.sum_eq_single b₀]
        · simp [b₀]
        · intro b' hb'
          have hne : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val ≠ b'.val :=
            fun h => hb' (Fin.ext h.symm)
          simp only [hne, ↓reduceIte]
      calc ∑ u ∈ Dictionary.dom dict, 1
          = ∑ u ∈ Dictionary.dom dict, ∑ b : Fin (numBucketsWhp n_max),
              if feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val then 1
              else 0 := Finset.sum_congr rfl h1_sum
        _ = ∑ b : Fin (numBucketsWhp n_max), ∑ u ∈ Dictionary.dom dict,
              if feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val then 1
              else 0 := Finset.sum_comm
        _ = ∑ b : Fin (numBucketsWhp n_max), X_fin b := by
            refine Fintype.sum_congr _ _ fun b => ?_
            rw [← Finset.card_filter, hcard_b b]
    exact hdom_sum.symm.trans hcard_dom
  obtain ⟨hback_lt_cb, _, hpool_le⟩ := sum_sub_capFront_le_poolSize hth X_fin
    (hsum_X.trans_le hfbM_le)
    (fun b => by
      have hb := (hgood.2.1 b).1
      rwa [hcard_b b, hcard_dom, ← hsum_X] at hb)
    (fun b => by
      have hb := (hgood.2.1 b).2
      rwa [hcard_b b, hcard_dom, ← hsum_X] at hb)
  have hbpM_eq : buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) csr.fbStart
      (numBucketsWhp n_max) = ∑ b : Fin (numBucketsWhp n_max), (X_fin b - capFrontWhp n_max) := by
    rw [hbp_sum (numBucketsWhp n_max) le_rfl, ← Fin.sum_univ_eq_sum_range]
  refine ⟨fun b hb => ?_, hbpM_eq ▸ hpool_le⟩
  have hcb := hback_lt_cb ⟨b, hb⟩
  dsimp only [X_fin] at hcb
  exact ⟨hcb, by unfold totalLocalCoordsWhp; omega⟩

/-- Compact 16-word runtime bundle for `csrToFastGenProg` array phases:
`((((base, w), (nMax, M)), ((cf, cb), (totalLoc, poolSize))),`
` ((gBits, tcEntries), ((offBm, offFb), ((offBp, offPs), (offPo, offLs)))))`. -/
private abbrev HealRt : Type :=
  (((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) ×
    ((ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))

private def hlBase (rt : HealRt) : ℕ := rt.1.1.1.1
private def hlW (rt : HealRt) : ℕ := rt.1.1.1.2
private def hlNMax (rt : HealRt) : ℕ := rt.1.1.2.1
private def hlM (rt : HealRt) : ℕ := rt.1.1.2.2
private def hlCF (rt : HealRt) : ℕ := rt.1.2.1.1
private def hlCB (rt : HealRt) : ℕ := rt.1.2.1.2
private def hlTotalLoc (rt : HealRt) : ℕ := rt.1.2.2.1
private def hlPoolSize (rt : HealRt) : ℕ := rt.1.2.2.2
private def hlGBits (rt : HealRt) : ℕ := rt.2.1.1
private def hlTcEntries (rt : HealRt) : ℕ := rt.2.1.2
private def hlOffBm (rt : HealRt) : ℕ := rt.2.2.1.1
private def hlOffFb (rt : HealRt) : ℕ := rt.2.2.1.2
private def hlOffBp (rt : HealRt) : ℕ := rt.2.2.2.1.1
private def hlOffPs (rt : HealRt) : ℕ := rt.2.2.2.1.2
private def hlOffPo (rt : HealRt) : ℕ := rt.2.2.2.2.1
private def hlOffLs (rt : HealRt) : ℕ := rt.2.2.2.2.2

/-- Construct `HealRt` for `(c, U, V, w, n_max, base)`. -/
private def mkHealRt (c U V w n_max base : ℕ) : HealRt :=
  ((((base, w), (n_max, numBucketsWhp n_max)),
    ((capFrontWhp n_max, capBackWhp n_max),
     (totalLocalCoordsWhp n_max, poolSizeWhp n_max))),
   ((globalPtrBits n_max, trieChildEntriesWhp c n_max),
    ((offBktMeta c U V w n_max, offFbStart c U V w n_max),
     ((offBackPtr c U V w n_max, offPoolFreeStack c U V w n_max),
      (offPoolOwner c U V w n_max, offLocState c U V w n_max)))))

/-- Parameter-free `HealRt` envelope. -/
private def HealRtEnvGen (w : ℕ) (rt : HealRt) : Prop :=
  ∃ c U V w₀ n_max, WhpLargeEnv c U V w₀ n_max w (hlBase rt) ∧
    rt = mkHealRt c U V w₀ n_max (hlBase rt)

@[irreducible] private def mkHealRtGenProg : WhpCoreParams × ℕ → Memory.Prog HealRt
  | (cp, base_in) => do
    let base ← pure base_in
    let a1 ← pure ((base, wpW cp), (wpNMax cp, wpM cp))
    let a2 ← pure ((wpCapFront cp, wpCapBack cp), (wpTotalLoc cp, wpPoolSize cp))
    let b1 ← pure (wpGlobalPtrBits cp, wpTrieChildEntries cp)
    let b2 ← pure (wpOffBktMeta cp, wpOffFbStart cp)
    let b3 ← pure (wpOffBackPtr cp, wpOffPoolFreeStack cp)
    let b4 ← pure (wpOffPoolOwner cp, wpOffLocState cp)
    pure ((a1, a2), (b1, (b2, (b3, b4))))

private theorem realizes_mkHealRtGen :
    Realizes .exact mkHealRtGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := HealRt))
      (fun w d _ => WhpLargeEnvGen w d.1 d.2)
      (fun _ _ => 0) := by
  unfold mkHealRtGenProg
  realize

private theorem mkHealRtGenProg_spec {c U V w n_max base : ℕ}
    (hth : whpThreshold c ≤ n_max) (s : Memory.State) :
    let prog := mkHealRtGenProg (mkWhpCoreParams c U V w n_max, base)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = mkHealRt c U V w n_max base ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  dsimp only
  unfold mkHealRtGenProg
  simp only [wp_large_w hth, wp_large_nMax hth, wp_large_M hth,
    wp_large_capFront hth, wp_large_capBack hth, wp_large_totalLoc hth, wp_large_poolSize hth,
    wp_large_globalPtrBits hth, wp_large_trieChildEntries hth, wp_large_offBktMeta hth,
    wp_large_offFbStart hth, wp_large_offBackPtr hth, wp_large_offPoolFreeStack hth,
    wp_large_offPoolOwner hth, wp_large_offLocState hth, pure_bind]
  exact ⟨rfl, rfl, validProg_pure _⟩

private theorem hl_bounds {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let M := numBucketsWhp n_max
    M < n_max ∧
    16 * M ≤ n_max ∧
    M * capBackWhp n_max ≤ n_max ∧
    poolSizeWhp n_max ≤ n_max ∧
    2 * totalLocalCoordsWhp n_max < n_max ∧
    trieChildEntriesWhp c n_max ≤ n_max ∧
    3 ≤ w ∧
    globalPtrBits n_max ≤ w := by
  have hth := henv.2.2.2.1
  have hL2 := two_le_slabScale n_max
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have hM_ge := (large_bounds_lt_n_max hth).1
  have h16M := sixteen_mul_numBuckets_le_n_max hth
  have hcb_le : capBackWhp n_max ≤ (slabScale n_max) ^ 12 := by
    unfold capBackWhp
    calc 2 * (slabScale n_max) ^ 11 ≤ slabScale n_max * (slabScale n_max) ^ 11 :=
          Nat.mul_le_mul_right _ hL2
      _ = (slabScale n_max) ^ 12 := by ring
  have hMcb : numBucketsWhp n_max * capBackWhp n_max ≤ n_max :=
    (Nat.mul_le_mul_left _ hcb_le).trans hML12
  have htot3 := @totalLocalCoordsWhp_le_three_mul n_max
  have hL_pos : 1 ≤ (slabScale n_max) ^ 12 := Nat.one_le_pow 12 _ (slabScale_pos n_max)
  have h1024 : 1024 * (slabScale n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ hM_ge).trans hML12
  have h2tot : 2 * totalLocalCoordsWhp n_max < n_max := by
    calc 2 * totalLocalCoordsWhp n_max ≤ 6 * (slabScale n_max) ^ 12 := by omega
      _ < 1024 * (slabScale n_max) ^ 12 := by omega
      _ ≤ n_max := h1024
  have htc_le : trieChildEntriesWhp c n_max ≤ n_max := by
    have hsub := (sublinear_table_bits_le hth).2.2.2.1
    exact (Nat.le_mul_of_pos_right _ (globalPtrBits_pos_of_large hth)).trans hsub
  have hlog := henv.log_lt_w
  have hge := log_ge_mul_ell hth
  have hell := one_le_logLogFactor n_max
  exact ⟨by omega, h16M, hMcb, Nat.sub_le _ _, h2tot, htc_le, by omega,
    globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1⟩

/-! ### Phase A: `bpPrefixLoopProg` (`buildBackPrefix` into even slots `offBktMeta[2 * x]`) -/

@[irreducible] private def bpPrefixStepProg : HealRt × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (rt, (b_in, acc_in)) => do
    let b ← pure b_in
    let acc ← pure acc_in
    let one_v ← pure 1
    let b1 ← pure (b + one_v)
    let lo ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b)
    let hi ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b1)
    let idxOut ← pure (2 * b1)
    if lo ≤ hi then
      let xb ← pure (hi - lo)
      if hlCF rt ≤ xb then
        let exc ← pure (xb - hlCF rt)
        if acc ≤ hlNMax rt then
          let remN ← pure (hlNMax rt - acc)
          if exc ≤ remN then
            let acc1 ← pure (acc + exc)
            writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxOut), acc1)
            pure (b1, acc1)
          else
            writePackedGenProg
              ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxOut), hlNMax rt)
            pure (b1, hlNMax rt)
        else
          writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxOut), hlNMax rt)
          pure (b1, hlNMax rt)
      else
        writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxOut), acc)
        pure (b1, acc)
    else
      writePackedGenProg ((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxOut), acc)
      pure (b1, acc)

private theorem memoryCost_bpPrefixStep_pos (d : HealRt × (ℕ × ℕ)) (s : Memory.State) :
    0 < memoryCost (bpPrefixStepProg d) s := by
  rcases d with ⟨rt, b, acc⟩
  unfold bpPrefixStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

private def BpPrefixStepPre (w : ℕ) (d : HealRt × (ℕ × ℕ)) (_s : Memory.State) : Prop :=
  HealRtEnvGen w d.1 ∧ d.2.1 < hlM d.1

private theorem realizes_bpPrefixStep :
    Realizes .exact bpPrefixStepProg
      (WordEncoding.encode (α := HealRt × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      BpPrefixStepPre
      (fun _ _ => 0) := by
  unfold bpPrefixStepProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨rt, b, acc⟩
    dsimp only [BpPrefixStepPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hb_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨hM_lt, h16M, _, _, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := WhpLargeEnv.seg_end_le c U V w n_max
    dsimp only [mkHealRt, hlBase, hlW, hlNMax, hlM, hlCF, hlGBits, hlOffBm, hlOffFb] at *
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact to_true_exists
        (henv.packed_safe_of_le hgk (idx := b) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists
        (henv.packed_safe_of_le hgk (idx := b + 1) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists (henv.bktMeta_safe (idx := 2 * (b + 1)) (by omega))
  )

@[irreducible] private def bpPrefixLoopProg : (HealRt × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((rt, acc), rem) => iterate bpPrefixStepProg rt rem acc

private theorem realizes_bpPrefixLoop :
    Realizes .exact bpPrefixLoopProg
      (WordEncoding.encode (α := (HealRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((rt, acc), rem) s =>
        iterationSafe bpPrefixStepProg BpPrefixStepPre w rt rem acc s)
      (fun _ _ => 0) := by
  unfold bpPrefixLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizes_bpPrefixStep
    memoryCost_bpPrefixStep_pos

private theorem bpPrefixLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem b₀ acc₀ (s : Memory.State),
      b₀ + rem ≤ numBucketsWhp n_max →
      iterationSafe bpPrefixStepProg BpPrefixStepPre w rt rem (b₀, acc₀) s := by
  intro rt rem
  induction rem with
  | zero => intro _ _ _ _; exact trivial
  | succ rem ih =>
    intro b₀ acc₀ s hle
    refine ⟨⟨⟨c, U, V, w, n_max, henv, rfl⟩, by dsimp [rt, mkHealRt, hlM]; omega⟩, ?_⟩
    rw [clientState_width, clientResult_width]
    set p1 := bpPrefixStepProg (rt, (b₀, acc₀))
    have hfst : ((Memory.spec 0).clientResult s p1).1 = b₀ + 1 := by
      dsimp only [p1]; unfold bpPrefixStepProg
      dsimp only [readPackedGenProg, writePackedGenProg]
      simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedProg,
        clientResult_bind, clientState_readPackedProg]
      split_ifs <;> (rw [clientResult_bind]; rfl)
    set res := (Memory.spec 0).clientResult s p1
    have heta : res = (b₀ + 1, res.2) := Prod.ext hfst rfl
    rw [heta]
    exact ih (b₀ + 1) res.2 _ (by omega)

private theorem bpPrefixLoop_spec {c U V w n_max base : ℕ} {fbStart : ℕ → ℕ}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hfb_adj : ∀ b < numBucketsWhp n_max, fbStart b ≤ fbStart (b + 1))
    (hbp_le : buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) fbStart
      (numBucketsWhp n_max) ≤ n_max)
    (hfb_mem : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s₀.mem x = fbStart x) :
    let rt := mkHealRt c U V w n_max base
    let M := numBucketsWhp n_max
    let bp := buildBackPrefix M (capFrontWhp n_max) fbStart
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ M →
      (∀ x ≤ b₀,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem (2 * x) =
          bp x) →
      (∀ idx < 16 * M, idx % 2 = 1 →
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx =
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s₀.mem idx) →
      (∀ a, (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
        s.mem a = s₀.mem a) →
      let prog := bpPrefixLoopProg ((rt, (b₀, bp b₀)), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ x ≤ b₀ + rem,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem (2 * x) =
          bp x) ∧
      (∀ idx < 16 * M, idx % 2 = 1 →
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s₀.mem idx) ∧
      (∀ a, (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) := by
  intro rt M bp rem
  have hw := henv.2.1
  obtain ⟨_, _, _, _, _, _, _, hgk⟩ := hl_bounds henv
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.1 _
  have hbm_end : offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w = offFbStart c U V w n_max := rfl
  obtain ⟨_, hbp_adj, _, hbp_mono⟩ := backPrefix_spec M (capFrontWhp n_max) fbStart
  induction rem with
  | zero =>
    intro b₀ s _ hev hodd hout
    unfold bpPrefixLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hev, hodd, hout⟩
  | succ rem ih =>
    intro b₀ s hle hev hodd hout
    have hb_lt : b₀ < M := by omega
    have hfb_s : ∀ x ≤ M,
        readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem x = fbStart x :=
      fun x hx => (readPacked_congr hw (fun a ⟨ha1, _⟩ => hout a (Or.inr ha1))
        (Nat.lt_succ_of_le hx)).trans (hfb_mem x hx)
    have hlo_hi := hfb_adj b₀ hb_lt
    have hbp1_eq := hbp_adj b₀ hb_lt
    have hbp1_le : bp (b₀ + 1) ≤ n_max := (hbp_mono (b₀ + 1) M hb_lt le_rfl).trans hbp_le
    have hbp0_le : bp b₀ ≤ n_max := (hbp_mono b₀ (b₀ + 1) (Nat.le_succ b₀) hb_lt).trans hbp1_le
    have hidx_ev : 2 * (b₀ + 1) < 16 * M := by omega
    have hbp1_pow : bp (b₀ + 1) < 2 ^ globalPtrBits n_max :=
      lt_two_pow_globalPtrBits_of_le_n_max hbp1_le
    set p1 := bpPrefixStepProg (rt, (b₀, bp b₀))
    set m1 := writePacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
      (2 * (b₀ + 1)) (bp (b₀ + 1))
    have hs1 : (Memory.spec 0).clientState s p1 = { mem := m1, frontier := s.frontier } ∧
        (Memory.spec 0).clientResult s p1 = (b₀ + 1, bp (b₀ + 1)) ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold bpPrefixStepProg; dsimp only [rt, mkHealRt, hlBase, hlW, hlNMax,
        hlCF, hlGBits, hlOffBm, hlOffFb, readPackedGenProg, writePackedGenProg]
      simp only [pure_bind]
      change bp (b₀ + 1) = bp b₀ + ((fbStart (b₀ + 1) - fbStart b₀) - capFrontWhp n_max) at hbp1_eq
      by_cases hcf : capFrontWhp n_max ≤ fbStart (b₀ + 1) - fbStart b₀
      · have hexc_le : (fbStart (b₀ + 1) - fbStart b₀) - capFrontWhp n_max ≤ n_max - bp b₀ := by
          omega
        refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
            clientState_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt]
          simp only [hlo_hi, hcf, hbp0_le, hexc_le, ↓reduceIte]
          rw [clientState_bind, clientState_writePackedProg, ← hbp1_eq]; rfl
        · rw [clientResult_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
            clientResult_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt]
          simp only [hlo_hi, hcf, hbp0_le, hexc_le, ↓reduceIte]
          rw [clientResult_bind, ← hbp1_eq]; rfl
        · refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
          rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s b₀ hb_lt.le]
          refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
          rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt]
          simp only [hlo_hi, hcf, hbp0_le, hexc_le, ↓reduceIte]
          exact validProg_bind (validProg_writePacked hw hgk hidx_ev hbm_b)
            (validProg_pure _)
      · have hbp1_same : bp (b₀ + 1) = bp b₀ := by omega
        refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
            clientState_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt]
          simp only [hlo_hi, hcf, ↓reduceIte]
          rw [clientState_bind, clientState_writePackedProg]
          dsimp only [m1]; rw [hbp1_same]; rfl
        · rw [clientResult_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
            clientResult_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt]
          simp only [hlo_hi, hcf, ↓reduceIte]
          rw [clientResult_bind, hbp1_same]; rfl
        · refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
          rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s b₀ hb_lt.le]
          refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
          rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt]
          simp only [hlo_hi, hcf, ↓reduceIte]
          exact validProg_bind (validProg_writePacked hw hgk hidx_ev hbm_b)
            (validProg_pure _)
    set s1 : Memory.State := { mem := m1, frontier := s.frontier }
    have hev1 : ∀ x ≤ b₀ + 1,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s1.mem (2 * x) =
          bp x := by
      intro x hx
      dsimp only [s1, m1]
      rcases Nat.le_iff_lt_or_eq.mp hx with hlt | rfl
      · rw [readPacked_writePacked_of_ne hw _ (by omega)]; exact hev x (Nat.le_of_lt_succ hlt)
      · exact readPacked_writePacked_self _ _ _ _ _ hbp1_pow
    have hodd1 : ∀ idx < 16 * M, idx % 2 = 1 →
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s1.mem idx =
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s₀.mem idx := by
      intro idx hidx hmod
      dsimp only [s1, m1]
      rw [readPacked_writePacked_of_ne hw _ (by omega)]
      exact hodd idx hidx hmod
    have hout1 : ∀ a, (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
        s1.mem a = s₀.mem a := by
      intro a ha; dsimp only [s1, m1]
      rw [writePacked_outside hw _ hidx_ev _ (by omega)]; exact hout a ha
    obtain ⟨hf_r, hvp_r, hev_r, hodd_r, hout_r⟩ := ih (b₀ + 1) s1 (by omega) hev1 hodd1 hout1
    have hadd : b₀ + 1 + rem = b₀ + (rem + 1) := by omega
    rw [hadd] at hev_r
    unfold bpPrefixLoopProg at hf_r hvp_r hev_r hodd_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hf_r
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro x hx; rw [clientState_bind, hs1.1, hs1.2.1]; exact hev_r x hx
    · intro idx hidx hmod
      rw [clientState_bind, hs1.1, hs1.2.1]; exact hodd_r idx hidx hmod
    · intro a ha; rw [clientState_bind, hs1.1, hs1.2.1]; exact hout_r a ha

/-! ### Phase B: `fillBackPtrOuterLoopProg` (populate `offBackPtr[b * cb + k]`) -/

@[irreducible] private def fillBackPtrInnerStepProg :
    (HealRt × (ℕ × (ℕ × ℕ))) × ℕ → Memory.Prog ℕ
  | ((rt, (b_in, (remBack_in, bpb_in))), k_in) => do
    let b ← pure b_in
    let remBack ← pure remBack_in
    let bp_b ← pure bpb_in
    let k ← pure k_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let k1 ← pure (k + one_v)
    let idx ← pure (b * hlCB rt + k)
    if k < remBack then
      if bp_b ≤ hlNMax rt then
        let remN ← pure (hlNMax rt - bp_b)
        if k ≤ remN then
          let v ← pure (bp_b + k)
          writePackedGenProg ((((hlBase rt, hlOffBp rt), (hlGBits rt, hlW rt)), idx), v)
          pure k1
        else
          writePackedGenProg ((((hlBase rt, hlOffBp rt), (hlGBits rt, hlW rt)), idx), zero_v)
          pure k1
      else
        writePackedGenProg ((((hlBase rt, hlOffBp rt), (hlGBits rt, hlW rt)), idx), zero_v)
        pure k1
    else
      writePackedGenProg ((((hlBase rt, hlOffBp rt), (hlGBits rt, hlW rt)), idx), zero_v)
      pure k1

private theorem memoryCost_fillBackPtrInnerStep_pos
    (d : (HealRt × (ℕ × (ℕ × ℕ))) × ℕ) (s : Memory.State) :
    0 < memoryCost (fillBackPtrInnerStepProg d) s := by
  rcases d with ⟨⟨rt, b, remBack, bp_b⟩, k⟩
  unfold fillBackPtrInnerStepProg
  simp only [pure_bind]
  simp only [← PFunctor.FreeM.bind_eq_bind]
  split_ifs <;> (rw [memoryCost_bind]; change 0 < 4 + _; omega)

private def FillBackPtrInnerPre (w : ℕ)
    (d : (HealRt × (ℕ × (ℕ × ℕ))) × ℕ) (_s : Memory.State) : Prop :=
  HealRtEnvGen w d.1.1 ∧ d.1.2.1 < hlM d.1.1 ∧ d.2 < hlCB d.1.1

private theorem realizes_fillBackPtrInnerStep :
    Realizes .exact fillBackPtrInnerStepProg
      (WordEncoding.encode (α := (HealRt × (ℕ × (ℕ × ℕ))) × ℕ))
      (WordEncoding.encode (α := ℕ))
      FillBackPtrInnerPre
      (fun _ _ => 0) := by
  unfold fillBackPtrInnerStepProg
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨rt, b, remBack, bp_b⟩, k⟩
    dsimp only [FillBackPtrInnerPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hb_lt, hk_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨_, _, hMcb, _, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.1
    dsimp only [mkHealRt, hlBase, hlW, hlNMax, hlM, hlCB, hlGBits, hlOffBp] at *
    have hidx := mul_add_lt_mul_bound hb_lt hk_lt
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.packed_safe_of_le hgk hidx hseg
  )

@[irreducible] private def fillBackPtrInnerLoopProg :
    ((HealRt × (ℕ × (ℕ × ℕ))) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, k₀), rem) => iterate fillBackPtrInnerStepProg cfg rem k₀

private theorem realizes_fillBackPtrInnerLoop :
    Realizes .exact fillBackPtrInnerLoopProg
      (WordEncoding.encode (α := ((HealRt × (ℕ × (ℕ × ℕ))) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, k₀), rem) s =>
        iterationSafe fillBackPtrInnerStepProg FillBackPtrInnerPre w cfg rem k₀ s)
      (fun _ _ => 0) := by
  unfold fillBackPtrInnerLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt × (ℕ × (ℕ × ℕ))))
    (WordEncoding.encode (α := ℕ))
    realizes_fillBackPtrInnerStep
    memoryCost_fillBackPtrInnerStep_pos

private theorem fillBackPtrInnerLoop_safe {c U V w n_max base b remBack bp_b : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hb : b < numBucketsWhp n_max) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem k₀ (s : Memory.State),
      k₀ + rem ≤ capBackWhp n_max →
      iterationSafe fillBackPtrInnerStepProg FillBackPtrInnerPre w
        (rt, (b, (remBack, bp_b))) rem k₀ s := by
  intro rt rem
  induction rem with
  | zero => intro _ _ _; exact trivial
  | succ rem ih =>
    intro k₀ s hle
    have hk_lt : k₀ < capBackWhp n_max := by omega
    refine ⟨⟨⟨c, U, V, w, n_max, henv, rfl⟩, hb, hk_lt⟩, ?_⟩
    rw [clientState_width, clientResult_width]
    set p1 := fillBackPtrInnerStepProg ((rt, (b, (remBack, bp_b))), k₀)
    have hr1 : (Memory.spec 0).clientResult s p1 = k₀ + 1 := by
      dsimp only [p1]; unfold fillBackPtrInnerStepProg; dsimp only [writePackedGenProg]
      simp only [pure_bind]
      split_ifs <;> (rw [clientResult_bind]; rfl)
    rw [hr1]
    exact ih (k₀ + 1) _ (by omega)

private theorem fillBackPtrInnerLoop_spec {c U V w n_max base b remBack bp_b : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hsum_le : bp_b + remBack ≤ n_max) :
    let rt := mkHealRt c U V w n_max base
    let M := numBucketsWhp n_max
    let cb := capBackWhp n_max
    ∀ rem k₀ (s : Memory.State),
      k₀ + rem ≤ cb →
      (∀ k < k₀,
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s.mem
          (b * cb + k) = if k < remBack then bp_b + k else 0) →
      let prog := fillBackPtrInnerLoopProg (((rt, (b, (remBack, bp_b))), k₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ k < k₀ + rem,
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
          (b * cb + k) = if k < remBack then bp_b + k else 0) ∧
      (∀ b' < M, b' ≠ b → ∀ k < cb,
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
          (b' * cb + k) =
          readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s.mem
            (b' * cb + k)) ∧
      (∀ a, (a < base + offBackPtr c U V w n_max ∨ base + offBackAux c U V w n_max ≤ a) →
        s'.mem a = s.mem a) := by
  intro rt M cb rem
  have hw := henv.2.1
  obtain ⟨_, _, _, _, _, _, _, hgk⟩ := hl_bounds henv
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.1
  have hbp_b_seg : base + offBackPtr c U V w n_max +
      packedWords (M * cb) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  have hbp_end : offBackPtr c U V w n_max +
      packedWords (M * cb) (globalPtrBits n_max) w = offBackAux c U V w n_max := rfl
  induction rem with
  | zero =>
    intro k₀ s _ hprev
    unfold fillBackPtrInnerLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    intro k₀ s hle hprev
    have hk_lt : k₀ < cb := by omega
    have hidx := mul_add_lt_mul_bound hb hk_lt
    set vVal := if k₀ < remBack then bp_b + k₀ else 0
    have hv_pow : vVal < 2 ^ globalPtrBits n_max := by
      dsimp only [vVal]; split_ifs <;> exact lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    set p1 := fillBackPtrInnerStepProg ((rt, (b, (remBack, bp_b))), k₀)
    set m1 := writePacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s.mem
      (b * cb + k₀) vVal
    have hs1 : (Memory.spec 0).clientState s p1 = { mem := m1, frontier := s.frontier } ∧
        (Memory.spec 0).clientResult s p1 = k₀ + 1 ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold fillBackPtrInnerStepProg; dsimp only [rt, mkHealRt, hlBase, hlW,
        hlNMax, hlCB, hlGBits, hlOffBp, writePackedGenProg]
      simp only [pure_bind]
      by_cases hkr : k₀ < remBack
      · have h1 : bp_b ≤ n_max := by omega
        have h2 : k₀ ≤ n_max - bp_b := by omega
        simp only [hkr, h1, h2, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, clientState_writePackedProg]
          dsimp only [m1, vVal]; simp only [hkr, ↓reduceIte]; rfl
        · rw [clientResult_bind]; rfl
        · exact validProg_bind (validProg_writePacked hw hgk hidx hbp_b_seg)
            (validProg_pure _)
      · simp only [hkr, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, clientState_writePackedProg]
          dsimp only [m1, vVal]; simp only [hkr, ↓reduceIte]; rfl
        · rw [clientResult_bind]; rfl
        · exact validProg_bind (validProg_writePacked hw hgk hidx hbp_b_seg)
            (validProg_pure _)
    set s1 : Memory.State := { mem := m1, frontier := s.frontier }
    have hprev1 : ∀ k < k₀ + 1,
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s1.mem
          (b * cb + k) = if k < remBack then bp_b + k else 0 := by
      intro k hk
      dsimp only [s1, m1]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · rw [readPacked_writePacked_of_ne hw _ (by omega)]; exact hprev k hlt
      · exact readPacked_writePacked_self _ _ _ _ _ hv_pow
    obtain ⟨hf_r, hvp_r, hp_r, hoth_r, hout_r⟩ := ih (k₀ + 1) s1 (by omega) hprev1
    have hadd : k₀ + 1 + rem = k₀ + (rem + 1) := by omega
    rw [hadd] at hp_r
    unfold fillBackPtrInnerLoopProg at hf_r hvp_r hp_r hoth_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hf_r
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro k hk; rw [clientState_bind, hs1.1, hs1.2.1]; exact hp_r k hk
    · intro b' hb' hne k hk
      rw [clientState_bind, hs1.1, hs1.2.1, hoth_r b' hb' hne k hk]
      have hne_idx : b' * cb + k ≠ b * cb + k₀ := by
        intro heq
        have hcb_pos : 0 < cb := by omega
        have hd1 : (b' * cb + k) / cb = b' := by
          rw [mul_comm, Nat.mul_add_div hcb_pos, Nat.div_eq_of_lt hk, Nat.add_zero]
        have hd2 : (b * cb + k₀) / cb = b := by
          rw [mul_comm, Nat.mul_add_div hcb_pos, Nat.div_eq_of_lt hk_lt, Nat.add_zero]
        exact hne (by rw [← hd1, heq, hd2])
      exact readPacked_writePacked_of_ne hw _ hne_idx _
    · intro a ha
      rw [clientState_bind, hs1.1, hs1.2.1, hout_r a ha]
      dsimp only [M, cb] at hidx hbp_end
      exact writePacked_outside hw _ hidx _ (by omega)

@[irreducible] private def fillBackPtrOuterStepProg : HealRt × ℕ → Memory.Prog ℕ
  | (rt, b_in) => do
    let b ← pure b_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let b1 ← pure (b + one_v)
    let lo ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b)
    let hi ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b1)
    let idxBm ← pure (2 * b)
    let bp_b ← readPackedGenProg (((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxBm)
    if lo ≤ hi then
      let cnt ← pure (hi - lo)
      if hlCF rt ≤ cnt then
        let remBack ← pure (cnt - hlCF rt)
        let _ ← fillBackPtrInnerLoopProg (((rt, (b, (remBack, bp_b))), zero_v), hlCB rt)
        pure b1
      else
        let _ ← fillBackPtrInnerLoopProg (((rt, (b, (zero_v, bp_b))), zero_v), hlCB rt)
        pure b1
    else
      let _ ← fillBackPtrInnerLoopProg (((rt, (b, (zero_v, bp_b))), zero_v), hlCB rt)
      pure b1

private theorem memoryCost_fillBackPtrOuterStep_pos (d : HealRt × ℕ) (s : Memory.State) :
    0 < memoryCost (fillBackPtrOuterStepProg d) s := by
  rcases d with ⟨rt, b⟩
  unfold fillBackPtrOuterStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

private def FillBackPtrOuterPre (w : ℕ) (d : HealRt × ℕ) (_s : Memory.State) : Prop :=
  HealRtEnvGen w d.1 ∧ d.2 < hlM d.1

private theorem realizes_fillBackPtrOuterStep :
    Realizes .exact fillBackPtrOuterStepProg
      (WordEncoding.encode (α := HealRt × ℕ))
      (WordEncoding.encode (α := ℕ))
      FillBackPtrOuterPre
      (fun _ _ => 0) := by
  unfold fillBackPtrOuterStepProg
  have hrp := realizes_readPackedGen
  have hil := realizes_fillBackPtrInnerLoop
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨rt, b⟩
    dsimp only [FillBackPtrOuterPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hb_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨hM_lt, h16M, _, _, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := WhpLargeEnv.seg_end_le c U V w n_max
    dsimp only [mkHealRt, hlBase, hlW, hlM, hlCF, hlCB, hlGBits, hlOffBm, hlOffFb] at *
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact to_true_exists
        (henv.packed_safe_of_le hgk (idx := b) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists
        (henv.packed_safe_of_le hgk (idx := b + 1) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists (henv.bktMeta_safe (idx := 2 * b) (by omega))
    | exact fillBackPtrInnerLoop_safe henv hb_lt (capBackWhp n_max) 0 s (by omega)
  )

@[irreducible] private def fillBackPtrOuterLoopProg : (HealRt × ℕ) × ℕ → Memory.Prog ℕ
  | ((rt, b₀), rem) => iterate fillBackPtrOuterStepProg rt rem b₀

private theorem realizes_fillBackPtrOuterLoop :
    Realizes .exact fillBackPtrOuterLoopProg
      (WordEncoding.encode (α := (HealRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((rt, b₀), rem) s =>
        iterationSafe fillBackPtrOuterStepProg FillBackPtrOuterPre w rt rem b₀ s)
      (fun _ _ => 0) := by
  unfold fillBackPtrOuterLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt))
    (WordEncoding.encode (α := ℕ))
    realizes_fillBackPtrOuterStep
    memoryCost_fillBackPtrOuterStep_pos

private theorem fillBackPtrOuterLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ numBucketsWhp n_max →
      iterationSafe fillBackPtrOuterStepProg FillBackPtrOuterPre w rt rem b₀ s := by
  intro rt rem
  induction rem with
  | zero => intro _ _ _; exact trivial
  | succ rem ih =>
    intro b₀ s hle
    refine ⟨⟨⟨c, U, V, w, n_max, henv, rfl⟩, by dsimp [rt, mkHealRt, hlM]; omega⟩, ?_⟩
    rw [clientState_width, clientResult_width]
    have hr1 : (Memory.spec 0).clientResult s (fillBackPtrOuterStepProg (rt, b₀)) = b₀ + 1 := by
      unfold fillBackPtrOuterStepProg; dsimp only [readPackedGenProg]
      simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedProg,
        clientResult_bind, clientState_readPackedProg,
        clientResult_bind, clientState_readPackedProg]
      split_ifs <;> (rw [clientResult_bind]; rfl)
    rw [hr1]
    exact ih (b₀ + 1) _ (by omega)

private theorem fillBackPtrOuterLoop_spec {c U V w n_max base : ℕ} {fbStart : ℕ → ℕ}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hfb_adj : ∀ b < numBucketsWhp n_max, fbStart b ≤ fbStart (b + 1))
    (hbp_le : buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) fbStart
      (numBucketsWhp n_max) ≤ n_max)
    (hfb_mem : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s₀.mem x = fbStart x)
    (hbp_mem : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s₀.mem (2 * x) =
        buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) fbStart x) :
    let rt := mkHealRt c U V w n_max base
    let M := numBucketsWhp n_max
    let cf := capFrontWhp n_max
    let cb := capBackWhp n_max
    let bp := buildBackPrefix M cf fbStart
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ M →
      (∀ b < b₀, ∀ k < cb,
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s.mem
          (b * cb + k) = if k < (fbStart (b + 1) - fbStart b) - cf then bp b + k else 0) →
      (∀ a, (a < base + offBackPtr c U V w n_max ∨ base + offBackAux c U V w n_max ≤ a) →
        s.mem a = s₀.mem a) →
      let prog := fillBackPtrOuterLoopProg ((rt, b₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ b < b₀ + rem, ∀ k < cb,
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
          (b * cb + k) = if k < (fbStart (b + 1) - fbStart b) - cf then bp b + k else 0) ∧
      (∀ a, (a < base + offBackPtr c U V w n_max ∨ base + offBackAux c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) := by
  intro rt M cf cb bp rem
  have hw := henv.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.1 _
  have hbm_end : offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w = offFbStart c U V w n_max := rfl
  have hfb_end : offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w = offBackPtr c U V w n_max := rfl
  obtain ⟨_, hbp_adj, _, hbp_mono⟩ := backPrefix_spec M cf fbStart
  induction rem with
  | zero =>
    intro b₀ s _ hprev hout
    unfold fillBackPtrOuterLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, hout⟩
  | succ rem ih =>
    intro b₀ s hle hprev hout
    have hb_lt : b₀ < M := by omega
    have hfb_s : ∀ x ≤ M,
        readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem x = fbStart x :=
      fun x hx => (readPacked_congr hw (hidx := show x < M + 1 by omega)
        (fun a ⟨_, ha2⟩ => hout a (Or.inl (by dsimp only [M] at hfb_end ha2; omega)))).trans
        (hfb_mem x hx)
    have hbp_s : readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
        (2 * b₀) = bp b₀ :=
      (readPacked_congr hw (hidx := show 2 * b₀ < 16 * M by omega)
        (fun a ⟨_, ha2⟩ => hout a (Or.inl (by dsimp only [M] at hbm_end hfb_end ha2; omega)))).trans
        (hbp_mem b₀ hb_lt.le)
    have hlo_hi := hfb_adj b₀ hb_lt
    set remBack := (fbStart (b₀ + 1) - fbStart b₀) - cf
    have hsum_le : bp b₀ + remBack ≤ n_max := by
      have h1 : bp (b₀ + 1) = bp b₀ + remBack := hbp_adj b₀ hb_lt
      have h2 : bp (b₀ + 1) ≤ n_max := (hbp_mono (b₀ + 1) M hb_lt le_rfl).trans hbp_le
      omega
    obtain ⟨hin_f, hin_vp, hin_k, hin_oth, hin_out⟩ := fillBackPtrInnerLoop_spec
      (b := b₀) (remBack := remBack) (bp_b := bp b₀) henv hb_lt hsum_le cb 0 s (by omega)
      (fun _ h => absurd h (Nat.not_lt_zero _))
    rw [Nat.zero_add] at hin_k
    set s_in := (Memory.spec 0).clientState s
      (fillBackPtrInnerLoopProg (((rt, (b₀, (remBack, bp b₀))), 0), cb))
    set p1 := fillBackPtrOuterStepProg (rt, b₀)
    have hs1 : (Memory.spec 0).clientState s p1 = s_in ∧
        (Memory.spec 0).clientResult s p1 = b₀ + 1 ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold fillBackPtrOuterStepProg; dsimp only [rt, mkHealRt, hlBase, hlW,
        hlCF, hlCB, hlGBits, hlOffBm, hlOffFb, readPackedGenProg]
      simp only [pure_bind]
      by_cases hcf : cf ≤ fbStart (b₀ + 1) - fbStart b₀
      · refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
            clientState_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt,
            clientState_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hbp_s]
          simp only [hlo_hi, show capFrontWhp n_max ≤ fbStart (b₀ + 1) - fbStart b₀ from hcf,
            ↓reduceIte]
          rw [clientState_bind]; rfl
        · rw [clientResult_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
            clientResult_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt,
            clientResult_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hbp_s]
          simp only [hlo_hi, show capFrontWhp n_max ≤ fbStart (b₀ + 1) - fbStart b₀ from hcf,
            ↓reduceIte]
          rw [clientResult_bind]; rfl
        · refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
          rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s b₀ hb_lt.le]
          refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
          rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt]
          refine validProg_bind (validProg_readPacked hw (by omega) hbm_b) ?_
          rw [clientState_readPackedProg, clientResult_readPackedProg, hbp_s]
          simp only [hlo_hi, show capFrontWhp n_max ≤ fbStart (b₀ + 1) - fbStart b₀ from hcf,
            ↓reduceIte]
          dsimp only [rt, mkHealRt] at hin_vp
          exact validProg_bind hin_vp (validProg_pure _)
      · have hrem0 : remBack = 0 := by dsimp only [remBack]; omega
        refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
            clientState_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt,
            clientState_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hbp_s]
          simp only [hlo_hi, show ¬(capFrontWhp n_max ≤ fbStart (b₀ + 1) - fbStart b₀) from hcf,
            ↓reduceIte]
          rw [clientState_bind]
          dsimp only [s_in, rt, mkHealRt]; rw [hrem0]; rfl
        · rw [clientResult_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
            clientResult_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt,
            clientResult_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hbp_s]
          simp only [hlo_hi, show ¬(capFrontWhp n_max ≤ fbStart (b₀ + 1) - fbStart b₀) from hcf,
            ↓reduceIte]
          rw [clientResult_bind]; rfl
        · refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
          rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s b₀ hb_lt.le]
          refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
          rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt]
          refine validProg_bind (validProg_readPacked hw (by omega) hbm_b) ?_
          rw [clientState_readPackedProg, clientResult_readPackedProg, hbp_s]
          simp only [hlo_hi, show ¬(capFrontWhp n_max ≤ fbStart (b₀ + 1) - fbStart b₀) from hcf,
            ↓reduceIte]
          dsimp only [rt, mkHealRt] at hin_vp
          rw [hrem0] at hin_vp
          exact validProg_bind hin_vp (validProg_pure _)
    have hprev1 : ∀ b < b₀ + 1, ∀ k < cb,
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s_in.mem
          (b * cb + k) = if k < (fbStart (b + 1) - fbStart b) - cf then bp b + k else 0 := by
      intro b hb k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hlt | rfl
      · rw [hin_oth b (hlt.trans hb_lt) (by omega) k hk]; exact hprev b hlt k hk
      · exact hin_k k hk
    have hout1 : ∀ a, (a < base + offBackPtr c U V w n_max ∨ base + offBackAux c U V w n_max ≤ a) →
        s_in.mem a = s₀.mem a := fun a ha => (hin_out a ha).trans (hout a ha)
    obtain ⟨hf_r, hvp_r, hp_r, hout_r⟩ := ih (b₀ + 1) s_in (by omega) hprev1 hout1
    have hadd : b₀ + 1 + rem = b₀ + (rem + 1) := by omega
    rw [hadd] at hp_r
    unfold fillBackPtrOuterLoopProg at hf_r hvp_r hp_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hf_r.trans hin_f
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro b hb k hk
      rw [clientState_bind, hs1.1, hs1.2.1]; exact hp_r b hb k hk
    · intro a ha; rw [clientState_bind, hs1.1, hs1.2.1]; exact hout_r a ha

/-! ### Phase D1: `fillPoolOwnerLoopProg` (populate `offPoolOwner[poolIdx]`) -/

@[irreducible] private def fillPoolOwnerStepProg : (HealRt × ℕ) × ℕ → Memory.Prog ℕ
  | ((rt, tb_in), pid_in) => do
    let totalBack ← pure tb_in
    let poolIdx ← pure pid_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let two_v ← pure 2
    let p1 ← pure (poolIdx + one_v)
    if poolIdx < totalBack then
      let sb ← scanBucketLoopProg
        (((((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), (two_v, poolIdx)), (zero_v, zero_v)),
         hlM rt)
      let b ← pure sb.2
      if b < hlM rt then
        let idxBm ← pure (2 * b)
        let bp_b ← readPackedGenProg (((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxBm)
        if bp_b ≤ poolIdx then
          let k ← pure (poolIdx - bp_b)
          if k < hlCB rt then
            let enc ← pure (b * hlCB rt + k)
            writePackedGenProg ((((hlBase rt, hlOffPo rt), (hlGBits rt, hlW rt)), poolIdx), enc)
            pure p1
          else
            writePackedGenProg
              ((((hlBase rt, hlOffPo rt), (hlGBits rt, hlW rt)), poolIdx), zero_v)
            pure p1
        else
          writePackedGenProg ((((hlBase rt, hlOffPo rt), (hlGBits rt, hlW rt)), poolIdx), zero_v)
          pure p1
      else
        writePackedGenProg ((((hlBase rt, hlOffPo rt), (hlGBits rt, hlW rt)), poolIdx), zero_v)
        pure p1
    else
      writePackedGenProg ((((hlBase rt, hlOffPo rt), (hlGBits rt, hlW rt)), poolIdx), zero_v)
      pure p1

private theorem memoryCost_fillPoolOwnerStep_pos (d : (HealRt × ℕ) × ℕ) (s : Memory.State) :
    0 < memoryCost (fillPoolOwnerStepProg d) s := by
  rcases d with ⟨⟨rt, tb⟩, pid⟩
  have hwp : ∀ y s', memoryCost (writePackedGenProg y) s' = 4 := fun _ _ => rfl
  unfold fillPoolOwnerStepProg
  simp only [pure_bind]
  simp only [← PFunctor.FreeM.bind_eq_bind]
  split_ifs
  · rw [memoryCost_bind]
    split_ifs
    · rw [memoryCost_bind]
      split_ifs <;> (rw [memoryCost_bind, hwp]; omega)
    · rw [memoryCost_bind, hwp]; omega
  · rw [memoryCost_bind, hwp]; omega

private def FillPoolOwnerPre (w : ℕ) (d : (HealRt × ℕ) × ℕ) (_s : Memory.State) : Prop :=
  HealRtEnvGen w d.1.1 ∧ d.2 < hlPoolSize d.1.1

private theorem realizes_fillPoolOwnerStep :
    Realizes .exact fillPoolOwnerStepProg
      (WordEncoding.encode (α := (HealRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      FillPoolOwnerPre
      (fun _ _ => 0) := by
  unfold fillPoolOwnerStepProg
  have hsbl := realizes_scanBucketLoop
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨rt, totalBack⟩, poolIdx⟩
    dsimp only [FillPoolOwnerPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hp_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨_, h16M, hMcb, hps_le, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.2.1
    obtain ⟨hsb_sf, hsb_st, _, _⟩ :=
      scanBucketLoop_invariant (target := poolIdx) henv (Or.inr ⟨rfl, rfl⟩) (s := s)
    dsimp only [mkHealRt, hlBase, hlW, hlM, hlCB, hlPoolSize, hlGBits, hlOffBm, hlOffPo] at *
    simp only [hsb_st, hcs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | (refine henv.fits_of_le_n_max ?_
       exact (mul_add_lt_mul_bound (by assumption) (by assumption)).le.trans hMcb)
    | exact to_true_exists (henv.bktMeta_safe (idx := 2 * _) (by omega))
    | exact to_true_exists (henv.packed_safe_of_le hgk hp_lt hseg)
  )

@[irreducible] private def fillPoolOwnerLoopProg :
    ((HealRt × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, p₀), rem) => iterate fillPoolOwnerStepProg cfg rem p₀

private theorem realizes_fillPoolOwnerLoop :
    Realizes .exact fillPoolOwnerLoopProg
      (WordEncoding.encode (α := ((HealRt × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, p₀), rem) s =>
        iterationSafe fillPoolOwnerStepProg FillPoolOwnerPre w cfg rem p₀ s)
      (fun _ _ => 0) := by
  unfold fillPoolOwnerLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizes_fillPoolOwnerStep
    memoryCost_fillPoolOwnerStep_pos

private theorem fillPoolOwnerLoop_safe {c U V w n_max base totalBack : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem p₀ (s : Memory.State),
      p₀ + rem ≤ poolSizeWhp n_max →
      iterationSafe fillPoolOwnerStepProg FillPoolOwnerPre w (rt, totalBack) rem p₀ s := by
  intro rt rem
  induction rem with
  | zero => intro _ _ _; exact trivial
  | succ rem ih =>
    intro p₀ s hle
    have hp_lt : p₀ < poolSizeWhp n_max := by omega
    refine ⟨⟨⟨c, U, V, w, n_max, henv, rfl⟩, hp_lt⟩, ?_⟩
    rw [clientState_width, clientResult_width]
    have hr1 : (Memory.spec 0).clientResult s
        (fillPoolOwnerStepProg ((rt, totalBack), p₀)) = p₀ + 1 := by
      unfold fillPoolOwnerStepProg; dsimp only; simp only [pure_bind]
      split_ifs with hlt
      · rw [clientResult_bind]
        split_ifs with hb
        · rw [clientResult_bind]
          split_ifs <;> (rw [clientResult_bind]; rfl)
        · rw [clientResult_bind]; rfl
      · rw [clientResult_bind]; rfl
    rw [hr1]
    exact ih (p₀ + 1) _ (by omega)

private theorem fillPoolOwnerLoop_spec {c U V w n_max base : ℕ} {fbStart : ℕ → ℕ}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hback_cb : ∀ b < numBucketsWhp n_max,
      (fbStart (b + 1) - fbStart b) - capFrontWhp n_max < capBackWhp n_max)
    (hbp_mem : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s₀.mem (2 * x) =
        buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) fbStart x) :
    let rt := mkHealRt c U V w n_max base
    let M := numBucketsWhp n_max
    let cf := capFrontWhp n_max
    let cb := capBackWhp n_max
    let bp := buildBackPrefix M cf fbStart
    let findOwner : ℕ → ℕ := fun poolIdx =>
      let b := csrBucketOfIdx bp poolIdx M
      let k := poolIdx - bp b
      if poolIdx < bp M then b * cb + k else 0
    ∀ rem p₀ (s : Memory.State),
      p₀ + rem ≤ poolSizeWhp n_max →
      (∀ idx < p₀,
        readPacked (base + offPoolOwner c U V w n_max) (globalPtrBits n_max) w s.mem idx =
          findOwner idx) →
      (∀ a, (a < base + offPoolOwner c U V w n_max ∨ base + offBtMeta c U V w n_max ≤ a) →
        s.mem a = s₀.mem a) →
      let prog := fillPoolOwnerLoopProg (((rt, bp M), p₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ idx < p₀ + rem,
        readPacked (base + offPoolOwner c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
          findOwner idx) ∧
      (∀ a, (a < base + offPoolOwner c U V w n_max ∨ base + offBtMeta c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) := by
  intro rt M cf cb bp findOwner rem
  have hw := henv.2.1
  have hM_pos : 0 < M := Nat.two_pow_pos _
  obtain ⟨_, _, hMcb, _, _, _, _, hgk⟩ := hl_bounds henv
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  have hpo_b : base + offPoolOwner c U V w n_max +
      packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.2.2.2.1 _
  have hpo_end : offPoolOwner c U V w n_max +
      packedWords (poolSizeWhp n_max) (globalPtrBits n_max) w = offBtMeta c U V w n_max := rfl
  have hbm_le_po : offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w ≤ offPoolOwner c U V w n_max := by
    have h1 : offFbStart c U V w n_max =
      offBktMeta c U V w n_max + packedWords (16 * M) (globalPtrBits n_max) w := rfl
    unfold offPoolOwner offPoolFreeStack offBackAux offBackPtr; omega
  obtain ⟨hbp0, hbp_adj, _, _⟩ := backPrefix_spec M cf fbStart
  have hbp_le_step : ∀ b < M, bp b ≤ bp (b + 1) := fun b hb => by
    have h1 : bp (b + 1) = bp b + ((fbStart (b + 1) - fbStart b) - cf) := hbp_adj b hb
    omega
  induction rem with
  | zero =>
    intro p₀ s _ hprev hout
    unfold fillPoolOwnerLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, hout⟩
  | succ rem ih =>
    intro p₀ s hle hprev hout
    have hp_lt : p₀ < poolSizeWhp n_max := by omega
    have hbp_s : ∀ x ≤ M,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem (2 * x) =
          bp x := fun x hx =>
      (readPacked_congr hw (hidx := show 2 * x < 16 * M by omega)
        (fun a ⟨_, ha2⟩ => hout a (Or.inl (by dsimp only [M] at hbm_le_po ha2; omega)))).trans
        (hbp_mem x hx)
    set p1 := fillPoolOwnerStepProg ((rt, bp M), p₀)
    set m1 := writePacked (base + offPoolOwner c U V w n_max) (globalPtrBits n_max) w s.mem
      p₀ (findOwner p₀)
    have hown_pow : findOwner p₀ < 2 ^ globalPtrBits n_max := by
      dsimp only [findOwner]
      by_cases hlt : p₀ < bp M
      · obtain ⟨hb_i, hlo_i, hhi_i⟩ := csrBucketOfIdx_spec hbp0 hbp_le_step M le_rfl p₀ hlt
        have hk_cb : p₀ - bp (csrBucketOfIdx bp p₀ M) < cb := by
          have h1 : bp (csrBucketOfIdx bp p₀ M + 1) =
              bp (csrBucketOfIdx bp p₀ M) +
                ((fbStart (csrBucketOfIdx bp p₀ M + 1) - fbStart (csrBucketOfIdx bp p₀ M)) - cf) :=
            hbp_adj _ hb_i
          have h2 : (fbStart (csrBucketOfIdx bp p₀ M + 1) - fbStart (csrBucketOfIdx bp p₀ M)) - cf <
              cb := hback_cb _ hb_i
          change buildBackPrefix M cf fbStart (csrBucketOfIdx bp p₀ M) ≤ p₀ at hlo_i
          dsimp only [bp, cf, cb] at h1 h2 hlo_i hhi_i ⊢
          omega
        rw [ite_eq_left hlt]
        exact lt_two_pow_globalPtrBits_of_le_n_max ((mul_add_lt_mul_bound hb_i hk_cb).le.trans hMcb)
      · rw [ite_eq_right hlt]; exact Nat.two_pow_pos _
    have hs1 : (Memory.spec 0).clientState s p1 = { mem := m1, frontier := s.frontier } ∧
        (Memory.spec 0).clientResult s p1 = p₀ + 1 ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold fillPoolOwnerStepProg; dsimp only [rt, mkHealRt, hlBase, hlW,
        hlM, hlCB, hlGBits, hlOffBm, hlOffPo, readPackedGenProg, writePackedGenProg]
      simp only [pure_bind]
      by_cases hlt : p₀ < bp M
      · obtain ⟨_, hsb_st, hsb_res, hsb_vp⟩ :=
          scanBucketLoop_invariant (target := p₀) henv (Or.inr ⟨rfl, rfl⟩) (s := s)
        have hsb_b : csrBucketOfIdx (fun x => readPacked (base + offBktMeta c U V w n_max)
            (globalPtrBits n_max) w s.mem (2 * x)) p₀ M = csrBucketOfIdx bp p₀ M :=
          csrBucketOfIdx_congr hbp_s
        rw [hsb_b] at hsb_res
        set b_i := csrBucketOfIdx bp p₀ M
        obtain ⟨hb_i, hlo_i, hhi_i⟩ := csrBucketOfIdx_spec hbp0 hbp_le_step M le_rfl p₀ hlt
        have hk_cb : p₀ - bp b_i < cb := by
          have h1 : bp (b_i + 1) = bp b_i + ((fbStart (b_i + 1) - fbStart b_i) - cf) :=
            hbp_adj b_i hb_i
          have h2 : (fbStart (b_i + 1) - fbStart b_i) - cf < cb := hback_cb b_i hb_i
          have hlo' : bp b_i ≤ p₀ := hlo_i
          have hhi' : p₀ < bp (b_i + 1) := hhi_i
          dsimp only [b_i, bp, cf, cb] at h1 h2 hlo' hhi' ⊢
          omega
        have hb_i' : b_i < M := hb_i
        have h2bi : 2 * b_i < 16 * M := by omega
        have hown_eq : findOwner p₀ = b_i * cb + (p₀ - bp b_i) := ite_eq_left hlt
        simp only [hlt, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, hsb_st, hsb_res]
          simp only [show b_i < numBucketsWhp n_max from hb_i, ↓reduceIte]
          rw [clientState_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hbp_s b_i hb_i.le]
          simp only [show bp b_i ≤ p₀ from hlo_i,
            show p₀ - bp b_i < capBackWhp n_max from hk_cb, ↓reduceIte]
          rw [clientState_bind, clientState_writePackedProg]
          dsimp only [m1]; rw [hown_eq]; rfl
        · rw [clientResult_bind, hsb_st, hsb_res]
          simp only [show b_i < numBucketsWhp n_max from hb_i, ↓reduceIte]
          rw [clientResult_bind, clientState_readPackedProg,
            clientResult_readPackedProg, hbp_s b_i hb_i.le]
          simp only [show bp b_i ≤ p₀ from hlo_i,
            show p₀ - bp b_i < capBackWhp n_max from hk_cb, ↓reduceIte]
          rw [clientResult_bind]; rfl
        · refine validProg_bind hsb_vp ?_; rw [hsb_st, hsb_res]
          simp only [show b_i < numBucketsWhp n_max from hb_i, ↓reduceIte]
          refine validProg_bind (validProg_readPacked hw h2bi hbm_b) ?_
          rw [clientState_readPackedProg, clientResult_readPackedProg, hbp_s b_i hb_i.le]
          simp only [show bp b_i ≤ p₀ from hlo_i,
            show p₀ - bp b_i < capBackWhp n_max from hk_cb, ↓reduceIte]
          exact validProg_bind (validProg_writePacked hw hgk hp_lt hpo_b)
            (validProg_pure _)
      · have hown0 : findOwner p₀ = 0 := ite_eq_right hlt
        simp only [hlt, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, clientState_writePackedProg]
          dsimp only [m1]; rw [hown0]; rfl
        · rw [clientResult_bind]; rfl
        · exact validProg_bind (validProg_writePacked hw hgk hp_lt hpo_b)
            (validProg_pure _)
    set s1 : Memory.State := { mem := m1, frontier := s.frontier }
    have hprev1 : ∀ idx < p₀ + 1,
        readPacked (base + offPoolOwner c U V w n_max) (globalPtrBits n_max) w s1.mem idx =
          findOwner idx := by
      intro idx hidx
      dsimp only [s1, m1]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hidx with hlt | rfl
      · rw [readPacked_writePacked_of_ne hw _ (by omega)]; exact hprev idx hlt
      · exact readPacked_writePacked_self _ _ _ _ _ hown_pow
    have hout1 : ∀ a, (a < base + offPoolOwner c U V w n_max ∨ base + offBtMeta c U V w n_max ≤ a) →
        s1.mem a = s₀.mem a := by
      intro a ha; dsimp only [s1, m1]
      rw [writePacked_outside hw _ hp_lt _ (by omega)]; exact hout a ha
    obtain ⟨hf_r, hvp_r, hp_r, hout_r⟩ := ih (p₀ + 1) s1 (by omega) hprev1 hout1
    have hadd : p₀ + 1 + rem = p₀ + (rem + 1) := by omega
    rw [hadd] at hp_r
    unfold fillPoolOwnerLoopProg at hf_r hvp_r hp_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hf_r
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro idx hidx; rw [clientState_bind, hs1.1, hs1.2.1]; exact hp_r idx hidx
    · intro a ha; rw [clientState_bind, hs1.1, hs1.2.1]; exact hout_r a ha

/-! ### Phase D2: `fillFreeStackLoopProg` (populate `offPoolFreeStack[j]`) -/

@[irreducible] private def fillFreeStackStepProg :
    (HealRt × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | ((rt, (tb_in, ft_in)), j_in) => do
    let totalBack ← pure tb_in
    let freeTop ← pure ft_in
    let j ← pure j_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let j1 ← pure (j + one_v)
    if j < freeTop then
      if totalBack ≤ hlNMax rt then
        let remN ← pure (hlNMax rt - totalBack)
        if j ≤ remN then
          let v ← pure (totalBack + j)
          writePackedGenProg ((((hlBase rt, hlOffPs rt), (hlGBits rt, hlW rt)), j), v)
          pure j1
        else
          writePackedGenProg ((((hlBase rt, hlOffPs rt), (hlGBits rt, hlW rt)), j), zero_v)
          pure j1
      else
        writePackedGenProg ((((hlBase rt, hlOffPs rt), (hlGBits rt, hlW rt)), j), zero_v)
        pure j1
    else
      writePackedGenProg ((((hlBase rt, hlOffPs rt), (hlGBits rt, hlW rt)), j), zero_v)
      pure j1

private theorem memoryCost_fillFreeStackStep_pos
    (d : (HealRt × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    0 < memoryCost (fillFreeStackStepProg d) s := by
  rcases d with ⟨⟨rt, tb, ft⟩, j⟩
  unfold fillFreeStackStepProg
  simp only [pure_bind]
  simp only [← PFunctor.FreeM.bind_eq_bind]
  split_ifs <;> (rw [memoryCost_bind]; change 0 < 4 + _; omega)

private def FillFreeStackPre (w : ℕ) (d : (HealRt × (ℕ × ℕ)) × ℕ) (_s : Memory.State) : Prop :=
  HealRtEnvGen w d.1.1 ∧ d.2 < hlPoolSize d.1.1

private theorem realizes_fillFreeStackStep :
    Realizes .exact fillFreeStackStepProg
      (WordEncoding.encode (α := (HealRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      FillFreeStackPre
      (fun _ _ => 0) := by
  unfold fillFreeStackStepProg
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨rt, tb, ft⟩, j⟩
    dsimp only [FillFreeStackPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hj_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨_, _, _, hps_le, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.1
    dsimp only [mkHealRt, hlBase, hlW, hlNMax, hlPoolSize, hlGBits, hlOffPs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.packed_safe_of_le hgk hj_lt hseg
  )

@[irreducible] private def fillFreeStackLoopProg :
    ((HealRt × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, j₀), rem) => iterate fillFreeStackStepProg cfg rem j₀

private theorem realizes_fillFreeStackLoop :
    Realizes .exact fillFreeStackLoopProg
      (WordEncoding.encode (α := ((HealRt × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, j₀), rem) s =>
        iterationSafe fillFreeStackStepProg FillFreeStackPre w cfg rem j₀ s)
      (fun _ _ => 0) := by
  unfold fillFreeStackLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ))
    realizes_fillFreeStackStep
    memoryCost_fillFreeStackStep_pos

private theorem fillFreeStackLoop_safe {c U V w n_max base tb ft : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem j₀ (s : Memory.State),
      j₀ + rem ≤ poolSizeWhp n_max →
      iterationSafe fillFreeStackStepProg FillFreeStackPre w (rt, (tb, ft)) rem j₀ s := by
  intro rt rem
  induction rem with
  | zero => intro _ _ _; exact trivial
  | succ rem ih =>
    intro j₀ s hle
    have hj_lt : j₀ < poolSizeWhp n_max := by omega
    refine ⟨⟨⟨c, U, V, w, n_max, henv, rfl⟩, hj_lt⟩, ?_⟩
    rw [clientState_width, clientResult_width]
    have hr1 : (Memory.spec 0).clientResult s
        (fillFreeStackStepProg ((rt, (tb, ft)), j₀)) = j₀ + 1 := by
      unfold fillFreeStackStepProg; dsimp only [writePackedGenProg]; simp only [pure_bind]
      split_ifs <;> (rw [clientResult_bind]; rfl)
    rw [hr1]
    exact ih (j₀ + 1) _ (by omega)

private theorem fillFreeStackLoop_spec {c U V w n_max base totalBack : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base)
    (htb_le : totalBack ≤ poolSizeWhp n_max) :
    let rt := mkHealRt c U V w n_max base
    let ps := poolSizeWhp n_max
    let freeTop := ps - totalBack
    ∀ rem j₀ (s : Memory.State),
      j₀ + rem ≤ ps →
      (∀ idx < j₀,
        readPacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s.mem idx =
          if idx < freeTop then totalBack + idx else 0) →
      let prog := fillFreeStackLoopProg (((rt, (totalBack, freeTop)), j₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ idx < j₀ + rem,
        readPacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
          if idx < freeTop then totalBack + idx else 0) ∧
      (∀ a, (a < base + offPoolFreeStack c U V w n_max ∨
          base + offPoolOwner c U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  intro rt ps freeTop rem
  have hw := henv.2.1
  obtain ⟨_, _, _, hps_le, _, _, _, hgk⟩ := hl_bounds henv
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.2.2.1
  have hps_b : base + offPoolFreeStack c U V w n_max +
      packedWords ps (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  have hps_end : offPoolFreeStack c U V w n_max +
      packedWords ps (globalPtrBits n_max) w = offPoolOwner c U V w n_max := rfl
  induction rem with
  | zero =>
    intro j₀ s _ hprev
    unfold fillFreeStackLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, fun _ _ => rfl⟩
  | succ rem ih =>
    intro j₀ s hle hprev
    have hj_lt : j₀ < ps := by omega
    set vVal := if j₀ < freeTop then totalBack + j₀ else 0
    have hv_pow : vVal < 2 ^ globalPtrBits n_max := by
      dsimp only [vVal, freeTop, ps] at *
      split_ifs <;> exact lt_two_pow_globalPtrBits_of_le_n_max (by omega)
    set p1 := fillFreeStackStepProg ((rt, (totalBack, freeTop)), j₀)
    set m1 := writePacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s.mem
      j₀ vVal
    have hs1 : (Memory.spec 0).clientState s p1 = { mem := m1, frontier := s.frontier } ∧
        (Memory.spec 0).clientResult s p1 = j₀ + 1 ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold fillFreeStackStepProg; dsimp only [rt, mkHealRt, hlBase, hlW,
        hlNMax, hlGBits, hlOffPs, writePackedGenProg]
      simp only [pure_bind]
      by_cases hjf : j₀ < freeTop
      · have h1 : totalBack ≤ n_max := htb_le.trans hps_le
        have h2 : j₀ ≤ n_max - totalBack := by dsimp only [freeTop, ps] at hjf hps_le; omega
        simp only [hjf, h1, h2, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, clientState_writePackedProg]
          dsimp only [m1, vVal]; simp only [hjf, ↓reduceIte]; rfl
        · rw [clientResult_bind]; rfl
        · exact validProg_bind (validProg_writePacked hw hgk hj_lt hps_b)
            (validProg_pure _)
      · simp only [hjf, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, clientState_writePackedProg]
          dsimp only [m1, vVal]; simp only [hjf, ↓reduceIte]; rfl
        · rw [clientResult_bind]; rfl
        · exact validProg_bind (validProg_writePacked hw hgk hj_lt hps_b)
            (validProg_pure _)
    set s1 : Memory.State := { mem := m1, frontier := s.frontier }
    have hprev1 : ∀ idx < j₀ + 1,
        readPacked (base + offPoolFreeStack c U V w n_max) (globalPtrBits n_max) w s1.mem idx =
          if idx < freeTop then totalBack + idx else 0 := by
      intro idx hidx
      dsimp only [s1, m1]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hidx with hlt | rfl
      · rw [readPacked_writePacked_of_ne hw _ (by omega)]; exact hprev idx hlt
      · exact readPacked_writePacked_self _ _ _ _ _ hv_pow
    obtain ⟨hf_r, hvp_r, hp_r, hout_r⟩ := ih (j₀ + 1) s1 (by omega) hprev1
    have hadd : j₀ + 1 + rem = j₀ + (rem + 1) := by omega
    rw [hadd] at hp_r
    unfold fillFreeStackLoopProg at hf_r hvp_r hp_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hf_r
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro idx hidx; rw [clientState_bind, hs1.1, hs1.2.1]; exact hp_r idx hidx
    · intro a ha
      rw [clientState_bind, hs1.1, hs1.2.1, hout_r a ha]
      dsimp only [ps] at hj_lt hps_end
      exact writePacked_outside hw _ hj_lt _ (by omega)

/-! ### Phase D3: `fillLocStateOuterLoopProg` (populate `offLocState`) -/

@[irreducible] private def fillLocStateInnerStepProg :
    (HealRt × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | ((rt, (b_in, cnt_in)), loc_in) => do
    let _ ← Memory.read (hlBase rt)
    let b ← pure b_in
    let cnt ← pure cnt_in
    let loc ← pure loc_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let loc1 ← pure (loc + one_v)
    if loc < cnt then
      writeLocStateGenProg
        ((((hlBase rt, hlOffLs rt), (hlTotalLoc rt, hlW rt)), (b, loc)), one_v)
      pure loc1
    else
      writeLocStateGenProg
        ((((hlBase rt, hlOffLs rt), (hlTotalLoc rt, hlW rt)), (b, loc)), zero_v)
      pure loc1

private theorem memoryCost_fillLocStateInnerStep_pos
    (d : (HealRt × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    0 < memoryCost (fillLocStateInnerStepProg d) s := by
  rcases d with ⟨⟨rt, b, cnt⟩, loc⟩
  unfold fillLocStateInnerStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 1 + _
  omega

private def FillLocStateInnerPre (w : ℕ)
    (d : (HealRt × (ℕ × ℕ)) × ℕ) (_s : Memory.State) : Prop :=
  HealRtEnvGen w d.1.1 ∧ d.1.2.1 < hlM d.1.1 ∧ d.2 < hlTotalLoc d.1.1

private theorem realizes_fillLocStateInnerStep :
    Realizes .exact fillLocStateInnerStepProg
      (WordEncoding.encode (α := (HealRt × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      FillLocStateInnerPre
      (fun _ _ => 0) := by
  unfold fillLocStateInnerStepProg
  have hwl := realizes_writeLocStateGen
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨rt, b, cnt⟩, loc⟩
    dsimp only [FillLocStateInnerPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hb_lt, hloc_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨_, _, _, _, h2T, _, hw3, _⟩ := hl_bounds henv
    have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.1
    have hn_fit := henv.fits_of_le_n_max le_rfl
    dsimp only [mkHealRt, hlBase, hlW, hlM, hlTotalLoc, hlOffLs] at *
    simp only [hcs_r] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | (refine ⟨numBucketsWhp n_max, rfl, hw3, h2T.trans hn_fit, hb_lt, hloc_lt, ?_⟩
       refine henv.fits_largeSpace.of_le ?_
       rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _)
  )

@[irreducible] private def fillLocStateInnerLoopProg :
    ((HealRt × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, l₀), rem) => iterate fillLocStateInnerStepProg cfg rem l₀

private theorem realizes_fillLocStateInnerLoop :
    Realizes .exact fillLocStateInnerLoopProg
      (WordEncoding.encode (α := ((HealRt × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, l₀), rem) s =>
        iterationSafe fillLocStateInnerStepProg FillLocStateInnerPre w cfg rem l₀ s)
      (fun _ _ => 0) := by
  unfold fillLocStateInnerLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ))
    realizes_fillLocStateInnerStep
    memoryCost_fillLocStateInnerStep_pos

private theorem fillLocStateInnerLoop_safe {c U V w n_max base b cnt : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) (hb : b < numBucketsWhp n_max) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem l₀ (s : Memory.State),
      l₀ + rem ≤ totalLocalCoordsWhp n_max →
      iterationSafe fillLocStateInnerStepProg FillLocStateInnerPre w
        (rt, (b, cnt)) rem l₀ s := by
  intro rt rem
  induction rem with
  | zero => intro _ _ _; exact trivial
  | succ rem ih =>
    intro l₀ s hle
    have hl_lt : l₀ < totalLocalCoordsWhp n_max := by omega
    refine ⟨⟨⟨c, U, V, w, n_max, henv, rfl⟩, hb, hl_lt⟩, ?_⟩
    rw [clientState_width, clientResult_width]
    have hr1 : (Memory.spec 0).clientResult s
        (fillLocStateInnerStepProg ((rt, (b, cnt)), l₀)) = l₀ + 1 := by
      unfold fillLocStateInnerStepProg; dsimp only; simp only [pure_bind]
      rw [clientResult_bind]
      have hcs_r : (Memory.spec 0).clientState s (Memory.read (hlBase rt)) = s := rfl
      rw [hcs_r]
      split_ifs <;> (rw [clientResult_bind]; rfl)
    rw [hr1]
    exact ih (l₀ + 1) _ (by omega)

private theorem fillLocStateInnerLoop_spec {c U V w n_max base b cnt : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) :
    let rt := mkHealRt c U V w n_max base
    let M := numBucketsWhp n_max
    let totalLoc := totalLocalCoordsWhp n_max
    ∀ rem l₀ (s : Memory.State),
      l₀ + rem ≤ totalLoc →
      (∀ loc < l₀,
        readPacked (base + offLocState c U V w n_max) 2 w s.mem (b * totalLoc + loc) =
          if loc < cnt then 1 else 0) →
      let prog := fillLocStateInnerLoopProg (((rt, (b, cnt)), l₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ loc < l₀ + rem,
        readPacked (base + offLocState c U V w n_max) 2 w s'.mem (b * totalLoc + loc) =
          if loc < cnt then 1 else 0) ∧
      (∀ b' < M, b' ≠ b → ∀ loc < totalLoc,
        readPacked (base + offLocState c U V w n_max) 2 w s'.mem (b' * totalLoc + loc) =
          readPacked (base + offLocState c U V w n_max) 2 w s.mem (b' * totalLoc + loc)) ∧
      (∀ a, (a < base + offLocState c U V w n_max ∨ base + offBktMeta c U V w n_max ≤ a) →
        s'.mem a = s.mem a) := by
  intro rt M totalLoc rem
  have hw := henv.2.1
  have hls_end : offLocState c U V w n_max +
      packedWords (M * totalLoc) 2 w = offBktMeta c U V w n_max := rfl
  induction rem with
  | zero =>
    intro l₀ s _ hprev
    unfold fillLocStateInnerLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    intro l₀ s hle hprev
    have hl_lt : l₀ < totalLoc := by omega
    have hidx := mul_add_lt_mul_bound hb hl_lt
    set vVal := if l₀ < cnt then 1 else 0
    have hv_pow : vVal < 2 ^ 2 := by dsimp only [vVal]; split_ifs <;> decide
    obtain ⟨hwl1_st, _, hwl1_vp⟩ := writeLocStateGenProg_spec (b := b) (loc := l₀) (val := 1)
      henv hb hl_lt (s := s)
    obtain ⟨hwl0_st, _, hwl0_vp⟩ := writeLocStateGenProg_spec (b := b) (loc := l₀) (val := 0)
      henv hb hl_lt (s := s)
    set p1 := fillLocStateInnerStepProg ((rt, (b, cnt)), l₀)
    set m1 := writePacked (base + offLocState c U V w n_max) 2 w s.mem (b * totalLoc + l₀) vVal
    have hbase_lt : base < base + largeSpaceWhp c U V w n_max := by
      have : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
      omega
    have hcs_r : (Memory.spec 0).clientState s (Memory.read base) = s := rfl
    have hs1 : (Memory.spec 0).clientState s p1 = { mem := m1, frontier := s.frontier } ∧
        (Memory.spec 0).clientResult s p1 = l₀ + 1 ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold fillLocStateInnerStepProg; dsimp only [rt, mkHealRt, hlBase, hlW,
        hlTotalLoc, hlOffLs]
      simp only [pure_bind]
      by_cases hlc : l₀ < cnt
      · simp only [hlc, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, hcs_r,
            clientState_bind, hwl1_st]
          dsimp only [m1, vVal]; simp only [hlc, ↓reduceIte]; rfl
        · rw [clientResult_bind, hcs_r,
            clientResult_bind]; rfl
        · refine validProg_bind (validProg_read hbase_lt) ?_; rw [hcs_r]
          exact validProg_bind hwl1_vp (validProg_pure _)
      · simp only [hlc, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, hcs_r,
            clientState_bind, hwl0_st]
          dsimp only [m1, vVal]; simp only [hlc, ↓reduceIte]; rfl
        · rw [clientResult_bind, hcs_r,
            clientResult_bind]; rfl
        · refine validProg_bind (validProg_read hbase_lt) ?_; rw [hcs_r]
          exact validProg_bind hwl0_vp (validProg_pure _)
    set s1 : Memory.State := { mem := m1, frontier := s.frontier }
    have hprev1 : ∀ loc < l₀ + 1,
        readPacked (base + offLocState c U V w n_max) 2 w s1.mem (b * totalLoc + loc) =
          if loc < cnt then 1 else 0 := by
      intro loc hloc
      dsimp only [s1, m1]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hloc with hlt | rfl
      · rw [readPacked_writePacked_of_ne hw _ (by omega)]; exact hprev loc hlt
      · exact readPacked_writePacked_self _ _ _ _ _ hv_pow
    obtain ⟨hf_r, hvp_r, hp_r, hoth_r, hout_r⟩ := ih (l₀ + 1) s1 (by omega) hprev1
    have hadd : l₀ + 1 + rem = l₀ + (rem + 1) := by omega
    rw [hadd] at hp_r
    unfold fillLocStateInnerLoopProg at hf_r hvp_r hp_r hoth_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hf_r
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro loc hloc
      rw [clientState_bind, hs1.1, hs1.2.1]; exact hp_r loc hloc
    · intro b' hb' hne loc hloc
      rw [clientState_bind, hs1.1, hs1.2.1, hoth_r b' hb' hne loc hloc]
      have hne_idx : b' * totalLoc + loc ≠ b * totalLoc + l₀ := by
        intro heq
        have htl_pos : 0 < totalLoc := by omega
        have hd1 : (b' * totalLoc + loc) / totalLoc = b' := by
          rw [mul_comm, Nat.mul_add_div htl_pos, Nat.div_eq_of_lt hloc, Nat.add_zero]
        have hd2 : (b * totalLoc + l₀) / totalLoc = b := by
          rw [mul_comm, Nat.mul_add_div htl_pos, Nat.div_eq_of_lt hl_lt, Nat.add_zero]
        exact hne (by rw [← hd1, heq, hd2])
      exact readPacked_writePacked_of_ne hw _ hne_idx _
    · intro a ha
      rw [clientState_bind, hs1.1, hs1.2.1, hout_r a ha]
      dsimp only [M, totalLoc] at hidx hls_end
      exact writePacked_outside hw _ hidx _ (by omega)

@[irreducible] private def fillLocStateOuterStepProg : HealRt × ℕ → Memory.Prog ℕ
  | (rt, b_in) => do
    let b ← pure b_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let b1 ← pure (b + one_v)
    let lo ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b)
    let hi ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b1)
    if lo ≤ hi then
      let cnt ← pure (hi - lo)
      let _ ← fillLocStateInnerLoopProg (((rt, (b, cnt)), zero_v), hlTotalLoc rt)
      pure b1
    else
      let _ ← fillLocStateInnerLoopProg (((rt, (b, zero_v)), zero_v), hlTotalLoc rt)
      pure b1

private theorem memoryCost_fillLocStateOuterStep_pos (d : HealRt × ℕ) (s : Memory.State) :
    0 < memoryCost (fillLocStateOuterStepProg d) s := by
  rcases d with ⟨rt, b⟩
  unfold fillLocStateOuterStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

private theorem realizes_fillLocStateOuterStep :
    Realizes .exact fillLocStateOuterStepProg
      (WordEncoding.encode (α := HealRt × ℕ))
      (WordEncoding.encode (α := ℕ))
      FillBackPtrOuterPre
      (fun _ _ => 0) := by
  unfold fillLocStateOuterStepProg
  have hrp := realizes_readPackedGen
  have hil := realizes_fillLocStateInnerLoop
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨rt, b⟩
    dsimp only [FillBackPtrOuterPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, heq_rt⟩, hb_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨hM_lt, _, _, _, h2T, _, _, hgk⟩ := hl_bounds henv
    have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.1
    dsimp only [mkHealRt, hlBase, hlW, hlM, hlTotalLoc, hlGBits, hlOffFb] at *
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact to_true_exists (henv.packed_safe_of_le hgk (idx := b) (by omega) hseg)
    | exact to_true_exists (henv.packed_safe_of_le hgk (idx := b + 1) (by omega) hseg)
    | exact fillLocStateInnerLoop_safe henv hb_lt (totalLocalCoordsWhp n_max) 0 s (by omega)
  )

@[irreducible] private def fillLocStateOuterLoopProg : (HealRt × ℕ) × ℕ → Memory.Prog ℕ
  | ((rt, b₀), rem) => iterate fillLocStateOuterStepProg rt rem b₀

private theorem realizes_fillLocStateOuterLoop :
    Realizes .exact fillLocStateOuterLoopProg
      (WordEncoding.encode (α := (HealRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((rt, b₀), rem) s =>
        iterationSafe fillLocStateOuterStepProg FillBackPtrOuterPre w rt rem b₀ s)
      (fun _ _ => 0) := by
  unfold fillLocStateOuterLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt))
    (WordEncoding.encode (α := ℕ))
    realizes_fillLocStateOuterStep
    memoryCost_fillLocStateOuterStep_pos

private theorem fillLocStateOuterLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ numBucketsWhp n_max →
      iterationSafe fillLocStateOuterStepProg FillBackPtrOuterPre w rt rem b₀ s := by
  intro rt rem
  induction rem with
  | zero => intro _ _ _; exact trivial
  | succ rem ih =>
    intro b₀ s hle
    refine ⟨⟨⟨c, U, V, w, n_max, henv, rfl⟩, by dsimp [rt, mkHealRt, hlM]; omega⟩, ?_⟩
    rw [clientState_width, clientResult_width]
    have hr1 : (Memory.spec 0).clientResult s (fillLocStateOuterStepProg (rt, b₀)) = b₀ + 1 := by
      unfold fillLocStateOuterStepProg; dsimp only [readPackedGenProg]; simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedProg,
        clientResult_bind, clientState_readPackedProg]
      split_ifs <;> (rw [clientResult_bind]; rfl)
    rw [hr1]
    exact ih (b₀ + 1) _ (by omega)

private theorem fillLocStateOuterLoop_spec {c U V w n_max base : ℕ} {fbStart : ℕ → ℕ}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hfb_adj : ∀ b < numBucketsWhp n_max, fbStart b ≤ fbStart (b + 1))
    (hfb_mem : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s₀.mem x = fbStart x) :
    let rt := mkHealRt c U V w n_max base
    let M := numBucketsWhp n_max
    let totalLoc := totalLocalCoordsWhp n_max
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ M →
      (∀ b < b₀, ∀ loc < totalLoc,
        readPacked (base + offLocState c U V w n_max) 2 w s.mem (b * totalLoc + loc) =
          if loc < fbStart (b + 1) - fbStart b then 1 else 0) →
      (∀ a, (a < base + offLocState c U V w n_max ∨ base + offBktMeta c U V w n_max ≤ a) →
        s.mem a = s₀.mem a) →
      let prog := fillLocStateOuterLoopProg ((rt, b₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ b < b₀ + rem, ∀ loc < totalLoc,
        readPacked (base + offLocState c U V w n_max) 2 w s'.mem (b * totalLoc + loc) =
          if loc < fbStart (b + 1) - fbStart b then 1 else 0) ∧
      (∀ a, (a < base + offLocState c U V w n_max ∨ base + offBktMeta c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) := by
  intro rt M totalLoc rem
  have hw := henv.2.1
  have hseg := (WhpLargeEnv.seg_end_le c U V w n_max).2.2.2.2.2.1
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg _
  have hbm_le_fb : offBktMeta c U V w n_max ≤ offFbStart c U V w n_max := by
    unfold offFbStart; exact Nat.le_add_right _ _
  induction rem with
  | zero =>
    intro b₀ s _ hprev hout
    unfold fillLocStateOuterLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, hout⟩
  | succ rem ih =>
    intro b₀ s hle hprev hout
    have hb_lt : b₀ < M := by omega
    have hfb_s : ∀ x ≤ M,
        readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem x = fbStart x :=
      fun x hx => (readPacked_congr hw (fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega)))
        (Nat.lt_succ_of_le hx)).trans (hfb_mem x hx)
    have hlo_hi := hfb_adj b₀ hb_lt
    set cnt := fbStart (b₀ + 1) - fbStart b₀
    obtain ⟨hin_f, hin_vp, hin_l, hin_oth, hin_out⟩ := fillLocStateInnerLoop_spec
      (b := b₀) (cnt := cnt) henv hb_lt totalLoc 0 s (by omega)
      (fun _ h => absurd h (Nat.not_lt_zero _))
    rw [Nat.zero_add] at hin_l
    set s_in := (Memory.spec 0).clientState s
      (fillLocStateInnerLoopProg (((rt, (b₀, cnt)), 0), totalLoc))
    set p1 := fillLocStateOuterStepProg (rt, b₀)
    have hs1 : (Memory.spec 0).clientState s p1 = s_in ∧
        (Memory.spec 0).clientResult s p1 = b₀ + 1 ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold fillLocStateOuterStepProg; dsimp only [rt, mkHealRt, hlBase, hlW,
        hlTotalLoc, hlGBits, hlOffFb, readPackedGenProg]
      simp only [pure_bind]
      refine ⟨?_, ?_, ?_⟩
      · rw [clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
          clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt]
        simp only [hlo_hi, ↓reduceIte]
        rw [clientState_bind]; rfl
      · rw [clientResult_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
          clientResult_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt]
        simp only [hlo_hi, ↓reduceIte]
        rw [clientResult_bind]; rfl
      · refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
        rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s b₀ hb_lt.le]
        refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
        rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt]
        simp only [hlo_hi, ↓reduceIte]
        dsimp only [rt, mkHealRt] at hin_vp
        exact validProg_bind hin_vp (validProg_pure _)
    have hprev1 : ∀ b < b₀ + 1, ∀ loc < totalLoc,
        readPacked (base + offLocState c U V w n_max) 2 w s_in.mem (b * totalLoc + loc) =
          if loc < fbStart (b + 1) - fbStart b then 1 else 0 := by
      intro b hb loc hloc
      rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hlt | rfl
      · rw [hin_oth b (hlt.trans hb_lt) (by omega) loc hloc]; exact hprev b hlt loc hloc
      · exact hin_l loc hloc
    have hout1 : ∀ a, (a < base + offLocState c U V w n_max ∨
        base + offBktMeta c U V w n_max ≤ a) → s_in.mem a = s₀.mem a :=
      fun a ha => (hin_out a ha).trans (hout a ha)
    obtain ⟨hf_r, hvp_r, hp_r, hout_r⟩ := ih (b₀ + 1) s_in (by omega) hprev1 hout1
    have hadd : b₀ + 1 + rem = b₀ + (rem + 1) := by omega
    rw [hadd] at hp_r
    unfold fillLocStateOuterLoopProg at hf_r hvp_r hp_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hf_r.trans hin_f
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro b hb loc hloc
      rw [clientState_bind, hs1.1, hs1.2.1]; exact hp_r b hb loc hloc
    · intro a ha; rw [clientState_bind, hs1.1, hs1.2.1]; exact hout_r a ha


/-! ### Phase E1: `resetAllSlicesLoopProg` (reset all `3 * M` slices to `zeroBTreeSlice`) -/

@[irreducible] private def resetAllSlicesStepProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, base_in), sIdx_in) => do
    let base ← pure base_in
    let sIdx ← pure sIdx_in
    let one_v ← pure 1
    resetBTreeSliceGenProg ((cp, base), sIdx)
    pure (sIdx + one_v)

private theorem memoryCost_resetAllSlicesStep_pos
    (d : (WhpCoreParams × ℕ) × ℕ) (s : Memory.State) :
    0 < memoryCost (resetAllSlicesStepProg d) s := by
  rcases d with ⟨⟨cp, base⟩, sIdx⟩
  unfold resetAllSlicesStepProg resetBTreeSliceGenProg writePackedGenProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 4 + (4 + 0)
  omega

private def ResetAllSlicesPre (w : ℕ) (d : (WhpCoreParams × ℕ) × ℕ) (_s : Memory.State) : Prop :=
  WhpLargeEnvGen w d.1.1 d.1.2 ∧ d.2 < 3 * wpM d.1.1

private theorem realizes_resetAllSlicesStep :
    Realizes .exact resetAllSlicesStepProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      ResetAllSlicesPre
      (fun _ _ => 0) := by
  unfold resetAllSlicesStepProg
  have hrs := realizes_resetBTreeSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, sIdx⟩
    dsimp only [ResetAllSlicesPre] at h
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hsIdx⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    simp only [wp_large_M hth] at hsIdx
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (simp only [wp_large_M hth]; exact hsIdx)
    | exact henv.fits_of_le_n_max (by omega)
  )

@[irreducible] private def resetAllSlicesLoopProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, s₀), rem) => iterate resetAllSlicesStepProg cfg rem s₀

private theorem realizes_resetAllSlicesLoop :
    Realizes .exact resetAllSlicesLoopProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, s₀), rem) s =>
        iterationSafe resetAllSlicesStepProg ResetAllSlicesPre w cfg rem s₀ s)
      (fun _ _ => 0) := by
  unfold resetAllSlicesLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := WhpCoreParams × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizes_resetAllSlicesStep
    memoryCost_resetAllSlicesStep_pos

private theorem resetAllSlicesLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let cp := mkWhpCoreParams c U V w n_max
    ∀ rem s₀ (s : Memory.State),
      s₀ + rem ≤ 3 * numBucketsWhp n_max →
      iterationSafe resetAllSlicesStepProg ResetAllSlicesPre w (cp, base) rem s₀ s := by
  intro cp rem
  have hth := henv.2.2.2.1
  induction rem with
  | zero => intro _ _ _; exact trivial
  | succ rem ih =>
    intro s₀ s hle
    refine ⟨⟨⟨c, U, V, w, n_max, henv, rfl⟩, by dsimp only [cp]; rw [wp_large_M hth]; omega⟩, ?_⟩
    rw [clientState_width, clientResult_width]
    have hr1 : (Memory.spec 0).clientResult s (resetAllSlicesStepProg ((cp, base), s₀)) =
        s₀ + 1 := by
      unfold resetAllSlicesStepProg
      simp only [pure_bind]
      rw [clientResult_bind]; rfl
    rw [hr1]
    exact ih (s₀ + 1) _ (by omega)

private theorem resetAllSlicesLoop_spec {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let cp := mkWhpCoreParams c U V w n_max
    let M := numBucketsWhp n_max
    ∀ rem s₀ (s : Memory.State),
      s₀ + rem ≤ 3 * M →
      (∀ sIdx < s₀, BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice s.mem) →
      let prog := resetAllSlicesLoopProg (((cp, base), s₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ sIdx < s₀ + rem, BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice s'.mem) ∧
      (∀ idx < 16 * M, idx % 16 = 1 →
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx) ∧
      (∀ a, (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
        s'.mem a = s.mem a) := by
  intro cp M rem
  have hth := henv.2.2.2.1
  have hw := henv.2.1
  have hnU := henv.2.2.2.2.1
  have hU := henv.2.2.2.2.2.1
  induction rem with
  | zero =>
    intro s₀ s _ hprev
    unfold resetAllSlicesLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, fun _ _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    intro s₀ s hle hprev
    have hs_lt : s₀ < 3 * M := by omega
    obtain ⟨hfr1, _, hvp1, hrep1, hoth1, hbm1, hout1⟩ :=
      resetBTreeSliceGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max)
        (base := base) hth hw hnU hU hs_lt (s := s)
    set s1 := (Memory.spec 0).clientState s (resetBTreeSliceGenProg ((cp, base), s₀))
    set p1 := resetAllSlicesStepProg ((cp, base), s₀)
    have hs1_eq : (Memory.spec 0).clientState s p1 = s1 ∧
        (Memory.spec 0).clientResult s p1 = s₀ + 1 ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold resetAllSlicesStepProg; simp only [pure_bind]
      exact ⟨by rw [clientState_bind]; rfl,
        by rw [clientResult_bind]; rfl,
        validProg_bind hvp1 (validProg_pure _)⟩
    have hprev1 : ∀ sIdx < s₀ + 1,
        BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice s1.mem := by
      intro sIdx hsIdx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hsIdx with hlt | rfl
      · exact hoth1 sIdx (hlt.trans hs_lt) (by omega) zeroBTreeSlice (hprev sIdx hlt)
      · exact hrep1
    obtain ⟨hfr_r, hvp_r, hrep_r, hbm_r, hout_r⟩ := ih (s₀ + 1) s1 (by omega) hprev1
    have hadd : s₀ + 1 + rem = s₀ + (rem + 1) := by omega
    rw [hadd] at hrep_r
    unfold resetAllSlicesLoopProg at hfr_r hvp_r hrep_r hbm_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1_eq.1, hs1_eq.2.1]; exact hfr_r.trans hfr1
    · refine validProg_bind hs1_eq.2.2 ?_; rw [hs1_eq.1, hs1_eq.2.1]; exact hvp_r
    · intro sIdx hsIdx
      rw [clientState_bind, hs1_eq.1, hs1_eq.2.1]; exact hrep_r sIdx hsIdx
    · intro idx hidx hmod
      rw [clientState_bind, hs1_eq.1, hs1_eq.2.1, hbm_r idx hidx hmod]
      have hrole : s₀ % 3 < 3 := Nat.mod_lt _ (by decide)
      exact hbm1 idx hidx (by omega) (by omega)
    · intro a ha
      rw [clientState_bind, hs1_eq.1, hs1_eq.2.1, hout_r a ha]
      exact hout1 a ha

/-! ### Phase E2: `buildAllBucketsOuterLoopProg` (populate live `BTreeSlice` `3 * b`) -/

@[irreducible] private def readHealSlotQuotProg :
    (HealRt × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((rt, (offQ_in, qBits_in)), (b_in, loc_in)) => do
    let offQ ← pure offQ_in
    let qBits ← pure qBits_in
    let b ← pure b_in
    let loc ← pure loc_in
    let zero_v ← pure 0
    if loc < hlCF rt then
      let p ← pure (b * hlCF rt + loc)
      readPackedGenProg (((hlBase rt, offQ), (qBits, hlW rt)), p)
    else
      let k ← pure (loc - hlCF rt)
      if k < hlCB rt then
        let idxBp ← pure (b * hlCB rt + k)
        let bpVal ← readPackedGenProg (((hlBase rt, hlOffBp rt), (hlGBits rt, hlW rt)), idxBp)
        if bpVal < hlPoolSize rt then
          let ft ← pure (hlM rt * hlCF rt)
          let p ← pure (ft + bpVal)
          readPackedGenProg (((hlBase rt, offQ), (qBits, hlW rt)), p)
        else
          pure zero_v
      else
        pure zero_v

private def ReadHealSlotQuotPre (w : ℕ)
    (d : (HealRt × (ℕ × ℕ)) × (ℕ × ℕ)) (_s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max,
    WhpLargeEnv c U V w₀ n_max w (hlBase d.1.1) ∧
    d.1.1 = mkHealRt c U V w₀ n_max (hlBase d.1.1) ∧
    d.1.2.1 = offQuotWhp c w₀ n_max ∧
    d.1.2.2 = quotBitsWhp U n_max ∧
    d.2.1 < numBucketsWhp n_max

private theorem realizes_readHealSlotQuot :
    Realizes .exact readHealSlotQuotProg
      (WordEncoding.encode (α := (HealRt × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      ReadHealSlotQuotPre
      (fun _ _ => 0) := by
  unfold readHealSlotQuotProg
  have hrp := realizes_readPackedGen
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨rt, offQ, qBits⟩, b, loc⟩
    dsimp only [ReadHealSlotQuotPre] at h
    obtain ⟨c, U, V, w₀, n_max, henv, heq_rt, rfl, rfl, hb_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    generalize hlBase rt = base at henv heq_rt
    subst heq_rt
    obtain ⟨_, _, hMcb, _, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := WhpLargeEnv.seg_end_le c U V w n_max
    have hMcf_le : numBucketsWhp n_max * capFrontWhp n_max ≤ n_max :=
      (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)
    have hMcf_ps : numBucketsWhp n_max * capFrontWhp n_max + poolSizeWhp n_max ≤ n_max := by
      unfold poolSizeWhp; omega
    have hqk : quotBitsWhp U n_max ≤ w :=
      (Nat.sub_le _ _).trans (keyBits_le_w henv.2.2.2.2.2.1)
    dsimp only [mkHealRt, hlBase, hlW, hlM, hlCF, hlCB, hlPoolSize, hlGBits, hlOffBp] at *
    simp only [hcs] at *
    first
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | (refine henv.fits_of_le_n_max ?_
       exact (mul_add_lt_mul_bound hb_lt (by assumption)).le.trans hMcf_le)
    | (refine henv.fits_of_le_n_max ?_
       exact (mul_add_lt_mul_bound hb_lt (by assumption)).le.trans hMcb)
    | (refine to_true_exists (henv.packed_safe_of_le hqk ?_ hseg.1)
       exact (mul_add_lt_mul_bound hb_lt (by assumption)).trans_le hMcf_le)
    | (refine to_true_exists (henv.packed_safe_of_le hgk ?_ hseg.2.2.2.2.2.2.1)
       exact mul_add_lt_mul_bound hb_lt (by assumption))
    | exact to_true_exists (henv.packed_safe_of_le hqk (by omega) hseg.1)
  )

private theorem readHealSlotQuotProg_spec {c U V w n_max base b loc : ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) :
    let rt := mkHealRt c U V w n_max base
    let prog := readHealSlotQuotProg ((rt, (offQuotWhp c w n_max, quotBitsWhp U n_max)), (b, loc))
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog < 2 ^ quotBitsWhp U n_max ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hw := henv.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hq_b : base + offQuotWhp c w n_max +
      packedWords n_max (quotBitsWhp U n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.1 _
  have hbp_b : base + offBackPtr c U V w n_max +
      packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.2.1 _
  have hMcf_le : numBucketsWhp n_max * capFrontWhp n_max ≤ n_max :=
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)
  dsimp only
  unfold readHealSlotQuotProg
  dsimp only [mkHealRt, hlBase, hlW, hlM, hlCF, hlCB, hlPoolSize, hlGBits, hlOffBp,
    readPackedGenProg]
  simp only [pure_bind]
  by_cases hcf : loc < capFrontWhp n_max
  · simp only [hcf, ↓reduceIte]
    have hp_lt : b * capFrontWhp n_max + loc < n_max :=
      (mul_add_lt_mul_bound hb hcf).trans_le hMcf_le
    exact ⟨clientState_readPackedProg _ _ _ _ _ _,
      (clientResult_readPackedProg _ _ _ _ _ _).symm ▸ readPacked_lt _ _ _ _ _,
      validProg_readPacked hw hp_lt hq_b⟩
  · simp only [hcf, ↓reduceIte]
    by_cases hk : loc - capFrontWhp n_max < capBackWhp n_max
    · simp only [hk, ↓reduceIte]
      have hidx_bp := mul_add_lt_mul_bound hb hk
      let bpVal := readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s.mem
        (b * capBackWhp n_max + (loc - capFrontWhp n_max))
      by_cases hbp : bpVal < poolSizeWhp n_max
      · have hp_lt : numBucketsWhp n_max * capFrontWhp n_max + bpVal < n_max := by
          unfold poolSizeWhp at hbp; omega
        refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, clientState_readPackedProg,
            clientResult_readPackedProg, ite_eq_left hbp]
          exact clientState_readPackedProg _ _ _ _ _ _
        · rw [clientResult_bind, clientState_readPackedProg,
            clientResult_readPackedProg, ite_eq_left hbp, clientResult_readPackedProg]
          exact readPacked_lt _ _ _ _ _
        · refine validProg_bind (validProg_readPacked hw hidx_bp hbp_b) ?_
          rw [clientState_readPackedProg, clientResult_readPackedProg, ite_eq_left hbp]
          exact validProg_readPacked hw hp_lt hq_b
      · refine ⟨?_, ?_, ?_⟩
        · rw [clientState_bind, clientState_readPackedProg,
            clientResult_readPackedProg, ite_eq_right hbp]; rfl
        · rw [clientResult_bind, clientState_readPackedProg,
            clientResult_readPackedProg, ite_eq_right hbp]
          exact Nat.two_pow_pos _
        · refine validProg_bind (validProg_readPacked hw hidx_bp hbp_b) ?_
          rw [clientState_readPackedProg, clientResult_readPackedProg, ite_eq_right hbp]
          exact validProg_pure _
    · simp only [hk, ↓reduceIte]
      exact ⟨rfl, Nat.two_pow_pos _, validProg_pure _⟩

private theorem readHealSlotQuotProg_eq {c U V w n_max base b loc : ℕ}
    {qArr : ℕ → ℕ} {backPtr : ℕ → ℕ → ℕ} {s : Memory.State}
    (hb : b < numBucketsWhp n_max)
    (hq_mem : ∀ i < n_max,
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem i = qArr i)
    (hbp_mem : ∀ k < capBackWhp n_max,
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s.mem
        (b * capBackWhp n_max + k) = backPtr b k)
    (hk_cb : loc - capFrontWhp n_max < capBackWhp n_max)
    (hbp_ps : capFrontWhp n_max ≤ loc → backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max) :
    let rt := mkHealRt c U V w n_max base
    let prog := readHealSlotQuotProg ((rt, (offQuotWhp c w n_max, quotBitsWhp U n_max)), (b, loc))
    let cf := capFrontWhp n_max
    let p := if loc < cf then b * cf + loc else numBucketsWhp n_max * cf + backPtr b (loc - cf)
    (Memory.spec 0).clientResult s prog = qArr p := by
  have hMcf_le : numBucketsWhp n_max * capFrontWhp n_max ≤ n_max :=
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)
  dsimp only
  unfold readHealSlotQuotProg
  dsimp only [mkHealRt, hlBase, hlW, hlM, hlCF, hlCB, hlPoolSize, hlGBits, hlOffBp,
    readPackedGenProg]
  simp only [pure_bind]
  by_cases hcf : loc < capFrontWhp n_max
  · simp only [hcf, ↓reduceIte, clientResult_readPackedProg]
    exact hq_mem _ ((mul_add_lt_mul_bound hb hcf).trans_le hMcf_le)
  · have hge : capFrontWhp n_max ≤ loc := Nat.le_of_not_lt hcf
    have hbp_lt := hbp_ps hge
    have hp_lt : numBucketsWhp n_max * capFrontWhp n_max + backPtr b (loc - capFrontWhp n_max) <
        n_max := by
      unfold poolSizeWhp at hbp_lt; omega
    simp only [hcf, hk_cb, ↓reduceIte]
    rw [clientResult_bind, clientState_readPackedProg,
      clientResult_readPackedProg, hbp_mem _ hk_cb]
    simp only [hbp_lt, ↓reduceIte, clientResult_readPackedProg]
    exact hq_mem _ hp_lt

@[irreducible] private def buildBktSliceStepProg :
    (((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | ((((cp, base_in), (rt, hrt)), (b_in, salt_in)), loc_in) => do
    let base ← pure base_in
    let _ ← Memory.read base
    let b ← pure b_in
    let salt ← pure salt_in
    let loc ← pure loc_in
    let one_v ← pure 1
    let q ← readHealSlotQuotProg ((rt, (wpOffQuot cp, wpQuotBits cp)), (b, loc))
    let fp ← fpOfQuotRtProg (((hrt, salt), b), q)
    let sIdx ← pure (3 * b)
    btreeInsertGenProg ((((cp, base), sIdx), fp), loc)
    pure (loc + one_v)

private theorem memoryCost_buildBktSliceStep_pos
    (d : (((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    0 < memoryCost (buildBktSliceStepProg d) s := by
  rcases d with ⟨⟨⟨⟨cp, base⟩, rt, hrt⟩, b, salt⟩, loc⟩
  unfold buildBktSliceStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 1 + _
  omega

private def BuildBktSliceStepPre (w : ℕ)
    (d : (((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)) × ℕ)
    (s : Memory.State) : Prop :=
  let cp := d.1.1.1.1
  let base := d.1.1.1.2
  let rt := d.1.1.2.1
  let hrt := d.1.1.2.2
  let b := d.1.2.1
  let loc := d.2
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (sl : BTreeSlice) (mapFn : ℕ → Option ℕ),
    WhpLargeEnv c U V w₀ n_max w base ∧
    cp = mkWhpCoreParams c U V w₀ n_max ∧
    rt = mkHealRt c U V w₀ n_max base ∧
    hrt = mkHashRt c U w₀ n_max base ∧
    SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
    b < numBucketsWhp n_max ∧
    loc < totalLocalCoordsWhp n_max ∧
    BTreeSliceMemRep base c U V w₀ n_max (3 * b) sl s.mem ∧
    ValidWhpSlice n_max loc sl mapFn

private theorem realizes_buildBktSliceStep :
    Realizes .exact buildBktSliceStepProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      BuildBktSliceStepPre
      (fun _ _ => 0) := by
  unfold buildBktSliceStepProg
  have hrq := realizes_readHealSlotQuot
  have hfp := realizes_fpOfQuotRt
  have hbi := realizes_btreeInsertGen
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, rt, hrt⟩, b, salt⟩, loc⟩
    dsimp only [BuildBktSliceStepPre] at h
    obtain ⟨c, U, V, w₀, n_max, θ, sl, mapFn, henv, rfl, rfl, rfl, hseed, hb_lt, hloc_lt,
      hrep, hv⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max hth
    have htot_n := (large_bounds_lt_n_max hth).2.2.1
    have htot3 := @totalLocalCoordsWhp_le_three_mul n_max
    obtain ⟨hrq_st, hrq_lt, _⟩ := readHealSlotQuotProg_spec (b := b) (loc := loc) henv hb_lt
      (s := s)
    let qVal := (Memory.spec 0).clientResult s
      (readHealSlotQuotProg
        ((mkHealRt c U V w n_max base, (offQuotWhp c w n_max, quotBitsWhp U n_max)), (b, loc)))
    obtain ⟨hfp_st, hfp_res, _, _⟩ := fpOfQuotRtProg_spec (salt := salt) (b := b) (q := qVal)
      henv hseed (s := s)
    have hfp_lt : (Memory.spec 0).clientResult s
        (fpOfQuotRtProg (((mkHashRt c U w n_max base, salt), b), qVal)) < 2 ^ fpBitsWhp n_max := by
      rw [hfp_res]
      split_ifs with hs hu
      · exact fpHash_lt c U n_max θ.2 ⟨salt, hs⟩ ⟨_, hu⟩
      · exact Nat.two_pow_pos _
      · exact Nat.two_pow_pos _
    have hloc_val : loc < 2 ^ valLaneBitsWhp n_max := by rw [two_pow_valLaneBitsWhp]; omega
    dsimp only [qVal] at hfp_st hfp_lt
    simp only [hcs_r, wp_large_offQuot hth, wp_large_quotBits hth] at *
    simp only [hrq_st] at *
    simp only [hfp_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl, rfl, rfl, hb_lt⟩
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed, hrq_lt⟩
    | exact ⟨c, U, V, w, n_max, loc, sl, mapFn, henv, rfl, by omega, by omega, hrep, hv,
        hfp_lt, hloc_val⟩
  )

@[irreducible] private def buildBktSliceLoopProg :
    ((((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, l₀), rem) => iterate buildBktSliceStepProg cfg rem l₀

private theorem realizes_buildBktSliceLoop :
    Realizes .exact buildBktSliceLoopProg
      (WordEncoding.encode
        (α := ((((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, l₀), rem) s =>
        iterationSafe buildBktSliceStepProg BuildBktSliceStepPre w cfg rem l₀ s)
      (fun _ _ => 0) := by
  unfold buildBktSliceLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × (HealRt × HashRt)) × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ))
    realizes_buildBktSliceStep
    memoryCost_buildBktSliceStep_pos

private theorem buildBktSliceLoop_safe {c U V w n_max base b salt : ℕ}
    {θ : SeedWhp c U n_max}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) :
    let cp := mkWhpCoreParams c U V w n_max
    let rt := mkHealRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    ∀ rem l₀ (sl : BTreeSlice) (mapFn : ℕ → Option ℕ) (s : Memory.State),
      l₀ + rem ≤ totalLocalCoordsWhp n_max →
      SeedWhpMemRep base c U w n_max θ s.mem →
      BTreeSliceMemRep base c U V w n_max (3 * b) sl s.mem →
      ValidWhpSlice n_max l₀ sl mapFn →
      iterationSafe buildBktSliceStepProg BuildBktSliceStepPre w
        (((cp, base), (rt, hrt)), (b, salt)) rem l₀ s := by
  intro cp rt hrt rem
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  have htot3 := @totalLocalCoordsWhp_le_three_mul n_max
  have hq_bm : offQuotWhp c w n_max ≤ offBktMeta c U V w n_max := by
    unfold offBktMeta offLocState offPermAct offValWhp; omega
  induction rem with
  | zero => intro _ _ _ _ _ _ _ _; exact trivial
  | succ rem ih =>
    intro l₀ sl mapFn s hle hseed hrep hv
    have hl_lt : l₀ < totalLocalCoordsWhp n_max := by omega
    have hpre : BuildBktSliceStepPre w ((((cp, base), (rt, hrt)), (b, salt)), l₀) s :=
      ⟨c, U, V, w, n_max, θ, sl, mapFn, henv, rfl, rfl, rfl, hseed, hb, hl_lt, hrep, hv⟩
    refine ⟨hpre, ?_⟩
    rw [clientState_width, clientResult_width]
    obtain ⟨hrq_st, _, _⟩ := readHealSlotQuotProg_spec (b := b) (loc := l₀) henv hb (s := s)
    let qVal := (Memory.spec 0).clientResult s
      (readHealSlotQuotProg ((rt, (offQuotWhp c w n_max, quotBitsWhp U n_max)), (b, l₀)))
    obtain ⟨hfp_st, hfp_res, _, _⟩ := fpOfQuotRtProg_spec (salt := salt) (b := b) (q := qVal)
      henv hseed (s := s)
    let fpVal := (Memory.spec 0).clientResult s (fpOfQuotRtProg (((hrt, salt), b), qVal))
    have hfp_lt : fpVal < 2 ^ fpBitsWhp n_max := by
      change (Memory.spec 0).clientResult s (fpOfQuotRtProg (((hrt, salt), b), qVal)) < _
      rw [hfp_res]
      split_ifs with hs hu
      · exact fpHash_lt c U n_max θ.2 ⟨salt, hs⟩ ⟨_, hu⟩
      · exact Nat.two_pow_pos _
      · exact Nat.two_pow_pos _
    have hl_val : l₀ < 2 ^ valLaneBitsWhp n_max := by rw [two_pow_valLaneBitsWhp]; omega
    obtain ⟨_, _, _, hrep', hv', _, _, hout'⟩ := btreeInsertGenProg_spec (sIdx := 3 * b)
      (insCount := l₀) (q := fpVal) (val := l₀) henv (by omega) (by omega) hrep hv hfp_lt hl_val
    set s' := (Memory.spec 0).clientState s (btreeInsertGenProg ((((cp, base), 3 * b), fpVal), l₀))
    set p1 := buildBktSliceStepProg ((((cp, base), (rt, hrt)), (b, salt)), l₀)
    have hcs_r : (Memory.spec 0).clientState s (Memory.read base) = s := rfl
    have hs1 : (Memory.spec 0).clientState s p1 = s' ∧
        (Memory.spec 0).clientResult s p1 = l₀ + 1 := by
      dsimp only [p1]; unfold buildBktSliceStepProg
      dsimp only [cp, rt, hrt] at hrq_st hfp_st s' ⊢
      simp only [pure_bind, wp_large_offQuot hth, wp_large_quotBits hth]
      refine ⟨?_, ?_⟩
      · rw [clientState_bind, hcs_r,
          clientState_bind, hrq_st,
          clientState_bind, hfp_st,
          clientState_bind]; rfl
      · rw [clientResult_bind, hcs_r,
          clientResult_bind, hrq_st,
          clientResult_bind, hfp_st,
          clientResult_bind]; rfl
    have hseed' : SeedWhpMemRep base c U w n_max θ s'.mem :=
      SeedWhpMemRep.congr_hash hw (fun a _ ha2 => (hout' a (Or.inl (by omega))).symm) hseed
    rw [hs1.1, hs1.2]
    exact ih (l₀ + 1) _ _ s' (by omega) hseed' hrep' hv'

private theorem buildBktSliceLoop_spec {c U V w n_max base b salt cnt : ℕ}
    {θ : SeedWhp c U n_max} {qArr : ℕ → ℕ} {backPtr : ℕ → ℕ → ℕ} {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hcnt_le : cnt ≤ totalLocalCoordsWhp n_max)
    (hback_cb : cnt - capFrontWhp n_max < capBackWhp n_max)
    (hbp_ps : ∀ k < cnt - capFrontWhp n_max, backPtr b k < poolSizeWhp n_max)
    (hseed₀ : SeedWhpMemRep base c U w n_max θ s₀.mem)
    (hq₀ : ∀ i < n_max,
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s₀.mem i = qArr i)
    (hbp₀ : ∀ k < capBackWhp n_max,
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s₀.mem
        (b * capBackWhp n_max + k) = backPtr b k) :
    let cp := mkWhpCoreParams c U V w n_max
    let rt := mkHealRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    ∀ rem l₀ (mapFn : ℕ → Option ℕ) (s : Memory.State),
      l₀ + rem ≤ cnt →
      BTreeSliceMemRep base c U V w n_max (3 * b)
        (buildBucketSlice c U n_max θ qArr backPtr b salt l₀) s.mem →
      ValidWhpSlice n_max l₀ (buildBucketSlice c U n_max θ qArr backPtr b salt l₀) mapFn →
      (∀ a, (a < base + offBktMeta c U V w n_max ∨
          (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
          base + offTrieChild0 c U V w n_max ≤ a) → s.mem a = s₀.mem a) →
      let prog := buildBktSliceLoopProg (((((cp, base), (rt, hrt)), (b, salt)), l₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      BTreeSliceMemRep base c U V w n_max (3 * b)
        (buildBucketSlice c U n_max θ qArr backPtr b salt (l₀ + rem)) s'.mem ∧
      (∀ sIdx' < 3 * numBucketsWhp n_max, sIdx' ≠ 3 * b → ∀ sl₂,
        BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s.mem →
        BTreeSliceMemRep base c U V w n_max sIdx' sl₂ s'.mem) ∧
      (∀ idx < 16 * numBucketsWhp n_max,
        idx ≠ 16 * b + 10 → idx ≠ 16 * b + 11 →
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem idx =
          readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem idx) ∧
      (∀ a, (a < base + offBktMeta c U V w n_max ∨
          (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
          base + offTrieChild0 c U V w n_max ≤ a) → s'.mem a = s₀.mem a) := by
  intro cp rt hrt rem
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  have htot3 := @totalLocalCoordsWhp_le_three_mul n_max
  have hbase_lt : base < base + largeSpaceWhp c U V w n_max := by
    have : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    omega
  have hq_bm : offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w ≤
      offBktMeta c U V w n_max := by
    have h1 : offValWhp c U w n_max =
      offQuotWhp c w n_max + packedWords n_max (quotBitsWhp U n_max) w := rfl
    unfold offBktMeta offLocState offPermAct; omega
  have hbp_bt : offFbStart c U V w n_max ≤ offBackPtr c U V w n_max ∧
      offBackPtr c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w ≤
      offBtMeta c U V w n_max := by
    have h1 : offBackAux c U V w n_max = offBackPtr c U V w n_max +
        packedWords (numBucketsWhp n_max * capBackWhp n_max) (globalPtrBits n_max) w := rfl
    refine ⟨by unfold offBackPtr; omega, ?_⟩
    unfold offBtMeta offPoolOwner offPoolFreeStack; omega
  induction rem with
  | zero =>
    intro l₀ _ s _ hrep _ hout
    unfold buildBktSliceLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hrep, fun _ _ _ _ hr => hr,
      fun _ _ _ _ => rfl, hout⟩
  | succ rem ih =>
    intro l₀ mapFn s hle hrep hv hout
    have hl_cnt : l₀ < cnt := by omega
    have hl_tot : l₀ < totalLocalCoordsWhp n_max := hl_cnt.trans_le hcnt_le
    have hseed_s : SeedWhpMemRep base c U w n_max θ s.mem :=
      SeedWhpMemRep.congr_hash hw (fun a _ ha2 => (hout a (Or.inl (by omega))).symm) hseed₀
    have hq_s : ∀ i < n_max,
        readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s.mem i = qArr i :=
      fun i hi => (readPacked_congr hw (hidx := hi) (fun a ⟨_,
        ha2⟩ => hout a (Or.inl (by omega)))).trans
        (hq₀ i hi)
    have hbp_s : ∀ k < capBackWhp n_max,
        readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s.mem
          (b * capBackWhp n_max + k) = backPtr b k := fun k hk =>
      (readPacked_congr hw (hidx := mul_add_lt_mul_bound hb hk)
        (fun a ⟨ha1, ha2⟩ => hout a (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans (hbp₀ k hk)
    obtain ⟨hrq_st, _, hrq_vp⟩ := readHealSlotQuotProg_spec (b := b) (loc := l₀) henv hb (s := s)
    have hrq_eq := readHealSlotQuotProg_eq (loc := l₀) hb hq_s hbp_s (by omega)
      (fun hge => hbp_ps _ (by omega))
    set p_loc := if l₀ < capFrontWhp n_max then b * capFrontWhp n_max + l₀
      else numBucketsWhp n_max * capFrontWhp n_max + backPtr b (l₀ - capFrontWhp n_max)
    obtain ⟨hfp_st, hfp_res, _, hfp_vp⟩ := fpOfQuotRtProg_spec (salt := salt) (b := b)
      (q := qArr p_loc) henv hseed_s (s := s)
    set kv_loc := feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b (qArr p_loc)
    set fp_loc :=
      if hs : salt < sMaxWhp c n_max then
        if hu : kv_loc < U then fpHash c U n_max θ.2 ⟨salt, hs⟩ ⟨kv_loc, hu⟩ else 0
      else 0
    have hfp_lt : fp_loc < 2 ^ fpBitsWhp n_max := by
      dsimp only [fp_loc]
      split_ifs with hs hu
      · exact fpHash_lt c U n_max θ.2 ⟨salt, hs⟩ ⟨kv_loc, hu⟩
      · exact Nat.two_pow_pos _
      · exact Nat.two_pow_pos _
    have hl_val : l₀ < 2 ^ valLaneBitsWhp n_max := by rw [two_pow_valLaneBitsWhp]; omega
    obtain ⟨hfr_bi, _, hvp_bi, hrep_bi, hv_bi, hoth_bi, hbm_bi, hout_bi⟩ :=
      btreeInsertGenProg_spec (sIdx := 3 * b) (insCount := l₀) (q := fp_loc) (val := l₀)
        henv (by omega) (by omega) hrep hv hfp_lt hl_val
    set s1 := (Memory.spec 0).clientState s
      (btreeInsertGenProg ((((cp, base), 3 * b), fp_loc), l₀))
    set p1 := buildBktSliceStepProg ((((cp, base), (rt, hrt)), (b, salt)), l₀)
    have hcs_r : (Memory.spec 0).clientState s (Memory.read base) = s := rfl
    have hs1 : (Memory.spec 0).clientState s p1 = s1 ∧
        (Memory.spec 0).clientResult s p1 = l₀ + 1 ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold buildBktSliceStepProg
      dsimp only [cp, rt, hrt] at hrq_st hrq_eq hrq_vp hfp_st hfp_res hfp_vp hvp_bi s1 ⊢
      simp only [pure_bind, wp_large_offQuot hth, wp_large_quotBits hth]
      refine ⟨?_, ?_, ?_⟩
      · rw [clientState_bind, hcs_r,
          clientState_bind, hrq_st, hrq_eq,
          clientState_bind, hfp_st, hfp_res,
          clientState_bind]; rfl
      · rw [clientResult_bind, hcs_r,
          clientResult_bind, hrq_st, hrq_eq,
          clientResult_bind, hfp_st, hfp_res,
          clientResult_bind]; rfl
      · refine validProg_bind (validProg_read hbase_lt) ?_; rw [hcs_r]
        refine validProg_bind hrq_vp ?_; rw [hrq_st, hrq_eq]
        refine validProg_bind hfp_vp ?_; rw [hfp_st, hfp_res]
        exact validProg_bind hvp_bi (validProg_pure _)
    have hout1 : ∀ a, (a < base + offBktMeta c U V w n_max ∨
        (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
        base + offTrieChild0 c U V w n_max ≤ a) → s1.mem a = s₀.mem a :=
      fun a ha => (hout_bi a ha).trans (hout a ha)
    obtain ⟨hfr_r, hvp_r, hrep_r, hoth_r, hbm_r, hout_r⟩ := ih (l₀ + 1)
      (Function.update mapFn fp_loc (some l₀)) s1 (by omega) hrep_bi hv_bi hout1
    have hadd : l₀ + 1 + rem = l₀ + (rem + 1) := by omega
    rw [hadd] at hrep_r
    unfold buildBktSliceLoopProg at hfr_r hvp_r hrep_r hoth_r hbm_r hout_r ⊢
    dsimp only [iterate]
    have hdiv3 : (3 * b) / 3 = b := by omega
    have hmod3 : (3 * b) % 3 = 0 := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hfr_r.trans hfr_bi
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hrep_r
    · intro sIdx' hsIdx' hne sl₂ hr₂
      rw [clientState_bind, hs1.1, hs1.2.1]
      exact hoth_r sIdx' hsIdx' hne sl₂ (hoth_bi sIdx' hsIdx' hne sl₂ hr₂)
    · intro idx hidx h10 h11
      rw [clientState_bind, hs1.1, hs1.2.1, hbm_r idx hidx h10 h11]
      exact hbm_bi idx hidx (by rw [hdiv3, hmod3]; omega) (by rw [hdiv3, hmod3]; omega)
    · intro a ha
      rw [clientState_bind, hs1.1, hs1.2.1]; exact hout_r a ha

@[irreducible] private def buildAllBucketsOuterStepProg :
    ((WhpCoreParams × ℕ) × (HealRt × HashRt)) × ℕ → Memory.Prog ℕ
  | (((cp, base_in), (rt, hrt)), b_in) => do
    let base ← pure base_in
    let b ← pure b_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let b1 ← pure (b + one_v)
    let lo ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b)
    let hi ← readPackedGenProg (((hlBase rt, hlOffFb rt), (hlGBits rt, hlW rt)), b1)
    let idxSalt ← pure (16 * b + 1)
    let salt ← readPackedGenProg (((hlBase rt, hlOffBm rt), (hlGBits rt, hlW rt)), idxSalt)
    if lo ≤ hi then
      let cnt ← pure (hi - lo)
      if cnt ≤ hlTotalLoc rt then
        let _ ← buildBktSliceLoopProg (((((cp, base), (rt, hrt)), (b, salt)), zero_v), cnt)
        pure b1
      else
        pure b1
    else
      pure b1

private theorem memoryCost_buildAllBucketsOuterStep_pos
    (d : ((WhpCoreParams × ℕ) × (HealRt × HashRt)) × ℕ) (s : Memory.State) :
    0 < memoryCost (buildAllBucketsOuterStepProg d) s := by
  rcases d with ⟨⟨⟨cp, base⟩, rt, hrt⟩, b⟩
  unfold buildAllBucketsOuterStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  change 0 < 2 + _
  omega

private def BuildAllBucketsOuterPre (w : ℕ)
    (d : ((WhpCoreParams × ℕ) × (HealRt × HashRt)) × ℕ)
    (s : Memory.State) : Prop :=
  let cp := d.1.1.1
  let base := d.1.1.2
  let rt := d.1.2.1
  let hrt := d.1.2.2
  let b := d.2
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max),
    WhpLargeEnv c U V w₀ n_max w base ∧
    cp = mkWhpCoreParams c U V w₀ n_max ∧
    rt = mkHealRt c U V w₀ n_max base ∧
    hrt = mkHashRt c U w₀ n_max base ∧
    SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
    b < numBucketsWhp n_max ∧
    (∀ sIdx < 3 * numBucketsWhp n_max, b ≤ sIdx / 3 →
      BTreeSliceMemRep base c U V w₀ n_max sIdx zeroBTreeSlice s.mem)

private theorem realizes_buildAllBucketsOuterStep :
    Realizes .exact buildAllBucketsOuterStepProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × (HealRt × HashRt)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      BuildAllBucketsOuterPre
      (fun _ _ => 0) := by
  unfold buildAllBucketsOuterStepProg
  have hrp := realizes_readPackedGen
  have hbs := realizes_buildBktSliceLoop
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, rt, hrt⟩, b⟩
    dsimp only [BuildAllBucketsOuterPre] at h
    obtain ⟨c, U, V, w₀, n_max, θ, henv, rfl, rfl, rfl, hseed, hb_lt, hz_rem⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    obtain ⟨hM_lt, h16M, _, _, _, _, _, hgk⟩ := hl_bounds henv
    have hseg := WhpLargeEnv.seg_end_le c U V w n_max
    have hrep3b : BTreeSliceMemRep base c U V w n_max (3 * b) zeroBTreeSlice s.mem :=
      hz_rem (3 * b) (by omega) (by omega)
    dsimp only [mkHealRt, hlBase, hlW, hlM, hlTotalLoc, hlGBits, hlOffBm, hlOffFb] at *
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | omega
    | exact henv.fits_of_le_n_max (by omega)
    | exact to_true_exists (henv.packed_safe_of_le hgk (idx := b) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists (henv.packed_safe_of_le hgk (idx := b + 1) (by omega) hseg.2.2.2.2.2.1)
    | exact to_true_exists (henv.bktMeta_safe (idx := 16 * b + 1) (by omega))
    | exact buildBktSliceLoop_safe henv hb_lt _ 0 zeroBTreeSlice (fun _ => none) s
        (by omega) hseed hrep3b (validWhpSlice_zero _ 0 _)
  )

@[irreducible] private def buildAllBucketsOuterLoopProg :
    (((WhpCoreParams × ℕ) × (HealRt × HashRt)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, b₀), rem) => iterate buildAllBucketsOuterStepProg cfg rem b₀

private theorem realizes_buildAllBucketsOuterLoop :
    Realizes .exact buildAllBucketsOuterLoopProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × (HealRt × HashRt)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((cfg, b₀), rem) s =>
        iterationSafe buildAllBucketsOuterStepProg BuildAllBucketsOuterPre w cfg rem b₀ s)
      (fun _ _ => 0) := by
  unfold buildAllBucketsOuterLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := (WhpCoreParams × ℕ) × (HealRt × HashRt)))
    (WordEncoding.encode (α := ℕ))
    realizes_buildAllBucketsOuterStep
    memoryCost_buildAllBucketsOuterStep_pos

private theorem buildAllBucketsOuterLoop_safe {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let cp := mkWhpCoreParams c U V w n_max
    let rt := mkHealRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ numBucketsWhp n_max →
      SeedWhpMemRep base c U w n_max θ s.mem →
      (∀ sIdx < 3 * numBucketsWhp n_max, b₀ ≤ sIdx / 3 →
        BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice s.mem) →
      iterationSafe buildAllBucketsOuterStepProg BuildAllBucketsOuterPre w
        ((cp, base), (rt, hrt)) rem b₀ s := by
  intro cp rt hrt rem
  have hw := henv.2.1
  have hth := henv.2.2.2.1
  have htot3 := @totalLocalCoordsWhp_le_three_mul n_max
  have hq_bm : offQuotWhp c w n_max ≤ offBktMeta c U V w n_max := by
    unfold offBktMeta offLocState offPermAct offValWhp; omega
  induction rem with
  | zero => intro _ _ _ _ _; exact trivial
  | succ rem ih =>
    intro b₀ s hle hseed hz_rem
    have hb_lt : b₀ < numBucketsWhp n_max := by omega
    refine ⟨⟨c, U, V, w, n_max, θ, henv, rfl, rfl, rfl, hseed, hb_lt, hz_rem⟩, ?_⟩
    rw [clientState_width, clientResult_width]
    set p1 := buildAllBucketsOuterStepProg (((cp, base), (rt, hrt)), b₀)
    set lo := readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem b₀
    set hi := readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem (b₀ + 1)
    set salt := readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem
      (16 * b₀ + 1)
    have hr1 : (Memory.spec 0).clientResult s p1 = b₀ + 1 := by
      dsimp only [p1]; unfold buildAllBucketsOuterStepProg; dsimp only [readPackedGenProg]
      simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedProg,
        clientResult_bind, clientState_readPackedProg,
        clientResult_bind, clientState_readPackedProg]
      split_ifs
      · rw [clientResult_bind]; rfl
      · rfl
      · rfl
    rw [hr1]
    by_cases hcond : lo ≤ hi ∧ hi - lo ≤ totalLocalCoordsWhp n_max
    · have hs1_eq : (Memory.spec 0).clientState s p1 =
          (Memory.spec 0).clientState s
            (buildBktSliceLoopProg (((((cp, base), (rt, hrt)), (b₀, salt)), 0), hi - lo)) := by
        dsimp only [p1]; unfold buildAllBucketsOuterStepProg
        simp only [rt, mkHealRt, hlBase, hlW, hlTotalLoc, hlGBits, hlOffBm, hlOffFb,
          readPackedGenProg, pure_bind]
        rw [clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg,
          clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg,
          clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg]
        have hc1 : readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem b₀ ≤
            readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem (b₀ + 1) :=
          hcond.1
        have hc2 : readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem
              (b₀ + 1) -
            readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem b₀ ≤
            totalLocalCoordsWhp n_max := hcond.2
        rw [ite_eq_left hc1, ite_eq_left hc2, clientState_bind]
        rfl
      rw [hs1_eq]
      have hinner : ∀ k l (sl : BTreeSlice) (mf : ℕ → Option ℕ) (st : Memory.State),
          l + k ≤ totalLocalCoordsWhp n_max →
          SeedWhpMemRep base c U w n_max θ st.mem →
          BTreeSliceMemRep base c U V w n_max (3 * b₀) sl st.mem →
          ValidWhpSlice n_max l sl mf →
          (∀ sIdx < 3 * numBucketsWhp n_max, b₀ + 1 ≤ sIdx / 3 →
            BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice st.mem) →
          let st' := (Memory.spec 0).clientState st
            (buildBktSliceLoopProg (((((cp, base), (rt, hrt)), (b₀, salt)), l), k))
          SeedWhpMemRep base c U w n_max θ st'.mem ∧
          (∀ sIdx < 3 * numBucketsWhp n_max, b₀ + 1 ≤ sIdx / 3 →
            BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice st'.mem) := by
        intro k
        induction k with
        | zero =>
          intro _ _ _ st _ hs _ _ hz
          unfold buildBktSliceLoopProg iterate
          exact ⟨hs, hz⟩
        | succ k ihk =>
          intro l sl mf st hlk hs hr hv_sl hz
          obtain ⟨hrq_st, _, _⟩ := readHealSlotQuotProg_spec (b := b₀) (loc := l) henv hb_lt
            (s := st)
          let qv := (Memory.spec 0).clientResult st
            (readHealSlotQuotProg ((rt, (offQuotWhp c w n_max, quotBitsWhp U n_max)), (b₀, l)))
          obtain ⟨hfp_st, hfp_res, _, _⟩ := fpOfQuotRtProg_spec (salt := salt) (b := b₀) (q := qv)
            henv hs (s := st)
          let fpv := (Memory.spec 0).clientResult st (fpOfQuotRtProg (((hrt, salt), b₀), qv))
          have hfp_lt : fpv < 2 ^ fpBitsWhp n_max := by
            change (Memory.spec 0).clientResult st (fpOfQuotRtProg (((hrt, salt), b₀), qv)) < _
            rw [hfp_res]
            split_ifs with hs' hu'
            · exact fpHash_lt c U n_max θ.2 ⟨salt, hs'⟩ ⟨_, hu'⟩
            · exact Nat.two_pow_pos _
            · exact Nat.two_pow_pos _
          have hl_val : l < 2 ^ valLaneBitsWhp n_max := by rw [two_pow_valLaneBitsWhp]; omega
          obtain ⟨_, _, _, hr', hv', hoth', _, hout'⟩ := btreeInsertGenProg_spec (sIdx := 3 * b₀)
            (insCount := l) (q := fpv) (val := l) henv (by omega) (by omega) hr hv_sl hfp_lt hl_val
          set st1 := (Memory.spec 0).clientState st
            (btreeInsertGenProg ((((cp, base), 3 * b₀), fpv), l))
          have hcs_r : (Memory.spec 0).clientState st (Memory.read base) = st := rfl
          have hstep_st : (Memory.spec 0).clientState st
              (buildBktSliceStepProg ((((cp, base), (rt, hrt)), (b₀, salt)), l)) = st1 ∧
              (Memory.spec 0).clientResult st
                (buildBktSliceStepProg ((((cp, base), (rt, hrt)), (b₀, salt)), l)) = l + 1 := by
            unfold buildBktSliceStepProg
            dsimp only [cp, rt, hrt] at hrq_st hfp_st st1 ⊢
            simp only [pure_bind, wp_large_offQuot hth, wp_large_quotBits hth]
            exact ⟨by rw [clientState_bind, hcs_r,
                clientState_bind, hrq_st,
                clientState_bind, hfp_st,
                clientState_bind]; rfl,
              by rw [clientResult_bind, hcs_r,
                clientResult_bind, hrq_st,
                clientResult_bind, hfp_st,
                clientResult_bind]; rfl⟩
          have hs1 : SeedWhpMemRep base c U w n_max θ st1.mem :=
            SeedWhpMemRep.congr_hash hw (fun a _ ha2 => (hout' a (Or.inl (by omega))).symm) hs
          have hz1 : ∀ sIdx < 3 * numBucketsWhp n_max, b₀ + 1 ≤ sIdx / 3 →
              BTreeSliceMemRep base c U V w n_max sIdx zeroBTreeSlice st1.mem :=
            fun sIdx hsIdx hge => hoth' sIdx hsIdx (by omega) zeroBTreeSlice (hz sIdx hsIdx hge)
          have hih := ihk (l + 1) _ _ st1 (by omega) hs1 hr' hv' hz1
          unfold buildBktSliceLoopProg at hih ⊢
          dsimp only [iterate]
          rw [clientState_bind, hstep_st.1, hstep_st.2]
          exact hih
      obtain ⟨hseed_f, hz_f⟩ := hinner (hi - lo) 0 zeroBTreeSlice (fun _ => none) s
        (by omega) hseed (hz_rem (3 * b₀) (by omega) (by omega)) (validWhpSlice_zero _ 0 _)
        (fun sIdx hsIdx hge => hz_rem sIdx hsIdx (by omega))
      exact ih (b₀ + 1) _ (by omega) hseed_f hz_f
    · have hs1_eq : (Memory.spec 0).clientState s p1 = s := by
        dsimp only [p1]; unfold buildAllBucketsOuterStepProg
        simp only [rt, mkHealRt, hlBase, hlW, hlTotalLoc, hlGBits, hlOffBm, hlOffFb,
          readPackedGenProg, pure_bind]
        rw [clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg,
          clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg,
          clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg]
        by_cases h1 : readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem
            b₀ ≤
            readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem (b₀ + 1)
        · have h2 : ¬(readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem
                (b₀ + 1) -
              readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem b₀ ≤
              totalLocalCoordsWhp n_max) := fun h => hcond ⟨h1, h⟩
          rw [ite_eq_left h1, ite_eq_right h2]; rfl
        · rw [ite_eq_right h1]; rfl
      rw [hs1_eq]
      exact ih (b₀ + 1) s (by omega) hseed (fun sIdx hsIdx hge => hz_rem sIdx hsIdx (by omega))

private theorem buildAllBucketsOuterLoop_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fbStart qArr : ℕ → ℕ} {backPtr : ℕ → ℕ → ℕ} {salts : ℕ → ℕ}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hfb_adj : ∀ b < numBucketsWhp n_max, fbStart b ≤ fbStart (b + 1))
    (hbnd : ∀ b < numBucketsWhp n_max,
      (fbStart (b + 1) - fbStart b) - capFrontWhp n_max < capBackWhp n_max ∧
      fbStart (b + 1) - fbStart b ≤ totalLocalCoordsWhp n_max)
    (hbp_ps : ∀ b < numBucketsWhp n_max,
      ∀ k < (fbStart (b + 1) - fbStart b) - capFrontWhp n_max,
        backPtr b k < poolSizeWhp n_max)
    (hseed₀ : SeedWhpMemRep base c U w n_max θ s₀.mem)
    (hfb₀ : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s₀.mem x = fbStart x)
    (hq₀ : ∀ i < n_max,
      readPacked (base + offQuotWhp c w n_max) (quotBitsWhp U n_max) w s₀.mem i = qArr i)
    (hbp₀ : ∀ b < numBucketsWhp n_max, ∀ k < capBackWhp n_max,
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s₀.mem
        (b * capBackWhp n_max + k) = backPtr b k) :
    let cp := mkWhpCoreParams c U V w n_max
    let rt := mkHealRt c U V w n_max base
    let hrt := mkHashRt c U w n_max base
    let M := numBucketsWhp n_max
    let targetSlice : ℕ → BTreeSlice := fun sIdx =>
      let b := sIdx / 3
      let role := sIdx % 3
      if b < M ∧ role = 0 then
        buildBucketSlice c U n_max θ qArr backPtr b (salts b) (fbStart (b + 1) - fbStart b)
      else zeroBTreeSlice
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ M →
      (∀ sIdx < 3 * M,
        BTreeSliceMemRep base c U V w n_max sIdx
          (if sIdx / 3 < b₀ then targetSlice sIdx else zeroBTreeSlice) s.mem) →
      (∀ b < M,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s.mem (16 * b + 1) =
          salts b) →
      (∀ a, (a < base + offBktMeta c U V w n_max ∨
          (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
          base + offTrieChild0 c U V w n_max ≤ a) → s.mem a = s₀.mem a) →
      let prog := buildAllBucketsOuterLoopProg ((((cp, base), (rt, hrt)), b₀), rem)
      let s' := (Memory.spec 0).clientState s prog
      s'.frontier = s.frontier ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (∀ sIdx < 3 * M,
        BTreeSliceMemRep base c U V w n_max sIdx
          (if sIdx / 3 < b₀ + rem then targetSlice sIdx else zeroBTreeSlice) s'.mem) ∧
      (∀ b < M,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s'.mem (16 * b + 1) =
          salts b) ∧
      (∀ a, (a < base + offBktMeta c U V w n_max ∨
          (base + offFbStart c U V w n_max ≤ a ∧ a < base + offBtMeta c U V w n_max) ∨
          base + offTrieChild0 c U V w n_max ≤ a) → s'.mem a = s₀.mem a) := by
  intro cp rt hrt M targetSlice rem
  have hw := henv.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max +
      packedWords (16 * M) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.1 _
  have hfb_b : base + offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ base + largeSpaceWhp c U V w n_max := by
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hseg.2.2.2.2.2.1 _
  have hfb_bt : offFbStart c U V w n_max +
      packedWords (M + 1) (globalPtrBits n_max) w ≤ offBtMeta c U V w n_max := by
    have h6 : offBackPtr c U V w n_max =
      offFbStart c U V w n_max + packedWords (M + 1) (globalPtrBits n_max) w := rfl
    unfold offBtMeta offPoolOwner offPoolFreeStack offBackAux; omega
  induction rem with
  | zero =>
    intro b₀ s _ hprev hsalt_s hout
    unfold buildAllBucketsOuterLoopProg iterate
    rw [Nat.add_zero]
    exact ⟨rfl, validProg_pure _, hprev, hsalt_s, hout⟩
  | succ rem ih =>
    intro b₀ s hle hprev hsalt_s hout
    have hb_lt : b₀ < M := by omega
    have hfb_s : ∀ x ≤ M,
        readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s.mem x = fbStart x :=
      fun x hx => (readPacked_congr hw (hidx := show x < M + 1 by omega)
        (fun a ⟨ha1, ha2⟩ => hout a (Or.inr (Or.inl ⟨ha1, by
          dsimp only [M] at hfb_bt ha2; omega⟩)))).trans (hfb₀ x hx)
    have hlo_hi := hfb_adj b₀ hb_lt
    obtain ⟨hcb_b, hcnt_le⟩ := hbnd b₀ hb_lt
    set cnt := fbStart (b₀ + 1) - fbStart b₀
    have hrep3b : BTreeSliceMemRep base c U V w n_max (3 * b₀) zeroBTreeSlice s.mem := by
      have hp := hprev (3 * b₀) (by omega)
      have hnot : ¬((3 * b₀) / 3 < b₀) := by omega
      rwa [ite_eq_right hnot] at hp
    obtain ⟨hin_fr, hin_vp, hin_rep, hin_oth, hin_bm, hin_out⟩ :=
      buildBktSliceLoop_spec (b := b₀) (salt := salts b₀) (cnt := cnt)
        henv hb_lt hcnt_le hcb_b (hbp_ps b₀ hb_lt) hseed₀ hq₀ (hbp₀ b₀ hb_lt)
        cnt 0 (fun _ => none) s (by omega) hrep3b (validWhpSlice_zero _ 0 _) hout
    rw [Nat.zero_add] at hin_rep
    set s_in := (Memory.spec 0).clientState s
      (buildBktSliceLoopProg (((((cp, base), (rt, hrt)), (b₀, salts b₀)), 0), cnt))
    set p1 := buildAllBucketsOuterStepProg (((cp, base), (rt, hrt)), b₀)
    have h16b1 : 16 * b₀ + 1 < 16 * M := by omega
    have hs1 : (Memory.spec 0).clientState s p1 = s_in ∧
        (Memory.spec 0).clientResult s p1 = b₀ + 1 ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold buildAllBucketsOuterStepProg
      dsimp only [rt, mkHealRt, hlBase, hlW, hlTotalLoc, hlGBits, hlOffBm, hlOffFb,
        readPackedGenProg]
      simp only [pure_bind]
      refine ⟨?_, ?_, ?_⟩
      · rw [clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
          clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt,
          clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hsalt_s b₀ hb_lt]
        simp only [hlo_hi,
          show fbStart (b₀ + 1) - fbStart b₀ ≤ totalLocalCoordsWhp n_max from hcnt_le, ↓reduceIte]
        rw [clientState_bind]; rfl
      · rw [clientResult_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
          clientResult_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt,
          clientResult_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hsalt_s b₀ hb_lt]
        simp only [hlo_hi,
          show fbStart (b₀ + 1) - fbStart b₀ ≤ totalLocalCoordsWhp n_max from hcnt_le, ↓reduceIte]
        rw [clientResult_bind]; rfl
      · refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
        rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s b₀ hb_lt.le]
        refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
        rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt]
        refine validProg_bind (validProg_readPacked hw h16b1 hbm_b) ?_
        rw [clientState_readPackedProg, clientResult_readPackedProg, hsalt_s b₀ hb_lt]
        simp only [hlo_hi,
          show fbStart (b₀ + 1) - fbStart b₀ ≤ totalLocalCoordsWhp n_max from hcnt_le, ↓reduceIte]
        dsimp only [rt, mkHealRt] at hin_vp
        exact validProg_bind hin_vp (validProg_pure _)
    have hprev1 : ∀ sIdx < 3 * M,
        BTreeSliceMemRep base c U V w n_max sIdx
          (if sIdx / 3 < b₀ + 1 then targetSlice sIdx else zeroBTreeSlice) s_in.mem := by
      intro sIdx hsIdx
      by_cases heq3 : sIdx = 3 * b₀
      · subst heq3
        have hlt1 : (3 * b₀) / 3 < b₀ + 1 := by omega
        rw [ite_eq_left hlt1]
        dsimp only [targetSlice]
        have hd : (3 * b₀) / 3 = b₀ := by omega
        have hm : (3 * b₀) % 3 = 0 := by omega
        rw [hd, hm, ite_eq_left ⟨hb_lt, rfl⟩]
        exact hin_rep
      · have hp := hin_oth sIdx hsIdx heq3 _ (hprev sIdx hsIdx)
        by_cases hlt0 : sIdx / 3 < b₀
        · have hlt1 : sIdx / 3 < b₀ + 1 := by omega
          rw [ite_eq_left hlt0] at hp; rw [ite_eq_left hlt1]; exact hp
        · by_cases hlt1 : sIdx / 3 < b₀ + 1
          · have hdb : sIdx / 3 = b₀ := by omega
            have hmr : sIdx % 3 ≠ 0 := by omega
            rw [ite_eq_right hlt0] at hp
            rw [ite_eq_left hlt1]
            dsimp only [targetSlice]
            rw [hdb, ite_eq_right (fun h => hmr h.2)]
            exact hp
          · rw [ite_eq_right hlt0] at hp
            rw [ite_eq_right hlt1]
            exact hp
    have hsalt1 : ∀ b < M,
        readPacked (base + offBktMeta c U V w n_max) (globalPtrBits n_max) w s_in.mem (16 * b + 1) =
          salts b := fun b hb =>
      (hin_bm (16 * b + 1) (by omega) (by omega) (by omega)).trans (hsalt_s b hb)
    obtain ⟨hfr_r, hvp_r, hrep_r, hsalt_r, hout_r⟩ := ih (b₀ + 1) s_in (by omega) hprev1 hsalt1
      hin_out
    have hadd : b₀ + 1 + rem = b₀ + (rem + 1) := by omega
    rw [hadd] at hrep_r
    unfold buildAllBucketsOuterLoopProg at hfr_r hvp_r hrep_r hsalt_r hout_r ⊢
    dsimp only [iterate]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hs1.1, hs1.2.1]; exact hfr_r.trans hin_fr
    · refine validProg_bind hs1.2.2 ?_; rw [hs1.1, hs1.2.1]; exact hvp_r
    · intro sIdx hsIdx
      rw [clientState_bind, hs1.1, hs1.2.1]; exact hrep_r sIdx hsIdx
    · intro b hb
      rw [clientState_bind, hs1.1, hs1.2.1]; exact hsalt_r b hb
    · intro a ha
      rw [clientState_bind, hs1.1, hs1.2.1]; exact hout_r a ha

/-! ### Phase F: `fillFinalBktMetaLoopProg` (write final bucket scalar fields `0, 2..9`) -/

@[irreducible] private def fillFinalBktMetaStepProg : HealRt × ℕ → Memory.Prog ℕ
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
      FillBackPtrOuterPre
      (fun _ _ => 0) := by
  unfold fillFinalBktMetaStepProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  have hcs : ∀ y s', (Memory.spec 0).clientState s' (readPackedGenProg y) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨rt, b⟩
    dsimp only [FillBackPtrOuterPre] at h
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

@[irreducible] private def fillFinalBktMetaLoopProg : (HealRt × ℕ) × ℕ → Memory.Prog ℕ
  | ((rt, b₀), rem) => iterate fillFinalBktMetaStepProg rt rem b₀

private theorem realizes_fillFinalBktMetaLoop :
    Realizes .exact fillFinalBktMetaLoopProg
      (WordEncoding.encode (α := (HealRt × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((rt, b₀), rem) s =>
        iterationSafe fillFinalBktMetaStepProg FillBackPtrOuterPre w rt rem b₀ s)
      (fun _ _ => 0) := by
  unfold fillFinalBktMetaLoopProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := HealRt))
    (WordEncoding.encode (α := ℕ))
    realizes_fillFinalBktMetaStep
    memoryCost_fillFinalBktMetaStep_pos

private theorem fillFinalBktMetaLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    ∀ rem b₀ (s : Memory.State),
      b₀ + rem ≤ numBucketsWhp n_max →
      iterationSafe fillFinalBktMetaStepProg FillBackPtrOuterPre w rt rem b₀ s := by
  intro rt rem
  induction rem with
  | zero => intro _ _ _; exact trivial
  | succ rem ih =>
    intro b₀ s hle
    refine ⟨⟨⟨c, U, V, w, n_max, henv, rfl⟩, by dsimp [rt, mkHealRt, hlM]; omega⟩, ?_⟩
    rw [clientState_width, clientResult_width]
    have hr1 : (Memory.spec 0).clientResult s (fillFinalBktMetaStepProg (rt, b₀)) = b₀ + 1 := by
      unfold fillFinalBktMetaStepProg; dsimp only [readPackedGenProg, writePackedGenProg]
      simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedProg,
        clientResult_bind, clientState_readPackedProg,
        clientResult_bind, clientState_writePackedProg,
        clientResult_bind, clientState_writePackedProg,
        clientResult_bind, clientState_writePackedProg,
        clientResult_bind, clientState_writePackedProg,
        clientResult_bind, clientState_writePackedProg,
        clientResult_bind, clientState_writePackedProg,
        clientResult_bind, clientState_writePackedProg]
      split_ifs <;>
        (rw [clientResult_bind, clientState_writePackedProg,
           clientResult_bind]
         rfl)
    rw [hr1]
    exact ih (b₀ + 1) _ (by omega)

private theorem fillFinalBktMetaLoop_spec {c U V w n_max base : ℕ} {fbStart : ℕ → ℕ}
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
    have hs1 : (Memory.spec 0).clientState s p1 = { mem := m1, frontier := s.frontier } ∧
        (Memory.spec 0).clientResult s p1 = b₀ + 1 ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold fillFinalBktMetaStepProg
      dsimp only [rt, mkHealRt, hlBase, hlW, hlNMax, hlGBits, hlOffBm, hlOffFb,
        readPackedGenProg, writePackedGenProg]
      simp only [pure_bind]
      refine ⟨?_, ?_, ?_⟩
      · rw [clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
          clientState_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt,
          clientState_bind, clientState_writePackedProg,
          clientState_bind, clientState_writePackedProg,
          clientState_bind, clientState_writePackedProg,
          clientState_bind, clientState_writePackedProg,
          clientState_bind, clientState_writePackedProg,
          clientState_bind, clientState_writePackedProg,
          clientState_bind, clientState_writePackedProg]
        simp only [hlo_hi, show fbStart (b₀ + 1) - fbStart b₀ ≤ n_max from hcnt_le, ↓reduceIte]
        rw [clientState_bind, clientState_writePackedProg,
          clientState_bind, clientState_writePackedProg]; rfl
      · rw [clientResult_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hfb_s b₀ hb_lt.le,
          clientResult_bind, clientState_readPackedProg,
          clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt,
          clientResult_bind, clientState_writePackedProg,
          clientResult_bind, clientState_writePackedProg,
          clientResult_bind, clientState_writePackedProg,
          clientResult_bind, clientState_writePackedProg,
          clientResult_bind, clientState_writePackedProg,
          clientResult_bind, clientState_writePackedProg,
          clientResult_bind, clientState_writePackedProg]
        simp only [hlo_hi, show fbStart (b₀ + 1) - fbStart b₀ ≤ n_max from hcnt_le, ↓reduceIte]
        rw [clientResult_bind, clientState_writePackedProg,
          clientResult_bind]; rfl
      · refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
        rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s b₀ hb_lt.le]
        refine validProg_bind (validProg_readPacked hw (by omega) hfb_b) ?_
        rw [clientState_readPackedProg, clientResult_readPackedProg, hfb_s (b₀ + 1) hb_lt]
        refine validProg_bind (validProg_writePacked (N := 16 * M) hw hgk (by omega) hbm_b) ?_
        rw [clientState_writePackedProg]
        refine validProg_bind (validProg_writePacked (N := 16 * M) hw hgk (by omega) hbm_b) ?_
        rw [clientState_writePackedProg]
        refine validProg_bind (validProg_writePacked (N := 16 * M) hw hgk (by omega) hbm_b) ?_
        rw [clientState_writePackedProg]
        refine validProg_bind (validProg_writePacked (N := 16 * M) hw hgk (by omega) hbm_b) ?_
        rw [clientState_writePackedProg]
        refine validProg_bind (validProg_writePacked (N := 16 * M) hw hgk (by omega) hbm_b) ?_
        rw [clientState_writePackedProg]
        refine validProg_bind (validProg_writePacked (N := 16 * M) hw hgk (by omega) hbm_b) ?_
        rw [clientState_writePackedProg]
        refine validProg_bind (validProg_writePacked (N := 16 * M) hw hgk (by omega) hbm_b) ?_
        rw [clientState_writePackedProg]
        simp only [hlo_hi, show fbStart (b₀ + 1) - fbStart b₀ ≤ n_max from hcnt_le, ↓reduceIte]
        refine validProg_bind (validProg_writePacked (N := 16 * M) hw hgk (by omega) hbm_b) ?_
        rw [clientState_writePackedProg]
        exact validProg_bind (validProg_writePacked (N := 16 * M) hw hgk (by omega) hbm_b)
          (validProg_pure _)
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
        dsimp only [s1] at hp ⊢
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hne_m1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega)]; exact hp.1
        · rw [hne_m1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega)]; exact hp.2.1
        · rw [hne_m1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega)]; exact hp.2.2.1
        · rw [hne_m1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega)]; exact hp.2.2.2.1
        · rw [hne_m1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega)]; exact hp.2.2.2.2.1
        · rw [hne_m1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega)]; exact hp.2.2.2.2.2.1
        · rw [hne_m1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega)]; exact hp.2.2.2.2.2.2.1
        · rw [hne_m1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega)]; exact hp.2.2.2.2.2.2.2.1
        · rw [hne_m1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega)]; exact hp.2.2.2.2.2.2.2.2
      · dsimp only [s1, m1, wpAt]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [Nat.add_zero, readPacked_writePacked_of_ne hw _ (by omega)]
          exact readPacked_writePacked_self _ _ _ _ _ hcnt_pow
        · repeat rw [readPacked_writePacked_of_ne hw _ (by omega)]
          exact readPacked_writePacked_self _ _ _ _ _ h0_pow
        · exact readPacked_writePacked_self _ _ _ _ _ hcnt_pow
        · rw [readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_self _ _ _ _ _ h1_pow]
        · rw [readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_self _ _ _ _ _ h0_pow]
        · rw [readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_self _ _ _ _ _ h0_pow]
        · rw [readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_self _ _ _ _ _ h0_pow]
        · rw [readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_self _ _ _ _ _ h0_pow]
        · rw [readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_of_ne hw _ (by omega),
            readPacked_writePacked_self _ _ _ _ _ h0_pow]
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
      rw [writePacked_outside hw _ (by omega : 16 * b₀ + 3 < 16 * M) _ (by cases hdisj <;> omega),
        writePacked_outside hw _ (by omega : 16 * b₀ < 16 * M) _ (by cases hdisj <;> omega),
        writePacked_outside hw _ (by omega : 16 * b₀ + 9 < 16 * M) _ (by cases hdisj <;> omega),
        writePacked_outside hw _ (by omega : 16 * b₀ + 8 < 16 * M) _ (by cases hdisj <;> omega),
        writePacked_outside hw _ (by omega : 16 * b₀ + 7 < 16 * M) _ (by cases hdisj <;> omega),
        writePacked_outside hw _ (by omega : 16 * b₀ + 6 < 16 * M) _ (by cases hdisj <;> omega),
        writePacked_outside hw _ (by omega : 16 * b₀ + 5 < 16 * M) _ (by cases hdisj <;> omega),
        writePacked_outside hw _ (by omega : 16 * b₀ + 4 < 16 * M) _ (by cases hdisj <;> omega),
        writePacked_outside hw _ (by omega : 16 * b₀ + 2 < 16 * M) _ (by cases hdisj <;> omega)]
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

/-! ### Phase G: `zeroTrieChildrenLoopProg` and `writeHealHdrsAndTrieMetaProg` -/

@[irreducible] private def zeroTrieChildrenStepProg :
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

private def ZeroTrieChildrenPre (w : ℕ)
    (d : (HealRt × (ℕ × ℕ)) × ℕ) (_s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max,
    WhpLargeEnv c U V w₀ n_max w (hlBase d.1.1) ∧
    d.1.1 = mkHealRt c U V w₀ n_max (hlBase d.1.1) ∧
    d.1.2.1 = offTrieChild0 c U V w₀ n_max ∧
    d.1.2.2 = offTrieChild1 c U V w₀ n_max ∧
    d.2 < trieChildEntriesWhp c n_max

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

@[irreducible] private def zeroTrieChildrenLoopProg :
    ((HealRt × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((cfg, i₀), rem) => iterate zeroTrieChildrenStepProg cfg rem i₀

private theorem realizes_zeroTrieChildrenLoop :
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

private theorem zeroTrieChildrenLoop_safe {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let rt := mkHealRt c U V w n_max base
    let tc0 := offTrieChild0 c U V w n_max
    let tc1 := offTrieChild1 c U V w n_max
    ∀ rem i₀ (s : Memory.State),
      i₀ + rem ≤ trieChildEntriesWhp c n_max →
      iterationSafe zeroTrieChildrenStepProg ZeroTrieChildrenPre w (rt, (tc0, tc1)) rem i₀ s := by
  intro rt tc0 tc1 rem
  induction rem with
  | zero => intro _ _ _; exact trivial
  | succ rem ih =>
    intro i₀ s hle
    refine ⟨⟨c, U, V, w, n_max, henv, rfl, rfl, rfl, by omega⟩, ?_⟩
    rw [clientState_width, clientResult_width]
    have hr1 : (Memory.spec 0).clientResult s
        (zeroTrieChildrenStepProg ((rt, (tc0, tc1)), i₀)) = i₀ + 1 := by
      unfold zeroTrieChildrenStepProg; dsimp only [writePackedGenProg]; simp only [pure_bind]
      rw [clientResult_bind, clientState_writePackedProg,
        clientResult_bind]; rfl
    rw [hr1]
    exact ih (i₀ + 1) _ (by omega)

private theorem zeroTrieChildrenLoop_spec {c U V w n_max base : ℕ}
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
    have hs1 : (Memory.spec 0).clientState s p1 = { mem := m2, frontier := s.frontier } ∧
        (Memory.spec 0).clientResult s p1 = i₀ + 1 ∧
        ValidProg w (base + largeSpaceWhp c U V w n_max) s p1 := by
      dsimp only [p1]; unfold zeroTrieChildrenStepProg
      dsimp only [rt, mkHealRt, hlBase, hlW, hlGBits, writePackedGenProg]
      simp only [pure_bind]
      refine ⟨?_, ?_, ?_⟩
      · rw [clientState_bind, clientState_writePackedProg,
          clientState_bind, clientState_writePackedProg]; rfl
      · rw [clientResult_bind, clientState_writePackedProg,
          clientResult_bind]; rfl
      · refine validProg_bind (validProg_writePacked hw hgk hi_lt htc0_b) ?_
        rw [clientState_writePackedProg]
        exact validProg_bind (validProg_writePacked hw hgk hi_lt htc1_b)
          (validProg_pure _)
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

@[irreducible] private def writeHealHdrsAndTrieMetaProg :
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

private def WriteHealHdrsPre (w : ℕ)
    (d : (HealRt × (ℕ × ℕ)) × ℕ) (_s : Memory.State) : Prop :=
  ∃ c U V w₀ n_max,
    WhpLargeEnv c U V w₀ n_max w (hlBase d.1.1) ∧
    d.1.1 = mkHealRt c U V w₀ n_max (hlBase d.1.1) ∧
    d.1.2.1 = offTrieMeta0 c U V w₀ n_max ∧
    d.1.2.2 = offTrieMeta1 c U V w₀ n_max

private theorem realizes_writeHealHdrsAndTrieMeta :
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

private theorem writeHealHdrsAndTrieMetaProg_spec {c U V w n_max base freeTop : ℕ}
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
  have hst_eq : (Memory.spec 0).clientState s
      (writeHealHdrsAndTrieMetaProg ((rt, (tm0, tm1)), freeTop)) =
      { mem := m_fin, frontier := s.frontier } := by
    unfold writeHealHdrsAndTrieMetaProg
    dsimp only [rt, mkHealRt, hlBase, hlW, hlGBits, writePackedGenProg]
    simp only [pure_bind]
    rfl
  have hm_ge16 : ∀ a, (a < base ∨ base + 16 ≤ a) → m_fin a = m_tm1 a := by
    intro a ha; dsimp only [m_fin, upd]
    repeat rw [Function.update_of_ne (by omega)]
  have h0_pow : 0 < 2 ^ gBits := Nat.two_pow_pos _
  refine ⟨by rw [hst_eq], ?_, ?_⟩
  · unfold writeHealHdrsAndTrieMetaProg
    dsimp only [rt, mkHealRt, hlBase, hlW, hlGBits, writePackedGenProg]
    simp only [pure_bind]
    refine validProg_bind (validProg_writePacked hw hgk h2_lt htm0_b) ?_
    rw [clientState_writePackedProg]
    refine validProg_bind (validProg_writePacked hw hgk h2_lt htm1_b) ?_
    rw [clientState_writePackedProg]
    refine validProg_bind (validProg_write (by omega) h1_fit) ?_
    refine validProg_bind (validProg_write (by omega) hft_fit) ?_
    refine validProg_bind (validProg_write (by omega) h0_fit) ?_
    refine validProg_bind (validProg_write (by omega) h0_fit) ?_
    refine validProg_bind (validProg_write (by omega) h5_fit) ?_
    refine validProg_bind (validProg_write (by omega) h0_fit) ?_
    refine validProg_bind (validProg_write (by omega) h0_fit) ?_
    refine validProg_bind (validProg_write (by omega) h0_fit) ?_
    refine validProg_bind (validProg_write (by omega) h0_fit) ?_
    refine validProg_bind (validProg_write (by omega) h0_fit) ?_
    refine validProg_bind (validProg_write (by omega) h0_fit) ?_
    refine validProg_bind (validProg_write (by omega) h0_fit) ?_
    refine validProg_bind (validProg_write (by omega) h1_fit) ?_
    refine validProg_bind (validProg_write (by omega) h0_fit) ?_
    refine validProg_bind (validProg_write (by omega) h1_fit) ?_
    exact validProg_write (by omega) h0_fit
  · rw [hst_eq]
    dsimp only [hdrMode, hdrPoolFreeTop, hdrCurEp, hdrEpochClock, hdrRebStage, hdrStageCursor,
      hdrDirtyCount, hdrDirtyIdx, hdrRebCandSalt, hdrRebScanCursor, hdrRebInsCount,
      hdrRebCollision, hdrBuf0NodeAlloc, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc, hdrBuf1ItemAlloc]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
    · dsimp only [m_fin, upd]; rw [Nat.add_zero]
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      repeat rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]
      rw [Function.update_of_ne (by omega)]
      exact Function.update_self _ _ _
    · dsimp only [m_fin, upd]; exact Function.update_self _ _ _
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

/-! ### Phase C Helper (`heval` for `permuteByTargetProg`, `mode = 2`) & `csrToFastGenProg`
-/

private theorem csrPermute_eval_spec {c U V w n_max base : ℕ} {csr : CsrState}
    {s₀ : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hfb0 : csr.fbStart 0 = 0)
    (hfb_adj : ∀ b < numBucketsWhp n_max, csr.fbStart b ≤ csr.fbStart (b + 1))
    (hback_cb : ∀ b < numBucketsWhp n_max,
      (csr.fbStart (b + 1) - csr.fbStart b) - capFrontWhp n_max < capBackWhp n_max)
    (hbp_ps : buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) csr.fbStart
      (numBucketsWhp n_max) ≤ poolSizeWhp n_max)
    (hfb_mem : ∀ x ≤ numBucketsWhp n_max,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s₀.mem x = csr.fbStart x)
    (hbp_mem : ∀ b < numBucketsWhp n_max, ∀ k < capBackWhp n_max,
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s₀.mem
        (b * capBackWhp n_max + k) =
        if k < (csr.fbStart (b + 1) - csr.fbStart b) - capFrontWhp n_max then
          buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) csr.fbStart b + k
        else 0) :
    let M := numBucketsWhp n_max
    let cf := capFrontWhp n_max
    let bp := buildBackPrefix M cf csr.fbStart
    let bktCnt : ℕ → ℕ := fun b => if b < M then csr.fbStart (b + 1) - csr.fbStart b else 0
    let backPtr : ℕ → ℕ → ℕ := fun b k =>
      if b < M ∧ k < bktCnt b - cf then bp b + k else 0
    let act₀ : ℕ → Bool := fun i => decide (i < csr.fbStart M)
    let dest : ℕ → ℕ := fun i =>
      let b := csrBucketOfIdx csr.fbStart i M
      let loc := i - csr.fbStart b
      if loc < cf then b * cf + loc
      else M * cf + backPtr b (loc - cf)
    ∀ x < n_max, ∀ s' : Memory.State,
      (∀ a, (a < base + offQuotWhp c w n_max ∨ base + offLocState c U V w n_max ≤ a) →
        s'.mem a = s₀.mem a) →
      ((Memory.spec 0).clientResult s'
        (permEvalActDestProg ((mkPermRt c U V w n_max base, 2), x))).1 =
          (if act₀ x then 1 else 0) ∧
      (act₀ x = true →
        ((Memory.spec 0).clientResult s'
          (permEvalActDestProg ((mkPermRt c U V w n_max base, 2), x))).2 = dest x ∧
        dest x < n_max) := by
  intro M cf bp bktCnt backPtr act₀ dest x _ s' hout
  have hw := henv.2.1
  have hMcf_le : M * cf ≤ n_max :=
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (Nat.mul_div_le _ _)
  have hls_fb : offLocState c U V w n_max ≤ offFbStart c U V w n_max := by
    unfold offFbStart offBktMeta; omega
  have hls_bp : offLocState c U V w n_max ≤ offBackPtr c U V w n_max := by
    unfold offBackPtr offFbStart offBktMeta; omega
  have hfb_s' : ∀ z ≤ M,
      readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w s'.mem z =
        csr.fbStart z := fun z hz =>
    (readPacked_congr hw (fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega)))
      (Nat.lt_succ_of_le hz)).trans (hfb_mem z hz)
  have hbp_s' : ∀ b < M, ∀ k < capBackWhp n_max,
      readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
        (b * capBackWhp n_max + k) = backPtr b k := by
    intro b hb k hk
    rw [readPacked_congr hw (fun a ⟨ha1, _⟩ => hout a (Or.inr (by omega)))
      (mul_add_lt_mul_bound hb hk), hbp_mem b hb k hk]
    dsimp only [backPtr, bktCnt]
    by_cases hk' : k < (csr.fbStart (b + 1) - csr.fbStart b) - cf
    · rw [ite_eq_left hk', ite_eq_left ⟨hb, by simp only [hb, ↓reduceIte]; exact hk'⟩]
    · have hnot : ¬(b < M ∧ k < (if b < M then csr.fbStart (b + 1) - csr.fbStart b else 0) - cf) :=
        fun h => hk' (by have h2 := h.2; simp only [hb, ↓reduceIte] at h2; exact h2)
      rw [ite_eq_right hk', ite_eq_right hnot]
  obtain ⟨_, hbp_adj, _, hbp_mono⟩ := backPrefix_spec M cf csr.fbStart
  let fbRd := fun k => readPacked (base + offFbStart c U V w n_max) (globalPtrBits n_max) w
    s'.mem k
  let b_rd := csrBucketOfIdx fbRd x (numBucketsWhp n_max)
  have hfbM : fbRd (numBucketsWhp n_max) = csr.fbStart M := hfb_s' M le_rfl
  have hb_congr : b_rd = csrBucketOfIdx csr.fbStart x M := csrBucketOfIdx_congr hfb_s'
  have hboth :
      (Memory.spec 0).clientResult s'
        (permEvalActDestProg ((mkPermRt c U V w n_max base, 2), x)) =
        (if act₀ x then (1, dest x) else (0, 0)) ∧
      (act₀ x = true → dest x < n_max) := by
    rw [clientResult_permEvalActDestProg_of_ne_one henv (by decide) s']
    change (if x < fbRd (numBucketsWhp n_max) then
        if b_rd < numBucketsWhp n_max then
          if x < fbRd b_rd then (0, 0)
          else if x - fbRd b_rd < capFrontWhp n_max then
            (1, b_rd * capFrontWhp n_max + (x - fbRd b_rd))
          else if x - fbRd b_rd - capFrontWhp n_max < capBackWhp n_max then
            if readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
                (b_rd * capBackWhp n_max + (x - fbRd b_rd - capFrontWhp n_max)) <
                poolSizeWhp n_max then
              (1, numBucketsWhp n_max * capFrontWhp n_max +
                readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
                  (b_rd * capBackWhp n_max + (x - fbRd b_rd - capFrontWhp n_max)))
            else (0, 0)
          else (0, 0)
        else (0, 0)
      else (0, 0)) = (if act₀ x then (1, dest x) else (0, 0)) ∧ _
    by_cases hxN : x < csr.fbStart M
    · have hxN_rd : x < fbRd (numBucketsWhp n_max) := hfbM.symm ▸ hxN
      set b_x := csrBucketOfIdx csr.fbStart x M
      obtain ⟨hb_x, hlo_x, hhi_x⟩ := csrBucketOfIdx_spec hfb0 hfb_adj M le_rfl x hxN
      have hb_x' : b_x < M := hb_x
      have hlo_x' : csr.fbStart b_x ≤ x := hlo_x
      have hhi_x' : x < csr.fbStart (b_x + 1) := hhi_x
      have hb_x_rd : b_rd < numBucketsWhp n_max := hb_congr.symm ▸ hb_x'
      have hfb_bx : fbRd b_rd = csr.fbStart b_x := by
        dsimp only [fbRd]; rw [hb_congr]; exact hfb_s' b_x hb_x'.le
      have hnot_lt_rd : ¬(x < fbRd b_rd) := by rw [hfb_bx]; exact Nat.not_lt.mpr hlo_x'
      have ha_true : act₀ x = true := by dsimp only [act₀]; exact decide_eq_true hxN
      rw [ite_eq_left hxN_rd, ite_eq_left hb_x_rd, ite_eq_right hnot_lt_rd, ha_true,
        ite_eq_left rfl]
      set loc_x := x - csr.fbStart b_x
      by_cases hcf : loc_x < cf
      · have hcf_rd : x - fbRd b_rd < capFrontWhp n_max := by rw [hfb_bx]; exact hcf
        have hd_eq : dest x = b_x * cf + loc_x := by dsimp only [dest]; exact ite_eq_left hcf
        rw [ite_eq_left hcf_rd, hfb_bx, hb_congr, hd_eq]
        exact ⟨rfl, fun _ => (mul_add_lt_mul_bound hb_x' hcf).trans_le hMcf_le⟩
      · have hcf_rd : ¬(x - fbRd b_rd < capFrontWhp n_max) := by rw [hfb_bx]; exact hcf
        set k_x := loc_x - cf
        have hk_rem : k_x < (csr.fbStart (b_x + 1) - csr.fbStart b_x) - cf := by
          dsimp only [k_x, loc_x] at hcf ⊢; omega
        have hk_cb : k_x < capBackWhp n_max := hk_rem.trans (hback_cb b_x hb_x')
        have hk_cb_rd : x - fbRd b_rd - capFrontWhp n_max < capBackWhp n_max := by
          rw [hfb_bx]; exact hk_cb
        have hbp_val_eq : backPtr b_x k_x = bp b_x + k_x := by
          dsimp only [backPtr, bktCnt]
          exact ite_eq_left ⟨hb_x', by rw [ite_eq_left hb_x']; exact hk_rem⟩
        have hbp_lt_ps : backPtr b_x k_x < poolSizeWhp n_max := by
          rw [hbp_val_eq]
          have hstep : bp (b_x + 1) = bp b_x + ((csr.fbStart (b_x + 1) - csr.fbStart b_x) - cf) :=
            hbp_adj b_x hb_x'
          have hleM : bp (b_x + 1) ≤ bp M := hbp_mono (b_x + 1) M hb_x' le_rfl
          have hbp_ps' : bp M ≤ poolSizeWhp n_max := hbp_ps
          dsimp only [k_x, loc_x] at hk_rem ⊢
          omega
        have hbp_rd : readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w s'.mem
            (b_rd * capBackWhp n_max + (x - fbRd b_rd - capFrontWhp n_max)) = backPtr b_x k_x := by
          rw [hfb_bx, hb_congr]; exact hbp_s' b_x hb_x' k_x hk_cb
        have hbp_lt_rd : readPacked (base + offBackPtr c U V w n_max) (globalPtrBits n_max) w
            s'.mem (b_rd * capBackWhp n_max + (x - fbRd b_rd - capFrontWhp n_max)) <
            poolSizeWhp n_max := by
          rw [hbp_rd]; exact hbp_lt_ps
        have hd_lt : M * cf + backPtr b_x k_x < n_max := by
          unfold poolSizeWhp at hbp_lt_ps; dsimp only [M, cf]; omega
        have hd_eq : dest x = M * cf + backPtr b_x k_x := by
          dsimp only [dest]; exact ite_eq_right hcf
        rw [ite_eq_right hcf_rd, ite_eq_left hk_cb_rd, ite_eq_left hbp_lt_rd, hbp_rd, hd_eq]
        exact ⟨rfl, fun _ => hd_lt⟩
    · have hxN_rd : ¬(x < fbRd (numBucketsWhp n_max)) := by rw [hfbM]; exact hxN
      have ha_false : act₀ x = false := by dsimp only [act₀]; exact decide_eq_false hxN
      rw [ite_eq_right hxN_rd, ha_false, ite_eq_right Bool.false_ne_true]
      exact ⟨rfl, fun h => Bool.noConfusion h⟩
  rw [hboth.1]
  cases ha : act₀ x
  · rw [ite_eq_right Bool.false_ne_true]
    exact ⟨rfl, fun h => Bool.noConfusion h⟩
  · rw [ite_eq_left rfl]
    exact ⟨rfl, fun _ => ⟨rfl, hboth.2 ha⟩⟩

@[irreducible] private def clampSubProg (p : ℕ × ℕ) : Memory.Prog ℕ :=
  if p.2 ≤ p.1 then pure (p.1 - p.2) else pure 0

private theorem realizes_clampSub :
    Realizes .exact clampSubProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True)
      (fun _ _ => 0) := by
  unfold clampSubProg
  realize
  omega

private theorem clampSubProg_spec {ps tb w F : ℕ} (hle : tb ≤ ps) (s : Memory.State) :
    (Memory.spec 0).clientState s (clampSubProg (ps, tb)) = s ∧
    (Memory.spec 0).clientResult s (clampSubProg (ps, tb)) = ps - tb ∧
    ValidProg w F s (clampSubProg (ps, tb)) := by
  unfold clampSubProg
  dsimp only
  rw [ite_eq_left hle]
  exact ⟨rfl, rfl, validProg_pure _⟩

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
@[irreducible] private def csrToFastGenProg : WhpParams × ℕ → Memory.Prog Unit
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
  -- Step w0
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
    (readPacked_congr hw (hidx := show x < M + 1 by omega) (fun a ⟨ha1,
      _⟩ => hout_bp a (Or.inr ha1))).trans
      (hrep.2.1 x hx)
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
  -- Helper: memory equality from `s_ras` back to intermediate states
  have hras_to_ls_nonBm : ∀ a,
      (a < base + offBktMeta c U V w n_max ∨ base + offFbStart c U V w n_max ≤ a) →
      s_ras.mem a = s_ls.mem a := hout_ras
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
    exact (readPacked_congr hw (hidx := show x < M + 1 by omega) (fun a ⟨ha1,
      ha2⟩ => ha_fn a ha1 ha2)).trans
      ((readPacked_congr hw (hidx := show x < M + 1 by omega)
        (fun a ⟨ha1, _⟩ => hout_pt a (Or.inr (by omega)))).trans (hfb_fbp x hx))
  · intro i hi
    exact ⟨(readPacked_congr hw (hidx := hi) (fun a ⟨_,
      ha2⟩ => hras_to_pt a (Or.inl (by omega)))).trans
        (hpt_qv i hi).1,
      (readPacked_congr hw (hidx := hi) (fun a ⟨_, ha2⟩ => hras_to_pt a (Or.inl (by omega)))).trans
        (hpt_qv i hi).2⟩
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
    rw [readPacked_congr hw (hidx := mul_add_lt_mul_bound hb hk) (fun a ⟨ha1,
      ha2⟩ => ha_fn a ha1 ha2),
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
    refine ⟨?_, ?_⟩
    · exact (readPacked_congr hw (hidx := hj) (fun a ⟨ha1, _⟩ =>
        (hout_ras a (Or.inr (by omega))).trans (hout_ls a (Or.inr (by omega))))).trans
        (hfs_j j hj)
    · exact (readPacked_congr hw (hidx := hj) (fun a ⟨ha1, _⟩ =>
        (hout_ras a (Or.inr (by omega))).trans
          ((hout_ls a (Or.inr (by omega))).trans (hout_fs a (Or.inr ha1))))).trans
        (hpo_j j hj)
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

private theorem hlBase_mk (c U V w n_max base : ℕ) :
    hlBase (mkHealRt c U V w n_max base) = base := rfl
private theorem hlW_mk (c U V w n_max base : ℕ) :
    hlW (mkHealRt c U V w n_max base) = w := rfl
private theorem hlM_mk (c U V w n_max base : ℕ) :
    hlM (mkHealRt c U V w n_max base) = numBucketsWhp n_max := rfl
private theorem hlPoolSize_mk (c U V w n_max base : ℕ) :
    hlPoolSize (mkHealRt c U V w n_max base) = poolSizeWhp n_max := rfl
private theorem hlGBits_mk (c U V w n_max base : ℕ) :
    hlGBits (mkHealRt c U V w n_max base) = globalPtrBits n_max := rfl
private theorem hlOffBm_mk (c U V w n_max base : ℕ) :
    hlOffBm (mkHealRt c U V w n_max base) = offBktMeta c U V w n_max := rfl

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
    fun y _ => by unfold clampSubProg; split_ifs <;> rfl
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
    (Memory.spec 0).clientState s (csrToFastPart1Prog (cp, base)) = s_ras ∧
    (Memory.spec 0).clientResult s (csrToFastPart1Prog (cp, base)) = freeTop ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s (csrToFastPart1Prog (cp, base)) := by
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
  have htb_rd_gen : (Memory.spec 0).clientResult s_bp
      (readPackedGenProg (((base, offBktMeta c U V w n_max), (gBits, w)), 2 * M)) = totalBack :=
    htb_rd
  have hcs_rp : (Memory.spec 0).clientState s_bp
      (readPackedGenProg (((base, offBktMeta c U V w n_max), (gBits, w)), 2 * M)) = s_bp := rfl
  obtain ⟨hcl_st, hcl_res, hcl_vp⟩ :=
    clampSubProg_spec (w := w) (F := base + largeSpaceWhp c U V w n_max) htb_le s_pt
  have hM_pos : 0 < M := Nat.two_pow_pos _
  dsimp only [cp] at hmr_st hmr_res hmr_vp hmp_st hmp_res hmp_vp hmr_pt_st hmr_pt_res hmr_pt_vp
  have h1a : (Memory.spec 0).clientState s (csrToFastPart1aProg (cp, base)) = s_pt ∧
      (Memory.spec 0).clientResult s (csrToFastPart1aProg (cp, base)) = totalBack ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s (csrToFastPart1aProg (cp, base)) := by
    unfold csrToFastPart1aProg
    simp only [pure_bind]
    refine ⟨?_, ?_, ?_⟩
    · rw [clientState_bind, hmr_st, hmr_res,
        clientState_bind, hmp_st, hmp_res]
      simp only [hlBase_mk, hlW_mk, hlM_mk, hlGBits_mk, hlOffBm_mk]
      rw [clientState_bind, clientState_bind]
      change (Memory.spec 0).clientState s_bp _ = s_pt
      rw [clientState_bind, hcs_rp, htb_rd_gen,
        clientState_bind, clientState_bind]
      rfl
    · rw [clientResult_bind, hmr_st, hmr_res,
        clientResult_bind, hmp_st, hmp_res]
      simp only [hlBase_mk, hlW_mk, hlM_mk, hlGBits_mk, hlOffBm_mk]
      rw [clientResult_bind, clientResult_bind]
      change (Memory.spec 0).clientResult s_bp _ = totalBack
      rw [clientResult_bind, hcs_rp, htb_rd_gen,
        clientResult_bind, clientResult_bind]
      rfl
    · refine validProg_bind hmr_vp ?_; rw [hmr_st, hmr_res]
      refine validProg_bind hmp_vp ?_; rw [hmp_st, hmp_res]
      simp only [hlBase_mk, hlW_mk, hlM_mk, hlGBits_mk, hlOffBm_mk]
      refine validProg_bind hvp_w0 ?_
      refine validProg_bind hvp_bp ?_
      refine validProg_bind (validProg_readPacked hw (by omega) hbm_b) ?_
      rw [hcs_rp, htb_rd_gen]
      refine validProg_bind hvp_fbp ?_
      exact validProg_bind hvp_pt (validProg_pure _)
  have h1b : (Memory.spec 0).clientState s_pt
        (csrToFastPart1bProg ((cp, base), totalBack)) = s_ras ∧
      (Memory.spec 0).clientResult s_pt
        (csrToFastPart1bProg ((cp, base), totalBack)) = freeTop ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s_pt
        (csrToFastPart1bProg ((cp, base), totalBack)) := by
    unfold csrToFastPart1bProg
    simp only [pure_bind]
    refine ⟨?_, ?_, ?_⟩
    · rw [clientState_bind, hmr_pt_st, hmr_pt_res]
      simp only [hlM_mk, hlPoolSize_mk]
      rw [clientState_bind, hcl_st, hcl_res,
        clientState_bind, clientState_bind,
        clientState_bind, clientState_bind]
      rfl
    · rw [clientResult_bind, hmr_pt_st, hmr_pt_res]
      simp only [hlM_mk, hlPoolSize_mk]
      rw [clientResult_bind, hcl_st, hcl_res,
        clientResult_bind, clientResult_bind,
        clientResult_bind, clientResult_bind]
      rfl
    · refine validProg_bind hmr_pt_vp ?_; rw [hmr_pt_st, hmr_pt_res]
      simp only [hlM_mk, hlPoolSize_mk]
      refine validProg_bind hcl_vp ?_; rw [hcl_st, hcl_res]
      refine validProg_bind hvp_po ?_
      refine validProg_bind hvp_fs ?_
      refine validProg_bind hvp_ls ?_
      exact validProg_bind hvp_ras (validProg_pure _)
  unfold csrToFastPart1Prog
  simp only [pure_bind]
  refine ⟨?_, ?_, ?_⟩
  · rw [clientState_bind, h1a.1, h1a.2.1]; exact h1b.1
  · rw [clientResult_bind, h1a.1, h1a.2.1]; exact h1b.2.1
  · refine validProg_bind h1a.2.2 ?_; rw [h1a.1, h1a.2.1]; exact h1b.2.2

/-- Precondition for `csrToFastGenProg` (`d = (wp, base)`). -/
private def CsrToFastPre (w : ℕ) (d : WhpParams × ℕ) (s : Memory.State) : Prop :=
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

private theorem realizes_csrToFastGen :
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
private theorem csrToFastGenProg_spec {c U V w n_max base : ℕ}
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
  obtain ⟨_, _, _, hbp_mono⟩ := backPrefix_spec (numBucketsWhp n_max) (capFrontWhp n_max)
    csr.fbStart
  obtain ⟨_, hbp_adj, _, _⟩ := backPrefix_spec (numBucketsWhp n_max) (capFrontWhp n_max)
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
  obtain ⟨hp1_st, hp1_res, hp1_vp⟩ :=
    csrToFastPart1Prog_eq henv hseed hrep hcsr hqv hgood hsalts_mem
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
  -- Offset bounds for framing `s_fin` back to `s_ffm` / `s_bab` / `s_ras` / `s`
  have hch := largeOffsetChain c U V w n_max
  have hbm_b : base + offBktMeta c U V w n_max + packedWords (16 * M) gBits w ≤
      base + largeSpaceWhp c U V w n_max := by dsimp only [M, gBits]; omega
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
  have hst_eq : (Memory.spec 0).clientState s
      (csrToFastGenProg (mkWhpParams c U V w n_max, base)) = s_fin := by
    unfold csrToFastGenProg; dsimp only
    simp only [pure_bind]
    rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1,
      clientState_bind, hp1_st, hp1_res,
      clientState_bind]
    dsimp only [cp] at hmr_st hmr_res ⊢
    rw [hmr_st, hmr_res, clientState_bind, hmh_st, hmh_res]
    dsimp only [mkHealRt, hlM, hlTcEntries]
    simp only [wp_large_offTrieChild0 hth, wp_large_offTrieChild1 hth,
      wp_large_offTrieMeta0 hth, wp_large_offTrieMeta1 hth]
    rw [clientState_bind, clientState_bind,
      clientState_bind]
    rfl
  refine ⟨?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · -- `SeedWhpMemRep`
    rw [hst_eq]
    refine SeedWhpMemRep.congr_hash hw (fun a ha1 ha2 => ?_) hseed_ras
    dsimp only [offHashBkt] at ha1
    exact (hfin_to_ras_nonBmBt a (by omega) (Or.inl (by omega))).symm
  · -- `FastMemRep` for `csrToFast c U n_max θ csr salts`
    rw [hst_eq]
    have hmt_pos : 1 ≤ maxTrieNodesWhp c n_max := by unfold maxTrieNodesWhp; omega
    dsimp only [FastMemRep, csrToFast]
    refine ⟨Nat.zero_le _, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    · -- quotArr & valArr
      intro i hi
      exact ⟨(readPacked_congr hw (hidx := hi) (fun a ⟨ha1, ha2⟩ =>
          hfin_to_ras_nonBmBt a (by omega) (Or.inl (by omega)))).trans (hqv_ras i hi).1,
        (readPacked_congr hw (hidx := hi) (fun a ⟨ha1, ha2⟩ =>
          hfin_to_ras_nonBmBt a (by omega) (Or.inl (by omega)))).trans (hqv_ras i hi).2⟩
    · -- locState
      intro b hb loc hloc
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
    · -- offBktMeta scalar fields `0 .. 9`
      intro b hb
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
    · -- backPtr
      intro b hb k hk
      exact (readPacked_congr hw (hidx := mul_add_lt_mul_bound hb hk) (fun a ⟨ha1, ha2⟩ =>
        hfin_to_ras_nonBmBt a (by omega) (Or.inr ⟨by omega, by
          dsimp only [M, cb, gBits] at hq_bm ha2; omega⟩))).trans (hbp_ras b hb k hk)
    · -- poolFreeStack & poolOwner
      intro j hj
      exact ⟨(readPacked_congr hw (hidx := hj) (fun a ⟨ha1, ha2⟩ =>
          hfin_to_ras_nonBmBt a (by omega) (Or.inr ⟨by omega, by
            dsimp only [gBits] at hq_bm ha2; omega⟩))).trans (hpool_ras j hj).1,
        (readPacked_congr hw (hidx := hj) (fun a ⟨ha1, ha2⟩ =>
          hfin_to_ras_nonBmBt a (by omega) (Or.inr ⟨by omega, by
            dsimp only [gBits] at hq_bm ha2; omega⟩))).trans (hpool_ras j hj).2⟩
    · -- BTreeSliceMemRep for all `sIdx < 3 * M`
      intro sIdx hsIdx
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
    · -- BufTrieMemRep 0 emptyBufTrie
      dsimp only [BufTrieMemRep, emptyBufTrie]
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
    · -- BufTrieMemRep 1 emptyBufTrie
      dsimp only [BufTrieMemRep, emptyBufTrie]
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
  · -- frontier
    rw [hst_eq]
    exact hfr_whd.trans (hfr_ztc.trans (hfr_ffm.trans (hfr_bab.trans hfr_ras)))
  · -- ValidProg
    unfold csrToFastGenProg; dsimp only
    simp only [pure_bind]
    rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
    refine validProg_bind hp1_vp ?_; rw [hp1_st, hp1_res]
    dsimp only [cp] at hmr_st hmr_res hmr_vp ⊢
    refine validProg_bind hmr_vp ?_; rw [hmr_st, hmr_res]
    refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
    dsimp only [mkHealRt, hlM, hlTcEntries]
    simp only [wp_large_offTrieChild0 hth, wp_large_offTrieChild1 hth,
      wp_large_offTrieMeta0 hth, wp_large_offTrieMeta1 hth]
    dsimp only [cp, rt, hrt, M] at hvp_bab hvp_ffm hvp_ztc hvp_whd ⊢
    refine validProg_bind hvp_bab ?_
    refine validProg_bind hvp_ffm ?_
    exact validProg_bind hvp_ztc hvp_whd
  · -- Footprint outside `[base, base + largeSpaceWhp)`
    rw [hst_eq]
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
@[irreducible] private def trySelfHealGenProg : WhpParams × ℕ → Memory.Prog Unit
  | d => do
    let one_v ← pure 1
    let ok ← checkGoodSeedOnStateGenProg d
    if ok = one_v then
      csrToFastGenProg d
    else
      pure ()

/-- Precondition for `trySelfHealGenProg` (`d = (wp, base)`). -/
private def TrySelfHealPre (w : ℕ) (d : WhpParams × ℕ) (s : Memory.State) : Prop :=
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (csr : CsrState) (dict : Dictionary.State U),
    WhpLargeEnv c U V w₀ n_max w d.2 ∧
    d.1 = mkWhpParams c U V w₀ n_max ∧
    SeedWhpMemRep d.2 c U w₀ n_max θ s.mem ∧
    CsrMemRep d.2 c U V w₀ n_max csr s.mem ∧
    ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict ∧
    (∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1)

private theorem realizes_trySelfHealGen :
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
private theorem trySelfHealGenProg_spec {c U V w n_max base : ℕ}
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
  set s1 := (Memory.spec 0).clientState s
    (checkGoodSeedOnStateGenProg (mkWhpParams c U V w n_max, base))
  dsimp only [trySelfHeal]
  unfold trySelfHealGenProg
  simp only [pure_bind]
  by_cases hok : (checkGoodSeedOnState c U n_max θ csr).1 = true
  · have hgood : GoodSeedOnState c U n_max θ dict :=
      (checkGoodSeedOnState_spec hcsr).1.mp hok
    obtain ⟨hcf_seed, hcf_rep, hcf_fr, hcf_vp, hcf_out⟩ :=
      csrToFastGenProg_spec henv hck_seed hck_rep hcsr hqv hgood hck_salts (s := s1)
    rw [hok] at hck_res ⊢
    simp only [↓reduceIte] at hck_res ⊢
    refine ⟨?_, ?_, ?_, fun a ha => ?_⟩
    · rw [clientState_bind, hck_res]; simp only [↓reduceIte]
      exact ⟨hth, hcf_seed, hcf_rep⟩
    · rw [clientState_bind, hck_res]; simp only [↓reduceIte]
      exact hcf_fr.trans hck_fr
    · refine validProg_bind hck_vp ?_; rw [hck_res]; simp only [↓reduceIte]; exact hcf_vp
    · rw [clientState_bind, hck_res]; simp only [↓reduceIte]
      exact (hcf_out a ha).trans (hck_out a ha)
  · have hok_f : (checkGoodSeedOnState c U n_max θ csr).1 = false := Bool.eq_false_iff.mpr hok
    rw [hok_f] at hck_res ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at hck_res ⊢
    refine ⟨?_, ?_, ?_, fun a ha => ?_⟩
    · rw [clientState_bind, hck_res]
      simp only [Nat.zero_ne_one, ↓reduceIte]
      exact ⟨hth, hck_seed, hck_rep⟩
    · rw [clientState_bind, hck_res]
      simp only [Nat.zero_ne_one, ↓reduceIte]; exact hck_fr
    · refine validProg_bind hck_vp ?_; rw [hck_res]
      simp only [Nat.zero_ne_one, ↓reduceIte]; exact validProg_pure _
    · rw [clientState_bind, hck_res]
      simp only [Nat.zero_ne_one, ↓reduceIte]; exact hck_out a ha

/-! ## Section 3: Top-Level `whpFastBranchCost` and `whpStepPureGenProg` -/

/-- `c`-only `memoryCost` upper bound on `whpStepPureGenProg` whenever `IsFastStepHit` holds
(`1` mode-word read plus `smallOpCostWhp c` or `fastOpCostWhp c`). -/
@[expose] def whpFastBranchCost (c : ℕ) : ℕ :=
  max (smallOpCostWhp c + 1) (fastOpCostWhp c + 1)

@[irreducible] private def fallbackAndHealGenProg :
    ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((wp_base, opTag), uv) => do
    let res ← csrStepOpGenProg ((wp_base, opTag), uv)
    trySelfHealGenProg wp_base
    pure res

private def FallbackAndHealPre (w : ℕ)
    (d : ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (csr : CsrState) (dict : Dictionary.State U)
      (op : Dynamic.Op U),
    WhpLargeEnv c U V w₀ n_max w d.1.1.2 ∧
    d.1.1.1 = mkWhpParams c U V w₀ n_max ∧
    SeedWhpMemRep d.1.1.2 c U w₀ n_max θ s.mem ∧
    CsrMemRep d.1.1.2 c U V w₀ n_max csr s.mem ∧
    ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict ∧
    (∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1) ∧
    Dynamic.valid V n_max dict op ∧
    encodeOpWhp op = (d.1.2, d.2)

private theorem realizes_fallbackAndHealGen :
    Realizes .exact fallbackAndHealGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      FallbackAndHealPre
      (fun _ _ => 0) := by
  unfold fallbackAndHealGenProg
  have hcs := realizes_csrStepOpGen
  have hsh := realizes_trySelfHealGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, opTag⟩, uv⟩
    dsimp only [FallbackAndHealPre] at h
    obtain ⟨c, U, V, w₀, n_max, θ, csr, dict, op, henv, rfl, hseed, hrep, hcsr, hqv,
      hval_op, hop_enc⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hnU := henv.2.2.2.2.1
    first
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | (have hop1 : (encodeOpWhp op).1 = opTag := congrArg Prod.fst hop_enc
       have hop2 : (encodeOpWhp op).2 = uv := congrArg Prod.snd hop_enc
       obtain ⟨hseed1, hrep1, _, _, _, _⟩ :=
         csrStepOpGenProg_spec henv hseed hrep hcsr op hval_op (s := s)
       obtain ⟨hcsr1, _, hqv1⟩ := csrStepOp_spec hnU θ.1 hcsr hqv hval_op
       rw [← hop1, ← hop2]
       exact ⟨c, U, V, w, n_max, θ, (csrStepOp c U n_max θ.1 csr op).1,
         (Dynamic.step dict op).1, henv, rfl, hseed1, hrep1, hcsr1, hqv1⟩)
  )

private theorem fallbackAndHealGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {csr : CsrState} {dict : Dictionary.State U}
    {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : CsrMemRep base c U V w n_max csr s.mem)
    (hcsr : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict)
    (hqv : ∀ p, csr.qArr p < 2 ^ quotBitsWhp U n_max ∧ csr.vArr p < max V 1)
    {op : Dynamic.Op U} (hval_op : Dynamic.valid V n_max dict op) :
    let enc := encodeOpWhp op
    let prog := fallbackAndHealGenProg (((mkWhpParams c U V w n_max, base), enc.1), enc.2)
    let s' := (Memory.spec 0).clientState s prog
    let pureOut := csrStepOp c U n_max θ.1 csr op
    WhpMemRep base c U V w n_max θ (trySelfHeal c U n_max θ pureOut.1) s'.mem ∧
    (Memory.spec 0).clientResult s prog = encodeOptRes pureOut.2 ∧
    s'.frontier = s.frontier ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    (∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → s'.mem a = s.mem a) := by
  have hnU := henv.2.2.2.2.1
  obtain ⟨hseed1, hrep1, hfr1, hres1, hvp1, hout1⟩ :=
    csrStepOpGenProg_spec henv hseed hrep hcsr op hval_op (s := s)
  obtain ⟨hcsr1, _, hqv1⟩ := csrStepOp_spec hnU θ.1 hcsr hqv hval_op
  set s1 := (Memory.spec 0).clientState s
    (csrStepOpGenProg (((mkWhpParams c U V w n_max, base), (encodeOpWhp op).1),
      (encodeOpWhp op).2))
  obtain ⟨hsh_rep, hsh_fr, hsh_vp, hsh_out⟩ :=
    trySelfHealGenProg_spec henv hseed1 hrep1 hcsr1 hqv1 (s := s1)
  dsimp only
  unfold fallbackAndHealGenProg
  refine ⟨?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · rw [clientState_bind, clientState_bind]
    exact hsh_rep
  · rw [clientResult_bind, clientResult_bind]
    exact hres1
  · rw [clientState_bind, clientState_bind]
    exact hsh_fr.trans hfr1
  · exact validProg_bind hvp1 (validProg_bind hsh_vp (validProg_pure _))
  · rw [clientState_bind, clientState_bind]
    exact (hsh_out a ha).trans (hout1 a ha)

/-- Top-level parameter-free `Memory.Prog` step dispatcher for `whpStepPure c U n_max θ st op`
across `.small`, `.fast`, and `.fallback` modes (`d = (((wp, base), opTag), (u_val, v_val))`). -/
@[irreducible] def whpStepPureGenProg :
    ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (((wp, base_in), opTag_in), uv_in) => do
    let base ← pure base_in
    let opTag ← pure opTag_in
    let uv ← pure uv_in
    let zero_v ← pure 0
    let one_v ← pure 1
    let mode ← Memory.read base
    if mode = zero_v then
      smallStepOpGenProg (((wp.1, base), opTag), uv)
    else if mode = one_v then
      let out ← fastStepPureGenProg ((wp, base), (opTag, uv))
      if out.1 = one_v then
        pure out.2
      else
        fastToCsrGenProg (wp.1, base)
        fallbackAndHealGenProg (((wp, base), opTag), uv)
    else
      fallbackAndHealGenProg (((wp, base), opTag), uv)

/-- Precondition for `whpStepPureGenProg` (`d = (((wp, base), opTag), (u_val, v_val))`). -/
@[expose] def WhpStepPurePre (w : ℕ)
    (d : ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let (p1, uv) := d
  let (p0, opTag) := p1
  let (wp, base) := p0
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (st : WhpDictState) (dict : Dictionary.State U)
      (op : Dynamic.Op U),
    0 < c ∧ 0 < w ∧ w = w₀ ∧ n_max ≤ U ∧ Fits w U ∧ Fits w V ∧
    Fits w (base + whpSpace c U V w₀ n_max) ∧
    wp = mkWhpParams c U V w₀ n_max ∧
    WhpMemRep base c U V w₀ n_max θ st s.mem ∧
    ValidWhpState c U V n_max θ st dict ∧
    Dynamic.valid V n_max dict op ∧
    encodeOpWhp op = (opTag, uv)

theorem realizes_whpStepPureGen :
    Realizes .exact whpStepPureGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      WhpStepPurePre
      (fun _ _ => 0) := by
  unfold whpStepPureGenProg
  have hsm := realizes_smallStepOpGen
  have hfs := realizes_fastStepPureGen
  have hfc := realizes_fastToCsrGen
  have hfh := realizes_fallbackAndHealGen
  have hcs_r : ∀ a s', (Memory.spec 0).clientState s' (Memory.read a) = s' := fun _ _ => rfl
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, opTag⟩, uv⟩
    dsimp only [WhpStepPurePre] at h
    obtain ⟨c, U, V, w₀, n_max, θ, st, dict, op,
      hc_pos, hw, hw_eq, hnU, hU, hV, hfit_sp, rfl, hrep, hv, hval_op, hop_enc⟩ := h
    subst hw_eq
    simp only [hcs_r] at *
    first
    | exact Nat.one_lt_two_pow hw.ne'
    | (cases st with
       | small sm =>
         obtain ⟨hsm_lt, hsm_rep⟩ := hrep
         have hsp_eq : whpSpace c U V w n_max = smallSpaceWhp U V w n_max := by
           unfold whpSpace; exact ite_eq_left hsm_lt
         have hm0 : s.mem base = 0 := by
           have hm := hsm_rep.1; dsimp only [hdrMode] at hm; rwa [Nat.add_zero] at hm
         have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
           unfold mkWhpParams; exact congrArg Prod.fst (ite_eq_left hsm_lt)
         have henv_sm : WhpSmallEnv c U V w n_max w base :=
           ⟨hc_pos, hw, rfl, hsm_lt, hnU, hU, hV, hfit_sp⟩
         first
         | (exfalso; omega)
         | (rw [hwp1]; exact ⟨c, U, V, w, n_max, henv_sm, rfl⟩)
       | fast fs =>
         obtain ⟨hth, hseed, hfs_rep⟩ := hrep
         have hsp_eq : whpSpace c U V w n_max = largeSpaceWhp c U V w n_max := by
           unfold whpSpace; exact ite_eq_right (Nat.not_lt.mpr hth)
         have hm1 : s.mem base = 1 := by
           have hm := hfs_rep.2.1; dsimp only [hdrMode] at hm; rwa [Nat.add_zero] at hm
         have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
           unfold mkWhpParams; rw [ite_eq_right (Nat.not_lt.mpr hth)]
         have henv_lg : WhpLargeEnv c U V w n_max w base :=
           ⟨hc_pos, hw, rfl, hth, hnU, hU, hV, hfit_sp⟩
         first
         | (exfalso; omega)
         | exact ⟨c, U, V, w, n_max, θ, fs, dict, op, henv_lg, rfl, hseed, hfs_rep, hv,
             hval_op, hop_enc⟩
         | (rw [hwp1]; exact ⟨c, U, V, w, n_max, henv_lg, rfl⟩)
         | (obtain ⟨_, _, hfs_m⟩ := fastStepPureGenProg_spec henv_lg hseed hfs_rep hv hval_op
              (s := s)
            cases hfsp : fastStepPure c U n_max θ fs op with
            | some p =>
              rw [hfsp] at hfs_m
              have hout1 : ((Memory.spec 0).clientResult s
                  (fastStepPureGenProg
                    ((mkWhpParams c U V w n_max, base), (opTag, uv)))).1 = 1 := by
                rw [← hop_enc, hfs_m.1]
              have hne1 : ((Memory.spec 0).clientResult s
                  (fastStepPureGenProg
                    ((mkWhpParams c U V w n_max, base), (opTag, uv)))).1 ≠ 1 := by assumption
              exact False.elim (hne1 hout1)
            | none =>
              rw [hfsp] at hfs_m
              have hs_eq : (Memory.spec 0).clientState s
                  (fastStepPureGenProg ((mkWhpParams c U V w n_max, base), (opTag, uv))) = s := by
                rw [← hop_enc]; exact hfs_m.2
              rw [hs_eq]
              simp only [Prod.mk.eta]
              rw [hwp1]
              obtain ⟨hseed_fc, hrep_fc, _, _, _⟩ := fastToCsrGenProg_spec henv_lg hseed hfs_rep
                hv (s := s)
              obtain ⟨hcsr_fc, hqv_fc⟩ := hv.fastToCsr_spec
              exact ⟨c, U, V, w, n_max, θ, fastToCsr n_max fs, dict, op, henv_lg, rfl,
                hseed_fc, hrep_fc, hcsr_fc, hqv_fc, hval_op, hop_enc⟩)
       | fallback csr =>
         obtain ⟨hth, hseed, hcsr_rep⟩ := hrep
         obtain ⟨_, hcsr, hqv⟩ := hv
         have hsp_eq : whpSpace c U V w n_max = largeSpaceWhp c U V w n_max := by
           unfold whpSpace; exact ite_eq_right (Nat.not_lt.mpr hth)
         have hm2 : s.mem base = 2 := by
           have hm := hcsr_rep.1; dsimp only [hdrMode] at hm; rwa [Nat.add_zero] at hm
         have henv_lg : WhpLargeEnv c U V w n_max w base :=
           ⟨hc_pos, hw, rfl, hth, hnU, hU, hV, hfit_sp⟩
         first
         | (exfalso; omega)
         | exact ⟨c, U, V, w, n_max, θ, csr, dict, op, henv_lg, rfl, hseed, hcsr_rep, hcsr, hqv,
             hval_op, hop_enc⟩)
  )

/-- Master `Memory.Prog` refinement and conditional `O_c(1)` `memoryCost` specification for
`whpStepPureGenProg`:
* For **every** seed `θ` and valid state `(st, dict)`, refines `whpStepPure c U n_max θ st op`,
  preserves `WhpMemRep` and `frontier`, satisfies `ValidProg` inside
  `[base, base + whpSpace c U V w n_max)`, and leaves caller memory outside
  `[base, base + whpSpace c U V w n_max)` untouched;
* Whenever `st = whpRunPure c U n_max θ ops_prev` and `IsFastStepHit c U n_max ops_prev op θ`
  holds, executes in at most `whpFastBranchCost c` (`O_c(1)`) worst-case memory operations. -/
theorem whpStepPureGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {st : WhpDictState} {dict : Dictionary.State U}
    {s : Memory.State}
    (hc : 0 < c) (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit_sp : Fits w (base + whpSpace c U V w n_max))
    (hrep : WhpMemRep base c U V w n_max θ st s.mem)
    (hv : ValidWhpState c U V n_max θ st dict)
    {op : Dynamic.Op U} (hval_op : Dynamic.valid V n_max dict op) :
    let enc := encodeOpWhp op
    let prog := whpStepPureGenProg (((mkWhpParams c U V w n_max, base), enc.1), enc.2)
    let s' := (Memory.spec 0).clientState s prog
    let pureOut := whpStepPure c U n_max θ st op
    WhpMemRep base c U V w n_max θ pureOut.1 s'.mem ∧
    (Memory.spec 0).clientResult s prog = encodeOptRes pureOut.2 ∧
    s'.frontier = s.frontier ∧
    ValidProg w (base + whpSpace c U V w n_max) s prog ∧
    (∀ a, (a < base ∨ base + whpSpace c U V w n_max ≤ a) → s'.mem a = s.mem a) ∧
    (∀ ops_prev : List (Dynamic.Op U),
      st = whpRunPure c U n_max θ ops_prev →
      IsFastStepHit c U n_max ops_prev op θ →
      memoryCost prog s ≤ whpFastBranchCost c) := by
  have hcs_r : (Memory.spec 0).clientState s (Memory.read base) = s := rfl
  have hcr_r : (Memory.spec 0).clientResult s (Memory.read base) = s.mem base := rfl
  have hmc_r : memoryCost (Memory.read base) s = 1 := rfl
  have hbase_lt : base < base + whpSpace c U V w n_max := by
    have h32 : 32 ≤ whpSpace c U V w n_max := by
      unfold whpSpace; split_ifs <;> [dsimp [smallSpaceWhp]; dsimp [largeSpaceWhp]] <;> omega
    omega
  dsimp only [whpFastBranchCost]
  cases st with
  | small sm =>
    obtain ⟨hsm_lt, hsm_rep⟩ := hrep
    have hsp_eq : whpSpace c U V w n_max = smallSpaceWhp U V w n_max := by
      unfold whpSpace; exact ite_eq_left hsm_lt
    have hm0 : s.mem base = 0 := by
      have hm := hsm_rep.1; dsimp only [hdrMode] at hm; rwa [Nat.add_zero] at hm
    have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      unfold mkWhpParams; exact congrArg Prod.fst (ite_eq_left hsm_lt)
    have henv_sm : WhpSmallEnv c U V w n_max w base :=
      ⟨hc, hw, rfl, hsm_lt, hnU, hU, hV, hfit_sp⟩
    obtain ⟨hsm_out_rep, hsm_fr, hsm_res, hsm_mc, hsm_vp, hsm_out⟩ :=
      smallStepOpGenProg_spec henv_sm hsm_rep hv.2 op hval_op (s := s)
    unfold whpStepPureGenProg
    simp only [pure_bind, hwp1]
    have hwhp_eq : whpStepPure c U n_max θ (.small sm) op =
        (let p := match op with
          | .query u => (sm, smallQuery n_max sm u.val)
          | .delete u => (smallDelete n_max sm u.val, none)
          | .insert u v => (smallInsert n_max sm u.val v, none)
         (.small p.1, p.2)) := by
      cases op <;> rfl
    rw [hwhp_eq]
    refine ⟨?_, ?_, ?_, ?_, fun a ha => ?_, fun _ _ _ => ?_⟩
    · rw [clientState_bind, hcs_r, hcr_r, hm0]; simp only [↓reduceIte]
      exact ⟨hsm_lt, hsm_out_rep⟩
    · rw [clientResult_bind, hcs_r, hcr_r, hm0]; simp only [↓reduceIte]
      exact hsm_res
    · rw [clientState_bind, hcs_r, hcr_r, hm0]; simp only [↓reduceIte]
      exact hsm_fr
    · refine validProg_bind (validProg_read hbase_lt) ?_
      rw [hcs_r, hcr_r, hm0]; simp only [↓reduceIte, hsp_eq]; exact hsm_vp
    · rw [clientState_bind, hcs_r, hcr_r, hm0]; simp only [↓reduceIte]
      rw [hsp_eq] at ha; exact hsm_out a ha
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hmc_r, hcs_r, hcr_r, hm0]; simp only [↓reduceIte]
      rw [Nat.add_comm 1]
      exact (Nat.add_le_add_right hsm_mc 1).trans (le_max_left _ _)
  | fast fs =>
    obtain ⟨hth, hseed, hfs_rep⟩ := hrep
    have hsp_eq : whpSpace c U V w n_max = largeSpaceWhp c U V w n_max := by
      unfold whpSpace; exact ite_eq_right (Nat.not_lt.mpr hth)
    have hm1 : s.mem base = 1 := by
      have hm := hfs_rep.2.1; dsimp only [hdrMode] at hm; rwa [Nat.add_zero] at hm
    have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      unfold mkWhpParams; rw [ite_eq_right (Nat.not_lt.mpr hth)]
    have henv_lg : WhpLargeEnv c U V w n_max w base :=
      ⟨hc, hw, rfl, hth, hnU, hU, hV, hfit_sp⟩
    obtain ⟨hfs_mc, hfs_vp, hfs_m⟩ :=
      fastStepPureGenProg_spec henv_lg hseed hfs_rep hv hval_op (s := s)
    have hop_eta : ((encodeOpWhp op).1, (encodeOpWhp op).2) = encodeOpWhp op := Prod.mk.eta
    unfold whpStepPureGenProg
    simp only [pure_bind, hop_eta, hwp1]
    dsimp only [whpStepPure]
    cases hfsp : fastStepPure c U n_max θ fs op with
    | some p =>
      rcases p with ⟨fs', res⟩
      rw [hfsp] at hfs_m
      dsimp only
      refine ⟨?_, ?_, ?_, ?_, fun a ha => ?_, fun _ _ _ => ?_⟩
      · rw [clientState_bind, hcs_r, hcr_r, hm1]
        simp only [Nat.one_ne_zero, ↓reduceIte]
        rw [clientState_bind, hfs_m.1]
        simp only [↓reduceIte]
        exact ⟨hth, hfs_m.2.2.1, hfs_m.2.2.2.1⟩
      · rw [clientResult_bind, hcs_r, hcr_r, hm1]
        simp only [Nat.one_ne_zero, ↓reduceIte]
        rw [clientResult_bind, hfs_m.1]; rfl
      · rw [clientState_bind, hcs_r, hcr_r, hm1]
        simp only [Nat.one_ne_zero, ↓reduceIte]
        rw [clientState_bind, hfs_m.1]; exact hfs_m.2.1
      · refine validProg_bind (validProg_read hbase_lt) ?_
        rw [hcs_r, hcr_r, hm1]; simp only [Nat.one_ne_zero, ↓reduceIte, hsp_eq]
        refine validProg_bind hfs_vp ?_; rw [hfs_m.1]; simp only [↓reduceIte]
        exact validProg_pure _
      · rw [clientState_bind, hcs_r, hcr_r, hm1]
        simp only [Nat.one_ne_zero, ↓reduceIte]
        rw [clientState_bind, hfs_m.1]; simp only [↓reduceIte]
        rw [hsp_eq] at ha; exact hfs_m.2.2.2.2 a ha
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hmc_r, hcs_r, hcr_r, hm1]
        simp only [Nat.one_ne_zero, ↓reduceIte, memoryCost_bind, hfs_m.1]
        have hmc_pure : memoryCost (pure (encodeOptRes res) : Memory.Prog (ℕ × ℕ))
            ((Memory.spec 0).clientState s
              (fastStepPureGenProg ((mkWhpParams c U V w n_max, base), encodeOpWhp op))) = 0 := rfl
        rw [hmc_pure, Nat.add_zero, Nat.add_comm 1]
        exact (Nat.add_le_add_right hfs_mc 1).trans (le_max_right _ _)
    | none =>
      rw [hfsp] at hfs_m
      dsimp only
      obtain ⟨hseed_fc, hrep_fc, hfr_fc, hvp_fc, hout_fc⟩ :=
        fastToCsrGenProg_spec henv_lg hseed hfs_rep hv (s := s)
      obtain ⟨hcsr_fc, hqv_fc⟩ := hv.fastToCsr_spec
      set s_fc := (Memory.spec 0).clientState s
        (fastToCsrGenProg (mkWhpCoreParams c U V w n_max, base))
      obtain ⟨hfh_rep, hfh_res, hfh_fr, hfh_vp, hfh_out⟩ :=
        fallbackAndHealGenProg_spec henv_lg hseed_fc hrep_fc hcsr_fc hqv_fc hval_op (s := s_fc)
      refine ⟨?_, ?_, ?_, ?_, fun a ha => ?_, fun ops_prev hst_run hhit => ?_⟩
      · rw [clientState_bind, hcs_r, hcr_r, hm1]
        simp only [Nat.one_ne_zero, ↓reduceIte]
        rw [clientState_bind, hfs_m.1, hfs_m.2]
        simp only [Nat.zero_ne_one, ↓reduceIte]
        rw [clientState_bind]; exact hfh_rep
      · rw [clientResult_bind, hcs_r, hcr_r, hm1]
        simp only [Nat.one_ne_zero, ↓reduceIte]
        rw [clientResult_bind, hfs_m.1, hfs_m.2]
        simp only [Nat.zero_ne_one, ↓reduceIte]
        rw [clientResult_bind]; exact hfh_res
      · rw [clientState_bind, hcs_r, hcr_r, hm1]
        simp only [Nat.one_ne_zero, ↓reduceIte]
        rw [clientState_bind, hfs_m.1, hfs_m.2]
        simp only [Nat.zero_ne_one, ↓reduceIte]
        rw [clientState_bind]; exact hfh_fr.trans hfr_fc
      · refine validProg_bind (validProg_read hbase_lt) ?_
        rw [hcs_r, hcr_r, hm1]; simp only [Nat.one_ne_zero, ↓reduceIte, hsp_eq]
        refine validProg_bind hfs_vp ?_; rw [hfs_m.1, hfs_m.2]
        simp only [Nat.zero_ne_one, ↓reduceIte]
        exact validProg_bind hvp_fc hfh_vp
      · rw [clientState_bind, hcs_r, hcr_r, hm1]
        simp only [Nat.one_ne_zero, ↓reduceIte]
        rw [clientState_bind, hfs_m.1, hfs_m.2]
        simp only [Nat.zero_ne_one, ↓reduceIte]
        rw [clientState_bind]
        rw [hsp_eq] at ha; exact (hfh_out a ha).trans (hout_fc a ha)
      · dsimp only [IsFastStepHit] at hhit
        rw [← hst_run] at hhit; dsimp only at hhit
        rw [hfsp] at hhit; cases hhit
  | fallback csr =>
    obtain ⟨hth, hseed, hcsr_rep⟩ := hrep
    obtain ⟨_, hcsr, hqv⟩ := hv
    have hsp_eq : whpSpace c U V w n_max = largeSpaceWhp c U V w n_max := by
      unfold whpSpace; exact ite_eq_right (Nat.not_lt.mpr hth)
    have hm2 : s.mem base = 2 := by
      have hm := hcsr_rep.1; dsimp only [hdrMode] at hm; rwa [Nat.add_zero] at hm
    have henv_lg : WhpLargeEnv c U V w n_max w base :=
      ⟨hc, hw, rfl, hth, hnU, hU, hV, hfit_sp⟩
    obtain ⟨hfh_rep, hfh_res, hfh_fr, hfh_vp, hfh_out⟩ :=
      fallbackAndHealGenProg_spec henv_lg hseed hcsr_rep hcsr hqv hval_op (s := s)
    unfold whpStepPureGenProg
    simp only [pure_bind]
    dsimp only [whpStepPure]
    refine ⟨?_, ?_, ?_, ?_, fun a ha => ?_, fun ops_prev hst_run hhit => ?_⟩
    · rw [clientState_bind, hcs_r, hcr_r, hm2]
      simp only [show ¬((2 : ℕ) = 0) by decide, show ¬((2 : ℕ) = 1) by decide, ↓reduceIte]
      exact hfh_rep
    · rw [clientResult_bind, hcs_r, hcr_r, hm2]
      simp only [show ¬((2 : ℕ) = 0) by decide, show ¬((2 : ℕ) = 1) by decide, ↓reduceIte]
      exact hfh_res
    · rw [clientState_bind, hcs_r, hcr_r, hm2]
      simp only [show ¬((2 : ℕ) = 0) by decide, show ¬((2 : ℕ) = 1) by decide, ↓reduceIte]
      exact hfh_fr
    · refine validProg_bind (validProg_read hbase_lt) ?_
      rw [hcs_r, hcr_r, hm2]
      simp only [show ¬((2 : ℕ) = 0) by decide, show ¬((2 : ℕ) = 1) by decide, ↓reduceIte, hsp_eq]
      exact hfh_vp
    · rw [clientState_bind, hcs_r, hcr_r, hm2]
      simp only [show ¬((2 : ℕ) = 0) by decide, show ¬((2 : ℕ) = 1) by decide, ↓reduceIte]
      rw [hsp_eq] at ha; exact hfh_out a ha
    · dsimp only [IsFastStepHit] at hhit
      rw [← hst_run] at hhit; exact False.elim hhit

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
