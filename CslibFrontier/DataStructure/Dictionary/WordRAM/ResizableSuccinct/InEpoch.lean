/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.MetaSync
public import CslibFrontier.Computability.WordRAM.Resizable.Basic
import Mathlib.Tactic.Ring

/-!
# In-Epoch Resizable Succinct Compacted Representation and Primitives

This module formalizes the compacted epoch representation and live invariants of the resizable
succinct dynamic dictionary on the word-granular **Resizable Word RAM** (`Cslib.WordRAM.Resizable`).

It establishes:
1. **Static `1 · OPT` compacted epoch footprint bounds** (`compactedEpochWords_le_succinctWords`,
   `w_mul_compactedEpochWords_le_bits`): under `EpochValid U n N`, the live compacted epoch
   footprint formula is at most `Dynamic.succinctWords 1355 441 U V w n` words (`1 · OPT`,
   never `2 · OPT`). The constant `1355` decomposes algebraically as `11 + 1344`, where
   `11 = 5 + 6` bounds the quotient-bit slack (5 from Feistel quotient/val vs `optBits` and
   6 from `quotientBits U N ≤ quotientBits U n + 6` via `N ≤ 4 * n`), and `1344 = 16 * 84`
   bounds the `84 * N * logLogFactor N` metadata arrays via `N ≤ 4 * n` and
   `logLogFactor N ≤ 4 * logLogFactor n`.
2. **Dense key reconstruction and live representation invariants** (`reconstructKeyAt_spec`,
   `CompactedSplitRep`, `CompactedRep`, `compactedRep_empty`): every dense slot $d < n$
   reconstructs a live $(u, v)$ in $s_{\mathrm{abs}}$ injectively and surjectively.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompactedSplitRep`:
  active epoch representation at arbitrary `(metaBase, itemBase)`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompactedRep`:
  live resting invariant on `RData r` at `frontier = base + compactedEpochWords`.

## Main results

* `compactedEpochWords_le_succinctWords`: live epoch words bounded by succinct words.
* `w_mul_compactedEpochWords_le_bits`: word-multiplied `1 · OPT` bit-space bound.
* `reconstructKeyAt_spec`: exact bijective key/value reconstruction on live dense slots.
* `compactedRep_empty`: initial empty dictionary representation certificate.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4 and 6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select*, SODA 2026,
  Section 5.1][KuszmaulLiangZhou2026]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM
open scoped BigOperators ENNReal

/-! ## Section 1: Compacted Epoch `1 · OPT` Word-Space and Bit-Space Bounds -/

private theorem compactedEpochWords_pos_le_div_add {U V w N n : ℕ}
    (hw : 0 < w) (hNU : N ≤ U) (hU : U ≤ 2 ^ w) :
    offCompItems U w N + compactedItemWords U V w N n ≤
      (n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N +
        globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N +
        (2 * N) * 1 + w - 1) / w + 441 := by
  have hlm_eq : 9 * totalMicroBuckets N = localMetaLen N := by
    unfold localMetaLen effBucketCap totalMicroBuckets totalMicroBits numBuckets numMicroPerBucket
    rw [Nat.pow_add]; ring
  have hh := hashSpace_le hw hNU hU
  have h1 := div_add_mul_packedWords_le 9
    (n * (quotientBits U N + valBits V)) 2 (totalMicroBuckets N) (effBucketPosBits N) w
  rw [hlm_eq] at h1
  have h2 := div_add_packedWords_le
    (n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N) 29
    (globalMetaLen N) (globalPtrBits N) w
  have h3 := div_add_mul_packedWords_le 2
    (n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N +
      globalMetaLen N * globalPtrBits N) 32 (maxTailItems N) (globalPtrBits N) w
  have h4 := div_add_packedWords_le
    (n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N +
      globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N) 38
    (2 * N) 1 w
  unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords
    epochHashSpace epochQBits epochHashB lmSubWords compactedItemWords
  unfold hashSpace qBits hashB at hh
  omega

/-- **Static `1 · OPT` word-space bound (`compactedEpochWords_le_succinctWords`):**
whenever `EpochValid U n N` (`n = 0 ∧ N = 0` or `1 ≤ n ≤ N ≤ 4 * n ∧ N ≤ U`), the live compacted
footprint `compactedEpochWords U V w N n` is at most `Dynamic.succinctWords 1355 441 U V w n`. -/
theorem compactedEpochWords_le_succinctWords {U V w N n : ℕ}
    (hw : 0 < w) (hU : Fits w U) (_hU_pos : 0 < U) (_hV_pos : 0 < V) (hev : EpochValid U n N) :
    compactedEpochWords U V w N n ≤ Dynamic.succinctWords 1355 441 U V w n := by
  rcases hev with ⟨rfl, rfl⟩ | ⟨_, hnN, hN4, hNU⟩
  · simp only [compactedEpochWords, rootHdrWords, Dynamic.succinctWords, ↓reduceIte]
    exact (by decide : 8 ≤ 441).trans (Nat.le_add_left 441 _)
  · rw [compactedEpochWords, ite_eq_right (by omega)]
    have hbase := compactedEpochWords_pos_le_div_add (V := V) (n := n) hw hNU hU.le
    have hq6 := quotientBits_le_add_six_of_le_four_mul U hnN hN4
    have hqv_opt := quotient_val_bits_le_optBits (U := U) (V := V) (n := n)
    have hll_n := Dynamic.one_le_logLogFactor n
    have hll_N : Dynamic.logLogFactor N ≤ 4 * Dynamic.logLogFactor n :=
      (Dynamic.logLogFactor_mono hN4).trans (Dynamic.logLogFactor_four_mul_le n)
    have hlm := localMetaLen_mul_effBucketPosBits_le N
    have hgm := globalMetaLen_mul_globalPtrBits_le N
    have htail := maxTailItems_mul_globalPtrBits_le N
    have hitem_bits :
        n * (quotientBits U N + valBits V) ≤
          Dynamic.optBits U V n + 11 * n * Dynamic.logLogFactor n := by
      calc n * (quotientBits U N + valBits V)
          ≤ n * (quotientBits U n + 6 + valBits V) := Nat.mul_le_mul_left n (by omega)
        _ = n * (quotientBits U n + valBits V) + 6 * n := by ring
        _ ≤ (Dynamic.optBits U V n + 5 * n * Dynamic.logLogFactor n) +
              6 * n * Dynamic.logLogFactor n :=
            Nat.add_le_add hqv_opt (Nat.le_mul_of_pos_right _ hll_n)
        _ = Dynamic.optBits U V n + 11 * n * Dynamic.logLogFactor n := by ring
    have hmeta_bits :
        localMetaLen N * effBucketPosBits N + globalMetaLen N * globalPtrBits N +
          (2 * maxTailItems N) * globalPtrBits N + (2 * N) * 1 ≤
          1344 * n * Dynamic.logLogFactor n := by
      have h10N : (2 * maxTailItems N) * globalPtrBits N + (2 * N) * 1 ≤
          10 * N * Dynamic.logLogFactor N := by
        calc (2 * maxTailItems N) * globalPtrBits N + (2 * N) * 1
            = 2 * (maxTailItems N * globalPtrBits N) + 2 * N := by ring
          _ ≤ 2 * (4 * N) + 2 * N := Nat.add_le_add (Nat.mul_le_mul_left 2 htail) le_rfl
          _ = 10 * N := by ring
          _ ≤ 10 * N * Dynamic.logLogFactor N :=
              Nat.le_mul_of_pos_right _ (Dynamic.one_le_logLogFactor N)
      calc localMetaLen N * effBucketPosBits N + globalMetaLen N * globalPtrBits N +
            (2 * maxTailItems N) * globalPtrBits N + (2 * N) * 1
          ≤ 54 * N * Dynamic.logLogFactor N + 20 * N * Dynamic.logLogFactor N +
              10 * N * Dynamic.logLogFactor N := by omega
        _ = 84 * (N * Dynamic.logLogFactor N) := by ring
        _ ≤ 84 * ((4 * n) * (4 * Dynamic.logLogFactor n)) :=
            Nat.mul_le_mul_left 84 (Nat.mul_le_mul hN4 hll_N)
        _ = 1344 * n * Dynamic.logLogFactor n := by ring
    have hnum :
        n * (quotientBits U N + valBits V) + localMetaLen N * effBucketPosBits N +
          globalMetaLen N * globalPtrBits N + (2 * maxTailItems N) * globalPtrBits N +
          (2 * N) * 1 + w - 1 ≤
        Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + w - 1 :=
      Nat.sub_le_sub_right (by linarith only [hitem_bits, hmeta_bits]) 1
    have hdiv := Nat.div_le_div_right (c := w) hnum
    simp only [Dynamic.succinctWords]; omega

/-- **Static `1 · OPT` bit-space bound (`w_mul_compactedEpochWords_le_bits`):**
multiplying `compactedEpochWords U V w N n` by `w` yields at most
`Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + 442 * w` bits across every valid
epoch (`EpochValid U n N`). -/
theorem w_mul_compactedEpochWords_le_bits {U V w N n : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hU_pos : 0 < U) (hV_pos : 0 < V) (hev : EpochValid U n N) :
    w * compactedEpochWords U V w N n ≤
      Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + 442 * w := by
  calc w * compactedEpochWords U V w N n
      ≤ w * Dynamic.succinctWords 1355 441 U V w n :=
        Nat.mul_le_mul_left w (compactedEpochWords_le_succinctWords hw hU hU_pos hV_pos hev)
    _ ≤ Dynamic.optBits U V n + 1355 * n * Dynamic.logLogFactor n + (441 + 1) * w :=
        succinctWords_mul_w_le_bits 1355 441 U V w n

/-! ## Section 2: Key Reconstruction and Compacted Representation Invariants -/

/-- Every dense slot `d < n` reconstructs a live `(u, v)` in `s_abs`
injectively and surjectively. -/
theorem reconstructKeyAt_spec {metaBase itemBase U V w N n : ℕ} {θ : QuotHashSeed U N}
    {s_abs : Dictionary.State U} {s_fix s : Memory.State}
    (hvals : Dictionary.ValuesBounded V s_abs) (hNU : N ≤ U)
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s)
    (hn : totalSlots N (compGmAt metaBase U w N s.mem) = n) :
    (∀ d < n, ∃ hu : reconstructKeyAt metaBase itemBase U V w N n θ s.mem d < U,
      s_abs ⟨reconstructKeyAt metaBase itemBase U V w N n θ s.mem d, hu⟩ =
        some (compValAt itemBase U V w N n s.mem d) ∧
      compValAt itemBase U V w N n s.mem d < V) ∧
    (∀ d₁ < n, ∀ d₂ < n,
      reconstructKeyAt metaBase itemBase U V w N n θ s.mem d₁ =
      reconstructKeyAt metaBase itemBase U V w N n θ s.mem d₂ → d₁ = d₂) ∧
    (∀ u : Fin U, (s_abs u).isSome →
      ∃ d < n, reconstructKeyAt metaBase itemBase U V w N n θ s.mem d = u.val) := by
  obtain ⟨L, hbucket⟩ := hinv.hbucket
  set gm := compGmAt metaBase U w N s.mem
  set td := compTDAt metaBase U w N s.mem
  set dt := compDTAt metaBase U w N s.mem
  set wg := ghostW w
  have hgm_eq : gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem = gm := hcpl.gm_eq.symm
  have hslot : SlotStoreInv N gm := hgm_eq ▸ hbucket.hslot
  have htd : 0 < bucketBits N → TailDenseInv N (gm 0) (gm 1) td dt := fun hb => by
    have hwin := hcpl.win_inv; simp only [Nat.ne_of_gt hb, ↓reduceIte] at hwin; exact hwin
  have hqv_slot {d b j} (hd : d < totalSlots N gm)
      (hphys : physOfDense N gm dt d = slotOf N gm b j) :
      compQuotAt itemBase U V w N n s.mem d =
        quotAt 0 U wg N (hashSpace U wg N) s_fix.mem
          (slotOf N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b j) ∧
      compValAt itemBase U V w N n s.mem d =
        valAt 0 U V wg N (hashSpace U wg N) s_fix.mem
          (slotOf N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b j) := by
    rw [← hn, hgm_eq, ← hphys]
    exact ⟨hcpl.quot_eq d hd, hcpl.val_eq d hd⟩
  have howner : ∀ d < n,
      let b := ownerBucketOfDense N gm dt d
      let j := logicalIdxOfDense N gm dt d
      let key := reconstructKeyAt metaBase itemBase U V w N n θ s.mem d
      b < numBuckets N ∧
      j < bCount N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b ∧
      denseOfPhys N gm td (slotOf N gm b j) = d ∧
      feistelBucket (bucketBits N) (hValOfSeed U N θ) key = b ∧
      keyQuotient (bucketBits N) key = compQuotAt itemBase U V w N n s.mem d ∧
      compQuotAt itemBase U V w N n s.mem d =
        quotAt 0 U wg N (hashSpace U wg N) s_fix.mem
          (slotOf N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b j) ∧
      compValAt itemBase U V w N n s.mem d =
        valAt 0 U V wg N (hashSpace U wg N) s_fix.mem
          (slotOf N (gmAt 0 U V wg N (hashSpace U wg N) s_fix.mem) b j) := fun d hd => by
    have hd_tot : d < totalSlots N gm := hn ▸ hd
    obtain ⟨hb_lt, hj_lt, hd_eq⟩ := ownerBucketOfDense_lt_and_slotOf hslot htd hd_tot
    obtain ⟨hq_d, hv_d⟩ := hqv_slot hd_tot (physOfDense_eq_slotOf_owner hslot htd hd_tot)
    obtain ⟨hfb_b, hfb_q⟩ := feistelBucket_feistelReconstruct (hValOfSeed U N θ) hb_lt
      (compQuotAt itemBase U V w N n s.mem d)
    exact ⟨hb_lt, hgm_eq.symm ▸ hj_lt, hd_eq, hfb_b, hfb_q, hq_d, hv_d⟩
  refine ⟨fun d hd => ?_, fun d₁ hd₁ d₂ hd₂ heq => ?_, fun u hu => ?_⟩
  · obtain ⟨hb_lt, hj_lt, -, -, -, hq_d, hv_d⟩ := howner d hd
    have hmap := hbucket.hmap_some _ hb_lt _ hj_lt
    rw [← hq_d, ← hv_d] at hmap; unfold bucketMapOfState at hmap
    split_ifs at hmap with hcond
    exact ⟨hcond.1, hmap, hvals _ _ hmap⟩
  · obtain ⟨hb₁_lt, hj₁_lt, hd₁_eq, hfb₁_b, hfb₁_q, hq₁, -⟩ := howner d₁ hd₁
    obtain ⟨-, hj₂_lt, hd₂_eq, hfb₂_b, hfb₂_q, hq₂, -⟩ := howner d₂ hd₂
    have hb_eq : ownerBucketOfDense N gm dt d₁ = ownerBucketOfDense N gm dt d₂ := by
      rw [← hfb₁_b, heq, hfb₂_b]
    have hq_eq : compQuotAt itemBase U V w N n s.mem d₁ =
        compQuotAt itemBase U V w N n s.mem d₂ := by rw [← hfb₁_q, heq, hfb₂_q]
    have hj_eq := hbucket.hnodup_q _ hb₁_lt _ hj₁_lt _ (hb_eq ▸ hj₂_lt)
      (by rw [← hq₁, hb_eq, ← hq₂, hq_eq])
    rw [← hd₁_eq, ← hd₂_eq, hb_eq, hj_eq]
  · set b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val
    set q := keyQuotient (bucketBits N) u.val
    have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) (hValOfSeed U N θ) u.val
    have hbm_eq := bucketMapOfState_feistelBucket hNU (hValOfSeed U N θ) s_abs u
    obtain ⟨j, hj_lt', hq_j⟩ := (hbucket.hmap_dom b hb_lt q).mp (by rwa [hbm_eq])
    have hj_lt : j < bCount N gm b := hgm_eq ▸ hj_lt'
    obtain ⟨hd_lt, hb_inv, _⟩ := denseOfPhys_slotOf_lt_and_inv hslot htd hb_lt hj_lt
    have hq_d := (hqv_slot hd_lt (physOfDense_denseOfPhys_slotOf hslot htd hb_lt hj_lt)).1
    refine ⟨_, hd_lt.trans_eq hn, ?_⟩
    unfold reconstructKeyAt; dsimp only
    rw [hb_inv, hq_d, hq_j]
    exact feistelReconstruct_feistelBucket (bucketBits N) (hValOfSeed U N θ) u.val

/-- Active compacted epoch invariant at arbitrary `(metaBase, itemBase)` (`s : Memory.State`). -/
structure CompactedSplitRep (metaBase itemBase U V w N n n_init : ℕ)
    (θ : QuotHashSeed U N) (s_abs : Dictionary.State U) (s : Memory.State) : Prop where
  root_hdr : RootHeaderValid U V w N n n_init metaBase s.mem
  params_stored : EpochParamsStored U V w N metaBase s.mem
  hash_rep : ReducedKWise.Rep (metaBase + epochHdrWords) w (qBits U N) (hashB N)
    (totalMicroBits N) 3 θ s.mem
  card_eq : (Dictionary.dom s_abs).card = n
  vals_lt : Dictionary.ValuesBounded V s_abs
  coupled : ∃ s_fix : Memory.State,
    DictStateInv U V (ghostW w) N 0 θ s_abs s_fix ∧
    totalSlots N (compGmAt metaBase U w N s.mem) = n ∧
    FixedCoupled metaBase itemBase U V w N s_fix s

/-- Live resting representation invariant on `RData r` (`metaBase = base`, exact `x.frontier`). -/
structure CompactedRep {r : ℕ} (U V w N n n_init base : ℕ)
    (s_abs : Dictionary.State U) (x : RData r) : Prop where
  bounded : x.Bounded w
  frontier_eq : x.frontier = base + compactedEpochWords U V w N n
  root_hdr : RootHeaderValid U V w N n n_init base x.mem
  fits_U : Fits w U
  pos_U : 0 < U
  pos_V : 0 < V
  card_eq : (Dictionary.dom s_abs).card = n
  vals_lt : Dictionary.ValuesBounded V s_abs
  epoch_inv : EpochValid U n N
  active_inv : 0 < n → ∃ θ : QuotHashSeed U N,
    CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩

/-- An empty dictionary state (`n = 0`, `N = 0`) satisfies `CompactedRep`. -/
theorem compactedRep_empty {r : ℕ} {U V w base : ℕ} {x : RData r}
    (hx : x.Bounded w) (hfr : x.frontier = base + 8)
    (hhdr : RootHeaderValid U V w 0 0 0 base x.mem) :
    CompactedRep U V w 0 0 0 base (Dictionary.empty U) x :=
  ⟨hx, by simp [compactedEpochWords, rootHdrWords, hfr], hhdr, hhdr.fits_U, hhdr.pos_U, hhdr.pos_V,
    by simp only [Dictionary.dom_empty, Finset.card_empty], (fun _ _ h => nomatch h),
    Or.inl ⟨rfl, rfl⟩, fun hn0 => (Nat.not_lt_zero 0 hn0).elim⟩

/-- An active compacted epoch split representation yields a resting `CompactedRep`. -/
theorem compactedRep_of_split {r : ℕ} {U V w N n n_init base : ℕ} {θ : QuotHashSeed U N}
    {s_abs : Dictionary.State U} {x : RData r}
    (hx : x.Bounded w)
    (hfr : x.frontier = base + compactedEpochWords U V w N n)
    (hepoch : EpochValid U n N)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩) :
    CompactedRep U V w N n n_init base s_abs x :=
  ⟨hx, hfr, hsplit.root_hdr, hsplit.root_hdr.fits_U, hsplit.root_hdr.pos_U, hsplit.root_hdr.pos_V,
    hsplit.card_eq, hsplit.vals_lt, hepoch, fun _ => ⟨θ, hsplit⟩⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
