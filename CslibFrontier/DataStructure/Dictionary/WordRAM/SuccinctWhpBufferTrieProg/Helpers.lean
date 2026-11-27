/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Rt
import CslibFrontier.Tactic.Realize

/-!
# Shared Internal `BufRt` Accessors, Safety Lemmas, and Frame Bridges

Internal module imported privately by `SuccinctWhpBufferTrieProg` submodules; never re-exported
through the public facade.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.mkBufRtGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufReadItemPairRtProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_mkBufRtGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.mkBufRtGenProg_spec`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufTrieMemRep_iff_rt`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufReadItemPairRt`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Finset
open scoped BigOperators
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

theorem laneGet_zero_eq_mod (bChar r : ℕ) :
    laneGet bChar r 0 = r % 2 ^ bChar := by
  rw [laneGet_eq_div_mod, Nat.zero_mul, pow_zero, Nat.div_one]

private theorem laneGet_succ_eq (bChar r off : ℕ) :
    laneGet bChar r (off + 1) = laneGet bChar (r / 2 ^ bChar) off := by
  rw [laneGet_eq_div_mod, laneGet_eq_div_mod, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 2
  ring

/-- Shift-offset invariance of `bufWalk`: stepping `off + 1` is identical to shifting `r` right by
`bChar` and stepping `off`. -/
theorem bufWalk_add_off (bChar : ℕ) (child : ℕ → ℕ → ℕ) :
    ∀ rem off r cur,
      bufWalk bChar child r rem (off + 1) cur =
        bufWalk bChar child (r / 2 ^ bChar) rem off cur := by
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro off r cur
    dsimp only [bufWalk]
    rw [laneGet_succ_eq]
    split_ifs with h0
    · rfl
    · exact ih (off + 1) r _

/-- Shift-offset invariance of `bufEnsurePath`: stepping `off + 1` is identical to shifting `r`
right by `bChar` and stepping `off`. -/
theorem bufEnsurePath_add_off (bChar : ℕ) :
    ∀ rem off r tr cur,
      bufEnsurePath bChar r rem (off + 1) tr cur =
        bufEnsurePath bChar (r / 2 ^ bChar) rem off tr cur := by
  intro rem
  induction rem with
  | zero => intros; rfl
  | succ rem ih =>
    intro off r tr cur
    dsimp only [bufEnsurePath]
    rw [laneGet_succ_eq]
    split_ifs with h0
    · exact ih (off + 1) r _ _
    · exact ih (off + 1) r _ _

/-- Unique `(v, c)` decomposition of `v * 2 ^ bChar + c` when `c < 2 ^ bChar`. -/
theorem child_idx_eq_iff {bChar v₁ c₁ v₂ c₂ : ℕ}
    (hc₁ : c₁ < 2 ^ bChar) (hc₂ : c₂ < 2 ^ bChar) :
    v₁ * 2 ^ bChar + c₁ = v₂ * 2 ^ bChar + c₂ ↔ v₁ = v₂ ∧ c₁ = c₂ := by
  constructor
  · intro heq
    have hpos : 0 < 2 ^ bChar := Nat.two_pow_pos bChar
    have hv : v₁ = v₂ := by
      have hd₁ : (v₁ * 2 ^ bChar + c₁) / 2 ^ bChar = v₁ := by
        rw [Nat.mul_comm v₁ (2 ^ bChar), Nat.mul_add_div hpos, Nat.div_eq_of_lt hc₁, Nat.add_zero]
      have hd₂ : (v₂ * 2 ^ bChar + c₂) / 2 ^ bChar = v₂ := by
        rw [Nat.mul_comm v₂ (2 ^ bChar), Nat.mul_add_div hpos, Nat.div_eq_of_lt hc₂, Nat.add_zero]
      rw [← hd₁, heq, hd₂]
    exact ⟨hv, by subst hv; omega⟩
  · rintro ⟨rfl, rfl⟩; rfl


/-- Base word address in `BufRt`. -/
@[expose] def brBase (rt : BufRt) : ℕ := rt.1.1.1
/-- Machine word width in `BufRt`. -/
@[expose] def brW (rt : BufRt) : ℕ := rt.1.1.2
/-- Global pointer bit-width in `BufRt`. -/
@[expose] def brGBits (rt : BufRt) : ℕ := rt.1.2.1
/-- Character bit-width in `BufRt`. -/
@[expose] def brBChar (rt : BufRt) : ℕ := rt.1.2.2
/-- Character alphabet size `2 ^ bChar` in `BufRt`. -/
@[expose] def brPowBChar (rt : BufRt) : ℕ := rt.2.1.1.1
/-- Character mask `2 ^ bChar - 1` in `BufRt`. -/
@[expose] def brMaskBChar (rt : BufRt) : ℕ := rt.2.1.1.2
/-- Constant trie depth `cTab` in `BufRt`. -/
@[expose] def brCTab (rt : BufRt) : ℕ := rt.2.1.2.1
/-- Epoch capacity `qEpoch` in `BufRt`. -/
@[expose] def brQEp (rt : BufRt) : ℕ := rt.2.1.2.2
/-- Maximum trie node capacity `maxTrieNodesWhp` in `BufRt`. -/
@[expose] def brMaxNodes (rt : BufRt) : ℕ := rt.2.2.1.1

/-- Parameter-free `BufRt` envelope in the large regime. -/
@[expose] def BufRtEnvGen (w : ℕ) (rt : BufRt) : Prop :=
  ∃ c U V w₀ n_max base ep,
    WhpLargeEnv c U V w₀ n_max w base ∧ (ep = 0 ∨ ep = 1) ∧
    rt = mkBufRt c U V w₀ n_max base ep

/-- Extract `BufRt` from `((cp, base), ep)` in zero memory operations. -/
def mkBufRtGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog BufRt
  | ((cp, base_in), ep) => do
    let base ← pure base_in
    if ep = 0 then
      pure (((base, wpW cp), (wpGlobalPtrBits cp, wpBChar cp)),
        (((wpPowBChar cp, wpMaskBChar cp), (wpCTab cp, wpQEpoch cp)),
         ((wpMaxTrieNodes cp, wpOffTrieChild0 cp),
          ((wpOffTrieMeta0 cp, wpOffTrieItems0 cp),
           (hdrBuf0NodeAlloc, hdrBuf0ItemAlloc)))))
    else
      pure (((base, wpW cp), (wpGlobalPtrBits cp, wpBChar cp)),
        (((wpPowBChar cp, wpMaskBChar cp), (wpCTab cp, wpQEpoch cp)),
         ((wpMaxTrieNodes cp, wpOffTrieChild1 cp),
          ((wpOffTrieMeta1 cp, wpOffTrieItems1 cp),
           (hdrBuf1NodeAlloc, hdrBuf1ItemAlloc)))))

theorem mkBufRtGenProg_spec {c U V w n_max base ep : ℕ} (hth : whpThreshold c ≤ n_max)
    (s : Memory.State) :
    let prog := mkBufRtGenProg ((mkWhpCoreParams c U V w n_max, base), ep)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = mkBufRt c U V w n_max base ep ∧
    memoryCost prog s = 0 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  unfold mkBufRtGenProg mkBufRt
  simp only [pure_bind, wp_large_w hth, wp_large_globalPtrBits hth, wp_large_bChar hth,
    wp_large_powBChar hth, wp_large_maskBChar hth, wp_large_cTab hth, wp_large_qEpoch hth,
    wp_large_maxTrieNodes hth, wp_large_offTrieChild0 hth, wp_large_offTrieChild1 hth,
    wp_large_offTrieMeta0 hth, wp_large_offTrieMeta1 hth, wp_large_offTrieItems0 hth,
    wp_large_offTrieItems1 hth]
  split_ifs with h0 <;> exact ⟨rfl, rfl, rfl, validProg_pure _⟩

theorem realizes_mkBufRtGen :
    Realizes .exact mkBufRtGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := BufRt))
      (fun w ((cp, base), _) _ => WhpLargeEnvGen w cp base)
      (fun _ _ => 0) := by
  realize
  all_goals
    rcases d with ⟨⟨cp, base⟩, ep⟩
    obtain ⟨c, U, V, w₀, n_max, henv, rfl⟩ := h
    exact henv.fits_const (by decide)

section RtSafety

variable {c U V w₀ n_max w base ep : ℕ}

theorem rt_child_safe (henv : WhpLargeEnv c U V w₀ n_max w base)
    (hep : ep = 0 ∨ ep = 1) {idx : ℕ} (hidx : idx < trieChildEntriesWhp c n_max) :
    let rt := mkBufRt c U V w₀ n_max base ep
    ∃ N, w = brW rt ∧ 0 < w ∧ brGBits rt ≤ w ∧ idx < N ∧
      Fits w (brBase rt + brOffChild rt + packedWords N (brGBits rt) w) := by
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w₀ n_max
  rcases hep with rfl | rfl
  · exact henv.packed_safe_of_le hgk hidx hseg.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact henv.packed_safe_of_le hgk hidx hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem rt_meta_safe (henv : WhpLargeEnv c U V w₀ n_max w base)
    (hep : ep = 0 ∨ ep = 1) {idx : ℕ} (hidx : idx < 6 * maxTrieNodesWhp c n_max) :
    let rt := mkBufRt c U V w₀ n_max base ep
    ∃ N, w = brW rt ∧ 0 < w ∧ brGBits rt ≤ w ∧ idx < N ∧
      Fits w (brBase rt + brOffMeta rt + packedWords N (brGBits rt) w) := by
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w₀ n_max
  rcases hep with rfl | rfl
  · exact henv.packed_safe_of_le hgk hidx hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact henv.packed_safe_of_le hgk hidx hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem rt_items_safe (henv : WhpLargeEnv c U V w₀ n_max w base)
    (hep : ep = 0 ∨ ep = 1) {idx : ℕ} (hidx : idx < 6 * qEpochWhp n_max + 6) :
    let rt := mkBufRt c U V w₀ n_max base ep
    ∃ N, w = brW rt ∧ 0 < w ∧ brGBits rt ≤ w ∧ idx < N ∧
      Fits w (brBase rt + brOffItems rt + packedWords N (brGBits rt) w) := by
  have hgk := globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1
  have hseg := WhpLargeEnv.seg_end_le c U V w₀ n_max
  rcases hep with rfl | rfl
  · exact henv.packed_safe_of_le hgk hidx hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact henv.packed_safe_of_le hgk hidx hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem rt_seg_le (c U V w n_max base ep : ℕ) (hep : ep = 0 ∨ ep = 1) :
    let rt := mkBufRt c U V w n_max base ep
    base + brHdrNA rt < base + largeSpaceWhp c U V w n_max ∧
    base + brHdrIA rt < base + largeSpaceWhp c U V w n_max ∧
    base + brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max ∧
    base + brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max ∧
    base + brOffItems rt + packedWords (6 * qEpochWhp n_max + 6) (globalPtrBits n_max) w ≤
      base + largeSpaceWhp c U V w n_max := by
  have h32 : 32 ≤ largeSpaceWhp c U V w n_max := by
    dsimp only [largeSpaceWhp]; omega
  have hseg := WhpLargeEnv.seg_end_le c U V w n_max
  have h13 := hseg.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h14 := hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h15 := hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h16 := hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h17 := hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h18 := hseg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rcases hep with rfl | rfl <;>
    (dsimp only [mkBufRt, brHdrNA, brHdrIA, brOffChild, brOffMeta, brOffItems,
       hdrBuf0NodeAlloc, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc, hdrBuf1ItemAlloc]
     simp only [↓reduceIte, Nat.one_ne_zero]
     exact ⟨by omega, by omega, by omega, by omega, by omega⟩)

end RtSafety


private theorem offTrieItems0_ge_32 (c U V w n_max : ℕ) :
    32 ≤ offTrieItems0 c U V w n_max := by
  have hch := largeOffsetChain c U V w n_max
  omega

theorem bufEpFrame_write_hdrNA {base c U V w n_max ep val : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hep : ep = 0 ∨ ep = 1) :
    let rt := mkBufRt c U V w n_max base ep
    BufEpFrame base c U V w n_max ep mem (Function.update mem (base + brHdrNA rt) val) := by
  have h32 := offTrieItems0_ge_32 c U V w n_max
  have hna_lt : brHdrNA (mkBufRt c U V w n_max base ep) < 32 := by
    rcases hep with rfl | rfl <;>
      (dsimp [mkBufRt, brHdrNA, hdrBuf0NodeAlloc, hdrBuf1NodeAlloc]; omega)
  exact ⟨fun a h1 _ _ _ _ => Function.update_of_ne h1 _ _,
    fun idx _ h2 => readPacked_update_outside hw h2 (Or.inl (by omega))⟩

theorem bufEpFrame_write_hdrIA {base c U V w n_max ep val : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hep : ep = 0 ∨ ep = 1) :
    let rt := mkBufRt c U V w n_max base ep
    BufEpFrame base c U V w n_max ep mem (Function.update mem (base + brHdrIA rt) val) := by
  have h32 := offTrieItems0_ge_32 c U V w n_max
  have hia_lt : brHdrIA (mkBufRt c U V w n_max base ep) < 32 := by
    rcases hep with rfl | rfl <;>
      (dsimp [mkBufRt, brHdrIA, hdrBuf0ItemAlloc, hdrBuf1ItemAlloc]; omega)
  exact ⟨fun a _ h2 _ _ _ => Function.update_of_ne h2 _ _,
    fun idx _ h2 => readPacked_update_outside hw h2 (Or.inl (by omega))⟩

theorem bufEpFrame_writeChild {base c U V w n_max ep idx val : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hep : ep = 0 ∨ ep = 1) (hidx : idx < trieChildEntriesWhp c n_max) :
    let rt := mkBufRt c U V w n_max base ep
    BufEpFrame base c U V w n_max ep mem
      (writePacked (base + brOffChild rt) (globalPtrBits n_max) w mem idx val) := by
  have hch := largeOffsetChain c U V w n_max
  refine ⟨fun a _ _ h3 _ _ => writePacked_outside hw _ hidx _ (by cases h3 <;> omega),
    fun j _ hj => ?_⟩
  rcases hep with rfl | rfl <;>
    exact readPacked_writePacked_disjoint hw hj hidx
      (Or.inr (by dsimp [mkBufRt, brOffChild]; omega))

theorem bufEpFrame_writeMeta {base c U V w n_max ep idx val : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hep : ep = 0 ∨ ep = 1) (hidx : idx < 6 * maxTrieNodesWhp c n_max) :
    let rt := mkBufRt c U V w n_max base ep
    BufEpFrame base c U V w n_max ep mem
      (writePacked (base + brOffMeta rt) (globalPtrBits n_max) w mem idx val) := by
  have hch := largeOffsetChain c U V w n_max
  refine ⟨fun a _ _ _ h4 _ => writePacked_outside hw _ hidx _ (by cases h4 <;> omega),
    fun j _ hj => ?_⟩
  rcases hep with rfl | rfl <;>
    exact readPacked_writePacked_disjoint hw hj hidx
      (Or.inr (by dsimp [mkBufRt, brOffMeta]; omega))

theorem bufEpFrame_writeItems_lt3q {base c U V w n_max ep idx val : ℕ} {mem : ℕ → ℕ}
    (hw : 0 < w) (hep : ep = 0 ∨ ep = 1) (hidx : idx < 3 * qEpochWhp n_max) :
    let rt := mkBufRt c U V w n_max base ep
    BufEpFrame base c U V w n_max ep mem
      (writePacked (base + brOffItems rt) (globalPtrBits n_max) w mem idx val) := by
  have hidx6 : idx < 6 * qEpochWhp n_max + 6 := by omega
  have hch := largeOffsetChain c U V w n_max
  refine ⟨fun a _ _ _ _ h5 => writePacked_outside hw _ hidx6 _ (by cases h5 <;> omega),
    fun j hj3 hj6 => ?_⟩
  rcases hep with rfl | rfl
  · dsimp only [mkBufRt, brOffItems, ↓reduceIte]
    exact readPacked_writePacked_of_ne hw mem (by omega) val
  · simp only [mkBufRt, brOffItems, Nat.one_ne_zero, ↓reduceIte]
    exact readPacked_writePacked_disjoint hw hj6 hidx6 (Or.inl (by omega))

theorem rt_disj_le (c U V w n_max base ep : ℕ) (hep : ep = 0 ∨ ep = 1) :
    let rt := mkBufRt c U V w n_max base ep
    brHdrNA rt < 32 ∧
    brHdrIA rt < 32 ∧
    brHdrNA rt ≠ brHdrIA rt ∧
    32 ≤ brOffChild rt ∧
    brOffChild rt + packedWords (trieChildEntriesWhp c n_max) (globalPtrBits n_max) w ≤
      brOffMeta rt ∧
    brOffMeta rt + packedWords (6 * maxTrieNodesWhp c n_max) (globalPtrBits n_max) w ≤
      brOffItems rt := by
  have hch := largeOffsetChain c U V w n_max
  rcases hep with rfl | rfl <;>
    (dsimp only [mkBufRt, brHdrNA, brHdrIA, brOffChild, brOffMeta, brOffItems,
       hdrBuf0NodeAlloc, hdrBuf0ItemAlloc, hdrBuf1NodeAlloc, hdrBuf1ItemAlloc]
     simp only [↓reduceIte, Nat.one_ne_zero]
     exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)

theorem bufTrieMemRep_iff_rt {base c U V w n_max ep : ℕ} {tr : BufTrie} {mem : ℕ → ℕ} :
    BufTrieMemRep base c U V w n_max ep tr mem ↔
      let rt := mkBufRt c U V w n_max base ep
      tr.nodeAlloc ≤ maxTrieNodesWhp c n_max ∧
      tr.itemAlloc ≤ qEpochWhp n_max ∧
      mem (base + brHdrNA rt) = tr.nodeAlloc ∧
      mem (base + brHdrIA rt) = tr.itemAlloc ∧
      (∀ u < maxTrieNodesWhp c n_max, ∀ ch < 2 ^ bCharWhp n_max,
        readPacked (base + brOffChild rt) (globalPtrBits n_max) w mem
          (u * 2 ^ bCharWhp n_max + ch) = tr.trieChild u ch) ∧
      (∀ u, 1 ≤ u → u < tr.nodeAlloc →
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w mem (4 * u + 0) =
          tr.nodeParent u ∧
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w mem (4 * u + 1) =
          tr.nodeChar u) ∧
      (∀ u < tr.nodeAlloc,
        readPacked (base + brOffMeta rt) (globalPtrBits n_max) w mem (4 * u + 2) =
          tr.nodeLeafItem u ∧
        (tr.nodeLeafItem u ≠ 0 →
          readPacked (base + brOffMeta rt) (globalPtrBits n_max) w mem (4 * u + 3) =
            tr.nodeActive u)) ∧
      (∀ id < tr.itemAlloc,
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w mem id = tr.itemLeaf id ∧
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w mem (qEpochWhp n_max + id) =
          tr.itemBucket id ∧
        readPacked (base + brOffItems rt) (globalPtrBits n_max) w mem (2 * qEpochWhp n_max + id) =
          tr.itemLoc id) :=
  Iff.rfl


/-- `BufRt` active-item reader for `bufLookup`: given `(rt, id)` (`id < qEp`), reads
`(1, (b, loc))`. -/
@[irreducible] def bufReadItemPairRtProg (d : BufRt × ℕ) :
    Memory.Prog (ℕ × (ℕ × ℕ)) := do
  let rt := d.1
  let idxB ← pure (brQEp rt + d.2)
  let idxL ← pure (2 * brQEp rt + d.2)
  let b ← readPackedGenProg (((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxB)
  let loc ← readPackedGenProg (((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxL)
  pure (1, (b, loc))

theorem bufReadItemPairRtProg_eq (d : BufRt × ℕ) :
    bufReadItemPairRtProg d = (do
      let rt := d.1
      let idxB ← pure (brQEp rt + d.2)
      let idxL ← pure (2 * brQEp rt + d.2)
      let b ← readPackedGenProg (((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxB)
      let loc ← readPackedGenProg (((brBase rt, brOffItems rt), (brGBits rt, brW rt)), idxL)
      pure (1, (b, loc))) := by
  unfold bufReadItemPairRtProg; rfl

theorem realizes_bufReadItemPairRt :
    Realizes .exact bufReadItemPairRtProg
      (WordEncoding.encode (α := BufRt × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w d _ => BufRtEnvGen w d.1 ∧ d.2 < brQEp d.1)
      (fun _ _ => 0) := by
  unfold bufReadItemPairRtProg
  have hrp := realizes_readPackedGen
  have hcs : ∀ x s', (Memory.spec 0).clientState s' (readPackedGenProg x) = s' := fun _ _ => rfl
  realize
  all_goals
    rcases d with ⟨rt, id⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hid⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brQEp] at hid ⊢
    obtain ⟨_, _, _, _, _, hq6_le⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have h6q : 6 * qEpochWhp n_max + 6 ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans hq6_le
    simp only [hcs] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact rt_items_safe henv hep (by omega)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
