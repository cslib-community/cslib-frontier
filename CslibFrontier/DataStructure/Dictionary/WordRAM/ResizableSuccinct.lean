/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration

/-!
# Resizable Succinct Dynamic Dictionary on the Resizable Word RAM

This module packages the resizable succinct dynamic dictionary supporting `insert`, `delete`, and
`query` over `Cslib.WordRAM.Basis.exact` and `Cslib.WordRAM.Basis.standard` on the word-granular
**Resizable Word RAM** (`Cslib.WordRAM.Resizable`), certified as reusable
`Cslib.DataStructure.WordRAM.Resizable.Randomized.ObliviousSequenceImpl` certificates
(`obliviousImpl` and `obliviousImplStandard`) for
`(Cslib.DataStructure.Dictionary.Dynamic.spec U V U).toObliviousSequenceSpec (Dictionary.empty U)`.

## Mathematical and algorithmic design

This synthesis—combining expected amortized `O(1)` oblivious instructions, explicit stored 3-wise
independent quotient hashing, and strict `1 · OPT(U, V, n)` single-tape resting and migration-peak
space on the Resizable Word RAM—is **original to this formalization** (deamortized high-probability
bounds remain open under `#3167`). It draws on the bucket partition and fingerprint-indexed buckets
of [Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–4 and 6][BenderFarachColtonKuszmaulKuszmaul2024], one-round Feistel quotienting
([Arbitman, Naor, and Segev, FOCS 2010, Claim 5.7][ArbitmanNaorSegev2010];
[Bender, Conway, Farach-Colton, Kuszmaul, and Tagliavini, *J. ACM* 2023,
Section 7][BenderConwayFarachColtonKuszmaulTagliavini2023]), fixed-width full slabs with a shared
tail pool ([Bender, Farach-Colton, J. Kuszmaul, W. Kuszmaul, and M. Liu, STOC 2022, Sections 5.2
and 6.1, Lemma 24][BenderFarachColtonKuszmaulKuszmaulLiu2022]), and word-granular frontier resizing
(`.grow` and `.shrink`) on the Resizable Word RAM
([Kuszmaul, Liang, and Zhou, SODA 2026, Section 5.1][KuszmaulLiangZhou2026]):

1. **Metadata-first compacted epoch layout and `U - 1` / `V - 1` root header (`Params`,
   `InEpoch`)**:
   * When empty (`n_t = 0`), the dictionary occupies only the 8-word persistent root header
     `[U - 1, V - 1, w, keyBits U, valBits V, 0, 0, 0]` at `[base, base + 8)` (`initCode` runs in
     `initSteps = 68` deterministic instructions). Storing `U - 1` and `V - 1` supports full-word
     value ranges `V = 2 ^ w` without overflowing `w`-bit words.
   * When active (`1 ≤ n_t ≤ N ≤ min (4 * n_t) U`), metadata (`HashParams`, `CompParams`,
     `ReducedKWise` seed and Four-Russians table, `LocalMeta`, `GlobalMeta`, `TailToDense`, and
     `DenseToTail`) sits at `[base, base + offCompItems U w N)` below a dense `[0, n_t)` stream of
     `(quotient, value)` pairs packed into `compactedItemWords U V w N n_t` words, linked to
     physical slab/tail coordinates via the circular-window bijection `denseOfCirc`. Resting memory
     above `base` never exceeds `Dynamic.succinctWords 1355 441 U V w n_t` words (`1 · OPT`: at
     most `Dynamic.optBits U V n_t + 1355 * n_t * Dynamic.logLogFactor n_t + 442 * w` bits).
2. **Single-tape `1 · OPT` capacity-doubling and capacity-halving rebuilds (`Migration`)**:
   * An `insert` at `n_t = N < U` or a `delete` at `2 ≤ n_t` with `4 * (n_t - 1) < N` triggers
     `migrateActiveCode`, which shifts the existing `[0, n_t)` packed item stream into a shared
     upper arena, initializes fresh metadata for `N' = targetCap U n_t = min (2 * n_t) U`, samples
     a fresh uniform 3-wise independent quotient-hash seed (`QuotHashSeed U N'`) in place via
     `resampleHashCode` (`RInstr.rand`), streams all `n_t` items left-to-right into `[0, n_t)`
     without holding two separate item arrays, and shrinks any trailing arena slack via
     `shrinkCode`.
   * Across every intermediate machine step—both in-epoch and during capacity migrations—the active
     hardware frontier above `base` never exceeds
     `Dynamic.succinctWords 2699 888 U V w (max n_t n_{t+1})` words (`1 · OPT`, never `2 · OPT`),
     sharpening to `Dynamic.succinctWords 1355 441 U V w (max n_t n_{t+1})` words on non-migrating
     operations.
3. **Self-contained hashing, oblivious operation model, and expected amortized `O(1)` time**:
   * **No external hash or prime hypotheses**: all quotient-hash seeds and Four-Russians carryless
     multiplication tables (`RuntimeReducedKWise`) are sampled and built internally by the program.
   * **Oblivious operation sequence vs. adaptive `.grow` adversary**: the operation sequence
     `ops : List (Dynamic.Op U)` is **oblivious** (fixed before initialization randomness, as
     specified by `ObliviousSequenceImpl`). Independently, within `ExecRCodeDist`, every newly
     allocated word returned by `.grow` is chosen by an **adaptive demonic allocation adversary**
     (`RAdv` / `DemonicGrow`), which `growZeroCode` zeroes immediately upon allocation.
   * **Expected amortized `O(1)` vs. SOSA 2024 WHP**: operations run in `O(1)` **expected
     amortized** Resizable Word RAM instructions (`resizableCharge : ℕ`, a parameter-free universal
     constant independent of `U`, `V`, `w`, `base`, and `ops.length`) via explicit two-stage 3-wise
     independent quotient hashing combined with slab-hysteresis and epoch-distance potentials
     (`resizablePotential`). By contrast, [Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul,
     SOSA 2024, Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024] prove deamortized
     with-high-probability bounds under idealized fully random hash functions.
4. **Program specialization**:
   * The operational dispatcher `(subroutineCode U V w).code = resizableOpCode` does not depend on
     `(U, V, w, base)`. The initializer `initCode U V w` depends on `(U, V, w)` only through the
     five header constants written to `[base, base + 5)`, and neither program inspects the ambient
     word width via `Op.width` (`¬(subroutineCode U V w).ReadsWidth`). No theorem bounds static
     code size; all time bounds count executed Resizable Word RAM instructions.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.initSteps`, `initCode`: 68-instruction
  empty-dictionary initializer allocating and populating the 8-word root header at
  `[base, base + 8)`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.subroutineCode`,
  `subroutineCodeStandard`: relocatable `Resizable.SubroutineCode` packages over `Basis.exact` and
  `Basis.standard`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.obliviousImpl`,
  `obliviousImplStandard`: `Resizable.Randomized.ObliviousSequenceImpl` certificates over
  `Basis.exact` and `Basis.standard`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.stepSuccinctPeakWords`: pure
  `Dynamic.succinctWords 2699 888 U V w (max #(dom s) #(dom s'))` `1 · OPT` peak-word function.

## Main results

* `not_readsWidth_initCode`, `not_readsWidth_subroutineCode`,
  `not_readsWidth_subroutineCodeStandard`: width-independence (`¬ReadsWidth`) of `initCode` and
  `subroutineCode`.
* `initCode_demonicExec`: deterministic `RDemonicExec` specification for `initCode`.
* `epochSpaceBound_le_succinctWords`, `w_mul_epochSpaceBound_le_bits`: resting `1 · OPT` word and
  bit footprint bounds (`Dynamic.succinctWords 1355 441 U V w n_t`) along any valid prefix.
* `epochPeakSpaceBound_le_succinctWords`, `epochPeakSpaceBound_inEpoch_le_succinctWords`,
  `w_mul_epochPeakSpaceBound_le_bits`: stepwise `1 · OPT` peak word and bit bounds
  (`Dynamic.succinctWords 2699 888 U V w (max n_t n_{t+1})`, `1355, 441` in-epoch; never `2 · OPT`).
* `obliviousPeakFits_of_succinctWords`: discharges `ObliviousPeakFits` from pure
  `PeakFitsHistory` over `stepSuccinctPeakWords`.
* `seq_expected_amortized`, `seq_expected_amortized_standard`: end-to-end `O(|ops| + 1)` expected
  instruction time, resting and stepwise-peak `1 · OPT` space, caller `[0, base)` preservation, and
  distributional correctness theorems over `Basis.exact` and `Basis.standard`.

## References

* [Y. Arbitman, M. Naor, and G. Segev, *Backyard Cuckoo Hashing: Constant Worst-Case Operations
  with a Succinct Representation*, Claim 5.7][ArbitmanNaorSegev2010]
* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul, and M. Liu,
  *On the Optimal Time/Space Tradeoff for Hash Tables*, Sections 5.2 and
  6.1][BenderFarachColtonKuszmaulKuszmaulLiu2022]
* [M. A. Bender, A. Conway, M. Farach-Colton, W. Kuszmaul, and G. Tagliavini,
  *Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once*,
  Section 7][BenderConwayFarachColtonKuszmaulTagliavini2023]
* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–4 and 6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select: Bypassing the Tree-Structure
  Bottleneck*, Section 5.1][KuszmaulLiangZhou2026]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Resizable
open Cslib.DataStructure
open Cslib.DataStructure.WordRAM.Resizable
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.Probability
open scoped ENNReal

/-! ## Section 1: Empty-Dictionary Initializer (`initCode`) and `SubroutineCode` -/

/-- Exact instruction budget (`68` steps) for `initCode U V w`. -/
@[expose]
def initSteps : ℕ := 68

private noncomputable def initStoreConstCode (off val : ℕ) : RCode .exact rResize :=
  .seq (.op (.const mRes val)) (storeAtOffCode mBase mRes mCur off)

private theorem not_readsWidth_initStoreConstCode (off val : ℕ) :
    ¬(initStoreConstCode off val).ReadsWidth := by
  simp [initStoreConstCode, RCode.ReadsWidth, Op.ReadsWidth, not_readsWidth_storeAtOffCode]

private theorem initStoreConstCode_exec {w L_peak base off val : ℕ} {x : RData rResize}
    (hx : x.Bounded w) (hL : x.frontier ≤ L_peak) (hbase : x.regs mBase = base)
    (hoff_fit : Fits w off) (hval_fit : Fits w val) (hlt : base + off < x.frontier) :
    ∃ y : RData rResize,
      RDemonicExec w L_peak (initStoreConstCode off val) x 4 (· = y) ∧
      y.Bounded w ∧
      y.frontier = x.frontier ∧
      y.regs mBase = base ∧
      y.mem (base + off) = val ∧
      (∀ a, a ≠ base + off → y.mem a = x.mem a) := by
  have hs1 := RDemonicExec.const (B := .exact) (d := mRes) (v := val) (x := x) hL hval_fit
  have hx1b : (x.set mRes val).Bounded w := hx.set hval_fit
  have hbase1 : (x.set mRes val).regs mBase = base := by
    rw [RData.set_regs, Function.update_of_ne (mReg_ne (by decide))]; exact hbase
  obtain ⟨hs2, hyb⟩ := storeAtOffCode_exec (rAddr := mBase) (rSrc := mRes) (rTmp := mCur)
    (off := off) (val := val) hx1b hL (mReg_ne (by decide)) (mReg_ne (by decide)) hbase1
    (by simp [RData.set]) hoff_fit hlt
  let y := ((x.set mRes val).set mCur (base + off)).write (base + off) val
  have hy_base : y.regs mBase = base := by
    dsimp only [y, RData.write]
    rwa [RData.set_regs, Function.update_of_ne (mReg_ne (by decide))]
  exact ⟨y, (hs1.seq_eq hs2).mono (by decide) (fun _ h => h), hyb, rfl, hy_base,
    by simp [y, RData.write], fun a ha => by simp [y, RData.write, Function.update_of_ne ha]⟩

/-- Initializer (`RCode .exact rResize`) growing and zeroing the 8-word root header at
`[base, base + 8)` (`base = x₀.frontier`), recording `base` in `mBase`, and writing
`[U - 1, V - 1, w, keyBits U, valBits V, 0, 0, 0]`. -/
noncomputable def initCode (U V w : ℕ) : RCode .exact rResize :=
  .seq (.op (.const mK 8)) <|
  .seq (growZeroCode mK mRes mCur mIdx mZero mOne) <|
  .seq (.op (.copy mBase mRes)) <|
  .seq (initStoreConstCode 0 (U - 1)) <|
  .seq (initStoreConstCode 1 (V - 1)) <|
  .seq (initStoreConstCode 2 w) <|
  .seq (initStoreConstCode 3 (keyBits U))
       (initStoreConstCode 4 (valBits V))

/-- `initCode U V w` does not inspect the ambient word width via `Op.width`. -/
theorem not_readsWidth_initCode (U V w : ℕ) : ¬(initCode U V w).ReadsWidth := by
  simp [initCode, RCode.ReadsWidth, Op.ReadsWidth, growZeroCode_not_readsWidth,
    not_readsWidth_initStoreConstCode]

/-- Deterministic `RDemonicExec` specification for `initCode U V w`: from any `w`-bounded state
`x₀` at `x₀.frontier = base` with `Fits w (base + 8)`, `initCode U V w` runs in `initSteps = 68`
instructions within peak frontier `base + 8`, establishes `EpochRep` for `EpochState.empty U` and
`LatentSeed.empty U`, and preserves caller memory `[0, base)`. -/
theorem initCode_demonicExec {U V w base : ℕ} {x₀ : RData rResize}
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hU_pos : 0 < U) (hU : Fits w U) (hV_pos : 0 < V) (hV : V ≤ 2 ^ w)
    (hfit₈ : Fits w (base + 8)) :
    ∃ y : RData rResize,
      RDemonicExec w (base + 8) (initCode U V w) x₀ initSteps (· = y) ∧
      EpochRep U V w base (EpochState.empty U) (LatentSeed.empty U) y ∧
      (∀ addr < base, y.mem addr = x₀.mem addr) := by
  have hfit8_const : Fits w 8 := hfit₈.of_le (Nat.le_add_left 8 base)
  have hfit1 : Fits w 1 := hfit8_const.of_le (by decide)
  have hfit_w : Fits w w := Nat.lt_two_pow_self
  have hfit_kb : Fits w (keyBits U) :=
    hfit_w.of_le ((Nat.clog_le_iff_le_pow one_lt_two).mpr hU.le)
  have hfit_vb : Fits w (valBits V) :=
    hfit_w.of_le ((Nat.clog_le_iff_le_pow one_lt_two).mpr hV)
  have hL₀ : x₀.frontier ≤ base + 8 := hfr₀ ▸ Nat.le_add_right base 8
  -- Step 1: `mK := 8` (1 step)
  let x₁ := x₀.set mK 8
  have hs_k8 := RDemonicExec.const (B := .exact) (d := mK) (v := 8) (x := x₀) hL₀ hfit8_const
  have hx₁b : x₁.Bounded w := hx₀.set hfit8_const
  have hx₁_fr : x₁.frontier = base := hfr₀
  have hx₁_k : x₁.regs mK = 8 := by simp [x₁]
  -- Step 2: `growZeroCode mK mRes mCur mIdx mZero mOne` (46 steps)
  let x₂ := growZeroPost mK mRes mCur mIdx mZero mOne x₁
  have hs_gz : RDemonicExec w (base + 8) (growZeroCode mK mRes mCur mIdx mZero mOne) x₁ 46
      (· = x₂) :=
    (growZeroCode_exec (w := w) (L_peak := base + 8)
      (count := mK) (result := mRes) (cur := mCur) (idx := mIdx) (zero := mZero) (one := mOne)
      hx₁b mGrow_nodup hfit1 (by rw [hx₁_fr, hx₁_k])
      (by rwa [hx₁_fr, hx₁_k])).mono
      (by rw [hx₁_k]) (fun _ h => h)
  have hx₂_fr : x₂.frontier = base + 8 := by simp [x₂, growZeroPost, hx₁_fr, hx₁_k]
  have hx₂_res : x₂.regs mRes = base := by
    simp only [x₂, growZeroPost, hx₁_k, hx₁_fr, Nat.succ_ne_zero, ↓reduceIte]
    rw [Function.update_of_ne (mReg_ne (by decide)),
      Function.update_of_ne (mReg_ne (by decide)), Function.update_self]
  have hx₂b : x₂.Bounded w :=
    growZeroPost_bounded hx₁b hfit1 (by rwa [hx₁_fr, hx₁_k])
  -- Step 3: `mBase := mRes` (1 step)
  let x₃ := x₂.set mBase (x₂.regs mRes)
  have hs_cp := RDemonicExec.copy (B := .exact) (w := w) (L_peak := base + 8)
    (d := mBase) (s := mRes) (x := x₂) hx₂_fr.le
  have hx₃b : x₃.Bounded w := hx₂b.set (hx₂b.regs_fits mRes)
  have hx₃_base : x₃.regs mBase = base := by simp [x₃, hx₂_res]
  have hx₃_mem : x₃.mem = x₀.mem := rfl
  -- Steps 4..8: store `U - 1`, `V - 1`, `w`, `keyBits U`, `valBits V` into `base + 0 .. 4`
  have storeStep (off val : ℕ) {x : RData rResize} (hxb : x.Bounded w)
      (hfr : x.frontier = base + 8) (hbase : x.regs mBase = base)
      (hoff : off < 8) (hval : Fits w val) :
      ∃ y : RData rResize, RDemonicExec w (base + 8) (initStoreConstCode off val) x 4 (· = y) ∧
        y.Bounded w ∧ y.frontier = base + 8 ∧ y.regs mBase = base ∧ y.mem (base + off) = val ∧
        ∀ a, a ≠ base + off → y.mem a = x.mem a := by
    obtain ⟨y, hs, hyb, hyfr, hybase, hym, hyne⟩ := initStoreConstCode_exec hxb hfr.le hbase
      (hfit8_const.of_le hoff.le) hval (by omega)
    exact ⟨y, hs, hyb, hyfr.trans hfr, hybase, hym, hyne⟩
  obtain ⟨x₄, hs_0, hx₄b, hx₄_fr, hx₄_base, hm₄_0, hm₄_ne⟩ :=
    storeStep 0 (U - 1) hx₃b hx₂_fr hx₃_base (by decide) (hU.of_le (Nat.sub_le U 1))
  obtain ⟨x₅, hs_1, hx₅b, hx₅_fr, hx₅_base, hm₅_1, hm₅_ne⟩ :=
    storeStep 1 (V - 1) hx₄b hx₄_fr hx₄_base (by decide)
      (lt_of_lt_of_le (Nat.sub_lt hV_pos Nat.one_pos) hV)
  obtain ⟨x₆, hs_2, hx₆b, hx₆_fr, hx₆_base, hm₆_2, hm₆_ne⟩ :=
    storeStep 2 w hx₅b hx₅_fr hx₅_base (by decide) hfit_w
  obtain ⟨x₇, hs_3, hx₇b, hx₇_fr, hx₇_base, hm₇_3, hm₇_ne⟩ :=
    storeStep 3 (keyBits U) hx₆b hx₆_fr hx₆_base (by decide) hfit_kb
  obtain ⟨y_fin, hs_4, hyb, hy_fin_fr, hy_base, hmy_4, hmy_ne⟩ :=
    storeStep 4 (valBits V) hx₇b hx₇_fr hx₇_base (by decide) hfit_vb
  have hex_all : RDemonicExec w (base + 8) (initCode U V w) x₀ initSteps (· = y_fin) :=
    (hs_k8.seq_eq <| hs_gz.seq_eq <| hs_cp.seq_eq <|
      hs_0.seq_eq <| hs_1.seq_eq <| hs_2.seq_eq <| hs_3.seq_eq hs_4).mono
      (by decide) (fun _ h => h)
  have hzero_ge5 : ∀ off, 5 ≤ off → y_fin.mem (base + off) = 0 := fun off hoff => by
    have hne (k : ℕ) (hk : k < 5) : base + off ≠ base + k :=
      (Nat.add_lt_add_left (hk.trans_le hoff) base).ne'
    rw [hmy_ne _ (hne 4 (by decide)), hm₇_ne _ (hne 3 (by decide)), hm₆_ne _ (hne 2 (by decide)),
      hm₅_ne _ (hne 1 (by decide)), hm₄_ne _ (hne 0 (by decide)), hx₃_mem]
    exact hx₀.zero_above (by rw [hfr₀]; exact Nat.le_add_right base off)
  have hbelow : ∀ addr < base, y_fin.mem addr = x₀.mem addr := fun addr hlt => by
    have hne (k : ℕ) : addr ≠ base + k := (hlt.trans_le (Nat.le_add_right base k)).ne
    rw [hmy_ne _ (hne 4), hm₇_ne _ (hne 3), hm₆_ne _ (hne 2), hm₅_ne _ (hne 1), hm₄_ne _ (hne 0),
      hx₃_mem]
  have hne_add (a b : ℕ) (hab : decide (a ≠ b) = true := by decide) : base + a ≠ base + b :=
    fun h => of_decide_eq_true hab (Nat.add_left_cancel h)
  have hhdr : RootHeaderValid U V w 0 0 0 base y_fin.mem := by
    refine ⟨hU, hU_pos, hV_pos, ?_, ?_,
      by rw [hmy_ne _ (hne_add 2 4), hm₇_ne _ (hne_add 2 3), hm₆_2],
      by rw [hmy_ne _ (hne_add 3 4), hm₇_3], hmy_4,
      hzero_ge5 5 (by decide), hzero_ge5 6 (by decide), hzero_ge5 7 (by decide)⟩
    · rw [← Nat.add_zero base, hmy_ne _ (hne_add 0 4), hm₇_ne _ (hne_add 0 3),
        hm₆_ne _ (hne_add 0 2), hm₅_ne _ (hne_add 0 1), hm₄_0]
    · rw [hmy_ne _ (hne_add 1 4), hm₇_ne _ (hne_add 1 3), hm₆_ne _ (hne_add 1 2), hm₅_1]
  exact ⟨y_fin, hex_all,
    ⟨LatentSeed.empty_cap U, by
      simpa only [EpochState.empty, Dictionary.dom_empty, Finset.card_empty] using
        compactedRep_empty hyb hy_fin_fr hhdr,
      hy_base, fun hpos => by simp [EpochState.empty] at hpos⟩, hbelow⟩

/-- Relocatable `Resizable.SubroutineCode` over `Basis.exact` for the resizable succinct dynamic
dictionary (`k_init = 0` runtime register parameters; `code = resizableOpCode`). -/
@[expose]
noncomputable def subroutineCode (U V w : ℕ) :
    Cslib.DataStructure.WordRAM.Resizable.SubroutineCode .exact rResize 0 where
  baseReg := mBase
  initParams := ⟨Fin.elim0, fun j => Fin.elim0 j⟩
  input := resizableInput
  input_baseReg_false := resizableInput_mBase
  initCode := initCode U V w
  code := resizableOpCode

/-- Standard-basis (`Basis.standard`) relocatable `SubroutineCode` obtained via basis simulation. -/
noncomputable abbrev subroutineCodeStandard (U V w : ℕ) :
    Cslib.DataStructure.WordRAM.Resizable.SubroutineCode .standard rResize 0 :=
  (subroutineCode U V w).toStandard

/-- `subroutineCode U V w` does not inspect the ambient word width (`¬ReadsWidth`). -/
theorem not_readsWidth_subroutineCode (U V w : ℕ) : ¬(subroutineCode U V w).ReadsWidth := by
  unfold Cslib.DataStructure.WordRAM.Resizable.SubroutineCode.ReadsWidth subroutineCode
  exact not_or.mpr ⟨not_readsWidth_initCode U V w, not_readsWidth_resizableOpCode⟩

/-- `subroutineCodeStandard U V w` does not inspect the ambient word width (`¬ReadsWidth`). -/
theorem not_readsWidth_subroutineCodeStandard (U V w : ℕ) :
    ¬(subroutineCodeStandard U V w).ReadsWidth :=
  Cslib.DataStructure.WordRAM.Resizable.SubroutineCode.not_readsWidth_mapSimulates
    .exactStandard (not_readsWidth_subroutineCode U V w)

/-! ## Section 2: `1 · OPT` Resting and Peak Space Bounds Along Operation Trajectories -/

/-- **`1 · OPT` Resting Word-Footprint Bound (`epochSpaceBound_le_succinctWords`):**
After any admissible prefix `prefOps` reaching `n_t = #(Dictionary.dom s_t)` keys, the resting
hardware frontier above `base` uses at most `Dynamic.succinctWords 1355 441 U V w n_t` words. -/
theorem epochSpaceBound_le_succinctWords {U V w : ℕ}
    (hw : 0 < w) (hU_pos : 0 < U) (hU : Fits w U) (hV_pos : 0 < V)
    {prefOps : List (Dynamic.Op U)}
    (hvh : (Dynamic.spec U V U).ValidHistory (Dictionary.empty U) prefOps) :
    let n_t := (Dictionary.dom ((Dynamic.spec U V U).run (Dictionary.empty U) prefOps).1).card
    epochSpaceBound U V w prefOps ≤ Dynamic.succinctWords 1355 441 U V w n_t := by
  intro n_t
  have hanc := epochAnchorInv_run hU_pos (epochAnchorInv_empty U) hvh
  have hd := EpochState.dict_run V (EpochState.empty U) prefOps
  rw [epochSpaceBound, hd]
  exact compactedEpochWords_le_succinctWords hw hU hU_pos hV_pos (hd ▸ hanc.1)

/-- **`1 · OPT` Resting Bit-Space Bound (`w_mul_epochSpaceBound_le_bits`):**
After any admissible prefix `prefOps` reaching `n_t` active keys, `w * epochSpaceBound U V w
prefOps ≤ Dynamic.optBits U V n_t + 1355 * n_t * Dynamic.logLogFactor n_t + 442 * w` bits. -/
theorem w_mul_epochSpaceBound_le_bits {U V w : ℕ}
    (hw : 0 < w) (hU_pos : 0 < U) (hU : Fits w U) (hV_pos : 0 < V)
    {prefOps : List (Dynamic.Op U)}
    (hvh : (Dynamic.spec U V U).ValidHistory (Dictionary.empty U) prefOps) :
    let n_t := (Dictionary.dom ((Dynamic.spec U V U).run (Dictionary.empty U) prefOps).1).card
    w * epochSpaceBound U V w prefOps ≤
      Dynamic.optBits U V n_t + 1355 * n_t * Dynamic.logLogFactor n_t + 442 * w := by
  intro n_t
  calc w * epochSpaceBound U V w prefOps
      ≤ w * Dynamic.succinctWords 1355 441 U V w n_t :=
        Nat.mul_le_mul_left w (epochSpaceBound_le_succinctWords hw hU_pos hU hV_pos hvh)
    _ ≤ Dynamic.optBits U V n_t + 1355 * n_t * Dynamic.logLogFactor n_t + (441 + 1) * w :=
        succinctWords_mul_w_le_bits 1355 441 U V w n_t

/-- Pure specification-level `1 · OPT` stepwise peak-word bound
`Dynamic.succinctWords 2699 888 U V w (max #(dom s) #(dom s'))`. -/
@[expose]
def stepSuccinctPeakWords {U : ℕ} (V w : ℕ) (s : Dictionary.State U) (o : Dynamic.Op U) : ℕ :=
  Dynamic.succinctWords 2699 888 U V w
    (max (Dictionary.dom s).card (Dictionary.dom ((Dynamic.spec U V U).stepFn s o).1).card)

/-- **`1 · OPT` Stepwise Peak Word-Footprint Bound (`epochPeakSpaceBound_le_succinctWords`):**
Across every admissible operation `o` after prefix `prefOps` (including single-tape capacity
doubling and halving rebuilds), the intermediate hardware frontier above `base` never exceeds
`stepSuccinctPeakWords V w s_t o = Dynamic.succinctWords 2699 888 U V w (max n_t n_{t+1})` words
(never `2 · OPT`). -/
theorem epochPeakSpaceBound_le_succinctWords {U V w : ℕ}
    (hw : 0 < w) (hU_pos : 0 < U) (hU : Fits w U) (hV_pos : 0 < V)
    {prefOps : List (Dynamic.Op U)} {o : Dynamic.Op U}
    (hvh : (Dynamic.spec U V U).ValidHistory (Dictionary.empty U) prefOps)
    (hval : (Dynamic.spec U V U).valid ((Dynamic.spec U V U).run (Dictionary.empty U) prefOps).1
      o) :
    epochPeakSpaceBound U V w prefOps o ≤
      stepSuccinctPeakWords V w ((Dynamic.spec U V U).run (Dictionary.empty U) prefOps).1 o := by
  have hd := EpochState.dict_run V (EpochState.empty U) prefOps
  dsimp only [EpochState.empty] at hd
  rw [epochPeakSpaceBound, stepSuccinctPeakWords, ← hd]
  exact stepExactPeakWords_le_succinctWords hw hU hU_pos hV_pos
    (epochAnchorInv_run hU_pos (epochAnchorInv_empty U) hvh).1 (hd ▸ hval)

/-- **In-Epoch `1 · OPT` Peak Word-Footprint Bound
(`epochPeakSpaceBound_inEpoch_le_succinctWords`):**
On any operation `o` that does not trigger active capacity migration, `epochPeakSpaceBound` is
bounded by `Dynamic.succinctWords 1355 441 U V w (max n_t n_{t+1})` words. -/
theorem epochPeakSpaceBound_inEpoch_le_succinctWords {U V w : ℕ}
    (hw : 0 < w) (hU_pos : 0 < U) (hU : Fits w U) (hV_pos : 0 < V)
    {prefOps : List (Dynamic.Op U)} {o : Dynamic.Op U}
    (hvh : (Dynamic.spec U V U).ValidHistory (Dictionary.empty U) prefOps)
    (hval : (Dynamic.spec U V U).valid ((Dynamic.spec U V U).run (Dictionary.empty U) prefOps).1 o)
    (hno_mig :
      let st := EpochState.run V (EpochState.empty U) prefOps
      let n := (Dictionary.dom st.dict).card
      (∀ u v, o = .insert u v → n ≠ 0 → ¬(n = st.cap ∧ st.cap < U)) ∧
      (∀ u, o = .delete u → 2 ≤ n → ¬(4 * (n - 1) < st.cap))) :
    let s_t := ((Dynamic.spec U V U).run (Dictionary.empty U) prefOps).1
    let m := max (Dictionary.dom s_t).card
      (Dictionary.dom ((Dynamic.spec U V U).stepFn s_t o).1).card
    epochPeakSpaceBound U V w prefOps o ≤ Dynamic.succinctWords 1355 441 U V w m := by
  intro s_t m
  have hd := EpochState.dict_run V (EpochState.empty U) prefOps
  dsimp only [epochPeakSpaceBound, EpochState.empty, m, s_t] at hd ⊢
  rw [← hd]
  exact stepExactPeakWords_inEpoch_le_succinctWords hw hU hU_pos hV_pos
    (epochAnchorInv_run hU_pos (epochAnchorInv_empty U) hvh).1 (hd ▸ hval) hno_mig

/-- **`1 · OPT` Stepwise Peak Bit-Space Bound (`w_mul_epochPeakSpaceBound_le_bits`):**
Across every admissible operation `o` after prefix `prefOps`, `w * epochPeakSpaceBound U V w
prefOps o ≤ Dynamic.optBits U V m + 2699 * m * Dynamic.logLogFactor m + 889 * w` bits, where
`m = max n_t n_{t+1}` (never `2 · OPT`). -/
theorem w_mul_epochPeakSpaceBound_le_bits {U V w : ℕ}
    (hw : 0 < w) (hU_pos : 0 < U) (hU : Fits w U) (hV_pos : 0 < V)
    {prefOps : List (Dynamic.Op U)} {o : Dynamic.Op U}
    (hvh : (Dynamic.spec U V U).ValidHistory (Dictionary.empty U) prefOps)
    (hval : (Dynamic.spec U V U).valid ((Dynamic.spec U V U).run (Dictionary.empty U) prefOps).1
      o) :
    let s_t := ((Dynamic.spec U V U).run (Dictionary.empty U) prefOps).1
    let m := max (Dictionary.dom s_t).card
      (Dictionary.dom ((Dynamic.spec U V U).stepFn s_t o).1).card
    w * epochPeakSpaceBound U V w prefOps o ≤
      Dynamic.optBits U V m + 2699 * m * Dynamic.logLogFactor m + 889 * w := by
  intro s_t m
  calc w * epochPeakSpaceBound U V w prefOps o
      ≤ w * Dynamic.succinctWords 2699 888 U V w m :=
        Nat.mul_le_mul_left w (epochPeakSpaceBound_le_succinctWords hw hU_pos hU hV_pos hvh hval)
    _ ≤ Dynamic.optBits U V m + 2699 * m * Dynamic.logLogFactor m + (888 + 1) * w :=
        succinctWords_mul_w_le_bits 2699 888 U V w m

private theorem obliviousPeakFits_of_succinctWords_aux {U V w base : ℕ}
    (hw : 0 < w) (hU_pos : 0 < U) (hU : Fits w U) (hV_pos : 0 < V)
    (prefOps remOps : List (Dynamic.Op U))
    (hvh_pref : (Dynamic.spec U V U).ValidHistory (Dictionary.empty U) prefOps)
    (hvh_rem : (Dynamic.spec U V U).ValidHistory
      ((Dynamic.spec U V U).run (Dictionary.empty U) prefOps).1 remOps)
    (hfit : PeakFitsHistory (D := Dynamic.spec U V U) w base (stepSuccinctPeakWords V w)
      ((Dynamic.spec U V U).run (Dictionary.empty U) prefOps).1 remOps) :
    ObliviousPeakFits w base (epochPeakSpaceBound U V w) prefOps remOps := by
  induction remOps generalizing prefOps with
  | nil => trivial
  | cons o os ih =>
    obtain ⟨hv_o, hvh_os⟩ := hvh_rem
    obtain ⟨hfit_o, hfit_os⟩ := hfit
    have hle := epochPeakSpaceBound_le_succinctWords hw hU_pos hU hV_pos hvh_pref hv_o
    have hrun_app : ((Dynamic.spec U V U).run (Dictionary.empty U) (prefOps ++ [o])).1 =
        ((Dynamic.spec U V U).stepFn
          ((Dynamic.spec U V U).run (Dictionary.empty U) prefOps).1 o).1 :=
      congrArg Prod.fst ((Dynamic.spec U V U).run_append _ _ _)
    exact ⟨hfit_o.of_le (Nat.add_le_add_left hle base),
      ih (prefOps ++ [o])
        (((Dynamic.spec U V U).validHistory_append _ _ _).mpr ⟨hvh_pref, hv_o, trivial⟩)
        (hrun_app ▸ hvh_os) (hrun_app ▸ hfit_os)⟩

/-- Discharges `ObliviousPeakFits` from the pure `1 · OPT` specification-level `PeakFitsHistory`
condition `Fits w (base + Dynamic.succinctWords 2699 888 U V w (max n_t n_{t+1}))` along `ops`. -/
theorem obliviousPeakFits_of_succinctWords {U V w base : ℕ}
    (hw : 0 < w) (hU_pos : 0 < U) (hU : Fits w U) (hV_pos : 0 < V)
    {ops : List (Dynamic.Op U)}
    (hvh : (Dynamic.spec U V U).ValidHistory (Dictionary.empty U) ops)
    (hfit : PeakFitsHistory (D := Dynamic.spec U V U) w base (stepSuccinctPeakWords V w)
      (Dictionary.empty U) ops) :
    ObliviousPeakFits w base (epochPeakSpaceBound U V w) [] ops :=
  obliviousPeakFits_of_succinctWords_aux hw hU_pos hU hV_pos [] ops trivial hvh hfit

/-! ## Section 3: `ObliviousSequenceImpl` Certificates and End-to-End Headline Theorems -/

/-- Reusable `Resizable.Randomized.ObliviousSequenceImpl` certificate over `Basis.exact` for the
resizable succinct dynamic dictionary (`initTime = 68`, `initPotential = 0`, constant per-operation
charge `resizableCharge`, resting space `epochSpaceBound`, peak space `epochPeakSpaceBound`). -/
@[expose]
noncomputable def obliviousImpl {U V w base : ℕ}
    (hw2 : Fits w 2) (hU_pos : 0 < U) (hU : Fits w U) (hV_pos : 0 < V) (hV : V ≤ 2 ^ w) :
    ObliviousSequenceImpl (subroutineCode U V w)
      ((Dynamic.spec U V U).toObliviousSequenceSpec (Dictionary.empty U)) w base ![] where
  Latent := LatentSeed U
  spaceBound := epochSpaceBound U V w
  peakSpaceBound := epochPeakSpaceBound U V w
  initTime := initSteps
  initPotential := 0
  charge := fun _ => resizableCharge
  initInv := fun ν₀ =>
    (∀ t ∈ ν₀.support, EpochRep U V w base (EpochState.empty U) t.latent t.data) ∧
      ∃ mem₀ : ℕ → ℕ, ∀ t ∈ ν₀.support, ∀ addr < base, t.data.mem addr = mem₀ addr
  validOp := fun _ o =>
    match o with
    | .query _ => True
    | .insert _ v => v < V
    | .delete _ => True
  encode := resizableEncode
  decode := resizableDecode
  bounded := fun hinv _ ht => (hinv.1 _ ht).compacted_rep.bounded
  frontier_le := fun hinv t ht => by
    have hfr := (hinv.1 t ht).compacted_rep.frontier_eq
    dsimp only [EpochState.empty] at hfr
    rw [Dictionary.dom_empty, Finset.card_empty] at hfr
    have hsp0 : epochSpaceBound U V w [] = compactedEpochWords U V w 0 0 := by
      simp [epochSpaceBound, EpochState.run, EpochState.empty]
    exact ⟨by rw [hfr]; exact Nat.le_add_right _ _, by rw [hfr, hsp0], (hinv.1 t ht).base_reg_eq⟩
  arguments_fit := fun o hv_op => by
    have hval : (Dynamic.spec U V U).valid (Dictionary.empty U) o := by
      cases o with
      | query _ => trivial
      | insert _ _ =>
        refine ⟨Or.inl ?_, hv_op⟩
        rw [Dictionary.dom_empty, Finset.card_empty]
        exact hU_pos
      | delete _ => trivial
    exact fits_resizableEncode hw2 hU hV hval
  init_exec := fun {x₀} hx₀ hfr₀ _ hfit₀ => by
    rw [epochSpaceBound_nil] at hfit₀ ⊢
    obtain ⟨y, hex_init, hrep_y, hbel_y⟩ :=
      initCode_demonicExec hx₀ hfr₀ hU_pos hU hV_pos hV hfit₀
    let s_init : LatentRState (LatentSeed U) rResize := ⟨LatentSeed.empty U, y⟩
    have hex_dist : ExecRCodeDist w (initCode U V w) x₀
        ((PMF.pure s_init).map LatentRState.data) initSteps (base + 8) :=
      (ExecRCodeDist.of_demonicExec hex_init).congr_dist (by simp [s_init]) le_rfl
    refine ⟨PMF.pure s_init, hex_dist, ⟨fun t ht => ?_, ⟨x₀.mem, fun t ht => ?_⟩⟩, fun t ht => ?_⟩
    · rw [PMF.support_pure, Set.mem_singleton_iff] at ht; subst ht; exact hrep_y
    · rw [PMF.support_pure, Set.mem_singleton_iff] at ht; subst ht; exact hbel_y
    · rw [PMF.support_pure, Set.mem_singleton_iff] at ht; subst ht; exact hbel_y
  steps_exec := fun ops ν₀ hv_seq hfit_ops hinv₀ => by
    obtain ⟨hrep₀, mem₀, hmem₀⟩ := hinv₀
    have hvh : (Dynamic.spec U V U).ValidHistory (Dictionary.empty U) ops :=
      ((Dynamic.spec U V U).validOpSeq_iff_validHistory (Dictionary.empty U) ops).mp hv_seq
    have hr_fit : ReachedEpochsFit V w base (EpochState.run V (EpochState.empty U) []) ops :=
      (obliviousPeakFits_iff_reachedEpochsFit [] ops).mp hfit_ops
    have hanc₀ : EpochAnchorInv U
        (Dictionary.dom (EpochState.run V (EpochState.empty U) []).dict).card
        (EpochState.run V (EpochState.empty U) []).cap
        (EpochState.run V (EpochState.empty U) []).initCount :=
      epochAnchorInv_empty U
    let ν_seq₀ : PMF (SeqROutcome (LatentSeed U) (Dynamic.Op.Result (U := U)) rResize) :=
      ν₀.map SeqROutcome.ofLatentRState
    have hseq_inv₀ : EpochSeqInv V w base (EpochState.run V (EpochState.empty U) [])
        [] mem₀ ν_seq₀ := by
      refine ⟨fun t ht => ?_, fun hpos => ?_⟩
      · dsimp only [ν_seq₀] at ht
        rw [PMF.mem_support_map_iff] at ht
        obtain ⟨u, hu, rfl⟩ := ht
        exact ⟨hrep₀ u hu, rfl, hmem₀ u hu⟩
      · dsimp only [EpochState.run, EpochState.empty] at hpos
        rw [Dictionary.dom_empty, Finset.card_empty] at hpos
        exact absurd hpos (Nat.not_lt_zero 0)
    obtain ⟨ν_final, T_ops, hex_steps, hinv_fin, hcost_fin⟩ :=
      resizableOpCode_steps_expected_amortized (subroutineCode U V w) rfl rfl rfl
        [] ops ν_seq₀ hw2 hU_pos hU hV hvh hr_fit hanc₀ hseq_inv₀
    have hpot₀ : (∑' t, ν_seq₀ t *
        (resizablePotential U w (EpochState.run V (EpochState.empty U) []).cap
          (Dictionary.dom (EpochState.run V (EpochState.empty U) []).dict).card
          (EpochState.run V (EpochState.empty U) []).initCount base t.data : ℝ≥0∞)) = 0 := by
      dsimp only [EpochState.run, EpochState.empty]
      rw [Dictionary.dom_empty, Finset.card_empty]
      simp [resizablePotential_zero]
    have hcontract : ((Dynamic.spec U V U).toObliviousSequenceSpec (Dictionary.empty U)).Contract
        ops (ν_final.map SeqROutcome.transcript) := by
      rw [(Dynamic.spec U V U).toObliviousSequenceSpec_contract_iff_of_hasStepFn
        (Dictionary.empty U) hvh]
      intro out hout
      rw [PMF.mem_support_map_iff] at hout
      obtain ⟨t, ht, rfl⟩ := hout
      have htr := (hinv_fin.1 t ht).2.1
      simpa only [EpochState.run_nil, EpochState.empty, List.nil_append] using htr
    refine ⟨ν_final, T_ops, hex_steps, hcontract, ?_⟩
    rw [hpot₀, zero_add] at hcost_fin
    simp only [Nat.cast_zero, zero_add, List.map_const', List.sum_replicate, smul_eq_mul]
    exact (le_self_add (a := T_ops)).trans hcost_fin

/-- Standard-basis (`Basis.standard`) `ObliviousSequenceImpl` certificate obtained via basis
simulation (`ObliviousSequenceImpl.toStandard`). -/
noncomputable abbrev obliviousImplStandard {U V w base : ℕ}
    (hw2 : Fits w 2) (hU_pos : 0 < U) (hU : Fits w U) (hV_pos : 0 < V) (hV : V ≤ 2 ^ w) :
    ObliviousSequenceImpl (subroutineCodeStandard U V w)
      ((Dynamic.spec U V U).toObliviousSequenceSpec (Dictionary.empty U)) w base ![] :=
  (obliviousImpl hw2 hU_pos hU hV_pos hV).toStandard

/-- **End-to-End Expected-Amortized Resizable Succinct Dictionary (`seq_expected_amortized`):**
For any key universe `0 < U < 2 ^ w`, value range `0 < V ≤ 2 ^ w`, word width `w` with `Fits w 2`,
caller base address `base` with `Fits w (base + 8)`, initial `w`-bounded state `x₀` at
`x₀.frontier = base`, and oblivious admissible operation sequence `ops` whose `1 · OPT` stepwise
peak footprint `stepSuccinctPeakWords` (`Dynamic.succinctWords 2699 888 U V w (max n_t n_{t+1})`)
fits above `base`:
1. `initCode U V w` executes in `initSteps = 68` instructions within `base + 8` words;
2. `subroutineCode U V w` (`code = resizableOpCode`) executes `ops` under `ExecSteps` within
   stepwise peak frontier `base + epochPeakSpaceBound ≤ base + stepSuccinctPeakWords`;
3. Every final state `t ∈ ν_final.support` is `w`-bounded, rests at frontier
   `≤ base + Dynamic.succinctWords 1355 441 U V w n_fin` (`1 · OPT`), keeps `regs mBase = base`,
   preserves caller memory `[0, base)`, and outputs exact canonical transcript
   `((Dynamic.spec U V U).run (Dictionary.empty U) ops).2`;
4. Total expected executed instructions satisfy
   `initSteps + T_ops ≤ initSteps + ops.length * resizableCharge` (`O(|ops| + 1)`). -/
theorem seq_expected_amortized {U V w base : ℕ} {x₀ : RData rResize}
    (ops : List (Dynamic.Op U))
    (hw2 : Fits w 2) (hU_pos : 0 < U) (hU : Fits w U) (hV_pos : 0 < V) (hV : V ≤ 2 ^ w)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hfit₀ : Fits w (base + 8))
    (hvh : (Dynamic.spec U V U).ValidHistory (Dictionary.empty U) ops)
    (hfit_ops : PeakFitsHistory (D := Dynamic.spec U V U) w base (stepSuccinctPeakWords V w)
      (Dictionary.empty U) ops) :
    let C := obliviousImpl (base := base) hw2 hU_pos hU hV_pos hV
    let n_fin := (Dictionary.dom ((Dynamic.spec U V U).run (Dictionary.empty U) ops).1).card
    ∃ (ν₀ : PMF (LatentRState (LatentSeed U) rResize))
      (ν_final : PMF (SeqROutcome (LatentSeed U) (Dynamic.Op.Result (U := U)) rResize))
      (T_ops : ℝ≥0∞),
      ExecRCodeDist w (initCode U V w) x₀ (ν₀.map LatentRState.data) initSteps (base + 8) ∧
      (∀ t ∈ ν₀.support, ∀ addr < base, t.data.mem addr = x₀.mem addr) ∧
      C.Steps ops (ν₀.map SeqROutcome.ofLatentRState) ν_final T_ops ∧
      (∀ t ∈ ν_final.support,
        t.data.Bounded w ∧
        (base ≤ t.data.frontier ∧
          t.data.frontier ≤ base + Dynamic.succinctWords 1355 441 U V w n_fin ∧
          t.data.regs mBase = base) ∧
        (∀ addr < base, t.data.mem addr = x₀.mem addr) ∧
        t.transcript = ((Dynamic.spec U V U).run (Dictionary.empty U) ops).2) ∧
      (initSteps : ℝ≥0∞) + T_ops ≤
        (initSteps : ℝ≥0∞) + ((ops.length * resizableCharge : ℕ) : ℝ≥0∞) := by
  intro C n_fin
  have hw_pos : 0 < w := Nat.pos_of_ne_zero fun h => absurd (h ▸ hw2) (by decide)
  have hv_seq : ((Dynamic.spec U V U).toObliviousSequenceSpec (Dictionary.empty U)).ValidOpSeq
      ops :=
    ((Dynamic.spec U V U).validOpSeq_iff_validHistory (Dictionary.empty U) ops).mpr hvh
  have hob_fit : ObliviousPeakFits w base C.peakSpaceBound [] ops :=
    obliviousPeakFits_of_succinctWords hw_pos hU_pos hU hV_pos hvh hfit_ops
  have hfit₀' : Fits w (base + C.spaceBound []) := by
    simpa only [C, obliviousImpl, epochSpaceBound_nil] using hfit₀
  obtain ⟨ν₀, ν_final, T_ops, he_init, hcaller₀, hex, hfin, hcontract, hcost⟩ :=
    C.seq_expected ops hx₀ hfr₀ (fun j => Fin.elim0 j) hfit₀' hv_seq hob_fit
  simp only [C, obliviousImpl, epochSpaceBound_nil] at he_init
  have htr_eq : ∀ t ∈ ν_final.support,
      t.transcript = ((Dynamic.spec U V U).run (Dictionary.empty U) ops).2 := by
    rw [(Dynamic.spec U V U).toObliviousSequenceSpec_contract_iff_of_hasStepFn
      (Dictionary.empty U) hvh] at hcontract
    exact fun t ht => hcontract t.transcript ((PMF.mem_support_map_iff _ _ _).mpr ⟨t, ht, rfl⟩)
  have hsp_le : C.spaceBound ops ≤ Dynamic.succinctWords 1355 441 U V w n_fin :=
    epochSpaceBound_le_succinctWords hw_pos hU_pos hU hV_pos hvh
  refine ⟨ν₀, ν_final, T_ops, he_init, hcaller₀, hex, fun t ht => ?_,
    by simpa [C, obliviousImpl, ObliviousSequenceImpl.totalCharge] using hcost⟩
  obtain ⟨hbdd, ⟨hlo, hhi, hreg⟩, hmem⟩ := hfin t ht
  exact ⟨hbdd, ⟨hlo, hhi.trans (Nat.add_le_add_left hsp_le base), hreg⟩, hmem, htr_eq t ht⟩

/-- **Standard-Basis End-to-End Expected-Amortized Resizable Succinct Dictionary
(`seq_expected_amortized_standard`):**
Transports `seq_expected_amortized` to `Basis.standard` via `obliviousImplStandard`. -/
theorem seq_expected_amortized_standard {U V w base : ℕ} {x₀ : RData rResize}
    (ops : List (Dynamic.Op U))
    (hw2 : Fits w 2) (hU_pos : 0 < U) (hU : Fits w U) (hV_pos : 0 < V) (hV : V ≤ 2 ^ w)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hfit₀ : Fits w (base + 8))
    (hvh : (Dynamic.spec U V U).ValidHistory (Dictionary.empty U) ops)
    (hfit_ops : PeakFitsHistory (D := Dynamic.spec U V U) w base (stepSuccinctPeakWords V w)
      (Dictionary.empty U) ops) :
    let C := obliviousImplStandard (base := base) hw2 hU_pos hU hV_pos hV
    let n_fin := (Dictionary.dom ((Dynamic.spec U V U).run (Dictionary.empty U) ops).1).card
    ∃ (ν₀ : PMF (LatentRState (LatentSeed U) rResize))
      (ν_final : PMF (SeqROutcome (LatentSeed U) (Dynamic.Op.Result (U := U)) rResize))
      (T_ops : ℝ≥0∞),
      ExecRCodeDist w (subroutineCodeStandard U V w).initCode x₀ (ν₀.map LatentRState.data)
        initSteps (base + 8) ∧
      (∀ t ∈ ν₀.support, ∀ addr < base, t.data.mem addr = x₀.mem addr) ∧
      C.Steps ops (ν₀.map SeqROutcome.ofLatentRState) ν_final T_ops ∧
      (∀ t ∈ ν_final.support,
        t.data.Bounded w ∧
        (base ≤ t.data.frontier ∧
          t.data.frontier ≤ base + Dynamic.succinctWords 1355 441 U V w n_fin ∧
          t.data.regs mBase = base) ∧
        (∀ addr < base, t.data.mem addr = x₀.mem addr) ∧
        t.transcript = ((Dynamic.spec U V U).run (Dictionary.empty U) ops).2) ∧
      (initSteps : ℝ≥0∞) + T_ops ≤
        (initSteps : ℝ≥0∞) + ((ops.length * resizableCharge : ℕ) : ℝ≥0∞) := by
  intro C n_fin
  obtain ⟨ν₀, ν_final, T_ops, he_init, hcaller₀, hex, hfin, hcost⟩ :=
    seq_expected_amortized ops hw2 hU_pos hU hV_pos hV hx₀ hfr₀ hfit₀ hvh hfit_ops
  exact ⟨ν₀, ν_final, T_ops, he_init.mapSimulates .exactStandard, hcaller₀,
    hex.mapSimulates .exactStandard, hfin, hcost⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
