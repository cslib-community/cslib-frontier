/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shared Register Context, Retained Witnesses, and Active-Epoch Prologues

Provides the shared parameter-free register space `Fin rEpoch`, retained `RealizesBounded .exact`
subroutine witnesses, ABI register conventions, `InEpochValid` / `1 · OPT` `inEpochPeakWords`
specifications, `CompactedSplitRep` frame lemmas, and verified active-epoch context-loading and
quotient-hash evaluation subroutines (`loadActiveCtxCode`, `evalKeyHashCode`) consumed by
`Dispatch.lean` (in-epoch operations) and epoch migration.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.rEpoch`, `eReg`, `rBase`..`rMicro`,
  `hpReg`, `cpReg`, `inEpochFactor`: parameter-free register bank and combined exchange factor.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.loadActiveCtxCode`, `evalKeyHashCode`:
  parameter-free `RCode .exact rEpoch` active-epoch parameter loader and key-hash evaluator.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.encode`, `argMatch`, `decode`,
  `opKey`, `InEpochValid`, `inEpochPeakWords`, `inEpochPotential`, `inEpochBaseCharge`,
  `inEpochCharge`: ABI, admissibility, peak-space, potential, and amortized charge definitions.

## Main results

* `inEpochPeakWords_le_succinctWords`: `inEpochPeakWords` is bounded by `1 · OPT` succinct words.
* `loadActiveCtxCode_exec`, `runEvalHashAtQuot`, `evalKeyHashCode_exec`: deterministic
  `RDemonicExec` certificates reconstructing `x.frontier` and evaluating `hValOfSeed`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4 and 6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise
open Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
open Cslib.Probability

/-! ## Section 1: Retained `RealizesBounded` Witnesses, Register Layout, and Exchange Factor -/

/-- `RealizesBounded` witness for computing compacted item word count `compItemWordsGenProg`. -/
noncomputable def wItemWords :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_compItemWordsGen
private noncomputable def wExtractQuot :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_compExtractQuotGen
/-- `RealizesBounded` witness for 3-wise quotient-hash evaluation `evalHashGenProg`. -/
noncomputable def wEvalHash :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_evalHashGen
/-- `RealizesBounded` witness for in-epoch compacted query `compQueryWithHashGenProg`. -/
noncomputable def wQuery :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_compQueryWithHashGen
/-- `RealizesBounded` witness for split-insert Phase 1 search `compInsertSearchWithHashGenProg`. -/
noncomputable def wInsSearch :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_compInsertSearchWithHashGen
/-- `RealizesBounded` witness for split-insert value overwrite `compWritePhysValGenProg`. -/
noncomputable def wWriteVal :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_compWritePhysValGen
/-- `RealizesBounded` witness for insert grow-delta calculation `compGrowDeltaGenProg`. -/
noncomputable def wGrowDelta :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_compGrowDeltaGen
/-- `RealizesBounded` witness for split-insert Phase 2b append `compInsertAppendNewGenProg`. -/
noncomputable def wInsAppend :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_compInsertAppendNewGen
/-- `RealizesBounded` witness for split-delete Phase 1 search `compDeletePrepWithHashGenProg`. -/
noncomputable def wDelPrep :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_compDeletePrepWithHashGen
/-- `RealizesBounded` witness for split-delete Phase 2 finish `compDeleteFinishWithHashGenProg`. -/
noncomputable def wDelFin :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_compDeleteFinishWithHashGen
/-- `RealizesBounded` witness for delete shrink-delta calculation `compShrinkDeltaGenProg`. -/
noncomputable def wShrinkDelta :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_compShrinkDeltaGen

/-- Combined parameter-free scratch register bank size across the eleven `RealizesBounded`
subroutines used in in-epoch operation dispatch. -/
noncomputable def scratchEpoch : ℕ :=
  max (1 + wItemWords.scratchSize + 1) <|
  max (1 + wExtractQuot.scratchSize + 1) <|
  max (1 + wEvalHash.scratchSize + 1) <|
  max (2 + wQuery.scratchSize + 1) <|
  max (4 + wInsSearch.scratchSize + 1) <|
  max (0 + wWriteVal.scratchSize + 1) <|
  max (1 + wGrowDelta.scratchSize + 1) <|
  max (0 + wInsAppend.scratchSize + 1) <|
  max (4 + wDelPrep.scratchSize + 1) <|
  max (0 + wDelFin.scratchSize + 1)
      (1 + wShrinkDelta.scratchSize + 1)

/-- Parameter-free register budget `88 + scratchEpoch` for in-epoch resizable succinct dispatch
(`0..24` fixed working/ABI registers, `32..50` `HashParams`, `52..87` `CompParams`, `88..`
scratch). -/
noncomputable def rEpoch : ℕ := 88 + scratchEpoch

theorem le_rEpoch : 88 ≤ rEpoch := by
  dsimp only [rEpoch]; omega

/-- Canonical embedding `Fin 88 → Fin rEpoch` for fixed control, ABI, and parameter registers. -/
noncomputable def eReg : Fin 88 → Fin rEpoch :=
  Fin.castLE le_rEpoch

private theorem eReg_injective : Function.Injective eReg :=
  Fin.castLE_injective le_rEpoch

@[simp]
theorem eReg_inj {i j : Fin 88} : eReg i = eReg j ↔ i = j :=
  eReg_injective.eq_iff

@[simp]
theorem val_eReg (i : Fin 88) : (eReg i).val = i.val := by
  dsimp only [eReg]; rfl

theorem eReg_lt_88 (i : Fin 88) : (eReg i).val < 88 := i.isLt

theorem eReg_ne {i j : Fin 88} (h : i ≠ j) : eReg i ≠ eReg j :=
  fun heq => h (eReg_injective heq)

/-- Persistent base-address register `0`. -/
noncomputable abbrev rBase : Fin rEpoch := eReg 0
/-- Hardware frontier tracking register `1`. -/
noncomputable abbrev rFr : Fin rEpoch := eReg 1
/-- Operation tag input register `2` (`0` = `query`, `1` = `insert`, `2` = `delete`). -/
noncomputable abbrev rTag : Fin rEpoch := eReg 2
/-- Input key register `3` (`u.val`). -/
noncomputable abbrev rArgU : Fin rEpoch := eReg 3
/-- Input value register `4` (`v` for `insert`, `0` otherwise). -/
noncomputable abbrev rArgV : Fin rEpoch := eReg 4
/-- Output presence tag register `5` (`0` = `none`, `1` = `some`). -/
noncomputable abbrev rOutTag : Fin rEpoch := eReg 5
/-- Output value register `6` (`v` if found, `0` otherwise). -/
noncomputable abbrev rOutVal : Fin rEpoch := eReg 6
/-- Word count delta register `7` for `growZeroCode` / `shrinkCode`. -/
noncomputable abbrev rK : Fin rEpoch := eReg 7
/-- Result pointer register `8` for `growZeroCode`. -/
noncomputable abbrev rRes : Fin rEpoch := eReg 8
/-- Current address / temporary offset register `9`. -/
noncomputable abbrev rCur : Fin rEpoch := eReg 9
/-- Loop index / offset scratch register `10`. -/
noncomputable abbrev rIdx : Fin rEpoch := eReg 10
/-- Constant-`0` scratch register `11`. -/
noncomputable abbrev rZero : Fin rEpoch := eReg 11
/-- Constant-`1` scratch register `12`. -/
noncomputable abbrev rOne : Fin rEpoch := eReg 12
/-- Active element count `n` register `13`. -/
noncomputable abbrev rCnt : Fin rEpoch := eReg 13
/-- Compacted item-stream base address `base + offCompItems` register `14`. -/
noncomputable abbrev rItemBase : Fin rEpoch := eReg 14
/-- Quotient-hash base address `base + epochHdrWords` register `15`. -/
noncomputable abbrev rHashBase : Fin rEpoch := eReg 15
/-- Limb-scratch base address `base + offScratch` register `16`. -/
noncomputable abbrev rScratchBase : Fin rEpoch := eReg 16
/-- Extracted quotient input register `17` for `evalHashGenProg`. -/
noncomputable abbrev rQuot : Fin rEpoch := eReg 17
/-- Evaluated hash output register `18` from `evalHashGenProg`. -/
noncomputable abbrev rHashOut : Fin rEpoch := eReg 18
/-- Saved primary hash value `h_q` register `19` across two-phase deletion. -/
noncomputable abbrev rHq : Fin rEpoch := eReg 19
/-- Bucket search `found` flag register `20`. -/
noncomputable abbrev rFound : Fin rEpoch := eReg 20
/-- Deletion logical slot index `j_del` register `21`. -/
noncomputable abbrev rJDel : Fin rEpoch := eReg 21
/-- Resolved physical slot index `phys` register `22`. -/
noncomputable abbrev rPhys : Fin rEpoch := eReg 22
/-- Feistel bucket index `b` register `23`. -/
noncomputable abbrev rBucket : Fin rEpoch := eReg 23
/-- Micro-bucket index `m` register `24`. -/
noncomputable abbrev rMicro : Fin rEpoch := eReg 24

/-- Register bank `32..50` holding the 19 words of `RuntimeReducedKWise.HashParams`. -/
@[expose]
noncomputable def hpReg (i : Fin 19) : Fin rEpoch :=
  eReg ⟨32 + i.val, by omega⟩

/-- Register bank `52..87` holding the 36 words of `CompParams`. -/
@[expose]
noncomputable def cpReg (i : Fin 36) : Fin rEpoch :=
  eReg ⟨52 + i.val, by omega⟩

@[simp]
theorem val_hpReg (i : Fin 19) : (hpReg i).val = 32 + i.val := by
  dsimp only [hpReg]; rw [val_eReg]

@[simp]
theorem val_cpReg (i : Fin 36) : (cpReg i).val = 52 + i.val := by
  dsimp only [cpReg]; rw [val_eReg]

theorem rGrow_nodup : ([rK, rRes, rCur, rIdx, rZero, rOne] : List (Fin rEpoch)).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
    rK, rRes, rCur, rIdx, rZero, rOne, eReg_inj]
  decide

theorem rShrink_nodup : ([rK, rIdx, rZero, rOne] : List (Fin rEpoch)).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true,
    rK, rIdx, rZero, rOne, eReg_inj]
  decide

/-- Combined parameter-free exchange factor `≥ 1` dominating all eleven `RealizesBounded`
subroutines. -/
noncomputable def inEpochFactor : ℕ :=
  max 1 <|
  max wItemWords.factor <|
  max wExtractQuot.factor <|
  max wEvalHash.factor <|
  max wQuery.factor <|
  max wInsSearch.factor <|
  max wWriteVal.factor <|
  max wGrowDelta.factor <|
  max wInsAppend.factor <|
  max wDelPrep.factor <|
  max wDelFin.factor
      wShrinkDelta.factor

theorem one_le_inEpochFactor : 1 ≤ inEpochFactor := le_max_left _ _

theorem factor_wItemWords_le : wItemWords.factor ≤ inEpochFactor := by
  simp only [inEpochFactor, le_max_iff, le_refl, or_true, true_or]
private theorem factor_wExtractQuot_le : wExtractQuot.factor ≤ inEpochFactor := by
  simp only [inEpochFactor, le_max_iff, le_refl, or_true, true_or]
private theorem factor_wEvalHash_le : wEvalHash.factor ≤ inEpochFactor := by
  simp only [inEpochFactor, le_max_iff, le_refl, or_true, true_or]
theorem factor_wQuery_le : wQuery.factor ≤ inEpochFactor := by
  simp only [inEpochFactor, le_max_iff, le_refl, or_true, true_or]
theorem factor_wInsSearch_le : wInsSearch.factor ≤ inEpochFactor := by
  simp only [inEpochFactor, le_max_iff, le_refl, or_true, true_or]
theorem factor_wWriteVal_le : wWriteVal.factor ≤ inEpochFactor := by
  simp only [inEpochFactor, le_max_iff, le_refl, or_true, true_or]
theorem factor_wGrowDelta_le : wGrowDelta.factor ≤ inEpochFactor := by
  simp only [inEpochFactor, le_max_iff, le_refl, or_true, true_or]
theorem factor_wInsAppend_le : wInsAppend.factor ≤ inEpochFactor := by
  simp only [inEpochFactor, le_max_iff, le_refl, or_true, true_or]
theorem factor_wDelPrep_le : wDelPrep.factor ≤ inEpochFactor := by
  simp only [inEpochFactor, le_max_iff, le_refl, or_true, true_or]
theorem factor_wDelFin_le : wDelFin.factor ≤ inEpochFactor := by
  simp only [inEpochFactor, le_max_iff, le_refl, or_true, true_or]
theorem factor_wShrinkDelta_le : wShrinkDelta.factor ≤ inEpochFactor := by
  simp only [inEpochFactor, le_max_iff, le_refl, or_true]

/-! ## Section 2: Generic Register-Wiring Combinators and Emitted Subroutines -/

/-- Single-register source map `Fin 1 → Fin r` selecting `reg`. -/
abbrev reg1 {r : ℕ} (reg : Fin r) : Fin 1 → Fin r := fun _ => reg

/-- Concatenation of two register source maps `Fin k₁ → Fin r` and `Fin k₂ → Fin r`. -/
abbrev pairSrc {r k₁ k₂ : ℕ} (s₁ : Fin k₁ → Fin r) (s₂ : Fin k₂ → Fin r) :
    Fin (k₁ + k₂) → Fin r :=
  Fin.append s₁ s₂

/-- Register-bank encoding predicate decoupled from syntactic `WordEncoding.width` equality. -/
def RegsEncode {r : ℕ} {α : Type} [WordEncoding α] {k : ℕ} (x : RData r)
    (s : Fin k → Fin r) (a : α) : Prop :=
  ∃ hk : k = WordEncoding.width α,
    ∀ i : Fin k, x.regs (s i) = WordEncoding.encode a (Fin.cast hk i)

theorem RegsEncode.eq {r : ℕ} {α : Type} [WordEncoding α] {x : RData r}
    {s : Fin (WordEncoding.width α) → Fin r} {a : α} (h : RegsEncode x s a) :
    x.regs ∘ s = WordEncoding.encode a := by
  obtain ⟨hk, hf⟩ := h
  have hk_rfl : hk = rfl := Subsingleton.elim _ _
  subst hk_rfl
  exact funext hf

theorem regs_reg1_eq {r : ℕ} {x : RData r} (reg : Fin r) {v : ℕ}
    (hv : x.regs reg = v) :
    RegsEncode x (reg1 reg) v :=
  ⟨rfl, fun i => by fin_cases i; exact hv⟩

theorem regs_hp_eq {r : ℕ} {x : RData r} {s : Fin 19 → Fin r} {hp : HashParams}
    (h : ∀ i : Fin 19, x.regs (s i) = hp i) :
    RegsEncode x s hp :=
  ⟨rfl, h⟩

theorem regs_cp_eq {r : ℕ} {x : RData r} {s : Fin 36 → Fin r} {cp : CompParams}
    (h : ∀ i : Fin 36, x.regs (s i) = cp i) :
    RegsEncode x s cp :=
  ⟨rfl, h⟩

theorem encode_pair2_0 (a b c d : ℕ) :
    WordEncoding.encode ((a, b), (c, d)) 0 = a := rfl
theorem encode_pair2_1 (a b c d : ℕ) :
    WordEncoding.encode ((a, b), (c, d)) 1 = b := rfl
theorem encode_pair2_2 (a b c d : ℕ) :
    WordEncoding.encode ((a, b), (c, d)) 2 = c := rfl
theorem encode_pair2_3 (a b c d : ℕ) :
    WordEncoding.encode ((a, b), (c, d)) 3 = d := rfl

theorem encode_left4_0 (a b c d : ℕ) :
    WordEncoding.encode (((a, b), c), d) 0 = a := rfl
theorem encode_left4_1 (a b c d : ℕ) :
    WordEncoding.encode (((a, b), c), d) 1 = b := rfl
theorem encode_left4_2 (a b c d : ℕ) :
    WordEncoding.encode (((a, b), c), d) 2 = c := rfl
theorem encode_left4_3 (a b c d : ℕ) :
    WordEncoding.encode (((a, b), c), d) 3 = d := rfl

theorem regs_pairSrc {r : ℕ} {α β : Type} [WordEncoding α] [WordEncoding β]
    {k₁ k₂ : ℕ} {x : RData r}
    {s₁ : Fin k₁ → Fin r} {s₂ : Fin k₂ → Fin r} {a : α} {b : β}
    (h₁ : RegsEncode x s₁ a) (h₂ : RegsEncode x s₂ b) :
    RegsEncode x (pairSrc s₁ s₂) (a, b) := by
  obtain ⟨rfl, hf₁⟩ := h₁
  obtain ⟨rfl, hf₂⟩ := h₂
  refine ⟨rfl, fun i => i.addCases (fun j => ?_) (fun j => ?_)⟩
  · change x.regs (Fin.append s₁ s₂ (Fin.castAdd _ j)) =
      Fin.append (WordEncoding.encode a) (WordEncoding.encode b) (Fin.castAdd _ j)
    rw [Fin.append_left, Fin.append_left]
    exact hf₁ j
  · change x.regs (Fin.append s₁ s₂ (Fin.natAdd _ j)) =
      Fin.append (WordEncoding.encode a) (WordEncoding.encode b) (Fin.natAdd _ j)
    rw [Fin.append_right, Fin.append_right]
    exact hf₂ j

theorem pairSrc_forall {r : ℕ} {P : Fin r → Prop} {k₁ k₂ : ℕ}
    {s₁ : Fin k₁ → Fin r} {s₂ : Fin k₂ → Fin r}
    (h₁ : ∀ i, P (s₁ i)) (h₂ : ∀ j, P (s₂ j)) :
    ∀ i, P (pairSrc s₁ s₂ i) := fun i =>
  i.addCases
    (fun j => by dsimp only [pairSrc]; rw [Fin.append_left]; exact h₁ j)
    (fun j => by dsimp only [pairSrc]; rw [Fin.append_right]; exact h₂ j)

theorem pairSrc_lt {r bound k₁ k₂ : ℕ} {s₁ : Fin k₁ → Fin r} {s₂ : Fin k₂ → Fin r}
    (h₁ : ∀ i, (s₁ i).val < bound) (h₂ : ∀ j, (s₂ j).val < bound) :
    ∀ i, (pairSrc s₁ s₂ i).val < bound :=
  pairSrc_forall (P := fun reg => reg.val < bound) h₁ h₂

theorem pairSrc_ne_reg {r k₁ k₂ : ℕ} {reg : Fin r} {s₁ : Fin k₁ → Fin r} {s₂ : Fin k₂ → Fin r}
    (h₁ : ∀ i, s₁ i ≠ reg) (h₂ : ∀ j, s₂ j ≠ reg) :
    ∀ i, pairSrc s₁ s₂ i ≠ reg :=
  pairSrc_forall (P := fun x => x ≠ reg) h₁ h₂

theorem pairSrc_ne_outs {r k₁ k₂ l : ℕ} {s₁ : Fin k₁ → Fin r}
    {s₂ : Fin k₂ → Fin r} {outs : Fin l → Fin r}
    (h₁ : ∀ i a, s₁ i ≠ outs a) (h₂ : ∀ j a, s₂ j ≠ outs a) :
    ∀ i a, pairSrc s₁ s₂ i ≠ outs a :=
  pairSrc_forall (P := fun reg => ∀ a, reg ≠ outs a) h₁ h₂

/-- Scratch-and-output register map placing `l` outputs in `outs` and the remaining `s + 1`
temporaries consecutively starting at `baseOff + l` inside `Fin r`. -/
def mkTmp {r baseOff l s : ℕ} (outs : Fin l → Fin r) (hb : baseOff + (l + s + 1) ≤ r)
    (j : Fin (l + s + 1)) : Fin r :=
  if h : j.val < l then outs ⟨j.val, h⟩
  else ⟨baseOff + j.val, by have := j.isLt; omega⟩

private theorem val_mkTmp {r baseOff l s : ℕ} (outs : Fin l → Fin r)
    (hb : baseOff + (l + s + 1) ≤ r) (j : Fin (l + s + 1)) :
    (mkTmp (baseOff := baseOff) outs hb j).val =
      if h : j.val < l then (outs ⟨j.val, h⟩).val else baseOff + j.val := by
  dsimp only [mkTmp]; split_ifs <;> rfl

@[simp]
theorem mkTmp_castAdd {r baseOff l s : ℕ} (outs : Fin l → Fin r)
    (hb : baseOff + (l + s + 1) ≤ r) (i : Fin l) :
    mkTmp (baseOff := baseOff) outs hb (Fin.castAdd (s + 1) i) = outs i := by
  dsimp only [mkTmp]
  split_ifs with h
  · rfl
  · exfalso; exact h i.isLt

theorem mkTmp_injective {r baseOff l s : ℕ} {outs : Fin l → Fin r}
    (hb : baseOff + (l + s + 1) ≤ r)
    (hinj : Function.Injective outs) (hlt : ∀ i : Fin l, (outs i).val < baseOff) :
    Function.Injective (mkTmp (baseOff := baseOff) outs hb) := by
  intro j₁ j₂ heq
  have hv := congrArg Fin.val heq
  rw [val_mkTmp, val_mkTmp] at hv
  by_cases h₁ : j₁.val < l <;> by_cases h₂ : j₂.val < l <;>
    simp only [h₁, h₂, ↓reduceDIte] at hv
  · have hi := hinj (Fin.ext hv)
    exact Fin.ext (congrArg (Fin.val (n := l)) hi)
  · have := hlt ⟨j₁.val, h₁⟩; omega
  · have := hlt ⟨j₂.val, h₂⟩; omega
  · exact Fin.ext (by omega)

theorem src_ne_mkTmp {r baseOff k l s : ℕ} {src : Fin k → Fin r} {outs : Fin l → Fin r}
    (hb : baseOff + (l + s + 1) ≤ r) (hsrc_lt : ∀ i : Fin k, (src i).val < baseOff)
    (hdisj : ∀ (i : Fin k) (a : Fin l), src i ≠ outs a) :
    ∀ (i : Fin k) (j : Fin (l + s + 1)), src i ≠ mkTmp (baseOff := baseOff) outs hb j := by
  intro i j heq
  have hv := congrArg Fin.val heq
  rw [val_mkTmp] at hv
  split_ifs at hv with hj
  · exact hdisj i ⟨j.val, hj⟩ (Fin.ext hv)
  · have := hsrc_lt i; omega

theorem mkTmp_ne_reg {r baseOff l s : ℕ} {outs : Fin l → Fin r}
    (hb : baseOff + (l + s + 1) ≤ r) {reg : Fin r}
    (hreg_lt : reg.val < baseOff) (hne : ∀ a : Fin l, outs a ≠ reg) :
    ∀ j : Fin (l + s + 1), mkTmp (baseOff := baseOff) outs hb j ≠ reg := by
  intro j heq
  have hv := congrArg Fin.val heq
  rw [val_mkTmp] at hv
  split_ifs at hv with hj
  · exact hne ⟨j.val, hj⟩ (Fin.ext hv)
  · omega

theorem outs1_inj {r : ℕ} (reg : Fin r) : Function.Injective ![reg] := by
  intro a b _; fin_cases a; fin_cases b; rfl

theorem outs2_inj {r : ℕ} {r0 r1 : Fin r} (h : r0 ≠ r1) :
    Function.Injective ![r0, r1] := by
  intro a b heq
  fin_cases a <;> fin_cases b
  · rfl
  · exact absurd heq h
  · exact absurd heq.symm h
  · rfl

private theorem epochTmpHb {n : ℕ} (hb : n ≤ scratchEpoch) : 88 + n ≤ rEpoch :=
  Nat.add_le_add_left hb 88

private noncomputable abbrev srcItemWords := pairSrc cpReg (reg1 rCnt)
private noncomputable def tmpItemWords :=
  mkTmp (baseOff := 88) ![rCur] (epochTmpHb (le_max_left _ _))

private noncomputable abbrev srcExtractQuot := pairSrc cpReg (reg1 rArgU)
private noncomputable def tmpExtractQuot :=
  mkTmp (baseOff := 88) ![rQuot] (epochTmpHb (le_max_of_le_right (le_max_left _ _)))

/-- Input register wiring `(hp, hashBase, scratchBase, q)` for `wEvalHash`. -/
noncomputable abbrev srcEvalHash :=
  pairSrc hpReg (pairSrc (reg1 rHashBase) (pairSrc (reg1 rScratchBase) (reg1 rQuot)))
/-- Output and scratch register wiring for `wEvalHash` (writing `rHashOut`). -/
noncomputable def tmpEvalHash :=
  mkTmp (baseOff := 88) ![rHashOut]
    (epochTmpHb (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))

/-- Input register wiring `((cp, (base, itemBase)), (u, h_q))` for `wQuery` and `wInsSearch`. -/
noncomputable abbrev srcKeyHashOp :=
  pairSrc (pairSrc cpReg (pairSrc (reg1 rBase) (reg1 rItemBase)))
    (pairSrc (reg1 rArgU) (reg1 rHashOut))

/-- Output and scratch register wiring for `wQuery` (writing `rOutTag`, `rOutVal`). -/
noncomputable def tmpQuery :=
  mkTmp (baseOff := 88) ![rOutTag, rOutVal]
    (epochTmpHb (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))

/-- Output and scratch register wiring for `wInsSearch` (writing `rFound`, `rPhys`, `rBucket`,
`rMicro`). -/
noncomputable def tmpInsSearch :=
  mkTmp (baseOff := 88) ![rFound, rPhys, rBucket, rMicro]
    (epochTmpHb (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _))))))

/-- Input register wiring `(((cp, (base, itemBase)), phys), v)` for `wWriteVal`. -/
noncomputable abbrev srcWriteVal :=
  pairSrc (pairSrc (pairSrc cpReg (pairSrc (reg1 rBase) (reg1 rItemBase))) (reg1 rPhys))
    (reg1 rArgV)
/-- Output and scratch register wiring for `wWriteVal`. -/
noncomputable def tmpWriteVal :=
  mkTmp (baseOff := 88) ![] (epochTmpHb (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))

/-- Input register wiring `(cp, n)` for `wGrowDelta`. -/
noncomputable abbrev srcGrowDelta := pairSrc cpReg (reg1 rCnt)
/-- Output and scratch register wiring for `wGrowDelta` (writing `rK`). -/
noncomputable def tmpGrowDelta :=
  mkTmp (baseOff := 88) ![rK] (epochTmpHb (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _))))))))

/-- Input register wiring `(((cp, (base, itemBase)), (b, m)), (u, v))` for `wInsAppend`. -/
noncomputable abbrev srcInsAppend :=
  pairSrc (pairSrc (pairSrc cpReg (pairSrc (reg1 rBase) (reg1 rItemBase)))
      (pairSrc (reg1 rBucket) (reg1 rMicro)))
    (pairSrc (reg1 rArgU) (reg1 rArgV))
/-- Output and scratch register wiring for `wInsAppend`. -/
noncomputable def tmpInsAppend :=
  mkTmp (baseOff := 88) ![] (epochTmpHb (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _)))))))))

/-- Input register wiring `((cp, (base, itemBase)), (u, h_q))` for `wDelPrep`. -/
noncomputable abbrev srcDelPrep :=
  pairSrc (pairSrc cpReg (pairSrc (reg1 rBase) (reg1 rItemBase)))
    (pairSrc (reg1 rArgU) (reg1 rHq))
/-- Output and scratch register wiring for `wDelPrep` (writing `rFound`, `rJDel`, `rPhys`,
`rQuot`). -/
noncomputable def tmpDelPrep :=
  mkTmp (baseOff := 88) ![rFound, rJDel, rPhys, rQuot]
    (epochTmpHb (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_left _ _))))))))))

/-- Input register wiring `((srcDelPrep, ((found, j_del), phys)), h_q_last)` for `wDelFin`. -/
noncomputable abbrev srcDelFin :=
  pairSrc (pairSrc srcDelPrep (pairSrc (pairSrc (reg1 rFound) (reg1 rJDel)) (reg1 rPhys)))
    (reg1 rHashOut)
/-- Output and scratch register wiring for `wDelFin`. -/
noncomputable def tmpDelFin :=
  mkTmp (baseOff := 88) ![] (epochTmpHb (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))))))

/-- Input register wiring `(cp, n)` for `wShrinkDelta`. -/
noncomputable abbrev srcShrinkDelta := pairSrc cpReg (reg1 rCnt)
/-- Output and scratch register wiring for `wShrinkDelta` (writing `rK`). -/
noncomputable def tmpShrinkDelta :=
  mkTmp (baseOff := 88) ![rK] (epochTmpHb (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))))))))))

private theorem tmpItemWords_out :
    tmpItemWords (Fin.castAdd (wItemWords.scratchSize + 1) (0 : Fin (WordEncoding.width ℕ))) =
      rCur := mkTmp_castAdd _ _ 0

private theorem tmpExtractQuot_out :
    tmpExtractQuot (Fin.castAdd (wExtractQuot.scratchSize + 1) (0 : Fin (WordEncoding.width ℕ))) =
      rQuot := mkTmp_castAdd _ _ 0

private theorem tmpEvalHash_out :
    tmpEvalHash (Fin.castAdd (wEvalHash.scratchSize + 1) (0 : Fin (WordEncoding.width ℕ))) =
      rHashOut := mkTmp_castAdd _ _ 0

theorem tmpGrowDelta_out :
    tmpGrowDelta (Fin.castAdd (wGrowDelta.scratchSize + 1) (0 : Fin (WordEncoding.width ℕ))) =
      rK := mkTmp_castAdd _ _ 0

theorem tmpShrinkDelta_out :
    tmpShrinkDelta (Fin.castAdd (wShrinkDelta.scratchSize + 1) (0 : Fin (WordEncoding.width ℕ))) =
      rK := mkTmp_castAdd _ _ 0

theorem tmpQuery_out_0 :
    tmpQuery (Fin.castAdd (wQuery.scratchSize + 1) (0 : Fin (WordEncoding.width (Option ℕ)))) =
      rOutTag := mkTmp_castAdd _ _ 0

theorem tmpQuery_out_1 :
    tmpQuery (Fin.castAdd (wQuery.scratchSize + 1) (1 : Fin (WordEncoding.width (Option ℕ)))) =
      rOutVal := mkTmp_castAdd _ _ 1

theorem tmpInsSearch_out (i : Fin (WordEncoding.width ((ℕ × ℕ) × (ℕ × ℕ)))) :
    tmpInsSearch (Fin.castAdd (wInsSearch.scratchSize + 1) i) =
      ![rFound, rPhys, rBucket, rMicro] i := mkTmp_castAdd _ _ i

theorem tmpDelPrep_out (i : Fin (WordEncoding.width (((ℕ × ℕ) × ℕ) × ℕ))) :
    tmpDelPrep (Fin.castAdd (wDelPrep.scratchSize + 1) i) =
      ![rFound, rJDel, rPhys, rQuot] i := mkTmp_castAdd _ _ i

theorem tmpQuery_ne_reg {reg : Fin rEpoch} (h88 : reg.val < 88)
    (h0 : reg ≠ rOutTag) (h1 : reg ≠ rOutVal) : ∀ j, tmpQuery j ≠ reg :=
  mkTmp_ne_reg _ h88 (fun a => by fin_cases a <;> first | exact h0.symm | exact h1.symm)

theorem tmpInsSearch_ne_reg {reg : Fin rEpoch} (h88 : reg.val < 88)
    (hf : reg ≠ rFound) (hp : reg ≠ rPhys) (hb : reg ≠ rBucket) (hm : reg ≠ rMicro) :
    ∀ j, tmpInsSearch j ≠ reg :=
  mkTmp_ne_reg _ h88 (fun a => by
    fin_cases a <;> first | exact hf.symm | exact hp.symm | exact hb.symm | exact hm.symm)

theorem tmpWriteVal_ne_reg {reg : Fin rEpoch} (h88 : reg.val < 88) : ∀ j, tmpWriteVal j ≠ reg :=
  mkTmp_ne_reg _ h88 (fun a => Fin.elim0 a)

theorem tmpGrowDelta_ne_reg {reg : Fin rEpoch} (h88 : reg.val < 88) (hk : reg ≠ rK) :
    ∀ j, tmpGrowDelta j ≠ reg :=
  mkTmp_ne_reg _ h88 (fun a => by fin_cases a; exact hk.symm)

theorem tmpInsAppend_ne_reg {reg : Fin rEpoch} (h88 : reg.val < 88) : ∀ j, tmpInsAppend j ≠ reg :=
  mkTmp_ne_reg _ h88 (fun a => Fin.elim0 a)

theorem tmpDelPrep_ne_reg {reg : Fin rEpoch} (h88 : reg.val < 88)
    (hf : reg ≠ rFound) (hj : reg ≠ rJDel) (hp : reg ≠ rPhys) (hq : reg ≠ rQuot) :
    ∀ j, tmpDelPrep j ≠ reg :=
  mkTmp_ne_reg _ h88 (fun a => by
    fin_cases a <;> first | exact hf.symm | exact hj.symm | exact hp.symm | exact hq.symm)

theorem tmpDelFin_ne_reg {reg : Fin rEpoch} (h88 : reg.val < 88) : ∀ j, tmpDelFin j ≠ reg :=
  mkTmp_ne_reg _ h88 (fun a => Fin.elim0 a)

theorem tmpShrinkDelta_ne_reg {reg : Fin rEpoch} (h88 : reg.val < 88) (hk : reg ≠ rK) :
    ∀ j, tmpShrinkDelta j ≠ reg :=
  mkTmp_ne_reg _ h88 (fun a => by fin_cases a; exact hk.symm)

/-! ## Section 3: Offset Memory Primitives and Active-Epoch Prologues -/

/-- Load `mem (regs rAddr + off)` into `rDst` using `rTmp` as scratch (`3` instructions). -/
def loadAtOffCode {r : ℕ} (rAddr rDst rTmp : Fin r) (off : ℕ) : RCode .exact r :=
  .seq (.op (.const rTmp off))
  (.seq (.op (.exactBin .add rTmp rAddr rTmp))
        (.op (.load rDst rTmp)))

/-- Store `regs rSrc` into `mem (regs rAddr + off)` using `rTmp` as scratch (`3` instructions). -/
def storeAtOffCode {r : ℕ} (rAddr rSrc rTmp : Fin r) (off : ℕ) : RCode .exact r :=
  .seq (.op (.const rTmp off))
  (.seq (.op (.exactBin .add rTmp rAddr rTmp))
        (.op (.store rTmp rSrc)))

/-- Load `k + 1` consecutive words starting at `regs rAddr + startOff` into `dst 0 .. dst k`
using `rTmp` as address scratch (`3 * (k + 1)` instructions). -/
def loadBlockUpTo {r m : ℕ} (rAddr rTmp : Fin r) (dst : Fin m → Fin r) (startOff : ℕ) :
    (k : ℕ) → k < m → RCode .exact r
  | 0, hk => loadAtOffCode rAddr (dst ⟨0, hk⟩) rTmp startOff
  | k + 1, hk =>
    .seq (loadBlockUpTo rAddr rTmp dst startOff k (by omega))
         (loadAtOffCode rAddr (dst ⟨k + 1, hk⟩) rTmp (startOff + (k + 1)))

/-- Active-epoch prologue (`0 < n`): loads `HashParams` and `CompParams` from `[base + 8, +55)`,
evaluates `compactedItemWords U V w N n` via `wItemWords`, and populates `rScratchBase`,
`rHashBase`, `rItemBase`, and `rFr = x.frontier`. -/
noncomputable def loadActiveCtxCode : RCode .exact rEpoch :=
  .seq (loadBlockUpTo rBase rCur hpReg offHashParams 18 (by decide)) <|
  .seq (loadBlockUpTo rBase rCur cpReg offCompParams 35 (by decide)) <|
  .seq (.op (.const rFr 0)) <|
  .seq (RCode.ofCode (wItemWords.code rFr srcItemWords tmpItemWords)) <|
  .seq (.op (.const rIdx offScratch)) <|
  .seq (.op (.exactBin .add rScratchBase rBase rIdx)) <|
  .seq (.op (.const rIdx epochHdrWords)) <|
  .seq (.op (.exactBin .add rHashBase rBase rIdx)) <|
  .seq (.op (.exactBin .add rItemBase rBase (cpReg ⟨34, by decide⟩)))
       (.op (.exactBin .add rFr rItemBase rCur))

/-- Extract `q = keyQuotient (bucketBits N) u` into `rQuot` and evaluate `h_q` into `rHashOut`. -/
noncomputable def evalKeyHashCode : RCode .exact rEpoch :=
  .seq (RCode.ofCode (wExtractQuot.code rFr srcExtractQuot tmpExtractQuot))
       (RCode.ofCode (wEvalHash.code rFr srcEvalHash tmpEvalHash))


/-! ## Section 4: Register Disjointness and Prologue Width-Independence (`¬ReadsWidth`) -/

theorem hpReg_lt_88 (i : Fin 19) : (hpReg i).val < 88 := by
  rw [val_hpReg]; omega

theorem cpReg_lt_88 (i : Fin 36) : (cpReg i).val < 88 := by
  rw [val_cpReg]; omega

theorem hpReg_ne_eReg (i : Fin 19) {c : Fin 88} (hc : c.val < 32) :
    hpReg i ≠ eReg c := by
  intro h; have hv := congrArg Fin.val h; rw [val_hpReg, val_eReg] at hv; omega

theorem cpReg_ne_eReg (i : Fin 36) {c : Fin 88} (hc : c.val < 52) :
    cpReg i ≠ eReg c := by
  intro h; have hv := congrArg Fin.val h; rw [val_cpReg, val_eReg] at hv; omega

private theorem pairSrc_lt_88 {k₁ k₂ : ℕ} {s₁ : Fin k₁ → Fin rEpoch}
    {s₂ : Fin k₂ → Fin rEpoch}
    (h₁ : ∀ i, (s₁ i).val < 88) (h₂ : ∀ j, (s₂ j).val < 88) :
    ∀ i, (pairSrc s₁ s₂ i).val < 88 :=
  pairSrc_lt h₁ h₂

private theorem pairSrc_ne_rFr {k₁ k₂ : ℕ} {s₁ : Fin k₁ → Fin rEpoch}
    {s₂ : Fin k₂ → Fin rEpoch}
    (h₁ : ∀ i, s₁ i ≠ rFr) (h₂ : ∀ j, s₂ j ≠ rFr) :
    ∀ i, pairSrc s₁ s₂ i ≠ rFr :=
  pairSrc_ne_reg h₁ h₂

private theorem outs2_query_inj : Function.Injective ![rOutTag, rOutVal] :=
  outs2_inj (eReg_ne (by decide))

private theorem outs4_ins_inj : Function.Injective ![rFound, rPhys, rBucket, rMicro] := by
  intro a b h
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [rFound, rPhys, rBucket, rMicro] at hv ⊢

private theorem outs4_del_inj : Function.Injective ![rFound, rJDel, rPhys, rQuot] := by
  intro a b h
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;> simp [rFound, rJDel, rPhys, rQuot] at hv ⊢

private theorem tmpItemWords_inj : Function.Injective tmpItemWords :=
  mkTmp_injective _ (outs1_inj rCur) (fun i => by fin_cases i; exact eReg_lt_88 _)
private theorem srcItemWords_ne_tmp : ∀ i j, srcItemWords i ≠ tmpItemWords j :=
  src_ne_mkTmp _ (pairSrc_lt_88 cpReg_lt_88 (fun _ => eReg_lt_88 _)) <|
    pairSrc_ne_outs (fun i a => by fin_cases a; exact cpReg_ne_eReg i (by decide))
      (fun _ a => by fin_cases a; exact eReg_ne (by decide))
private theorem tmpItemWords_ne_rFr : ∀ j, tmpItemWords j ≠ rFr :=
  mkTmp_ne_reg _ (eReg_lt_88 _) (fun a => by fin_cases a; exact eReg_ne (by decide))
private theorem srcItemWords_ne_rFr : ∀ i, srcItemWords i ≠ rFr :=
  pairSrc_ne_rFr (fun i => cpReg_ne_eReg i (by decide)) (fun _ => eReg_ne (by decide))

private theorem tmpExtractQuot_inj : Function.Injective tmpExtractQuot :=
  mkTmp_injective _ (outs1_inj rQuot) (fun i => by fin_cases i; exact eReg_lt_88 _)
private theorem srcExtractQuot_ne_tmp : ∀ i j, srcExtractQuot i ≠ tmpExtractQuot j :=
  src_ne_mkTmp _ (pairSrc_lt_88 cpReg_lt_88 (fun _ => eReg_lt_88 _)) <|
    pairSrc_ne_outs (fun i a => by fin_cases a; exact cpReg_ne_eReg i (by decide))
      (fun _ a => by fin_cases a; exact eReg_ne (by decide))
private theorem tmpExtractQuot_ne_rFr : ∀ j, tmpExtractQuot j ≠ rFr :=
  mkTmp_ne_reg _ (eReg_lt_88 _) (fun a => by fin_cases a; exact eReg_ne (by decide))
private theorem srcExtractQuot_ne_rFr : ∀ i, srcExtractQuot i ≠ rFr :=
  pairSrc_ne_rFr (fun i => cpReg_ne_eReg i (by decide)) (fun _ => eReg_ne (by decide))

theorem tmpEvalHash_inj : Function.Injective tmpEvalHash :=
  mkTmp_injective _ (outs1_inj rHashOut) (fun i => by fin_cases i; exact eReg_lt_88 _)
theorem srcEvalHash_ne_tmp : ∀ i j, srcEvalHash i ≠ tmpEvalHash j :=
  src_ne_mkTmp _
    (pairSrc_lt_88 hpReg_lt_88
      (pairSrc_lt_88 (fun _ => eReg_lt_88 _)
        (pairSrc_lt_88 (fun _ => eReg_lt_88 _) (fun _ => eReg_lt_88 _)))) <|
    pairSrc_ne_outs (fun i a => by fin_cases a; exact hpReg_ne_eReg i (by decide))
      (pairSrc_ne_outs (fun _ a => by fin_cases a; exact eReg_ne (by decide))
        (pairSrc_ne_outs (fun _ a => by fin_cases a; exact eReg_ne (by decide))
          (fun _ a => by fin_cases a; exact eReg_ne (by decide))))
theorem tmpEvalHash_ne_rFr : ∀ j, tmpEvalHash j ≠ rFr :=
  mkTmp_ne_reg _ (eReg_lt_88 _) (fun a => by fin_cases a; exact eReg_ne (by decide))
theorem srcEvalHash_ne_rFr : ∀ i, srcEvalHash i ≠ rFr :=
  pairSrc_ne_rFr (fun i => hpReg_ne_eReg i (by decide))
    (pairSrc_ne_rFr (fun _ => eReg_ne (by decide))
      (pairSrc_ne_rFr (fun _ => eReg_ne (by decide)) (fun _ => eReg_ne (by decide))))

private theorem srcKeyHashOp_lt_88 : ∀ i, (srcKeyHashOp i).val < 88 :=
  pairSrc_lt_88 (pairSrc_lt_88 cpReg_lt_88 (pairSrc_lt_88 (fun _ => eReg_lt_88 _)
    (fun _ => eReg_lt_88 _))) (pairSrc_lt_88 (fun _ => eReg_lt_88 _) (fun _ => eReg_lt_88 _))
theorem srcKeyHashOp_ne_rFr : ∀ i, srcKeyHashOp i ≠ rFr :=
  pairSrc_ne_rFr
    (pairSrc_ne_rFr (fun i => cpReg_ne_eReg i (by decide))
      (pairSrc_ne_rFr (fun _ => eReg_ne (by decide)) (fun _ => eReg_ne (by decide))))
    (pairSrc_ne_rFr (fun _ => eReg_ne (by decide)) (fun _ => eReg_ne (by decide)))

theorem tmpQuery_inj : Function.Injective tmpQuery :=
  mkTmp_injective _ outs2_query_inj (fun i => by fin_cases i <;> exact eReg_lt_88 _)
theorem srcKeyHashOp_ne_tmpQuery : ∀ i j, srcKeyHashOp i ≠ tmpQuery j :=
  src_ne_mkTmp _ srcKeyHashOp_lt_88 <|
    pairSrc_ne_outs
      (pairSrc_ne_outs (fun i a => by fin_cases a <;> exact cpReg_ne_eReg i (by decide))
        (pairSrc_ne_outs (fun _ a => by fin_cases a <;> exact eReg_ne (by decide))
          (fun _ a => by fin_cases a <;> exact eReg_ne (by decide))))
      (pairSrc_ne_outs (fun _ a => by fin_cases a <;> exact eReg_ne (by decide))
        (fun _ a => by fin_cases a <;> exact eReg_ne (by decide)))
theorem tmpQuery_ne_rFr : ∀ j, tmpQuery j ≠ rFr :=
  mkTmp_ne_reg _ (eReg_lt_88 _) (fun a => by fin_cases a <;> exact eReg_ne (by decide))

theorem tmpInsSearch_inj : Function.Injective tmpInsSearch :=
  mkTmp_injective _ outs4_ins_inj (fun i => by fin_cases i <;> exact eReg_lt_88 _)
theorem srcKeyHashOp_ne_tmpInsSearch : ∀ i j, srcKeyHashOp i ≠ tmpInsSearch j :=
  src_ne_mkTmp _ srcKeyHashOp_lt_88 <|
    pairSrc_ne_outs
      (pairSrc_ne_outs (fun i a => by fin_cases a <;> exact cpReg_ne_eReg i (by decide))
        (pairSrc_ne_outs (fun _ a => by fin_cases a <;> exact eReg_ne (by decide))
          (fun _ a => by fin_cases a <;> exact eReg_ne (by decide))))
      (pairSrc_ne_outs (fun _ a => by fin_cases a <;> exact eReg_ne (by decide))
        (fun _ a => by fin_cases a <;> exact eReg_ne (by decide)))
theorem tmpInsSearch_ne_rFr : ∀ j, tmpInsSearch j ≠ rFr :=
  mkTmp_ne_reg _ (eReg_lt_88 _) (fun a => by fin_cases a <;> exact eReg_ne (by decide))

theorem tmpWriteVal_inj : Function.Injective tmpWriteVal :=
  mkTmp_injective _ (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
theorem srcWriteVal_ne_tmp : ∀ i j, srcWriteVal i ≠ tmpWriteVal j :=
  src_ne_mkTmp _
    (pairSrc_lt_88
      (pairSrc_lt_88 (pairSrc_lt_88 cpReg_lt_88
        (pairSrc_lt_88 (fun _ => eReg_lt_88 _) (fun _ => eReg_lt_88 _))) (fun _ => eReg_lt_88 _))
      (fun _ => eReg_lt_88 _))
    (fun _ a => Fin.elim0 a)
theorem tmpWriteVal_ne_rFr : ∀ j, tmpWriteVal j ≠ rFr :=
  mkTmp_ne_reg _ (eReg_lt_88 _) (fun a => Fin.elim0 a)
theorem srcWriteVal_ne_rFr : ∀ i, srcWriteVal i ≠ rFr :=
  pairSrc_ne_rFr
    (pairSrc_ne_rFr
      (pairSrc_ne_rFr (fun i => cpReg_ne_eReg i (by decide))
        (pairSrc_ne_rFr (fun _ => eReg_ne (by decide)) (fun _ => eReg_ne (by decide))))
      (fun _ => eReg_ne (by decide)))
    (fun _ => eReg_ne (by decide))

theorem tmpGrowDelta_inj : Function.Injective tmpGrowDelta :=
  mkTmp_injective _ (outs1_inj rK) (fun i => by fin_cases i; exact eReg_lt_88 _)
theorem srcGrowDelta_ne_tmp : ∀ i j, srcGrowDelta i ≠ tmpGrowDelta j :=
  src_ne_mkTmp _ (pairSrc_lt_88 cpReg_lt_88 (fun _ => eReg_lt_88 _)) <|
    pairSrc_ne_outs (fun i a => by fin_cases a; exact cpReg_ne_eReg i (by decide))
      (fun _ a => by fin_cases a; exact eReg_ne (by decide))
theorem tmpGrowDelta_ne_rFr : ∀ j, tmpGrowDelta j ≠ rFr :=
  mkTmp_ne_reg _ (eReg_lt_88 _) (fun a => by fin_cases a; exact eReg_ne (by decide))
theorem srcGrowDelta_ne_rFr : ∀ i, srcGrowDelta i ≠ rFr :=
  pairSrc_ne_rFr (fun i => cpReg_ne_eReg i (by decide)) (fun _ => eReg_ne (by decide))

theorem tmpInsAppend_inj : Function.Injective tmpInsAppend :=
  mkTmp_injective _ (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
theorem srcInsAppend_ne_tmp : ∀ i j, srcInsAppend i ≠ tmpInsAppend j :=
  src_ne_mkTmp _
    (pairSrc_lt_88
      (pairSrc_lt_88 (pairSrc_lt_88 cpReg_lt_88
        (pairSrc_lt_88 (fun _ => eReg_lt_88 _) (fun _ => eReg_lt_88 _)))
        (pairSrc_lt_88 (fun _ => eReg_lt_88 _) (fun _ => eReg_lt_88 _)))
      (pairSrc_lt_88 (fun _ => eReg_lt_88 _) (fun _ => eReg_lt_88 _)))
    (fun _ a => Fin.elim0 a)
theorem tmpInsAppend_ne_rFr : ∀ j, tmpInsAppend j ≠ rFr :=
  mkTmp_ne_reg _ (eReg_lt_88 _) (fun a => Fin.elim0 a)
theorem srcInsAppend_ne_rFr : ∀ i, srcInsAppend i ≠ rFr :=
  pairSrc_ne_rFr
    (pairSrc_ne_rFr
      (pairSrc_ne_rFr (fun i => cpReg_ne_eReg i (by decide))
        (pairSrc_ne_rFr (fun _ => eReg_ne (by decide)) (fun _ => eReg_ne (by decide))))
      (pairSrc_ne_rFr (fun _ => eReg_ne (by decide)) (fun _ => eReg_ne (by decide))))
    (pairSrc_ne_rFr (fun _ => eReg_ne (by decide)) (fun _ => eReg_ne (by decide)))

private theorem srcDelPrep_lt_88 : ∀ i, (srcDelPrep i).val < 88 :=
  pairSrc_lt_88 (pairSrc_lt_88 cpReg_lt_88 (pairSrc_lt_88 (fun _ => eReg_lt_88 _)
    (fun _ => eReg_lt_88 _))) (pairSrc_lt_88 (fun _ => eReg_lt_88 _) (fun _ => eReg_lt_88 _))
theorem srcDelPrep_ne_rFr : ∀ i, srcDelPrep i ≠ rFr :=
  pairSrc_ne_rFr
    (pairSrc_ne_rFr (fun i => cpReg_ne_eReg i (by decide))
      (pairSrc_ne_rFr (fun _ => eReg_ne (by decide)) (fun _ => eReg_ne (by decide))))
    (pairSrc_ne_rFr (fun _ => eReg_ne (by decide)) (fun _ => eReg_ne (by decide)))
theorem tmpDelPrep_inj : Function.Injective tmpDelPrep :=
  mkTmp_injective _ outs4_del_inj (fun i => by fin_cases i <;> exact eReg_lt_88 _)
theorem srcDelPrep_ne_tmp : ∀ i j, srcDelPrep i ≠ tmpDelPrep j :=
  src_ne_mkTmp _ srcDelPrep_lt_88 <|
    pairSrc_ne_outs
      (pairSrc_ne_outs (fun i a => by fin_cases a <;> exact cpReg_ne_eReg i (by decide))
        (pairSrc_ne_outs (fun _ a => by fin_cases a <;> exact eReg_ne (by decide))
          (fun _ a => by fin_cases a <;> exact eReg_ne (by decide))))
      (pairSrc_ne_outs (fun _ a => by fin_cases a <;> exact eReg_ne (by decide))
        (fun _ a => by fin_cases a <;> exact eReg_ne (by decide)))
theorem tmpDelPrep_ne_rFr : ∀ j, tmpDelPrep j ≠ rFr :=
  mkTmp_ne_reg _ (eReg_lt_88 _) (fun a => by fin_cases a <;> exact eReg_ne (by decide))

theorem tmpDelFin_inj : Function.Injective tmpDelFin :=
  mkTmp_injective _ (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
theorem srcDelFin_ne_tmp : ∀ i j, srcDelFin i ≠ tmpDelFin j :=
  src_ne_mkTmp _
    (pairSrc_lt_88
      (pairSrc_lt_88 srcDelPrep_lt_88
        (pairSrc_lt_88 (pairSrc_lt_88 (fun _ => eReg_lt_88 _) (fun _ => eReg_lt_88 _))
          (fun _ => eReg_lt_88 _)))
      (fun _ => eReg_lt_88 _))
    (fun _ a => Fin.elim0 a)
theorem tmpDelFin_ne_rFr : ∀ j, tmpDelFin j ≠ rFr :=
  mkTmp_ne_reg _ (eReg_lt_88 _) (fun a => Fin.elim0 a)
theorem srcDelFin_ne_rFr : ∀ i, srcDelFin i ≠ rFr :=
  pairSrc_ne_rFr
    (pairSrc_ne_rFr srcDelPrep_ne_rFr
      (pairSrc_ne_rFr (pairSrc_ne_rFr (fun _ => eReg_ne (by decide))
        (fun _ => eReg_ne (by decide))) (fun _ => eReg_ne (by decide))))
    (fun _ => eReg_ne (by decide))

theorem tmpShrinkDelta_inj : Function.Injective tmpShrinkDelta :=
  mkTmp_injective _ (outs1_inj rK) (fun i => by fin_cases i; exact eReg_lt_88 _)
theorem srcShrinkDelta_ne_tmp : ∀ i j, srcShrinkDelta i ≠ tmpShrinkDelta j :=
  src_ne_mkTmp _ (pairSrc_lt_88 cpReg_lt_88 (fun _ => eReg_lt_88 _)) <|
    pairSrc_ne_outs (fun i a => by fin_cases a; exact cpReg_ne_eReg i (by decide))
      (fun _ a => by fin_cases a; exact eReg_ne (by decide))
theorem tmpShrinkDelta_ne_rFr : ∀ j, tmpShrinkDelta j ≠ rFr :=
  mkTmp_ne_reg _ (eReg_lt_88 _) (fun a => by fin_cases a; exact eReg_ne (by decide))
theorem srcShrinkDelta_ne_rFr : ∀ i, srcShrinkDelta i ≠ rFr :=
  pairSrc_ne_rFr (fun i => cpReg_ne_eReg i (by decide)) (fun _ => eReg_ne (by decide))

theorem not_readsWidth_loadAtOffCode {r : ℕ} (rAddr rDst rTmp : Fin r) (off : ℕ) :
    ¬(loadAtOffCode rAddr rDst rTmp off).ReadsWidth := by
  simp [loadAtOffCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin]

theorem not_readsWidth_storeAtOffCode {r : ℕ} (rAddr rSrc rTmp : Fin r) (off : ℕ) :
    ¬(storeAtOffCode rAddr rSrc rTmp off).ReadsWidth := by
  simp [storeAtOffCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin]

theorem not_readsWidth_loadBlockUpTo {r m : ℕ} (rAddr rTmp : Fin r) (dst : Fin m → Fin r)
    (startOff : ℕ) :
    ∀ (k : ℕ) (hk : k < m), ¬(loadBlockUpTo rAddr rTmp dst startOff k hk).ReadsWidth
  | 0, _ => not_readsWidth_loadAtOffCode _ _ _ _
  | k + 1, hk => by
    simp only [loadBlockUpTo, RCode.ReadsWidth, not_or]
    exact ⟨not_readsWidth_loadBlockUpTo rAddr rTmp dst startOff k (by omega),
      not_readsWidth_loadAtOffCode _ _ _ _⟩

theorem not_readsWidth_loadActiveCtxCode : ¬loadActiveCtxCode.ReadsWidth := by
  have h1 : ¬(RCode.ofCode (wItemWords.code rFr srcItemWords tmpItemWords)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wItemWords.code_spec rFr srcItemWords tmpItemWords
      tmpItemWords_inj srcItemWords_ne_tmp tmpItemWords_ne_rFr srcItemWords_ne_rFr).1
  have hblk1 := not_readsWidth_loadBlockUpTo rBase rCur hpReg offHashParams 18 (by decide)
  have hblk2 := not_readsWidth_loadBlockUpTo rBase rCur cpReg offCompParams 35 (by decide)
  simp [loadActiveCtxCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin, hblk1, hblk2, h1]

theorem not_readsWidth_evalKeyHashCode : ¬evalKeyHashCode.ReadsWidth := by
  have h2 : ¬(RCode.ofCode (wExtractQuot.code rFr srcExtractQuot tmpExtractQuot)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wExtractQuot.code_spec rFr srcExtractQuot tmpExtractQuot
      tmpExtractQuot_inj srcExtractQuot_ne_tmp tmpExtractQuot_ne_rFr srcExtractQuot_ne_rFr).1
  have h3 : ¬(RCode.ofCode (wEvalHash.code rFr srcEvalHash tmpEvalHash)).ReadsWidth := by
    rw [RCode.readsWidth_ofCode]
    exact (wEvalHash.code_spec rFr srcEvalHash tmpEvalHash
      tmpEvalHash_inj srcEvalHash_ne_tmp tmpEvalHash_ne_rFr srcEvalHash_ne_rFr).1
  simp only [evalKeyHashCode, RCode.ReadsWidth, not_or]
  exact ⟨h2, h3⟩


/-! ## Section 5: ABI Encoding, `InEpochValid`, `1 · OPT` Peak Space, Potential, and Charges -/

/-- Standalone register encoding for `Dynamic.Op U` on `Fin rEpoch`. -/
@[expose]
noncomputable def encode {U : ℕ} : Dynamic.Op U → Fin rEpoch → ℕ
  | .query u, r => if r = rTag then 0 else if r = rArgU then u.val else 0
  | .insert u v, r =>
    if r = rTag then 1 else if r = rArgU then u.val else if r = rArgV then v else 0
  | .delete u, r => if r = rTag then 2 else if r = rArgU then u.val else 0

/-- Partial argument-matching predicate for callers of `inEpochOpCode`. -/
@[expose]
noncomputable def argMatch {U : ℕ} : Dynamic.Op U → (Fin rEpoch → ℕ) → Prop
  | .query u, regs => regs rTag = 0 ∧ regs rArgU = u.val
  | .insert u v, regs => regs rTag = 1 ∧ regs rArgU = u.val ∧ regs rArgV = v
  | .delete u, regs => regs rTag = 2 ∧ regs rArgU = u.val

/-- Output decoder reading `Option ℕ` from `(rOutTag, rOutVal)` for `.query` and `()` for
`.insert` / `.delete`. -/
@[expose]
noncomputable def decode {U : ℕ} : (o : Dynamic.Op U) → (Fin rEpoch → ℕ) → Option o.Result
  | .query _, regs => if regs rOutTag = 0 then some none else some (some (regs rOutVal))
  | .insert _ _, _ => some ()
  | .delete _, _ => some ()

theorem argMatch_encode {U : ℕ} (o : Dynamic.Op U) : argMatch o (encode o) := by
  cases o with
  | query u =>
    exact ⟨by simp [encode], by simp [encode, show rArgU ≠ rTag from eReg_ne (by decide)]⟩
  | insert u v =>
    refine ⟨by simp [encode],
      by simp [encode, show rArgU ≠ rTag from eReg_ne (by decide)],
      by simp [encode, show rArgV ≠ rTag from eReg_ne (by decide),
          show rArgV ≠ rArgU from eReg_ne (by decide)]⟩
  | delete u =>
    exact ⟨by simp [encode], by simp [encode, show rArgU ≠ rTag from eReg_ne (by decide)]⟩

theorem decode_query_optionWords {U : ℕ} (u : Fin U) (res : Option ℕ)
    (regs : Fin rEpoch → ℕ)
    (h0 : regs rOutTag = WordEncoding.encode res 0)
    (h1 : regs rOutVal = WordEncoding.encode res 1) :
    decode (.query u) regs = some res := by
  dsimp only [decode]; rw [h0, h1]; cases res <;> rfl

/-- Extract the target key `u : Fin U` of a dynamic dictionary operation. -/
@[expose]
def opKey {U : ℕ} : Dynamic.Op U → Fin U
  | .query u => u
  | .insert u _ => u
  | .delete u => u

/-- Necessary and sufficient condition for `o : Dynamic.Op U` to execute within the current epoch
of capacity `N` without triggering an epoch capacity migration: `o` is a valid dictionary operation
and the post-step cardinality remains valid for epoch `N`. -/
@[expose]
def InEpochValid {U : ℕ} (V N : ℕ) (s_abs : Dictionary.State U) (o : Dynamic.Op U) : Prop :=
  (Dynamic.spec U V U).valid s_abs o ∧
  EpochValid U (Dictionary.dom ((Dynamic.spec U V U).stepFn s_abs o).1).card N

/-- Exact peak epoch word footprint across an in-epoch operation `o`, equal to
`compactedEpochWords U V w N (max n n')` where `n'` is the post-step live key count. -/
@[expose]
def inEpochPeakWords {U : ℕ} (V w N n : ℕ) (s_abs : Dictionary.State U)
    (o : Dynamic.Op U) : ℕ :=
  compactedEpochWords U V w N
    (max n (Dictionary.dom ((Dynamic.spec U V U).stepFn s_abs o).1).card)

/-- **Stepwise `1 · OPT` peak word-space bound (`inEpochPeakWords_le_succinctWords`):**
under `EpochValid U n N` and `InEpochValid V N s_abs o`, the peak hardware word footprint above
`base` never exceeds `Dynamic.succinctWords 1355 441 U V w (max n n')` (`1 · OPT`). -/
theorem inEpochPeakWords_le_succinctWords {U V w N n : ℕ}
    {s_abs : Dictionary.State U} {o : Dynamic.Op U}
    (hw : 0 < w) (hU : Fits w U) (hU_pos : 0 < U) (hV_pos : 0 < V)
    (hev : EpochValid U n N) (hval : InEpochValid V N s_abs o) :
    inEpochPeakWords V w N n s_abs o ≤
      Dynamic.succinctWords 1355 441 U V w
        (max n (Dictionary.dom ((Dynamic.spec U V U).stepFn s_abs o).1).card) := by
  set n' := (Dictionary.dom ((Dynamic.spec U V U).stepFn s_abs o).1).card
  have hev_max : EpochValid U (max n n') N := by
    rcases le_total n n' with hle | hge
    · rw [max_eq_right hle]; exact hval.2
    · rw [max_eq_left hge]; exact hev
  exact compactedEpochWords_le_succinctWords hw hU hU_pos hV_pos hev_max

/-- Scaled slab/tail hysteresis potential `(98 * inEpochFactor) * slotPotential` for in-epoch
operations on the Resizable Word RAM. -/
@[expose]
noncomputable def inEpochPotential (U w N base : ℕ) {r : ℕ} (x : RData r) : ℕ :=
  (98 * inEpochFactor) * slotPotential N (compGmAt base U w N x.mem)

/-- Parameter-free base instruction charge before adding `(12 * inEpochFactor) * probeExcess`
(`evalMemBound 3 = 45151`, so two hash evaluations plus bucket/slot updates cost at most
`90800 * inEpochFactor + 230` instructions). -/
@[expose]
noncomputable def inEpochBaseCharge : ℕ :=
  90800 * inEpochFactor + 230

/-- Parameter-free $O(1)$ expected amortized instruction charge per in-epoch operation under a
uniform `QuotHashSeed U N` (`5` bounds expected `probeExcess`, `12 * 5 = 60`). -/
@[expose]
noncomputable def inEpochCharge : ℕ :=
  inEpochBaseCharge + 60 * inEpochFactor

/-! ## Section 6: Low-Level Execution and Frame Helpers -/

theorem execBoundedExact_mem_eq_of_ge {B : Basis} {r w L n : ℕ}
    {c : Code B r} {x y : Data r}
    (h : ExecBoundedExact w L c x y n) {a : ℕ} (ha : L ≤ a) :
    y.mem a = x.mem a := by
  induction h with
  | @op o x₀ y₀ hb ho =>
    cases o with
    | const d v =>
      dsimp only [Op.eval, Data.put] at ho; split_ifs at ho; injection ho with hy; subst hy; rfl
    | copy d s => injection ho with hy; subst hy; rfl
    | alu f d args =>
      dsimp only [Op.eval] at ho
      cases h_i : B.interp w f (x₀.regs ∘ args) with
      | none => simp [h_i] at ho
      | some v =>
        simp only [h_i, bind, Option.bind, Data.put] at ho
        split_ifs at ho; injection ho with hy; subst hy; rfl
    | load d addr => injection ho with hy; subst hy; rfl
    | store addr src =>
      change x₀.regs addr < L at hb
      injection ho with hy; subst hy
      exact Function.update_of_ne (by omega : a ≠ x₀.regs addr) _ _
  | seq _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | branch_pos _ _ ih | branch_neg _ _ ih => exact ih
  | loop_exit _ => rfl
  | loop_iter _ _ _ ihb ihl => exact ihl.trans ihb

theorem execWitness {r k l : ℕ} {δ α : Type}
    {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safe : ℕ → δ → Memory.State → Prop}
    (W : RealizesBounded.Witness .exact p input output safe (fun _ _ => 0))
    {factor : ℕ} (hfac : W.factor ≤ factor)
    (rFr : Fin r) (src : Fin k → Fin r) (tmp : Fin (l + W.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ rFr) (hs : ∀ i, src i ≠ rFr)
    {w L_peak : ℕ} (d : δ) {x : RData r}
    (hx : x.Bounded w) (hL_peak : x.frontier ≤ L_peak)
    (hin : x.regs ∘ src = input d)
    (hsafe : safe w d (memoryState rFr x.toData))
    (hv : (Memory.spec w).ValidHistory (memoryState rFr x.toData)
      ((Memory.spec w).clientHistory (memoryState rFr x.toData) (p d)))
    (hnoalloc : ((Memory.spec 0).clientState
      (memoryState rFr x.toData) (p d)).frontier ≤ x.frontier) :
    ∃ y : RData r,
      RDemonicExec w L_peak (RCode.ofCode (W.code rFr src tmp)) x
        (factor * (memoryCost (p d) (memoryState rFr x.toData) + 1)) (· = y) ∧
      y.Bounded w ∧
      y.frontier = x.frontier ∧
      memoryState rFr y.toData = (Memory.spec 0).clientState (memoryState rFr x.toData) (p d) ∧
      (∀ i : Fin l, y.regs (tmp (Fin.castAdd (W.scratchSize + 1) i)) =
        output ((Memory.spec 0).clientResult (memoryState rFr x.toData) (p d)) i) ∧
      ∀ reg, reg ≠ rFr → (∀ j, tmp j ≠ reg) → y.regs reg = x.regs reg := by
  obtain ⟨_, hrun⟩ := W.code_spec rFr src tmp hi hd hf hs
  obtain ⟨yd, hy_eb, hm, hout, hframe⟩ := hrun w d x.toData hx.1 hin hsafe hv
  rw [clientState_width] at hm
  rw [clientResult_width] at hout
  have hy_fr : yd.regs rFr ≤ x.frontier := by
    have hm_fr := congrArg Memory.State.frontier hm
    change yd.regs rFr = _ at hm_fr
    omega
  obtain ⟨n_st, hn_st, hy_ex⟩ := hy_eb
  have hy_bdd : (⟨yd.regs, yd.mem, x.frontier⟩ : RData r).Bounded w :=
    ⟨hy_ex.bounded hx.1, hx.2.1, fun a ha =>
      (execBoundedExact_mem_eq_of_ge hy_ex (hy_fr.trans ha)).trans (hx.zero_above ha)⟩
  have hT : W.factor * (memoryCost (p d) (memoryState rFr x.toData) + 0 + 1) ≤
      factor * (memoryCost (p d) (memoryState rFr x.toData) + 1) :=
    Nat.mul_le_mul_right _ hfac
  refine ⟨⟨yd.regs, yd.mem, x.frontier⟩,
    (RDemonicExec.of_execBounded hL_peak hy_fr ⟨n_st, hn_st, hy_ex⟩).mono hT (fun _ h => h),
    hy_bdd, rfl, hm, hout, hframe⟩

theorem loadAtOffCode_exec {r w L_peak base off : ℕ} {rAddr rDst rTmp : Fin r} {x : RData r}
    (hx : x.Bounded w) (hL : x.frontier ≤ L_peak)
    (haddr_ne_tmp : rAddr ≠ rTmp)
    (hbase : x.regs rAddr = base) (hoff_fit : Fits w off)
    (hlt : base + off < x.frontier) :
    let y := (x.set rTmp (base + off)).set rDst (x.mem (base + off))
    RDemonicExec w L_peak (loadAtOffCode rAddr rDst rTmp off) x 3 (· = y) ∧
    y.Bounded w := by
  have hadd_fit : Fits w (base + off) := hx.frontier_fits.of_le hlt.le
  have s1 := RDemonicExec.const (B := .exact) (d := rTmp) (x := x) hL hoff_fit
  have s2 := RDemonicExec.exactBin (f := .add) (d := rTmp) (i := rAddr) (j := rTmp)
    (w := w) (L_peak := L_peak) (x := x.set rTmp off) hL (v := base + off)
    (by simp [BinOp.evalExact, Function.update_of_ne haddr_ne_tmp, hbase]) hadd_fit
  have hx2 : (x.set rTmp off).set rTmp (base + off) = x.set rTmp (base + off) := by
    ext j <;> simp [RData.set]
  rw [hx2] at s2
  have s3 := RDemonicExec.load (B := .exact) (d := rDst) (a := rTmp) (w := w)
    (L_peak := L_peak) (x := x.set rTmp (base + off)) hL (by simp [hlt])
  have hmem_eq : (x.set rTmp (base + off)).mem ((x.set rTmp (base + off)).regs rTmp) =
      x.mem (base + off) := by simp
  rw [hmem_eq] at s3
  exact ⟨(s1.seq_eq (s2.seq_eq s3)).mono le_rfl (fun _ h => h),
    (hx.set hadd_fit).set (hx.mem_fits (base + off))⟩

theorem storeAtOffCode_exec {r w L_peak base off val : ℕ} {rAddr rSrc rTmp : Fin r}
    {x : RData r}
    (hx : x.Bounded w) (hL : x.frontier ≤ L_peak)
    (haddr_ne_tmp : rAddr ≠ rTmp) (hs_ne_tmp : rSrc ≠ rTmp)
    (hbase : x.regs rAddr = base) (hsrc : x.regs rSrc = val)
    (hoff_fit : Fits w off) (hlt : base + off < x.frontier) :
    let y := (x.set rTmp (base + off)).write (base + off) val
    RDemonicExec w L_peak (storeAtOffCode rAddr rSrc rTmp off) x 3 (· = y) ∧
    y.Bounded w := by
  have hadd_fit : Fits w (base + off) := hx.frontier_fits.of_le hlt.le
  have hval_fit : Fits w val := hsrc ▸ hx.regs_fits rSrc
  have s1 := RDemonicExec.const (B := .exact) (d := rTmp) (x := x) hL hoff_fit
  have s2 := RDemonicExec.exactBin (f := .add) (d := rTmp) (i := rAddr) (j := rTmp)
    (w := w) (L_peak := L_peak) (x := x.set rTmp off) hL (v := base + off)
    (by simp [BinOp.evalExact, Function.update_of_ne haddr_ne_tmp, hbase]) hadd_fit
  have hx2 : (x.set rTmp off).set rTmp (base + off) = x.set rTmp (base + off) := by
    ext j <;> simp [RData.set]
  rw [hx2] at s2
  have s3 := RDemonicExec.store (B := .exact) (a := rTmp) (s := rSrc) (w := w)
    (L_peak := L_peak) (x := x.set rTmp (base + off)) hL (by simp [hlt])
  have haddr : (x.set rTmp (base + off)).regs rTmp = base + off := by simp
  have hv_eq : (x.set rTmp (base + off)).regs rSrc = val := by
    simp [Function.update_of_ne hs_ne_tmp, hsrc]
  rw [haddr, hv_eq] at s3
  exact ⟨(s1.seq_eq (s2.seq_eq s3)).mono le_rfl (fun _ h => h),
    (hx.set hadd_fit).write hlt hval_fit⟩

theorem loadBlockUpTo_exec {r m w L_peak base : ℕ}
    (rAddr rTmp : Fin r) (haddr_ne_tmp : rAddr ≠ rTmp)
    (dst : Fin m → Fin r) (hinj : Function.Injective dst)
    (hne_base : ∀ i, dst i ≠ rAddr) (hne_cur : ∀ i, dst i ≠ rTmp)
    (startOff k : ℕ) (hk : k < m) {x : RData r}
    (hx : x.Bounded w) (hL : x.frontier ≤ L_peak)
    (hbase : x.regs rAddr = base)
    (hbound : base + startOff + (k + 1) ≤ x.frontier) :
    ∃ y : RData r,
      RDemonicExec w L_peak (loadBlockUpTo rAddr rTmp dst startOff k hk) x (3 * (k + 1)) (· = y) ∧
      y.Bounded w ∧ y.mem = x.mem ∧ y.frontier = x.frontier ∧
      (∀ i : Fin m, i.val ≤ k → y.regs (dst i) = x.mem (base + startOff + i.val)) ∧
      ∀ reg, reg ≠ rTmp → (∀ i : Fin m, dst i ≠ reg) → y.regs reg = x.regs reg := by
  induction k with
  | zero =>
    have hlt : base + startOff < x.frontier := by omega
    have hoff_fit : Fits w startOff := hx.frontier_fits.of_le (by omega)
    obtain ⟨hex, hyb⟩ := loadAtOffCode_exec (rDst := dst ⟨0, hk⟩) hx hL haddr_ne_tmp
      hbase hoff_fit hlt
    refine ⟨_, hex, hyb, rfl, rfl, fun i hi => ?_, fun reg hrc hrd => ?_⟩
    · have hi0 : i = ⟨0, hk⟩ := Fin.ext (Nat.eq_zero_of_le_zero hi)
      subst hi0; simp [RData.set]
    · simp [RData.set, Function.update_of_ne (hrd ⟨0, hk⟩).symm, Function.update_of_ne hrc]
  | succ k ih =>
    obtain ⟨y₁, hex₁, hy₁b, hy₁m, hy₁f, hy₁d, hy₁r⟩ := ih (by omega) (by omega)
    have hy₁_base : y₁.regs rAddr = base :=
      (hy₁r rAddr haddr_ne_tmp (fun i => hne_base i)).trans hbase
    have hlt : base + (startOff + (k + 1)) < y₁.frontier := by omega
    have hoff_fit : Fits w (startOff + (k + 1)) := hy₁b.frontier_fits.of_le (by omega)
    obtain ⟨hex₂, hy₂b⟩ := loadAtOffCode_exec (rDst := dst ⟨k + 1, hk⟩) hy₁b (hy₁f.le.trans hL)
      haddr_ne_tmp hy₁_base hoff_fit hlt
    refine ⟨_, (hex₁.seq_eq hex₂).mono (by omega) (fun _ h => h),
      hy₂b, hy₁m, hy₁f, fun i hi => ?_, fun reg hrc hrd => ?_⟩
    · by_cases hik : i.val = k + 1
      · have hieq : i = ⟨k + 1, hk⟩ := Fin.ext hik
        subst hieq
        simp only [RData.set_regs, Function.update_self, hy₁m]
        congr 1; omega
      · have hne_d : dst i ≠ dst ⟨k + 1, hk⟩ := fun h => hik (congrArg Fin.val (hinj h))
        simp only [RData.set_regs, Function.update_of_ne hne_d,
          Function.update_of_ne (hne_cur i)]
        exact hy₁d i (by omega)
    · simp only [RData.set_regs, Function.update_of_ne (hrd ⟨k + 1, hk⟩).symm,
        Function.update_of_ne hrc]
      exact hy₁r reg hrc hrd

/-! ## Section 7: `CompactedSplitRep` Frame Lemmas (Scratch, `CompOpFrame`, Shrink, Header `n`) -/

theorem rootHeaderValid_bounds {U V w N n n_init base : ℕ} {r : ℕ} {x : RData r}
    (hx : x.Bounded w) (hhdr : RootHeaderValid U V w N n n_init base x.mem) :
    0 < w ∧ U < 2 ^ w ∧ V ≤ 2 ^ w := by
  have hU : U < 2 ^ w := hhdr.fits_U
  have hV : x.mem (base + 1) < 2 ^ w := hx.mem_fits (base + 1)
  rw [hhdr.hdr_V] at hV
  have := hhdr.pos_U; have := hhdr.pos_V
  refine ⟨Nat.pos_of_ne_zero fun hw => ?_, hU, by omega⟩
  subst hw; omega

private theorem rootHeaderValid_of_agree {U V w N n n_init base : ℕ} {mem mem' : ℕ → ℕ}
    (hhdr : RootHeaderValid U V w N n n_init base mem) (hout : ∀ a < base + 8, mem' a = mem a) :
    RootHeaderValid U V w N n n_init base mem' := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ := hhdr
  refine ⟨h₁, h₂, h₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact (hout _ (by omega)).trans ‹_›

/-- The stored parameters and the hash representation survive writes outside
`[base + 8, base + 63) ∪ [base + 225, base + offCompLM)`. -/
private theorem params_hash_of_agree {U V w N base : ℕ} {θ : QuotHashSeed U N}
    {mem mem' : ℕ → ℕ} (hpar : EpochParamsStored U V w N base mem)
    (hhash : ReducedKWise.Rep (base + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ mem)
    (hout : ∀ a, base + 8 ≤ a → a < base + offCompLM U w N →
      (a < base + offScratch ∨ base + epochHdrWords ≤ a) → mem' a = mem a) :
    EpochParamsStored U V w N base mem' ∧
      ReducedKWise.Rep (base + epochHdrWords) w (qBits U N) (hashB N)
        (totalMicroBits N) 3 θ mem' := by
  have heh : epochHdrWords = 225 := rfl
  refine ⟨⟨fun i => (hout _ ?_ ?_ ?_).trans (hpar.hp_eq i),
      fun i => (hout _ ?_ ?_ ?_).trans (hpar.cp_eq i)⟩,
    ReducedKWise.tableRep_congr hhash.1 fun a h₁ h₂ => (hout a ?_ ?_ ?_).symm,
    ReducedKWise.seedRep_congr (w := w) hhash.2 fun a h₁ h₂ => (hout a ?_ ?_ ?_).symm⟩
  all_goals dsimp only [offHashParams, offCompParams, offScratch, offCompLM, epochHashSpace, qBits,
    hashB, epochQBits, epochHashB] at *
  all_goals omega

/-- The fixed coupling and the global metadata survive writes below `base + offCompLM`. -/
private theorem fixedCoupled_of_agree {U V w N base : ℕ} {s_fix s s' : Memory.State} (hw : 0 < w)
    (hcpl : FixedCoupled base (base + offCompItems U w N) U V w N s_fix s)
    (hout : ∀ a, base + offCompLM U w N ≤ a → s'.mem a = s.mem a) :
    FixedCoupled base (base + offCompItems U w N) U V w N s_fix s' ∧
      compGmAt base U w N s'.mem = compGmAt base U w N s.mem := by
  have h₁ : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h₂ : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h₃ : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h₄ : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  have hlm := compLmAt_congr (metaBase := base) (U := U) (N := N) hw fun a ha => hout a ha.1
  have hgm := compGmAt_congr (metaBase := base) (U := U) (N := N) hw fun a ha => hout a (by omega)
  have htd := compTDAt_congr (metaBase := base) (U := U) (N := N) hw fun a ha => hout a (by omega)
  have hdt := compDTAt_congr (metaBase := base) (U := U) (N := N) hw fun a ha => hout a (by omega)
  have hq : ∀ m, compQuotAt (base + offCompItems U w N) U V w N m s'.mem =
      compQuotAt (base + offCompItems U w N) U V w N m s.mem := fun _ =>
    compQuotAt_congr hw fun a ha => hout a (by omega)
  have hv : ∀ m, compValAt (base + offCompItems U w N) U V w N m s'.mem =
      compValAt (base + offCompItems U w N) U V w N m s.mem := fun _ =>
    compValAt_congr hw fun a ha => hout a (by omega)
  refine ⟨⟨hgm.trans hcpl.gm_eq, hlm.trans hcpl.lm_eq, by rw [hgm, htd, hdt]; exact hcpl.win_inv,
    fun i => by rw [htd]; exact hcpl.td_lt i, fun i => by rw [hdt]; exact hcpl.dt_lt i,
    fun d hd => ?_, fun d hd => ?_⟩, hgm⟩
  · rw [hgm, hq, hdt]; exact hcpl.quot_eq d (by simpa only [epochTotalSlots, hgm] using hd)
  · rw [hgm, hv, hdt]; exact hcpl.val_eq d (by simpa only [epochTotalSlots, hgm] using hd)

theorem compactedSplitRep_of_scratch_mod {U V w N n n_init base : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s₀ s₁ : Memory.State}
    (hw : 0 < w)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs s₀)
    (_hfr : s₁.frontier = s₀.frontier)
    (hout : ∀ a, (a < base + offScratch ∨ base + epochHdrWords ≤ a) → s₁.mem a = s₀.mem a) :
    CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs s₁ := by
  have h₀ : epochHdrWords ≤ offCompLM U w N := Nat.le_add_right _ _
  obtain ⟨s_fix, hinv, htot, hcpl⟩ := hsplit.coupled
  obtain ⟨hpar, hhash⟩ := params_hash_of_agree hsplit.params_stored hsplit.hash_rep
    fun a _ _ h => hout a h
  obtain ⟨hcpl₁, hgm⟩ := fixedCoupled_of_agree hw hcpl fun a ha => hout a (Or.inr (by omega))
  exact ⟨rootHeaderValid_of_agree hsplit.root_hdr fun a ha => hout a (Or.inl (by
      unfold offScratch; omega)), hpar, hhash, hsplit.card_eq, hsplit.vals_lt, s_fix, hinv,
    hgm ▸ htot, hcpl₁⟩

theorem hdr_params_hash_of_opFrame {U V w N n n_init m_cap base : ℕ}
    {θ : QuotHashSeed U N} {s s' : Memory.State}
    (hhdr : RootHeaderValid U V w N n n_init base s.mem)
    (hpar : EpochParamsStored U V w N base s.mem)
    (hhash : ReducedKWise.Rep (base + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ s.mem)
    (hfr : CompOpFrame base (base + offCompItems U w N) U V w N m_cap s s') :
    RootHeaderValid U V w N n n_init base s'.mem ∧
    EpochParamsStored U V w N base s'.mem ∧
    ReducedKWise.Rep (base + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ s'.mem ∧
    (∀ addr < base, s'.mem addr = s.mem addr) := by
  have h_lm_ge : epochHdrWords ≤ offCompLM U w N := Nat.le_add_right _ _
  have h_lm_le : offCompLM U w N ≤ offCompItems U w N := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
  have heh : epochHdrWords = 225 := rfl
  have hbelow : ∀ a < base + offCompLM U w N, s'.mem a = s.mem a := fun a ha =>
    hfr.outside_eq a (by omega) (by omega)
  obtain ⟨hpar', hhash'⟩ := params_hash_of_agree hpar hhash fun a _ h _ => hbelow a h
  exact ⟨rootHeaderValid_of_agree hhdr fun a ha => hbelow a (by omega), hpar', hhash',
    fun a ha => hbelow a (by omega)⟩

theorem update_hdr_n_preserves_split {U V w N n_old n_new n_init base : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_fix : Memory.State}
    {mem : ℕ → ℕ} {fr : ℕ}
    (hw : 0 < w)
    (hhdr : RootHeaderValid U V w N n_old n_init base mem)
    (hpar : EpochParamsStored U V w N base mem)
    (hhash : ReducedKWise.Rep (base + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ mem)
    (hcard : (Dictionary.dom s_abs).card = n_new)
    (hvals : Dictionary.ValuesBounded V s_abs)
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled base (base + offCompItems U w N) U V w N s_fix ⟨mem, fr⟩) :
    let mem' := Function.update mem (base + 6) n_new
    CompactedSplitRep base (base + offCompItems U w N) U V w N n_new n_init θ s_abs ⟨mem', fr⟩ ∧
    compGmAt base U w N mem' = compGmAt base U w N mem := by
  intro mem'
  have h₀ : epochHdrWords ≤ offCompLM U w N := Nat.le_add_right _ _
  have hout : ∀ a, a ≠ base + 6 → mem' a = mem a := fun a hne =>
    Function.update_of_ne hne n_new mem
  obtain ⟨hpar', hhash'⟩ := params_hash_of_agree hpar hhash fun a h _ _ => hout a (by omega)
  obtain ⟨hcpl', hgm⟩ := fixedCoupled_of_agree (s' := ⟨mem', fr⟩) hw hcpl fun a ha =>
    hout a (by unfold epochHdrWords at h₀; omega)
  refine ⟨⟨?_, hpar', hhash', hcard, hvals, s_fix, hinv, ?_, hcpl'⟩, hgm⟩
  · obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, -, h₁₁⟩ := hhdr
    refine ⟨h₁, h₂, h₃, ?_, ?_, ?_, ?_, ?_, ?_, Function.update_self .., ?_⟩ <;>
      exact (hout _ (by omega)).trans ‹_›
  · rw [hgm, show compGmAt base U w N mem = _ from hcpl.gm_eq]; exact hinv.htot.trans hcard

/-! ## Section 8: Execution of `loadActiveCtxCode` and `evalKeyHashCode` -/

private theorem hpReg_inj : Function.Injective hpReg := fun a b h => by
  have hv := congrArg Fin.val h; rw [val_hpReg, val_hpReg] at hv; exact Fin.ext (by omega)

private theorem cpReg_inj : Function.Injective cpReg := fun a b h => by
  have hv := congrArg Fin.val h; rw [val_cpReg, val_cpReg] at hv; exact Fin.ext (by omega)

theorem loadActiveCtxCode_exec {U V w N n n_init base L_peak : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {x : RData rEpoch}
    (hx : x.Bounded w) (hn : 0 < n) (hev : EpochValid U n N)
    (hfr : x.frontier = base + compactedEpochWords U V w N n)
    (hL : x.frontier ≤ L_peak)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩)
    (hbase : x.regs rBase = base) (hcnt : x.regs rCnt = n) :
    ∃ y : RData rEpoch,
      RDemonicExec w L_peak loadActiveCtxCode x (inEpochFactor + 172) (· = y) ∧
      y.Bounded w ∧ y.mem = x.mem ∧ y.frontier = x.frontier ∧
      y.regs rBase = base ∧ y.regs rCnt = n ∧
      y.regs rScratchBase = base + offScratch ∧
      y.regs rHashBase = base + epochHdrWords ∧
      y.regs rItemBase = base + offCompItems U w N ∧
      y.regs rFr = x.frontier ∧
      y.regs rTag = x.regs rTag ∧
      y.regs rArgU = x.regs rArgU ∧
      y.regs rArgV = x.regs rArgV ∧
      (∀ i : Fin 19, y.regs (hpReg i) =
        mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i) ∧
      (∀ i : Fin 36, y.regs (cpReg i) = mkCompParams U V w N i) := by
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hx hsplit.root_hdr
  have hNU : N ≤ U := by rcases hev with ⟨rfl, _⟩ | ⟨_, _, _, hNU⟩ <;> omega
  have hfr_pos : x.frontier = base + offCompItems U w N + compactedItemWords U V w N n := by
    rw [hfr]; unfold compactedEpochWords; rw [ite_eq_right hn.ne']; omega
  have hoff_ge : 225 ≤ offCompItems U w N := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
  have hfit_fr : Fits w x.frontier := hx.frontier_fits
  obtain ⟨x₁, hex₁, hx₁b, hx₁m, hx₁f, hx₁_hp, hx₁_reg⟩ :=
    loadBlockUpTo_exec rBase rCur (eReg_ne (by decide)) hpReg hpReg_inj
      (fun i => hpReg_ne_eReg i (by decide)) (fun i => hpReg_ne_eReg i (by decide))
      offHashParams 18 (by decide) hx hL hbase (by unfold offHashParams; omega)
  have hx₁_base : x₁.regs rBase = base :=
    (hx₁_reg rBase (eReg_ne (by decide)) (fun i => hpReg_ne_eReg i (by decide))).trans hbase
  obtain ⟨x₂, hex₂, hx₂b, hx₂m, hx₂f, hx₂_cp, hx₂_reg⟩ :=
    loadBlockUpTo_exec rBase rCur (eReg_ne (by decide)) cpReg cpReg_inj
      (fun i => cpReg_ne_eReg i (by decide)) (fun i => cpReg_ne_eReg i (by decide))
      offCompParams 35 (by decide) hx₁b (hx₁f.le.trans hL) hx₁_base
      (by unfold offCompParams; omega)
  have hx₂_hp : ∀ i : Fin 19, x₂.regs (hpReg i) =
      mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i := fun i => by
    have hne : ∀ j : Fin 36, cpReg j ≠ hpReg i := fun j h => by
      have hv := congrArg Fin.val h; rw [val_cpReg, val_hpReg] at hv; omega
    rw [hx₂_reg (hpReg i) (hpReg_ne_eReg i (by decide)) hne, hx₁_hp i (by omega)]
    exact hsplit.params_stored.hp_eq i
  have hx₂_cp' : ∀ i : Fin 36, x₂.regs (cpReg i) = mkCompParams U V w N i := fun i => by
    rw [hx₂_cp i (by omega), hx₁m]
    exact hsplit.params_stored.cp_eq i
  have hpres₂ : ∀ {c : Fin 88}, c.val < 32 → c ≠ 9 → x₂.regs (eReg c) = x.regs (eReg c) :=
    fun {c} hc hne9 => by
      have hrc : eReg c ≠ rCur := eReg_ne hne9
      rw [hx₂_reg (eReg c) hrc (fun j => cpReg_ne_eReg j (by omega)),
        hx₁_reg (eReg c) hrc (fun j => hpReg_ne_eReg j hc)]
  set x₃ := x₂.set rFr 0
  have hx₂_hL : x₂.frontier ≤ L_peak := by rw [hx₂f, hx₁f]; exact hL
  have hex₃ := RDemonicExec.const (B := .exact) (d := rFr) (x := x₂) hx₂_hL (fits_zero w)
  have hx₃b : x₃.Bounded w := hx₂b.set (fits_zero w)
  have hin_iw : x₃.regs ∘ srcItemWords = WordEncoding.encode (mkCompParams U V w N, n) := by
    refine (regs_pairSrc (regs_cp_eq fun i => ?_) (regs_reg1_eq rCnt ?_)).eq
    · simp only [x₃, RData.set_regs, Function.update_of_ne (cpReg_ne_eReg (c := 1) i (by decide))]
      exact hx₂_cp' i
    · simp only [x₃, RData.set_regs, Function.update_of_ne (eReg_ne (by decide) : rCnt ≠ rFr)]
      exact (hpres₂ (c := 13) (by decide) (by decide)).trans hcnt
  have hfit_iw4 : Fits w (4 + compactedItemWords U V w N n) := hfit_fr.of_le (by omega)
  have hsafe_iw : CompItemWordsPre w (mkCompParams U V w N, n) (memoryState rFr x₃.toData) :=
    ⟨U, V, N, hw, hNU, hU, hV, rfl, fits_wOffQ_add_three_of_itemWords hw hfit_iw4⟩
  have hv_iw : (Memory.spec w).ValidHistory (memoryState rFr x₃.toData)
      ((Memory.spec w).clientHistory (memoryState rFr x₃.toData)
        (compItemWordsGenProg (mkCompParams U V w N, n))) :=
    validProg_compItemWordsGen _ _ ⟨wellFormed_memoryState hx₃b.1, Nat.zero_le _⟩
  have hnoalloc_iw : ((Memory.spec 0).clientState (memoryState rFr x₃.toData)
      (compItemWordsGenProg (mkCompParams U V w N, n))).frontier ≤ x₃.frontier := by
    rw [clientState_compItemWordsGenProg]; change 0 ≤ x₃.frontier; omega
  obtain ⟨x₄, hex₄, hx₄b, hx₄f, hm_iw, hout_iw, hframe_iw⟩ :=
    execWitness wItemWords factor_wItemWords_le rFr srcItemWords tmpItemWords
      tmpItemWords_inj srcItemWords_ne_tmp tmpItemWords_ne_rFr srcItemWords_ne_rFr
      (mkCompParams U V w N, n) hx₃b hx₂_hL hin_iw hsafe_iw hv_iw hnoalloc_iw
  rw [memoryCost_compItemWordsGenProg, zero_add, mul_one] at hex₄
  rw [clientState_compItemWordsGenProg] at hm_iw
  have hx₄m : x₄.mem = x.mem :=
    (congrArg Memory.State.mem hm_iw).trans (hx₂m.trans hx₁m)
  have hx₄_cur : x₄.regs rCur = compactedItemWords U V w N n := by
    have h0 := hout_iw 0
    rw [tmpItemWords_out, clientResult_compItemWordsGenProg hw] at h0
    exact h0
  have hpres₄_eReg : ∀ {c : Fin 88}, c.val < 32 → c ≠ 1 → c ≠ 9 →
      x₄.regs (eReg c) = x.regs (eReg c) := fun {c} hc hne1 hne9 => by
    rw [hframe_iw (eReg c) (eReg_ne hne1)
      (mkTmp_ne_reg _ (eReg_lt_88 _) (fun a => by fin_cases a; exact eReg_ne hne9.symm))]
    simp only [x₃, RData.set_regs, Function.update_of_ne (eReg_ne hne1)]
    exact hpres₂ hc hne9
  have hx₄_hp : ∀ i : Fin 19, x₄.regs (hpReg i) =
      mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i := fun i => by
    rw [hframe_iw (hpReg i) (hpReg_ne_eReg i (by decide))
      (mkTmp_ne_reg _ (hpReg_lt_88 i) (fun a => by fin_cases a; exact (hpReg_ne_eReg i
        (by decide)).symm))]
    simp only [x₃, RData.set_regs, Function.update_of_ne (hpReg_ne_eReg (c := 1) i (by decide))]
    exact hx₂_hp i
  have hx₄_cp : ∀ i : Fin 36, x₄.regs (cpReg i) = mkCompParams U V w N i := fun i => by
    rw [hframe_iw (cpReg i) (cpReg_ne_eReg i (by decide))
      (mkTmp_ne_reg _ (cpReg_lt_88 i) (fun a => by fin_cases a; exact (cpReg_ne_eReg i
        (by decide)).symm))]
    simp only [x₃, RData.set_regs, Function.update_of_ne (cpReg_ne_eReg (c := 1) i (by decide))]
    exact hx₂_cp' i
  have hx₄_base : x₄.regs rBase = base :=
    (hpres₄_eReg (c := 0) (by decide) (by decide) (by decide)).trans hbase
  have hx₄_ff : x₄.frontier = x.frontier := hx₄f.trans (hx₂f.trans hx₁f)
  have hfit_sc : Fits w offScratch := hfit_fr.of_le (by unfold offScratch; omega)
  have hfit_bs : Fits w (base + offScratch) := hfit_fr.of_le (by unfold offScratch; omega)
  have hfit_eh : Fits w epochHdrWords := hfit_fr.of_le (by unfold epochHdrWords; omega)
  have hfit_bh : Fits w (base + epochHdrWords) := hfit_fr.of_le (by unfold epochHdrWords; omega)
  have hfit_bi : Fits w (base + offCompItems U w N) := hfit_fr.of_le (by omega)
  set x₅ := x₄.set rIdx offScratch
  set x₆ := x₅.set rScratchBase (base + offScratch)
  set x₇ := x₆.set rIdx epochHdrWords
  set x₈ := x₇.set rHashBase (base + epochHdrWords)
  set x₉ := x₈.set rItemBase (base + offCompItems U w N)
  set y := x₉.set rFr x.frontier
  have hx₄_hL : x₄.frontier ≤ L_peak := by rw [hx₄_ff]; exact hL
  have s5 := RDemonicExec.const (B := .exact) (d := rIdx) (x := x₄) hx₄_hL hfit_sc
  have s6 := RDemonicExec.exactBin (f := .add) (d := rScratchBase) (i := rBase) (j := rIdx)
    (w := w) (L_peak := L_peak) (x := x₅) hx₄_hL (v := base + offScratch)
    (by simp [BinOp.evalExact, x₅, hx₄_base]) hfit_bs
  have s7 := RDemonicExec.const (B := .exact) (d := rIdx) (x := x₆) hx₄_hL hfit_eh
  have s8 := RDemonicExec.exactBin (f := .add) (d := rHashBase) (i := rBase) (j := rIdx)
    (w := w) (L_peak := L_peak) (x := x₇) hx₄_hL (v := base + epochHdrWords)
    (by simp [BinOp.evalExact, x₇, x₆, x₅, hx₄_base]) hfit_bh
  have hx₈_cp34 : x₈.regs (cpReg ⟨34, by decide⟩) = offCompItems U w N := by
    rw [← show x₄.regs (cpReg ⟨34, by decide⟩) = offCompItems U w N from hx₄_cp _]
    simp [x₈, x₇, x₆, x₅, Function.update_of_ne (cpReg_ne_eReg _ _)]
  have s9 := RDemonicExec.exactBin (f := .add) (d := rItemBase) (i := rBase)
    (j := cpReg ⟨34, by decide⟩) (w := w) (L_peak := L_peak) (x := x₈) hx₄_hL
    (v := base + offCompItems U w N)
    (by
      change some (x₈.regs rBase + x₈.regs (cpReg ⟨34, by decide⟩)) =
        some (base + offCompItems U w N)
      rw [hx₈_cp34]
      simp [x₈, x₇, x₆, x₅, hx₄_base]) hfit_bi
  have s10 := RDemonicExec.exactBin (f := .add) (d := rFr) (i := rItemBase) (j := rCur)
    (w := w) (L_peak := L_peak) (x := x₉) hx₄_hL (v := x.frontier)
    (by simp [BinOp.evalExact, x₉, x₈, x₇, x₆, x₅, hx₄_cur, hfr_pos]) hfit_fr
  have hex_all :=
    hex₁.seq_eq (hex₂.seq_eq (hex₃.seq_eq (hex₄.seq_eq
      (s5.seq_eq (s6.seq_eq (s7.seq_eq (s8.seq_eq (s9.seq_eq s10))))))))
  have hyb : y.Bounded w :=
    (((((hx₄b.set hfit_sc).set hfit_bs).set hfit_eh).set hfit_bh).set hfit_bi).set hfit_fr
  refine ⟨y, hex_all.mono (by omega) (fun _ h => h), hyb, hx₄m, hx₄_ff, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, fun i => ?_, fun i => ?_⟩ <;>
    simp [y, x₉, x₈, x₇, x₆, x₅, hx₄_base, hpres₄_eReg, hcnt, hx₄_hp, hx₄_cp,
      Function.update_of_ne (hpReg_ne_eReg _ _), Function.update_of_ne (cpReg_ne_eReg _ _)]

theorem runEvalHashAtQuot {U V w N n n_init base L_peak q : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {x : RData rEpoch}
    (hx : x.Bounded w) (hn : 0 < n) (hev : EpochValid U n N)
    (hfr : x.frontier = base + compactedEpochWords U V w N n)
    (hL : x.frontier ≤ L_peak)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩)
    (hrFr : x.regs rFr = x.frontier)
    (hrHash : x.regs rHashBase = base + epochHdrWords)
    (hrScr : x.regs rScratchBase = base + offScratch)
    (hrQuot : x.regs rQuot = q)
    (hhp : ∀ i : Fin 19, x.regs (hpReg i) =
      mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i)
    (hq_lt : q < 2 ^ quotientBits U N) :
    ∃ y : RData rEpoch,
      RDemonicExec w L_peak (RCode.ofCode (wEvalHash.code rFr srcEvalHash tmpEvalHash)) x
        (45206 * inEpochFactor) (· = y) ∧
      y.Bounded w ∧ y.frontier = x.frontier ∧
      y.regs rFr = y.frontier ∧
      y.regs rHashOut = hValOfSeed U N θ q ∧
      CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
        ⟨y.mem, y.frontier⟩ ∧
      (∀ a, (a < base + offScratch ∨ base + epochHdrWords ≤ a) → y.mem a = x.mem a) ∧
      ∀ reg, reg ≠ rFr → reg.val < 88 → reg ≠ rHashOut → y.regs reg = x.regs reg := by
  obtain ⟨hw, hU, _⟩ := rootHeaderValid_bounds hx hsplit.root_hdr
  have hNU : N ≤ U := by rcases hev with ⟨rfl, _⟩ | ⟨_, _, _, hNU⟩ <;> omega
  have hfr_pos : x.frontier = base + offCompItems U w N + compactedItemWords U V w N n := by
    rw [hfr]; unfold compactedEpochWords; rw [ite_eq_right hn.ne']; omega
  have hoff_ge : 225 ≤ offCompItems U w N := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords; omega
  have hfit_fr : Fits w x.frontier := hx.frontier_fits
  have hw2 : 2 ≤ w := by
    by_contra h
    have := Nat.pow_le_pow_right two_pos (show w ≤ 1 by omega)
    have : 225 < 2 ^ w := lt_of_le_of_lt (by omega) hfit_fr
    omega
  have hfr_h : (base + epochHdrWords) +
      ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3 ≤ x.frontier := by
    have : offCompLM U w N ≤ offCompItems U w N := by
      unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
    dsimp only [offCompLM, epochHashSpace, qBits, hashB, epochQBits, epochHashB] at *
    omega
  have hfit_h : Fits w ((base + epochHdrWords) +
      ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3) := hfit_fr.of_le hfr_h
  have hc_lt : 2 * reducedChunkBits
      (reducedTrinomialStep (qBits U N) (hashB N) (totalMicroBits N)) < w :=
    ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space
      (two_mul_reducedChunkBits_hash_le hw2 hNU hU.le) hfit_h
  have hfr_s : (base + offScratch) + scratchWords ≤ x.frontier := by
    unfold offScratch scratchWords; omega
  have hfit_s : Fits w ((base + offScratch) + scratchWords) := hfit_fr.of_le hfr_s
  have hdisj : (base + epochHdrWords) +
      ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3 ≤ base + offScratch ∨
      (base + offScratch) + scratchWords ≤ base + epochHdrWords :=
    Or.inr (by unfold offScratch scratchWords epochHdrWords; omega)
  have hms_eq : memoryState rFr x.toData = ⟨x.mem, x.frontier⟩ :=
    Memory.State.ext rfl hrFr
  let u_q : Fin (2 ^ quotientBits U N) := ⟨q, hq_lt⟩
  obtain ⟨hpre_eh, hv_eh, hcost_eh, hres_eh, hfr_eh, hout_eh⟩ :=
    evalHashGenProg_spec (w := w) (U := 2 ^ quotientBits U N)
      (w₀ := qBits U N) (b := hashB N) (b' := totalMicroBits N) (k := 3)
      (hashBase := base + epochHdrWords) (scratchBase := base + offScratch)
      (θ := θ) (u := u_q) (s₀ := memoryState rFr x.toData)
      (qBits_pos U N) (qBits_le_of_le_pow hw hU.le)
      (two_pow_quotientBits_le_two_pow_qBits U N)
      (totalMicroBits_le_of_le_pow hNU hU.le) (by decide) hc_lt
      (by rw [hms_eq]; exact hfr_h) hfit_h
      (by rw [hms_eq]; exact hfr_s) hfit_s hdisj hsplit.hash_rep
  set hp := mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3
  set d_eh := (hp, base + epochHdrWords, base + offScratch, q)
  have hin_eh : x.regs ∘ srcEvalHash = WordEncoding.encode d_eh :=
    (regs_pairSrc (regs_hp_eq hhp)
      (regs_pairSrc (regs_reg1_eq rHashBase hrHash)
        (regs_pairSrc (regs_reg1_eq rScratchBase hrScr) (regs_reg1_eq rQuot hrQuot)))).eq
  have hnoalloc_eh : ((Memory.spec 0).clientState (memoryState rFr x.toData)
      (evalHashGenProg d_eh)).frontier ≤ x.frontier := by
    rw [hfr_eh, hms_eq]
  obtain ⟨y, hex_eh, hyb, hyf, hm_eh, hout_reg, hframe_eh⟩ :=
    execWitness wEvalHash factor_wEvalHash_le rFr srcEvalHash tmpEvalHash
      tmpEvalHash_inj srcEvalHash_ne_tmp tmpEvalHash_ne_rFr srcEvalHash_ne_rFr
      d_eh hx hL hin_eh hpre_eh hv_eh hnoalloc_eh
  have hT_le : inEpochFactor * (memoryCost (evalHashGenProg d_eh) (memoryState rFr x.toData) + 1) ≤
      45206 * inEpochFactor := by
    have : evalMemBound 3 = 45151 := by decide
    rw [mul_comm 45206]; exact Nat.mul_le_mul_left _ (by omega)
  have hy_mem_eq : y.mem =
      ((Memory.spec 0).clientState (memoryState rFr x.toData) (evalHashGenProg d_eh)).mem :=
    congrArg Memory.State.mem hm_eh
  have hy_rFr : y.regs rFr = y.frontier := by
    have hfr_m := congrArg Memory.State.frontier hm_eh
    change y.regs rFr = _ at hfr_m
    rw [hfr_m, hfr_eh, hms_eq, hyf]
  have hy_hout : y.regs rHashOut = hValOfSeed U N θ q := by
    have h0 := hout_reg 0
    rw [tmpEvalHash_out, hres_eh] at h0
    change y.regs rHashOut =
      (reducedPolyHash (2 ^ quotientBits U N) (qBits U N) (hashB N)
        (totalMicroBits N) 3 θ u_q).val at h0
    rw [h0]
    unfold hValOfSeed evalQuotHash
    have hu_eq : u_q = ⟨q % 2 ^ quotientBits U N, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hq_lt).symm
    rw [hu_eq]
  have hy_out_mem : ∀ a, (a < base + offScratch ∨ base + epochHdrWords ≤ a) →
      y.mem a = x.mem a := fun a ha => by
    rw [hy_mem_eq]; exact hout_eh a ha
  have hsplit_y : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨y.mem, y.frontier⟩ :=
    compactedSplitRep_of_scratch_mod hw hsplit hyf hy_out_mem
  refine ⟨y, hex_eh.mono hT_le (fun _ h => h), hyb, hyf, hy_rFr, hy_hout, hsplit_y, hy_out_mem,
    fun reg hne_fr hlt88 hne_ho => hframe_eh reg hne_fr
      (mkTmp_ne_reg _ hlt88 (fun a => by fin_cases a; exact hne_ho.symm))⟩

theorem evalKeyHashCode_exec {U V w N n n_init base L_peak : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} (u : Fin U) {x : RData rEpoch}
    (hx : x.Bounded w) (hn : 0 < n) (hev : EpochValid U n N)
    (hfr : x.frontier = base + compactedEpochWords U V w N n)
    (hL : x.frontier ≤ L_peak)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩)
    (hrFr : x.regs rFr = x.frontier)
    (hrHash : x.regs rHashBase = base + epochHdrWords)
    (hrScr : x.regs rScratchBase = base + offScratch)
    (hrArgU : x.regs rArgU = u.val)
    (hhp : ∀ i : Fin 19, x.regs (hpReg i) =
      mkHashParams w (epochQBits U N) (epochHashB N) (totalMicroBits N) 3 i)
    (hcp : ∀ i : Fin 36, x.regs (cpReg i) = mkCompParams U V w N i) :
    ∃ y : RData rEpoch,
      RDemonicExec w L_peak evalKeyHashCode x (45207 * inEpochFactor) (· = y) ∧
      y.Bounded w ∧ y.frontier = x.frontier ∧
      y.regs rFr = y.frontier ∧
      y.regs rHashOut = hValOfSeed U N θ (keyQuotient (bucketBits N) u.val) ∧
      CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
        ⟨y.mem, y.frontier⟩ ∧
      (∀ a, (a < base + offScratch ∨ base + epochHdrWords ≤ a) → y.mem a = x.mem a) ∧
      ∀ reg, reg ≠ rFr → reg.val < 88 → reg ≠ rQuot → reg ≠ rHashOut →
        y.regs reg = x.regs reg := by
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hx hsplit.root_hdr
  have hNU : N ≤ U := by rcases hev with ⟨rfl, _⟩ | ⟨_, _, _, hNU⟩ <;> omega
  have hfr_pos : x.frontier = base + offCompItems U w N + compactedItemWords U V w N n := by
    rw [hfr]; unfold compactedEpochWords; rw [ite_eq_right hn.ne']; omega
  have hfit_off : Fits w (base + offCompItems U w N) := hx.frontier_fits.of_le (by omega)
  have hcp_fit := fits_mkCompParams (U := U) (V := V) (w := w) (N := N) hw hNU hU hV hfit_off
  have hin_eq : x.regs ∘ srcExtractQuot = WordEncoding.encode (mkCompParams U V w N, u.val) :=
    (regs_pairSrc (regs_cp_eq hcp) (regs_reg1_eq rArgU hrArgU)).eq
  have hsafe_eq : CompExtractQuotPre w (mkCompParams U V w N, u.val) (memoryState rFr x.toData) :=
    ⟨u.isLt.trans hU, hcp_fit ⟨20, by decide⟩⟩
  have hnoalloc_eq : ((Memory.spec 0).clientState (memoryState rFr x.toData)
      (compExtractQuotGenProg (mkCompParams U V w N, u.val))).frontier ≤ x.frontier := by
    rw [clientState_compExtractQuotGenProg]; exact hrFr.le
  have hv_eq_hist : (Memory.spec w).ValidHistory (memoryState rFr x.toData)
      ((Memory.spec w).clientHistory (memoryState rFr x.toData)
        (compExtractQuotGenProg (mkCompParams U V w N, u.val))) :=
    validProg_compExtractQuotGen _ _ ⟨wellFormed_memoryState hx.1, Nat.zero_le _⟩
  obtain ⟨x₁, hex₁, hx₁b, hx₁f, hm_eq, hout_eq, hframe_eq⟩ :=
    execWitness wExtractQuot factor_wExtractQuot_le rFr srcExtractQuot tmpExtractQuot
      tmpExtractQuot_inj srcExtractQuot_ne_tmp tmpExtractQuot_ne_rFr srcExtractQuot_ne_rFr
      (mkCompParams U V w N, u.val) hx hL hin_eq hsafe_eq hv_eq_hist hnoalloc_eq
  rw [memoryCost_compExtractQuotGenProg, zero_add, mul_one] at hex₁
  rw [clientState_compExtractQuotGenProg] at hm_eq
  have hx₁m : x₁.mem = x.mem := congrArg Memory.State.mem hm_eq
  have hx₁_rFr : x₁.regs rFr = x₁.frontier := by
    have hfm := congrArg Memory.State.frontier hm_eq
    change x₁.regs rFr = x.regs rFr at hfm
    rw [hfm, hrFr, hx₁f]
  have hx₁_quot : x₁.regs rQuot = keyQuotient (bucketBits N) u.val := by
    have h0 := hout_eq 0
    rw [tmpExtractQuot_out, clientResult_compExtractQuotGenProg] at h0
    exact h0
  have hx₁_pres : ∀ reg, reg ≠ rFr → reg.val < 88 → reg ≠ rQuot → x₁.regs reg = x.regs reg :=
    fun reg h1 h88 hq => hframe_eq reg h1
      (mkTmp_ne_reg _ h88 (fun a => by fin_cases a; exact hq.symm))
  have hq_lt : keyQuotient (bucketBits N) u.val < 2 ^ quotientBits U N :=
    keyQuotient_lt_two_pow_quotientBits hNU u.isLt
  obtain ⟨y, hex₂, hyb, hyf, hy_rFr, hy_hout, hsplit_y, hy_out_mem, hy_pres⟩ :=
    runEvalHashAtQuot hx₁b hn hev (hx₁f.trans hfr) (hx₁f.le.trans hL)
      (by rw [hx₁m, hx₁f]; exact hsplit) hx₁_rFr
      ((hx₁_pres rHashBase (eReg_ne (by decide)) (eReg_lt_88 _) (eReg_ne (by decide))).trans hrHash)
      ((hx₁_pres rScratchBase (eReg_ne (by decide)) (eReg_lt_88 _)
        (eReg_ne (by decide))).trans hrScr)
      hx₁_quot
      (fun i => (hx₁_pres (hpReg i) (hpReg_ne_eReg i (by decide)) (hpReg_lt_88 i)
        (hpReg_ne_eReg i (by decide))).trans (hhp i))
      hq_lt
  refine ⟨y, (hex₁.seq_eq hex₂).mono (by omega) (fun _ h => h),
    hyb, hyf.trans hx₁f, hy_rFr, hy_hout, hsplit_y,
    fun a ha => (hy_out_mem a ha).trans (congrFun hx₁m a),
    fun reg h1 h88 hq hho => (hy_pres reg h1 h88 hho).trans (hx₁_pres reg h1 h88 hq)⟩

/-! ## Section 9: Epoch Environment, Global-Metadata Frame, and `growZeroPost` Boundedness -/

theorem compEpochEnv_of_split {U V w N n n_init base : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {x : RData rEpoch}
    (hx : x.Bounded w) (hn : 0 < n) (hev : EpochValid U n N)
    (hfr : x.frontier = base + compactedEpochWords U V w N n)
    (hsplit : CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs
      ⟨x.mem, x.frontier⟩) :
    CompEpochEnv U V w N base (base + offCompItems U w N) n ⟨x.mem, x.frontier⟩ ∧
    Fits w (base + offCompItems U w N) := by
  obtain ⟨hw, hU, hV⟩ := rootHeaderValid_bounds hx hsplit.root_hdr
  rcases hev with ⟨rfl, _⟩ | ⟨_, hnN, _, hNU⟩
  · omega
  · have hfr_pos : x.frontier = base + offCompItems U w N + compactedItemWords U V w N n := by
      rw [hfr]; unfold compactedEpochWords; rw [ite_eq_right hn.ne']; omega
    exact ⟨⟨hw, by omega, hNU, hU, hV, le_rfl, by change _ ≤ x.frontier; omega⟩,
      hx.frontier_fits.of_le (by omega)⟩

theorem compGmAt_eq_of_scratch_mod {U w N base : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (hout : ∀ a, (a < base + offScratch ∨ base + epochHdrWords ≤ a) → mem₁ a = mem₂ a) :
    compGmAt base U w N mem₁ = compGmAt base U w N mem₂ := by
  have h0 : epochHdrWords ≤ offCompLM U w N := Nat.le_add_right _ _
  have h1 : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  exact compGmAt_congr hw fun a ha => hout a (Or.inr (by omega))

theorem growZeroPost_bounded {r w : ℕ} {rK rRes rCur rIdx rZero rOne : Fin r} {x : RData r}
    (hx : x.Bounded w) (h1 : Fits w 1) (hfit : Fits w (x.frontier + x.regs rK)) :
    (growZeroPost rK rRes rCur rIdx rZero rOne x).Bounded w := by
  refine ⟨⟨fun j => ?_, hx.mem_fits⟩, hfit, fun a ha => hx.zero_above ?_⟩
  · dsimp only [growZeroPost, RData.toData]
    simp only [Function.update_apply]
    split_ifs
    all_goals first | exact fits_zero w | exact h1 | exact hx.regs_fits _ | exact hx.frontier_fits
  · dsimp only [growZeroPost] at ha; omega

theorem shrinkPost_bounded {r w : ℕ} {rK rIdx rZero rOne : Fin r} {x : RData r}
    (hx : x.Bounded w) (h1 : Fits w 1) (hk_le : x.regs rK ≤ x.frontier) :
    (shrinkPost rK rIdx rZero rOne x).Bounded w :=
  (((hx.shrink hk_le).set (i := rZero) (fits_zero w)).set (i := rOne) h1).set (i := rIdx)
    (hx.regs_fits rK)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
