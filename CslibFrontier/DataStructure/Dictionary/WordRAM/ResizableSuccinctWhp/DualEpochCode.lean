/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.WordRAM.Resizable.Randomized.IncrementalRebuild
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.MigratePhase8
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map

/-!
# Resizable Word RAM `SubroutineCode` and Single-Step `ExecRCodeSteps` (`DualEpochCode`)

Defines the uniform `RCode .exact rWhp` initializer (`initCodeWhp`), parameter-free operational
dispatcher (`opCodeWhp`), and `Resizable.SubroutineCode` packages (`subroutineCodeWhp` and
`subroutineCodeWhpStandard`) for the 12-phase deamortized dual-epoch resizable succinct dictionary
of [Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024], and proves their `¬ReadsWidth`,
`RDemonicExec`, and single-operation `ExecRCodeSteps` specifications (`initCodeWhp_demonicExec`,
`opCodeWhp_query_exec`, `opCodeWhp_mutate_det_exec`, `opCodeWhp_mutate_ph5_exec`).

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM.Resizable
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability
open EpochUpdate
open scoped ENNReal

/-! ## Section 1: Register File, Leaf Lifter, `initCodeWhp`, `opCodeWhp`, and `SubroutineCode` -/

private noncomputable def wPrepGrow :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_prepGrow
private noncomputable def wStepOp :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_stepOp
private noncomputable def wPostRandShrink :=
  RealizesBounded.Witness.ofRealizesBounded realizesBounded_postRandShrink

/-- Maximum scratch register count across the three operational `RealizesBounded` leaf programs. -/
private noncomputable def maxWhpLeafScratch : ℕ :=
  max wPrepGrow.scratchSize (max wStepOp.scratchSize wPostRandShrink.scratchSize)

/-- Total register count `23 + maxWhpLeafScratch` for `subroutineCodeWhp`:
* `0`: `mBaseWhp` (persistent `baseReg`)
* `1`: `mFrWhp` (persistent register tracking `x.frontier` at rest)
* `2..4`: `rTag`, `rKey`, `rVal` (`whpInput = true`)
* `5`: `rFrArg` (non-`fr` copy of `mFrWhp` for `RealizesBounded` input tuples)
* `6..7`: `rOutFlag`, `rOutVal` (decoded query observation)
* `8..15`: `rK`, `rRes`, `rCur`, `rEnd`, `rMask`, `rIdx`, `rZero`, `rOne`
* `16..`: output & scratch temporaries for `RealizesBounded` leaf subroutines. -/
noncomputable def rWhp : ℕ := 23 + maxWhpLeafScratch

theorem le_rWhp_23 : 23 ≤ rWhp :=
  Nat.le_add_right 23 maxWhpLeafScratch

/-- Fixed control register bank `0..22` inside `Fin rWhp`. -/
@[expose]
noncomputable def whpReg : Fin 23 → Fin rWhp :=
  Fin.castLE le_rWhp_23

private theorem whpReg_injective : Function.Injective whpReg :=
  Fin.castLE_injective le_rWhp_23

@[simp]
private theorem whpReg_inj {i j : Fin 23} : whpReg i = whpReg j ↔ i = j :=
  whpReg_injective.eq_iff

@[simp]
private theorem val_whpReg (i : Fin 23) : (whpReg i).val = i.val := rfl

private theorem whpReg_ne {i j : Fin 23} (h : i ≠ j) : whpReg i ≠ whpReg j :=
  fun heq => h (whpReg_injective heq)

private theorem ne_of_val_ne {a b : Fin rWhp} (h : a.val ≠ b.val) : a ≠ b :=
  fun heq => h (congrArg Fin.val heq)

/-- Persistent base-address register (`0`) of `subroutineCodeWhp`. -/
noncomputable abbrev mBaseWhp : Fin rWhp := whpReg 0

/-- Persistent hardware-frontier mirror register (`1`) of `subroutineCodeWhp`. -/
noncomputable abbrev mFrWhp : Fin rWhp := whpReg 1

private noncomputable abbrev rTag : Fin rWhp := whpReg 2
private noncomputable abbrev rKey : Fin rWhp := whpReg 3
private noncomputable abbrev rVal : Fin rWhp := whpReg 4
private noncomputable abbrev rFrArg : Fin rWhp := whpReg 5

/-- Output presence-flag register (`6`: `1` = `some`, `0` = `none`) for `query`. -/
noncomputable abbrev rOutFlag : Fin rWhp := whpReg 6

/-- Output value register (`7`) for `query`. -/
noncomputable abbrev rOutVal : Fin rWhp := whpReg 7

private noncomputable abbrev rK : Fin rWhp := whpReg 8
private noncomputable abbrev rRes : Fin rWhp := whpReg 9
private noncomputable abbrev rCur : Fin rWhp := whpReg 10
private noncomputable abbrev rEnd : Fin rWhp := whpReg 11
private noncomputable abbrev rMask : Fin rWhp := whpReg 12
private noncomputable abbrev rIdx : Fin rWhp := whpReg 13
private noncomputable abbrev rZero : Fin rWhp := whpReg 14
private noncomputable abbrev rOne : Fin rWhp := whpReg 15
private noncomputable abbrev rTmp0 : Fin rWhp := whpReg 16
private noncomputable abbrev rTmp1 : Fin rWhp := whpReg 17
private noncomputable abbrev rTmp2 : Fin rWhp := whpReg 18
private noncomputable abbrev rTmp3 : Fin rWhp := whpReg 19
private noncomputable abbrev rTmp4 : Fin rWhp := whpReg 20

private noncomputable def mkWhpTmp {l s : ℕ} (hle_out : l ≤ 5) (hle_scr : s ≤ maxWhpLeafScratch)
    (j : Fin (l + s + 1)) : Fin rWhp :=
  if h : j.val < 5 then whpReg ⟨16 + j.val, by omega⟩
  else ⟨16 + j.val, by have := j.isLt; dsimp [rWhp]; omega⟩

private theorem val_mkWhpTmp {l s : ℕ} (hle_out : l ≤ 5) (hle_scr : s ≤ maxWhpLeafScratch)
    (j : Fin (l + s + 1)) : (mkWhpTmp hle_out hle_scr j).val = 16 + j.val := by
  dsimp only [mkWhpTmp]
  split_ifs with h <;> simp

private theorem mkWhpTmp_castAdd {l s : ℕ} (hle_out : l ≤ 5) (hle_scr : s ≤ maxWhpLeafScratch)
    (i : Fin l) :
    mkWhpTmp hle_out hle_scr (Fin.castAdd (s + 1) i) =
      whpReg ⟨16 + i.val, by have := i.isLt; omega⟩ := by
  dsimp only [mkWhpTmp, Fin.val_castAdd]
  exact dite_eq_left (lt_of_lt_of_le i.isLt hle_out)

private noncomputable def emitWhpWitness {k l : ℕ} {δ α : Type}
    {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safe : ℕ → δ → Memory.State → Prop}
    (W : RealizesBounded.Witness .exact p input output safe (fun _ _ => 0))
    (hle_out : l ≤ 5) (hle_scr : W.scratchSize ≤ maxWhpLeafScratch)
    (src : Fin k → Fin rWhp) : RCode .exact rWhp :=
  RCode.ofCode (W.code mFrWhp src (mkWhpTmp hle_out hle_scr))

private theorem emitWhpWitness_not_readsWidth {k l : ℕ} {δ α : Type}
    {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safe : ℕ → δ → Memory.State → Prop}
    (W : RealizesBounded.Witness .exact p input output safe (fun _ _ => 0))
    (hle_out : l ≤ 5) (hle_scr : W.scratchSize ≤ maxWhpLeafScratch)
    (src : Fin k → Fin rWhp)
    (hsrc_lt : ∀ i, (src i).val < 6) (hsrc_ne : ∀ i, (src i).val ≠ 1) :
    ¬(emitWhpWitness W hle_out hle_scr src).ReadsWidth := by
  let tmp := mkWhpTmp hle_out hle_scr
  have hi : Function.Injective tmp := fun a b hab => Fin.ext (by
    have hv := congrArg Fin.val hab
    rw [val_mkWhpTmp, val_mkWhpTmp] at hv; omega)
  have hd : ∀ i j, src i ≠ tmp j := fun i j hij => by
    have hv := congrArg Fin.val hij; have := hsrc_lt i
    rw [val_mkWhpTmp] at hv; omega
  have hf : ∀ j, tmp j ≠ mFrWhp := fun j hj => by
    have hv := congrArg Fin.val hj
    rw [val_mkWhpTmp] at hv; simp [mFrWhp] at hv; omega
  have hs : ∀ i, src i ≠ mFrWhp := fun i hsi =>
    hsrc_ne i (by simpa [mFrWhp] using congrArg Fin.val hsi)
  unfold emitWhpWitness
  rw [RCode.readsWidth_ofCode]
  exact (W.code_spec mFrWhp src tmp hi hd hf hs).1

private theorem emitWhpWitness_exec {k l : ℕ} {δ α : Type}
    {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safe : ℕ → δ → Memory.State → Prop}
    (W : RealizesBounded.Witness .exact p input output safe (fun _ _ => 0))
    (hle_out : l ≤ 5) (hle_scr : W.scratchSize ≤ maxWhpLeafScratch)
    (src : Fin k → Fin rWhp)
    (hsrc_lt : ∀ i, (src i).val < 6) (hsrc_ne : ∀ i, (src i).val ≠ 1)
    {w L_peak : ℕ} {x : RData rWhp} (d : δ)
    (hx : x.Bounded w) (hL_peak : x.frontier ≤ L_peak)
    (hfr : x.regs mFrWhp = x.frontier)
    (hin : x.regs ∘ src = input d)
    (hsafe : safe w d (Memory.State.mk x.mem x.frontier))
    (hv : (Memory.spec w).ValidHistory ⟨x.mem, x.frontier⟩
      ((Memory.spec w).clientHistory ⟨x.mem, x.frontier⟩ (p d)))
    (hnoalloc : ((Memory.spec 0).clientState ⟨x.mem, x.frontier⟩ (p d)).frontier = x.frontier) :
    ∃ y : RData rWhp,
      RDemonicExec w L_peak (emitWhpWitness W hle_out hle_scr src) x
        (W.factor * (memoryCost (p d) ⟨x.mem, x.frontier⟩ + 1)) (· = y) ∧
      y.Bounded w ∧
      y.frontier = x.frontier ∧
      y.mem = ((Memory.spec 0).clientState ⟨x.mem, x.frontier⟩ (p d)).mem ∧
      (∀ (i : Fin rWhp), i.val < 16 → y.regs i = x.regs i) ∧
      (∀ (j : Fin l),
        y.regs (whpReg ⟨16 + j.val, by have := j.isLt; omega⟩) =
          output ((Memory.spec 0).clientResult ⟨x.mem, x.frontier⟩ (p d)) j) := by
  let tmp := mkWhpTmp hle_out hle_scr
  have hi : Function.Injective tmp := fun a b hab => Fin.ext (by
    have hv_eq := congrArg Fin.val hab
    rw [val_mkWhpTmp, val_mkWhpTmp] at hv_eq; omega)
  have hd : ∀ i j, src i ≠ tmp j := fun i j hij => by
    have hv_eq := congrArg Fin.val hij; have := hsrc_lt i
    rw [val_mkWhpTmp] at hv_eq; omega
  have hf : ∀ j, tmp j ≠ mFrWhp := fun j hj => by
    have hv_eq := congrArg Fin.val hj
    rw [val_mkWhpTmp] at hv_eq; simp [mFrWhp] at hv_eq; omega
  have hs : ∀ i, src i ≠ mFrWhp := fun i hsi =>
    hsrc_ne i (by simpa [mFrWhp] using congrArg Fin.val hsi)
  have hms_eq : memoryState mFrWhp x.toData = ⟨x.mem, x.frontier⟩ :=
    Memory.State.ext rfl hfr
  obtain ⟨_, hrun⟩ := W.code_spec mFrWhp src tmp hi hd hf hs
  obtain ⟨yd, hy_eb, hm, hout, hframe⟩ := hrun w d x.toData hx.1 hin
    (by rw [hms_eq]; exact hsafe) (by rw [hms_eq]; exact hv)
  rw [clientState_width, hms_eq] at hm
  rw [clientResult_width, hms_eq] at hout
  have hy_fr_eq : yd.regs mFrWhp = x.frontier := by
    have hm_fr := congrArg Memory.State.frontier hm
    change yd.regs mFrWhp = _ at hm_fr
    exact hm_fr.trans hnoalloc
  obtain ⟨n_st, hn_st, hy_ex⟩ := hy_eb
  have hy_bdd : (⟨yd.regs, yd.mem, x.frontier⟩ : RData rWhp).Bounded w :=
    ⟨hy_ex.bounded hx.1, hx.2.1, fun a ha =>
      (execBoundedExact_mem_eq_of_ge hy_ex (hy_fr_eq.le.trans ha)).trans (hx.zero_above ha)⟩
  have hdem : RDemonicExec w L_peak (emitWhpWitness W hle_out hle_scr src) x
      (W.factor * (memoryCost (p d) ⟨x.mem, x.frontier⟩ + 1))
      (· = ⟨yd.regs, yd.mem, x.frontier⟩) := by
    have h0 := RDemonicExec.of_execBounded hL_peak hy_fr_eq.le ⟨n_st, hn_st, hy_ex⟩
    rw [hms_eq, Nat.add_zero] at h0
    exact h0
  refine ⟨⟨yd.regs, yd.mem, x.frontier⟩, hdem, hy_bdd, rfl, congrArg Memory.State.mem hm,
    fun i hi_lt => ?_, fun j => ?_⟩
  · by_cases hif : i = mFrWhp
    · subst hif; exact hy_fr_eq.trans hfr.symm
    · exact hframe i hif fun j hj => by
        have hv_eq := congrArg Fin.val hj
        rw [val_mkWhpTmp] at hv_eq; omega
  · have hj := hout j
    dsimp only [tmp] at hj
    rwa [mkWhpTmp_castAdd] at hj

private abbrev whpReg1 (reg : Fin rWhp) : Fin 1 → Fin rWhp := fun _ => reg

private abbrev whpPairSrc {k₁ k₂ : ℕ} (s₁ : Fin k₁ → Fin rWhp) (s₂ : Fin k₂ → Fin rWhp) :
    Fin (k₁ + k₂) → Fin rWhp :=
  Fin.append s₁ s₂

private def WhpRegsEncode {α : Type} [WordEncoding α] {k : ℕ} (x : RData rWhp)
    (s : Fin k → Fin rWhp) (a : α) : Prop :=
  ∃ hk : k = WordEncoding.width α,
    ∀ i : Fin k, x.regs (s i) = WordEncoding.encode a (Fin.cast hk i)

private theorem WhpRegsEncode.eq {α : Type} [WordEncoding α] {x : RData rWhp}
    {s : Fin (WordEncoding.width α) → Fin rWhp} {a : α} (h : WhpRegsEncode x s a) :
    x.regs ∘ s = WordEncoding.encode a := by
  obtain ⟨hk, hf⟩ := h
  have hk_rfl : hk = rfl := Subsingleton.elim _ _
  subst hk_rfl
  exact funext hf

private theorem whpRegs_reg1 {x : RData rWhp} (reg : Fin rWhp) {v : ℕ}
    (hv : x.regs reg = v) : WhpRegsEncode x (whpReg1 reg) v :=
  ⟨rfl, fun i => by fin_cases i; exact hv⟩

private theorem whpRegs_pair {α β : Type} [WordEncoding α] [WordEncoding β]
    {k₁ k₂ : ℕ} {x : RData rWhp}
    {s₁ : Fin k₁ → Fin rWhp} {s₂ : Fin k₂ → Fin rWhp} {a : α} {b : β}
    (h₁ : WhpRegsEncode x s₁ a) (h₂ : WhpRegsEncode x s₂ b) :
    WhpRegsEncode x (whpPairSrc s₁ s₂) (a, b) := by
  obtain ⟨rfl, hf₁⟩ := h₁
  obtain ⟨rfl, hf₂⟩ := h₂
  refine ⟨rfl, fun i => i.addCases (fun j => ?_) (fun j => ?_)⟩
  · change x.regs (Fin.append s₁ s₂ (Fin.castAdd _ j)) =
      Fin.append (WordEncoding.encode a) (WordEncoding.encode b) (Fin.castAdd _ j)
    rw [Fin.append_left, Fin.append_left]; exact hf₁ j
  · change x.regs (Fin.append s₁ s₂ (Fin.natAdd _ j)) =
      Fin.append (WordEncoding.encode a) (WordEncoding.encode b) (Fin.natAdd _ j)
    rw [Fin.append_right, Fin.append_right]; exact hf₂ j

private theorem whpPairSrc_forall {P : Fin rWhp → Prop} {k₁ k₂ : ℕ}
    {s₁ : Fin k₁ → Fin rWhp} {s₂ : Fin k₂ → Fin rWhp}
    (h₁ : ∀ i, P (s₁ i)) (h₂ : ∀ j, P (s₂ j)) :
    ∀ i, P (whpPairSrc s₁ s₂ i) := fun i =>
  i.addCases
    (fun j => by dsimp only [whpPairSrc]; rw [Fin.append_left]; exact h₁ j)
    (fun j => by dsimp only [whpPairSrc]; rw [Fin.append_right]; exact h₂ j)

private theorem wordEncode_pair (a b : ℕ) :
    WordEncoding.encode (a, b) (0 : Fin 2) = a ∧
    WordEncoding.encode (a, b) (1 : Fin 2) = b :=
  ⟨Fin.append_left (WordEncoding.encode a) (WordEncoding.encode b) (0 : Fin 1),
   Fin.append_right (WordEncoding.encode a) (WordEncoding.encode b) (0 : Fin 1)⟩

private theorem wordEncode_five (p : (ℕ × ℕ) × (ℕ × (ℕ × ℕ))) :
    WordEncoding.encode p (0 : Fin 5) = p.1.1 ∧
    WordEncoding.encode p (1 : Fin 5) = p.1.2 ∧
    WordEncoding.encode p (2 : Fin 5) = p.2.1 ∧
    WordEncoding.encode p (3 : Fin 5) = p.2.2.1 ∧
    WordEncoding.encode p (4 : Fin 5) = p.2.2.2 := by
  rcases p with ⟨⟨a, b⟩, ⟨c, ⟨d, e⟩⟩⟩
  have h_ab := wordEncode_pair a b
  have h_de := wordEncode_pair d e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (Fin.append_left (WordEncoding.encode (a, b)) (WordEncoding.encode (c, (d, e)))
      (0 : Fin 2)).trans h_ab.1
  · exact (Fin.append_left (WordEncoding.encode (a, b)) (WordEncoding.encode (c, (d, e)))
      (1 : Fin 2)).trans h_ab.2
  · exact (Fin.append_right (WordEncoding.encode (a, b)) (WordEncoding.encode (c, (d, e)))
      (0 : Fin 3)).trans
      (Fin.append_left (WordEncoding.encode c) (WordEncoding.encode (d, e)) (0 : Fin 1))
  · exact (Fin.append_right (WordEncoding.encode (a, b)) (WordEncoding.encode (c, (d, e)))
      (1 : Fin 3)).trans
      ((Fin.append_right (WordEncoding.encode c) (WordEncoding.encode (d, e))
        (0 : Fin 2)).trans h_de.1)
  · exact (Fin.append_right (WordEncoding.encode (a, b)) (WordEncoding.encode (c, (d, e)))
      (2 : Fin 3)).trans
      ((Fin.append_right (WordEncoding.encode c) (WordEncoding.encode (d, e))
        (1 : Fin 2)).trans h_de.2)

private theorem scr_prepGrow_le : wPrepGrow.scratchSize ≤ maxWhpLeafScratch :=
  le_max_left _ _
private theorem scr_stepOp_le : wStepOp.scratchSize ≤ maxWhpLeafScratch :=
  (le_max_left _ _).trans (le_max_right _ _)
private theorem scr_postShrink_le : wPostRandShrink.scratchSize ≤ maxWhpLeafScratch :=
  (le_max_right _ _).trans (le_max_right _ _)

private noncomputable def srcPrepGrow :=
  whpPairSrc (whpPairSrc (whpPairSrc (whpReg1 mBaseWhp) (whpReg1 rFrArg)) (whpReg1 rTag))
    (whpReg1 rKey)

private noncomputable def srcStepOp :=
  whpPairSrc (whpPairSrc (whpPairSrc (whpReg1 mBaseWhp) (whpReg1 rFrArg)) (whpReg1 rTag))
    (whpPairSrc (whpReg1 rKey) (whpReg1 rVal))

private noncomputable def srcPostRandShrink :=
  whpPairSrc (whpPairSrc (whpReg1 mBaseWhp) (whpReg1 rFrArg)) (whpReg1 rTag)

private noncomputable def whpPrepGrowCode : RCode .exact rWhp :=
  emitWhpWitness wPrepGrow (by decide) scr_prepGrow_le srcPrepGrow

private noncomputable def whpStepOpCode : RCode .exact rWhp :=
  emitWhpWitness wStepOp (by decide) scr_stepOp_le srcStepOp

private noncomputable def whpPostShrinkCode : RCode .exact rWhp :=
  emitWhpWitness wPostRandShrink (by decide) scr_postShrink_le srcPostRandShrink

/-- Worst-case `O_c(1)` per-operation instruction budget of `opCodeWhp` (depending only on `c`,
independent of `U`, `V`, `w`, `base`, `#(dom s_dict)`, and sequence length). -/
noncomputable def worstCaseTimeWhp (c : ℕ) : ℕ :=
  wPrepGrow.factor * 41 +
  wStepOp.factor *
    ((2 * epochStepCost c + 80) + (itemBatchWhp * (2 * epochStepCost c + 20) + 20000) + 1) +
  wPostRandShrink.factor * 116 +
  14 * bulkBatchWhp + 24

-- Seal witness definitions so `whnf` / `simp` / `omega` never unfold `rWhp` into `Classical.choose`
attribute [local irreducible] wPrepGrow wStepOp wPostRandShrink maxWhpLeafScratch rWhp

private theorem whpGrowBase_nodup :
    [rK, mBaseWhp, rCur, rIdx, rZero, rOne].Nodup :=
  show (List.map whpReg [8, 0, 10, 13, 14, 15]).Nodup from
    (by decide : ([8, 0, 10, 13, 14, 15] : List (Fin 23)).Nodup).map whpReg_injective

private theorem whpGrowRes_nodup :
    [rK, rRes, rCur, rIdx, rZero, rOne].Nodup :=
  show (List.map whpReg [8, 9, 10, 13, 14, 15]).Nodup from
    (by decide : ([8, 9, 10, 13, 14, 15] : List (Fin 23)).Nodup).map whpReg_injective

private theorem whpShrink_nodup :
    [rK, rIdx, rZero, rOne].Nodup :=
  show (List.map whpReg [8, 13, 14, 15]).Nodup from
    (by decide : ([8, 13, 14, 15] : List (Fin 23)).Nodup).map whpReg_injective

private theorem whpRand_nodup :
    [rCur, rEnd, rMask, rRes, rOne].Nodup :=
  show (List.map whpReg [10, 11, 12, 9, 15]).Nodup from
    (by decide : ([10, 11, 12, 9, 15] : List (Fin 23)).Nodup).map whpReg_injective

private theorem whpGrowZeroPost_bounded {w : ℕ} {res : Fin rWhp} {x : RData rWhp}
    (hx : x.Bounded w) (h1 : Fits w 1) (hfit : Fits w (x.frontier + x.regs rK)) :
    (growZeroPost rK res rCur rIdx rZero rOne x).Bounded w := by
  refine ⟨⟨fun j => ?_, hx.mem_fits⟩, hfit, fun a ha => hx.zero_above ?_⟩
  · dsimp only [growZeroPost, RData.toData]
    by_cases hj1 : j = rCur
    · subst hj1; rw [Function.update_self]; exact fits_zero w
    rw [Function.update_of_ne hj1]
    by_cases hj2 : j = rIdx
    · subst hj2; rw [Function.update_self]; exact hx.regs_fits rK
    rw [Function.update_of_ne hj2]
    by_cases hj3 : j = res
    · subst hj3; rw [Function.update_self]
      split_ifs <;> [exact hx.regs_fits j; exact hx.frontier_fits]
    rw [Function.update_of_ne hj3]
    by_cases hj4 : j = rOne
    · subst hj4; rw [Function.update_self]; exact h1
    rw [Function.update_of_ne hj4]
    by_cases hj5 : j = rZero
    · subst hj5; rw [Function.update_self]; exact fits_zero w
    rw [Function.update_of_ne hj5]; exact hx.regs_fits j
  · dsimp only [growZeroPost] at ha; omega

private theorem whpShrinkPost_bounded {w : ℕ} {x : RData rWhp}
    (hx : x.Bounded w) (h1 : Fits w 1) (hk_le : x.regs rK ≤ x.frontier) :
    (shrinkPost rK rIdx rZero rOne x).Bounded w :=
  (((hx.shrink hk_le).set (i := rZero) (fits_zero w)).set (i := rOne) h1).set (i := rIdx)
    (hx.regs_fits rK)

/-- Caller-overwritable argument register mask (`true` on `rTag`, `rKey`, `rVal` at indices `2..4`;
`false` on persistent `mBaseWhp`, `mFrWhp` at `0..1` and non-argument registers `5..rWhp - 1`,
which `prepare` leaves untouched). -/
@[expose]
def whpInput (i : Fin rWhp) : Bool :=
  decide (i.val = 2 ∨ i.val = 3 ∨ i.val = 4)

/-- Standalone register argument encoder for `Dynamic.Op U`:
* `query k` ↦ `(rTag = 0, rKey = k.val, rVal = 0)`
* `insert k v` ↦ `(rTag = 1, rKey = k.val, rVal = v)`
* `delete k` ↦ `(rTag = 2, rKey = k.val, rVal = 0)`. -/
@[expose]
def whpEncode {U : ℕ} : Dynamic.Op U → Fin rWhp → ℕ
  | .query k, i => if i.val = 2 then 0 else if i.val = 3 then k.val else 0
  | .insert k v, i =>
      if i.val = 2 then 1 else if i.val = 3 then k.val else if i.val = 4 then v else 0
  | .delete k, i => if i.val = 2 then 2 else if i.val = 3 then k.val else 0

/-- Output register decoder reading `Option ℕ` from `(rOutFlag, rOutVal)` on `query` and `()` on
`insert` / `delete`. -/
@[expose]
noncomputable def whpDecode {U V : ℕ} (o : Dynamic.Op U) (regs : Fin rWhp → ℕ) :
    Option ((Dynamic.spec U V U).Result o) :=
  match o with
  | .insert _ _ => some ()
  | .delete _ => some ()
  | .query _ => some (if regs rOutFlag = 0 then none else some (regs rOutVal))

/-- Projects `RData r` to `(mem, frontier) : Memory.State`. -/
abbrev rMemState {r : ℕ} (x : RData r) : Memory.State :=
  { mem := x.mem, frontier := x.frontier }

/-- Exact deterministic instruction count (`1164` steps) of `initCodeWhp c U V w`. -/
@[expose]
def initStepsWhp : ℕ := 1164

private noncomputable def initWriteConstCode (off val : ℕ) : RCode .exact rWhp :=
  .seq (.op (.const rCur off))
  (.seq (.op (.exactBin .add rCur mBaseWhp rCur))
  (.seq (.op (.const rRes val))
        (.op (.store rCur rRes))))

private noncomputable def initWriteAddConstCode (off addOff : ℕ) : RCode .exact rWhp :=
  .seq (.op (.const rCur off))
  (.seq (.op (.exactBin .add rCur mBaseWhp rCur))
  (.seq (.op (.const rRes addOff))
  (.seq (.op (.exactBin .add rRes mBaseWhp rRes))
        (.op (.store rCur rRes)))))

private theorem not_readsWidth_initWriteConstCode (off val : ℕ) :
    ¬(initWriteConstCode off val).ReadsWidth := by
  simp [initWriteConstCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin]

private theorem not_readsWidth_initWriteAddConstCode (off addOff : ℕ) :
    ¬(initWriteAddConstCode off addOff).ReadsWidth := by
  simp [initWriteAddConstCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin]

private theorem initWriteConstCode_exec {w L_peak base fr off val : ℕ} {x : RData rWhp}
    (hx : x.Bounded w) (hL : fr ≤ L_peak) (hx_fr : x.frontier = fr)
    (hbase : x.regs mBaseWhp = base) (hfr : x.regs mFrWhp = fr)
    (hoff_fit : Fits w off) (hval_fit : Fits w val) (hlt : base + off < fr) :
    ∃ y : RData rWhp,
      RDemonicExec w L_peak (initWriteConstCode off val) x 4 (· = y) ∧
      y.Bounded w ∧
      y.frontier = fr ∧
      y.regs mBaseWhp = base ∧
      y.regs mFrWhp = fr ∧
      y.mem (base + off) = val ∧
      (∀ addr, addr ≠ base + off → y.mem addr = x.mem addr) := by
  have hL_x : x.frontier ≤ L_peak := hx_fr ▸ hL
  have hfit_addr : Fits w (base + off) := hx.2.1.of_le (hx_fr ▸ hlt.le)
  have e1 := RDemonicExec.const (B := .exact) (d := rCur) (v := off) (x := x) hL_x hoff_fit
  set x1 := x.set rCur off
  have hx1b : x1.Bounded w := hx.set hoff_fit
  have hb1 : x1.regs mBaseWhp = base := by simp [x1, RData.set, hbase]
  have e2 : RDemonicExec w L_peak (.op (.exactBin .add rCur mBaseWhp rCur)) x1 1
      (· = x1.set rCur (base + off)) :=
    RDemonicExec.exactBin (x := x1) hL_x
      (by simp [BinOp.evalExact, x1, RData.set, hbase]) hfit_addr
  set x2 := x1.set rCur (base + off)
  have hx2b : x2.Bounded w := hx1b.set hfit_addr
  have e3 := RDemonicExec.const (B := .exact) (d := rRes) (v := val) (x := x2) hL_x hval_fit
  set x3 := x2.set rRes val
  have hx3b : x3.Bounded w := hx2b.set hval_fit
  have hy_cur : x3.regs rCur = base + off := by simp [x3, x2, RData.set]
  have hy_res : x3.regs rRes = val := by simp [x3, RData.set]
  have e4 := RDemonicExec.store (B := .exact) (w := w) (L_peak := L_peak)
    (a := rCur) (s := rRes) (x := x3) hL_x (by rw [hy_cur]; exact hx_fr.symm ▸ hlt)
  set y := x3.write (x3.regs rCur) (x3.regs rRes)
  have hyb : y.Bounded w := by
    dsimp only [y]; rw [hy_cur, hy_res]
    refine ⟨⟨hx3b.1.1, fun a => ?_⟩, hx3b.2.1, fun a ha => ?_⟩
    · dsimp only [RData.write, RData.toData]
      by_cases ha : a = base + off
      · subst ha; simp [hval_fit]
      · simp [Function.update_of_ne ha, hx3b.mem_fits a]
    · dsimp only [RData.write] at ha ⊢
      have hx3_fr : x3.frontier = fr := hx_fr
      rw [Function.update_of_ne (by omega)]; exact hx3b.zero_above ha
  refine ⟨y, (e1.seq_eq (e2.seq_eq (e3.seq_eq e4))).mono (by omega) (fun _ h => h),
    hyb, hx_fr, ?_, ?_, ?_, fun addr hne => ?_⟩
  · simp [y, x3, x2, x1, RData.write, RData.set, hbase]
  · simp [y, x3, x2, x1, RData.write, RData.set, hfr]
  · dsimp only [y, RData.write]; rw [hy_cur, hy_res, Function.update_self]
  · dsimp only [y, RData.write]; rw [hy_cur, Function.update_of_ne hne]; rfl

private theorem initWriteAddConstCode_exec {w L_peak base fr off addOff : ℕ} {x : RData rWhp}
    (hx : x.Bounded w) (hL : fr ≤ L_peak) (hx_fr : x.frontier = fr)
    (hbase : x.regs mBaseWhp = base) (hfr : x.regs mFrWhp = fr)
    (hoff_fit : Fits w off) (hadd_fit : Fits w addOff)
    (hlt : base + off < fr) (hle_add : base + addOff ≤ fr) :
    ∃ y : RData rWhp,
      RDemonicExec w L_peak (initWriteAddConstCode off addOff) x 5 (· = y) ∧
      y.Bounded w ∧
      y.frontier = fr ∧
      y.regs mBaseWhp = base ∧
      y.regs mFrWhp = fr ∧
      y.mem (base + off) = base + addOff ∧
      (∀ addr, addr ≠ base + off → y.mem addr = x.mem addr) := by
  have hL_x : x.frontier ≤ L_peak := hx_fr ▸ hL
  have hfit_addr : Fits w (base + off) := hx.2.1.of_le (hx_fr ▸ hlt.le)
  have hfit_val : Fits w (base + addOff) := hx.2.1.of_le (hx_fr ▸ hle_add)
  have e1 := RDemonicExec.const (B := .exact) (d := rCur) (v := off) (x := x) hL_x hoff_fit
  set x1 := x.set rCur off
  have hx1b : x1.Bounded w := hx.set hoff_fit
  have hb1 : x1.regs mBaseWhp = base := by simp [x1, RData.set, hbase]
  have e2 : RDemonicExec w L_peak (.op (.exactBin .add rCur mBaseWhp rCur)) x1 1
      (· = x1.set rCur (base + off)) :=
    RDemonicExec.exactBin (x := x1) hL_x
      (by simp [BinOp.evalExact, x1, RData.set, hbase]) hfit_addr
  set x2 := x1.set rCur (base + off)
  have hx2b : x2.Bounded w := hx1b.set hfit_addr
  have e3 := RDemonicExec.const (B := .exact) (d := rRes) (v := addOff) (x := x2) hL_x hadd_fit
  set x3 := x2.set rRes addOff
  have hx3b : x3.Bounded w := hx2b.set hadd_fit
  have e4 : RDemonicExec w L_peak (.op (.exactBin .add rRes mBaseWhp rRes)) x3 1
      (· = x3.set rRes (base + addOff)) :=
    RDemonicExec.exactBin (x := x3) hL_x
      (by simp [BinOp.evalExact, x3, x2, x1, RData.set, hbase]) hfit_val
  set x4 := x3.set rRes (base + addOff)
  have hx4b : x4.Bounded w := hx3b.set hfit_val
  have hy_cur : x4.regs rCur = base + off := by simp [x4, x3, x2, RData.set]
  have hy_res : x4.regs rRes = base + addOff := by simp [x4, RData.set]
  have e5 := RDemonicExec.store (B := .exact) (w := w) (L_peak := L_peak)
    (a := rCur) (s := rRes) (x := x4) hL_x (by rw [hy_cur]; exact hx_fr.symm ▸ hlt)
  set y := x4.write (x4.regs rCur) (x4.regs rRes)
  have hyb : y.Bounded w := by
    dsimp only [y]; rw [hy_cur, hy_res]
    refine ⟨⟨hx4b.1.1, fun a => ?_⟩, hx4b.2.1, fun a ha => ?_⟩
    · dsimp only [RData.write, RData.toData]
      by_cases ha : a = base + off
      · subst ha; simp [hfit_val]
      · simp [Function.update_of_ne ha, hx4b.mem_fits a]
    · dsimp only [RData.write] at ha ⊢
      have hx4_fr : x4.frontier = fr := hx_fr
      rw [Function.update_of_ne (by omega)]; exact hx4b.zero_above ha
  refine ⟨y, (e1.seq_eq (e2.seq_eq (e3.seq_eq (e4.seq_eq e5)))).mono (by omega) (fun _ h => h),
    hyb, hx_fr, ?_, ?_, ?_, fun addr hne => ?_⟩
  · simp [y, x4, x3, x2, x1, RData.write, RData.set, hbase]
  · simp [y, x4, x3, x2, x1, RData.write, RData.set, hfr]
  · dsimp only [y, RData.write]; rw [hy_cur, hy_res, Function.update_self]
  · dsimp only [y, RData.write]; rw [hy_cur, Function.update_of_ne hne]; rfl

private noncomputable def initSmallACode (offP offM kb : ℕ) : RCode .exact rWhp :=
  .seq (initWriteConstCode offP 0)
  (.seq (initWriteAddConstCode (offP + 1) offM)
  (.seq (initWriteConstCode (offP + 48) 0)
  (.seq (initWriteConstCode (offP + 49) 0)
  (.seq (initWriteAddConstCode (offP + 50) hdrSplit)
  (.seq (initWriteAddConstCode (offP + 51) 192)
        (initWriteConstCode (offP + 52) kb))))))

private noncomputable def initSmallBCode (offP wv vb kb : ℕ) : RCode .exact rWhp :=
  .seq (initWriteConstCode (offP + 53) 1)
  (.seq (initWriteConstCode (offP + 54) wv)
  (.seq (initWriteConstCode (offP + 55) 32)
  (.seq (initWriteConstCode (offP + 56) 4)
  (.seq (initWriteAddConstCode (offP + 57) 192)
  (.seq (initWriteConstCode (offP + 58) kb)
  (.seq (initWriteConstCode (offP + 59) vb)
        (initWriteConstCode (offP + 60) 0)))))))

private noncomputable def initSmallConstCode (offP offM wv vb kb : ℕ) : RCode .exact rWhp :=
  .seq (initSmallACode offP offM kb) (initSmallBCode offP wv vb kb)

private noncomputable def initHdrACode (c U V w : ℕ) : RCode .exact rWhp :=
  .seq (initWriteConstCode hdrU1 (U - 1))
  (.seq (initWriteConstCode hdrV1 (V - 1))
  (.seq (initWriteConstCode hdrW w)
  (.seq (initWriteConstCode hdrKeyBits (keyBits U))
  (.seq (initWriteConstCode hdrValBits (valBits V))
  (.seq (initWriteConstCode hdrThresh (if whpThreshold c ≤ U then whpThreshold c else 0))
        (initWriteConstCode hdrCTab (if whpThreshold c ≤ U then cTabWhp c else 0)))))))

private noncomputable def initHdrBCode (c U : ℕ) : RCode .exact rWhp :=
  .seq (initWriteConstCode hdrDTab (if whpThreshold c ≤ U then dTabWhp c else 0))
  (.seq (initWriteConstCode hdrRedW (redWidthWhp U))
  (.seq (initWriteConstCode hdrCEff (if whpThreshold c ≤ U then cEff c else 0))
  (.seq (initWriteAddConstCode hdrItemLo 192)
  (.seq (initWriteAddConstCode hdrItemHi 192)
  (.seq (initWriteConstCode hdrQLo (keyBits U))
        (initWriteConstCode hdrQHi (keyBits U)))))))

/-- Exact-basis (`RCode .exact rWhp`) initializer allocating and zeroing `[base, base + 194)` and
populating the 192-word dual-epoch root header and dual small `ParamTable`s in
`initStepsWhp = 1164` instructions. -/
noncomputable def initCodeWhp (c U V w : ℕ) : RCode .exact rWhp :=
  .seq (.op (.const rK 194))
  (.seq (growZeroCode rK mBaseWhp rCur rIdx rZero rOne)
  (.seq (.op (.exactBin .add mFrWhp mBaseWhp rK))
  (.seq (initHdrACode c U V w)
  (.seq (initHdrBCode c U)
  (.seq (initSmallConstCode hdrPBase0 hdrSmallMeta0 w (valBits V) (keyBits U))
        (initSmallConstCode hdrPBase1 hdrSmallMeta1 w (valBits V) (keyBits U)))))))

/-- `initCodeWhp c U V w` never inspects the ambient word width (`¬ReadsWidth`). -/
theorem not_readsWidth_initCodeWhp (c U V w : ℕ) : ¬(initCodeWhp c U V w).ReadsWidth := by
  simp [initCodeWhp, initHdrACode, initHdrBCode, initSmallConstCode, initSmallACode,
    initSmallBCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    growZeroCode_not_readsWidth, not_readsWidth_initWriteConstCode,
    not_readsWidth_initWriteAddConstCode]

private noncomputable def opPrefixCode (tail : RCode .exact rWhp) : RCode .exact rWhp :=
  .seq (.op (.copy rFrArg mFrWhp))
  (.seq whpPrepGrowCode
  (.seq (.op (.copy rK rTmp0))
  (.seq (growZeroCode rK rRes rCur rIdx rZero rOne)
  (.seq (.op (.exactBin .add mFrWhp mFrWhp rK))
  (.seq (.op (.copy rFrArg mFrWhp))
  (.seq whpStepOpCode
  (.seq (.op (.copy rOutFlag rTmp0))
  (.seq (.op (.copy rOutVal rTmp1))
  (.seq (.op (.copy rCur rTmp2))
  (.seq (.op (.copy rEnd rTmp3))
  (.seq (.op (.copy rMask rTmp4))
        tail)))))))))))

private noncomputable def opSuffixCode : RCode .exact rWhp :=
  .seq whpPostShrinkCode
  (.seq (.op (.copy rK rTmp0))
  (.seq (shrinkCode rK rIdx rZero rOne)
        (.op (.exactBin .sub mFrWhp mFrWhp rK))))

/-- Parameter-free operational body (`RCode .exact rWhp`) executing `query`, `insert`, and `delete`
with worst-case deamortized incremental resizing and `RInstr.rand` seed sampling. -/
noncomputable def opCodeWhp : RCode .exact rWhp :=
  opPrefixCode (.seq (randFillBatchCode rCur rEnd rMask rRes rOne) opSuffixCode)

private theorem srcPrepGrow_lt : ∀ i, (srcPrepGrow i).val < 6 := by
  unfold srcPrepGrow
  exact whpPairSrc_forall (P := fun r => r.val < 6)
    (whpPairSrc_forall (P := fun r => r.val < 6)
      (whpPairSrc_forall (P := fun r => r.val < 6)
        (fun _ => by simp [whpReg1]) (fun _ => by simp [whpReg1]))
      (fun _ => by simp [whpReg1]))
    (fun _ => by simp [whpReg1])

private theorem srcPrepGrow_ne1 : ∀ i, (srcPrepGrow i).val ≠ 1 := by
  unfold srcPrepGrow
  exact whpPairSrc_forall (P := fun r => r.val ≠ 1)
    (whpPairSrc_forall (P := fun r => r.val ≠ 1)
      (whpPairSrc_forall (P := fun r => r.val ≠ 1)
        (fun _ => by simp [whpReg1]) (fun _ => by simp [whpReg1]))
      (fun _ => by simp [whpReg1]))
    (fun _ => by simp [whpReg1])

private theorem srcStepOp_lt : ∀ i, (srcStepOp i).val < 6 := by
  unfold srcStepOp
  exact whpPairSrc_forall (P := fun r => r.val < 6)
    (whpPairSrc_forall (P := fun r => r.val < 6)
      (whpPairSrc_forall (P := fun r => r.val < 6)
        (fun _ => by simp [whpReg1]) (fun _ => by simp [whpReg1]))
      (fun _ => by simp [whpReg1]))
    (whpPairSrc_forall (P := fun r => r.val < 6)
      (fun _ => by simp [whpReg1]) (fun _ => by simp [whpReg1]))

private theorem srcStepOp_ne1 : ∀ i, (srcStepOp i).val ≠ 1 := by
  unfold srcStepOp
  exact whpPairSrc_forall (P := fun r => r.val ≠ 1)
    (whpPairSrc_forall (P := fun r => r.val ≠ 1)
      (whpPairSrc_forall (P := fun r => r.val ≠ 1)
        (fun _ => by simp [whpReg1]) (fun _ => by simp [whpReg1]))
      (fun _ => by simp [whpReg1]))
    (whpPairSrc_forall (P := fun r => r.val ≠ 1)
      (fun _ => by simp [whpReg1]) (fun _ => by simp [whpReg1]))

private theorem srcPostShrink_lt : ∀ i, (srcPostRandShrink i).val < 6 := by
  unfold srcPostRandShrink
  exact whpPairSrc_forall (P := fun r => r.val < 6)
    (whpPairSrc_forall (P := fun r => r.val < 6)
      (fun _ => by simp [whpReg1]) (fun _ => by simp [whpReg1]))
    (fun _ => by simp [whpReg1])

private theorem srcPostShrink_ne1 : ∀ i, (srcPostRandShrink i).val ≠ 1 := by
  unfold srcPostRandShrink
  exact whpPairSrc_forall (P := fun r => r.val ≠ 1)
    (whpPairSrc_forall (P := fun r => r.val ≠ 1)
      (fun _ => by simp [whpReg1]) (fun _ => by simp [whpReg1]))
    (fun _ => by simp [whpReg1])

/-- `opCodeWhp` never inspects the ambient word width (`¬ReadsWidth`). -/
theorem not_readsWidth_opCodeWhp : ¬opCodeWhp.ReadsWidth := by
  have h1 := emitWhpWitness_not_readsWidth wPrepGrow (by decide) scr_prepGrow_le
    srcPrepGrow srcPrepGrow_lt srcPrepGrow_ne1
  have h2 := emitWhpWitness_not_readsWidth wStepOp (by decide) scr_stepOp_le
    srcStepOp srcStepOp_lt srcStepOp_ne1
  have h3 := emitWhpWitness_not_readsWidth wPostRandShrink (by decide) scr_postShrink_le
    srcPostRandShrink srcPostShrink_lt srcPostShrink_ne1
  simp [opCodeWhp, opPrefixCode, opSuffixCode, whpPrepGrowCode, whpStepOpCode,
    whpPostShrinkCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    growZeroCode_not_readsWidth, shrinkCode_not_readsWidth, randFillBatchCode_not_readsWidth,
    h1, h2, h3]

/-- Relocatable `Resizable.SubroutineCode` over `Basis.exact` for the deamortized worst-case WHP
resizable succinct dynamic dictionary. -/
@[expose]
noncomputable def subroutineCodeWhp (c U V w : ℕ) :
    Cslib.DataStructure.WordRAM.Resizable.SubroutineCode .exact rWhp 0 where
  baseReg := mBaseWhp
  initParams := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  input := whpInput
  input_baseReg_false := by simp [whpInput, mBaseWhp]
  initCode := initCodeWhp c U V w
  code := opCodeWhp

/-- Relocatable `Resizable.SubroutineCode` over `Basis.standard` obtained via
`SubroutineCode.toStandard`. -/
noncomputable abbrev subroutineCodeWhpStandard (c U V w : ℕ) :
    Cslib.DataStructure.WordRAM.Resizable.SubroutineCode .standard rWhp 0 :=
  (subroutineCodeWhp c U V w).toStandard

/-- `subroutineCodeWhp c U V w` never inspects the ambient word width (`¬ReadsWidth`). -/
theorem not_readsWidth_subroutineCodeWhp (c U V w : ℕ) : ¬(subroutineCodeWhp c U V w).ReadsWidth :=
  fun h => h.elim (not_readsWidth_initCodeWhp c U V w) not_readsWidth_opCodeWhp

/-- `subroutineCodeWhpStandard c U V w` never inspects the ambient word width (`¬ReadsWidth`). -/
theorem not_readsWidth_subroutineCodeWhpStandard (c U V w : ℕ) :
    ¬(subroutineCodeWhpStandard c U V w).ReadsWidth :=
  Cslib.DataStructure.WordRAM.Resizable.SubroutineCode.not_readsWidth_mapSimulates
    .exactStandard (not_readsWidth_subroutineCodeWhp c U V w)

/-! ## Section 2: Space, Time, Failure Bounds, and `initCodeWhp` Execution -/

/-- Resting `1 · OPT` word-footprint upper bound above `base` at dictionary state `s_dict`. -/
@[expose]
def spaceBoundWhp {U : ℕ} (c V w : ℕ) (s_dict : Dictionary.State U) : ℕ :=
  Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w
    (Dictionary.dom s_dict).card

/-- Stepwise `1 · OPT` peak word-footprint upper bound above `base` across operation `o` from state
`s_dict`. -/
@[expose]
def stepSuccinctPeakWordsWhp {U : ℕ} (c V w : ℕ) (s_dict : Dictionary.State U)
    (o : Dynamic.Op U) : ℕ :=
  max (spaceBoundWhp c V w s_dict)
    (spaceBoundWhp c V w ((Dynamic.spec U V U).stepFn s_dict o).1)

/-- Per-operation WHP slow-path failure probability bound: `0` when `U < whpThreshold c` (small
unhashed regime), and `(max #(dom s_dict) (whpThreshold c))⁻¹ ^ c` otherwise. -/
@[expose]
noncomputable def stepFailureProbWhp {U : ℕ} (c : ℕ) (s_dict : Dictionary.State U)
    (_o : Dynamic.Op U) : ℝ≥0∞ :=
  if U < whpThreshold c then 0
  else (((max (Dictionary.dom s_dict).card (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c)

/-- Pointwise machine representation invariant coupling `s_dict : Dictionary.State U` and
`L : DualLatent c U V` to `x : RData rWhp`. -/
@[expose]
def DualRep (c U V w base : ℕ) (s_dict : Dictionary.State U)
    (L : DualLatent c U V) (x : RData rWhp) : Prop :=
  x.Bounded w ∧
  x.regs mBaseWhp = base ∧
  x.regs mFrWhp = x.frontier ∧
  DualStateInv c U V w base s_dict L (rMemState x)

theorem DualRep.bounded {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {x : RData rWhp} (h : DualRep c U V w base s_dict L x) :
    x.Bounded w :=
  h.1

theorem DualRep.frontier_le {c U V w base : ℕ} {s_dict : Dictionary.State U}
    {L : DualLatent c U V} {x : RData rWhp} (h : DualRep c U V w base s_dict L x) :
    base ≤ x.frontier ∧ x.frontier ≤ base + spaceBoundWhp c V w s_dict ∧
      x.regs mBaseWhp = base :=
  ⟨by have hb : base + 192 ≤ x.frontier := h.2.2.2.base_fr; omega,
   dualStateInv_frontier_le_succinctWords h.2.2.2,
   h.2.1⟩

/-- Standalone encoded arguments fit in `w`-bit words on admissible dictionary operations. -/
theorem whpEncode_fits {U V w : ℕ} (hUw : Fits w U) (hVw : V ≤ 2 ^ w)
    (hw11 : 11 ≤ w) {s_dict : Dictionary.State U} (o : Dynamic.Op U)
    (hv : (Dynamic.spec U V U).valid s_dict o) (i : Fin rWhp) :
    Fits w (whpEncode o i) := by
  have h4 : 4 ≤ 2 ^ w :=
    (by decide : 4 ≤ 2 ^ 11) |>.trans (Nat.pow_le_pow_right (by decide) hw11)
  cases o with
  | query k =>
    dsimp only [whpEncode]
    split_ifs <;> [exact fits_zero w; exact lt_trans k.isLt hUw; exact fits_zero w]
  | insert k v =>
    have hv_lt : v < V := hv.2
    dsimp only [whpEncode]
    split_ifs
    · unfold Fits; omega
    · exact lt_trans k.isLt hUw
    · exact lt_of_lt_of_le hv_lt hVw
    · exact fits_zero w
  | delete k =>
    dsimp only [whpEncode]
    split_ifs
    · unfold Fits; omega
    · exact lt_trans k.isLt hUw
    · exact fits_zero w

private theorem dualPaddedWords_zero_le_spaceBoundWhp (c U V w : ℕ) :
    194 ≤ spaceBoundWhp c V w (Dictionary.empty U) ∧
    dualPaddedWords c U V w 0 0 0 ≤ spaceBoundWhp c V w (Dictionary.empty U) := by
  have hsafe0 : EpochCapSafe (whpThreshold c) U 0 0 := by
    simp only [EpochCapSafe, ↓reduceIte]
    exact ⟨by have := whpThreshold_pos c; omega, Nat.zero_le U⟩
  have hpad := dualPaddedWords_le_succinctWords (V := V) (w := w) hsafe0 hsafe0
  have h194 : 194 ≤ dualPaddedWords c U V w 0 0 0 := by
    unfold dualPaddedWords rootHdrWhp; omega
  have hdom0 : (Dictionary.dom (Dictionary.empty U)).card = 0 := by
    rw [Dictionary.dom_empty, Finset.card_empty]
  unfold spaceBoundWhp
  rw [hdom0]
  exact ⟨h194.trans hpad, hpad⟩

private theorem initSmallACode_exec {U w L_peak base offP offM : ℕ} {x : RData rWhp}
    (hw11 : 11 ≤ w) (hoP : offP = hdrPBase0 ∨ offP = hdrPBase1)
    (hoM : offM = hdrSmallMeta0 ∨ offM = hdrSmallMeta1)
    (fkb : Fits w (keyBits U))
    (hx : x.Bounded w) (hL : base + 194 ≤ L_peak) (hx_fr : x.frontier = base + 194)
    (hbase : x.regs mBaseWhp = base) (hfr : x.regs mFrWhp = base + 194) :
    ∃ y : RData rWhp,
      RDemonicExec w L_peak (initSmallACode offP offM (keyBits U)) x 31 (· = y) ∧
      y.Bounded w ∧
      y.frontier = base + 194 ∧
      y.regs mBaseWhp = base ∧
      y.regs mFrWhp = base + 194 ∧
      y.mem (base + offP) = 0 ∧
      y.mem (base + offP + 1) = base + offM ∧
      y.mem (base + offP + 48) = 0 ∧
      y.mem (base + offP + 49) = 0 ∧
      y.mem (base + offP + 50) = base + hdrSplit ∧
      y.mem (base + offP + 51) = base + 192 ∧
      y.mem (base + offP + 52) = keyBits U ∧
      (∀ addr, ¬(base + offP ≤ addr ∧ addr < base + offP + 53) → y.mem addr = x.mem addr) := by
  have h2048 : 2048 ≤ 2 ^ w :=
    (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
  have f_const : ∀ k ≤ 256, Fits w k := fun k hk => by unfold Fits; omega
  have hoP_le : offP ≤ 128 := by rcases hoP with rfl | rfl <;> decide
  have hoM_lt : offM < 194 := by rcases hoM with rfl | rfl <;> decide
  obtain ⟨x1, e1, b1, fr1, hb1, hf1, v1, n1⟩ := initWriteConstCode_exec (off := offP) (val := 0)
    hx hL hx_fr hbase hfr (f_const _ (by omega)) (fits_zero w) (by omega)
  obtain ⟨x2, e2, b2, fr2, hb2, hf2, v2, n2⟩ := initWriteAddConstCode_exec
    (off := offP + 1) (addOff := offM) b1 hL fr1 hb1 hf1 (f_const _ (by omega))
    (f_const _ (by omega)) (by omega) (by omega)
  obtain ⟨x3, e3, b3, fr3, hb3, hf3, v3, n3⟩ := initWriteConstCode_exec
    (off := offP + 48) (val := 0) b2 hL fr2 hb2 hf2 (f_const _ (by omega)) (fits_zero w) (by omega)
  obtain ⟨x4, e4, b4, fr4, hb4, hf4, v4, n4⟩ := initWriteConstCode_exec
    (off := offP + 49) (val := 0) b3 hL fr3 hb3 hf3 (f_const _ (by omega)) (fits_zero w) (by omega)
  obtain ⟨x5, e5, b5, fr5, hb5, hf5, v5, n5⟩ := initWriteAddConstCode_exec
    (off := offP + 50) (addOff := hdrSplit) b4 hL fr4 hb4 hf4 (f_const _ (by omega))
    (f_const _ (by unfold hdrSplit; omega)) (by omega) (by unfold hdrSplit; omega)
  obtain ⟨x6, e6, b6, fr6, hb6, hf6, v6, n6⟩ := initWriteAddConstCode_exec
    (off := offP + 51) (addOff := 192) b5 hL fr5 hb5 hf5 (f_const _ (by omega))
    (f_const _ (by omega)) (by omega) (by omega)
  obtain ⟨y, e7, by_b, fry, hby, hfy, v7, n7⟩ := initWriteConstCode_exec
    (off := offP + 52) (val := keyBits U) b6 hL fr6 hb6 hf6 (f_const _ (by omega)) fkb (by omega)
  have hex : RDemonicExec w L_peak (initSmallACode offP offM (keyBits U)) x 31 (· = y) :=
    (e1.seq_eq <| e2.seq_eq <| e3.seq_eq <| e4.seq_eq <| e5.seq_eq <|
      e6.seq_eq e7).mono (by omega) (fun _ h => h)
  have ne_add (k1 k2 : ℕ) (hk : k1 ≠ k2) : base + offP + k1 ≠ base + (offP + k2) := by omega
  refine ⟨y, hex, by_b, fry, hby, hfy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun addr ha => ?_⟩
  · rw [n7 (base + offP) (ne_add 0 52 (by decide)), n6 (base + offP) (ne_add 0 51 (by decide)),
      n5 (base + offP) (ne_add 0 50 (by decide)), n4 (base + offP) (ne_add 0 49 (by decide)),
      n3 (base + offP) (ne_add 0 48 (by decide)), n2 (base + offP) (ne_add 0 1 (by decide)), v1]
  · rw [n7 _ (ne_add 1 52 (by decide)), n6 _ (ne_add 1 51 (by decide)),
      n5 _ (ne_add 1 50 (by decide)), n4 _ (ne_add 1 49 (by decide)),
      n3 _ (ne_add 1 48 (by decide)), show base + offP + 1 = base + (offP + 1) by omega, v2]
  · rw [n7 _ (ne_add 48 52 (by decide)), n6 _ (ne_add 48 51 (by decide)),
      n5 _ (ne_add 48 50 (by decide)), n4 _ (ne_add 48 49 (by decide)),
      show base + offP + 48 = base + (offP + 48) by omega, v3]
  · rw [n7 _ (ne_add 49 52 (by decide)), n6 _ (ne_add 49 51 (by decide)),
      n5 _ (ne_add 49 50 (by decide)), show base + offP + 49 = base + (offP + 49) by omega, v4]
  · rw [n7 _ (ne_add 50 52 (by decide)), n6 _ (ne_add 50 51 (by decide)),
      show base + offP + 50 = base + (offP + 50) by omega, v5]
  · rw [n7 _ (ne_add 51 52 (by decide)), show base + offP + 51 = base + (offP + 51) by omega, v6]
  · rw [show base + offP + 52 = base + (offP + 52) by omega, v7]
  · have hne_out : ∀ k < 53, addr ≠ base + (offP + k) := fun k hk => by clear *- ha hk; omega
    rw [n7 addr (hne_out 52 (by decide)), n6 addr (hne_out 51 (by decide)),
      n5 addr (hne_out 50 (by decide)), n4 addr (hne_out 49 (by decide)),
      n3 addr (hne_out 48 (by decide)), n2 addr (hne_out 1 (by decide)),
      n1 addr (by have := hne_out 0 (by decide); simpa using this)]

private theorem initSmallBCode_exec {U V w L_peak base offP : ℕ} {x : RData rWhp}
    (hw11 : 11 ≤ w) (hoP : offP = hdrPBase0 ∨ offP = hdrPBase1)
    (fvb : Fits w (valBits V)) (fkb : Fits w (keyBits U))
    (hx : x.Bounded w) (hL : base + 194 ≤ L_peak) (hx_fr : x.frontier = base + 194)
    (hbase : x.regs mBaseWhp = base) (hfr : x.regs mFrWhp = base + 194) :
    ∃ y : RData rWhp,
      RDemonicExec w L_peak (initSmallBCode offP w (valBits V) (keyBits U)) x 33 (· = y) ∧
      y.Bounded w ∧
      y.frontier = base + 194 ∧
      y.regs mBaseWhp = base ∧
      y.regs mFrWhp = base + 194 ∧
      y.mem (base + offP + 53) = 1 ∧
      y.mem (base + offP + 54) = w ∧
      y.mem (base + offP + 55) = 32 ∧
      y.mem (base + offP + 56) = 4 ∧
      y.mem (base + offP + 57) = base + 192 ∧
      y.mem (base + offP + 58) = keyBits U ∧
      y.mem (base + offP + 59) = valBits V ∧
      y.mem (base + offP + 60) = 0 ∧
      (∀ addr, ¬(base + offP + 53 ≤ addr ∧ addr < base + offP + 61) → y.mem addr = x.mem addr) := by
  have h2048 : 2048 ≤ 2 ^ w :=
    (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
  have f_const : ∀ k ≤ 256, Fits w k := fun k hk => by unfold Fits; omega
  have fw : Fits w w := Nat.lt_two_pow_self
  have hoP_le : offP ≤ 128 := by rcases hoP with rfl | rfl <;> decide
  obtain ⟨x8, e8, b8, fr8, hb8, hf8, v8, n8⟩ := initWriteConstCode_exec
    (off := offP + 53) (val := 1) hx hL hx_fr hbase hfr (f_const _ (by omega))
    (f_const _ (by omega)) (by omega)
  obtain ⟨x9, e9, b9, fr9, hb9, hf9, v9, n9⟩ := initWriteConstCode_exec
    (off := offP + 54) (val := w) b8 hL fr8 hb8 hf8 (f_const _ (by omega)) fw (by omega)
  obtain ⟨x10, e10, b10, fr10, hb10, hf10, v10, n10⟩ := initWriteConstCode_exec
    (off := offP + 55) (val := 32) b9 hL fr9 hb9 hf9 (f_const _ (by omega))
    (f_const _ (by omega)) (by omega)
  obtain ⟨x11, e11, b11, fr11, hb11, hf11, v11, n11⟩ := initWriteConstCode_exec
    (off := offP + 56) (val := 4) b10 hL fr10 hb10 hf10 (f_const _ (by omega))
    (f_const _ (by omega)) (by omega)
  obtain ⟨x12, e12, b12, fr12, hb12, hf12, v12, n12⟩ := initWriteAddConstCode_exec
    (off := offP + 57) (addOff := 192) b11 hL fr11 hb11 hf11 (f_const _ (by omega))
    (f_const _ (by omega)) (by omega) (by omega)
  obtain ⟨x13, e13, b13, fr13, hb13, hf13, v13, n13⟩ := initWriteConstCode_exec
    (off := offP + 58) (val := keyBits U) b12 hL fr12 hb12 hf12 (f_const _ (by omega)) fkb
    (by omega)
  obtain ⟨x14, e14, b14, fr14, hb14, hf14, v14, n14⟩ := initWriteConstCode_exec
    (off := offP + 59) (val := valBits V) b13 hL fr13 hb13 hf13 (f_const _ (by omega)) fvb
    (by omega)
  obtain ⟨y, e15, by_b, fry, hby, hfy, vy, ny⟩ := initWriteConstCode_exec
    (off := offP + 60) (val := 0) b14 hL fr14 hb14 hf14 (f_const _ (by omega))
    (fits_zero w) (by omega)
  have hex : RDemonicExec w L_peak (initSmallBCode offP w (valBits V) (keyBits U)) x 33 (· = y) :=
    (e8.seq_eq <| e9.seq_eq <| e10.seq_eq <| e11.seq_eq <| e12.seq_eq <| e13.seq_eq <|
      e14.seq_eq e15).mono (by omega) (fun _ h => h)
  have ne_add (k1 k2 : ℕ) (hk : k1 ≠ k2) : base + offP + k1 ≠ base + (offP + k2) := by omega
  refine ⟨y, hex, by_b, fry, hby, hfy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun addr ha => ?_⟩
  · rw [ny _ (ne_add 53 60 (by decide)), n14 _ (ne_add 53 59 (by decide)),
      n13 _ (ne_add 53 58 (by decide)), n12 _ (ne_add 53 57 (by decide)),
      n11 _ (ne_add 53 56 (by decide)), n10 _ (ne_add 53 55 (by decide)),
      n9 _ (ne_add 53 54 (by decide)), show base + offP + 53 = base + (offP + 53) by omega, v8]
  · rw [ny _ (ne_add 54 60 (by decide)), n14 _ (ne_add 54 59 (by decide)),
      n13 _ (ne_add 54 58 (by decide)), n12 _ (ne_add 54 57 (by decide)),
      n11 _ (ne_add 54 56 (by decide)), n10 _ (ne_add 54 55 (by decide)),
      show base + offP + 54 = base + (offP + 54) by omega, v9]
  · rw [ny _ (ne_add 55 60 (by decide)), n14 _ (ne_add 55 59 (by decide)),
      n13 _ (ne_add 55 58 (by decide)), n12 _ (ne_add 55 57 (by decide)),
      n11 _ (ne_add 55 56 (by decide)), show base + offP + 55 = base + (offP + 55) by omega, v10]
  · rw [ny _ (ne_add 56 60 (by decide)), n14 _ (ne_add 56 59 (by decide)),
      n13 _ (ne_add 56 58 (by decide)), n12 _ (ne_add 56 57 (by decide)),
      show base + offP + 56 = base + (offP + 56) by omega, v11]
  · rw [ny _ (ne_add 57 60 (by decide)), n14 _ (ne_add 57 59 (by decide)),
      n13 _ (ne_add 57 58 (by decide)), show base + offP + 57 = base + (offP + 57) by omega, v12]
  · rw [ny _ (ne_add 58 60 (by decide)), n14 _ (ne_add 58 59 (by decide)),
      show base + offP + 58 = base + (offP + 58) by omega, v13]
  · rw [ny _ (ne_add 59 60 (by decide)), show base + offP + 59 = base + (offP + 59) by omega, v14]
  · rw [show base + offP + 60 = base + (offP + 60) by omega, vy]
  · have hne_out : ∀ k, 53 ≤ k → k < 61 → addr ≠ base + (offP + k) := fun k hlo hhi => by
      clear *- ha hlo hhi; omega
    rw [ny addr (hne_out 60 (by decide) (by decide)),
      n14 addr (hne_out 59 (by decide) (by decide)),
      n13 addr (hne_out 58 (by decide) (by decide)),
      n12 addr (hne_out 57 (by decide) (by decide)),
      n11 addr (hne_out 56 (by decide) (by decide)),
      n10 addr (hne_out 55 (by decide) (by decide)),
      n9 addr (hne_out 54 (by decide) (by decide)),
      n8 addr (hne_out 53 (by decide) (by decide))]

private theorem initSmallConstCode_exec {U V w L_peak base offP offM : ℕ} {x : RData rWhp}
    (hw11 : 11 ≤ w) (hoP : offP = hdrPBase0 ∨ offP = hdrPBase1)
    (hoM : offM = hdrSmallMeta0 ∨ offM = hdrSmallMeta1)
    (fvb : Fits w (valBits V)) (fkb : Fits w (keyBits U))
    (hx : x.Bounded w) (hL : base + 194 ≤ L_peak) (hx_fr : x.frontier = base + 194)
    (hbase : x.regs mBaseWhp = base) (hfr : x.regs mFrWhp = base + 194) :
    ∃ y : RData rWhp,
      RDemonicExec w L_peak (initSmallConstCode offP offM w (valBits V) (keyBits U)) x 64 (· = y) ∧
      y.Bounded w ∧
      y.frontier = base + 194 ∧
      y.regs mBaseWhp = base ∧
      y.regs mFrWhp = base + 194 ∧
      SmallEpochLayout.ParamTable
        ⟨base + offM, U, V, directSlotIo w (valBits V) base (base + 192) (keyBits U) 0⟩
        (base + offP) y.mem ∧
      (∀ addr, ¬(base + offP ≤ addr ∧ addr < base + offP + 61) → y.mem addr = x.mem addr) := by
  obtain ⟨xm, ea, bm, frm, hbm, hfm, w0, w1, w48, w49, w50, w51, w52, na⟩ :=
    initSmallACode_exec hw11 hoP hoM fkb hx hL hx_fr hbase hfr
  obtain ⟨y, eb, by_b, fry, hby, hfy, w53, w54, w55, w56, w57, w58, w59, w60, nb⟩ :=
    initSmallBCode_exec hw11 hoP fvb fkb bm hL frm hbm hfm
  have hlow (k : ℕ) (hk : k < 53) :
      ¬(base + offP + 53 ≤ base + offP + k ∧ base + offP + k < base + offP + 61) := by
    clear *- hk; omega
  refine ⟨y, (ea.seq_eq eb).mono (by decide) (fun _ h => h), by_b, fry, hby, hfy, ?_,
    fun addr ha =>
      (nb addr (by clear *- ha; omega)).trans (na addr (by clear *- ha; omega))⟩
  unfold SmallEpochLayout.ParamTable directSlotIo
  dsimp only
  exact ⟨(nb _ (by clear *-; omega)).trans w0, (nb _ (hlow 1 (by decide))).trans w1,
    (nb _ (hlow 48 (by decide))).trans w48, (nb _ (hlow 49 (by decide))).trans w49,
    (nb _ (hlow 50 (by decide))).trans w50, (nb _ (hlow 51 (by decide))).trans w51,
    (nb _ (hlow 52 (by decide))).trans w52, w53, w54, w55, w56, w57, w58, w59, w60⟩

private theorem initHdrACode_exec {c U V w L_peak base : ℕ} {x : RData rWhp}
    (hw11 : 11 ≤ w) (fU : Fits w (U - 1)) (fV : Fits w (V - 1))
    (fkb : Fits w (keyBits U)) (fvb : Fits w (valBits V))
    (fth : Fits w (if whpThreshold c ≤ U then whpThreshold c else 0))
    (fct : Fits w (if whpThreshold c ≤ U then cTabWhp c else 0))
    (hx : x.Bounded w) (hL : base + 194 ≤ L_peak) (hx_fr : x.frontier = base + 194)
    (hbase : x.regs mBaseWhp = base) (hfr : x.regs mFrWhp = base + 194) :
    ∃ y : RData rWhp,
      RDemonicExec w L_peak (initHdrACode c U V w) x 28 (· = y) ∧
      y.Bounded w ∧
      y.frontier = base + 194 ∧
      y.regs mBaseWhp = base ∧
      y.regs mFrWhp = base + 194 ∧
      y.mem (base + hdrU1) = U - 1 ∧
      y.mem (base + hdrV1) = V - 1 ∧
      y.mem (base + hdrW) = w ∧
      y.mem (base + hdrKeyBits) = keyBits U ∧
      y.mem (base + hdrValBits) = valBits V ∧
      y.mem (base + hdrThresh) = (if whpThreshold c ≤ U then whpThreshold c else 0) ∧
      y.mem (base + hdrCTab) = (if whpThreshold c ≤ U then cTabWhp c else 0) ∧
      (∀ addr, ¬(base ≤ addr ∧ addr < base + 7) → y.mem addr = x.mem addr) := by
  have h2048 : 2048 ≤ 2 ^ w :=
    (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
  have f_const : ∀ k ≤ 256, Fits w k := fun k hk => by unfold Fits; omega
  have fw : Fits w w := Nat.lt_two_pow_self
  obtain ⟨s1, e1, b1, fr1, hb1, hf1, v1, n1⟩ := initWriteConstCode_exec
    (off := hdrU1) (val := U - 1) hx hL hx_fr hbase hfr
    (f_const _ (by unfold hdrU1; omega)) fU (by unfold hdrU1; omega)
  obtain ⟨s2, e2, b2, fr2, hb2, hf2, v2, n2⟩ := initWriteConstCode_exec
    (off := hdrV1) (val := V - 1) b1 hL fr1 hb1 hf1
    (f_const _ (by unfold hdrV1; omega)) fV (by unfold hdrV1; omega)
  obtain ⟨s3, e3, b3, fr3, hb3, hf3, v3, n3⟩ := initWriteConstCode_exec
    (off := hdrW) (val := w) b2 hL fr2 hb2 hf2
    (f_const _ (by unfold hdrW; omega)) fw (by unfold hdrW; omega)
  obtain ⟨s4, e4, b4, fr4, hb4, hf4, v4, n4⟩ := initWriteConstCode_exec
    (off := hdrKeyBits) (val := keyBits U) b3 hL fr3 hb3 hf3
    (f_const _ (by unfold hdrKeyBits; omega)) fkb (by unfold hdrKeyBits; omega)
  obtain ⟨s5, e5, b5, fr5, hb5, hf5, v5, n5⟩ := initWriteConstCode_exec
    (off := hdrValBits) (val := valBits V) b4 hL fr4 hb4 hf4
    (f_const _ (by unfold hdrValBits; omega)) fvb (by unfold hdrValBits; omega)
  obtain ⟨s6, e6, b6, fr6, hb6, hf6, v6, n6⟩ := initWriteConstCode_exec
    (off := hdrThresh) (val := if whpThreshold c ≤ U then whpThreshold c else 0)
    b5 hL fr5 hb5 hf5 (f_const _ (by unfold hdrThresh; omega)) fth (by unfold hdrThresh; omega)
  obtain ⟨y, e7, by_b, fry, hby, hfy, v7, n7⟩ := initWriteConstCode_exec
    (off := hdrCTab) (val := if whpThreshold c ≤ U then cTabWhp c else 0)
    b6 hL fr6 hb6 hf6 (f_const _ (by unfold hdrCTab; omega)) fct (by unfold hdrCTab; omega)
  have hex : RDemonicExec w L_peak (initHdrACode c U V w) x 28 (· = y) :=
    (e1.seq_eq <| e2.seq_eq <| e3.seq_eq <| e4.seq_eq <| e5.seq_eq <|
      e6.seq_eq e7).mono (by decide) (fun _ h => h)
  have b_ne {a b : ℕ} (h : a ≠ b) : base + a ≠ base + b := fun heq => h (Nat.add_left_cancel heq)
  refine ⟨y, hex, by_b, fry, hby, hfy, ?_, ?_, ?_, ?_, ?_, ?_, v7, fun addr ha => ?_⟩
  · rw [n7 _ (b_ne (by decide)), n6 _ (b_ne (by decide)), n5 _ (b_ne (by decide)),
      n4 _ (b_ne (by decide)), n3 _ (b_ne (by decide)), n2 _ (b_ne (by decide)), v1]
  · rw [n7 _ (b_ne (by decide)), n6 _ (b_ne (by decide)), n5 _ (b_ne (by decide)),
      n4 _ (b_ne (by decide)), n3 _ (b_ne (by decide)), v2]
  · rw [n7 _ (b_ne (by decide)), n6 _ (b_ne (by decide)), n5 _ (b_ne (by decide)),
      n4 _ (b_ne (by decide)), v3]
  · rw [n7 _ (b_ne (by decide)), n6 _ (b_ne (by decide)), n5 _ (b_ne (by decide)), v4]
  · rw [n7 _ (b_ne (by decide)), n6 _ (b_ne (by decide)), v5]
  · rw [n7 _ (b_ne (by decide)), v6]
  · have hne_h : ∀ k < 7, addr ≠ base + k := fun k hk => by clear *- ha hk; omega
    rw [n7 addr (hne_h hdrCTab (by decide)), n6 addr (hne_h hdrThresh (by decide)),
      n5 addr (hne_h hdrValBits (by decide)), n4 addr (hne_h hdrKeyBits (by decide)),
      n3 addr (hne_h hdrW (by decide)), n2 addr (hne_h hdrV1 (by decide)),
      n1 addr (hne_h hdrU1 (by decide))]

private theorem initHdrBCode_exec {c U w L_peak base : ℕ} {x : RData rWhp}
    (hw11 : 11 ≤ w) (fkb : Fits w (keyBits U))
    (fdt : Fits w (if whpThreshold c ≤ U then dTabWhp c else 0))
    (frw : Fits w (redWidthWhp U))
    (fce : Fits w (if whpThreshold c ≤ U then cEff c else 0))
    (hx : x.Bounded w) (hL : base + 194 ≤ L_peak) (hx_fr : x.frontier = base + 194)
    (hbase : x.regs mBaseWhp = base) (hfr : x.regs mFrWhp = base + 194) :
    ∃ y : RData rWhp,
      RDemonicExec w L_peak (initHdrBCode c U) x 30 (· = y) ∧
      y.Bounded w ∧
      y.frontier = base + 194 ∧
      y.regs mBaseWhp = base ∧
      y.regs mFrWhp = base + 194 ∧
      y.mem (base + hdrDTab) = (if whpThreshold c ≤ U then dTabWhp c else 0) ∧
      y.mem (base + hdrRedW) = redWidthWhp U ∧
      y.mem (base + hdrCEff) = (if whpThreshold c ≤ U then cEff c else 0) ∧
      y.mem (base + hdrItemLo) = base + 192 ∧
      y.mem (base + hdrItemHi) = base + 192 ∧
      y.mem (base + hdrQLo) = keyBits U ∧
      y.mem (base + hdrQHi) = keyBits U ∧
      (∀ addr, ¬(base + 7 ≤ addr ∧ addr < base + 10 ∨ base + 22 ≤ addr ∧ addr < base + 26) →
        y.mem addr = x.mem addr) := by
  have h2048 : 2048 ≤ 2 ^ w :=
    (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
  have f_const : ∀ k ≤ 256, Fits w k := fun k hk => by unfold Fits; omega
  obtain ⟨s8, e8, b8, fr8, hb8, hf8, v8, n8⟩ := initWriteConstCode_exec
    (off := hdrDTab) (val := if whpThreshold c ≤ U then dTabWhp c else 0)
    hx hL hx_fr hbase hfr (f_const _ (by unfold hdrDTab; omega)) fdt (by unfold hdrDTab; omega)
  obtain ⟨s9, e9, b9, fr9, hb9, hf9, v9, n9⟩ := initWriteConstCode_exec
    (off := hdrRedW) (val := redWidthWhp U) b8 hL fr8 hb8 hf8
    (f_const _ (by unfold hdrRedW; omega)) frw (by unfold hdrRedW; omega)
  obtain ⟨s10, e10, b10, fr10, hb10, hf10, v10, n10⟩ := initWriteConstCode_exec
    (off := hdrCEff) (val := if whpThreshold c ≤ U then cEff c else 0)
    b9 hL fr9 hb9 hf9 (f_const _ (by unfold hdrCEff; omega)) fce (by unfold hdrCEff; omega)
  obtain ⟨s11, e11, b11, fr11, hb11, hf11, v11, n11⟩ := initWriteAddConstCode_exec
    (off := hdrItemLo) (addOff := 192) b10 hL fr10 hb10 hf10
    (f_const _ (by unfold hdrItemLo; omega)) (f_const _ (by omega))
    (by unfold hdrItemLo; omega) (by omega)
  obtain ⟨s12, e12, b12, fr12, hb12, hf12, v12, n12⟩ := initWriteAddConstCode_exec
    (off := hdrItemHi) (addOff := 192) b11 hL fr11 hb11 hf11
    (f_const _ (by unfold hdrItemHi; omega)) (f_const _ (by omega))
    (by unfold hdrItemHi; omega) (by omega)
  obtain ⟨s13, e13, b13, fr13, hb13, hf13, v13, n13⟩ := initWriteConstCode_exec
    (off := hdrQLo) (val := keyBits U) b12 hL fr12 hb12 hf12
    (f_const _ (by unfold hdrQLo; omega)) fkb (by unfold hdrQLo; omega)
  obtain ⟨y, e14, by_b, fry, hby, hfy, v14, n14⟩ := initWriteConstCode_exec
    (off := hdrQHi) (val := keyBits U) b13 hL fr13 hb13 hf13
    (f_const _ (by unfold hdrQHi; omega)) fkb (by unfold hdrQHi; omega)
  have hex : RDemonicExec w L_peak (initHdrBCode c U) x 30 (· = y) :=
    (e8.seq_eq <| e9.seq_eq <| e10.seq_eq <| e11.seq_eq <| e12.seq_eq <|
      e13.seq_eq e14).mono (by decide) (fun _ h => h)
  have b_ne {a b : ℕ} (h : a ≠ b) : base + a ≠ base + b := fun heq => h (Nat.add_left_cancel heq)
  refine ⟨y, hex, by_b, fry, hby, hfy, ?_, ?_, ?_, ?_, ?_, ?_, v14, fun addr ha => ?_⟩
  · rw [n14 _ (b_ne (by decide)), n13 _ (b_ne (by decide)), n12 _ (b_ne (by decide)),
      n11 _ (b_ne (by decide)), n10 _ (b_ne (by decide)), n9 _ (b_ne (by decide)), v8]
  · rw [n14 _ (b_ne (by decide)), n13 _ (b_ne (by decide)), n12 _ (b_ne (by decide)),
      n11 _ (b_ne (by decide)), n10 _ (b_ne (by decide)), v9]
  · rw [n14 _ (b_ne (by decide)), n13 _ (b_ne (by decide)), n12 _ (b_ne (by decide)),
      n11 _ (b_ne (by decide)), v10]
  · rw [n14 _ (b_ne (by decide)), n13 _ (b_ne (by decide)), n12 _ (b_ne (by decide)), v11]
  · rw [n14 _ (b_ne (by decide)), n13 _ (b_ne (by decide)), v12]
  · rw [n14 _ (b_ne (by decide)), v13]
  · have hne_h : ∀ k, (7 ≤ k ∧ k < 10 ∨ 22 ≤ k ∧ k < 26) → addr ≠ base + k := fun k hk => by
      clear *- ha hk; omega
    rw [n14 addr (hne_h hdrQHi (by decide)), n13 addr (hne_h hdrQLo (by decide)),
      n12 addr (hne_h hdrItemHi (by decide)), n11 addr (hne_h hdrItemLo (by decide)),
      n10 addr (hne_h hdrCEff (by decide)), n9 addr (hne_h hdrRedW (by decide)),
      n8 addr (hne_h hdrDTab (by decide))]

/-- Deterministic `RDemonicExec` specification of `initCodeWhp c U V w`: runs in
`initStepsWhp = 1164` instructions within `base + spaceBoundWhp c V w (Dictionary.empty U)`,
establishes `DualRep` for `Dictionary.empty U` and `DualLatent.empty c U V`, and preserves caller
memory `[0, base)`. -/
theorem initCodeWhp_demonicExec {c U V w base : ℕ} {x₀ : RData rWhp}
    (hw11 : 11 ≤ w) (hU0 : 0 < U) (hUw : Fits w U) (hV0 : 0 < V) (hVw : V ≤ 2 ^ w)
    (hx₀ : x₀.Bounded w) (hfr₀ : x₀.frontier = base)
    (hfit₀ : Fits w (base + spaceBoundWhp c V w (Dictionary.empty U))) :
    ∃ y : RData rWhp,
      RDemonicExec w (base + spaceBoundWhp c V w (Dictionary.empty U))
        (initCodeWhp c U V w) x₀ initStepsWhp (· = y) ∧
      DualRep c U V w base (Dictionary.empty U) (DualLatent.empty c U V) y ∧
      (∀ addr < base, y.mem addr = x₀.mem addr) := by
  set L_peak := base + spaceBoundWhp c V w (Dictionary.empty U)
  obtain ⟨h194_le, hpad0_le⟩ := dualPaddedWords_zero_le_spaceBoundWhp c U V w
  have hL194 : base + 194 ≤ L_peak := Nat.add_le_add_left h194_le base
  have h2048 : 2048 ≤ 2 ^ w :=
    (by decide : 2048 = 2 ^ 11) ▸ Nat.pow_le_pow_right (by decide) hw11
  have f_const : ∀ k ≤ 256, Fits w k := fun k hk => by unfold Fits; omega
  have hfit194 : Fits w (base + 194) := hfit₀.of_le hL194
  have hpad_fits : base + dualPaddedWords c U V w 0 0 0 < 2 ^ w :=
    lt_of_le_of_lt (Nat.add_le_add_left hpad0_le base) hfit₀
  obtain ⟨fU, fV, fkb, fvb, fth, fct, fdt, frw, fce⟩ :
      Fits w (U - 1) ∧ Fits w (V - 1) ∧ Fits w (keyBits U) ∧ Fits w (valBits V) ∧
      Fits w (if whpThreshold c ≤ U then whpThreshold c else 0) ∧
      Fits w (if whpThreshold c ≤ U then cTabWhp c else 0) ∧
      Fits w (if whpThreshold c ≤ U then dTabWhp c else 0) ∧
      Fits w (redWidthWhp U) ∧
      Fits w (if whpThreshold c ≤ U then cEff c else 0) := by
    let ms0 : Memory.State := { mem := x₀.mem, frontier := base + 194 }
    have hwf0 : Memory.WellFormed w ms0 := ⟨hfit194, fun a => hx₀.mem_fits a⟩
    have h_ref :=
      (dualStateInv_init (c := c) (U := U) (V := V) hwf0 hw11 hU0 hUw hV0 hVw rfl
        (fun off _ => hx₀.zero_above (by rw [hfr₀]; exact Nat.le_add_right base off))
        hpad_fits).2.2.2
    exact ⟨h_ref.hdr.1 ▸ h_ref.wf.2 (base + hdrU1),
      h_ref.hdr.2.1 ▸ h_ref.wf.2 (base + hdrV1),
      h_ref.hdr.2.2.2.1 ▸ h_ref.wf.2 (base + hdrKeyBits),
      h_ref.hdr.2.2.2.2.1 ▸ h_ref.wf.2 (base + hdrValBits),
      h_ref.hdr.2.2.2.2.2.1 ▸ h_ref.wf.2 (base + hdrThresh),
      h_ref.hdr.2.2.2.2.2.2.1 ▸ h_ref.wf.2 (base + hdrCTab),
      h_ref.hdr.2.2.2.2.2.2.2.1 ▸ h_ref.wf.2 (base + hdrDTab),
      h_ref.hdr.2.2.2.2.2.2.2.2.1 ▸ h_ref.wf.2 (base + hdrRedW),
      h_ref.hdr.2.2.2.2.2.2.2.2.2 ▸ h_ref.wf.2 (base + hdrCEff)⟩
  have hzero0 : ∀ off < 194, x₀.mem (base + off) = 0 := fun off _ =>
    hx₀.zero_above (by rw [hfr₀]; exact Nat.le_add_right base off)
  have eg1 := RDemonicExec.const (B := .exact) (w := w) (L_peak := L_peak)
    (d := rK) (v := 194) (x := x₀) (by rw [hfr₀]; clear *- hL194; omega) (f_const 194 (by decide))
  set z1 := x₀.set rK 194
  have hz1b : z1.Bounded w := hx₀.set (f_const 194 (by decide))
  have hz1_k : z1.regs rK = 194 := by simp [z1, RData.set]
  have hz1_fr : z1.frontier = base := hfr₀
  have egz := growZeroCode_exec (w := w) (L_peak := L_peak)
    (count := rK) (result := mBaseWhp) (cur := rCur) (idx := rIdx) (zero := rZero) (one := rOne)
    hz1b whpGrowBase_nodup (f_const 1 (by decide))
    (by rw [hz1_fr, hz1_k]; exact hL194) (by rw [hz1_fr, hz1_k]; exact hfit194)
  set z2 := growZeroPost rK mBaseWhp rCur rIdx rZero rOne z1
  have hz2b : z2.Bounded w :=
    whpGrowZeroPost_bounded hz1b (f_const 1 (by decide)) (by rw [hz1_fr, hz1_k]; exact hfit194)
  have hz2_fr : z2.frontier = base + 194 := by simp [z2, growZeroPost, hz1_fr, hz1_k]
  have hz2_base : z2.regs mBaseWhp = base := by simp [z2, growZeroPost, hz1_fr, hz1_k]
  have hz2_k : z2.regs rK = 194 := by simp [z2, growZeroPost, hz1_k]
  have eg3 : RDemonicExec w L_peak (.op (.exactBin .add mFrWhp mBaseWhp rK)) z2 1
      (· = z2.set mFrWhp (base + 194)) :=
    RDemonicExec.exactBin (x := z2) (hz2_fr ▸ hL194)
      (by simp [BinOp.evalExact, hz2_base, hz2_k]) hfit194
  set z3 := z2.set mFrWhp (base + 194)
  have hz3b : z3.Bounded w := hz2b.set hfit194
  have hz3_fr : z3.frontier = base + 194 := hz2_fr
  have hz3_base : z3.regs mBaseWhp = base := by simp [z3, RData.set, hz2_base]
  have hz3_mfr : z3.regs mFrWhp = base + 194 := by simp [z3, RData.set]
  have hz3_mem : z3.mem = x₀.mem := rfl
  obtain ⟨sA, e_ha, b_ha, fr_ha, hb_ha, hf_ha, v1, v2, v3, v4, v5, v6, v7, outA⟩ :=
    initHdrACode_exec hw11 fU fV fkb fvb fth fct hz3b hL194 hz3_fr hz3_base hz3_mfr
  obtain ⟨s14, e_hb, b_14, fr_14, hb_14, hf_14, v8, v9, v10, v11, v12, v13, v14, outB⟩ :=
    initHdrBCode_exec hw11 fkb fdt frw fce b_ha hL194 fr_ha hb_ha hf_ha
  obtain ⟨s15, e_sm0, b_15, fr_15, hb_15, hf_15, hpt0_s15, hout_sm0⟩ := initSmallConstCode_exec
    (U := U) (V := V) hw11 (Or.inl rfl) (Or.inl rfl) fvb fkb b_14 hL194 fr_14 hb_14 hf_14
  obtain ⟨y, e_sm1, by_b, fry, hby, hfy, _, hout_sm1⟩ := initSmallConstCode_exec
    (U := U) (V := V) hw11 (Or.inr rfl) (Or.inr rfl) fvb fkb b_15 hL194 fr_15 hb_15 hf_15
  have hex_all : RDemonicExec w L_peak (initCodeWhp c U V w) x₀ initStepsWhp (· = y) :=
    (eg1.seq_eq <| egz.seq_eq <| eg3.seq_eq <|
      e_ha.seq_eq <| e_hb.seq_eq <| e_sm0.seq_eq e_sm1).mono
      (by rw [hz1_k]; unfold initStepsWhp; decide) (fun _ h => h)
  have hlow_y : ∀ off < 64, y.mem (base + off) = s14.mem (base + off) := fun off hoff =>
    (hout_sm1 (base + off) (by clear *- hoff; unfold hdrPBase1; omega)).trans
      (hout_sm0 (base + off) (by clear *- hoff; unfold hdrPBase0; omega))
  have hs14_out : ∀ addr,
      ¬(base ≤ addr ∧ addr < base + 10 ∨ base + 22 ≤ addr ∧ addr < base + 26) →
      s14.mem addr = x₀.mem addr := fun addr ha =>
    (outB addr (by clear *- ha; omega)).trans
      ((outA addr (by clear *- ha; omega)).trans (congrFun hz3_mem addr))
  have hbelow : ∀ addr < base, y.mem addr = x₀.mem addr := fun addr hlt =>
    (hout_sm1 addr (by clear *- hlt; unfold hdrPBase1; omega)).trans
      ((hout_sm0 addr (by clear *- hlt; unfold hdrPBase0; omega)).trans
        (hs14_out addr (by clear *- hlt; omega)))
  have hhdr_y : RootStaticHeader c U V w base y.mem := by
    have hs : ∀ off < 10, y.mem (base + off) = s14.mem (base + off) :=
      fun off h => hlow_y off (by clear *- h; omega)
    have hb_low : ∀ off < 7, s14.mem (base + off) = sA.mem (base + off) :=
      fun off h => outB (base + off) (by clear *- h; omega)
    unfold RootStaticHeader
    exact ⟨(hs hdrU1 (by decide)).trans ((hb_low hdrU1 (by decide)).trans v1),
      (hs hdrV1 (by decide)).trans ((hb_low hdrV1 (by decide)).trans v2),
      (hs hdrW (by decide)).trans ((hb_low hdrW (by decide)).trans v3),
      (hs hdrKeyBits (by decide)).trans ((hb_low hdrKeyBits (by decide)).trans v4),
      (hs hdrValBits (by decide)).trans ((hb_low hdrValBits (by decide)).trans v5),
      (hs hdrThresh (by decide)).trans ((hb_low hdrThresh (by decide)).trans v6),
      (hs hdrCTab (by decide)).trans ((hb_low hdrCTab (by decide)).trans v7),
      (hs hdrDTab (by decide)).trans v8,
      (hs hdrRedW (by decide)).trans v9,
      (hs hdrCEff (by decide)).trans v10⟩
  have hz_mid : ∀ off, (10 ≤ off ∧ off < 22 ∨ 26 ≤ off ∧ off < 64) → y.mem (base + off) = 0 :=
    fun off hoff => by
      rw [hlow_y off (by clear *- hoff; omega), hs14_out (base + off) (by clear *- hoff; omega)]
      exact hzero0 off (by clear *- hoff; omega)
  have hib_y : y.mem (base + hdrItemLo) = base + 192 ∧
      y.mem (base + hdrItemHi) = base + 192 ∧
      y.mem (base + hdrQLo) = keyBits U ∧
      y.mem (base + hdrQHi) = keyBits U :=
    ⟨(hlow_y hdrItemLo (by decide)).trans v11,
     (hlow_y hdrItemHi (by decide)).trans v12,
     (hlow_y hdrQLo (by decide)).trans v13,
     (hlow_y hdrQHi (by decide)).trans v14⟩
  have hpt0_y : SmallEpochLayout.ParamTable
      ⟨base + hdrSmallMeta0, U, V, directSlotIo w (valBits V) base (base + 192) (keyBits U) 0⟩
      (base + hdrPBase0) y.mem :=
    hpt0_s15.congr fun a h1 h2 =>
      hout_sm1 a (by clear *- h1 h2; unfold hdrPBase0 hdrPBase1 at *; omega)
  have hpw0 : pairStreamWords 0 (keyBits U) (valBits V) w = 2 := by
    unfold pairStreamWords packedWords
    simp [Nat.div_eq_of_lt (show w - 1 < w by clear *- hw11; omega)]
  have hm0_eq : epochMetaWordsWhp c w 0 = 0 := epochMetaWordsWhp_zero_eq c w
  have hdom_empty : (Dictionary.dom (Dictionary.empty U)).card = 0 := by simp
  have hnL : y.mem (base + hdrLive) = 0 := hz_mid 10 (Or.inl ⟨by decide, by decide⟩)
  have hph : y.mem (base + hdrPhase) = 0 := hz_mid 11 (Or.inl ⟨by decide, by decide⟩)
  have hstg : y.mem (base + hdrStage) = 0 := hz_mid 12 (Or.inl ⟨by decide, by decide⟩)
  have hnS : y.mem (base + hdrNSrc) = 0 := hz_mid 13 (Or.inl ⟨by decide, by decide⟩)
  have hnD : y.mem (base + hdrNDst) = 0 := hz_mid 14 (Or.inl ⟨by decide, by decide⟩)
  have hmS : y.mem (base + hdrMSrc) = 0 := hz_mid 19 (Or.inl ⟨by decide, by decide⟩)
  have hmD : y.mem (base + hdrMDst) = 0 := hz_mid 20 (Or.inl ⟨by decide, by decide⟩)
  have hsm0_0 : y.mem (base + hdrSmallMeta0) = 0 := hz_mid 48 (Or.inr ⟨by decide, by decide⟩)
  have hsm0_1 : y.mem (base + hdrSmallMeta0 + 1) = 0 := hz_mid 49 (Or.inr ⟨by decide, by decide⟩)
  have hkb_le : keyBits U ≤ w := Nat.clog_le_of_le_pow hUw.le
  have hvb_le : valBits V ≤ w := Nat.clog_le_of_le_pow hVw
  set io0 := directSlotIo w (valBits V) base (base + 192) (keyBits U) 0
  have hsl0_y : EpochSlotInv c U V w y.frontier (base + hdrPBase0) (base + hdrSmallMeta0)
      io0 0 false (SlotLatent.emptySmall c U V) y.mem := by
    unfold EpochSlotInv; dsimp only [SlotLatent.emptySmall, ↓reduceIte]
    refine ⟨by clear *- hU0 hw11; omega, by rw [fry]; clear *-; unfold hdrPBase0; omega,
      { io_valid := by
          unfold SlotIoLayout.Valid; dsimp only [io0, directSlotIo, ↓reduceIte]
          rw [fry, hpw0]
          exact ⟨by clear *- hw11; omega, rfl, hkb_le, hvb_le, Nat.two_pow_pos w, le_rfl⟩
        w_eq := rfl, qBits_eq := rfl, vBits_eq := rfl
        hdr_frontier := by dsimp only; rw [fry]; clear *-; unfold hdrSmallMeta0; omega
        disjoint_hdr := fun addr hmb hia => by
          simp only [io0, directSlotIo, SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr,
            hdrSmallMeta0, ↓reduceIte] at hmb hia
          clear *- hmb hia
          rcases hmb with rfl | rfl <;> omega },
      hpt0_y,
      fun a h1 h2 ha => by
        simp only [SmallEpochLayout.OwnsAddr, SlotIoLayout.OwnsAddr, PageArenaLayout.OwnsItemAddr,
          io0, directSlotIo, hdrPBase0, hdrSmallMeta0, ↓reduceIte] at h1 h2 ha
        clear *- h1 h2 ha; omega,
      hsm0_0, by simp only [io0, directSlotIo, hsm0_1]; decide,
      by
        unfold SlotIoLayout.StateInv
        simp only [io0, directSlotIo, ↓reduceIte, hsm0_1, le_rfl, true_and]
        exact Or.inl trivial,
      ⟨fun p hp => by rw [hsm0_1] at hp; clear *- hp; omega,
       fun p hp => by rw [hsm0_1] at hp; clear *- hp; omega,
       fun u v => ⟨fun h => (by cases h), fun ⟨p, hp, _⟩ => by
         rw [hsm0_1] at hp; clear *- hp; omega⟩⟩⟩
  have hinv_y :
      DualStateInv c U V w base (Dictionary.empty U) (DualLatent.empty c U V) (rMemState y) :=
    { hw11 := hw11, U_pos := hU0, U_lt := hUw, V_pos := hV0, V_le := hVw
      wf := ⟨by_b.2.1, fun a => by_b.mem_fits a⟩
      base_fr := by dsimp only [rMemState]; rw [fry]; clear *-; omega
      hdr := hhdr_y
      live_eq := hnL.trans hdom_empty.symm
      live_le := hdom_empty ▸ Nat.zero_le U
      ph_le := by dsimp only [rMemState]; rw [hph]; decide
      stg_le := by dsimp only [rMemState]; rw [hstg]; decide
      mSrc_eq := by dsimp only [rMemState]; rw [hmS, hnS, hm0_eq]
      cache_src := fun h => by dsimp only [rMemState] at h; rw [hnS] at h; clear *- h; omega
      nSrc_bounds := Or.inl hnS
      sched := by
        dsimp only [rMemState]; rw [ite_eq_left hph]
        exact
          { stg_zero := hstg, nDst_zero := hnD, mDst_zero := hmD
            ibLo_eq := by dsimp only; rw [hib_y.1, hmS]
            ibHi_eq := hib_y.2.1.trans hib_y.1.symm
            qLo_eq := by
              change y.mem (base + hdrQLo) =
                if y.mem (base + hdrNSrc) = 0 then keyBits U
                else quotBitsWhp U (y.mem (base + hdrNSrc))
              rw [hib_y.2.2.1, hnS, ite_eq_left rfl]
            qHi_eq := hib_y.2.2.2.trans hib_y.2.2.1.symm
            elapsed_zero := rfl
            safe_fr := by
              dsimp only; rw [ite_eq_right Bool.false_ne_true, hdom_empty, hnS, hib_y.1,
                hib_y.2.2.1]
              exact ⟨dualIdleSafe_empty c U, fun _ => whpThreshold_pos c, by rw [fry, hpw0]⟩
            ops_evs := fun h => by dsimp only at h; rw [hnS] at h; clear *- h; omega }
      pad_fits := by dsimp only [rMemState]; rw [hnS, ite_eq_left hph, hdom_empty]; exact hpad_fits
      ph1_inv := fun h => by dsimp only [rMemState] at h; rw [hph] at h; cases h
      ph3_inv := fun h => by dsimp only [rMemState] at h; rw [hph] at h; cases h
      ph4_inv := fun h => by dsimp only [rMemState] at h; rw [hph] at h; cases h
      pDst_pre := fun h _ _ => by dsimp only [rMemState] at h; rw [hph] at h; clear *- h; omega
      ph5_inv := fun h => by dsimp only [rMemState] at h; rw [hph] at h; cases h
      ph6_inv := fun h => by dsimp only [rMemState] at h; rw [hph] at h; cases h
      ph7_inv := fun h => by dsimp only [rMemState] at h; rw [hph] at h; cases h
      ph8_inv := fun h => by dsimp only [rMemState] at h; rw [hph] at h; cases h
      ph9_inv := fun h => by dsimp only [rMemState] at h; rw [hph] at h; cases h
      ph10_inv := fun h => by dsimp only [rMemState] at h; rw [hph] at h; cases h
      sl_le7 := fun _ => by
        dsimp only [rMemState]; unfold dualCapSrc dualPSrc dualMbSrc
        rw [hstg, hnS, hph, hib_y.1, hib_y.2.1, hib_y.2.2.1, hib_y.2.2.2, hdom_empty]
        exact ⟨rfl, rfl, by simpa [activeSrcIo, DualLatent.empty, io0] using hsl0_y,
          fun h => absurd h (Nat.lt_irrefl 0)⟩
      sl_67 := fun h => by
        dsimp only [rMemState] at h; rw [hph] at h; rcases h with h | h <;> cases h
      sl_8 := fun h => by dsimp only [rMemState] at h; rw [hph] at h; cases h
      sl_ge9 := fun h => by dsimp only [rMemState] at h; rw [hph] at h; clear *- h; omega }
  exact ⟨y, hex_all, ⟨by_b, hby, hfy.trans fry.symm, hinv_y⟩, hbelow⟩

/-! ## Section 3: Peak-Space Bounds and Single-State `ExecRCodeSteps` Execution -/

/-- `dualPaddedWords` stays within `spaceBoundWhp` before and after any valid mutation. -/
theorem dualPaddedWords_step_le_peak {c U V w base opTag : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (h : DualStateInv c U V w base s_dict L s)
    (hop_nz : opTag ≠ 0) (u : Fin U) (v : Fin V) :
    let s_dict' :=
      if opTag = 1 then Function.update s_dict u (some v.val) else Function.update s_dict u none
    let nSrc := s.mem (base + hdrNSrc)
    let nDst := if s.mem (base + hdrPhase) = 0 then nSrc else s.mem (base + hdrNDst)
    dualPaddedWords c U V w nSrc nDst (Dictionary.dom s_dict).card ≤
      spaceBoundWhp c V w s_dict ∧
    dualPaddedWords c U V w nSrc nDst (Dictionary.dom s_dict').card ≤
      spaceBoundWhp c V w s_dict' := by
  dsimp only
  obtain ⟨hsrc0, hdst0⟩ := dualCoreInv_cap_safe h
  have hle0 := dualPaddedWords_le_succinctWords (V := V) (w := w) hsrc0 hdst0
  have hsetup := fgSetup_of_dualStateInv h hop_nz u v
  obtain ⟨_, _, _, hlo_s, hhi_s, hnU', _, _⟩ := hsetup.card_step
  set s_dict' :=
    if opTag = 1 then Function.update s_dict u (some v.val) else Function.update s_dict u none
  set nLive := (Dictionary.dom s_dict).card
  set nLive' := (Dictionary.dom s_dict').card
  have hsched := h.sched
  by_cases hp0 : s.mem (base + hdrPhase) = 0
  · rw [ite_eq_left hp0] at hsched hle0 ⊢
    obtain ⟨hidle, h0_lt, _⟩ := hsched.safe_fr
    have hno_or : dualTriggerCap c U (s.mem (base + hdrNSrc)) nLive 0 = none ∨
        s.mem (base + hdrNSrc) ≠ 0 := by
      by_cases hs0 : s.mem (base + hdrNSrc) = 0
      · refine Or.inl ?_
        have hlt := h0_lt hs0
        rw [hs0]; unfold dualTriggerCap; simp only [↓reduceIte]
        rw [ite_eq_right (fun hk => absurd hk.2 (Nat.not_le_of_gt hlt))]
      · exact Or.inr hs0
    have hpost := dualPostUpdateSafe_of_idle hidle hno_or ⟨hhi_s, hlo_s⟩ hnU'
    have hcap' := dualPostUpdateSafe_to_epochCapSafe hpost
    exact ⟨hle0, dualPaddedWords_le_succinctWords (V := V) (w := w) hcap' hcap'⟩
  · rw [ite_eq_right hp0] at hsched hle0 ⊢
    have hel2 := hsched.budget.2.2
    have har := active_rebuild_safe hsched.post_trig hsched.trig_cap
      (d := L.elapsed + 1)
      (by have hd := hsched.drift_hi; simp only [Bool.false_eq_true, ↓reduceIte] at hd; omega)
      (by have hd := hsched.drift_lo; simp only [Bool.false_eq_true, ↓reduceIte] at hd; omega)
      (by omega) hnU'
    exact ⟨hle0, dualPaddedWords_le_succinctWords (V := V) (w := w) har.2.1 har.2.2.1⟩

private theorem execRCodeSteps_seq_demonic {w L_peak n : ℕ} {c₁ c₂ : RCode .exact rWhp}
    {xa xb : RData rWhp} {μ : PMF (RCodeStepOutcome rWhp)}
    (hd : RDemonicExec w L_peak c₁ xa n (· = xb))
    (he : ExecRCodeSteps w c₂ xb μ L_peak) :
    ExecRCodeSteps w (.seq c₁ c₂) xa
      (μ.map fun z => ⟨z.data, n + z.steps, z.timed⟩) L_peak := by
  refine (ExecRCodeSteps.seq (ExecRCodeSteps.of_demonicExec hd)
    (μ₂ := fun _ => μ) fun z hz => ?_).congr_dist ?_
  · rw [PMF.mem_support_pure_iff] at hz; subst hz; exact he
  · rw [PMF.pure_bind]; rfl

private theorem opPrefixCode_exec {w L_peak base opTag u_val v_val : ℕ}
    {s : Memory.State} {x0 : RData rWhp}
    (hs_eq : rMemState x0 = s)
    (hw11 : 11 ≤ w) (hx0b : x0.Bounded w) (hL_x : s.frontier ≤ L_peak)
    (hx0_base : x0.regs mBaseWhp = base) (hx0_fr : x0.regs mFrWhp = s.frontier)
    (hx0_tag : x0.regs rTag = opTag) (hx0_key : x0.regs rKey = u_val)
    (hx0_val : x0.regs rVal = v_val)
    (hwf0 : Memory.WellFormed w s)
    (hpre_pg : PrepGrowPre w (((base, s.frontier), opTag), u_val) s)
    (hfr_prep : ((Memory.spec 0).clientState s
      (prepGrowProg (((base, s.frontier), opTag), u_val))).frontier = s.frontier)
    (hL_grow : s.frontier +
      (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u_val)) ≤ L_peak)
    (hwf_grow : Memory.WellFormed w
      { mem := ((Memory.spec 0).clientState s
          (prepGrowProg (((base, s.frontier), opTag), u_val))).mem
        frontier := s.frontier +
          (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u_val)) })
    (hpre_so : StepOpPre w
      (((base, s.frontier +
          (Memory.spec 0).clientResult s
            (prepGrowProg (((base, s.frontier), opTag), u_val))), opTag),
        (u_val, v_val))
      { mem := ((Memory.spec 0).clientState s
          (prepGrowProg (((base, s.frontier), opTag), u_val))).mem
        frontier := s.frontier +
          (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u_val)) })
    (hfr_tick : ((Memory.spec 0).clientState
      { mem := ((Memory.spec 0).clientState s
          (prepGrowProg (((base, s.frontier), opTag), u_val))).mem
        frontier := s.frontier +
          (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u_val)) }
      (stepOpProg (((base, s.frontier +
          (Memory.spec 0).clientResult s
            (prepGrowProg (((base, s.frontier), opTag), u_val))), opTag),
        (u_val, v_val)))).frontier =
      s.frontier +
        (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u_val))) :
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u_val))
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u_val))
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let s_tick := (Memory.spec 0).clientState s_grow
      (stepOpProg (((base, s_grow.frontier), opTag), (u_val, v_val)))
    let res_so := (Memory.spec 0).clientResult s_grow
      (stepOpProg (((base, s_grow.frontier), opTag), (u_val, v_val)))
    let T_pre := 1 + (wPrepGrow.factor *
      (memoryCost (prepGrowProg (((base, s.frontier), opTag), u_val)) s + 1) +
      (1 + ((5 * k_grow + 6) + (1 + (1 + (wStepOp.factor *
        (memoryCost (stepOpProg (((base, s_grow.frontier), opTag), (u_val, v_val))) s_grow + 1) +
          5))))))
    ∃ x8 : RData rWhp,
      (∀ (tail : RCode .exact rWhp) (μ_tail : PMF (RCodeStepOutcome rWhp)),
        ExecRCodeSteps w tail x8 μ_tail L_peak →
        ExecRCodeSteps w (opPrefixCode tail) x0
          (μ_tail.map fun z => ⟨z.data, T_pre + z.steps, z.timed⟩) L_peak) ∧
      rMemState x8 = s_tick ∧
      x8.Bounded w ∧
      x8.regs mBaseWhp = base ∧
      x8.regs mFrWhp = s_tick.frontier ∧
      x8.regs rFrArg = s_tick.frontier ∧
      x8.regs rTag = opTag ∧
      x8.regs rOne = 1 ∧
      x8.regs rOutFlag = res_so.1.1 ∧
      x8.regs rOutVal = res_so.1.2 ∧
      x8.regs rCur = res_so.2.1 ∧
      x8.regs rEnd = res_so.2.2.1 ∧
      x8.regs rMask = res_so.2.2.2 := by
  intro k_grow s_prep s_grow s_tick res_so T_pre
  have hx0_fr_s : x0.frontier = s.frontier := congrArg Memory.State.frontier hs_eq
  have hx0_mem_s : x0.mem = s.mem := congrArg Memory.State.mem hs_eq
  have f1 : Fits w 1 := by
    have : 2 ≤ 2 ^ w := (by decide : 2 ≤ 2 ^ 11) |>.trans (Nat.pow_le_pow_right (by decide) hw11)
    unfold Fits; omega
  have e1 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak)
    (d := rFrArg) (s := mFrWhp) (x := x0) (hx0_fr_s ▸ hL_x)
  set x1 := x0.set rFrArg (x0.regs mFrWhp)
  have hx1b : x1.Bounded w := hx0b.set (hx0b.regs_fits mFrWhp)
  have hx1_fr : x1.frontier = s.frontier := hx0_fr_s
  have hx1_ms : (⟨x1.mem, x1.frontier⟩ : Memory.State) = s := hs_eq
  have hin_pg : x1.regs ∘ srcPrepGrow =
      WordEncoding.encode (((base, s.frontier), opTag), u_val) :=
    (whpRegs_pair (x := x1)
      (whpRegs_pair (x := x1)
        (whpRegs_pair (x := x1)
          (whpRegs_reg1 (x := x1) mBaseWhp (by simp [x1, RData.set, hx0_base]))
          (whpRegs_reg1 (x := x1) rFrArg (by simp [x1, RData.set, hx0_fr])))
        (whpRegs_reg1 (x := x1) rTag (by simp [x1, RData.set, hx0_tag])))
      (whpRegs_reg1 (x := x1) rKey (by simp [x1, RData.set, hx0_key]))).eq
  obtain ⟨x2, e2, hx2b, hx2_fr, hx2_mem, hx2_regs, hx2_out⟩ :=
    emitWhpWitness_exec wPrepGrow (by decide) scr_prepGrow_le
      srcPrepGrow srcPrepGrow_lt srcPrepGrow_ne1
      (L_peak := L_peak) (((base, s.frontier), opTag), u_val) hx1b (hx1_fr ▸ hL_x)
      (by simp [x1, RData.set, hx0_fr, hx0_fr_s])
      hin_pg (hx1_ms.symm ▸ hpre_pg) (hx1_ms.symm ▸ validHistory_prepGrowProg hwf0 hpre_pg)
      (by rw [hx1_ms, hx1_fr]; exact hfr_prep)
  have hx2_tmp0 : x2.regs rTmp0 = k_grow := by
    have h0 := hx2_out 0
    rw [hx1_ms] at h0
    exact h0
  have e3 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak)
    (d := rK) (s := rTmp0) (x := x2) (by rw [hx2_fr, hx1_fr]; exact hL_x)
  set x3 := x2.set rK (x2.regs rTmp0)
  have hx3b : x3.Bounded w := hx2b.set (hx2b.regs_fits rTmp0)
  have hx3_k : x3.regs rK = k_grow := by simp [x3, RData.set, hx2_tmp0]
  have hx3_fr : x3.frontier = s.frontier := hx2_fr.trans hx1_fr
  have e4 := growZeroCode_exec (w := w) (L_peak := L_peak)
    (count := rK) (result := rRes) (cur := rCur) (idx := rIdx) (zero := rZero) (one := rOne)
    hx3b whpGrowRes_nodup f1 (by rw [hx3_fr, hx3_k]; exact hL_grow)
    (by rw [hx3_fr, hx3_k]; exact hwf_grow.1)
  set x4 := growZeroPost rK rRes rCur rIdx rZero rOne x3
  have hx4b : x4.Bounded w :=
    whpGrowZeroPost_bounded hx3b f1 (by rw [hx3_fr, hx3_k]; exact hwf_grow.1)
  have hx4_fr : x4.frontier = s_grow.frontier := by
    simp [x4, growZeroPost, hx3_k, hx3_fr, s_grow]
  have hx4_low : ∀ r : Fin rWhp, r.val < 6 → x4.regs r = x1.regs r := fun r hr => by
    have hne (c : Fin 23) (hc : 6 ≤ c.val) : r ≠ whpReg c :=
      ne_of_val_ne (by rw [val_whpReg]; omega)
    have h43 : x4.regs r = x3.regs r := by
      dsimp only [x4, growZeroPost]
      rw [Function.update_of_ne (hne 10 (by decide)), Function.update_of_ne (hne 13 (by decide)),
        Function.update_of_ne (hne 9 (by decide)), Function.update_of_ne (hne 15 (by decide)),
        Function.update_of_ne (hne 14 (by decide))]
    have h32 : x3.regs r = x2.regs r := by
      dsimp only [x3, RData.set]; rw [Function.update_of_ne (hne 8 (by decide))]
    exact h43.trans (h32.trans (hx2_regs r (by omega)))
  have hx4_one : x4.regs rOne = 1 := by simp [x4, growZeroPost]
  have hx4_mfr : x4.regs mFrWhp = s.frontier :=
    (hx4_low mFrWhp (by simp)).trans (by simp [x1, RData.set, hx0_fr])
  have hx4_k : x4.regs rK = k_grow := by simp [x4, growZeroPost, hx3_k]
  have e5 : RDemonicExec w L_peak (.op (.exactBin .add mFrWhp mFrWhp rK)) x4 1
      (· = x4.set mFrWhp s_grow.frontier) :=
    RDemonicExec.exactBin (x := x4) (hx4_fr ▸ hL_grow)
      (by simp [BinOp.evalExact, hx4_mfr, hx4_k, s_grow]) hwf_grow.1
  set x5 := x4.set mFrWhp s_grow.frontier
  have hx5b : x5.Bounded w := hx4b.set hwf_grow.1
  have e6 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak)
    (d := rFrArg) (s := mFrWhp) (x := x5) (hx4_fr ▸ hL_grow)
  set x6 := x5.set rFrArg (x5.regs mFrWhp)
  have hx6b : x6.Bounded w := hx5b.set (hx5b.regs_fits mFrWhp)
  have hmem_x6 : (⟨x6.mem, x6.frontier⟩ : Memory.State) = s_grow :=
    Memory.State.ext (hx2_mem.trans (congrArg (fun st => ((Memory.spec 0).clientState st _).mem)
      hx1_ms)) hx4_fr
  have hin_so : x6.regs ∘ srcStepOp =
      WordEncoding.encode (((base, s_grow.frontier), opTag), (u_val, v_val)) :=
    (whpRegs_pair (x := x6)
      (whpRegs_pair (x := x6)
        (whpRegs_pair (x := x6)
          (whpRegs_reg1 (x := x6) mBaseWhp
            (by simp [x6, x5, hx4_low mBaseWhp (by simp), x1, hx0_base]))
          (whpRegs_reg1 (x := x6) rFrArg (by simp [x6, x5])))
        (whpRegs_reg1 (x := x6) rTag
          (by simp [x6, x5, hx4_low rTag (by simp), x1, hx0_tag])))
      (whpRegs_pair (x := x6)
        (whpRegs_reg1 (x := x6) rKey
          (by simp [x6, x5, hx4_low rKey (by simp), x1, hx0_key]))
        (whpRegs_reg1 (x := x6) rVal
          (by simp [x6, x5, hx4_low rVal (by simp), x1, hx0_val])))).eq
  obtain ⟨x7, e7, hx7b, hx7_fr, hx7_mem, hx7_regs, hx7_out⟩ :=
    emitWhpWitness_exec wStepOp (by decide) scr_stepOp_le srcStepOp srcStepOp_lt srcStepOp_ne1
      (L_peak := L_peak) (((base, s_grow.frontier), opTag), (u_val, v_val)) hx6b (hx4_fr ▸ hL_grow)
      (by simp [x6, x5, RData.set, hx4_fr])
      hin_so (by rw [hmem_x6]; exact hpre_so)
      (by rw [hmem_x6]; exact validHistory_stepOpProg hwf_grow hpre_so)
      (by rw [hmem_x6]; exact hfr_tick.trans hx4_fr.symm)
  have hL_x7 : x7.frontier ≤ L_peak := by rw [hx7_fr]; exact hx4_fr ▸ hL_grow
  have ec0 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak)
    (d := rOutFlag) (s := rTmp0) (x := x7) hL_x7
  set c0 := x7.set rOutFlag (x7.regs rTmp0)
  have hb_c0 : c0.Bounded w := hx7b.set (hx7b.regs_fits rTmp0)
  have ec1 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak)
    (d := rOutVal) (s := rTmp1) (x := c0) hL_x7
  set c1 := c0.set rOutVal (c0.regs rTmp1)
  have hb_c1 : c1.Bounded w := hb_c0.set (hb_c0.regs_fits rTmp1)
  have ec2 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak)
    (d := rCur) (s := rTmp2) (x := c1) hL_x7
  set c2 := c1.set rCur (c1.regs rTmp2)
  have hb_c2 : c2.Bounded w := hb_c1.set (hb_c1.regs_fits rTmp2)
  have ec3 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak)
    (d := rEnd) (s := rTmp3) (x := c2) hL_x7
  set c3 := c2.set rEnd (c2.regs rTmp3)
  have hb_c3 : c3.Bounded w := hb_c2.set (hb_c2.regs_fits rTmp3)
  have ec4 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak)
    (d := rMask) (s := rTmp4) (x := c3) hL_x7
  set x8 := c3.set rMask (c3.regs rTmp4)
  have hx8b : x8.Bounded w := hb_c3.set (hb_c3.regs_fits rTmp4)
  have henc5 := wordEncode_five res_so
  refine ⟨x8, fun tail μ_tail htail => ?_, ?_, hx8b, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h :=
      execRCodeSteps_seq_demonic e1 <| execRCodeSteps_seq_demonic e2 <|
      execRCodeSteps_seq_demonic e3 <| execRCodeSteps_seq_demonic e4 <|
      execRCodeSteps_seq_demonic e5 <| execRCodeSteps_seq_demonic e6 <|
      execRCodeSteps_seq_demonic e7 <| execRCodeSteps_seq_demonic ec0 <|
      execRCodeSteps_seq_demonic ec1 <| execRCodeSteps_seq_demonic ec2 <|
      execRCodeSteps_seq_demonic ec3 <| execRCodeSteps_seq_demonic ec4 htail
    simp only [PMF.map_comp, Function.comp_def] at h
    refine h.congr_dist ?_
    congr 1; funext z
    rw [hx1_ms, hmem_x6, hx3_k]
    congr 1; dsimp only [T_pre]; omega
  · exact Memory.State.ext
      (hx7_mem.trans (congrArg (fun st => ((Memory.spec 0).clientState st _).mem) hmem_x6))
      (hx7_fr.trans (hx4_fr.trans hfr_tick.symm))
  · simp [x8, c3, c2, c1, c0, RData.set, hx7_regs mBaseWhp (by simp), x6, x5,
      hx4_low mBaseWhp (by simp), x1, hx0_base]
  · simp only [x8, c3, c2, c1, c0, RData.set, ne_eq, whpReg_inj,
      show (1 : Fin 23) ≠ 12 by decide, show (1 : Fin 23) ≠ 11 by decide,
      show (1 : Fin 23) ≠ 10 by decide, show (1 : Fin 23) ≠ 7 by decide,
      show (1 : Fin 23) ≠ 6 by decide, not_false_eq_true, Function.update_of_ne,
      hx7_regs mFrWhp (by simp), x6, x5, show (1 : Fin 23) ≠ 5 by decide,
      Function.update_self]
    exact hfr_tick.symm
  · simp only [x8, c3, c2, c1, c0, RData.set, ne_eq, whpReg_inj,
      show (5 : Fin 23) ≠ 12 by decide, show (5 : Fin 23) ≠ 11 by decide,
      show (5 : Fin 23) ≠ 10 by decide, show (5 : Fin 23) ≠ 7 by decide,
      show (5 : Fin 23) ≠ 6 by decide, not_false_eq_true, Function.update_of_ne,
      hx7_regs rFrArg (by simp), x6, x5, Function.update_self]
    exact hfr_tick.symm
  · simp [x8, c3, c2, c1, c0, RData.set, hx7_regs rTag (by simp), x6, x5,
      hx4_low rTag (by simp), x1, hx0_tag]
  · simp [x8, c3, c2, c1, c0, RData.set, hx7_regs rOne (by simp), x6, x5, hx4_one]
  · have h0 := hx7_out 0; rw [hmem_x6] at h0
    have h0' : x7.regs rTmp0 = res_so.1.1 := h0.trans henc5.1
    simp [x8, c3, c2, c1, c0, RData.set, h0']
  · have h1 := hx7_out 1; rw [hmem_x6] at h1
    have h1' : x7.regs rTmp1 = res_so.1.2 := h1.trans henc5.2.1
    simp [x8, c3, c2, c1, c0, RData.set, h1']
  · have h2 := hx7_out 2; rw [hmem_x6] at h2
    have h2' : x7.regs rTmp2 = res_so.2.1 := h2.trans henc5.2.2.1
    simp [x8, c3, c2, c1, c0, RData.set, h2']
  · have h3 := hx7_out 3; rw [hmem_x6] at h3
    have h3' : x7.regs rTmp3 = res_so.2.2.1 := h3.trans henc5.2.2.2.1
    simp [x8, c3, c2, c1, c0, RData.set, h3']
  · have h4 := hx7_out 4; rw [hmem_x6] at h4
    have h4' : x7.regs rTmp4 = res_so.2.2.2 := h4.trans henc5.2.2.2.2
    simp [x8, c3, c2, c1, c0, RData.set, h4']

private theorem opSuffixCode_exec {w L_peak base opTag : ℕ}
    {s_r : Memory.State} {xr : RData rWhp}
    (hs_r : rMemState xr = s_r)
    (hw11 : 11 ≤ w) (hxrb : xr.Bounded w) (hL_xr : s_r.frontier ≤ L_peak)
    (hxr_base : xr.regs mBaseWhp = base) (hxr_mfr : xr.regs mFrWhp = s_r.frontier)
    (hxr_fra : xr.regs rFrArg = s_r.frontier) (hxr_tag : xr.regs rTag = opTag)
    (hwf_r : Memory.WellFormed w s_r)
    (hpre_prs : PostRandShrinkPre w ((base, s_r.frontier), opTag) s_r)
    (hfr_ps : ((Memory.spec 0).clientState s_r
      (postRandShrinkProg ((base, s_r.frontier), opTag))).frontier = s_r.frontier)
    (hk_sh_fr : (Memory.spec 0).clientResult s_r
      (postRandShrinkProg ((base, s_r.frontier), opTag)) ≤ s_r.frontier) :
    let s_ps := (Memory.spec 0).clientState s_r (postRandShrinkProg ((base, s_r.frontier), opTag))
    let k_sh := (Memory.spec 0).clientResult s_r (postRandShrinkProg ((base, s_r.frontier), opTag))
    let T_suf := wPostRandShrink.factor *
      (memoryCost (postRandShrinkProg ((base, s_r.frontier), opTag)) s_r + 1) +
      (1 + ((4 * k_sh + 5) + 1))
    ∃ yw : RData rWhp,
      RDemonicExec w L_peak opSuffixCode xr T_suf (· = yw) ∧
      rMemState yw =
        { mem := clear s_ps.mem (s_r.frontier - k_sh) k_sh, frontier := s_r.frontier - k_sh } ∧
      yw.Bounded w ∧
      yw.regs mBaseWhp = base ∧
      yw.regs mFrWhp = yw.frontier ∧
      yw.regs rOutFlag = xr.regs rOutFlag ∧
      yw.regs rOutVal = xr.regs rOutVal := by
  intro s_ps k_sh T_suf
  have hxr_fr : xr.frontier = s_r.frontier := congrArg Memory.State.frontier hs_r
  have f1 : Fits w 1 := by
    have : 2 ≤ 2 ^ w := (by decide : 2 ≤ 2 ^ 11) |>.trans (Nat.pow_le_pow_right (by decide) hw11)
    unfold Fits; omega
  have hin_prs : xr.regs ∘ srcPostRandShrink =
      WordEncoding.encode ((base, s_r.frontier), opTag) :=
    (whpRegs_pair
      (whpRegs_pair (whpRegs_reg1 mBaseWhp hxr_base) (whpRegs_reg1 rFrArg hxr_fra))
      (whpRegs_reg1 rTag hxr_tag)).eq
  have hxr_ms : (⟨xr.mem, xr.frontier⟩ : Memory.State) = s_r := hs_r
  obtain ⟨x9, e9, hx9b, hx9_fr, hx9_mem, hx9_regs, hx9_out⟩ :=
    emitWhpWitness_exec wPostRandShrink (by decide) scr_postShrink_le
      srcPostRandShrink srcPostShrink_lt srcPostShrink_ne1
      (L_peak := L_peak) ((base, s_r.frontier), opTag) hxrb (hxr_fr ▸ hL_xr)
      (hxr_mfr.trans hxr_fr.symm) hin_prs (hxr_ms.symm ▸ hpre_prs)
      (hxr_ms.symm ▸ validHistory_postRandShrinkProg hwf_r hpre_prs)
      (by rw [hxr_ms, hxr_fr]; exact hfr_ps)
  have hx9_tmp0 : x9.regs rTmp0 = k_sh := by
    have h0 := hx9_out 0
    rw [hxr_ms] at h0
    exact h0
  have e10 := RDemonicExec.copy (B := .exact) (w := w) (L_peak := L_peak)
    (d := rK) (s := rTmp0) (x := x9) (by rw [hx9_fr, hxr_fr]; exact hL_xr)
  set x10 := x9.set rK (x9.regs rTmp0)
  have hx10b : x10.Bounded w := hx9b.set (hx9b.regs_fits rTmp0)
  have hx10_k : x10.regs rK = k_sh := by simp [x10, RData.set, hx9_tmp0]
  have hx10_fr : x10.frontier = s_r.frontier := hx9_fr.trans hxr_fr
  have e11 := shrinkCode_exec (w := w) (L_peak := L_peak)
    (count := rK) (idx := rIdx) (zero := rZero) (one := rOne)
    hx10b whpShrink_nodup f1 (hx10_fr ▸ hL_xr) (by rw [hx10_fr, hx10_k]; exact hk_sh_fr)
  set x11 := shrinkPost rK rIdx rZero rOne x10
  have hx11b : x11.Bounded w :=
    whpShrinkPost_bounded hx10b f1 (by rw [hx10_fr, hx10_k]; exact hk_sh_fr)
  have hx11_fr : x11.frontier = s_r.frontier - k_sh := by
    simp [x11, shrinkPost, hx10_k, hx10_fr]
  have hx11_low8 : ∀ r : Fin rWhp, r.val < 8 → x11.regs r = xr.regs r := fun r hr => by
    have hne (c : Fin 23) (hc : 8 ≤ c.val) : r ≠ whpReg c :=
      ne_of_val_ne (by rw [val_whpReg]; omega)
    have h1 : x11.regs r = x10.regs r := by
      dsimp only [x11, shrinkPost]
      rw [Function.update_of_ne (hne 13 (by decide)), Function.update_of_ne (hne 15 (by decide)),
        Function.update_of_ne (hne 14 (by decide))]
    have h2 : x10.regs r = x9.regs r := by
      dsimp only [x10, RData.set]; rw [Function.update_of_ne (hne 8 (by decide))]
    exact h1.trans (h2.trans (hx9_regs r (by omega)))
  have hx11_mfr : x11.regs mFrWhp = s_r.frontier :=
    (hx11_low8 mFrWhp (by simp)).trans hxr_mfr
  have hx11_k : x11.regs rK = k_sh := by simp [x11, shrinkPost, hx10_k]
  have hfit_post_fr : Fits w (s_r.frontier - k_sh) := hwf_r.1.of_le (Nat.sub_le _ _)
  have hk_le_fr : k_sh ≤ s_r.frontier := hk_sh_fr
  have hev12 : BinOp.evalExact .sub (x11.regs mFrWhp) (x11.regs rK) =
      some (s_r.frontier - k_sh) := by
    rw [hx11_mfr, hx11_k]; simp [BinOp.evalExact, hk_le_fr]
  have e12 : RDemonicExec w L_peak (.op (.exactBin .sub mFrWhp mFrWhp rK)) x11 1
      (· = x11.set mFrWhp (s_r.frontier - k_sh)) :=
    RDemonicExec.exactBin (x := x11)
      (by rw [hx11_fr]; exact (Nat.sub_le _ _).trans hL_xr) hev12 hfit_post_fr
  set yw := x11.set mFrWhp (s_r.frontier - k_sh)
  have hywb : yw.Bounded w := hx11b.set hfit_post_fr
  have hdem : RDemonicExec w L_peak opSuffixCode xr T_suf (· = yw) := by
    have hd := e9.seq_eq (e10.seq_eq (e11.seq_eq e12))
    rw [hxr_ms, hx10_k] at hd
    exact hd
  refine ⟨yw, hdem, ?_, hywb, ?_, by simp [yw, RData.set, hx11_fr], ?_, ?_⟩
  · refine Memory.State.ext ?_ hx11_fr
    dsimp only [rMemState, yw, RData.set, x11, shrinkPost, s_ps]
    rw [hx10_k, hx10_fr, show x10.mem = x9.mem from rfl, hx9_mem, hxr_ms]
  · simp [yw, RData.set, hx11_low8 mBaseWhp (by simp), hxr_base]
  · simp [yw, RData.set, hx11_low8 rOutFlag (by simp)]
  · simp [yw, RData.set, hx11_low8 rOutVal (by simp)]

private noncomputable def randFillPost {k w : ℕ} (start : ℕ) (x : RData rWhp)
    (ws : Fin k → Fin (2 ^ w)) : RData rWhp :=
  ⟨if hk : k = 0 then x.regs
   else Function.update (Function.update x.regs rRes (ws ⟨k - 1, by omega⟩).val)
     rCur (start + k),
   writeWords x.mem start ws, x.frontier⟩

private theorem randFillPost_bounded {k w start : ℕ} {x : RData rWhp}
    (hx : x.Bounded w) (hbound : start + k ≤ x.frontier) (hfit_end : Fits w (start + k))
    (ws : Fin k → Fin (2 ^ w)) :
    (randFillPost start x ws).Bounded w ∧
    (randFillPost start x ws).frontier = x.frontier ∧
    (randFillPost start x ws).mem = writeWords x.mem start ws ∧
    ∀ i : Fin rWhp, i ≠ rCur → i ≠ rRes → (randFillPost start x ws).regs i = x.regs i := by
  refine ⟨⟨⟨fun i => ?_, fun a => ?_⟩, hx.2.1, fun a ha => ?_⟩, rfl, rfl, fun i hc hr => ?_⟩
  · dsimp only [randFillPost, RData.toData]
    split_ifs with hk
    · exact hx.regs_fits i
    · by_cases hc : i = rCur
      · subst hc; simp [hfit_end]
      · rw [Function.update_of_ne hc]
        by_cases hr : i = rRes
        · subst hr; rw [Function.update_self]; exact (ws _).isLt
        · rw [Function.update_of_ne hr]; exact hx.regs_fits i
  · dsimp only [randFillPost, RData.toData]; unfold writeWords
    split_ifs with hin
    · exact (ws _).isLt
    · exact hx.mem_fits a
  · dsimp only [randFillPost] at ha ⊢
    rw [writeWords_apply_out _ _ _ (by omega)]
    exact hx.zero_above ha
  · dsimp only [randFillPost]
    split_ifs with hk
    · rfl
    · rw [Function.update_of_ne hc, Function.update_of_ne hr]

private theorem prepare_whp_regs {c U V w : ℕ} (o : Dynamic.Op U) (x : RData rWhp) :
    ((subroutineCodeWhp c U V w).prepare whpEncode o x).regs mBaseWhp = x.regs mBaseWhp ∧
    ((subroutineCodeWhp c U V w).prepare whpEncode o x).regs mFrWhp = x.regs mFrWhp := by
  simp [Cslib.DataStructure.WordRAM.Resizable.SubroutineCode.prepare,
    Cslib.DataStructure.WordRAM.Resizable.SubroutineCode.prepareRegs,
    subroutineCodeWhp, whpInput, mBaseWhp, mFrWhp]

/-- Single-state `ExecRCodeSteps` specification of `opCodeWhp` on `query u`. -/
theorem opCodeWhp_query_exec {c U V w base L_peak : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {x : RData rWhp}
    (hrep : DualRep c U V w base s_dict L x) (u : Fin U)
    (hL_peak : x.frontier ≤ L_peak) :
    ∃ (y : RData rWhp) (T : ℕ),
      ExecRCodeSteps w opCodeWhp
        ((subroutineCodeWhp c U V w).prepare whpEncode (.query u) x)
        (PMF.pure ⟨y, T, true⟩) L_peak ∧
      rMemState y = rMemState x ∧
      DualRep c U V w base s_dict L y ∧
      whpDecode (V := V) (.query u) y.regs = some (s_dict u) ∧
      (∀ addr < base, y.mem addr = x.mem addr) ∧
      (L.ActiveGood (x.mem (base + hdrPhase)) → T ≤ worstCaseTimeWhp c) := by
  obtain ⟨hxb, hx_base, hx_fr, hinv⟩ := hrep
  have hw11 := hinv.hw11
  set s := rMemState x
  set x0 := (subroutineCodeWhp c U V w).prepare whpEncode (.query u) x
  have hprep_r := prepare_whp_regs (c := c) (V := V) (w := w) (.query u) x
  have hx0b : x0.Bounded w :=
    (subroutineCodeWhp c U V w).prepare_bounded hxb
      fun i _ => whpEncode_fits (s_dict := s_dict) hinv.U_lt hinv.V_le hw11 (.query u) trivial i
  obtain ⟨hpre_pg, hst_pg, hres_pg, hmc_pg, hpre_so, hst_so, hres_so, hmc_so,
    hpre_prs, hst_prs, hres_prs, hmc_prs⟩ := stepOpProg_query_spec (v_val := 0) hinv u
  have hs_grow_eq :
      ({ mem := ((Memory.spec 0).clientState s
            (prepGrowProg (((base, s.frontier), 0), u.val))).mem
         frontier := s.frontier + (Memory.spec 0).clientResult s
            (prepGrowProg (((base, s.frontier), 0), u.val)) } : Memory.State) = s := by
    rw [hres_pg, Nat.add_zero, hst_pg]
  have hfr_g : s.frontier + (Memory.spec 0).clientResult s
      (prepGrowProg (((base, s.frontier), 0), u.val)) = s.frontier := by
    rw [hres_pg, Nat.add_zero]
  obtain ⟨x8, hpre_ex, hx8_mem, hx8b, hx8_base, hx8_mfr, hx8_fra, hx8_tag, _,
    hx8_of, hx8_ov, hx8_cur, hx8_end, _⟩ :=
    opPrefixCode_exec (L_peak := L_peak) (base := base) (opTag := 0) (u_val := u.val) (v_val := 0)
      (s := s) (x0 := x0) rfl hw11 hx0b hL_peak
      (hprep_r.1.trans hx_base) (hprep_r.2.trans hx_fr)
      rfl rfl rfl hinv.wf hpre_pg
      (congrArg Memory.State.frontier hst_pg)
      (hfr_g.symm ▸ hL_peak)
      (hs_grow_eq.symm ▸ hinv.wf)
      (by rw [hs_grow_eq, hfr_g]; exact hpre_so)
      (by rw [hs_grow_eq, hfr_g, hst_so])
  have hx8_s : rMemState x8 = s := by
    rw [hx8_mem]; change (Memory.spec 0).clientState _ _ = s
    rw [hs_grow_eq, hst_so]
  have hx8_fr : x8.frontier = s.frontier := congrArg Memory.State.frontier hx8_s
  have hres_so_q :
      (Memory.spec 0).clientResult
        { mem := ((Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), 0), u.val))).mem
          frontier := s.frontier +
            (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), 0), u.val)) }
        (stepOpProg (((base, s.frontier +
            (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), 0), u.val))), 0),
          (u.val, 0))) =
      ((match s_dict u with | none => 0 | some val => 1,
        match s_dict u with | none => 0 | some val => val), (0, (0, 0))) := by
    rw [hs_grow_eq, hfr_g, hres_so]
    cases s_dict u <;> rfl
  have hx8_ce : x8.regs rCur = x8.regs rEnd := by
    rw [hx8_cur, hx8_end, hres_so_q]
  have e_rf : RDemonicExec w L_peak (randFillBatchCode rCur rEnd rMask rRes rOne) x8 2 (· = x8) :=
    RDemonicExec.loop_exit (hx8_fr ▸ hL_peak) (by simp [Cond.Holds, hx8_ce]) rfl
  obtain ⟨y, e_suf, hy_mem, hyb, hy_base, hy_mfr, hy_of, hy_ov⟩ :=
    opSuffixCode_exec (L_peak := L_peak) (s_r := s) (xr := x8) hx8_s hw11 hx8b hL_peak hx8_base
      (hx8_mfr.trans (congrArg Memory.State.frontier (hx8_mem.symm.trans hx8_s)))
      (hx8_fra.trans (congrArg Memory.State.frontier (hx8_mem.symm.trans hx8_s)))
      hx8_tag hinv.wf hpre_prs (congrArg Memory.State.frontier hst_prs)
      (by rw [hres_prs]; exact Nat.zero_le _)
  have hex_tail := ExecRCodeSteps.of_demonicExec (e_rf.seq_eq e_suf)
  have hex_all := hpre_ex _ _ hex_tail
  rw [PMF.pure_map] at hex_all
  have hy_s : rMemState y = s := by
    rw [hy_mem]; simp only [hst_prs, hres_prs, Nat.sub_zero, clear_zero]
  refine ⟨y, _, hex_all, hy_s, ⟨hyb, hy_base, hy_mfr, hy_s ▸ hinv⟩, ?_,
    fun addr _ => congrArg (fun st => st.mem addr) hy_s, fun hgood => ?_⟩
  · have hof : y.regs rOutFlag = match s_dict u with | none => 0 | some _ => 1 :=
      hy_of.trans (hx8_of.trans (congrArg (fun p => p.1.1) hres_so_q))
    have hov : y.regs rOutVal = match s_dict u with | none => 0 | some val => val :=
      hy_ov.trans (hx8_ov.trans (congrArg (fun p => p.1.2) hres_so_q))
    unfold whpDecode
    rw [hof, hov]
    cases s_dict u <;> simp
  · dsimp only
    rw [hres_pg, Nat.add_zero, hst_pg, hres_prs, hmc_prs]
    change (1 + (wPrepGrow.factor *
        (memoryCost (prepGrowProg (((base, s.frontier), 0), u.val)) s + 1) +
        (1 + ((5 * 0 + 6) + (1 + (1 + (wStepOp.factor *
          (memoryCost (stepOpProg (((base, s.frontier), 0), (u.val, 0))) s + 1) +
            5))))))) +
      (2 + (wPostRandShrink.factor * (0 + 1) + (1 + ((4 * 0 + 5) + 1)))) ≤ worstCaseTimeWhp c
    have hso_le := hmc_so hgood
    have h1 : wPrepGrow.factor *
        (memoryCost (prepGrowProg (((base, s.frontier), 0), u.val)) s + 1) ≤
        wPrepGrow.factor * 41 := Nat.mul_le_mul_left _ (by omega)
    have h2 : wStepOp.factor *
        (memoryCost (stepOpProg (((base, s.frontier), 0), (u.val, 0))) s + 1) ≤
        wStepOp.factor *
          ((2 * epochStepCost c + 80) + (itemBatchWhp * (2 * epochStepCost c + 20) + 20000) + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : wPostRandShrink.factor * (0 + 1) ≤ wPostRandShrink.factor * 116 :=
      Nat.mul_le_mul_left _ (by decide)
    unfold worstCaseTimeWhp bulkBatchWhp
    omega

private theorem opCodeWhp_mutate_setup {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {s : Memory.State}
    (hinv : DualStateInv c U V w base s_dict L s)
    {o : Dynamic.Op U} {u : Fin U} {v : Fin V}
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o)) :
    opTag ≠ 0 ∧
    (opTag = 1 → v_val = v.val) ∧
    ((if opTag = 1 then Function.update s_dict u (some v.val)
      else Function.update s_dict u none) = ((Dynamic.spec U V U).stepFn s_dict o).1) ∧
    base + spaceBoundWhp c V w
      (if opTag = 1 then Function.update s_dict u (some v.val)
       else Function.update s_dict u none) < 2 ^ w ∧
    base + dualPaddedWords c U V w (s.mem (base + hdrNSrc))
      (if s.mem (base + hdrPhase) = 0 then s.mem (base + hdrNSrc)
       else s.mem (base + hdrNDst))
      (Dictionary.dom (if opTag = 1 then Function.update s_dict u (some v.val)
        else Function.update s_dict u none)).card < 2 ^ w ∧
    s.frontier ≤ base + stepSuccinctPeakWordsWhp c V w s_dict o := by
  have hop_nz : opTag ≠ 0 := by rcases ho_mut with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> decide
  have hv_eq : opTag = 1 → v_val = v.val := by
    rcases ho_mut with ⟨_, _, hv_v⟩ | ⟨_, rfl, _⟩
    · exact fun _ => hv_v
    · intro h; cases h
  have hs_dict'_eq :
      (if opTag = 1 then Function.update s_dict u (some v.val)
       else Function.update s_dict u none) = ((Dynamic.spec U V U).stepFn s_dict o).1 := by
    rcases ho_mut with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;> rfl
  obtain ⟨_, hpad'_le⟩ := dualPaddedWords_step_le_peak hinv hop_nz u v
  have hsucc_fits' :
      base + spaceBoundWhp c V w
        (if opTag = 1 then Function.update s_dict u (some v.val)
         else Function.update s_dict u none) < 2 ^ w := by
    rw [hs_dict'_eq]
    exact lt_of_le_of_lt (Nat.add_le_add_left (le_max_right _ _) base) hfit_peak
  exact ⟨hop_nz, hv_eq, hs_dict'_eq, hsucc_fits',
    lt_of_le_of_lt (Nat.add_le_add_left hpad'_le base) hsucc_fits',
    (dualStateInv_frontier_le_succinctWords hinv).trans
      (Nat.add_le_add_left (le_max_left _ _) base)⟩

/-- Single-state deterministic `ExecRCodeSteps` specification of `opCodeWhp` on `insert` / `delete`
outside Phase `5` (`x.mem (base + hdrPhase) ≠ 5`). -/
theorem opCodeWhp_mutate_det_exec {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {x : RData rWhp}
    (hrep : DualRep c U V w base s_dict L x)
    (o : Dynamic.Op U) (hv : (Dynamic.spec U V U).valid s_dict o)
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (hne5 : x.mem (base + hdrPhase) ≠ 5) :
    let s := rMemState x
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let s_tick := (Memory.spec 0).clientState s_grow
      (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val)))
    let k_sh := (Memory.spec 0).clientResult s_tick
      (postRandShrinkProg ((base, s_tick.frontier), opTag))
    let s_ps := (Memory.spec 0).clientState s_tick
      (postRandShrinkProg ((base, s_tick.frontier), opTag))
    let s_post : Memory.State :=
      { mem := clear s_ps.mem (s_tick.frontier - k_sh) k_sh, frontier := s_tick.frontier - k_sh }
    ∃ (y : RData rWhp) (T : ℕ),
      ExecRCodeSteps w opCodeWhp
        ((subroutineCodeWhp c U V w).prepare whpEncode o x)
        (PMF.pure ⟨y, T, true⟩) (base + stepSuccinctPeakWordsWhp c V w s_dict o) ∧
      rMemState y = s_post ∧
      y.Bounded w ∧
      y.regs mBaseWhp = base ∧
      y.regs mFrWhp = y.frontier ∧
      whpDecode (V := V) o y.regs = some ((Dynamic.spec U V U).stepFn s_dict o).2 ∧
      (∀ addr < base, y.mem addr = x.mem addr) ∧
      (memoryCost (prepGrowProg (((base, s.frontier), opTag), u.val)) s ≤ 40 →
        memoryCost (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val))) s_grow ≤
          (2 * epochStepCost c + 80) + (itemBatchWhp * (2 * epochStepCost c + 20) + 20000) →
        memoryCost (postRandShrinkProg ((base, s_tick.frontier), opTag)) s_tick ≤ 115 →
        T ≤ worstCaseTimeWhp c) := by
  intro s k_grow s_prep s_grow s_tick k_sh s_ps s_post
  obtain ⟨hxb, hx_base, hx_fr, hinv⟩ := hrep
  have hw11 := hinv.hw11
  set L_peak := base + stepSuccinctPeakWordsWhp c V w s_dict o
  obtain ⟨hop_nz, hv_eq, hs_dict'_eq, hsucc_fits', hpad_fits', hL_x⟩ :=
    opCodeWhp_mutate_setup hinv ho_mut hfit_peak
  obtain ⟨hpad0_le, _⟩ := dualPaddedWords_step_le_peak hinv hop_nz u v
  obtain ⟨hpre_pg, hfr_prep, hk_grow_b, _, hfr_grow_pad, hwf_grow, hpre_so, hres1,
    _, hout_mid, _, hpt_inv, _, _⟩ :=
    stepOpProg_mutate_spec hinv hop_nz u v hv_eq hsucc_fits' hpad_fits'
  have hL_grow : s_grow.frontier ≤ L_peak :=
    hfr_grow_pad.trans ((Nat.add_le_add_left hpad0_le base).trans
      (Nat.add_le_add_left (le_max_left _ _) base))
  have hsm_ph :
      ((Memory.spec 0).clientState s_grow
        (userMutateProg ((base, opTag), (u.val, v_val)))).mem (base + hdrPhase) =
      s.mem (base + hdrPhase) := by
    have hsetup := fgSetup_of_dualStateInv hinv hop_nz u v
    by_cases hle7 : x.mem (base + hdrPhase) ≤ 7
    · exact (fgStep_le7_aux hinv u v hv_eq hsetup rfl rfl rfl hle7).2.2.2.1
        (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
        (base_add_ne (by decide)) (base_add_ne (by decide))
    · by_cases h8 : x.mem (base + hdrPhase) = 8
      · exact (fgStep_eq8_aux hinv u v hv_eq hsetup rfl rfl rfl h8).2.2.2.1
          (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
          (base_add_ne (by decide)) (base_add_ne (by decide))
      · exact (fgStep_ge9_aux hinv u v hv_eq hsetup rfl rfl rfl
          (show 9 ≤ (rMemState x).mem (base + hdrPhase) by
            change 9 ≤ x.mem (base + hdrPhase); omega)).2.2.2.1
          (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
          (base_add_ne (by decide)) (base_add_ne (by decide))
  obtain ⟨hfr_tick_m, hwf_tick, hout_tick_m, hpt_br⟩ := hpt_inv
  rw [ite_eq_left (hsm_ph.symm ▸ hne5)] at hpt_br
  obtain ⟨hrArgs0, _, _, hpre_sh_inv, _⟩ := hpt_br
  obtain ⟨hpre_prs, hfr_ps, hk_sh_b, hk_sh_fr, hout_ps, _, _, _, hinv_post_any⟩ :=
    postRandShrinkProg_spec_pre hop_nz hpre_sh_inv
  have hfr_mid : ((Memory.spec 0).clientState s_grow
      (userMutateProg ((base, opTag), (u.val, v_val)))).frontier = s_grow.frontier :=
    (prepGrow_userMutate_spec hinv hop_nz u v hv_eq hpad_fits').2.2.2.2.2.2.2.1
  have hfr_tick : s_tick.frontier = s_grow.frontier := hfr_tick_m.trans hfr_mid
  set x0 := (subroutineCodeWhp c U V w).prepare whpEncode o x
  have hprep_r := prepare_whp_regs (c := c) (V := V) (w := w) o x
  have hx0b : x0.Bounded w :=
    (subroutineCodeWhp c U V w).prepare_bounded hxb
      fun i _ => whpEncode_fits hinv.U_lt hinv.V_le hw11 o hv i
  have hx0_enc : x0.regs rTag = opTag ∧ x0.regs rKey = u.val ∧ x0.regs rVal = v_val := by
    rcases ho_mut with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩
  obtain ⟨x8, hpre_ex, hx8_mem, hx8b, hx8_base, hx8_mfr, hx8_fra, hx8_tag, _,
    _, _, hx8_cur, hx8_end, _⟩ :=
    opPrefixCode_exec (L_peak := L_peak) (s := s) (x0 := x0) rfl hw11 hx0b hL_x
      (hprep_r.1.trans hx_base) (hprep_r.2.trans hx_fr)
      hx0_enc.1 hx0_enc.2.1 hx0_enc.2.2 hinv.wf hpre_pg hfr_prep hL_grow hwf_grow hpre_so hfr_tick
  have hx8_fr : x8.frontier = s_tick.frontier := congrArg Memory.State.frontier hx8_mem
  have hres_so0 : (Memory.spec 0).clientResult s_grow
      (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val))) = ((0, 0), (0, (0, 0))) :=
    Prod.ext hres1 hrArgs0
  have hx8_ce : x8.regs rCur = x8.regs rEnd := by
    rw [hx8_cur, hx8_end, hres_so0]
  have e_rf : RDemonicExec w L_peak (randFillBatchCode rCur rEnd rMask rRes rOne) x8 2 (· = x8) :=
    RDemonicExec.loop_exit (by rw [hx8_fr, hfr_tick]; exact hL_grow)
      (by simp [Cond.Holds, hx8_ce]) rfl
  obtain ⟨y, e_suf, hy_mem, hyb, hy_base, hy_mfr, _, _⟩ :=
    opSuffixCode_exec (L_peak := L_peak) (s_r := s_tick) (xr := x8) hx8_mem hw11 hx8b
      (hfr_tick.symm ▸ hL_grow)
      hx8_base hx8_mfr hx8_fra hx8_tag hwf_tick hpre_prs hfr_ps hk_sh_fr
  have hex_all := hpre_ex _ _ (ExecRCodeSteps.of_demonicExec (e_rf.seq_eq e_suf))
  rw [PMF.pure_map] at hex_all
  refine ⟨y, _, hex_all, hy_mem, hyb, hy_base, hy_mfr, ?_, ?_, fun hc_pg hc_so hc_prs => ?_⟩
  · rcases ho_mut with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  · intro addr hlt
    have heq_m := congrArg (fun st => st.mem addr) hy_mem
    dsimp only [rMemState, s_post] at heq_m
    have hb192 : base + 192 ≤ s_tick.frontier - k_sh := hinv_post_any.base_fr
    rw [heq_m, clear_of_not_owns (by simp only [Block.Owns]; omega),
      hout_ps addr hlt, hout_tick_m addr hlt, hout_mid addr hlt]
  · change (1 + (wPrepGrow.factor *
        (memoryCost (prepGrowProg (((base, s.frontier), opTag), u.val)) s + 1) +
        (1 + ((5 * k_grow + 6) + (1 + (1 + (wStepOp.factor *
          (memoryCost (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val))) s_grow + 1) +
            5))))))) +
      (2 + (wPostRandShrink.factor *
        (memoryCost (postRandShrinkProg ((base, s_tick.frontier), opTag)) s_tick + 1) +
        (1 + ((4 * k_sh + 5) + 1)))) ≤ worstCaseTimeWhp c
    have hk_b : k_grow ≤ bulkBatchWhp := hk_grow_b
    have hks_b : k_sh ≤ bulkBatchWhp := hk_sh_b
    have h1 : wPrepGrow.factor *
        (memoryCost (prepGrowProg (((base, s.frontier), opTag), u.val)) s + 1) ≤
        wPrepGrow.factor * 41 := Nat.mul_le_mul_left _ (by omega)
    have h2 : wStepOp.factor *
        (memoryCost (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val))) s_grow + 1) ≤
        wStepOp.factor *
          ((2 * epochStepCost c + 80) + (itemBatchWhp * (2 * epochStepCost c + 20) + 20000) + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : wPostRandShrink.factor *
        (memoryCost (postRandShrinkProg ((base, s_tick.frontier), opTag)) s_tick + 1) ≤
        wPostRandShrink.factor * 116 := Nat.mul_le_mul_left _ (by omega)
    unfold worstCaseTimeWhp
    omega

/-- Single-state randomized `ExecRCodeSteps` specification of `opCodeWhp` on `insert` / `delete`
during Phase `5` (`x.mem (base + hdrPhase) = 5`). -/
theorem opCodeWhp_mutate_ph5_exec {c U V w base opTag v_val : ℕ}
    {s_dict : Dictionary.State U} {L : DualLatent c U V} {x : RData rWhp}
    (hrep : DualRep c U V w base s_dict L x)
    (o : Dynamic.Op U) (hv : (Dynamic.spec U V U).valid s_dict o)
    (hfit_peak : Fits w (base + stepSuccinctPeakWordsWhp c V w s_dict o))
    (u : Fin U) (v : Fin V)
    (ho_mut : (o = .insert u v.val ∧ opTag = 1 ∧ v_val = v.val) ∨
      (o = .delete u ∧ opTag = 2 ∧ v_val = 0))
    (hp5 : x.mem (base + hdrPhase) = 5) :
    let s := rMemState x
    let cur := s.mem (base + hdrCur)
    let nDst := s.mem (base + hdrNDst)
    let offBM := offBktMeta c w nDst
    let endOff := cur + min bulkBatchWhp (offBM - cur)
    let metaDst := dualMbDst base s.mem
    let k_grow := (Memory.spec 0).clientResult s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_prep := (Memory.spec 0).clientState s (prepGrowProg (((base, s.frontier), opTag), u.val))
    let s_grow : Memory.State := { mem := s_prep.mem, frontier := s.frontier + k_grow }
    let s_tick := (Memory.spec 0).clientState s_grow
      (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val)))
    ∃ (y : (Fin (endOff - cur) → Fin (2 ^ w)) → RData rWhp)
      (T : (Fin (endOff - cur) → Fin (2 ^ w)) → ℕ),
      ExecRCodeSteps w opCodeWhp
        ((subroutineCodeWhp c U V w).prepare whpEncode o x)
        ((PMF.uniformOfFintype (Fin (endOff - cur) → Fin (2 ^ w))).map
          fun ws => ⟨y ws, T ws, true⟩)
        (base + stepSuccinctPeakWordsWhp c V w s_dict o) ∧
      ∀ ws : Fin (endOff - cur) → Fin (2 ^ w),
        let s_r : Memory.State :=
          { mem := writeWords s_tick.mem (metaDst + cur) ws, frontier := s_tick.frontier }
        let s_ps := (Memory.spec 0).clientState s_r
          (postRandShrinkProg ((base, s_r.frontier), opTag))
        let k_sh := (Memory.spec 0).clientResult s_r
          (postRandShrinkProg ((base, s_r.frontier), opTag))
        let s_post : Memory.State :=
          { mem := clear s_ps.mem (s_r.frontier - k_sh) k_sh, frontier := s_r.frontier - k_sh }
        rMemState (y ws) = s_post ∧
        (y ws).Bounded w ∧
        (y ws).regs mBaseWhp = base ∧
        (y ws).regs mFrWhp = (y ws).frontier ∧
        whpDecode (V := V) o (y ws).regs = some ((Dynamic.spec U V U).stepFn s_dict o).2 ∧
        (∀ addr < base, (y ws).mem addr = x.mem addr) ∧
        (endOff < offBM →
          ∃ L_post : DualLatent c U V,
            PreservesEpochSeeds False False
              { (L.applyFG 5 opTag u v) with elapsed := L.elapsed + 1 } L_post ∧
            DualStateInv c U V w base ((Dynamic.spec U V U).stepFn s_dict o).1 L_post s_post) ∧
        ((L.applyFG 5 opTag u v).slotSrc.GoodCovers → T ws ≤ worstCaseTimeWhp c) := by
  intro s cur nDst offBM endOff metaDst k_grow s_prep s_grow s_tick
  obtain ⟨hxb, hx_base, hx_fr, hinv⟩ := hrep
  have hw11 := hinv.hw11
  have hw_pos : 0 < w := by omega
  set L_peak := base + stepSuccinctPeakWordsWhp c V w s_dict o
  obtain ⟨hop_nz, hv_eq, hs_dict'_eq, hsucc_fits', hpad_fits', hL_x⟩ :=
    opCodeWhp_mutate_setup hinv ho_mut hfit_peak
  obtain ⟨hpad0_le, _⟩ := dualPaddedWords_step_le_peak hinv hop_nz u v
  obtain ⟨hpre_pg, hfr_prep, hk_grow_b, hmc_pg, hfr_grow_pad, hwf_grow, hpre_so, hres1,
    _, hout_mid, _, hpt_inv, hmc_so_eq, hmc_um⟩ :=
    stepOpProg_mutate_spec hinv hop_nz u v hv_eq hsucc_fits' hpad_fits'
  have hL_grow : s_grow.frontier ≤ L_peak :=
    hfr_grow_pad.trans ((Nat.add_le_add_left hpad0_le base).trans
      (Nat.add_le_add_left (le_max_left _ _) base))
  set s_mid := (Memory.spec 0).clientState s_grow (userMutateProg ((base, opTag), (u.val, v_val)))
  have hfg5 := fgStep_le7_aux hinv u v hv_eq (fgSetup_of_dualStateInv hinv hop_nz u v)
    rfl rfl rfl (by change x.mem (base + hdrPhase) ≤ 7; rw [hp5]; decide)
  have hfr_mid : s_mid.frontier = s_grow.frontier := hfg5.2.1
  have hp5_s : s.mem (base + hdrPhase) = 5 := hp5
  have hsm_ph5 : s_mid.mem (base + hdrPhase) = 5 :=
    (hfg5.2.2.2.1 (base + hdrPhase) (by dsimp only [hdrPhase]; omega)
      (base_add_ne (by decide)) (base_add_ne (by decide))).trans hp5
  have hsm_cur : s_mid.mem (base + hdrCur) = cur :=
    hfg5.2.2.2.1 (base + hdrCur) (by dsimp only [hdrCur]; omega)
      (base_add_ne (by decide)) (base_add_ne (by decide))
  have hsm_nDst : s_mid.mem (base + hdrNDst) = nDst :=
    hfg5.2.2.2.1 (base + hdrNDst) (by dsimp only [hdrNDst]; omega)
      (base_add_ne (by decide)) (base_add_ne (by decide))
  have hsm_stg : s_mid.mem (base + hdrStage) = s.mem (base + hdrStage) :=
    hfg5.2.2.2.1 (base + hdrStage) (by dsimp only [hdrStage]; omega)
      (base_add_ne (by decide)) (base_add_ne (by decide))
  have hsm_pad : s_mid.mem (base + hdrPad) = s.mem (base + hdrPad) :=
    hfg5.2.2.2.1 (base + hdrPad) (by dsimp only [hdrPad]; omega)
      (base_add_ne (by decide)) (base_add_ne (by decide))
  have hsm_mbDst : dualMbDst base s_mid.mem = metaDst := by
    dsimp only [metaDst]
    unfold dualMbDst
    rw [hsm_ph5, hsm_nDst, hsm_stg, hsm_pad, hp5_s]
  have hsm_pDst : dualPDst base s_mid.mem = dualPDst base s.mem := by
    unfold dualPDst
    rw [hsm_ph5, hsm_stg, hp5_s]
  obtain ⟨hfr_tick_m, hwf_tick, _, hpt_br⟩ := hpt_inv
  rw [ite_eq_right (not_not.mpr hsm_ph5)] at hpt_br
  dsimp only at hpt_br
  rw [hsm_cur, hsm_nDst, hsm_mbDst, hsm_pDst] at hpt_br
  obtain ⟨_, _, hcur_le_end, hend_le_bm, hend_batch, hrArgs5, hend_fr, hmc_bg, _, hrand_all⟩ :=
    hpt_br
  have hfr_tick : s_tick.frontier = s_grow.frontier := hfr_tick_m.trans hfr_mid
  set x0 := (subroutineCodeWhp c U V w).prepare whpEncode o x
  have hprep_r := prepare_whp_regs (c := c) (V := V) (w := w) o x
  have hx0b : x0.Bounded w :=
    (subroutineCodeWhp c U V w).prepare_bounded hxb
      fun i _ => whpEncode_fits hinv.U_lt hinv.V_le hw11 o hv i
  have hx0_enc : x0.regs rTag = opTag ∧ x0.regs rKey = u.val ∧ x0.regs rVal = v_val := by
    rcases ho_mut with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> exact ⟨rfl, rfl, rfl⟩
  obtain ⟨x8, hpre_ex, hx8_mem, hx8b, hx8_base, hx8_mfr, hx8_fra, hx8_tag, hx8_one,
    _, _, hx8_cur, hx8_end, hx8_mask⟩ :=
    opPrefixCode_exec (L_peak := L_peak) (s := s) (x0 := x0) rfl hw11 hx0b hL_x
      (hprep_r.1.trans hx_base) (hprep_r.2.trans hx_fr)
      hx0_enc.1 hx0_enc.2.1 hx0_enc.2.2 hinv.wf hpre_pg hfr_prep hL_grow hwf_grow hpre_so hfr_tick
  have hx8_fr : x8.frontier = s_tick.frontier := congrArg Memory.State.frontier hx8_mem
  have hres_so5 : (Memory.spec 0).clientResult s_grow
      (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val))) =
      ((0, 0), (metaDst + cur, (metaDst + endOff, 2 ^ w - 1))) :=
    Prod.ext hres1 hrArgs5
  have hadd_end : (metaDst + cur) + (endOff - cur) = metaDst + endOff := by omega
  have hfit_end : Fits w ((metaDst + cur) + (endOff - cur)) := by
    rw [hadd_end]; exact hwf_tick.1.of_le hend_fr
  have hex_rf : ExecRCodeSteps w
      (randFillBatchCode rCur rEnd rMask rRes rOne) x8
      ((PMF.uniformOfFintype (Fin (endOff - cur) → Fin (2 ^ w))).map
        fun ws => ⟨randFillPost (metaDst + cur) x8 ws, 5 * (endOff - cur) + 2, true⟩) L_peak :=
    randFillBatchCode_exec hw_pos whpRand_nodup (endOff - cur) (metaDst + cur) x8
      (by rw [hx8_cur, hres_so5])
      (by rw [hx8_end, hres_so5, hadd_end])
      (by rw [hx8_mask, hres_so5])
      hx8_one (by rw [hx8_fr, hfr_tick]; exact hL_grow)
      (by rw [hadd_end, hx8_fr]; exact hend_fr) hfit_end
  have htail : ∀ ws : Fin (endOff - cur) → Fin (2 ^ w),
      let s_r : Memory.State :=
        { mem := writeWords s_tick.mem (metaDst + cur) ws, frontier := s_tick.frontier }
      let s_ps := (Memory.spec 0).clientState s_r
        (postRandShrinkProg ((base, s_r.frontier), opTag))
      let k_sh := (Memory.spec 0).clientResult s_r
        (postRandShrinkProg ((base, s_r.frontier), opTag))
      let s_post : Memory.State :=
        { mem := clear s_ps.mem (s_r.frontier - k_sh) k_sh, frontier := s_r.frontier - k_sh }
      ∃ (yw : RData rWhp) (Tw : ℕ),
        RDemonicExec w L_peak opSuffixCode (randFillPost (metaDst + cur) x8 ws) Tw (· = yw) ∧
        Tw ≤ wPostRandShrink.factor * 116 + 4 * bulkBatchWhp + 7 ∧
        rMemState yw = s_post ∧
        yw.Bounded w ∧
        yw.regs mBaseWhp = base ∧
        yw.regs mFrWhp = yw.frontier ∧
        whpDecode (V := V) o yw.regs = some ((Dynamic.spec U V U).stepFn s_dict o).2 ∧
        (∀ addr < base, yw.mem addr = x.mem addr) ∧
        (endOff < offBM →
          ∃ L_post : DualLatent c U V,
            PreservesEpochSeeds False False
              { (L.applyFG 5 opTag u v) with elapsed := L.elapsed + 1 } L_post ∧
            DualStateInv c U V w base ((Dynamic.spec U V U).stepFn s_dict o).1 L_post s_post) := by
    intro ws s_r s_ps k_sh s_post
    set xr := randFillPost (metaDst + cur) x8 ws
    obtain ⟨hxrb, hxr_fr, hxr_mem, hxr_regs⟩ :=
      randFillPost_bounded hx8b (by rw [hadd_end, hx8_fr]; exact hend_fr) hfit_end ws
    have hmem_xr : rMemState xr = s_r :=
      Memory.State.ext
        (hxr_mem.trans (congrArg (fun st => writeWords st.mem _ ws) hx8_mem))
        (hxr_fr.trans hx8_fr)
    obtain ⟨hwf_r, hout_r_m, hph_r, hstg_r, hcur_r, hp31_r, hpre_lt, hmid_eq⟩ := hrand_all ws
    have hph_r' : s_r.mem (base + hdrPhase) = 5 := hph_r
    have hstg_r' : s_r.mem (base + hdrStage) = s_mid.mem (base + hdrStage) := hstg_r
    have hcur_r' : s_r.mem (base + hdrCur) = endOff := hcur_r
    have hp31_r' : s_r.mem (dualPDst base s.mem + 31) = offBM := hp31_r
    have hout_r_m' : ∀ addr < base, s_r.mem addr = s_mid.mem addr := hout_r_m
    obtain ⟨hpre_prs, hfr_ps, hk_sh_b, hk_sh_fr, hout_ps, hmc_prs, hlt_inv, hb192_post⟩ :
        PostRandShrinkPre w ((base, s_r.frontier), opTag) s_r ∧
        s_ps.frontier = s_r.frontier ∧
        k_sh ≤ bulkBatchWhp ∧
        k_sh ≤ s_r.frontier ∧
        (∀ addr < base, s_ps.mem addr = s_r.mem addr) ∧
        memoryCost (postRandShrinkProg ((base, s_r.frontier), opTag)) s_r ≤ 115 ∧
        (endOff < offBM →
          ∃ L_post : DualLatent c U V,
            PreservesEpochSeeds False False
              { (L.applyFG 5 opTag u v) with elapsed := L.elapsed + 1 } L_post ∧
            DualStateInv c U V w base ((Dynamic.spec U V U).stepFn s_dict o).1 L_post s_post) ∧
        base + 192 ≤ s_r.frontier - k_sh := by
      by_cases hlt : endOff < offBM
      · obtain ⟨hp1, hp2, hp3, hp4, hp5_o, hp6, L_post, hpres, hinv_p⟩ :=
          postRandShrinkProg_spec_pre hop_nz (hpre_lt hlt)
        rw [hs_dict'_eq] at hinv_p
        have hp6' : memoryCost (postRandShrinkProg ((base, s_r.frontier), opTag)) s_r ≤ 35 := hp6
        have hpres' : PreservesEpochSeeds False False
            { (L.applyFG 5 opTag u v) with elapsed := L.elapsed + 1 } L_post := by
          have hl_eq : L.applyFG (s.mem (base + hdrPhase)) opTag u v = L.applyFG 5 opTag u v :=
            congrArg (fun p => L.applyFG p opTag u v) hp5_s
          have hpres0 : PreservesEpochSeeds False (s_r.mem (base + hdrPhase) = 11 ∧
              s_ps.mem (base + hdrPhase) = 0)
              { (L.applyFG (s.mem (base + hdrPhase)) opTag u v) with
                elapsed := (L.applyFG (s.mem (base + hdrPhase)) opTag u v).elapsed + 1 } L_post :=
            hpres
          have hel5 : (L.applyFG 5 opTag u v).elapsed = L.elapsed := rfl
          rw [hl_eq, hel5, hph_r'] at hpres0
          simpa only [show (5 : ℕ) ≠ 11 by decide, false_and] using hpres0
        exact ⟨hp1, hp2, hp3, hp4, hp5_o, by omega, fun _ => ⟨L_post, hpres', hinv_p⟩,
          hinv_p.base_fr⟩
      · have heq_bm : endOff = offBM := le_antisymm hend_le_bm (Nat.not_lt.mp hlt)
        have hpD_r : dualPDst base s_r.mem = dualPDst base s.mem := by
          unfold dualPDst; rw [hph_r', hstg_r', hsm_stg, hp5_s]
        have hd_r : s_r.mem (dualPDst base s_r.mem + 31) ≤ s_r.mem (base + hdrCur) := by
          rw [hpD_r, hp31_r', hcur_r', heq_bm]
        obtain ⟨hp1, hp2, hp3, hp4, hp5_o, hp6, hinv_rf⟩ :=
          postRandShrinkProg_spec hop_nz (hmid_eq heq_bm) hph_r' hd_r
        exact ⟨hp1, hp2, hp3, hp4, hp5_o, hp6, fun hlt' => absurd hlt' hlt, hinv_rf.base_fr⟩
    obtain ⟨yw, e_suf, hyw_mem, hywb, hyw_base, hyw_mfr, _, _⟩ :=
      opSuffixCode_exec (L_peak := L_peak) (s_r := s_r) (xr := xr) hmem_xr hw11 hxrb
        (hfr_tick.symm ▸ hL_grow)
        ((hxr_regs mBaseWhp (whpReg_ne (by decide)) (whpReg_ne (by decide))).trans hx8_base)
        ((hxr_regs mFrWhp (whpReg_ne (by decide)) (whpReg_ne (by decide))).trans hx8_mfr)
        ((hxr_regs rFrArg (whpReg_ne (by decide)) (whpReg_ne (by decide))).trans hx8_fra)
        ((hxr_regs rTag (whpReg_ne (by decide)) (whpReg_ne (by decide))).trans hx8_tag)
        hwf_r hpre_prs hfr_ps hk_sh_fr
    refine ⟨yw, _, e_suf, ?_, hyw_mem, hywb, hyw_base, hyw_mfr, ?_, ?_, hlt_inv⟩
    · have h3 : wPostRandShrink.factor *
          (memoryCost (postRandShrinkProg ((base, s_r.frontier), opTag)) s_r + 1) ≤
          wPostRandShrink.factor * 116 := Nat.mul_le_mul_left _ (by omega)
      omega
    · rcases ho_mut with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
    · intro addr hlt_a
      have heq_m := congrArg (fun st => st.mem addr) hyw_mem
      dsimp only [rMemState, s_post] at heq_m
      rw [heq_m, clear_of_not_owns (by simp only [Block.Owns]; omega),
        hout_ps addr hlt_a, hout_r_m' addr hlt_a, hout_mid addr hlt_a]
  classical
  let y_fn := fun ws => (htail ws).choose
  let T_tail := fun ws => (htail ws).choose_spec.choose
  have htail_spec := fun ws => (htail ws).choose_spec.choose_spec
  let extractWs : RData rWhp → (Fin (endOff - cur) → Fin (2 ^ w)) :=
    fun d i => wordOfNat w (d.mem ((metaDst + cur) + i.val))
  have hextract_post : ∀ ws : Fin (endOff - cur) → Fin (2 ^ w),
      extractWs (randFillPost (metaDst + cur) x8 ws) = ws := fun ws => by
    funext i; apply Fin.ext
    dsimp only [extractWs, randFillPost]
    rw [writeWords_apply_in _ _ _ i.isLt]
    exact wordOfNat_val_of_lt (ws i).isLt
  have hex_rf_tail : ExecRCodeSteps w
      (.seq (randFillBatchCode rCur rEnd rMask rRes rOne) opSuffixCode) x8
      ((PMF.uniformOfFintype (Fin (endOff - cur) → Fin (2 ^ w))).map
        fun ws => ⟨y_fn ws, (5 * (endOff - cur) + 2) + T_tail ws, true⟩) L_peak := by
    have hseq := ExecRCodeSteps.seq hex_rf
      (μ₂ := fun z => PMF.pure ⟨y_fn (extractWs z.data), T_tail (extractWs z.data), true⟩)
      fun z hz => by
        rw [PMF.mem_support_map_iff] at hz; obtain ⟨ws, _, rfl⟩ := hz
        dsimp only; rw [hextract_post ws]
        exact ExecRCodeSteps.of_demonicExec (htail_spec ws).1
    refine hseq.congr_dist ?_
    rw [PMF.bind_map]
    unfold PMF.map
    refine congrArg (PMF.bind _) (funext fun ws => ?_)
    dsimp only [Function.comp_def]
    rw [PMF.pure_bind, hextract_post ws]
    rfl
  have hex_full := hpre_ex _ _ hex_rf_tail
  simp only [PMF.map_comp, Function.comp_def] at hex_full
  refine ⟨y_fn, _, hex_full, fun ws => ?_⟩
  obtain ⟨_, hTw_le, hyw_mem, hywb, hyw_base, hyw_mfr, hyw_dec, hyw_out, hyw_lt⟩ := htail_spec ws
  refine ⟨hyw_mem, hywb, hyw_base, hyw_mfr, hyw_dec, hyw_out, hyw_lt, fun hgc => ?_⟩
  have hgc' : (L.applyFG (s.mem (base + hdrPhase)) opTag u v).slotSrc.GoodCovers :=
    hp5_s.symm ▸ hgc
  have hc_um := hmc_um (fun _ => hgc') (fun h8 => absurd (hp5_s.symm.trans h8) (by decide))
    (fun h9 => absurd (hp5_s ▸ h9) (by decide))
  have hc_so : memoryCost (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val))) s_grow ≤
      (2 * epochStepCost c + 80) + (itemBatchWhp * (2 * epochStepCost c + 20) + 20000) := by
    rw [hmc_so_eq]; omega
  have hmc_pg' : memoryCost (prepGrowProg (((base, s.frontier), opTag), u.val)) s ≤ 40 := hmc_pg
  have hk_b' : k_grow ≤ bulkBatchWhp := hk_grow_b
  have hTw' : T_tail ws ≤ wPostRandShrink.factor * 116 + 4 * bulkBatchWhp + 7 := hTw_le
  have he_b' : endOff - cur ≤ bulkBatchWhp := by
    dsimp only [endOff]
    rw [Nat.add_sub_cancel_left]
    exact Nat.min_le_left _ _
  have h1 : wPrepGrow.factor *
      (memoryCost (prepGrowProg (((base, s.frontier), opTag), u.val)) s + 1) ≤
      wPrepGrow.factor * 41 := Nat.mul_le_mul_left _ (by omega)
  have h2 : wStepOp.factor *
      (memoryCost (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val))) s_grow + 1) ≤
      wStepOp.factor *
        ((2 * epochStepCost c + 80) + (itemBatchWhp * (2 * epochStepCost c + 20) + 20000) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  change (1 + (wPrepGrow.factor *
      (memoryCost (prepGrowProg (((base, s.frontier), opTag), u.val)) s + 1) +
      (1 + ((5 * k_grow + 6) + (1 + (1 + (wStepOp.factor *
        (memoryCost (stepOpProg (((base, s_grow.frontier), opTag), (u.val, v_val))) s_grow + 1) +
          5))))))) +
    ((5 * (endOff - cur) + 2) + T_tail ws) ≤ worstCaseTimeWhp c
  unfold worstCaseTimeWhp
  omega

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
