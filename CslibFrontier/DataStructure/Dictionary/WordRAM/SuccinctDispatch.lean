/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctHash
public import CslibFrontier.DataStructure.WordRAM.Randomized.StateTransition
import CslibFrontier.Tactic.FinIndex

/-!
# Register Wiring and Per-Operation Native Dispatch for the Succinct Dictionary

This module wires the five parameter-free `Realizes .exact` certificates from `SuccinctHash.lean`
(`realizes_extractQuotGen`, `realizes_queryWithHashGen`, `realizes_insertWithHashGen`,
`realizes_deletePrepWithHashGen`, `realizes_deleteFinishWithHashGen`) together with
`loadParamsCode`, `ReducedKWise.evalCode`, `ReducedKWise.initTableCode`, and
`ReducedKWise.resampleCode` into a single `SubroutineCode` (`subroutineCode U V w n_max`) on a
parameter-free constant number of registers `rSuccinct`, and proves the unified per-operation
deterministic execution theorem (`exec_opCode`) with a parameter-free `O(1)` amortized instruction
charge `chargeVal`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.rSuccinct`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.opFactor`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.chargeVal`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.charge`:
  parameter-free register budget, exchange factor dominating the five `Realizes` certificates, and
  per-operation amortized instruction charge.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.opCode`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.subroutineCode`:
  native Word-RAM operation dispatch code and `SubroutineCode` record.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.Rep`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.potential`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.encode`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.argMatch`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.decode`:
  concrete Word-RAM representation invariant, scaled potential, and ABI register conventions.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.le_rSuccinct`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.one_le_opFactor`:
  basic bounds on `rSuccinct` (`292 ≤ rSuccinct`) and `opFactor` (`1 ≤ opFactor`).
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.fits_mkDictParams`:
  every entry of `mkDictParams U V w n_max (hashSpace U w n_max)` fits in a `w`-bit word.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.exec_opCode`:
  unified per-operation deterministic execution of `opCode` for any `o : Dynamic.Op U`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.Probability
open Finset

/-! ## Section 1: Parameter-free register layout, scratch bank, and exchange factor -/

/-- Combined parameter-free scratch register bank size for the five `Realizes` certificates used in
operation dispatch. -/
@[expose]
noncomputable def scratchSuccinct : ℕ :=
  max (1 + realizes_extractQuotGen.scratchSize + 1)
    (max (2 + realizes_queryWithHashGen.scratchSize + 1)
      (max (0 + realizes_insertWithHashGen.scratchSize + 1)
        (max (4 + realizes_deletePrepWithHashGen.scratchSize + 1)
          (0 + realizes_deleteFinishWithHashGen.scratchSize + 1))))

/-- Parameter-free total register count `292 + scratchSuccinct` for the succinct dictionary
subroutine (`0..239` for `ReducedKWise`, `240..255` for fixed control/input/output registers,
`256..291` for the 36 runtime `DictParams` registers `paramReg`, and `292..` for scratch). -/
@[expose]
noncomputable def rSuccinct : ℕ :=
  292 + scratchSuccinct

theorem le_rSuccinct : 292 ≤ rSuccinct := by
  dsimp only [rSuccinct]
  omega

/-- Canonical embedding `Fin 292 → Fin rSuccinct` for fixed control, hash, and parameter
registers. -/
@[expose]
noncomputable def sReg : Fin 292 → Fin rSuccinct :=
  Fin.castLE le_rSuccinct

theorem sReg_injective : Function.Injective sReg :=
  Fin.castLE_injective le_rSuccinct

@[simp]
theorem sReg_inj {i j : Fin 292} :
    sReg i = sReg j ↔ i = j :=
  sReg_injective.eq_iff

@[simp]
theorem val_sReg (i : Fin 292) :
    (sReg i).val = i.val := rfl

theorem sReg_ne {i j : Fin 292} (h : i ≠ j) :
    sReg i ≠ sReg j :=
  fun heq => h (sReg_injective heq)

@[simp]
theorem update_sReg (f : Fin rSuccinct → ℕ)
    (j : Fin 292) (v : ℕ) (i : Fin 292) :
    Function.update f (sReg j) v (sReg i) =
      if i = j then v else f (sReg i) := by
  simp only [Function.update_apply, sReg_inj]

/-- Combined parameter-free exchange factor `≥ 1` dominating the five `Realizes.factor`
constants. -/
@[expose]
noncomputable def opFactor : ℕ :=
  max 1
    (max realizes_extractQuotGen.factor
      (max realizes_queryWithHashGen.factor
        (max realizes_insertWithHashGen.factor
          (max realizes_deletePrepWithHashGen.factor
            realizes_deleteFinishWithHashGen.factor))))

theorem one_le_opFactor : 1 ≤ opFactor :=
  le_max_left _ _

theorem factor_extractQuot_le :
    realizes_extractQuotGen.factor ≤ opFactor := by
  unfold opFactor; omega

theorem factor_queryWithHash_le :
    realizes_queryWithHashGen.factor ≤ opFactor := by
  unfold opFactor; omega

theorem factor_insertWithHash_le :
    realizes_insertWithHashGen.factor ≤ opFactor := by
  unfold opFactor; omega

theorem factor_deletePrepWithHash_le :
    realizes_deletePrepWithHashGen.factor ≤ opFactor := by
  unfold opFactor; omega

theorem factor_deleteFinishWithHash_le :
    realizes_deleteFinishWithHashGen.factor ≤ opFactor := by
  unfold opFactor; omega

/-- Embed a `ReducedKWise` register `i : Fin 240` into `Fin rSuccinct`. -/
@[expose]
noncomputable def coreReg : Fin 240 → Fin rSuccinct :=
  Fin.castLE (by dsimp only [rSuccinct]; omega)

theorem coreReg_injective : Function.Injective coreReg :=
  Fin.castLE_injective _

@[simp]
theorem val_coreReg (i : Fin 240) :
    (coreReg i).val = i.val := rfl

theorem notMem_range_coreReg {r : Fin rSuccinct}
    (hr : 240 ≤ r.val) : r ∉ Set.range coreReg := by
  rintro ⟨i, rfl⟩
  fin_index [coreReg]

/-- Persistent base-address register `0` (`sReg 0`). -/
noncomputable abbrev baseReg : Fin rSuccinct := sReg 0

/-- Hash input register `1` (`sReg 1`). -/
noncomputable abbrev hashKeyReg : Fin rSuccinct := sReg 1

/-- Hash output register `2` (`sReg 2`). -/
noncomputable abbrev hashOutReg : Fin rSuccinct := sReg 2

/-- Bump-pointer frontier register `240` (`sReg 240`). -/
noncomputable abbrev frontierReg : Fin rSuccinct := sReg 240

/-- Scratch pointer register `241` for `zeroFillCode` and `allocSpan`. -/
noncomputable abbrev curReg : Fin rSuccinct := sReg 241

/-- Constant-`0` scratch register `242` for `zeroFillCode` and operation dispatch. -/
noncomputable abbrev zeroReg : Fin rSuccinct := sReg 242

/-- Constant-`1` scratch register `243` for `zeroFillCode` and operation dispatch. -/
noncomputable abbrev oneReg : Fin rSuccinct := sReg 243

/-- Input operation-tag register `244` (`0` = `query`, `1` = `insert`, `2` = `delete`). -/
noncomputable abbrev tagReg : Fin rSuccinct := sReg 244

/-- Input key register `245` (`u.val`). -/
noncomputable abbrev argUReg : Fin rSuccinct := sReg 245

/-- Input value register `246` (`v` for `insert`, `0` otherwise). -/
noncomputable abbrev argVReg : Fin rSuccinct := sReg 246

/-- Nominal output register `247` for `SubroutineCode.output`. -/
noncomputable abbrev outReg : Fin rSuccinct := sReg 247

/-- Register `248` saving the first hash evaluation `h_q` across the second hash call in
`delete`. -/
noncomputable abbrev hqReg : Fin rSuccinct := sReg 248

/-- Register `249` storing `found` from `deletePrepWithHashGenProg`. -/
noncomputable abbrev foundReg : Fin rSuccinct := sReg 249

/-- Register `250` storing `j_del` from `deletePrepWithHashGenProg`. -/
noncomputable abbrev jDelReg : Fin rSuccinct := sReg 250

/-- Register `251` storing `phys_del` from `deletePrepWithHashGenProg`. -/
noncomputable abbrev physDelReg : Fin rSuccinct := sReg 251

/-- Register `252` storing the `Option ℕ` presence tag (`0` = `none`, `1` = `some`) from
`queryWithHashGenProg`. -/
noncomputable abbrev resTagReg : Fin rSuccinct := sReg 252

/-- Register `253` storing the `Option ℕ` payload value `v` from `queryWithHashGenProg`. -/
noncomputable abbrev resValReg : Fin rSuccinct := sReg 253

/-- Register block `256..291` holding the 36 words of `DictParams`. -/
@[expose]
noncomputable def paramReg (i : Fin 36) : Fin rSuccinct :=
  sReg ⟨256 + i.val, by omega⟩

@[simp]
theorem val_paramReg (i : Fin 36) :
    (paramReg i).val = 256 + i.val := rfl

/-! ## Section 2: Register wirings (`src*`, `tmp*`), `loadParamsCode`, and emitted native code -/

/-- Load entries `0 .. k` (`k < 36`) of `dp : DictParams` into `paramReg 0 .. paramReg k` in
`k + 1` instructions. -/
noncomputable def loadParamsUpTo (dp : DictParams) : (k : ℕ) → k < 36 → Code .exact rSuccinct
  | 0, hk => .op (.const (paramReg ⟨0, hk⟩) (dp ⟨0, hk⟩))
  | k + 1, hk =>
    .seq (loadParamsUpTo dp k (by omega))
         (.op (.const (paramReg ⟨k + 1, hk⟩) (dp ⟨k + 1, hk⟩)))

/-- Load all 36 words of `mkDictParams U V w n_max (hashSpace U w n_max)` into `paramReg 0 .. 35`
in 36 instructions. -/
@[expose]
noncomputable def loadParamsCode (U V w n_max : ℕ) : Code .exact rSuccinct :=
  loadParamsUpTo (mkDictParams U V w n_max (hashSpace U w n_max)) 35 (by decide)

/-- Payload source register wiring `![argUReg]` for `extractQuotGenProg`. -/
@[expose]
noncomputable def srcExtD : Fin 1 → Fin rSuccinct :=
  ![argUReg]

/-- Full source register wiring `Fin.append paramReg srcExtD` for `extractQuotGenProg`. -/
@[expose]
noncomputable def srcExt : Fin (36 + 1) → Fin rSuccinct :=
  Fin.append paramReg srcExtD

@[simp]
theorem val_srcExtD (i : Fin 1) : (srcExtD i).val = 245 := by
  fin_cases i; rfl

/-- Scratch/output register wiring for `extractQuotGenProg`, placing output `0` directly in
`hashKeyReg` (`1`) and remaining scratch registers at `292 + j.val`. -/
@[expose]
noncomputable def tmpExt
    (j : Fin (1 + realizes_extractQuotGen.scratchSize + 1)) : Fin rSuccinct :=
  if j.val = 0 then hashKeyReg
  else ⟨292 + j.val, by have := j.isLt; dsimp only [rSuccinct, scratchSuccinct]; omega⟩

@[simp]
theorem val_tmpExt (j : Fin (1 + realizes_extractQuotGen.scratchSize + 1)) :
    (tmpExt j).val = if j.val = 0 then 1 else 292 + j.val := by
  dsimp only [tmpExt]
  split_ifs <;> rfl

/-- Emitted native code for `extractQuotGenProg`. -/
@[expose]
noncomputable def extCode : Code .exact rSuccinct :=
  realizes_extractQuotGen.code frontierReg srcExt tmpExt

/-- Payload source register wiring `![baseReg, argUReg, hashOutReg]` for `queryWithHashGenProg`. -/
@[expose]
noncomputable def srcQryD : Fin 3 → Fin rSuccinct :=
  ![baseReg, argUReg, hashOutReg]

/-- Full source register wiring `Fin.append paramReg srcQryD` for `queryWithHashGenProg`. -/
@[expose]
noncomputable def srcQry : Fin (36 + 3) → Fin rSuccinct :=
  Fin.append paramReg srcQryD

@[simp]
theorem val_srcQryD (i : Fin 3) :
    (srcQryD i).val = if i.val = 0 then 0 else if i.val = 1 then 245 else 2 := by
  fin_cases i <;> rfl

/-- Scratch/output register wiring for `queryWithHashGenProg`, placing outputs `0, 1` in
`resTagReg` (`252`) and `resValReg` (`253`). -/
@[expose]
noncomputable def tmpQry
    (j : Fin (2 + realizes_queryWithHashGen.scratchSize + 1)) : Fin rSuccinct :=
  if j.val = 0 then resTagReg
  else if j.val = 1 then resValReg
  else ⟨292 + j.val, by have := j.isLt; dsimp only [rSuccinct, scratchSuccinct]; omega⟩

@[simp]
theorem val_tmpQry (j : Fin (2 + realizes_queryWithHashGen.scratchSize + 1)) :
    (tmpQry j).val = if j.val = 0 then 252 else if j.val = 1 then 253 else 292 + j.val := by
  dsimp only [tmpQry]
  split_ifs <;> rfl

/-- Emitted native code for `queryWithHashGenProg`. -/
@[expose]
noncomputable def qryCode : Code .exact rSuccinct :=
  realizes_queryWithHashGen.code frontierReg srcQry tmpQry

/-- Payload source register wiring `![baseReg, argUReg, argVReg, hashOutReg]` for
`insertWithHashGenProg`. -/
@[expose]
noncomputable def srcInsD : Fin 4 → Fin rSuccinct :=
  ![baseReg, argUReg, argVReg, hashOutReg]

/-- Full source register wiring `Fin.append paramReg srcInsD` for `insertWithHashGenProg`. -/
@[expose]
noncomputable def srcIns : Fin (36 + 4) → Fin rSuccinct :=
  Fin.append paramReg srcInsD

@[simp]
theorem val_srcInsD (i : Fin 4) :
    (srcInsD i).val =
      if i.val = 0 then 0 else if i.val = 1 then 245 else if i.val = 2 then 246 else 2 := by
  fin_cases i <;> rfl

/-- Scratch register wiring for `insertWithHashGenProg` at `292 + j.val`. -/
@[expose]
noncomputable def tmpIns
    (j : Fin (0 + realizes_insertWithHashGen.scratchSize + 1)) : Fin rSuccinct :=
  ⟨292 + j.val, by have := j.isLt; dsimp only [rSuccinct, scratchSuccinct]; omega⟩

@[simp]
theorem val_tmpIns (j : Fin (0 + realizes_insertWithHashGen.scratchSize + 1)) :
    (tmpIns j).val = 292 + j.val := rfl

/-- Emitted native code for `insertWithHashGenProg`. -/
@[expose]
noncomputable def insCode : Code .exact rSuccinct :=
  realizes_insertWithHashGen.code frontierReg srcIns tmpIns

/-- Payload source register wiring `![baseReg, argUReg, hqReg]` for `deletePrepWithHashGenProg`. -/
@[expose]
noncomputable def srcDelPrepD : Fin 3 → Fin rSuccinct :=
  ![baseReg, argUReg, hqReg]

/-- Full source register wiring `Fin.append paramReg srcDelPrepD` for
`deletePrepWithHashGenProg`. -/
@[expose]
noncomputable def srcDelPrep : Fin (36 + 3) → Fin rSuccinct :=
  Fin.append paramReg srcDelPrepD

@[simp]
theorem val_srcDelPrepD (i : Fin 3) :
    (srcDelPrepD i).val = if i.val = 0 then 0 else if i.val = 1 then 245 else 248 := by
  fin_cases i <;> rfl

/-- Scratch/output register wiring for `deletePrepWithHashGenProg`, placing outputs `0..3` in
`foundReg` (`249`), `jDelReg` (`250`), `physDelReg` (`251`), and `hashKeyReg` (`1`). -/
@[expose]
noncomputable def tmpDelPrep
    (j : Fin (4 + realizes_deletePrepWithHashGen.scratchSize + 1)) : Fin rSuccinct :=
  if j.val = 0 then foundReg
  else if j.val = 1 then jDelReg
  else if j.val = 2 then physDelReg
  else if j.val = 3 then hashKeyReg
  else ⟨292 + j.val, by have := j.isLt; dsimp only [rSuccinct, scratchSuccinct]; omega⟩

@[simp]
theorem val_tmpDelPrep (j : Fin (4 + realizes_deletePrepWithHashGen.scratchSize + 1)) :
    (tmpDelPrep j).val =
      if j.val = 0 then 249
      else if j.val = 1 then 250
      else if j.val = 2 then 251
      else if j.val = 3 then 1
      else 292 + j.val := by
  dsimp only [tmpDelPrep]
  split_ifs <;> rfl

/-- Emitted native code for `deletePrepWithHashGenProg`. -/
@[expose]
noncomputable def delPrepCode : Code .exact rSuccinct :=
  realizes_deletePrepWithHashGen.code frontierReg srcDelPrep tmpDelPrep

/-- Payload source register wiring
`![baseReg, argUReg, hqReg, foundReg, jDelReg, physDelReg, hashOutReg]` for
`deleteFinishWithHashGenProg`. -/
@[expose]
noncomputable def srcDelFinD : Fin 7 → Fin rSuccinct :=
  ![baseReg, argUReg, hqReg, foundReg, jDelReg, physDelReg, hashOutReg]

/-- Full source register wiring `Fin.append paramReg srcDelFinD` for
`deleteFinishWithHashGenProg`. -/
@[expose]
noncomputable def srcDelFin : Fin (36 + 7) → Fin rSuccinct :=
  Fin.append paramReg srcDelFinD

@[simp]
theorem val_srcDelFinD (i : Fin 7) :
    (srcDelFinD i).val =
      if i.val = 0 then 0
      else if i.val = 1 then 245
      else if i.val = 2 then 248
      else if i.val = 3 then 249
      else if i.val = 4 then 250
      else if i.val = 5 then 251
      else 2 := by
  fin_cases i <;> rfl

/-- Scratch register wiring for `deleteFinishWithHashGenProg` at `292 + j.val`. -/
@[expose]
noncomputable def tmpDelFin
    (j : Fin (0 + realizes_deleteFinishWithHashGen.scratchSize + 1)) : Fin rSuccinct :=
  ⟨292 + j.val, by have := j.isLt; dsimp only [rSuccinct, scratchSuccinct]; omega⟩

@[simp]
theorem val_tmpDelFin (j : Fin (0 + realizes_deleteFinishWithHashGen.scratchSize + 1)) :
    (tmpDelFin j).val = 292 + j.val := rfl

/-- Emitted native code for `deleteFinishWithHashGenProg`. -/
@[expose]
noncomputable def delFinCode : Code .exact rSuccinct :=
  realizes_deleteFinishWithHashGen.code frontierReg srcDelFin tmpDelFin

/-- Native quotient hash evaluation code `(ReducedKWise.evalCode ...).rename coreReg`. -/
@[expose]
noncomputable def hashEvalCode (U w n_max : ℕ) : Code .exact rSuccinct :=
  (ReducedKWise.evalCode w (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3).rename coreReg

/-- Complete `delete` branch code: saves `h_q` into `hqReg`, runs `delPrepCode` (which puts `q_last`
into `hashKeyReg`), evaluates `h_q_last` via `hashEvalCode`, and runs `delFinCode`. -/
@[expose]
noncomputable def delCode (U w n_max : ℕ) : Code .exact rSuccinct :=
  .seq (.op (.copy hqReg hashOutReg))
  (.seq delPrepCode
  (.seq (hashEvalCode U w n_max)
        delFinCode))

/-- Complete operation dispatch code for `subroutineCode`: loads `DictParams` into `paramReg`,
extracts `q`, evaluates `h_q`, and branches on `tagReg` between `qryCode`, `insCode`, and
`delCode`. -/
@[expose]
noncomputable def opCode (U V w n_max : ℕ) : Code .exact rSuccinct :=
  .seq (loadParamsCode U V w n_max)
  (.seq extCode
  (.seq (hashEvalCode U w n_max)
  (.seq (.op (.const zeroReg 0))
  (.branch (.eq tagReg zeroReg)
    qryCode
    (.seq (.op (.const oneReg 1))
    (.branch (.eq tagReg oneReg)
      insCode
      (delCode U w n_max)))))))

/-- Canonical `SubroutineCode` for the fixed-capacity succinct dynamic dictionary on `rSuccinct`
registers. Note that `subroutineCode U V w n_max` depends on the static parameters
`(U, V, w, n_max)` (through `space`, `loadParamsCode`, and `ReducedKWise` bit-width constants) and
is independent of `base`. -/
@[expose]
noncomputable def subroutineCode (U V w n_max : ℕ) :
    SubroutineCode .exact rSuccinct 0 where
  allocSpan :=
    .seq (.op (.copy baseReg frontierReg))
    (.seq (.op (.const curReg (space U V w n_max)))
          (.op (.exactBin .add frontierReg frontierReg curReg)))
  initSetup :=
    .seq ((ReducedKWise.initTableCode w (qBits U n_max) (hashB n_max)
            (totalMicroBits n_max) 3).rename coreReg)
         ((ReducedKWise.resampleCode (qBits U n_max) (hashB n_max)
            (totalMicroBits n_max) 3).rename coreReg)
  code := opCode U V w n_max
  frontierReg := frontierReg
  baseReg := baseReg
  initParams := Fin.elim0
  curReg := curReg
  zeroReg := zeroReg
  oneReg := oneReg
  incCur := .exactBin .add curReg curReg oneReg
  input r := decide (r = tagReg ∨ r = argUReg ∨ r = argVReg)
  output := outReg

/-! ## Section 3: Generic register-wiring disjointness and encoding helpers -/

/-- Generic disjointness between `Fin.append paramReg srcD` and `tmp` whenever `tmp` maps every
index outside `[256, 292)` and is disjoint from `srcD`. -/
theorem append_paramReg_ne_tmp {k m : ℕ} (srcD : Fin k → Fin rSuccinct)
    (tmp : Fin m → Fin rSuccinct)
    (htmp_out : ∀ j : Fin m, (tmp j).val < 256 ∨ 292 ≤ (tmp j).val)
    (hd : ∀ (i : Fin k) (j : Fin m), srcD i ≠ tmp j) :
    ∀ (i : Fin (36 + k)) (j : Fin m), Fin.append paramReg srcD i ≠ tmp j :=
  fun i j => i.addCases
    (fun i₀ => by have := htmp_out j; fin_index [val_paramReg])
    (fun i₁ => by have := hd i₁ j; fin_index)

/-- Generic disjointness between `Fin.append paramReg srcD` and `frontierReg` (`240`). -/
theorem append_paramReg_ne_frontier {k : ℕ} (srcD : Fin k → Fin rSuccinct)
    (hf : ∀ i : Fin k, (srcD i).val ≠ 240) :
    ∀ i : Fin (36 + k), Fin.append paramReg srcD i ≠ frontierReg :=
  fun i => i.addCases
    (fun i₀ => by fin_index [val_paramReg, frontierReg, val_sReg])
    (fun i₁ => by have := hf i₁; fin_index [frontierReg, val_sReg])

/-- Composing `x.regs` with `Fin.append paramReg srcD` yields `WordEncoding.encode (dp, d)`. -/
theorem regs_comp_append_paramReg {D : Type} [WordEncoding D]
    {x : Data rSuccinct} {dp : DictParams} (d : D)
    (srcD : Fin (WordEncoding.width D) → Fin rSuccinct)
    (hp : ∀ i : Fin 36, x.regs (paramReg i) = dp i)
    (hd : ∀ i : Fin (WordEncoding.width D), x.regs (srcD i) = WordEncoding.encode d i) :
    x.regs ∘ Fin.append paramReg srcD =
      WordEncoding.encode (α := DictParams × D) (dp, d) :=
  funext fun i => i.addCases
    (fun j => (congrArg x.regs (Fin.append_left _ _ j)).trans
      ((hp j).trans (Fin.append_left (WordEncoding.encode dp) (WordEncoding.encode d) j).symm))
    (fun j => (congrArg x.regs (Fin.append_right _ _ j)).trans
      ((hd j).trans (Fin.append_right (WordEncoding.encode dp) (WordEncoding.encode d) j).symm))

/-- Layout characterization for `tmp*` scratch/output register wirings: outputs occupy distinct
registers below `256` in `outs`, and remaining indices map to `292 + j.val`. -/
private structure TmpLayout (outs : List ℕ) {m : ℕ} (tmp : Fin m → Fin rSuccinct) : Prop where
  /-- Output register indices are pairwise distinct. -/
  nodup : outs.Nodup
  /-- Output register indices sit below the `paramReg` block `[256, 292)`. -/
  lt_256 : ∀ x ∈ outs, x < 256
  /-- Register-index formula for `tmp j`. -/
  val : ∀ j : Fin m,
    (tmp j).val = if h : j.val < outs.length then outs[j.val] else 292 + j.val

private theorem injective_of_tmpLayout {outs : List ℕ} {m : ℕ} {tmp : Fin m → Fin rSuccinct}
    (ht : TmpLayout outs tmp) : Function.Injective tmp := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [ht.val a, ht.val b] at hv
  split_ifs at hv with ha hb hb
  · exact Fin.ext ((ht.nodup.getElem_inj_iff).mp hv)
  · have := ht.lt_256 outs[a.val] (List.getElem_mem ha); omega
  · have := ht.lt_256 outs[b.val] (List.getElem_mem hb); omega
  · exact Fin.ext (by omega)

private theorem tmp_ne_sReg_of_tmpLayout {outs : List ℕ} {m : ℕ} {tmp : Fin m → Fin rSuccinct}
    (ht : TmpLayout outs tmp) {i : Fin 292} (hi : i.val ∉ outs) (j : Fin m) :
    tmp j ≠ sReg i := by
  intro h
  have hv := congrArg Fin.val h
  rw [ht.val j, val_sReg] at hv
  split_ifs at hv with hj
  · exact hi (hv ▸ List.getElem_mem hj)
  · have := i.isLt; omega

private theorem append_paramReg_ne_tmp_of_layout {outs : List ℕ} {k m : ℕ}
    {srcD : Fin k → Fin rSuccinct} {tmp : Fin m → Fin rSuccinct}
    (ht : TmpLayout outs tmp)
    (hsrc : ∀ i : Fin k, (srcD i).val < 292 ∧ (srcD i).val ∉ outs) :
    ∀ (i : Fin (36 + k)) (j : Fin m), Fin.append paramReg srcD i ≠ tmp j := by
  refine append_paramReg_ne_tmp srcD tmp (fun j => ?_) (fun i₁ j h => ?_)
  · rw [ht.val j]
    split_ifs with hj
    · exact Or.inl (ht.lt_256 _ (List.getElem_mem hj))
    · exact Or.inr (by omega)
  · have hv := congrArg Fin.val h
    rw [ht.val j] at hv
    split_ifs at hv with hj
    · exact (hsrc i₁).2 (hv ▸ List.getElem_mem hj)
    · have := (hsrc i₁).1; omega

private theorem regs_sReg_of_frame {outs : List ℕ} {m : ℕ} {tmp : Fin m → Fin rSuccinct}
    (ht : TmpLayout outs tmp) {x y : Data rSuccinct}
    (hframe : ∀ i, i ≠ frontierReg → (∀ j, tmp j ≠ i) → y.regs i = x.regs i)
    {i : Fin 292} (hfr : i ≠ 240) (hout : i.val ∉ outs) :
    y.regs (sReg i) = x.regs (sReg i) :=
  hframe (sReg i) (sReg_ne hfr) (tmp_ne_sReg_of_tmpLayout ht hout)

private theorem tmpLayout_tmpExt : TmpLayout [1] tmpExt :=
  ⟨by decide, by decide, fun j => by
    rw [val_tmpExt]; rcases j with ⟨_ | _, _⟩ <;> rfl⟩

private theorem tmpLayout_tmpQry : TmpLayout [252, 253] tmpQry :=
  ⟨by decide, by decide, fun j => by
    rw [val_tmpQry]; rcases j with ⟨_ | _ | _, _⟩ <;> rfl⟩

private theorem tmpLayout_tmpIns : TmpLayout [] tmpIns :=
  ⟨by decide, by decide, fun j => by rw [val_tmpIns]; rfl⟩

private theorem tmpLayout_tmpDelPrep : TmpLayout [249, 250, 251, 1] tmpDelPrep :=
  ⟨by decide, by decide, fun j => by
    rw [val_tmpDelPrep]; rcases j with ⟨_ | _ | _ | _ | _, _⟩ <;> rfl⟩

private theorem tmpLayout_tmpDelFin : TmpLayout [] tmpDelFin :=
  ⟨by decide, by decide, fun j => by rw [val_tmpDelFin]; rfl⟩

theorem tmpExt_injective : Function.Injective tmpExt :=
  injective_of_tmpLayout tmpLayout_tmpExt

theorem srcExt_ne_tmpExt (i : Fin (36 + 1))
    (j : Fin (1 + realizes_extractQuotGen.scratchSize + 1)) :
    srcExt i ≠ tmpExt j :=
  append_paramReg_ne_tmp_of_layout tmpLayout_tmpExt
    (fun i₁ => by rw [val_srcExtD]; decide) i j

theorem tmpExt_ne_frontier (j : Fin (1 + realizes_extractQuotGen.scratchSize + 1)) :
    tmpExt j ≠ frontierReg :=
  tmp_ne_sReg_of_tmpLayout tmpLayout_tmpExt (by decide) j

theorem srcExt_ne_frontier (i : Fin (36 + 1)) :
    srcExt i ≠ frontierReg :=
  append_paramReg_ne_frontier srcExtD (fun i₁ => by rw [val_srcExtD]; decide) i

theorem tmpQry_injective : Function.Injective tmpQry :=
  injective_of_tmpLayout tmpLayout_tmpQry

theorem srcQry_ne_tmpQry (i : Fin (36 + 3))
    (j : Fin (2 + realizes_queryWithHashGen.scratchSize + 1)) :
    srcQry i ≠ tmpQry j :=
  append_paramReg_ne_tmp_of_layout tmpLayout_tmpQry
    (fun i₁ => by rw [val_srcQryD]; split_ifs <;> decide) i j

theorem tmpQry_ne_frontier (j : Fin (2 + realizes_queryWithHashGen.scratchSize + 1)) :
    tmpQry j ≠ frontierReg :=
  tmp_ne_sReg_of_tmpLayout tmpLayout_tmpQry (by decide) j

theorem srcQry_ne_frontier (i : Fin (36 + 3)) :
    srcQry i ≠ frontierReg :=
  append_paramReg_ne_frontier srcQryD (fun i₁ => by rw [val_srcQryD]; split_ifs <;> omega) i

theorem tmpIns_injective : Function.Injective tmpIns :=
  injective_of_tmpLayout tmpLayout_tmpIns

theorem srcIns_ne_tmpIns (i : Fin (36 + 4))
    (j : Fin (0 + realizes_insertWithHashGen.scratchSize + 1)) :
    srcIns i ≠ tmpIns j :=
  append_paramReg_ne_tmp_of_layout tmpLayout_tmpIns
    (fun i₁ => by rw [val_srcInsD]; split_ifs <;> decide) i j

theorem tmpIns_ne_frontier (j : Fin (0 + realizes_insertWithHashGen.scratchSize + 1)) :
    tmpIns j ≠ frontierReg :=
  tmp_ne_sReg_of_tmpLayout tmpLayout_tmpIns (by decide) j

theorem srcIns_ne_frontier (i : Fin (36 + 4)) :
    srcIns i ≠ frontierReg :=
  append_paramReg_ne_frontier srcInsD (fun i₁ => by rw [val_srcInsD]; split_ifs <;> omega) i

theorem tmpDelPrep_injective : Function.Injective tmpDelPrep :=
  injective_of_tmpLayout tmpLayout_tmpDelPrep

theorem srcDelPrep_ne_tmpDelPrep (i : Fin (36 + 3))
    (j : Fin (4 + realizes_deletePrepWithHashGen.scratchSize + 1)) :
    srcDelPrep i ≠ tmpDelPrep j :=
  append_paramReg_ne_tmp_of_layout tmpLayout_tmpDelPrep
    (fun i₁ => by rw [val_srcDelPrepD]; split_ifs <;> decide) i j

theorem tmpDelPrep_ne_frontier (j : Fin (4 + realizes_deletePrepWithHashGen.scratchSize + 1)) :
    tmpDelPrep j ≠ frontierReg :=
  tmp_ne_sReg_of_tmpLayout tmpLayout_tmpDelPrep (by decide) j

theorem srcDelPrep_ne_frontier (i : Fin (36 + 3)) :
    srcDelPrep i ≠ frontierReg :=
  append_paramReg_ne_frontier srcDelPrepD (fun i₁ => by rw [val_srcDelPrepD]; split_ifs <;> omega) i

theorem tmpDelFin_injective : Function.Injective tmpDelFin :=
  injective_of_tmpLayout tmpLayout_tmpDelFin

theorem srcDelFin_ne_tmpDelFin (i : Fin (36 + 7))
    (j : Fin (0 + realizes_deleteFinishWithHashGen.scratchSize + 1)) :
    srcDelFin i ≠ tmpDelFin j :=
  append_paramReg_ne_tmp_of_layout tmpLayout_tmpDelFin
    (fun i₁ => by rw [val_srcDelFinD]; split_ifs <;> decide) i j

theorem tmpDelFin_ne_frontier (j : Fin (0 + realizes_deleteFinishWithHashGen.scratchSize + 1)) :
    tmpDelFin j ≠ frontierReg :=
  tmp_ne_sReg_of_tmpLayout tmpLayout_tmpDelFin (by decide) j

theorem srcDelFin_ne_frontier (i : Fin (36 + 7)) :
    srcDelFin i ≠ frontierReg :=
  append_paramReg_ne_frontier srcDelFinD (fun i₁ => by rw [val_srcDelFinD]; split_ifs <;> omega) i

/-! ## Section 4: Representation invariant, potential, charge, and ABI encoding -/

/-- Concrete Word-RAM representation invariant at `base` coupling `θ : QuotHashSeed U n_max`,
abstract dictionary state `s_abs : Dictionary.State U`, and machine state `x`. -/
@[expose]
def Rep (U V w n_max base : ℕ) (θ : QuotHashSeed U n_max)
    (s_abs : Dictionary.State U) (x : Data rSuccinct) : Prop :=
  x.Bounded w ∧
  x.regs baseReg = base ∧
  x.regs frontierReg = base + space U V w n_max ∧
  ReducedKWise.TableRep base w (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3 x.mem ∧
  ReducedKWise.SeedRep base (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3 θ x.mem ∧
  DictStateInv U V w n_max base θ s_abs (memoryState frontierReg x)

/-- Scaled concrete potential `(66 * opFactor) * slotPotential`. -/
@[expose]
noncomputable def potential (U V w n_max base : ℕ) (_θ : QuotHashSeed U n_max)
    (x : Data rSuccinct) : ℕ :=
  (66 * opFactor) *
    slotPotential n_max (gmAt base U V w n_max (hashSpace U w n_max) x.mem)

/-- Parameter-free `O(1)` per-operation amortized instruction charge `313 * opFactor + 284725`
(independent of `U`, `V`, `w`, `n_max`, `base`, and operation-sequence length). -/
@[expose]
noncomputable def chargeVal : ℕ :=
  313 * opFactor + 284725

/-- Per-operation amortized instruction charge (`chargeVal` for every operation). -/
@[expose]
noncomputable def charge {U : ℕ} (_s : Dictionary.State U) (_o : Dynamic.Op U) : ℕ :=
  chargeVal

/-- Standalone register encoding for `Dynamic.Op U`:
* `.query u`: `tagReg = 0`, `argUReg = u.val`, `argVReg = 0`
* `.insert u v`: `tagReg = 1`, `argUReg = u.val`, `argVReg = v`
* `.delete u`: `tagReg = 2`, `argUReg = u.val`, `argVReg = 0` -/
@[expose]
noncomputable def encode {U : ℕ} : Dynamic.Op U → Fin rSuccinct → ℕ
  | .query u, r =>
    if r = tagReg then 0
    else if r = argUReg then u.val
    else 0
  | .insert u v, r =>
    if r = tagReg then 1
    else if r = argUReg then u.val
    else if r = argVReg then v
    else 0
  | .delete u, r =>
    if r = tagReg then 2
    else if r = argUReg then u.val
    else 0

/-- Partial argument-matching predicate for inline callers. -/
@[expose]
noncomputable def argMatch {U : ℕ} : Dynamic.Op U → (Fin rSuccinct → ℕ) → Prop
  | .query u, regs =>
    regs tagReg = 0 ∧ regs argUReg = u.val
  | .insert u v, regs =>
    regs tagReg = 1 ∧ regs argUReg = u.val ∧ regs argVReg = v
  | .delete u, regs =>
    regs tagReg = 2 ∧ regs argUReg = u.val

/-- Output decoder reading `Option ℕ` from `(resTagReg, resValReg)` for `.query` and `()` for
`.insert`/`.delete`. -/
@[expose]
noncomputable def decode {U : ℕ} :
    (o : Dynamic.Op U) → (Fin rSuccinct → ℕ) → Option o.Result
  | .query _, regs =>
    if regs resTagReg = 0 then some none
    else some (some (regs resValReg))
  | .insert _ _, _ => some ()
  | .delete _, _ => some ()

theorem decode_query_optionWords {U : ℕ} (u : Fin U) (res : Option ℕ)
    (regs : Fin rSuccinct → ℕ)
    (h0 : regs resTagReg = optionWords res 0)
    (h1 : regs resValReg = optionWords res 1) :
    decode (.query u) regs = some res := by
  dsimp only [decode]
  rw [h0, h1]
  cases res <;> rfl

/-! ## Section 5: Memory footprint congruence lemmas for `TableRep`, `SeedRep`, `DictStateInv` -/

theorem bucketStateInv_congr {U V w n_max h_space base : ℕ} (hw : 0 < w)
    {mOf : ℕ → ℕ} {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ} {s₁ s₂ : Memory.State}
    (heq : ∀ a, base + h_space ≤ a → a < base + totalSpace U V w n_max h_space →
      s₁.mem a = s₂.mem a)
    (hinv : BucketStateInv U V w n_max h_space base mOf L B s₁) :
    BucketStateInv U V w n_max h_space base mOf L B s₂ := by
  obtain ⟨hq, hv, hlm, hgm⟩ := arrays_congr_of_eq_on hw heq
  rcases hinv with ⟨hslot, hchains, hcm, hnodup, hsome, hdom⟩
  exact ⟨hgm ▸ hslot, hlm ▸ hchains, by simpa only [← hgm, ← hq] using hcm,
    by simpa only [← hgm, ← hq] using hnodup, by simpa only [← hgm, ← hq, ← hv] using hsome,
    by simpa only [← hgm, ← hq] using hdom⟩

theorem dictStateInv_congr {U V w n_max base : ℕ} (hw : 0 < w)
    {θ : QuotHashSeed U n_max} {s_abs : Dictionary.State U} {s₁ s₂ : Memory.State}
    (heq : ∀ a, base + hashSpace U w n_max ≤ a → a < base + space U V w n_max →
      s₁.mem a = s₂.mem a)
    (hinv : DictStateInv U V w n_max base θ s_abs s₁) :
    DictStateInv U V w n_max base θ s_abs s₂ := by
  obtain ⟨_, _, _, hgm⟩ := arrays_congr_of_eq_on hw heq
  rcases hinv with ⟨⟨L, hb⟩, htot⟩
  exact ⟨⟨L, bucketStateInv_congr hw heq hb⟩, hgm ▸ htot⟩

theorem modifies_footprint_of_table {U V w n_max base : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hout : ∀ a, ¬(base + offQuot (hashSpace U w n_max) ≤ a ∧
      a < base + space U V w n_max) → mem₂ a = mem₁ a) :
    Modifies (Block.mk base (space U V w n_max)).footprint mem₁ mem₂ := by
  intro a ha
  rw [Block.mem_footprint, Block.Owns] at ha
  dsimp only [offQuot] at ha hout
  exact hout a fun ⟨h1, h2⟩ => ha ⟨by omega, h2⟩

/-! ## Section 6: `loadParamsCode` and common prefix execution helpers -/

/-- Package well-formed layout parameters and their memory envelope for generic subroutines. -/
private theorem dictEnvGen_mk {U V w n_max h_space base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hfit : Fits w (base + totalSpace U V w n_max h_space)) :
    DictEnvGen w (mkDictParams U V w n_max h_space) base := by
  refine ⟨⟨U, V, w, n_max, h_space, hwf.1, hwf.2.1, hwf.2.2.1, hwf.2.2.2, rfl⟩, ?_⟩
  simpa only [p_U_mk, p_V_mk, p_w_mk, p_nMax_mk, p_hSpace_mk] using
    (show DictEnv U V w n_max h_space w base from ⟨rfl, hfit⟩)

/-- Every entry of `mkDictParams U V w n_max (hashSpace U w n_max)` fits in a `w`-bit word under
`DictParamsWf U V w n_max`, `Fits w V`, and `Fits w (base + space U V w n_max)`. -/
theorem fits_mkDictParams {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hV_fit : Fits w V)
    (hfit : Fits w (base + space U V w n_max))
    (i : Fin 36) :
    Fits w (mkDictParams U V w n_max (hashSpace U w n_max) i) := by
  rcases hwf with ⟨hw, hnU, hU, hV⟩
  let h_space := hashSpace U w n_max
  have henv : DictEnvGen w (mkDictParams U V w n_max h_space) base :=
    dictEnvGen_mk ⟨hw, hnU, hU, hV⟩ hfit
  have hspace : Fits w (totalSpace U V w n_max h_space) := hfit.of_le (Nat.le_add_left _ _)
  have hw_fit : Fits w w := Nat.lt_two_pow_self
  have hmax_fit : Fits w (max n_max 1) := max_n_one_lt_two_pow_w hw hnU hU
  have hb_mask := fits_bucketBits_and_mask henv hw hnU hU
  have hslab_fit : Fits w (slabSize n_max) := hmax_fit.of_le (slabSize_le_max_n_one n_max)
  obtain ⟨h2s, hdir, htail, hgd, hgp, hgo, hgm⟩ :
      Fits w (2 * slabSize n_max) ∧ Fits w (dirSlabsPerBucket n_max) ∧
      Fits w (tailCapPerBucket n_max) ∧ Fits w (gmSlabDirBase n_max) ∧
      Fits w (gmTailPtrBase n_max) ∧ Fits w (gmTailOwnerBase n_max) ∧
      Fits w (gmSlabMetaBase n_max) := by
    rcases Nat.eq_zero_or_pos (bucketBits n_max) with hb0 | hb_pos
    · have h7 : Fits w 7 := fits_const_of_dictEnv henv (by decide)
      have h1 : slabSize n_max = 1 := by simp only [slabSize, slabBits, hb0, ↓reduceIte, pow_zero]
      simp only [h1, mul_one, gmSlabMetaBase, gmTailOwnerBase, gmTailPtrBase, gmSlabDirBase,
        maxTailItems, tailCapPerBucket, dirSlabsPerBucket, numBuckets, hb0, ↓reduceIte,
        Nat.pow_zero, Nat.mul_zero, Nat.add_zero]
      exact ⟨fits_const_of_dictEnv henv (by decide), fits_zero w, fits_zero w, h7, h7, h7, h7⟩
    · have hgm {x : ℕ} (hx : x ≤ globalMetaLen n_max) : Fits w x :=
        fits_of_le_globalMetaLen henv hb_pos hw hnU hU hx
      have h2slab : 2 * slabSize n_max ≤ numBuckets n_max * (slabScale n_max) ^ 3 := by
        rw [(slabSize_eq_sq_of_pos hb_pos).1]
        have := Nat.mul_le_mul (numBuckets_pos n_max)
          (Nat.mul_le_mul_left ((slabScale n_max) ^ 2) (two_le_slabScale n_max))
        linarith
      have hlen := gmSlabMetaBase_add_eq_globalMetaLen hb_pos
      unfold gmSlabMetaBase gmTailOwnerBase gmTailPtrBase at hlen
      refine ⟨hmax_fit.of_le ((h2slab.trans (numBuckets_mul_slabScale_cubed_le hb_pos)).trans
          (le_max_left _ _)),
        hgm (dirSlabsPerBucket_le_globalMetaLen hb_pos),
        hgm (tailCapPerBucket_le_globalMetaLen hb_pos),
        hgm (by omega),
        hgm (by simp only [gmTailPtrBase]; omega),
        hgm (by simp only [gmTailOwnerBase, gmTailPtrBase]; omega),
        hgm (by simp only [gmSlabMetaBase, gmTailOwnerBase, gmTailPtrBase]; omega)⟩
  have hmicro_fit : Fits w (numMicroPerBucket n_max) :=
    hmax_fit.of_le ((totalMicroBuckets_eq_mul n_max ▸
      Nat.le_mul_of_pos_left _ (numBuckets_pos n_max)).trans (totalMicroBuckets_le n_max))
  have hU_fit : Fits w U := hU
  have hoffQ : Fits w (offQuot h_space) :=
    hspace.of_le (by unfold totalSpace offGM offLM offVal offQuot; omega)
  have hoffV : Fits w (offVal U w n_max h_space) :=
    hspace.of_le (by unfold totalSpace offGM offLM offVal; omega)
  have hoffGM : Fits w (offGM U V w n_max h_space) :=
    hspace.of_le (by unfold totalSpace; omega)
  have hoffLM (c : ℕ) (hc : c ≤ 8) : Fits w (offLMSub U V w n_max h_space c) :=
    hspace.of_le (by
      have := Nat.mul_le_mul_right (lmSubWords n_max w) hc
      unfold totalSpace offGM offLMSub offLM
      omega)
  rcases i with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k, hi⟩
  exacts [hw_fit, hU_fit.of_le hnU, hU_fit.of_le (show n_max - 1 ≤ U by omega), hoffQ,
    hw_fit.of_le (quotientBits_le_of_le_pow (le_of_lt hU)), hoffV,
    hw_fit.of_le (Nat.clog_le_of_le_pow hV), hoffLM 0 (by decide), hoffLM 1 (by decide),
    hoffLM 2 (by decide), hoffLM 3 (by decide), hoffLM 4 (by decide), hoffLM 5 (by decide),
    hoffLM 6 (by decide), hoffLM 7 (by decide), hoffLM 8 (by decide),
    hw_fit.of_le (effBucketPosBits_le_of_lt_pow hnU hU), hoffGM,
    hw_fit.of_le (globalPtrBits_le_of_lt_pow hnU hU), hb_mask.1, hb_mask.2, hslab_fit,
    hslab_fit.of_le (Nat.sub_le _ _), h2s, hdir, hdir.of_le (Nat.sub_le _ _), htail, hgd, hgp,
    hgo, hgm, hmicro_fit, hU_fit.of_le ((Nat.min_le_left _ _).trans hnU), hU_fit, hV_fit, hoffQ,
    by omega]

/-- Any register below `256` is disjoint from the `paramReg` block `[256, 292)`. -/
private theorem ne_paramReg_of_lt {r : Fin rSuccinct} (hr : r.val < 256) (j : Fin 36) :
    r ≠ paramReg j := by fin_index [val_paramReg]

private theorem exec_loadParamsUpTo {w : ℕ} {dp : DictParams}
    (hfits : ∀ i : Fin 36, Fits w (dp i))
    {x : Data rSuccinct} (hx_bdd : x.Bounded w) (k : ℕ) (hk : k < 36) :
    ∃ y : Data rSuccinct,
      ExecWithin w (loadParamsUpTo dp k hk) x y (k + 1) ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      (∀ j : Fin 36, j.val ≤ k → y.regs (paramReg j) = dp j) ∧
      (∀ r : Fin rSuccinct, r.val < 256 → y.regs r = x.regs r) := by
  induction k with
  | zero =>
    have hex : ExecWithin (B := .exact) w (.op (.const (paramReg ⟨0, hk⟩) (dp ⟨0, hk⟩)))
        x (x.set (paramReg ⟨0, hk⟩) (dp ⟨0, hk⟩)) 1 :=
      ExecWithin.const (hfits ⟨0, hk⟩)
    refine ⟨_, hex, hex.bounded hx_bdd, rfl, fun j hj => ?_, fun r hr => ?_⟩
    · obtain rfl : j = ⟨0, hk⟩ := by fin_index
      rw [Data.set_regs, Function.update_self]
    · rw [Data.set_regs, Function.update_of_ne (ne_paramReg_of_lt hr _)]
  | succ k ih =>
    obtain ⟨y₀, hex₀, hy₀_bdd, hmem₀, hparam₀, hlow₀⟩ := ih (by omega)
    have hex₁ : ExecWithin (B := .exact) w (.op (.const (paramReg ⟨k + 1, hk⟩) (dp ⟨k + 1, hk⟩)))
        y₀ (y₀.set (paramReg ⟨k + 1, hk⟩) (dp ⟨k + 1, hk⟩)) 1 :=
      ExecWithin.const (hfits ⟨k + 1, hk⟩)
    refine ⟨_, hex₀.seq hex₁, hex₁.bounded hy₀_bdd, hmem₀, fun j hj => ?_, fun r hr => ?_⟩
    · obtain rfl | hne := eq_or_ne j ⟨k + 1, hk⟩
      · rw [Data.set_regs, Function.update_self]
      · rw [Data.set_regs, Function.update_of_ne (by fin_index [val_paramReg])]
        exact hparam₀ j (by fin_index)
    · rw [Data.set_regs, Function.update_of_ne (ne_paramReg_of_lt hr _)]
      exact hlow₀ r hr

private theorem exec_loadParamsCode {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hV_fit : Fits w V)
    (hfit : Fits w (base + space U V w n_max))
    {x : Data rSuccinct} (hx_bdd : x.Bounded w) :
    ∃ x₀ : Data rSuccinct,
      ExecWithin w (loadParamsCode U V w n_max) x x₀ 36 ∧
      x₀.Bounded w ∧
      x₀.mem = x.mem ∧
      (∀ j : Fin 36, x₀.regs (paramReg j) = mkDictParams U V w n_max (hashSpace U w n_max) j) ∧
      (∀ i : Fin 292, i.val < 256 → x₀.regs (sReg i) = x.regs (sReg i)) := by
  obtain ⟨x₀, hex, hbdd, hmem, hparam, hlow⟩ :=
    exec_loadParamsUpTo (fits_mkDictParams hwf hV_fit hfit) hx_bdd 35 (by decide)
  exact ⟨x₀, hex, hbdd, hmem, fun j => hparam j (by omega), fun i hi => hlow (sReg i) hi⟩

private theorem exec_extCode {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (henv : DictEnvGen w (mkDictParams U V w n_max (hashSpace U w n_max)) base)
    (u : Fin U) {x : Data rSuccinct}
    (hx_bdd : x.Bounded w)
    (hfr : x.regs frontierReg = base + space U V w n_max)
    (hparam : ∀ j : Fin 36, x.regs (paramReg j) = mkDictParams U V w n_max (hashSpace U w n_max) j)
    (hu_reg : x.regs argUReg = u.val) :
    ∃ x₁ : Data rSuccinct,
      ExecWithin w extCode x x₁ (realizes_extractQuotGen.factor * 1) ∧
      x₁.mem = x.mem ∧
      x₁.regs frontierReg = base + space U V w n_max ∧
      x₁.regs hashKeyReg = (quotientFin U n_max u).val ∧
      ∀ i : Fin 292, i ≠ 1 →
        x₁.regs (sReg i) = x.regs (sReg i) := by
  let dp := mkDictParams U V w n_max (hashSpace U w n_max)
  have hin : x.regs ∘ srcExt = WordEncoding.encode (α := DictParams × ℕ) (dp, u.val) :=
    regs_comp_append_paramReg u.val srcExtD hparam (fun i => by fin_cases i; exact hu_reg)
  have hsafe : ExtractQuotGenPre w (dp, u.val) (memoryState frontierReg x) :=
    ⟨u.isLt.trans hwf.2.2.1, (fits_bucketBits_and_mask henv hwf.1 hwf.2.1 hwf.2.2.1).1⟩
  obtain ⟨x₁, hex, hm, hout, hframe⟩ :=
    (realizes_extractQuotGen.code_spec frontierReg srcExt tmpExt
      tmpExt_injective srcExt_ne_tmpExt tmpExt_ne_frontier srcExt_ne_frontier).2
      w (dp, u.val) x hx_bdd hin hsafe trivial
  have hfr₁ : x₁.regs frontierReg = base + space U V w n_max :=
    (congrArg Memory.State.frontier hm).trans hfr
  have hkey₁ : x₁.regs hashKeyReg = (quotientFin U n_max u).val := by
    have h0 := hout 0
    rw [clientResult_width] at h0
    refine h0.trans (show u.val >>> bucketBits n_max = _ from ?_)
    rw [quotientFin_val_eq hwf.2.1 u, keyQuotient, Nat.shiftRight_eq_div_pow]
  refine ⟨x₁, hex, congrArg Memory.State.mem hm, hfr₁, hkey₁, fun i hi1 => ?_⟩
  obtain rfl | hif := eq_or_ne i 240
  · exact hfr₁.trans hfr.symm
  · exact regs_sReg_of_frame tmpLayout_tmpExt hframe hif
      (fun h => hi1 (Fin.ext (List.mem_singleton.mp h)))

private theorem exec_hashEvalCode {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hfit : Fits w (base + space U V w n_max))
    (θ : QuotHashSeed U n_max) (q : Fin (2 ^ quotientBits U n_max))
    {x : Data rSuccinct}
    (hbase : x.regs baseReg = base)
    (hkey : x.regs hashKeyReg = q.val)
    (htab : ReducedKWise.TableRep base w (qBits U n_max) (hashB n_max)
      (totalMicroBits n_max) 3 x.mem)
    (hseed : ReducedKWise.SeedRep base (qBits U n_max) (hashB n_max)
      (totalMicroBits n_max) 3 θ x.mem) :
    ∃ y : Data rSuccinct,
      ExecWithin w (hashEvalCode U w n_max) x y
        (ReducedKWise.evalSteps (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3) ∧
      y.mem = x.mem ∧
      y.regs baseReg = base ∧
      y.regs hashOutReg = hValOfSeed U n_max θ q.val ∧
      ∀ i : Fin 292, 240 ≤ i.val →
        y.regs (sReg i) = x.regs (sReg i) := by
  have hfit_hash : Fits w (base + hashSpace U w n_max) :=
    hfit.of_le (by unfold space totalSpace offGM offLM offVal offQuot; omega)
  obtain ⟨y_core, hex_core, hymem, hy0, hy2⟩ := ReducedKWise.evalCode_execWithin
    (qBits_pos U n_max) (qBits_le_of_le_pow hwf.1 (le_of_lt hwf.2.2.1))
    (two_pow_quotientBits_le_two_pow_qBits U n_max)
    (totalMicroBits_le_of_le_pow hwf.2.1 (le_of_lt hwf.2.2.1))
    (two_mul_reducedChunkBits_hash_lt hwf.2.1 (le_of_lt hwf.2.2.1) hfit)
    hfit_hash θ q (x.comap coreReg) hbase hkey htab hseed
  refine ⟨y_core.extend coreReg x, hex_core.rename coreReg_injective, hymem, ?_, ?_,
    fun i hi => Data.extend_regs_of_notMem _ _ (notMem_range_coreReg (r := sReg i) hi)⟩
  · change ((y_core.extend coreReg x).comap coreReg).regs 0 = base
    rwa [Data.comap_extend coreReg_injective]
  · change ((y_core.extend coreReg x).comap coreReg).regs 2 = hValOfSeed U n_max θ q.val
    rw [Data.comap_extend coreReg_injective, hy2]
    unfold hValOfSeed evalQuotHash
    congr 2; exact (Fin.ext (Nat.mod_eq_of_lt q.isLt)).symm

/-- Live machine state invariant maintained along the `opCode` dispatch prefix (`loadParams`,
`extCode`, `hashEvalCode`, scratch constant loads, and saving `h_q`). -/
private structure OpState (U V w n_max base : ℕ) (θ : QuotHashSeed U n_max)
    (u : Fin U) (x x' : Data rSuccinct) : Prop where
  bdd : x'.Bounded w
  mem : x'.mem = x.mem
  frontier : x'.regs frontierReg = base + space U V w n_max
  base_reg : x'.regs baseReg = base
  tag : x'.regs tagReg = x.regs tagReg
  argU : x'.regs argUReg = u.val
  argV : x'.regs argVReg = x.regs argVReg
  hashOut : x'.regs hashOutReg = hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val)
  params : ∀ j : Fin 36,
    x'.regs (paramReg j) = mkDictParams U V w n_max (hashSpace U w n_max) j

private theorem OpState.memoryState_eq {U V w n_max base : ℕ} {θ : QuotHashSeed U n_max}
    {u : Fin U} {x x' : Data rSuccinct} (hs : OpState U V w n_max base θ u x x')
    (hfr : x.regs frontierReg = base + space U V w n_max) :
    memoryState frontierReg x' = memoryState frontierReg x :=
  Memory.State.ext hs.mem (hs.frontier.trans hfr.symm)

private theorem OpState.set_sReg {U V w n_max base : ℕ} {θ : QuotHashSeed U n_max}
    {u : Fin U} {x x' : Data rSuccinct} (hs : OpState U V w n_max base θ u x x')
    {k : Fin 292} {v : ℕ} (hbdd : (x'.set (sReg k) v).Bounded w)
    (hlt : k.val < 256) (hne : k ∉ ([0, 2, 240, 244, 245, 246] : List (Fin 292))) :
    OpState U V w n_max base θ u x (x'.set (sReg k) v) := by
  have hkeep {i : Fin 292} (hi : i ≠ k) : (x'.set (sReg k) v).regs (sReg i) = x'.regs (sReg i) := by
    rw [Data.set_regs, update_sReg, ite_eq_right_iff]; exact fun h => absurd h hi
  have hni : ∀ i ∈ ([0, 2, 240, 244, 245, 246] : List (Fin 292)), i ≠ k :=
    fun i hi heq => hne (heq ▸ hi)
  exact ⟨hbdd, hs.mem,
    (hkeep (hni 240 (by decide))).trans hs.frontier,
    (hkeep (hni 0 (by decide))).trans hs.base_reg,
    (hkeep (hni 244 (by decide))).trans hs.tag,
    (hkeep (hni 245 (by decide))).trans hs.argU,
    (hkeep (hni 246 (by decide))).trans hs.argV,
    (hkeep (hni 2 (by decide))).trans hs.hashOut,
    fun j => (by
      rw [Data.set_regs, Function.update_of_ne (ne_paramReg_of_lt hlt j).symm]
      exact hs.params j)⟩

/-- Shared prefix execution helper for `opCode`: executes `loadParamsCode U V w n_max`, `extCode`,
`hashEvalCode U w n_max`, and `zeroReg := 0`, producing the state `x₃` at the entry of the
operation-tag branch. -/
private theorem exec_opPrefix {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max) (hV_fit : Fits w V)
    (hfit : Fits w (base + space U V w n_max))
    (θ : QuotHashSeed U n_max) {s_abs : Dictionary.State U} (u : Fin U)
    {x : Data rSuccinct} (hrep : Rep U V w n_max base θ s_abs x)
    (hu_reg : x.regs argUReg = u.val) :
    ∃ x₃ : Data rSuccinct,
      (∀ {y : Data rSuccinct} {t : ℕ},
        ExecWithin w
          (.branch (.eq tagReg zeroReg)
            qryCode
            (.seq (.op (.const oneReg 1))
              (.branch (.eq tagReg oneReg) insCode (delCode U w n_max)))) x₃ y t →
        ExecWithin w (opCode U V w n_max) x y
          (36 + (realizes_extractQuotGen.factor * 1 +
            (ReducedKWise.evalSteps (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3 +
              (1 + t))))) ∧
      x₃.regs zeroReg = 0 ∧
      OpState U V w n_max base θ u x x₃ := by
  rcases hrep with ⟨hx_bdd, hbase, hfr, htab, hseed, _⟩
  obtain ⟨x₀, hex_lp, hx₀_bdd, hmem₀, hparam₀, hlow₀⟩ :=
    exec_loadParamsCode hwf hV_fit hfit hx_bdd
  obtain ⟨x₁, hex_ext, hmem₁, hfr₁, hkey₁, hframe₁⟩ :=
    exec_extCode hwf (dictEnvGen_mk hwf hfit) u hx₀_bdd
      ((hlow₀ 240 (by decide)).trans hfr) hparam₀ ((hlow₀ 245 (by decide)).trans hu_reg)
  have hmem₁_x : x₁.mem = x.mem := hmem₁.trans hmem₀
  obtain ⟨x₂, hex_h1, hmem₂, hbase₂, hout₂, hhigh₂⟩ :=
    exec_hashEvalCode hwf hfit θ (quotientFin U n_max u)
      ((hframe₁ 0 (by decide)).trans ((hlow₀ 0 (by decide)).trans hbase))
      hkey₁ (hmem₁_x ▸ htab) (hmem₁_x ▸ hseed)
  rw [quotientFin_val_eq hwf.2.1 u] at hout₂
  have hs₂ : OpState U V w n_max base θ u x x₂ :=
    ⟨hex_h1.bounded (hex_ext.bounded hx₀_bdd), hmem₂.trans hmem₁_x,
      (hhigh₂ 240 (by decide)).trans hfr₁, hbase₂,
      (hhigh₂ 244 (by decide)).trans ((hframe₁ 244 (by decide)).trans (hlow₀ 244 (by decide))),
      (hhigh₂ 245 (by decide)).trans
        ((hframe₁ 245 (by decide)).trans ((hlow₀ 245 (by decide)).trans hu_reg)),
      (hhigh₂ 246 (by decide)).trans ((hframe₁ 246 (by decide)).trans (hlow₀ 246 (by decide))),
      hout₂, fun j =>
        (hhigh₂ ⟨256 + j.val, by omega⟩ (by dsimp; omega)).trans
          ((hframe₁ ⟨256 + j.val, by omega⟩ (by fin_index)).trans (hparam₀ j))⟩
  have hex_z : ExecWithin (B := .exact) w (.op (.const zeroReg 0)) x₂ (x₂.set zeroReg 0) 1 :=
    ExecWithin.const (Nat.two_pow_pos w)
  exact ⟨_, fun hex_br => hex_lp.seq (hex_ext.seq (hex_h1.seq (hex_z.seq hex_br))),
    by rw [Data.set_regs, Function.update_self],
    hs₂.set_sReg (hex_z.bounded hs₂.bdd) (by decide) (by decide)⟩

/-- Shared post-prefix execution helper for the `tagReg ≠ 0` branches (`insert` and `delete`):
takes the negative branch of `tagReg = zeroReg` and executes `oneReg := 1`, producing state `x₄`
at the entry of the `tagReg = oneReg` branch. -/
private theorem exec_opPrefix_ne_zero {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max) (hV_fit : Fits w V)
    (hfit : Fits w (base + space U V w n_max))
    (θ : QuotHashSeed U n_max) {s_abs : Dictionary.State U} (u : Fin U)
    {x : Data rSuccinct} (hrep : Rep U V w n_max base θ s_abs x)
    (hu_reg : x.regs argUReg = u.val) (htag_ne : x.regs tagReg ≠ 0) :
    ∃ x₄ : Data rSuccinct,
      (∀ {y : Data rSuccinct} {t : ℕ},
        ExecWithin w
          (.branch (.eq tagReg oneReg) insCode (delCode U w n_max)) x₄ y t →
        ExecWithin w (opCode U V w n_max) x y
          (36 + (realizes_extractQuotGen.factor * 1 +
            (ReducedKWise.evalSteps (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3 +
              (1 + (1 + t + 2)))))) ∧
      x₄.regs oneReg = 1 ∧
      OpState U V w n_max base θ u x x₄ := by
  obtain ⟨x₃, hex_pre, hzero₃, hs₃⟩ := exec_opPrefix hwf hV_fit hfit θ u hrep hu_reg
  have hcond_neg0 : ¬(Cond.eq tagReg zeroReg).Holds x₃ := by
    change x₃.regs tagReg ≠ x₃.regs zeroReg
    rw [hs₃.tag, hzero₃]; exact htag_ne
  have hex_o : ExecWithin (B := .exact) w (.op (.const oneReg 1)) x₃ (x₃.set oneReg 1) 1 :=
    ExecWithin.const (fits_one (Nat.ne_of_gt hwf.1))
  exact ⟨_, fun hex_br => hex_pre (ExecWithin.branch_neg hcond_neg0 (hex_o.seq hex_br)),
    by rw [Data.set_regs, Function.update_self],
    hs₃.set_sReg (hex_o.bounded hs₃.bdd) (by decide) (by decide)⟩

/-! ## Section 7: Per-operation deterministic execution of `opCode` -/

section

-- Register wiring uses the named parameter projections, not the packed layout body.
attribute [local irreducible] mkDictParams

/-- Package `Rep` and `Modifies` after a table-modifying `insert` or `deleteFinish` realization
call whose memory writes stay within `[base + offQuot (hashSpace ...), base + space ...)`. -/
private theorem rep_and_modifies_of_table_post {U V w n_max base : ℕ}
    {θ : QuotHashSeed U n_max} {s_abs' : Dictionary.State U}
    {x y : Data rSuccinct} {s_ref s_out : Memory.State}
    (htab : ReducedKWise.TableRep base w (qBits U n_max) (hashB n_max)
      (totalMicroBits n_max) 3 x.mem)
    (hseed : ReducedKWise.SeedRep base (qBits U n_max) (hashB n_max)
      (totalMicroBits n_max) 3 θ x.mem)
    (hy_bdd : y.Bounded w)
    (hybase : y.regs baseReg = base)
    (hmem_ref : s_ref.mem = x.mem)
    (hfr_ref : s_ref.frontier = base + space U V w n_max)
    (hm : memoryState frontierReg y = s_out)
    (hfr_out : s_out.frontier = s_ref.frontier)
    (hout_mem : ∀ a, ¬(base + offQuot (hashSpace U w n_max) ≤ a ∧
      a < base + space U V w n_max) → s_out.mem a = s_ref.mem a)
    (hdict_out : DictStateInv U V w n_max base θ s_abs' s_out) :
    Rep U V w n_max base θ s_abs' y ∧
    Modifies (Block.mk base (space U V w n_max)).footprint x.mem y.mem := by
  have hyfr : y.regs frontierReg = base + space U V w n_max :=
    ((congrArg Memory.State.frontier hm).trans hfr_out).trans hfr_ref
  have hmem_out : ∀ a, ¬(base + offQuot (hashSpace U w n_max) ≤ a ∧
      a < base + space U V w n_max) → y.mem a = x.mem a := by
    intro a ha
    change (memoryState frontierReg y).mem a = _
    rw [hm, hout_mem a ha, hmem_ref]
  have hhash_eq : ∀ a, base ≤ a → a < base + hashSpace U w n_max → x.mem a = y.mem a :=
    fun a ha1 ha2 => (hmem_out a (by dsimp [offQuot]; omega)).symm
  exact ⟨⟨hy_bdd, hybase, hyfr, tableRep_congr htab hhash_eq, seedRep_congr hseed hhash_eq,
    hm ▸ hdict_out⟩, modifies_footprint_of_table hmem_out⟩

/-- Scale a `Realizes` step bound `f * (c + 0 + 1)` by `f ≤ opFactor`. -/
private theorem factor_mul_cost_add_one_le {f c : ℕ} (hf : f ≤ opFactor) :
    f * (c + 0 + 1) ≤ opFactor * c + opFactor := by
  calc f * (c + 0 + 1) ≤ opFactor * (c + 1) := Nat.mul_le_mul hf (by omega)
    _ = opFactor * c + opFactor := by ring

/-- Scale an amortized `Memory.Prog` bound (`cost + 66 * pot_y ≤ 66 * pot_x + k + 8 * pe`) by
`opFactor`. -/
private theorem opFactor_mul_amortized_le {cost pot_y pot_x k pe : ℕ}
    (h : cost + 66 * pot_y ≤ 66 * pot_x + k + 8 * pe) :
    opFactor * cost + (66 * opFactor) * pot_y ≤
      (66 * opFactor) * pot_x + k * opFactor + (8 * opFactor) * pe := by
  calc opFactor * cost + (66 * opFactor) * pot_y
      = opFactor * (cost + 66 * pot_y) := by ring
    _ ≤ opFactor * (66 * pot_x + k + 8 * pe) := Nat.mul_le_mul_left _ h
    _ = (66 * opFactor) * pot_x + k * opFactor + (8 * opFactor) * pe := by ring

private theorem exec_opCode_query {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hV_fit : Fits w V)
    (hfit : Fits w (base + space U V w n_max))
    (θ : QuotHashSeed U n_max) (s_abs : Dictionary.State U) (u : Fin U)
    {x : Data rSuccinct}
    (hrep : Rep U V w n_max base θ s_abs x)
    (harg : argMatch (.query u) x.regs) :
    ∃ (y : Data rSuccinct) (steps : ℕ),
      ExecWithin w (opCode U V w n_max) x y steps ∧
      decode (.query u) y.regs = some (s_abs u) ∧
      Rep U V w n_max base θ s_abs y ∧
      Modifies (Block.mk base (space U V w n_max)).footprint x.mem y.mem ∧
      steps + potential U V w n_max base θ y ≤
        potential U V w n_max base θ x + (273 * opFactor + 284725) +
          (8 * opFactor) *
            probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
              (Dictionary.dom s_abs) u := by
  rcases harg with ⟨htag, hu_reg⟩
  obtain ⟨x₃, hex_pre, hzero₃, hs₃⟩ := exec_opPrefix hwf hV_fit hfit θ u hrep hu_reg
  rcases hrep with ⟨hx_bdd, _, hfr, htab, hseed, hdict⟩
  have hms₃ := hs₃.memoryState_eq hfr
  let dp := mkDictParams U V w n_max (hashSpace U w n_max)
  let d_qry := ((base, u.val), hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val))
  obtain ⟨hpre_qry, hst_qry, hres_qry, hcost_qry⟩ :=
    queryWithHashProg_dict_spec hwf (dictEnvGen_mk hwf hfit) θ (hms₃.symm ▸ hdict) u
  have hin_qry : x₃.regs ∘ srcQry =
      WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ)) (dp, d_qry) :=
    regs_comp_append_paramReg d_qry srcQryD hs₃.params
      (fun | 0 => hs₃.base_reg | 1 => hs₃.argU | 2 => hs₃.hashOut)
  obtain ⟨y, hex_qry, hm_qry, hout_qry, hframe_qry⟩ :=
    (realizes_queryWithHashGen.code_spec frontierReg srcQry tmpQry
      tmpQry_injective srcQry_ne_tmpQry tmpQry_ne_frontier srcQry_ne_frontier).2
      w (dp, d_qry) x₃ hs₃.bdd hin_qry
      ((queryWithHashGenPre_mk U V w n_max w d_qry _).2 hpre_qry)
      (by
        rw [queryWithHashGenProg_mk]
        exact validProg_queryWithHash hpre_qry
          ⟨wellFormed_memoryState hs₃.bdd, le_of_eq hs₃.frontier.symm⟩)
  rw [clientState_width, queryWithHashGenProg_mk, hst_qry] at hm_qry
  rw [clientResult_width, queryWithHashGenProg_mk, hres_qry] at hout_qry
  have hymem : y.mem = x.mem := (congrArg Memory.State.mem hm_qry).trans hs₃.mem
  have hex_all := hex_pre (ExecWithin.branch_pos
    (by change x₃.regs tagReg = x₃.regs zeroReg; rw [hs₃.tag, htag, hzero₃]) hex_qry)
  refine ⟨y, _, hex_all, decode_query_optionWords u (s_abs u) y.regs (hout_qry 0) (hout_qry 1),
    ⟨hex_all.bounded hx_bdd,
      (regs_sReg_of_frame tmpLayout_tmpQry hframe_qry (by decide) (by decide)).trans hs₃.base_reg,
      (congrArg Memory.State.frontier hm_qry).trans hs₃.frontier,
      hymem ▸ htab, hymem ▸ hseed, (hm_qry.trans hms₃).symm ▸ hdict⟩,
    by rw [hymem]; exact fun _ _ => rfl, ?_⟩
  have hF_ext := factor_extractQuot_le
  have hH_le := ReducedKWise.evalSteps_le (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3
  dsimp only [ReducedKWise.evalBound] at hH_le
  rw [queryWithHashGenProg_mk]
  have hmul_qry := factor_mul_cost_add_one_le
    (c := memoryCost (queryWithHashProg U V w n_max d_qry) (memoryState frontierReg x₃))
    factor_queryWithHash_le
  have hcost_scaled := Nat.mul_le_mul_left opFactor hcost_qry
  rw [Nat.mul_add, ← mul_assoc, mul_comm opFactor 26, mul_comm opFactor 8] at hcost_scaled
  unfold potential
  rw [hymem]
  dsimp only [d_qry] at hmul_qry ⊢
  omega

private theorem exec_opCode_insert {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hV_fit : Fits w V)
    (hfit : Fits w (base + space U V w n_max))
    (θ : QuotHashSeed U n_max) (s_abs : Dictionary.State U) (u : Fin U) (v : ℕ)
    (hval : (Dynamic.spec U V n_max).valid s_abs (.insert u v))
    {x : Data rSuccinct}
    (hrep : Rep U V w n_max base θ s_abs x)
    (harg : argMatch (.insert u v) x.regs) :
    ∃ (y : Data rSuccinct) (steps : ℕ),
      ExecWithin w (opCode U V w n_max) x y steps ∧
      decode (.insert u v) y.regs = some () ∧
      Rep U V w n_max base θ (Function.update s_abs u (some v)) y ∧
      Modifies (Block.mk base (space U V w n_max)).footprint x.mem y.mem ∧
      steps + potential U V w n_max base θ y ≤
        potential U V w n_max base θ x + (273 * opFactor + 284725) +
          (8 * opFactor) *
            probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
              (Dictionary.dom s_abs) u := by
  rcases harg with ⟨htag, hu_reg, hv_reg⟩
  obtain ⟨x₄, hex_pre, hone₄, hs₄⟩ :=
    exec_opPrefix_ne_zero hwf hV_fit hfit θ u hrep hu_reg (by rw [htag]; exact one_ne_zero)
  rcases hrep with ⟨hx_bdd, _, hfr, htab, hseed, hdict⟩
  let dp := mkDictParams U V w n_max (hashSpace U w n_max)
  let d_ins := (((base, u.val), v), hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val))
  obtain ⟨hpre_ins, hfr_ins, hout_ins, hdict_ins, hcost_ins⟩ :=
    insertWithHashProg_dict_spec hwf (dictEnvGen_mk hwf hfit) θ
      ((hs₄.memoryState_eq hfr).symm ▸ hdict) u v hval
  have hin_ins : x₄.regs ∘ srcIns =
      WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) (dp, d_ins) :=
    regs_comp_append_paramReg d_ins srcInsD hs₄.params
      (fun | 0 => hs₄.base_reg | 1 => hs₄.argU | 2 => hs₄.argV.trans hv_reg | 3 => hs₄.hashOut)
  obtain ⟨y, hex_ins, hm_ins, _, hframe_ins⟩ :=
    (realizes_insertWithHashGen.code_spec frontierReg srcIns tmpIns
      tmpIns_injective srcIns_ne_tmpIns tmpIns_ne_frontier srcIns_ne_frontier).2
      w (dp, d_ins) x₄ hs₄.bdd hin_ins
      ((insertWithHashGenPre_mk U V w n_max w d_ins _).2 hpre_ins)
      (by
        rw [insertWithHashGenProg_mk]
        exact validProg_insertWithHash hpre_ins
          ⟨wellFormed_memoryState hs₄.bdd, le_of_eq hs₄.frontier.symm⟩)
  rw [clientState_width, insertWithHashGenProg_mk] at hm_ins
  have hex_all := hex_pre (ExecWithin.branch_pos
    (by change x₄.regs tagReg = x₄.regs oneReg; rw [hs₄.tag, htag, hone₄]) hex_ins)
  obtain ⟨hy_rep, hmod⟩ := rep_and_modifies_of_table_post htab hseed (hex_all.bounded hx_bdd)
    ((regs_sReg_of_frame tmpLayout_tmpIns hframe_ins (by decide) (by decide)).trans hs₄.base_reg)
    hs₄.mem hs₄.frontier hm_ins hfr_ins hout_ins hdict_ins
  refine ⟨y, _, hex_all, rfl, hy_rep, hmod, ?_⟩
  rw [show (memoryState frontierReg x₄).mem = x.mem from hs₄.mem] at hcost_ins
  have hF_ext := factor_extractQuot_le
  have hH_le := ReducedKWise.evalSteps_le (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3
  dsimp only [ReducedKWise.evalBound] at hH_le
  rw [insertWithHashGenProg_mk]
  have hmul_ins := factor_mul_cost_add_one_le
    (c := memoryCost (insertWithHashProg U V w n_max d_ins) (memoryState frontierReg x₄))
    factor_insertWithHash_le
  have hcost_scaled := opFactor_mul_amortized_le hcost_ins
  unfold potential
  rw [show y.mem = _ from congrArg Memory.State.mem hm_ins]
  dsimp only [d_ins] at hmul_ins ⊢
  omega

/-- Execute `delPrepCode` on state `x₅` holding `(base, u, h_q)` and `paramReg`, returning `x₆`
with preserved memory/params/`baseReg`/`argUReg`/`hqReg` and the four extracted outputs. -/
private theorem exec_delPrepCode {U V w n_max base : ℕ}
    {θ : QuotHashSeed U n_max} {u : Fin U} {x x₅ : Data rSuccinct}
    (hs₅ : OpState U V w n_max base θ u x x₅)
    (h_q found j_del phys_del q_last : ℕ) (hhq : x₅.regs hqReg = h_q)
    (hpre : QueryWithHashPre U V w n_max w ((base, u.val), h_q) (memoryState frontierReg x₅))
    (hst : (Memory.spec 0).clientState (memoryState frontierReg x₅)
      (deletePrepWithHashProg U V w n_max ((base, u.val), h_q)) = memoryState frontierReg x₅)
    (hres : (Memory.spec 0).clientResult (memoryState frontierReg x₅)
      (deletePrepWithHashProg U V w n_max ((base, u.val), h_q)) =
      (((found, j_del), phys_del), q_last)) :
    ∃ x₆ : Data rSuccinct,
      ExecWithin w delPrepCode x₅ x₆
        (realizes_deletePrepWithHashGen.factor *
          (memoryCost (deletePrepWithHashGenProg
            (mkDictParams U V w n_max (hashSpace U w n_max), ((base, u.val), h_q)))
            (memoryState frontierReg x₅) + 0 + 1)) ∧
      x₆.Bounded w ∧ x₆.mem = x.mem ∧
      x₆.regs frontierReg = base + space U V w n_max ∧
      x₆.regs baseReg = base ∧ x₆.regs argUReg = u.val ∧ x₆.regs hqReg = h_q ∧
      (∀ j : Fin 36,
        x₆.regs (paramReg j) = mkDictParams U V w n_max (hashSpace U w n_max) j) ∧
      x₆.regs foundReg = found ∧ x₆.regs jDelReg = j_del ∧
      x₆.regs physDelReg = phys_del ∧ x₆.regs hashKeyReg = q_last := by
  let dp := mkDictParams U V w n_max (hashSpace U w n_max)
  let d_prep := ((base, u.val), h_q)
  have hin : x₅.regs ∘ srcDelPrep =
      WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ)) (dp, d_prep) :=
    regs_comp_append_paramReg d_prep srcDelPrepD hs₅.params
      (fun | 0 => hs₅.base_reg | 1 => hs₅.argU | 2 => hhq)
  obtain ⟨x₆, hex, hm, hout, hframe⟩ :=
    (realizes_deletePrepWithHashGen.code_spec frontierReg srcDelPrep tmpDelPrep
      tmpDelPrep_injective srcDelPrep_ne_tmpDelPrep
      tmpDelPrep_ne_frontier srcDelPrep_ne_frontier).2
      w (dp, d_prep) x₅ hs₅.bdd hin ((queryWithHashGenPre_mk U V w n_max w d_prep _).2 hpre)
      (by
        rw [deletePrepWithHashGenProg_mk]
        exact validProg_deletePrepWithHash hpre
          ⟨wellFormed_memoryState hs₅.bdd, le_of_eq hs₅.frontier.symm⟩)
  rw [clientState_width, deletePrepWithHashGenProg_mk, hst] at hm
  rw [clientResult_width, deletePrepWithHashGenProg_mk, hres] at hout
  have hkeep := fun {i : Fin 292} (h1 : i ≠ 240) (h2 : i.val ∉ [249, 250, 251, 1]) =>
    regs_sReg_of_frame tmpLayout_tmpDelPrep hframe h1 h2
  exact ⟨x₆, hex, hex.bounded hs₅.bdd, (congrArg Memory.State.mem hm).trans hs₅.mem,
    (congrArg Memory.State.frontier hm).trans hs₅.frontier,
    (hkeep (by decide) (by decide)).trans hs₅.base_reg,
    (hkeep (by decide) (by decide)).trans hs₅.argU,
    (hkeep (by decide) (by decide)).trans hhq,
    fun j => (hkeep (by fin_index)
      (fun hm => by have := tmpLayout_tmpDelPrep.lt_256 _ hm; dsimp at this; omega)).trans
      (hs₅.params j),
    hout 0, hout 1, hout 2, hout 3⟩

private theorem exec_opCode_delete {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hV_fit : Fits w V)
    (hfit : Fits w (base + space U V w n_max))
    (θ : QuotHashSeed U n_max) (s_abs : Dictionary.State U) (u : Fin U)
    {x : Data rSuccinct}
    (hrep : Rep U V w n_max base θ s_abs x)
    (harg : argMatch (.delete u) x.regs) :
    ∃ (y : Data rSuccinct) (steps : ℕ),
      ExecWithin w (opCode U V w n_max) x y steps ∧
      decode (.delete u) y.regs = some () ∧
      Rep U V w n_max base θ (Function.update s_abs u none) y ∧
      Modifies (Block.mk base (space U V w n_max)).footprint x.mem y.mem ∧
      steps + potential U V w n_max base θ y ≤
        potential U V w n_max base θ x + (273 * opFactor + 284725) +
          (8 * opFactor) *
            probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
              (Dictionary.dom s_abs) u := by
  rcases harg with ⟨htag, hu_reg⟩
  obtain ⟨x₄, hex_pre, hone₄, hs₄⟩ :=
    exec_opPrefix_ne_zero hwf hV_fit hfit θ u hrep hu_reg
      (by rw [htag]; exact OfNat.ofNat_ne_zero 2)
  rcases hrep with ⟨hx_bdd, _, hfr, htab, hseed, hdict⟩
  let dp := mkDictParams U V w n_max (hashSpace U w n_max)
  let h_q := hValOfSeed U n_max θ (keyQuotient (bucketBits n_max) u.val)
  let x₅ := x₄.set hqReg (x₄.regs hashOutReg)
  have hex_cp : ExecWithin (B := .exact) w (.op (.copy hqReg hashOutReg)) x₄ x₅ 1 :=
    ExecWithin.copy
  have hs₅ := hs₄.set_sReg (hex_cp.bounded hs₄.bdd) (by decide) (by decide)
  have hhq₅ : x₅.regs hqReg = h_q := by rw [Data.set_regs, Function.update_self]; exact hs₄.hashOut
  let s₅ := memoryState frontierReg x₅
  obtain ⟨found, j_del, phys_del, q_last, hprep_eq, hpre_prep, hst_prep, hqlast_lt,
      hpre_fin, hfr_fin, hout_fin, hdict_fin, hcost_del⟩ :=
    deleteWithHashProg_dict_spec hwf (dictEnvGen_mk hwf hfit) θ
      ((hs₅.memoryState_eq hfr).symm ▸ hdict) u
  obtain ⟨x₆, hex_prep, hx₆_bdd, hmem₆, hfr₆, hbase₆, hu₆, hhq₆, hparam₆,
      hfound₆, hj₆, hphys₆, hq₆⟩ :=
    exec_delPrepCode hs₅ h_q found j_del phys_del q_last hhq₅ hpre_prep hst_prep hprep_eq
  obtain ⟨x₇, hex_h2, hmem₇, hbase₇, hout₇, hhigh₇⟩ :=
    exec_hashEvalCode hwf hfit θ ⟨q_last, hqlast_lt⟩ hbase₆ hq₆
      (hmem₆ ▸ htab) (hmem₆ ▸ hseed)
  have hms₇ : memoryState frontierReg x₇ = s₅ :=
    Memory.State.ext ((hmem₇.trans hmem₆).trans hs₅.mem.symm)
      (((hhigh₇ 240 (by decide)).trans hfr₆).trans hs₅.frontier.symm)
  let d_fin := ((((base, u.val), h_q), ((found, j_del), phys_del)), hValOfSeed U n_max θ q_last)
  have hin_fin : x₇.regs ∘ srcDelFin =
      WordEncoding.encode (α := DictParams × ((((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × ℕ)) × ℕ)) (dp, d_fin) :=
    regs_comp_append_paramReg d_fin srcDelFinD
      (fun j => (hhigh₇ ⟨256 + j.val, by omega⟩ (by dsimp; omega)).trans (hparam₆ j))
      (fun
        | 0 => hbase₇ | 1 => (hhigh₇ 245 (by decide)).trans hu₆
        | 2 => (hhigh₇ 248 (by decide)).trans hhq₆ | 3 => (hhigh₇ 249 (by decide)).trans hfound₆
        | 4 => (hhigh₇ 250 (by decide)).trans hj₆ | 5 => (hhigh₇ 251 (by decide)).trans hphys₆
        | 6 => hout₇)
  obtain ⟨y, hex_fin, hm_fin, _, hframe_fin⟩ :=
    (realizes_deleteFinishWithHashGen.code_spec frontierReg srcDelFin tmpDelFin
      tmpDelFin_injective srcDelFin_ne_tmpDelFin tmpDelFin_ne_frontier srcDelFin_ne_frontier).2
      w (dp, d_fin) x₇ (hex_h2.bounded hx₆_bdd) hin_fin
      (by rw [deleteFinishWithHashGenPre_mk, hms₇]; exact hpre_fin)
      (by
        rw [deleteFinishWithHashGenProg_mk, hms₇]
        exact validProg_deleteFinishWithHash hpre_fin
          ⟨wellFormed_memoryState hs₅.bdd, le_of_eq hs₅.frontier.symm⟩)
  rw [clientState_width, deleteFinishWithHashGenProg_mk, hms₇] at hm_fin
  have hex_all := hex_pre (ExecWithin.branch_neg
    (by change x₄.regs tagReg ≠ x₄.regs oneReg; rw [hs₄.tag, htag, hone₄]; decide)
    (hex_cp.seq (hex_prep.seq (hex_h2.seq hex_fin))))
  obtain ⟨hy_rep, hmod⟩ := rep_and_modifies_of_table_post htab hseed (hex_all.bounded hx_bdd)
    ((regs_sReg_of_frame tmpLayout_tmpDelFin hframe_fin (by decide) (by decide)).trans hbase₇)
    hs₅.mem hs₅.frontier hm_fin hfr_fin hout_fin hdict_fin
  refine ⟨y, _, hex_all, rfl, hy_rep, hmod, ?_⟩
  rw [show s₅.mem = x.mem from hs₅.mem] at hcost_del
  have hF_ext := factor_extractQuot_le
  have hH_le := ReducedKWise.evalSteps_le (qBits U n_max) (hashB n_max) (totalMicroBits n_max) 3
  dsimp only [ReducedKWise.evalBound] at hH_le
  rw [deletePrepWithHashGenProg_mk, deleteFinishWithHashGenProg_mk, hms₇]
  have hmul_prep := factor_mul_cost_add_one_le
    (c := memoryCost (deletePrepWithHashProg U V w n_max ((base, u.val), h_q)) s₅)
    factor_deletePrepWithHash_le
  have hmul_fin := factor_mul_cost_add_one_le
    (c := memoryCost (deleteFinishWithHashProg U V w n_max d_fin) s₅)
    factor_deleteFinishWithHash_le
  have hcost_scaled := opFactor_mul_amortized_le hcost_del
  rw [Nat.mul_add] at hcost_scaled
  unfold potential
  rw [show y.mem = _ from congrArg Memory.State.mem hm_fin]
  dsimp only [s₅, x₅, hqReg, dp, d_fin, h_q] at hmul_prep hmul_fin ⊢
  omega

/-- Extract the target key `u : Fin U` of a dynamic dictionary operation `o : Dynamic.Op U`. -/
@[expose]
def opKey {U : ℕ} : Dynamic.Op U → Fin U
  | .query u => u
  | .insert u _ => u
  | .delete u => u

/-- Unified per-operation deterministic execution of `opCode` for any `o : Dynamic.Op U`. -/
theorem exec_opCode {U V w n_max base : ℕ}
    (hwf : DictParamsWf U V w n_max)
    (hV_fit : Fits w V)
    (hfit : Fits w (base + space U V w n_max))
    (θ : QuotHashSeed U n_max) (s_abs : Dictionary.State U) (o : Dynamic.Op U)
    (hval : (Dynamic.spec U V n_max).valid s_abs o)
    {x : Data rSuccinct}
    (hrep : Rep U V w n_max base θ s_abs x)
    (harg : argMatch o x.regs) :
    ∃ (y : Data rSuccinct) (steps : ℕ),
      ExecWithin w (opCode U V w n_max) x y steps ∧
      decode o y.regs = some ((Dynamic.spec U V n_max).stepFn s_abs o).2 ∧
      Rep U V w n_max base θ ((Dynamic.spec U V n_max).stepFn s_abs o).1 y ∧
      Modifies (Block.mk base (space U V w n_max)).footprint x.mem y.mem ∧
      steps + potential U V w n_max base θ y ≤
        potential U V w n_max base θ x + (273 * opFactor + 284725) +
          (8 * opFactor) *
            probeExcess n_max (qStage1 U n_max θ.1) (polyStage2 U n_max) θ.2
              (Dictionary.dom s_abs) (opKey o) := by
  cases o with
  | query u => exact exec_opCode_query hwf hV_fit hfit θ s_abs u hrep harg
  | insert u v => exact exec_opCode_insert hwf hV_fit hfit θ s_abs u v hval hrep harg
  | delete u => exact exec_opCode_delete hwf hV_fit hfit θ s_abs u hrep harg

end

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
