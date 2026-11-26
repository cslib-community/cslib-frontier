/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpTickHealProg
public import CslibFrontier.DataStructure.WordRAM.Randomized.HighProbability
import CslibFrontier.Computability.WordRAM.Width
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform

/-!
# Fixed-Capacity Succinct Dynamic Dictionary with High-Probability `O_c(1)` Operations

This module packages the fixed-capacity succinct dynamic dictionary (`insert`, `delete`, `query`)
with high-probability `O_c(1)` worst-case operation time over `Cslib.WordRAM.Basis.exact` and
`Cslib.WordRAM.Basis.standard` as a reusable
`Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl` certificate
(`Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.impl` and `implStandard`) for
`Cslib.DataStructure.Dictionary.Dynamic.spec U V n_max`, adapting the partition hash table
architecture of [Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024, Sections 2.2 and
3–5, pp. 363–373; author copy pp. 3–7][BenderFarachColtonKuszmaulKuszmaul2024].

## Mathematical guarantees, model, and adaptations vs. SOSA 2024

For any failure-probability exponent `0 < c`, capacity `n_max ≤ U`, word width `0 < w`, and
addressable universe/value/footprint bounds `Fits w U`, `Fits w V`, and
`Fits w (base + whpSpace c U V w n_max)`:

1. **Succinct `1 · OPT + O_c(n_max log log n_max)` space (`whpSpace_le_succinctWords`)**:
   the allocated Word-RAM block occupies `whpSpace c U V w n_max` machine words, bounded across all
   `w` and `n_max ≤ U` by `Dynamic.succinctWords (whpSpaceFactor c) whpSpaceConst U V w n_max`
   (`⌈(OPT(U, V, n_max) + whpSpaceFactor c · n_max · logLogFactor n_max) / w⌉ + 160` words).
2. **Self-contained `O(n_max)` randomized initialization (`initTime_impl_le`)**:
   when `whpThreshold c ≤ n_max`, `initSetupCode` samples two independent uniform Thorup
   bit-packed double-tabulation seeds (`BitPackedDoubleTabulation.resampleCode`, [Thorup2013])
   directly into `[base + offHashBkt, base + offQuotWhp c w n_max)` and initializes the fast
   front-yard/backyard/SWAR B+-tree metadata in `O(n_max)` deterministic worst-case instructions
   (`≤ initTimeLinearFactor * n_max + initTimeLinearConst`); below `whpThreshold c`, initialization
   requires `0` random draws and `3` `allocSpan` instructions.
3. **Worst-case `O_c(1)` operations with probability `≥ 1 - (max n_max 1)⁻¹ ^ c`
   (`reachable_step_whp`, `seq_whp`, `poly_seq_whp`)**:
   on any oblivious operation sequence `ops : List (Dynamic.Op U)` satisfying
   `ValidHistory (Dictionary.empty U) ops` (chosen independently of the internal hash seeds):
   * **Zero-error correctness**: *every* execution path (including rare `¬IsFastStepHit` fallback
     branches handled via `fastToCsrGenProg` and `fallbackAndHealGenProg`) produces the exact
     specification transcript `((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).2`,
     preserves `Rep`, and leaves caller memory outside `[base, base + whpSpace c U V w n_max)`
     untouched (`Modifies`).
   * **Per-operation high-probability bound (`reachable_step_whp`)**: after *any* valid oblivious
     prefix `ops` (of arbitrary length), the next valid operation `o` halts in clocked `evalRand`
     within `worstCaseTimeWhp c + 1` instructions (`O_c(1)`, independent of `U`, `V`, `w`, `n_max`,
     `base`, and `ops.length`) with probability at least `1 - (max n_max 1 : ℝ≥0∞)⁻¹ ^ c`.
   * **Whole-sequence and polynomial-horizon bounds (`seq_whp`, `poly_seq_whp`)**: across `ops`,
     every operation runs within `worstCaseTimeWhp c` body instructions with probability at least
     `1 - ops.length * (max n_max 1 : ℝ≥0∞)⁻¹ ^ c`; instantiating at exponent `c + c₀` covers any
     polynomial sequence `ops.length ≤ max n_max 1 ^ c₀` with failure probability at most
     `(max n_max 1 : ℝ≥0∞)⁻¹ ^ c`.
4. **Adaptations relative to SOSA 2024 Sections 3–5**:
   * **Fixed capacity**: `n_max` is fixed without table resizing (SOSA 2024 Section 6 adds
     resizing).
   * **Key-value payloads and general universes**: supports arbitrary key universe `n_max ≤ U < 2^w`
     and value payloads `< V < 2^w` via one-round Feistel quotienting, whereas SOSA 2024 Sections
     3–5 state a key-only membership dictionary on `w = Θ(log n)`-bit keys.
   * **Explicit seeded tabulation vs. random-oracle hashing**: SOSA 2024 Section 2.1 assumes
     zero-space oracle access to fully random hash functions; here both bucket and fingerprint hash
     families are explicitly sampled and stored inside `whpSpace c U V w n_max` via salted
     bit-packed double tabulation [Thorup2013], and below the `c`-only threshold `whpThreshold c`
     (`bMinWhp c = Θ(c^6)`) operations use a deterministic bit-packed array in `O_c(1)` time.
   * **High-probability vs. deterministic query time**: SOSA 2024 (Theorem 1.1, Lemma 4.3 on PDF
     p. 5, and Section 5 on PDF pp. 6–7) achieves deterministic worst-case `O(1)` queries alongside
     w.h.p. `O(1)` updates by resampling colliding bucket fingerprints from its random hash oracle
     until injective. Because `SuccinctWhp` samples a static seed pair once during `initSetupCode`
     (`0` runtime `rand` calls) and routes rare bad seeds to deterministic `CsrState` (`O(n_max)`
     scan), `query` here runs in `O_c(1)` worst-case time with high probability
     `≥ 1 - (max n_max 1 : ℝ≥0∞)⁻¹ ^ c` (`reachable_step_whp`) rather than deterministic
     worst-case `O(1)` on bad seeds.
   * **Width independence (`not_readsWidth_subroutineCode`)**: none of `initFresh`, `initClear`, or
     `code` inspects the ambient word width `w` (`¬ReadsWidth`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.rWhp`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.worstCaseTimeWhp`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.initSetupSteps`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.initSetupRandCalls`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.initTimeLinearFactor`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.initTimeLinearConst`:
  parameter-free register budget `rWhp`, `c`-only worst-case operation instruction budget
  `worstCaseTimeWhp c`, and initialization instruction / RNG-call budgets.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.opCode`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.initSetupCode`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.subroutineCode`:
  native Word-RAM operation body, self-contained initializer, and `SubroutineCode .exact rWhp 0`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.GhostRep`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.Rep`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.encode`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.argMatch`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.decode`:
  coupled Word-RAM representation invariants and ABI register conventions.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.impl`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.implStandard`:
  `HighProbStateTransitionImpl` certificates over `Basis.exact` and `Basis.standard`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.not_readsWidth_subroutineCode`:
  width independence (`¬ReadsWidth`) of `initFresh`, `initClear`, and `code`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.initTime_impl_le`:
  explicit `O(n_max)` deterministic upper bound on `(impl ...).initTime`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.seq_whp`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.poly_seq_whp`,
  `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.reachable_step_whp`:
  headline whole-sequence, polynomial-horizon, and arbitrary-prefix per-operation high-probability
  theorems.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 2.2 and 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.WordRAM.Randomized.HighProbStateTransitionImpl
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.Probability
open scoped ENNReal

/-! ## Section 1: Parameter-Free Register Bank `rWhp` and Emitted Native Code -/

/-- Parameter-free scratch register bank size dominating `realizes_initFastGen` and
`realizes_whpStepPureGen`. -/
private noncomputable def scratchWhp : ℕ :=
  max (0 + realizes_initFastGen.scratchSize + 1)
    (2 + realizes_whpStepPureGen.scratchSize + 1)

/-- Parameter-free total register count `132 + scratchWhp` (`0..11` for
`BitPackedDoubleTabulation.resampleCode`, `16..26` for persistent control and ABI registers,
`32..131` for `WhpCoreParams` / `WhpParams`, and `132..` for `Realizes` scratch). -/
noncomputable def rWhp : ℕ :=
  132 + scratchWhp

private theorem le_rWhp : 132 ≤ rWhp := by
  dsimp only [rWhp]
  omega

/-- Canonical embedding `Fin 132 → Fin rWhp` for fixed hash, control, ABI, and parameter
registers. -/
private noncomputable def sReg : Fin 132 → Fin rWhp :=
  Fin.castLE le_rWhp

private theorem sReg_injective : Function.Injective sReg :=
  Fin.castLE_injective le_rWhp

@[simp] private theorem sReg_inj {i j : Fin 132} : sReg i = sReg j ↔ i = j :=
  sReg_injective.eq_iff

@[simp] private theorem val_sReg (i : Fin 132) : (sReg i).val = i.val := rfl

private theorem sReg_ne {i j : Fin 132} (h : i ≠ j) : sReg i ≠ sReg j :=
  fun heq => h (sReg_injective heq)

@[simp] private theorem update_sReg (f : Fin rWhp → ℕ) (j : Fin 132) (v : ℕ) (i : Fin 132) :
    Function.update f (sReg j) v (sReg i) = if i = j then v else f (sReg i) := by
  simp only [Function.update_apply, sReg_inj]

private theorem set_regs_sReg_ne (x : Data rWhp) {i j : Fin 132} (h : i ≠ j) (v : ℕ) :
    (x.set (sReg j) v).regs (sReg i) = x.regs (sReg i) := by
  rw [Data.set_regs, Function.update_of_ne (sReg_ne h)]

/-- Embedding `Fin 12 → Fin rWhp` (`0..11`) for `BitPackedDoubleTabulation.resampleCode`. -/
private noncomputable def resampleReg : Fin 12 → Fin rWhp :=
  Fin.castLE (by dsimp only [rWhp]; omega)

private theorem resampleReg_injective : Function.Injective resampleReg :=
  Fin.castLE_injective _

@[simp] private theorem val_resampleReg (i : Fin 12) : (resampleReg i).val = i.val := rfl

private theorem notMem_range_resampleReg {r : Fin rWhp} (hr : 12 ≤ r.val) :
    r ∉ Set.range resampleReg := by
  rintro ⟨i, rfl⟩
  have := i.isLt
  dsimp only [resampleReg, Fin.val_castLE] at hr
  omega

/-- Persistent base-address register `16` (`sReg 16`). -/
private noncomputable abbrev baseReg : Fin rWhp := sReg 16

/-- Bump-pointer frontier register `17` (`sReg 17`). -/
noncomputable def frontierReg : Fin rWhp := sReg 17

/-- Scratch pointer register `18` (`sReg 18`) for `allocSpan` and `zeroFillCode`. -/
private noncomputable abbrev curReg : Fin rWhp := sReg 18

/-- Constant-`0` scratch register `19` (`sReg 19`) for `zeroFillCode`. -/
private noncomputable abbrev zeroReg : Fin rWhp := sReg 19

/-- Constant-`1` scratch register `20` (`sReg 20`) for `zeroFillCode`. -/
private noncomputable abbrev oneReg : Fin rWhp := sReg 20

/-- Input operation-tag register `21` (`0` = `query`, `1` = `insert`, `2` = `delete`). -/
private noncomputable abbrev tagReg : Fin rWhp := sReg 21

/-- Input key register `22` (`u.val`). -/
private noncomputable abbrev argUReg : Fin rWhp := sReg 22

/-- Input value register `23` (`v` for `insert`, `0` otherwise). -/
private noncomputable abbrev argVReg : Fin rWhp := sReg 23

/-- Nominal output register `24` for `SubroutineCode.output`. -/
noncomputable def outReg : Fin rWhp := sReg 24

/-- Output `Option ℕ` presence-tag register `25` (`0` = `none`, `1` = `some`). -/
noncomputable def resTagReg : Fin rWhp := sReg 25

/-- Output `Option ℕ` value-payload register `26`. -/
noncomputable def resValReg : Fin rWhp := sReg 26

/-- Register block `32..99` holding the 68 words of `WhpCoreParams` during `initFastCode`. -/
private noncomputable def coreParamReg (i : Fin 68) : Fin rWhp :=
  sReg ⟨32 + i.val, by omega⟩

@[simp] private theorem val_coreParamReg (i : Fin 68) : (coreParamReg i).val = 32 + i.val := rfl

/-- Register block `32..131` holding the 100 encoded words of `WhpParams` during `opCode`. -/
private noncomputable def whpParamReg (i : Fin (WordEncoding.width WhpParams)) : Fin rWhp :=
  sReg ⟨32 + i.val, by have := i.isLt; change i.val < 68 + (16 + 16) at this; omega⟩

@[simp] private theorem val_whpParamReg (i : Fin (WordEncoding.width WhpParams)) :
    (whpParamReg i).val = 32 + i.val := rfl

/-- Load `vals ⟨0, _⟩ .. vals ⟨k, _⟩` into `reg ⟨0, _⟩ .. reg ⟨k, _⟩` in `k + 1` `const`
instructions. -/
private noncomputable def loadVecUpTo {m : ℕ} (reg : Fin m → Fin rWhp) (vals : Fin m → ℕ) :
    (k : ℕ) → k < m → Code .exact rWhp
  | 0, hk => .op (.const (reg ⟨0, hk⟩) (vals ⟨0, hk⟩))
  | k + 1, hk =>
    .seq (loadVecUpTo reg vals k (by omega))
         (.op (.const (reg ⟨k + 1, hk⟩) (vals ⟨k + 1, hk⟩)))

/-- Load all 68 words of `mkWhpCoreParams c U V w n_max` into `coreParamReg` in 68 instructions. -/
private noncomputable def loadCoreParamsCode (c U V w n_max : ℕ) : Code .exact rWhp :=
  loadVecUpTo coreParamReg (mkWhpCoreParams c U V w n_max) 67 (by decide)

/-- Load all 100 encoded words of `mkWhpParams c U V w n_max` into `whpParamReg` in 100
instructions. -/
private noncomputable def loadWhpParamsCode (c U V w n_max : ℕ) : Code .exact rWhp :=
  loadVecUpTo whpParamReg (WordEncoding.encode (α := WhpParams) (mkWhpParams c U V w n_max))
    99 (by change 99 < 68 + (16 + 16); decide)

/-- Source register map `Fin.append coreParamReg ![baseReg]` for `initFastGenProg`. -/
private noncomputable def srcInit :
    Fin (WordEncoding.width (WhpCoreParams × ℕ)) → Fin rWhp :=
  Fin.append coreParamReg ![baseReg]

/-- Scratch register map for `initFastGenProg` at `132 + j.val`. -/
private noncomputable def tmpInit
    (j : Fin (0 + realizes_initFastGen.scratchSize + 1)) : Fin rWhp :=
  ⟨132 + j.val, by have := j.isLt; dsimp only [rWhp, scratchWhp]; omega⟩

@[simp] private theorem val_tmpInit (j : Fin (0 + realizes_initFastGen.scratchSize + 1)) :
    (tmpInit j).val = 132 + j.val := rfl

/-- Emitted native code for `initFastGenProg`. -/
private noncomputable def initFastCode : Code .exact rWhp :=
  realizes_initFastGen.code frontierReg srcInit tmpInit

/-- Source register map for `whpStepPureGenProg` (`(((wp, base), opTag), (u_val, v_val))`). -/
private noncomputable def srcStep :
    Fin (WordEncoding.width (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ))) → Fin rWhp :=
  Fin.append
    (Fin.append (Fin.append whpParamReg ![baseReg]) ![tagReg])
    (Fin.append ![argUReg] ![argVReg])

/-- Scratch and output register map for `whpStepPureGenProg`, placing outputs `0, 1` in
`resTagReg` (`25`) and `resValReg` (`26`) and scratch registers at `132 + j.val`. -/
private noncomputable def tmpStep
    (j : Fin (2 + realizes_whpStepPureGen.scratchSize + 1)) : Fin rWhp :=
  if j.val = 0 then resTagReg
  else if j.val = 1 then resValReg
  else ⟨132 + j.val, by have := j.isLt; dsimp only [rWhp, scratchWhp]; omega⟩

@[simp] private theorem val_tmpStep (j : Fin (2 + realizes_whpStepPureGen.scratchSize + 1)) :
    (tmpStep j).val = if j.val = 0 then 25 else if j.val = 1 then 26 else 132 + j.val := by
  dsimp only [tmpStep]
  split_ifs <;> rfl

/-- Emitted native code for `whpStepPureGenProg`. -/
private noncomputable def stepCode : Code .exact rWhp :=
  realizes_whpStepPureGen.code frontierReg srcStep tmpStep

/-- Load `baseReg + off` into `sReg 0` (`resampleReg 0`) in 2 instructions. -/
private noncomputable def setResampleBaseCode (off : ℕ) : Code .exact rWhp :=
  .seq (.op (.const (sReg 0) off))
       (.op (.exactBin .add (sReg 0) baseReg (sReg 0)))

/-- Resample the bucket double-tabulation seed at `base + offHashBkt`. -/
private noncomputable def resampleBktCode (c U w n_max : ℕ) : Code .exact rWhp :=
  (BitPackedDoubleTabulation.resampleCode w (w0Whp U) (cTabWhp c) (dTabWhp c)
    (bCharWhp n_max) (bWhp n_max)).rename resampleReg

/-- Resample the fingerprint double-tabulation seed at `base + offHashFp c w n_max`. -/
private noncomputable def resampleFpCode (c U w n_max : ℕ) : Code .exact rWhp :=
  (BitPackedDoubleTabulation.resampleCode w (w0Whp U) (cTabWhp c) (dTabWhp c)
    (bCharWhp n_max) (fpBitsWhp n_max)).rename resampleReg

/-- Large-regime (`whpThreshold c ≤ n_max`) self-contained setup code: samples both
double-tabulation hash seeds into `[base + offHashBkt, base + offQuotWhp c w n_max)` and runs
`loadCoreParamsCode` followed by `initFastCode`. -/
private noncomputable def initLargeCode (c U V w n_max : ℕ) : Code .exact rWhp :=
  .seq
    (.seq
      (.seq (setResampleBaseCode offHashBkt) (resampleBktCode c U w n_max))
      (.seq (setResampleBaseCode (offHashFp c w n_max)) (resampleFpCode c U w n_max)))
    (.seq (loadCoreParamsCode c U V w n_max) initFastCode)

/-- Unified `initSetup` code across both `< whpThreshold c` (`.op (.const zeroReg 0)`, since zeroed
memory already represents `emptySmallState`) and `≥ whpThreshold c` (`initLargeCode`). -/
noncomputable def initSetupCode (c U V w n_max : ℕ) : Code .exact rWhp :=
  if n_max < whpThreshold c then .op (.const zeroReg 0) else initLargeCode c U V w n_max

/-- Complete per-operation Word-RAM body: loads the 100 static `WhpParams` words into `whpParamReg`
and executes the compiled `stepCode` (`whpStepPureGenProg`). -/
noncomputable def opCode (c U V w n_max : ℕ) : Code .exact rWhp :=
  .seq (loadWhpParamsCode c U V w n_max) stepCode

/-- Canonical `SubroutineCode` for the fixed-capacity high-probability succinct dynamic dictionary
on `rWhp` registers. -/
noncomputable def subroutineCode (c U V w n_max : ℕ) :
    SubroutineCode .exact rWhp 0 where
  allocSpan :=
    .seq (.op (.copy baseReg frontierReg))
    (.seq (.op (.const curReg (whpSpace c U V w n_max)))
          (.op (.exactBin .add frontierReg frontierReg curReg)))
  initSetup := initSetupCode c U V w n_max
  code := opCode c U V w n_max
  frontierReg := frontierReg
  baseReg := baseReg
  initParams := Fin.elim0
  curReg := curReg
  zeroReg := zeroReg
  oneReg := oneReg
  incCur := .exactBin .add curReg curReg oneReg
  input r := decide (r = tagReg ∨ r = argUReg ∨ r = argVReg)
  output := outReg

/-! ## Section 2: Register Disjointness, Width Independence (`¬ReadsWidth`), and Cost Budgets -/

private theorem val_srcInit (i : Fin (WordEncoding.width (WhpCoreParams × ℕ))) :
    (srcInit i).val = 16 ∨ (32 ≤ (srcInit i).val ∧ (srcInit i).val < 100) := by
  dsimp only [srcInit]
  refine i.addCases (fun i₀ => ?_) (fun i₁ => ?_)
  · rw [Fin.append_left, val_coreParamReg]; right; omega
  · rw [Fin.append_right]; fin_cases i₁; left; rfl

private theorem tmpInit_injective : Function.Injective tmpInit := fun _ _ h => by
  have hv := (val_tmpInit _).symm.trans ((congrArg Fin.val h).trans (val_tmpInit _))
  exact Fin.ext (by omega)

private theorem srcInit_ne_tmpInit (i : Fin (WordEncoding.width (WhpCoreParams × ℕ)))
    (j : Fin (0 + realizes_initFastGen.scratchSize + 1)) :
    srcInit i ≠ tmpInit j := fun h => by
  have hv := (congrArg Fin.val h).trans (val_tmpInit j)
  have hs := val_srcInit i
  omega

private theorem tmpInit_ne_frontier (j : Fin (0 + realizes_initFastGen.scratchSize + 1)) :
    tmpInit j ≠ frontierReg := fun h => by
  have hv : (tmpInit j).val = 17 := congrArg Fin.val h
  rw [val_tmpInit] at hv
  omega

private theorem srcInit_ne_frontier (i : Fin (WordEncoding.width (WhpCoreParams × ℕ))) :
    srcInit i ≠ frontierReg := fun h => by
  have hv : (srcInit i).val = 17 := congrArg Fin.val h
  have hs := val_srcInit i
  omega

private theorem val_srcStep
    (i : Fin (WordEncoding.width (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)))) :
    (srcStep i).val ∈ ({16, 21, 22, 23} : Set ℕ) ∨
      (32 ≤ (srcStep i).val ∧ (srcStep i).val < 132) := by
  dsimp only [srcStep]
  refine i.addCases (fun i₀ => ?_) (fun i₁ => ?_)
  · rw [Fin.append_left]
    refine i₀.addCases (fun j₀ => ?_) (fun j₁ => ?_)
    · rw [Fin.append_left]
      refine j₀.addCases (fun k₀ => ?_) (fun k₁ => ?_)
      · rw [Fin.append_left, val_whpParamReg]
        have hk := k₀.isLt
        change k₀.val < 68 + (16 + 16) at hk
        right; omega
      · rw [Fin.append_right]; fin_cases k₁; left; simp
    · rw [Fin.append_right]; fin_cases j₁; left; simp
  · rw [Fin.append_right]
    refine i₁.addCases (fun j₀ => ?_) (fun j₁ => ?_)
    · rw [Fin.append_left]; fin_cases j₀; left; simp
    · rw [Fin.append_right]; fin_cases j₁; left; simp

private theorem tmpStep_injective : Function.Injective tmpStep := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [val_tmpStep, val_tmpStep] at hv
  split_ifs at hv <;> exact Fin.ext (by omega)

private theorem srcStep_ne_tmpStep
    (i : Fin (WordEncoding.width (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ))))
    (j : Fin (2 + realizes_whpStepPureGen.scratchSize + 1)) :
    srcStep i ≠ tmpStep j := fun h => by
  have hv := (congrArg Fin.val h).trans (val_tmpStep j)
  have hs := val_srcStep i
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  split_ifs at hv <;> omega

private theorem tmpStep_ne_frontier (j : Fin (2 + realizes_whpStepPureGen.scratchSize + 1)) :
    tmpStep j ≠ frontierReg := fun h => by
  have hv : (tmpStep j).val = 17 := congrArg Fin.val h
  rw [val_tmpStep] at hv
  split_ifs at hv <;> omega

private theorem srcStep_ne_frontier
    (i : Fin (WordEncoding.width (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)))) :
    srcStep i ≠ frontierReg := fun h => by
  have hv : (srcStep i).val = 17 := congrArg Fin.val h
  have hs := val_srcStep i
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  omega

private theorem not_readsWidth_loadVecUpTo {m : ℕ} (reg : Fin m → Fin rWhp) (vals : Fin m → ℕ)
    (k : ℕ) (hk : k < m) :
    ¬(loadVecUpTo reg vals k hk).ReadsWidth := by
  induction k with
  | zero => simp [loadVecUpTo, Code.ReadsWidth, Op.ReadsWidth]
  | succ k ih =>
    simp only [loadVecUpTo, Code.ReadsWidth, Op.ReadsWidth, or_false]
    exact ih (by omega)

private theorem not_readsWidth_resampleCode (w w₀ c_tab d b_char M_out : ℕ) :
    ¬(BitPackedDoubleTabulation.resampleCode w w₀ c_tab d b_char M_out).ReadsWidth := by
  simp [BitPackedDoubleTabulation.resampleCode, Tabulation.randFillLoop, Tabulation.randFillBody,
    Code.readsWidth_rename, Code.ReadsWidth, Op.ReadsWidth, Op.exactBin]

private theorem not_readsWidth_initSetupCode (c U V w n_max : ℕ) :
    ¬(initSetupCode c U V w n_max).ReadsWidth := by
  unfold initSetupCode
  split_ifs
  · simp [Code.ReadsWidth, Op.ReadsWidth]
  · have hfast := (realizes_initFastGen.code_spec frontierReg srcInit tmpInit
      tmpInit_injective srcInit_ne_tmpInit tmpInit_ne_frontier srcInit_ne_frontier).1
    have hload := not_readsWidth_loadVecUpTo coreParamReg (mkWhpCoreParams c U V w n_max) 67
      (by decide)
    have hbkt := not_readsWidth_resampleCode w (w0Whp U) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (bWhp n_max)
    have hfp := not_readsWidth_resampleCode w (w0Whp U) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (fpBitsWhp n_max)
    simp only [initLargeCode, setResampleBaseCode, resampleBktCode, resampleFpCode,
      loadCoreParamsCode, initFastCode, Code.ReadsWidth, Code.readsWidth_rename,
      Op.ReadsWidth, Op.exactBin]
    tauto

private theorem not_readsWidth_opCode (c U V w n_max : ℕ) :
    ¬(opCode c U V w n_max).ReadsWidth := by
  have hstep := (realizes_whpStepPureGen.code_spec frontierReg srcStep tmpStep
    tmpStep_injective srcStep_ne_tmpStep tmpStep_ne_frontier srcStep_ne_frontier).1
  have hload := not_readsWidth_loadVecUpTo whpParamReg
    (WordEncoding.encode (α := WhpParams) (mkWhpParams c U V w n_max)) 99
    (by change 99 < 68 + (16 + 16); decide)
  simp only [opCode, loadWhpParamsCode, stepCode, Code.ReadsWidth]
  exact not_or.mpr ⟨hload, hstep⟩

/-- Width independence (`¬ReadsWidth`) of all emitted programs in `subroutineCode c U V w n_max`:
none of `initFresh`, `initClear`, or `code` inspects the ambient word width `w`. -/
theorem not_readsWidth_subroutineCode (c U V w n_max : ℕ) :
    ¬(subroutineCode c U V w n_max).initFresh.ReadsWidth ∧
    ¬(subroutineCode c U V w n_max).initClear.ReadsWidth ∧
    ¬(subroutineCode c U V w n_max).code.ReadsWidth := by
  have hsetup := not_readsWidth_initSetupCode c U V w n_max
  have hop := not_readsWidth_opCode c U V w n_max
  have halloc : ¬(subroutineCode c U V w n_max).allocSpan.ReadsWidth := by
    simp [subroutineCode, Code.ReadsWidth, Op.ReadsWidth, Op.exactBin]
  have hzero : ¬(subroutineCode c U V w n_max).zeroFillCode.ReadsWidth := by
    simp [SubroutineCode.zeroFillCode, subroutineCode, Code.ReadsWidth, Op.ReadsWidth, Op.exactBin]
  refine ⟨?_, ?_, hop⟩
  · simp only [SubroutineCode.initFresh, Code.ReadsWidth]
    exact not_or.mpr ⟨halloc, hsetup⟩
  · simp only [SubroutineCode.initClear, Code.ReadsWidth]
    tauto

/-- `c`-only deterministic worst-case instruction budget for a single dictionary operation
(`100` parameter-load instructions plus the `Realizes` instruction budget for
`whpFastBranchCost c`). -/
noncomputable def worstCaseTimeWhp (c : ℕ) : ℕ :=
  100 + realizes_whpStepPureGen.factor * (whpFastBranchCost c + 1)

/-- Deterministic worst-case instruction budget for `initSetupCode c U V w n_max`. -/
@[expose] noncomputable def initSetupSteps (c w n_max : ℕ) : ℕ :=
  if n_max < whpThreshold c then 1
  else
    2 + BitPackedDoubleTabulation.resampleSteps w (cTabWhp c) (dTabWhp c)
          (bCharWhp n_max) (bWhp n_max) +
    2 + BitPackedDoubleTabulation.resampleSteps w (cTabWhp c) (dTabWhp c)
          (bCharWhp n_max) (fpBitsWhp n_max) +
    68 + realizes_initFastGen.factor * (initFastCostWhp n_max + 1)

/-- Worst-case random word draws (`unifFin`) made by `initSetupCode c U V w n_max`. -/
@[expose] def initSetupRandCalls (c w n_max : ℕ) : ℕ :=
  if n_max < whpThreshold c then 0
  else
    (1 + (BitPackedDoubleTabulation.topWords w (cTabWhp c) (dTabWhp c) (bCharWhp n_max) +
          BitPackedDoubleTabulation.botWords w (dTabWhp c) (bCharWhp n_max) (bWhp n_max))) +
    (1 + (BitPackedDoubleTabulation.topWords w (cTabWhp c) (dTabWhp c) (bCharWhp n_max) +
          BitPackedDoubleTabulation.botWords w (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max)))

/-- Parameter-free slope on `n_max` in `initTime_impl_le`. -/
noncomputable def initTimeLinearFactor : ℕ :=
  8 * realizes_initFastGen.factor + 20

/-- Parameter-free additive constant in `initTime_impl_le`. -/
noncomputable def initTimeLinearConst : ℕ :=
  6 * realizes_initFastGen.factor + 135

/-! ## Section 3: Representation Invariants and ABI Conventions -/

/-- Trajectory-coupled representation invariant at `base` for oblivious operation history `ops`,
seed `θ : SeedWhp c U n_max`, abstract dictionary state `s_abs`, and machine state `x`. -/
def GhostRep (c U V w n_max base : ℕ) (ops : List (Dynamic.Op U))
    (θ : SeedWhp c U n_max) (s_abs : Dictionary.State U) (x : Data rWhp) : Prop :=
  x.Bounded w ∧
  x.regs baseReg = base ∧
  x.regs frontierReg = base + whpSpace c U V w n_max ∧
  WhpMemRep base c U V w n_max θ (whpRunPure c U n_max θ ops) x.mem ∧
  ValidWhpState c U V n_max θ (whpRunPure c U n_max θ ops) s_abs ∧
  s_abs = ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 ∧
  (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) ops

/-- Existential state-level representation invariant exposed by `(impl ...).rep`. -/
def Rep (c U V w n_max base : ℕ) (θ : SeedWhp c U n_max)
    (s_abs : Dictionary.State U) (x : Data rWhp) : Prop :=
  ∃ ops : List (Dynamic.Op U), GhostRep c U V w n_max base ops θ s_abs x

/-- Standalone register encoding for `Dynamic.Op U` matching `encodeOpWhp`:
* `.query u`: `tagReg = 0`, `argUReg = u.val`, `argVReg = 0`
* `.insert u v`: `tagReg = 1`, `argUReg = u.val`, `argVReg = v`
* `.delete u`: `tagReg = 2`, `argUReg = u.val`, `argVReg = 0` -/
noncomputable def encode {U : ℕ} : Dynamic.Op U → Fin rWhp → ℕ
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

/-- Argument-matching predicate tying `(tagReg, (argUReg, argVReg))` to `encodeOpWhp o`. -/
noncomputable def argMatch {U : ℕ} (o : Dynamic.Op U) (regs : Fin rWhp → ℕ) : Prop :=
  encodeOpWhp o = (regs tagReg, (regs argUReg, regs argVReg))

/-- Output decoder reading `Option ℕ` from `(resTagReg, resValReg)` for `.query` and `()` for
`.insert`/`.delete`. -/
@[expose] noncomputable def decode {U : ℕ} :
    (o : Dynamic.Op U) → (Fin rWhp → ℕ) → Option o.Result
  | .query _, regs =>
    if regs resTagReg = 0 then some none
    else some (some (regs resValReg))
  | .insert _ _, _ => some ()
  | .delete _, _ => some ()

@[simp] private theorem input_tagReg (c U V w n_max : ℕ) :
    (subroutineCode c U V w n_max).input tagReg = true :=
  decide_eq_true (Or.inl rfl)

@[simp] private theorem input_argUReg (c U V w n_max : ℕ) :
    (subroutineCode c U V w n_max).input argUReg = true :=
  decide_eq_true (Or.inr (Or.inl rfl))

@[simp] private theorem input_argVReg (c U V w n_max : ℕ) :
    (subroutineCode c U V w n_max).input argVReg = true :=
  decide_eq_true (Or.inr (Or.inr rfl))

private theorem input_sReg_eq_false {c U V w n_max : ℕ} {i : Fin 132}
    (h1 : i ≠ 21) (h2 : i ≠ 22) (h3 : i ≠ 23) :
    (subroutineCode c U V w n_max).input (sReg i) = false := by
  dsimp only [subroutineCode]
  rw [decide_eq_false_iff_not]
  rintro (h | h | h)
  · exact h1 (sReg_injective h)
  · exact h2 (sReg_injective h)
  · exact h3 (sReg_injective h)

/-- Output registers `resTagReg` and `resValReg` are disjoint from `subroutineCode.input`. -/
@[simp] theorem input_resRegs_eq_false (c U V w n_max : ℕ) :
    (subroutineCode c U V w n_max).input resTagReg = false ∧
    (subroutineCode c U V w n_max).input resValReg = false :=
  ⟨input_sReg_eq_false (by decide) (by decide) (by decide),
   input_sReg_eq_false (by decide) (by decide) (by decide)⟩

private theorem thirtyTwo_le_whpSpace (c U V w n_max : ℕ) :
    32 ≤ whpSpace c U V w n_max := by
  unfold whpSpace
  split_ifs <;> [dsimp only [smallSpaceWhp]; dsimp only [largeSpaceWhp]] <;> omega

/-! ## Section 4: Execution of `loadVecUpTo`, `allocSpan`, `initSetupCode`, and `opCode` -/

private theorem regs_comp_append {α β : Type} [WordEncoding α] [WordEncoding β]
    {x : Data rWhp} {a : α} {b : β}
    {src₁ : Fin (WordEncoding.width α) → Fin rWhp}
    {src₂ : Fin (WordEncoding.width β) → Fin rWhp}
    (h₁ : x.regs ∘ src₁ = WordEncoding.encode a)
    (h₂ : x.regs ∘ src₂ = WordEncoding.encode b) :
    x.regs ∘ Fin.append src₁ src₂ = WordEncoding.encode (α := α × β) (a, b) := by
  change x.regs ∘ Fin.append src₁ src₂ = Fin.append (WordEncoding.encode a) (WordEncoding.encode b)
  funext i
  refine i.addCases (fun i₀ => ?_) (fun i₁ => ?_)
  · simp only [Function.comp_apply, Fin.append_left]
    exact congrFun h₁ i₀
  · simp only [Function.comp_apply, Fin.append_right]
    exact congrFun h₂ i₁

private theorem regs_comp_singleton {x : Data rWhp} (reg : Fin rWhp) (v : ℕ)
    (h : x.regs reg = v) :
    x.regs ∘ (![reg] : Fin (WordEncoding.width ℕ) → Fin rWhp) =
      WordEncoding.encode (α := ℕ) v := by
  funext i
  fin_cases i
  exact h

private theorem fits_encode_mkWhpParams {base c U V w n_max : ℕ}
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + whpSpace c U V w n_max))
    (i : Fin (WordEncoding.width WhpParams)) :
    Fits w (WordEncoding.encode (α := WhpParams) (mkWhpParams c U V w n_max) i) := by
  obtain ⟨hcore, hhash⟩ := fits_mkWhpParams hw hnU hU hV hfit
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    unfold mkWhpParams
    split_ifs <;> rfl
  change Fits w (Fin.append (WordEncoding.encode (mkWhpParams c U V w n_max).1)
    (WordEncoding.encode (mkWhpParams c U V w n_max).2) i)
  refine i.addCases (fun i₀ => ?_) (fun i₁ => ?_)
  · rw [Fin.append_left, hwp1]
    exact hcore i₀
  · rw [Fin.append_right]
    change Fits w (Fin.append (WordEncoding.encode (wpHash1 (mkWhpParams c U V w n_max)))
      (WordEncoding.encode (wpHash2 (mkWhpParams c U V w n_max))) i₁)
    refine i₁.addCases (fun j₀ => ?_) (fun j₁ => ?_)
    · rw [Fin.append_left]
      exact (hhash j₀).1
    · rw [Fin.append_right]
      exact (hhash j₁).2

private theorem exec_loadVecUpTo {w m : ℕ} {reg : Fin m → Fin rWhp} {vals : Fin m → ℕ}
    (hreg : ∀ i : Fin m, (reg i).val = 32 + i.val)
    (hfits : ∀ i : Fin m, Fits w (vals i))
    {x : Data rWhp} (hx_bdd : x.Bounded w) (k : ℕ) (hk : k < m) :
    ∃ y : Data rWhp,
      ExecWithin w (loadVecUpTo reg vals k hk) x y (k + 1) ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      (∀ j : Fin m, j.val ≤ k → y.regs (reg j) = vals j) ∧
      (∀ r : Fin rWhp, r.val < 32 → y.regs r = x.regs r) := by
  have hne : ∀ (r : Fin rWhp) (n : ℕ) (hn : n < m), r.val ≠ 32 + n → r ≠ reg ⟨n, hn⟩ :=
    fun r n hn h heq => h (by subst heq; exact hreg _)
  induction k with
  | zero =>
    let y := x.set (reg ⟨0, hk⟩) (vals ⟨0, hk⟩)
    have hex : ExecWithin (B := .exact) w (.op (.const (reg ⟨0, hk⟩) (vals ⟨0, hk⟩))) x y 1 :=
      ExecWithin.const (hfits ⟨0, hk⟩)
    refine ⟨y, hex, hex.bounded hx_bdd, rfl, fun j hj => ?_, fun r hr => ?_⟩
    · obtain rfl : j = ⟨0, hk⟩ := Fin.ext (Nat.le_zero.mp hj)
      simp [y, Data.set_regs]
    · rw [Data.set_regs, Function.update_of_ne (hne r 0 hk (by omega))]
  | succ k ih =>
    obtain ⟨y₀, hex₀, hy₀_bdd, hmem₀, hparam₀, hlow₀⟩ := ih (by omega)
    let y := y₀.set (reg ⟨k + 1, hk⟩) (vals ⟨k + 1, hk⟩)
    have hex₁ : ExecWithin (B := .exact) w
        (.op (.const (reg ⟨k + 1, hk⟩) (vals ⟨k + 1, hk⟩))) y₀ y 1 :=
      ExecWithin.const (hfits ⟨k + 1, hk⟩)
    refine ⟨y, hex₀.seq hex₁, hex₁.bounded hy₀_bdd, hmem₀, fun j hj => ?_, fun r hr => ?_⟩
    · by_cases hjk : j.val = k + 1
      · obtain rfl : j = ⟨k + 1, hk⟩ := Fin.ext hjk
        simp [y, Data.set_regs]
      · rw [Data.set_regs, Function.update_of_ne (hne _ _ hk (by rw [hreg]; omega))]
        exact hparam₀ j (by omega)
    · rw [Data.set_regs, Function.update_of_ne (hne r _ hk (by omega))]
      exact hlow₀ r hr

private theorem span_exec_whp {c U V w n_max base : ℕ}
    (hfit : Fits w (base + whpSpace c U V w n_max))
    {x : Data rWhp} (hfr : x.regs frontierReg = base) :
    ∃ x₁ : Data rWhp,
      ExecWithin w (subroutineCode c U V w n_max).allocSpan x x₁ 3 ∧
      x₁.mem = x.mem ∧
      x₁.regs baseReg = base ∧
      x₁.regs frontierReg = base + whpSpace c U V w n_max ∧
      (∀ j : Fin 0, x₁.regs ((subroutineCode c U V w n_max).initParams j) = Fin.elim0 j) := by
  let s₁ := x.set baseReg (x.regs frontierReg)
  let s₂ := s₁.set curReg (whpSpace c U V w n_max)
  let s₃ := s₂.set frontierReg (base + whpSpace c U V w n_max)
  have e₁ : ExecWithin (B := .exact) w (.op (.copy baseReg frontierReg)) x s₁ 1 :=
    ExecWithin.copy
  have e₂ : ExecWithin (B := .exact) w (.op (.const curReg (whpSpace c U V w n_max))) s₁ s₂ 1 :=
    ExecWithin.const (hfit.of_le (Nat.le_add_left _ _))
  have e₃ : ExecWithin (B := .exact) w
      (.op (.exactBin .add frontierReg frontierReg curReg)) s₂ s₃ 1 := by
    apply ExecWithin.op
    rw [Op.eval_exactBin]
    have hfr₂ : s₂.regs frontierReg = base :=
      (set_regs_sReg_ne _ (by decide) _).trans ((set_regs_sReg_ne _ (by decide) _).trans hfr)
    have hcur₂ : s₂.regs curReg = whpSpace c U V w n_max := by
      simp only [s₂, Data.set_regs, update_sReg, ↓reduceIte]
    rw [hfr₂, hcur₂]
    exact Data.put_of_fits hfit
  refine ⟨s₃, e₁.seq (e₂.seq e₃), rfl, ?_, ?_, fun j => Fin.elim0 j⟩
  · unfold s₃ s₂ s₁ frontierReg; unfold frontierReg at hfr
    simp only [Data.set_regs, update_sReg, Fin.reduceEq, ↓reduceIte, hfr]
  · unfold s₃ frontierReg
    simp only [Data.set_regs, update_sReg, ↓reduceIte]

private theorem exec_setResampleBaseCode {w base off : ℕ}
    (hfit : Fits w (base + off))
    {x : Data rWhp} (hbase : x.regs baseReg = base) :
    Exec w (setResampleBaseCode off) x (x.set (sReg 0) (base + off)) 2 := by
  let x₁ := x.set (sReg 0) off
  have e₁ : Exec (B := .exact) w (.op (.const (sReg 0) off)) x x₁ 1 :=
    Exec.const (hfit.of_le (Nat.le_add_left _ _))
  have e₂ : Exec (B := .exact) w (.op (.exactBin .add (sReg 0) baseReg (sReg 0)))
      x₁ (x.set (sReg 0) (base + off)) 1 := by
    have hx_set : x₁.set (sReg 0) (base + off) = x.set (sReg 0) (base + off) := by
      cases x; simp [x₁, Data.set]
    rw [← hx_set]
    apply Exec.op
    rw [Op.eval_exactBin]
    have hb₁ : x₁.regs baseReg = base := (set_regs_sReg_ne _ (by decide) _).trans hbase
    have h0₁ : x₁.regs (sReg 0) = off := by
      simp only [x₁, Data.set_regs, update_sReg, ↓reduceIte]
    rw [hb₁, h0₁]
    exact Data.put_of_fits hfit
  exact e₁.seq e₂

/-- One seed-resampling stage of `initLargeCode`: point `sReg 0` at `base + off`, then resample
the double-tabulation seed stored there. -/
private noncomputable def resampleStage (w w₀ base off c_tab d b_char M : ℕ) (y : Data rWhp) :
    ProbComp (Data rWhp × ℕ) :=
  (fun z : Data 12 × ℕ => (z.1.extend resampleReg (y.set (sReg 0) (base + off)), 2 + z.2)) <$>
    BitPackedDoubleTabulation.resampleComp (base + off) w w₀ c_tab d b_char M
      ((y.set (sReg 0) (base + off)).comap resampleReg)

private theorem resampleStage_regs0 (y : Data rWhp) (a : ℕ) :
    ((y.set (sReg 0) a).comap resampleReg).regs 0 = a := by
  change (y.set (sReg 0) a).regs (sReg 0) = a
  simp [Data.set_regs]

private theorem resampleStage_execRand {w w₀ base off c_tab d b_char M : ℕ} (hw : 0 < w)
    (hw₀ : w₀ ≤ w)
    (hfit : Fits w ((base + off) + BitPackedDoubleTabulation.space w c_tab d b_char M))
    {y : Data rWhp} (hbase : y.regs baseReg = base) :
    ExecRand w (.seq (setResampleBaseCode off)
        ((BitPackedDoubleTabulation.resampleCode w w₀ c_tab d b_char M).rename resampleReg)) y
      (resampleStage w w₀ base off c_tab d b_char M y) := by
  have hr := (BitPackedDoubleTabulation.resampleCode_execRand hw hw₀
    (resampleStage_regs0 y (base + off)) hfit).rename resampleReg_injective
  simpa only [resampleStage, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    using (exec_setResampleBaseCode (hfit.of_le (Nat.le_add_right _ _)) hbase).seqRand hr

private theorem isQueryBounded_resampleStage {w w₀ base off c_tab d b_char M : ℕ}
    (y : Data rWhp) :
    (resampleStage w w₀ base off c_tab d b_char M y).IsQueryBounded
      (1 + (BitPackedDoubleTabulation.topWords w c_tab d b_char +
        BitPackedDoubleTabulation.botWords w d b_char M)) := by
  rw [resampleStage, ← bind_pure_comp]
  simpa only [Nat.add_zero] using
    (BitPackedDoubleTabulation.isQueryBounded_resampleComp _ _ _ _ _ _ _ _).bind
      fun _ => .pure _ 0

/-- Pathwise postcondition of `resampleStage`: it keeps `Bounded w`, `baseReg` and `frontierReg`,
writes a seed representation into `[base + off, base + off + space)`, leaves other memory alone,
and takes `2 + resampleSteps` instructions. -/
private theorem mem_support_resampleStage {w w₀ base off c_tab d b_char M : ℕ} (hw : 0 < w)
    (hw₀ : w₀ ≤ w)
    (hfit : Fits w ((base + off) + BitPackedDoubleTabulation.space w c_tab d b_char M))
    {y : Data rWhp} (hy : y.Bounded w) {z : Data rWhp × ℕ}
    (hz : z ∈ (resampleStage w w₀ base off c_tab d b_char M y).support) :
    z.1.Bounded w ∧ z.1.regs baseReg = y.regs baseReg ∧
      z.1.regs frontierReg = y.regs frontierReg ∧
      BitPackedDoubleTabulation.SeedRep (base + off) w w₀ c_tab d b_char M
        (BitPackedDoubleTabulation.extractSeed (base + off) w w₀ c_tab d b_char M z.1.mem)
        z.1.mem ∧
      (∀ a, (a < base + off ∨ base + off + BitPackedDoubleTabulation.space w c_tab d b_char M ≤ a) →
        z.1.mem a = y.mem a) ∧
      z.2 = 2 + BitPackedDoubleTabulation.resampleSteps w c_tab d b_char M := by
  have hya := hy.set (i := sReg 0) (hfit.of_le (Nat.le_add_right _ _))
  rw [resampleStage, ← bind_pure_comp] at hz
  obtain ⟨u, hu, hp⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
  cases OracleComp.eq_of_mem_supportWith_pure hp
  obtain ⟨_, hsr, _, hmem, hu_bdd, hst⟩ := BitPackedDoubleTabulation.mem_support_resampleComp hw
    hw₀ (resampleStage_regs0 y (base + off)) hfit (hya.comap resampleReg) hu
  have hregs (i : Fin 132) (hi : 12 ≤ i.val) (h0 : i ≠ 0) :
      (u.1.extend resampleReg (y.set (sReg 0) (base + off))).regs (sReg i) = y.regs (sReg i) := by
    rw [Data.extend_regs_of_notMem _ _ (notMem_range_resampleReg hi), set_regs_sReg_ne _ h0]
  exact ⟨hu_bdd.extend resampleReg_injective hya, hregs 16 (by decide) (by decide),
    hregs 17 (by decide) (by decide), hsr, hmem, by rw [hst]⟩

private theorem exec_initFastTail {c U V w n_max base : ℕ} {θ : SeedWhp c U n_max}
    (henv : WhpLargeEnv c U V w n_max w base)
    {y₂ : Data rWhp}
    (hy₂_bdd : y₂.Bounded w)
    (hy₂_base : y₂.regs baseReg = base)
    (hy₂_fr : y₂.regs frontierReg = base + whpSpace c U V w n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ y₂.mem)
    (hz_hdr : ∀ a, base ≤ a → a < base + 32 → y₂.mem a = 0)
    (hz_body : ∀ a, base + offQuotWhp c w n_max ≤ a →
      a < base + largeSpaceWhp c U V w n_max → y₂.mem a = 0) :
    ∃ z_det : Data rWhp × ℕ,
      z_det.2 ≤ 68 + realizes_initFastGen.factor * (initFastCostWhp n_max + 1) ∧
      Exec w (.seq (loadCoreParamsCode c U V w n_max) initFastCode) y₂ z_det.1 z_det.2 ∧
      z_det.1.Bounded w ∧
      z_det.1.regs baseReg = base ∧
      z_det.1.regs frontierReg = base + whpSpace c U V w n_max ∧
      SeedWhpMemRep base c U w n_max θ z_det.1.mem ∧
      FastMemRep base c U V w n_max (emptyFastState n_max) z_det.1.mem ∧
      (∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → z_det.1.mem a = y₂.mem a) := by
  have ⟨_, hw, _, hth, hnU, hU, hV, hfit⟩ := henv
  have hsp_eq : whpSpace c U V w n_max = largeSpaceWhp c U V w n_max := by
    unfold whpSpace; exact ite_eq_right (Nat.not_lt.mpr hth)
  obtain ⟨hcore_fit, _⟩ := fits_mkWhpParams hw hnU hU hV hfit
  obtain ⟨y₃, ⟨n₁, hn₁, he₁⟩, hy₃_bdd, hy₃_mem, hparam₃, hlow₃⟩ :=
    exec_loadVecUpTo val_coreParamReg hcore_fit hy₂_bdd 67 (by decide)
  have hy₃_base : y₃.regs baseReg = base := (hlow₃ baseReg (by decide)).trans hy₂_base
  have hy₃_fr : y₃.regs frontierReg = base + whpSpace c U V w n_max :=
    (hlow₃ frontierReg (by decide)).trans hy₂_fr
  let cp := mkWhpCoreParams c U V w n_max
  have hin : y₃.regs ∘ srcInit = WordEncoding.encode (α := WhpCoreParams × ℕ) (cp, base) :=
    regs_comp_append (funext fun i => hparam₃ i (by omega))
      (regs_comp_singleton baseReg base hy₃_base)
  obtain ⟨hseed', hfast', hfr_st, hmc, hvp, hout⟩ :=
    initFastGenProg_spec (s := memoryState frontierReg y₃) henv
      (hy₃_mem.symm ▸ hseed)
      (fun a ha1 ha2 => (congrFun hy₃_mem a).trans (hz_hdr a ha1 ha2))
      (fun a ha1 ha2 => (congrFun hy₃_mem a).trans (hz_body a ha1 ha2))
  have hvh_mem := hvp.validHistory (wellFormed_memoryState hy₃_bdd)
    (by change _ ≤ y₃.regs frontierReg; omega)
  have hsafe : WhpLargeEnvGen w cp base := ⟨c, U, V, w, n_max, henv, rfl⟩
  have hcode := (realizes_initFastGen.code_spec frontierReg srcInit tmpInit
    tmpInit_injective srcInit_ne_tmpInit tmpInit_ne_frontier srcInit_ne_frontier).2
  obtain ⟨y₄, ⟨n₂, hn₂, he₂⟩, hm₄, _, hframe₄⟩ :=
    hcode w (cp, base) y₃ hy₃_bdd hin hsafe hvh_mem
  rw [clientState_width w] at hm₄
  have hmem₄ : y₄.mem = ((Memory.spec 0).clientState (memoryState frontierReg y₃)
      (initFastGenProg (cp, base))).mem := congrArg Memory.State.mem hm₄
  have hfr₄ : y₄.regs frontierReg = base + whpSpace c U V w n_max :=
    (congrArg Memory.State.frontier hm₄).trans (hfr_st.trans hy₃_fr)
  have hbase₄ : y₄.regs baseReg = base :=
    (hframe₄ baseReg (sReg_ne (by decide))
      fun j hj => by
        have hv : (tmpInit j).val = 16 := congrArg Fin.val hj
        rw [val_tmpInit] at hv
        omega).trans hy₃_base
  have hy₄_bdd : y₄.Bounded w := he₂.bounded hy₃_bdd
  have hn₂' : n₂ ≤ realizes_initFastGen.factor * (initFastCostWhp n_max + 1) := by
    dsimp only [cp] at hn₂
    rwa [hmc, Nat.add_zero] at hn₂
  refine ⟨(y₄, n₁ + n₂), by omega, he₁.seq he₂, hy₄_bdd, hbase₄, hfr₄,
    hmem₄ ▸ hseed', hmem₄ ▸ hfast', fun a ha => ?_⟩
  exact (congrFun hmem₄ a).trans ((hout a ha).trans (congrFun hy₃_mem a))

private theorem setup_exec_whp {c U V w n_max base : ℕ}
    (hc : 0 < c) (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + whpSpace c U V w n_max))
    {x₁ : Data rWhp}
    (hx₁ : x₁.Bounded w)
    (hbase : x₁.regs baseReg = base)
    (hfr : x₁.regs frontierReg = base + whpSpace c U V w n_max)
    (hz : ∀ a ∈ (Block.mk base (whpSpace c U V w n_max)).footprint, x₁.mem a = 0) :
    ∃ (m₀ : ProbComp (Data rWhp × ℕ)) (ν₀ : PMF (SeedWhp c U n_max × Data rWhp)),
      ExecRand w (subroutineCode c U V w n_max).initSetup x₁ m₀ ∧
      OracleComp.IsQueryBounded m₀ (initSetupRandCalls c w n_max) ∧
      (∀ z ∈ m₀.support, z.2 ≤ initSetupSteps c w n_max) ∧
      ν₀.map Prod.snd = (Prod.fst <$> m₀).eval ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ 1 * (seedLawWhp c U n_max) θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs frontierReg = base + whpSpace c U V w n_max ∧
        GhostRep c U V w n_max base [] p.1 (Dictionary.empty U) p.2 ∧
        Modifies (Block.mk base (whpSpace c U V w n_max)).footprint x₁.mem p.2.mem := by
  classical
  by_cases hsm : n_max < whpThreshold c
  · have hsp : whpSpace c U V w n_max = smallSpaceWhp U V w n_max := by
      unfold whpSpace; exact ite_eq_left hsm
    let x₁' := x₁.set zeroReg 0
    let m₀ : ProbComp (Data rWhp × ℕ) := pure (x₁', 1)
    let ν₀ : PMF (SeedWhp c U n_max × Data rWhp) :=
      (seedLawWhp c U n_max).map fun θ => (θ, x₁')
    have hex : ExecRand w (subroutineCode c U V w n_max).initSetup x₁ m₀ := by
      change ExecRand w (initSetupCode c U V w n_max) x₁ (pure (x₁', 1))
      unfold initSetupCode
      rw [ite_eq_left hsm]
      exact (Exec.const (Nat.two_pow_pos w)).execRand
    have hqb : OracleComp.IsQueryBounded m₀ (initSetupRandCalls c w n_max) := by
      unfold initSetupRandCalls
      rw [ite_eq_left hsm]
      exact .pure _ 0
    have htime : ∀ z ∈ m₀.support, z.2 ≤ initSetupSteps c w n_max := by
      intro z hz_mem
      cases OracleComp.eq_of_mem_supportWith_pure hz_mem
      unfold initSetupSteps
      rw [ite_eq_left hsm]
    have hsnd : ν₀.map Prod.snd = (Prod.fst <$> m₀).eval := by
      rw [PMF.map_comp, map_pure, ProbComp.eval_pure]
      exact PMF.map_const _ x₁'
    have hfst : ∀ θ, (ν₀.map Prod.fst) θ ≤ 1 * (seedLawWhp c U n_max) θ := fun θ => by
      rw [PMF.map_comp, one_mul, show Prod.fst ∘ (fun θ => (θ, x₁')) = id from rfl, PMF.map_id]
    refine ⟨m₀, ν₀, hex, hqb, htime, hsnd, hfst, fun p hp => ?_⟩
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨θ, _, rfl⟩ := hp
    have hend := smallOffsets_eq U V w n_max
    have hs1 : offSmallPres = 32 := rfl
    have hs2 : offSmallKeys U w n_max = offSmallPres + packedWords n_max 1 w := rfl
    have hs3 : offSmallVals U w n_max = offSmallKeys U w n_max + packedWords n_max (keyBits U) w :=
      rfl
    have hz_in (a : ℕ) (ha1 : base ≤ a) (ha2 : a < base + smallSpaceWhp U V w n_max) :
        x₁'.mem a = 0 :=
      hz a (by simp [Block.mem_footprint, Block.Owns, hsp, ha1, ha2])
    have hsm_rep : SmallMemRep base U V w n_max emptySmallState x₁'.mem :=
      ⟨hz_in base le_rfl (by omega), fun i hi =>
        ⟨readPacked_eq_zero_of_zero_range hw hi fun a _ _ => hz_in a (by omega) (by omega),
         readPacked_eq_zero_of_zero_range hw hi fun a _ _ => hz_in a (by omega) (by omega),
         readPacked_eq_zero_of_zero_range hw hi fun a _ _ => hz_in a (by omega) (by omega)⟩⟩
    have hinit_eq : whpRunPure c U n_max θ [] = .small emptySmallState := ite_eq_left hsm
    have hx₁'_bdd : x₁'.Bounded w := hx₁.set (Nat.two_pow_pos w)
    have hx₁'_fr : x₁'.regs frontierReg = base + whpSpace c U V w n_max :=
      (set_regs_sReg_ne _ (by decide) _).trans hfr
    refine ⟨hx₁'_fr, ⟨hx₁'_bdd, (set_regs_sReg_ne _ (by decide) _).trans hbase, hx₁'_fr, ?_,
      whpRunPure_spec hnU θ trivial, rfl, trivial⟩, Modifies.refl _ _⟩
    rw [hinit_eq]
    exact ⟨hsm, hsm_rep⟩
  · have hth : whpThreshold c ≤ n_max := Nat.le_of_not_lt hsm
    have hsp : whpSpace c U V w n_max = largeSpaceWhp c U V w n_max := by
      unfold whpSpace
      exact ite_eq_right hsm
    have henv : WhpLargeEnv c U V w n_max w base := ⟨hc, hw, rfl, hth, hnU, hU, hV, hfit⟩
    have hw0_le : w0Whp U ≤ w := w0Whp_le_w hw hU
    have hlog_w := log_n_max_lt_w hth hnU hU
    have hlog_ge := log_ge_mul_ell hth
    have hell := Dynamic.one_le_logLogFactor n_max
    have hbc_le : bCharWhp n_max ≤ w := ((Nat.div_le_self _ 4).trans_lt hlog_w).le
    have hb_le : bWhp n_max ≤ w := ((Nat.sub_le _ _).trans_lt hlog_w).le
    have hfp_le : fpBitsWhp n_max ≤ w := by
      have hfp_log : fpBitsWhp n_max ≤ Nat.log 2 n_max := by
        unfold fpBitsWhp
        omega
      exact (hfp_log.trans_lt hlog_w).le
    have hfit_bkt_end : Fits w ((base + offHashBkt) +
        BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max)
          (bWhp n_max)) := by
      refine hfit.of_le ?_
      rw [hsp]; dsimp only [largeSpaceWhp, offHashBkt]; omega
    have hfit_fp_end : Fits w ((base + offHashFp c w n_max) +
        BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp n_max)
          (fpBitsWhp n_max)) := by
      refine hfit.of_le ?_
      rw [hsp]; dsimp only [largeSpaceWhp, offHashFp, offHashBkt, bktHashWords]; omega
    let m₁ := resampleStage w (w0Whp U) base offHashBkt (cTabWhp c) (dTabWhp c) (bCharWhp n_max)
      (bWhp n_max) x₁
    let m₂_of := resampleStage w (w0Whp U) base (offHashFp c w n_max) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (fpBitsWhp n_max)
    let m₁₂ : ProbComp (Data rWhp × ℕ) := do
      let z₁ ← m₁
      let z₂ ← m₂_of z₁.1
      pure (z₂.1, z₁.2 + z₂.2)
    let ext₁ (mem : ℕ → ℕ) : BktSeed c U n_max :=
      BitPackedDoubleTabulation.extractSeed (base + offHashBkt) w (w0Whp U)
        (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max) mem
    let ext₂ (mem : ℕ → ℕ) : FpSeed c U n_max :=
      BitPackedDoubleTabulation.extractSeed (base + offHashFp c w n_max) w (w0Whp U)
        (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max) mem
    let extPair (y : Data rWhp) : SeedWhp c U n_max := (ext₁ y.mem, ext₂ y.mem)
    have hex₁₂ : ExecRand w
        (.seq
          (.seq (setResampleBaseCode offHashBkt) (resampleBktCode c U w n_max))
          (.seq (setResampleBaseCode (offHashFp c w n_max)) (resampleFpCode c U w n_max)))
        x₁ m₁₂ :=
      (resampleStage_execRand hw hw0_le hfit_bkt_end hbase).seq (m₂ := m₂_of) fun _ hz₁ =>
        resampleStage_execRand hw hw0_le hfit_fp_end
          ((mem_support_resampleStage hw hw0_le hfit_bkt_end hx₁ hz₁).2.1.trans hbase)
    have hz_in (a : ℕ) (ha1 : base ≤ a) (ha2 : a < base + largeSpaceWhp c U V w n_max) :
        x₁.mem a = 0 :=
      hz a (by simp [Block.mem_footprint, Block.Owns, hsp, ha1, ha2])
    let hasInv (y₂ : Data rWhp) : Prop :=
      y₂.Bounded w ∧
      y₂.regs baseReg = base ∧
      y₂.regs frontierReg = base + whpSpace c U V w n_max ∧
      SeedWhpMemRep base c U w n_max (extPair y₂) y₂.mem ∧
      (∀ a, base ≤ a → a < base + 32 → y₂.mem a = 0) ∧
      (∀ a, base + offQuotWhp c w n_max ≤ a →
        a < base + largeSpaceWhp c U V w n_max → y₂.mem a = 0)
    have hy₂_pair : ∀ z₁ ∈ m₁.support, ∀ z₂ ∈ (m₂_of z₁.1).support,
        extPair z₂.1 = (ext₁ z₁.1.mem, ext₂ z₂.1.mem) ∧ hasInv z₂.1 ∧
        (∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → z₂.1.mem a = x₁.mem a) ∧
        z₁.2 + z₂.2 =
          2 + BitPackedDoubleTabulation.resampleSteps w (cTabWhp c) (dTabWhp c)
                (bCharWhp n_max) (bWhp n_max) +
          2 + BitPackedDoubleTabulation.resampleSteps w (cTabWhp c) (dTabWhp c)
                (bCharWhp n_max) (fpBitsWhp n_max) := by
      intro z₁ hz₁ z₂ hz₂
      obtain ⟨hb₁, hbase₁, hfr₁, hsr₁, hmem₁, hst₁⟩ :=
        mem_support_resampleStage hw hw0_le hfit_bkt_end hx₁ hz₁
      obtain ⟨hb₂, hbase₂, hfr₂, hsr₂, hmem₂, hst₂⟩ :=
        mem_support_resampleStage hw hw0_le hfit_fp_end hb₁ hz₂
      have hl_hb : offHashBkt = 32 := rfl
      have hl_hf : offHashFp c w n_max =
          offHashBkt + BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c)
            (bCharWhp n_max) (bWhp n_max) := rfl
      have hl_q : offQuotWhp c w n_max =
          offHashFp c w n_max + BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c)
            (bCharWhp n_max) (fpBitsWhp n_max) := rfl
      have hq_le_sp : offQuotWhp c w n_max ≤ largeSpaceWhp c U V w n_max := by
        dsimp only [largeSpaceWhp, offQuotWhp, offHashFp, offHashBkt, bktHashWords, fpHashWords]
        omega
      have hsr₁₂ := BitPackedDoubleTabulation.seedRep_congr_mem hw hsr₁
        (fun a _ ha2 => hmem₂ a (Or.inl (by omega)))
      have hext₁ := BitPackedDoubleTabulation.extractSeed_eq_of_seedRep hsr₁₂
      rw [← hext₁] at hsr₁₂
      refine ⟨Prod.ext hext₁ rfl, ⟨hb₂, hbase₂.trans (hbase₁.trans hbase),
        hfr₂.trans (hfr₁.trans hfr), ⟨hsr₁₂, hsr₂⟩, fun a ha1 ha2 => ?_, fun a ha1 ha2 => ?_⟩,
        fun a ha => ?_, by omega⟩
      · rw [hmem₂ a (Or.inl (by omega)), hmem₁ a (Or.inl (by omega))]
        exact hz_in a ha1 (by omega)
      · rw [hmem₂ a (Or.inr (by omega)), hmem₁ a (Or.inr (by omega))]
        exact hz_in a (by omega) ha2
      · rw [hmem₂ a (by omega), hmem₁ a (by omega)]
    have hm₁₂_supp : ∀ z₁₂ ∈ m₁₂.support,
        hasInv z₁₂.1 ∧
        (∀ a, (a < base ∨ base + largeSpaceWhp c U V w n_max ≤ a) → z₁₂.1.mem a = x₁.mem a) ∧
        z₁₂.2 =
          2 + BitPackedDoubleTabulation.resampleSteps w (cTabWhp c) (dTabWhp c)
                (bCharWhp n_max) (bWhp n_max) +
          2 + BitPackedDoubleTabulation.resampleSteps w (cTabWhp c) (dTabWhp c)
                (bCharWhp n_max) (fpBitsWhp n_max) := by
      intro z₁₂ hz₁₂
      dsimp only [m₁₂] at hz₁₂
      obtain ⟨z₁, hz₁, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz₁₂
      obtain ⟨z₂, hz₂, hp⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
      cases OracleComp.eq_of_mem_supportWith_pure hp
      exact (hy₂_pair z₁ hz₁ z₂ hz₂).2
    let tailEx (y₂ : Data rWhp) (hi : hasInv y₂) :=
      exec_initFastTail henv hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2
    let detOut (y₂ : Data rWhp) : Data rWhp × ℕ :=
      if hi : hasInv y₂ then Classical.choose (tailEx y₂ hi) else (y₂, 0)
    let m_tail (y₂ : Data rWhp) : ProbComp (Data rWhp × ℕ) := pure (detOut y₂)
    let m₀ : ProbComp (Data rWhp × ℕ) := do
      let z₁₂ ← m₁₂
      let z_t ← m_tail z₁₂.1
      pure (z_t.1, z₁₂.2 + z_t.2)
    let ν₀ : PMF (SeedWhp c U n_max × Data rWhp) :=
      m₁₂.eval.map fun z₁₂ => (extPair z₁₂.1, (detOut z₁₂.1).1)
    have hex_all : ExecRand w (subroutineCode c U V w n_max).initSetup x₁ m₀ := by
      change ExecRand w (initSetupCode c U V w n_max) x₁ m₀
      unfold initSetupCode
      rw [ite_eq_right hsm]
      refine ExecRand.seq hex₁₂ (m₂ := m_tail) fun z₁₂ hz₁₂ => ?_
      have hi : hasInv z₁₂.1 := (hm₁₂_supp z₁₂ hz₁₂).1
      have hd_eq : detOut z₁₂.1 = Classical.choose (tailEx z₁₂.1 hi) := dite_eq_left hi
      dsimp only [m_tail]
      rw [hd_eq]
      exact (Classical.choose_spec (tailEx z₁₂.1 hi)).2.1.execRand
    have hqb : OracleComp.IsQueryBounded m₀ (initSetupRandCalls c w n_max) := by
      unfold initSetupRandCalls
      rw [ite_eq_right hsm]
      have hqb₁₂ : m₁₂.IsQueryBounded _ :=
        (isQueryBounded_resampleStage _).bind fun _ =>
          (isQueryBounded_resampleStage _).bind fun _ => .pure _ 0
      simpa only [m₀, m_tail, pure_bind, Nat.add_zero] using hqb₁₂.bind fun _ => .pure _ 0
    have htime : ∀ z ∈ m₀.support, z.2 ≤ initSetupSteps c w n_max := by
      intro z hz_mem
      dsimp only [m₀] at hz_mem
      obtain ⟨z₁₂, hz₁₂, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz_mem
      obtain ⟨z_t, hz_t, hp⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
      cases OracleComp.eq_of_mem_supportWith_pure hz_t
      cases OracleComp.eq_of_mem_supportWith_pure hp
      obtain ⟨hi, _, hst₁₂⟩ := hm₁₂_supp z₁₂ hz₁₂
      have hd_eq : detOut z₁₂.1 = Classical.choose (tailEx z₁₂.1 hi) := dite_eq_left hi
      have hle_t : (detOut z₁₂.1).2 ≤
          68 + realizes_initFastGen.factor * (initFastCostWhp n_max + 1) := by
        rw [hd_eq]
        exact (Classical.choose_spec (tailEx z₁₂.1 hi)).1
      simp only [initSetupSteps, hsm, ↓reduceIte]
      omega
    have hsnd : ν₀.map Prod.snd = (Prod.fst <$> m₀).eval := by
      have hm₀_eq : (Prod.fst <$> m₀) = (fun z₁₂ => (detOut z₁₂.1).1) <$> m₁₂ := by
        simp [m₀, m_tail, ← bind_pure_comp, bind_assoc]
      rw [hm₀_eq, ProbComp.eval_map]
      simp [ν₀, PMF.map_comp, Function.comp_def]
    have hfst : ∀ θ, (ν₀.map Prod.fst) θ ≤ 1 * (seedLawWhp c U n_max) θ := by
      have hmap_fst : ν₀.map Prod.fst = seedLawWhp c U n_max := by
        have hunif {off M : ℕ} (hM : M ≤ w) (y : Data rWhp) :
            (resampleStage w (w0Whp U) base off (cTabWhp c) (dTabWhp c)
              (bCharWhp n_max) M y).eval.map
              (fun z : Data rWhp × ℕ => BitPackedDoubleTabulation.extractSeed (base + off) w
                (w0Whp U) (cTabWhp c) (dTabWhp c) (bCharWhp n_max) M z.1.mem) =
            PMF.uniformOfFintype _ := by
          rw [resampleStage, ProbComp.eval_map, PMF.map_comp]
          exact BitPackedDoubleTabulation.map_extractSeed_eval_resampleComp hw hbc_le hM _
        dsimp only [ν₀, m₁₂]
        rw [PMF.map_comp, Function.comp_def, ProbComp.eval_bind, PMF.map_bind]
        have hinner : ∀ z₁ ∈ m₁.eval.support,
            ((do let z₂ ← m₂_of z₁.1; pure (z₂.1, z₁.2 + z₂.2)).eval).map
              (fun z₁₂ : Data rWhp × ℕ => extPair z₁₂.1) =
            (PMF.uniformOfFintype (FpSeed c U n_max)).map
              (fun θ₂ => (ext₁ z₁.1.mem, θ₂)) := fun z₁ hz₁ => by
          rw [ProbComp.support_eval] at hz₁
          rw [bind_pure_comp, ProbComp.eval_map, PMF.map_comp]
          have hcongr : (m₂_of z₁.1).eval.map
              ((fun z₁₂ : Data rWhp × ℕ => extPair z₁₂.1) ∘
                fun z₂ : Data rWhp × ℕ => (z₂.1, z₁.2 + z₂.2)) =
              (m₂_of z₁.1).eval.map
                ((fun θ₂ => (ext₁ z₁.1.mem, θ₂)) ∘ fun z₂ : Data rWhp × ℕ => ext₂ z₂.1.mem) :=
            Cslib.Probability.PMF.map_congr_on_support _ _ _ fun z₂ hz₂ =>
              (hy₂_pair z₁ hz₁ z₂ (ProbComp.support_eval _ ▸ hz₂)).1
          rw [hcongr, ← PMF.map_comp, hunif hfp_le z₁.1]
        rw [Cslib.Probability.PMF.bind_congr_on_support _ _ _ hinner]
        refine (PMF.bind_map _ (fun z₁ : Data rWhp × ℕ => ext₁ z₁.1.mem)
          (fun θ₁ => (PMF.uniformOfFintype (FpSeed c U n_max)).map (fun θ₂ => (θ₁, θ₂)))).symm.trans
          ?_
        rw [hunif hb_le x₁]
        exact PMF.uniformOfFintype_prod _ _
      intro θ
      rw [hmap_fst, one_mul]
    refine ⟨m₀, ν₀, hex_all, hqb, htime, hsnd, hfst, fun p hp => ?_⟩
    dsimp only [ν₀] at hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨z₁₂, hz₁₂, rfl⟩ := hp
    rw [ProbComp.support_eval] at hz₁₂
    obtain ⟨hi, hzo, _⟩ := hm₁₂_supp z₁₂ hz₁₂
    have hspec := Classical.choose_spec (tailEx z₁₂.1 hi)
    have hd_eq : detOut z₁₂.1 = Classical.choose (tailEx z₁₂.1 hi) := dite_eq_left hi
    obtain ⟨_, _, hy₄_bdd, hy₄_base, hy₄_fr, hy₄_seed, hy₄_fast, hy₄_out⟩ := hspec
    rw [← hd_eq] at hy₄_bdd hy₄_base hy₄_fr hy₄_seed hy₄_fast hy₄_out
    have hinit_eq : whpRunPure c U n_max (extPair z₁₂.1) [] = .fast (emptyFastState n_max) := by
      change whpInitPure c n_max = _
      exact ite_eq_right hsm
    have hmod : Modifies (Block.mk base (whpSpace c U V w n_max)).footprint
        x₁.mem (detOut z₁₂.1).1.mem := by
      intro a ha
      simp only [Block.mem_footprint, Block.Owns, hsp, not_and_or, not_le, not_lt] at ha
      exact (hy₄_out a ha).trans (hzo a ha)
    refine ⟨hy₄_fr, ⟨hy₄_bdd, hy₄_base, hy₄_fr, ?_, whpRunPure_spec hnU _ trivial, rfl, trivial⟩,
      hmod⟩
    rw [hinit_eq]
    exact ⟨hth, hy₄_seed, hy₄_fast⟩

/-! ## Section 5: Per-Operation Deterministic Execution (`exec_opCode`) -/

private theorem run_fst_snoc {U V n_max : ℕ} (s : Dictionary.State U)
    (ops : List (Dynamic.Op U)) (o : Dynamic.Op U) :
    ((Dynamic.spec U V n_max).run s (ops ++ [o])).1 =
      (Dynamic.step ((Dynamic.spec U V n_max).run s ops).1 o).1 := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => exact ih _

private theorem whpRunPure_snoc (c U n_max : ℕ) (θ : SeedWhp c U n_max)
    (ops : List (Dynamic.Op U)) (o : Dynamic.Op U) :
    whpRunPure c U n_max θ (ops ++ [o]) =
      (whpStepPure c U n_max θ (whpRunPure c U n_max θ ops) o).1 := by
  suffices ∀ st l, whpRunFrom c U n_max θ st (l ++ [o]) =
      (whpStepPure c U n_max θ (whpRunFrom c U n_max θ st l) o).1 from this _ ops
  intro st l
  induction l generalizing st with
  | nil => rfl
  | cons _ _ ih => exact ih _

private theorem exec_opCode {c U V w n_max base : ℕ}
    (hc : 0 < c) (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + whpSpace c U V w n_max))
    {ops : List (Dynamic.Op U)} {θ : SeedWhp c U n_max} {s_abs : Dictionary.State U}
    {x : Data rWhp} {o : Dynamic.Op U}
    (hgrep : GhostRep c U V w n_max base ops θ s_abs x)
    (hval_op : (Dynamic.spec U V n_max).valid s_abs o)
    (harg : argMatch o x.regs) :
    ∃ z_op : Data rWhp × ℕ,
      Exec w (opCode c U V w n_max) x z_op.1 z_op.2 ∧
      decode o z_op.1.regs = some ((Dynamic.spec U V n_max).stepFn s_abs o).2 ∧
      GhostRep c U V w n_max base (ops ++ [o]) θ
        ((Dynamic.spec U V n_max).stepFn s_abs o).1 z_op.1 ∧
      Modifies (Block.mk base (whpSpace c U V w n_max)).footprint x.mem z_op.1.mem ∧
      (IsFastStepHit c U n_max ops o θ → z_op.2 ≤ worstCaseTimeWhp c) := by
  obtain ⟨hx_bdd, hbase, hfr, hrep_mem, hv_st, hs_eq, hvh⟩ := hgrep
  obtain ⟨x₀, ⟨n₁, hn₁, he₁⟩, hx₀_bdd, hx₀_mem, hparam₀, hlow₀⟩ :=
    exec_loadVecUpTo val_whpParamReg (fits_encode_mkWhpParams hw hnU hU hV hfit) hx_bdd 99
      (by change 99 < 68 + (16 + 16); decide)
  have hx₀_base : x₀.regs baseReg = base := (hlow₀ baseReg (by decide)).trans hbase
  have hx₀_fr : x₀.regs frontierReg = base + whpSpace c U V w n_max :=
    (hlow₀ frontierReg (by decide)).trans hfr
  let wp := mkWhpParams c U V w n_max
  let enc := encodeOpWhp o
  let d_in : ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ) := (((wp, base), enc.1), enc.2)
  have henc_x₀ : (x₀.regs tagReg, (x₀.regs argUReg, x₀.regs argVReg)) = enc := by
    rw [hlow₀ tagReg (by decide), hlow₀ argUReg (by decide), hlow₀ argVReg (by decide)]
    exact harg.symm
  have hin : x₀.regs ∘ srcStep =
      WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) d_in :=
    regs_comp_append
      (regs_comp_append
        (regs_comp_append
          (funext fun i => hparam₀ i (by have hk : i.val < 68 + (16 + 16) := i.isLt; omega))
          (regs_comp_singleton baseReg base hx₀_base))
        (regs_comp_singleton tagReg enc.1 (congrArg Prod.fst henc_x₀)))
      (regs_comp_append
        (regs_comp_singleton argUReg enc.2.1 (congrArg (·.2.1) henc_x₀))
        (regs_comp_singleton argVReg enc.2.2 (congrArg (·.2.2) henc_x₀)))
  have hrep₀ : WhpMemRep base c U V w n_max θ (whpRunPure c U n_max θ ops)
      (memoryState frontierReg x₀).mem := by
    dsimp [memoryState]
    rwa [hx₀_mem]
  obtain ⟨hrep', hres', hfr_st, hvp, hout, hfast_mc⟩ :=
    whpStepPureGenProg_spec hc hw hnU hU hV hfit hrep₀ hv_st hval_op
  have hvh_mem := hvp.validHistory (wellFormed_memoryState hx₀_bdd) hx₀_fr.ge
  have hsafe : WhpStepPurePre w d_in (memoryState frontierReg x₀) :=
    ⟨c, U, V, w, n_max, θ, whpRunPure c U n_max θ ops, s_abs, o,
      hc, hw, rfl, hnU, hU, hV, hfit, rfl, hrep₀, hv_st, hval_op, Prod.mk.eta⟩
  have hcode := (realizes_whpStepPureGen.code_spec frontierReg srcStep tmpStep
    tmpStep_injective srcStep_ne_tmpStep tmpStep_ne_frontier srcStep_ne_frontier).2
  obtain ⟨y, ⟨n₂, hn₂, he₂⟩, hm_y, hout_y, hframe_y⟩ :=
    hcode w d_in x₀ hx₀_bdd hin hsafe hvh_mem
  rw [clientState_width w] at hm_y
  have hmem_y : y.mem = ((Memory.spec 0).clientState (memoryState frontierReg x₀)
      (whpStepPureGenProg d_in)).mem := congrArg Memory.State.mem hm_y
  have hfr_y : y.regs frontierReg = base + whpSpace c U V w n_max :=
    (congrArg Memory.State.frontier hm_y).trans (hfr_st.trans hx₀_fr)
  have hbase_y : y.regs baseReg = base :=
    (hframe_y baseReg (sReg_ne (by decide))
      fun j hj => by
        have hv : (tmpStep j).val = 16 := congrArg Fin.val hj
        rw [val_tmpStep] at hv
        split_ifs at hv <;> omega).trans hx₀_base
  have hy_bdd : y.Bounded w := he₂.bounded hx₀_bdd
  have hout0 : y.regs resTagReg = _ := (hout_y 0).trans (by rw [clientResult_width, hres'])
  have hout1 : y.regs resValReg = _ := (hout_y 1).trans (by rw [clientResult_width, hres'])
  obtain ⟨hv_st', hres_opt⟩ := whpStepPure_spec hnU θ hv_st hval_op
  have hdec : decode o y.regs = some ((Dynamic.spec U V n_max).stepFn s_abs o).2 := by
    cases o with
    | query u =>
      have hres_q : (whpStepPure c U n_max θ (whpRunPure c U n_max θ ops) (.query u)).2 =
          s_abs u := hres_opt
      dsimp only [decode]
      rw [hout0, hout1, hres_q]
      cases s_abs u <;> rfl
    | insert _ _ => rfl
    | delete _ => rfl
  have hmod : Modifies (Block.mk base (whpSpace c U V w n_max)).footprint x.mem y.mem := by
    intro a ha
    simp only [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
    rw [hmem_y, hout a ha]
    exact congrFun hx₀_mem a
  have hvh_snoc : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) (ops ++ [o]) :=
    ((Dynamic.spec U V n_max).validHistory_append _ ops [o]).mpr ⟨hvh, hs_eq ▸ hval_op, trivial⟩
  refine ⟨(y, n₁ + n₂), he₁.seq he₂, hdec, ⟨hy_bdd, hbase_y, hfr_y, ?_, ?_,
    by rw [run_fst_snoc, ← hs_eq], hvh_snoc⟩, hmod, fun hhit => ?_⟩
  · rwa [whpRunPure_snoc, hmem_y]
  · rwa [whpRunPure_snoc]
  have hmc_le := hfast_mc ops rfl hhit
  have hn₂_le : n₂ ≤ realizes_whpStepPureGen.factor * (whpFastBranchCost c + 1) := by
    have h1 : memoryCost (whpStepPureGenProg d_in) (memoryState frontierReg x₀) + 0 + 1 ≤
        whpFastBranchCost c + 1 := by
      dsimp only [d_in, wp, enc]
      omega
    exact hn₂.trans (Nat.mul_le_mul_left _ h1)
  dsimp only [worstCaseTimeWhp]
  omega

/-! ## Section 6: `HighProbStateTransitionImpl` Packaging and Headline Theorems -/

/-- Reusable `HighProbStateTransitionImpl` certificate over `Basis.exact` for the fixed-capacity
succinct dynamic dictionary (`Dynamic.spec U V n_max`). -/
@[expose] noncomputable def impl {c U V w n_max base : ℕ}
    (hc : 0 < c) (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + whpSpace c U V w n_max)) :
    HighProbStateTransitionImpl (subroutineCode c U V w n_max)
      (Dynamic.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  HighProbStateTransitionImpl.ofFnGhost
    (Ghost := List (Dynamic.Op U))
    (ghostInit := [])
    (ghostStep := fun ops o => ops ++ [o])
    (Seed := SeedWhp c U n_max)
    (seedLaw := seedLawWhp c U n_max)
    (seedSlack := 1)
    (seedSlack_ne_top := by simp)
    (space := whpSpace c U V w n_max)
    (spanTime := 3)
    (setupTime := initSetupSteps c w n_max)
    (setupRandCalls := initSetupRandCalls c w n_max)
    (worstCaseTime := worstCaseTimeWhp c)
    (failureProb := (max n_max 1 : ℝ≥0∞)⁻¹ ^ c)
    (ghostRep := GhostRep c U V w n_max base)
    (encode := encode)
    (argMatch := argMatch)
    (decode := decode)
    (bounded := by exact fun h => h.1)
    (arguments_fit := by
      intro s o hval i hi
      have h32 := thirtyTwo_le_whpSpace c U V w n_max
      have hfit2 : Fits w 2 := hfit.of_le (by omega)
      have hfit1 : Fits w 1 := hfit2.of_le (by decide)
      have hfit0 : Fits w 0 := hfit2.of_le (by decide)
      rcases of_decide_eq_true hi with rfl | rfl | rfl <;> cases o with
      | query u =>
        dsimp only [encode]
        split_ifs <;> first | exact hfit0 | exact u.isLt.trans hU
      | insert u v =>
        dsimp only [encode]
        split_ifs <;>
          first | exact hfit1 | exact u.isLt.trans hU | exact hval.2.trans hV | exact hfit0
      | delete u =>
        dsimp only [encode]
        split_ifs <;> first | exact hfit2 | exact u.isLt.trans hU | exact hfit0)
    (encode_matches := by
      intro o regs
      cases o <;>
        simp only [argMatch, encode, encodeOpWhp, input_tagReg, input_argUReg, input_argVReg,
          sReg_inj, Fin.reduceEq, ↓reduceIte])
    (rep_supported := by
      intro ops θ s x x' hregs hmem hx'_bdd ⟨_, hbase, hfr, hrep_mem, hv_st, hs_eq, hvh⟩
      have hbase' : x'.regs baseReg = base :=
        (hregs baseReg (input_sReg_eq_false (by decide) (by decide) (by decide))).trans hbase
      have hfr' : x'.regs frontierReg = base + whpSpace c U V w n_max :=
        (hregs frontierReg (input_sReg_eq_false (by decide) (by decide) (by decide))).trans hfr
      exact ⟨hx'_bdd, hbase', hfr', WhpMemRep.congr_footprint hw hmem hrep_mem,
        hv_st, hs_eq, hvh⟩)
    (clear_nodup := by
      change (List.map sReg [18, 19, 20, 16, 17]).Nodup
      exact (List.nodup_map_iff sReg_injective).mpr (by decide))
    (params_not_clear := fun j => Fin.elim0 j)
    (incCur_eval := by
      intro x h1 hfit_inc
      change x.regs oneReg = 1 at h1
      change (Op.exactBin .add curReg curReg oneReg).eval w x = _
      rw [Op.eval_exactBin, h1]
      exact Data.put_of_fits hfit_inc)
    (span_exec := by exact fun _ hfr _ => span_exec_whp hfit hfr)
    (setup_exec := by
      exact fun hx₁ hbase hfr _ hz => setup_exec_whp hc hw hnU hU hV hfit hx₁ hbase hfr hz)
    (step_exec := by
      classical
      intro s ops o ν hval_op hseed hsupp
      obtain ⟨p₀, hp₀⟩ := ν.support_nonempty
      have hs_eq₀ := (hsupp p₀ hp₀).1.2.2.2.2.2.1
      have hvh₀ := (hsupp p₀ hp₀).1.2.2.2.2.2.2
      have hvh_snoc : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) (ops ++ [o]) :=
        ((Dynamic.spec U V n_max).validHistory_append _ ops [o]).mpr
          ⟨hvh₀, hs_eq₀ ▸ hval_op, trivial⟩
      let detStep (p : SeedWhp c U n_max × Data rWhp) : Data rWhp × ℕ :=
        if hp : p ∈ ν.support then
          Classical.choose (exec_opCode hc hw hnU hU hV hfit (hsupp p hp).1 hval_op (hsupp p hp).2)
        else (p.2, 0)
      let m_step (p : SeedWhp c U n_max × Data rWhp) : ProbComp (Data rWhp × ℕ) :=
        pure (detStep p)
      let μ_step (p : SeedWhp c U n_max × Data rWhp) :
          PMF ((SeedWhp c U n_max × Data rWhp) × ℕ) :=
        PMF.pure ((p.1, (detStep p).1), (detStep p).2)
      refine ⟨m_step, μ_step, ?_, ?_, ?_⟩
      · intro p hp
        have hspec := Classical.choose_spec
          (exec_opCode hc hw hnU hU hV hfit (hsupp p hp).1 hval_op (hsupp p hp).2)
        have hd_eq : detStep p = Classical.choose
            (exec_opCode hc hw hnU hU hV hfit (hsupp p hp).1 hval_op (hsupp p hp).2) :=
          dite_eq_left hp
        refine ⟨?_, ?_, ?_⟩
        · dsimp only [m_step]
          rw [hd_eq]
          exact hspec.1.execRand
        · dsimp only [μ_step, m_step]
          rw [ProbComp.eval_pure, PMF.pure_map]
        · intro q hq
          dsimp only [μ_step] at hq
          rw [PMF.support_pure, Set.mem_singleton_iff] at hq
          subst hq
          dsimp only [stepData, stepSeed]
          rw [hd_eq]
          exact ⟨hspec.2.1, hspec.2.2.1, hspec.2.2.2.1⟩
      · intro θ'
        have hmap_eq : (((ν.bind μ_step).map Prod.fst).map Prod.fst) = ν.map Prod.fst := by
          rw [PMF.map_comp, PMF.map_bind]
          dsimp only [μ_step]
          simp only [PMF.pure_map]
          rfl
        rw [hmap_eq]
        exact hseed θ'
      · have hbind_le :
            (ν.bind μ_step).toOuterMeasure {q | worstCaseTimeWhp c < q.2} ≤
              (ν.map Prod.fst).toOuterMeasure {θ | ¬ IsFastStepHit c U n_max ops o θ} := by
          rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
            PMF.toOuterMeasure_apply]
          refine tsum_le_tsum fun p => ?_
          by_cases hp : p ∈ ν.support
          · dsimp only [μ_step]
            rw [PMF.toOuterMeasure_pure_apply]
            have hspec := Classical.choose_spec
              (exec_opCode hc hw hnU hU hV hfit (hsupp p hp).1 hval_op (hsupp p hp).2)
            have hd_eq : detStep p = Classical.choose
                (exec_opCode hc hw hnU hU hV hfit (hsupp p hp).1 hval_op (hsupp p hp).2) :=
              dite_eq_left hp
            by_cases hlt : worstCaseTimeWhp c < (detStep p).2
            · have hnot_hit : ¬ IsFastStepHit c U n_max ops o p.1 := by
                intro hhit
                have hle := hspec.2.2.2.2 hhit
                rw [← hd_eq] at hle
                omega
              simp [hlt, hnot_hit]
            · simp [hlt]
          · simp [(PMF.apply_eq_zero_iff _ _).mpr hp]
        have hseed_le :
            (ν.map Prod.fst).toOuterMeasure {θ | ¬ IsFastStepHit c U n_max ops o θ} ≤
              (seedLawWhp c U n_max).toOuterMeasure {θ | ¬ IsFastStepHit c U n_max ops o θ} := by
          rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
          refine tsum_le_tsum fun θ => ?_
          have hs := hseed θ
          rw [one_mul] at hs
          exact Set.indicator_le_indicator' fun _ => hs
        exact (hbind_le.trans hseed_le).trans (toOuterMeasure_not_isFastStepHit_le hnU hvh_snoc))

/-- Reusable `HighProbStateTransitionImpl` certificate over `Basis.standard` for the fixed-capacity
succinct dynamic dictionary (`Dynamic.spec U V n_max`). -/
@[expose] noncomputable def implStandard {c U V w n_max base : ℕ}
    (hc : 0 < c) (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + whpSpace c U V w n_max)) :
    HighProbStateTransitionImpl (subroutineCode c U V w n_max).toStandard
      (Dynamic.spec U V n_max) w base Fin.elim0 (Dictionary.empty U) :=
  (impl hc hw hnU hU hV hfit).toStandard

private theorem packedWords_le_bits_add_two {N k w : ℕ} (hw : 0 < w) :
    packedWords N k w ≤ N * k + 2 := by
  unfold packedWords
  have h1 : N * k ≤ (N * k) * w := Nat.le_mul_of_pos_right _ hw
  have hlt : N * k + w - 1 < w * (N * k + 1) := by
    rw [Nat.mul_add_one, Nat.mul_comm w]
    omega
  have hdiv : (N * k + w - 1) / w ≤ N * k := Nat.lt_succ_iff.mp (Nat.div_lt_of_lt_mul hlt)
  omega

/-- Explicit `O(n_max)` deterministic upper bound on fresh initialization instructions:
`(impl ...).initTime ≤ initTimeLinearFactor * n_max + initTimeLinearConst`. -/
theorem initTime_impl_le {c U V w n_max base : ℕ}
    (hc : 0 < c) (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + whpSpace c U V w n_max)) :
    (impl hc hw hnU hU hV hfit).initTime = 3 + initSetupSteps c w n_max ∧
    3 + initSetupSteps c w n_max ≤ initTimeLinearFactor * n_max + initTimeLinearConst := by
  refine ⟨rfl, ?_⟩
  unfold initSetupSteps initTimeLinearFactor initTimeLinearConst
  split_ifs with hsm
  · omega
  · have hth : whpThreshold c ≤ n_max := Nat.le_of_not_lt hsm
    obtain ⟨htb1, htb2, htb3, _, _, _⟩ := sublinear_table_bits_le hth
    have hM_le : numBucketsWhp n_max ≤ n_max := by
      have hL12 : 1 ≤ (slabScale n_max) ^ 12 := Nat.one_le_pow 12 _ (slabScale_pos n_max)
      exact (Nat.le_mul_of_pos_right _ hL12).trans (numBucketsWhp_mul_scale_pow12_le hth)
    have hps_le : poolSizeWhp n_max ≤ n_max := Nat.sub_le _ _
    have htw : BitPackedDoubleTabulation.topWords w (cTabWhp c) (dTabWhp c) (bCharWhp n_max) ≤
        n_max + 2 :=
      (packedWords_le_bits_add_two hw).trans (Nat.add_le_add_right htb1 2)
    have hbw1 : BitPackedDoubleTabulation.botWords w (dTabWhp c) (bCharWhp n_max) (bWhp n_max) ≤
        n_max + 2 :=
      (packedWords_le_bits_add_two hw).trans (Nat.add_le_add_right htb2 2)
    have hbw2 : BitPackedDoubleTabulation.botWords w (dTabWhp c) (bCharWhp n_max)
        (fpBitsWhp n_max) ≤ n_max + 2 :=
      (packedWords_le_bits_add_two hw).trans (Nat.add_le_add_right htb3 2)
    have hcost_le : initFastCostWhp n_max + 1 ≤ 8 * n_max + 6 := by
      unfold initFastCostWhp; omega
    have hmul_le : realizes_initFastGen.factor * (initFastCostWhp n_max + 1) ≤
        realizes_initFastGen.factor * (8 * n_max + 6) :=
      Nat.mul_le_mul_left _ hcost_le
    have hr1 : BitPackedDoubleTabulation.resampleSteps w (cTabWhp c) (dTabWhp c)
        (bCharWhp n_max) (bWhp n_max) ≤ 10 * n_max + 30 := by
      unfold BitPackedDoubleTabulation.resampleSteps; omega
    have hr2 : BitPackedDoubleTabulation.resampleSteps w (cTabWhp c) (dTabWhp c)
        (bCharWhp n_max) (fpBitsWhp n_max) ≤ 10 * n_max + 30 := by
      unfold BitPackedDoubleTabulation.resampleSteps; omega
    nlinarith

private theorem execWhpSteps_modifies {B : Basis} {r_ds n_par : ℕ}
    {P : SubroutineCode B r_ds n_par} {D : StateTransitionSpec}
    {w base : ℕ} {params : Fin n_par → ℕ} {s₀ : D.State}
    {C : HighProbStateTransitionImpl P D w base params s₀}
    {out : Fin r_ds} {ops : List D.Op}
    {τ τ_final : PMF (WhpSeqOutcome C.Seed D r_ds)} {m₀ : ℕ → ℕ}
    (hex : C.ExecWhpSteps out ops τ τ_final)
    (hinit : ∀ tr ∈ τ.support, Modifies (Block.mk base C.space).footprint m₀ tr.current.data.mem) :
    ∀ tr ∈ τ_final.support, Modifies (Block.mk base C.space).footprint m₀ tr.current.data.mem := by
  induction hex with
  | nil _ => exact hinit
  | @cons o os τ τ_final m_op μ_step hstep _ ih =>
    refine ih fun tr' htr' => ?_
    rw [PMF.mem_support_bind_iff] at htr'
    obtain ⟨tr, htr, hmap⟩ := htr'
    rw [PMF.mem_support_map_iff] at hmap
    obtain ⟨p, hp, rfl⟩ := hmap
    have ht_cur : tr.current ∈ (τ.map WhpSeqOutcome.current).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨tr, htr, rfl⟩
    have hmod_step := ((hstep tr.current ht_cur).2.2.2.2 p hp).2.2.2.2
    exact fun a ha => (hmod_step a ha).trans (hinit tr htr a ha)

/-- **Headline whole-sequence with-high-probability theorem (`seq_whp`)**:
Starting from zeroed memory on `[base, base + whpSpace c U V w n_max)`, fresh initialization halts
within `(impl ...).initTime + 1` instructions, and across any valid oblivious operation sequence
`ops : List (Dynamic.Op U)` (`ValidHistory (Dictionary.empty U) ops`):
1. every supported branch produces the exact specification state and transcript
   `((Dynamic.spec U V n_max).run (Dictionary.empty U) ops)`, maintains `Rep`, and leaves caller
   memory outside `[base, base + whpSpace c U V w n_max)` untouched (`Modifies`);
2. with probability at least `1 - ops.length * (max n_max 1 : ℝ≥0∞)⁻¹ ^ c`, **every single
   operation** in `ops` executes within `worstCaseTimeWhp c` (`O_c(1)`) deterministic worst-case
   instructions. -/
theorem seq_whp {c U V w n_max base : ℕ}
    (hc : 0 < c) (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + whpSpace c U V w n_max))
    {x : Data rWhp} (ops : List (Dynamic.Op U))
    (hx : x.Bounded w) (hfr : x.regs frontierReg = base)
    (hz : ∀ a ∈ (Block.mk base (whpSpace c U V w n_max)).footprint, x.mem a = 0)
    (hv : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    let C := impl hc hw hnU hU hV hfit
    ∃ (ν₀ : PMF (SeedWhp c U n_max × Data rWhp))
      (τ_final : PMF (WhpSeqOutcome (SeedWhp c U n_max) (Dynamic.spec U V n_max) rWhp)),
      RandHaltsWithin w ((subroutineCode c U V w n_max).initFresh.program outReg) ⟨0, x⟩
        (C.initTime + 1) ∧
      evalRand w ((subroutineCode c U V w n_max).initFresh.program outReg) (C.initTime + 1) ⟨0, x⟩ =
        ν₀.map (fun p => RandCfg.halted (p.2.regs outReg) p.2) ∧
      (∀ p ∈ ν₀.support,
        p.2.Bounded w ∧
        p.2.regs frontierReg = base + whpSpace c U V w n_max ∧
        Rep c U V w n_max base p.1 (Dictionary.empty U) p.2 ∧
        Modifies (Block.mk base (whpSpace c U V w n_max)).footprint x.mem p.2.mem) ∧
      C.ExecWhpSteps outReg ops
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, Dictionary.empty U, p.2⟩) τ_final ∧
      (∀ tr ∈ τ_final.support,
        tr.current.state = ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 ∧
        tr.transcript = ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).2 ∧
        Rep c U V w n_max base tr.current.seed
          ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 tr.current.data ∧
        Modifies (Block.mk base (whpSpace c U V w n_max)).footprint x.mem tr.current.data.mem) ∧
      τ_final.toOuterMeasure {tr | worstCaseTimeWhp c < tr.maxSteps} ≤
        (ops.length : ℝ≥0∞) * (max n_max 1 : ℝ≥0∞)⁻¹ ^ c ∧
      1 - (ops.length : ℝ≥0∞) * (max n_max 1 : ℝ≥0∞)⁻¹ ^ c ≤
        τ_final.toOuterMeasure
          {tr | tr.maxSteps ≤ worstCaseTimeWhp c ∧
            tr.transcript = ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).2} := by
  intro C
  obtain ⟨ν₀, τ_final, hhalts, heval₀, hsupp₀, hex, hsupp_fin, hfail, hsucc⟩ :=
    C.seq_whp_ofFn outReg ops hx hfr (fun j => Fin.elim0 j) hz hv
  have hmod_fin := execWhpSteps_modifies hex (m₀ := x.mem) fun tr htr => by
    rw [PMF.mem_support_map_iff] at htr
    obtain ⟨p, hp, rfl⟩ := htr
    exact (hsupp₀ p hp).2.2.2
  refine ⟨ν₀, τ_final, hhalts, heval₀, hsupp₀, hex, fun tr htr => ?_, hfail, hsucc⟩
  obtain ⟨hst, htrans, hrep⟩ := hsupp_fin tr htr
  exact ⟨hst, htrans, hrep, hmod_fin tr htr⟩

/-- **Polynomial-horizon whole-sequence corollary (`poly_seq_whp`)**:
Instantiating the dictionary at exponent `c + c₀` (`0 < c`) guarantees that starting from `⟨0, x⟩`,
fresh initialization produces `ν₀` in `(impl ...).initTime + 1` steps, every supported trajectory
yields the exact specification state and transcript while preserving caller memory (`Modifies`),
and across any valid oblivious sequence `ops` of polynomial length `ops.length ≤ max n_max 1 ^ c₀`,
every operation in `ops` executes within `worstCaseTimeWhp (c + c₀)` (`O_{c, c₀}(1)`) worst-case
instructions with probability at least `1 - (max n_max 1 : ℝ≥0∞)⁻¹ ^ c`. -/
theorem poly_seq_whp {c c₀ U V w n_max base : ℕ}
    (hc : 0 < c) (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + whpSpace (c + c₀) U V w n_max))
    {x : Data rWhp} (ops : List (Dynamic.Op U))
    (hlen : ops.length ≤ max n_max 1 ^ c₀)
    (hx : x.Bounded w) (hfr : x.regs frontierReg = base)
    (hz : ∀ a ∈ (Block.mk base (whpSpace (c + c₀) U V w n_max)).footprint, x.mem a = 0)
    (hv : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    let C := impl (Nat.add_pos_left hc c₀) hw hnU hU hV hfit
    ∃ (ν₀ : PMF (SeedWhp (c + c₀) U n_max × Data rWhp))
      (τ_final : PMF (WhpSeqOutcome (SeedWhp (c + c₀) U n_max) (Dynamic.spec U V n_max) rWhp)),
      RandHaltsWithin w ((subroutineCode (c + c₀) U V w n_max).initFresh.program outReg) ⟨0, x⟩
        (C.initTime + 1) ∧
      evalRand w ((subroutineCode (c + c₀) U V w n_max).initFresh.program outReg)
        (C.initTime + 1) ⟨0, x⟩ =
        ν₀.map (fun p => RandCfg.halted (p.2.regs outReg) p.2) ∧
      (∀ p ∈ ν₀.support,
        p.2.Bounded w ∧
        p.2.regs frontierReg = base + whpSpace (c + c₀) U V w n_max ∧
        Rep (c + c₀) U V w n_max base p.1 (Dictionary.empty U) p.2 ∧
        Modifies (Block.mk base (whpSpace (c + c₀) U V w n_max)).footprint x.mem p.2.mem) ∧
      C.ExecWhpSteps outReg ops
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, Dictionary.empty U, p.2⟩) τ_final ∧
      (∀ tr ∈ τ_final.support,
        tr.current.state = ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 ∧
        tr.transcript = ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).2 ∧
        Rep (c + c₀) U V w n_max base tr.current.seed
          ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 tr.current.data ∧
        Modifies (Block.mk base (whpSpace (c + c₀) U V w n_max)).footprint x.mem
          tr.current.data.mem) ∧
      τ_final.toOuterMeasure {tr | worstCaseTimeWhp (c + c₀) < tr.maxSteps} ≤
        (max n_max 1 : ℝ≥0∞)⁻¹ ^ c ∧
      1 - (max n_max 1 : ℝ≥0∞)⁻¹ ^ c ≤
        τ_final.toOuterMeasure
          {tr | tr.maxSteps ≤ worstCaseTimeWhp (c + c₀) ∧
            tr.transcript = ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).2} := by
  intro C
  obtain ⟨ν₀, τ_final, hhalts, heval₀, hsupp₀, hex, hsupp_fin, hfail, _⟩ :=
    seq_whp (Nat.add_pos_left hc c₀) hw hnU hU hV hfit ops hx hfr hz hv
  have hfail_poly : τ_final.toOuterMeasure {tr | worstCaseTimeWhp (c + c₀) < tr.maxSteps} ≤
      (max n_max 1 : ℝ≥0∞)⁻¹ ^ c := by
    have hcast : ((max n_max 1 : ℕ) : ℝ≥0∞) = max (n_max : ℝ≥0∞) 1 := by
      simpa only [Nat.cast_one] using
        Monotone.map_max (fun _ _ => Nat.cast_le.2) (a := n_max) (b := 1)
    have hp := C.poly_seq_failureProb_le hlen (c := c) (by
      change (max (n_max : ℝ≥0∞) 1)⁻¹ ^ (c + c₀) ≤ _
      rw [hcast])
    exact hfail.trans (by rwa [hcast] at hp)
  have hcompl := Cslib.Probability.PMF.one_sub_le_toOuterMeasure_compl τ_final _ hfail_poly
  refine ⟨ν₀, τ_final, hhalts, heval₀, hsupp₀, hex, hsupp_fin, hfail_poly, hcompl.trans ?_⟩
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  refine tsum_le_tsum fun tr => ?_
  by_cases htr : tr ∈ τ_final.support
  · have htrans := (hsupp_fin tr htr).2.1
    by_cases hle : tr.maxSteps ≤ worstCaseTimeWhp (c + c₀) <;> simp [hle, htrans]
  · simp [Set.indicator_apply, (PMF.apply_eq_zero_iff _ _).mpr htr]

/-- **Headline per-operation with-high-probability theorem after an arbitrary-length prefix
(`reachable_step_whp`)**:
Starting from `⟨0, x⟩` via fresh initialization (`ν₀`) and executing *any* valid oblivious prefix
`ops` (regardless of `ops.length`) to `τ_pref`, preparing the next admissible operation `o` and
running `(subroutineCode c U V w n_max).code.program outReg` halts in clocked `evalRand` within
`worstCaseTimeWhp c + 1` instructions (`O_c(1)`) with probability at least
`1 - (max n_max 1 : ℝ≥0∞)⁻¹ ^ c`, decoding the exact specification result, preserving `Rep`, and
leaving caller memory outside `[base, base + whpSpace c U V w n_max)` untouched relative to both the
prefix state and the caller's initial memory `x.mem` (`Modifies`). -/
theorem reachable_step_whp {c U V w n_max base : ℕ}
    (hc : 0 < c) (hw : 0 < w) (hnU : n_max ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit : Fits w (base + whpSpace c U V w n_max))
    {x : Data rWhp} (ops : List (Dynamic.Op U)) (o : Dynamic.Op U)
    (hx : x.Bounded w) (hfr : x.regs frontierReg = base)
    (hz : ∀ a ∈ (Block.mk base (whpSpace c U V w n_max)).footprint, x.mem a = 0)
    (hv : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) ops)
    (hvo : (Dynamic.spec U V n_max).valid ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1
      o) :
    let C := impl hc hw hnU hU hV hfit
    ∃ (ν₀ : PMF (SeedWhp c U n_max × Data rWhp))
      (τ_pref : PMF (WhpSeqOutcome (SeedWhp c U n_max) (Dynamic.spec U V n_max) rWhp)),
      RandHaltsWithin w ((subroutineCode c U V w n_max).initFresh.program outReg) ⟨0, x⟩
        (C.initTime + 1) ∧
      evalRand w ((subroutineCode c U V w n_max).initFresh.program outReg) (C.initTime + 1) ⟨0, x⟩ =
        ν₀.map (fun p => RandCfg.halted (p.2.regs outReg) p.2) ∧
      (∀ p ∈ ν₀.support,
        p.2.Bounded w ∧
        p.2.regs frontierReg = base + whpSpace c U V w n_max ∧
        Rep c U V w n_max base p.1 (Dictionary.empty U) p.2 ∧
        Modifies (Block.mk base (whpSpace c U V w n_max)).footprint x.mem p.2.mem) ∧
      C.ExecWhpSteps outReg ops
        (ν₀.map fun p => WhpSeqOutcome.ofCoupled ⟨p.1, Dictionary.empty U, p.2⟩) τ_pref ∧
      (∀ tr ∈ τ_pref.support,
        tr.current.state = ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 ∧
        tr.transcript = ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).2 ∧
        Rep c U V w n_max base tr.current.seed
          ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 tr.current.data ∧
        Modifies (Block.mk base (whpSpace c U V w n_max)).footprint x.mem tr.current.data.mem) ∧
      1 - (max n_max 1 : ℝ≥0∞)⁻¹ ^ c ≤
        ((τ_pref.map fun tr => (tr.current.seed, tr.current.data)).bind fun p =>
          evalRand w ((subroutineCode c U V w n_max).code.program outReg)
            (worstCaseTimeWhp c + 1) ⟨0, C.prepare o p.2⟩).toOuterMeasure
          {cfg | ∃ (p q : SeedWhp c U n_max × Data rWhp),
            p ∈ (τ_pref.map fun tr => (tr.current.seed, tr.current.data)).support ∧
            cfg = .halted (q.2.regs outReg) q.2 ∧
            decode o q.2.regs =
              some ((Dynamic.spec U V n_max).stepFn
                ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 o).2 ∧
            Rep c U V w n_max base q.1
              ((Dynamic.spec U V n_max).stepFn
                ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 o).1 q.2 ∧
            q.2.Bounded w ∧
            Modifies (Block.mk base (whpSpace c U V w n_max)).footprint p.2.mem q.2.mem ∧
            Modifies (Block.mk base (whpSpace c U V w n_max)).footprint x.mem q.2.mem} := by
  intro C
  have hv_rel : (Dynamic.spec U V n_max).ValidOpSeq (Dictionary.empty U) ops :=
    ((Dynamic.spec U V n_max).validOpSeq_iff_validHistory (Dictionary.empty U) ops).mpr hv
  obtain ⟨ν₀, τ_pref, hhalts₀, heval₀, hsupp₀, hex, hrep_pref, hseed_pref, _, _⟩ :=
    C.seq_whp outReg ops hx hfr (fun j => Fin.elim0 j) hz hv_rel
  have htr_eq := hex.transcript_eq_ofFn (s := Dictionary.empty U) (acc := []) fun tr htr => by
    rw [PMF.mem_support_map_iff] at htr
    obtain ⟨_, _, rfl⟩ := htr
    exact ⟨rfl, rfl⟩
  have hmod_pref := execWhpSteps_modifies hex (m₀ := x.mem) fun tr htr => by
    rw [PMF.mem_support_map_iff] at htr
    obtain ⟨p, hp, rfl⟩ := htr
    exact (hsupp₀ p hp).2.2.2
  let ν_cur : PMF (SeedWhp c U n_max × Data rWhp) :=
    τ_pref.map fun tr => (tr.current.seed, tr.current.data)
  have hseed_cur : ∀ θ, (ν_cur.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ := fun θ => by
    have heq : ν_cur.map Prod.fst = (τ_pref.map WhpSeqOutcome.current).map CoupledState.seed := by
      simp only [ν_cur, PMF.map_comp]; rfl
    exact heq ▸ hseed_pref θ
  have hrep_cur : ∀ p ∈ ν_cur.support,
      C.ghostRep (C.ghostRun C.ghostInit ops) p.1
        ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 p.2 := by
    intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨tr, htr, rfl⟩ := hp
    exact (htr_eq tr htr).1 ▸ hrep_pref tr htr
  have hstep := C.step_whp_ofFn outReg o ν_cur hvo hseed_cur hrep_cur
  refine ⟨ν₀, τ_pref, hhalts₀, heval₀, hsupp₀, hex, fun tr htr => ?_,
    hstep.trans (MeasureTheory.measure_mono fun cfg hcfg => ?_)⟩
  · obtain ⟨hs_tr, htrans_tr⟩ := htr_eq tr htr
    rw [List.nil_append] at htrans_tr
    exact ⟨hs_tr, htrans_tr, ⟨C.ghostRun C.ghostInit ops, hs_tr ▸ hrep_pref tr htr⟩,
      hmod_pref tr htr⟩
  · obtain ⟨p, q, hp, rfl, hdec, hgrep, hbdd, hmod_pq⟩ := hcfg
    obtain ⟨tr, htr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
    have hp_mod : Modifies (Block.mk base (whpSpace c U V w n_max)).footprint x.mem
        tr.current.data.mem := hmod_pref tr htr
    exact ⟨(tr.current.seed, tr.current.data), q, hp, rfl, hdec, ⟨_, hgrep⟩, hbdd, hmod_pq,
      fun a ha => (hmod_pq a ha).trans (hp_mod a ha)⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
