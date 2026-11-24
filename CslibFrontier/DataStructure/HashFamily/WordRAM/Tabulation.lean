/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.ExactLog
public import CslibFrontier.Computability.WordRAM.Randomized.Structured
public import CslibFrontier.Computability.WordRAM.Word
public import CslibFrontier.Probability.PairwiseIndependentHash.Shift
public import CslibFrontier.Probability.Product
public import CslibFrontier.Probability.Uniform
public import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.WordRAM.Randomized.SymbolicExec
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.SuppCases
public import CslibFrontier.Tactic.WramOmega.Init
import CslibFrontier.Tactic.WramOmega

/-!
# Self-contained Word-RAM random tables and tabulated odd-stride generation

This file provides two self-contained Word-RAM hashing primitives over `Cslib.WordRAM.Basis.exact`,
built on a shared uniform word-slice sampler (`randFillLoop`):

1. **`RandomTable`**: `resampleCode` populates an array `Z[0 .. 2 ^ M - 1]` of `m = 2 ^ M`
   independent uniform `M`-bit words in `5 * 2 ^ M + 7` instructions and `2 ^ M` calls to
   `Code.rand`, inducing `PMF.uniformOfFintype (Fin (2 ^ M) → Fin (2 ^ M))`. `lookupCode` reads
   `Z[idx]` in `2` deterministic instructions, and `xorLookupCode` evaluates the XOR-shifted hash
   `f(u) ^^^ Z[g(u)]` in `3` deterministic instructions [Carter and Wegman][CarterWegman1979];
   [Mitzenmacher and Upfal][MitzenmacherUpfal2017].
2. **`TabulatedOddStride`**: `simpleTab` splits the low `d * b` bits of an input key `u` into `d`
   characters of `b = max 1 (Nat.log 2 (max n_max 2) / 2)` bits (`2 ^ b ≤ max 2 n_max` words per
   character table) and XORs their table entries (following the simple tabulation scheme of Zobrist
   1970 and Pătraşcu and Thorup 2012). `initCode d` samples the `d` character tables via
   `Code.rand` in `4 * Nat.log 2 (max n_max 2) + 5 * (d * 2 ^ b) + 30` instructions
   (`O(d * 2 ^ b + log n_max)`, which is `O(n_max)` for fixed `d`), and `evalCode d` evaluates
   `oddStride M (simpleTab b d M T u).val = (2 * (simpleTab b d M T u).val + 1) &&& (2 ^ M - 1)` in
   `8 * d + 21` deterministic instructions (`O(d)`). When `M > 0`, this stride `h₂(u)` is odd (at
   `M = 0` it is `0` on `Fin 1`), and for every `M` it is coprime to `2 ^ M`, so for any initial
   slot `h₁(u) : Fin (2 ^ M)` the linear probe sequence `probeSeq M h₁(u) tab i =
   (h₁(u) + i * h₂(u)) % 2 ^ M` is a bijection on `Fin (2 ^ M)` (`bijective_probeSeq`)
   [Cormen, Leiserson, Rivest, and Stein, Section 11.4][CLRS2009]. Only this full-cycle permutation
   property is proved here: no `k`-wise or 3-wise independence theorem for simple tabulation is
   claimed in this module, and `simpleTab` inspects only the low `d * b` bits of `u`.

## Main definitions

* `Cslib.DataStructure.HashFamily.WordRAM.Tabulation.randFillLoop`,
  `randFillComp`, `extractSlice`: generic loop filling a contiguous
  memory slice with independent uniform `bits`-bit words.
* `Cslib.DataStructure.HashFamily.WordRAM.Tabulation.RandomTable.resampleCode`,
  `lookupCode`, `xorLookupCode`: 1-D random table
  initialization/resampling and `O(1)` deterministic lookup.
* `Cslib.DataStructure.HashFamily.WordRAM.Tabulation.TabulatedOddStride.charBits`,
  `simpleTab`, `oddStride`, `probeSeq`, `initCode`, `evalCode`: `d`-character simple
  tabulation and odd-stride permutation generator on the Word RAM.

## Main results

* `Cslib.DataStructure.HashFamily.WordRAM.Tabulation.randFillLoop_execRand`,
  `map_extractSlice_eval_randFillComp`: exact execution
  and product uniformity of `randFillLoop`.
* `Cslib.DataStructure.HashFamily.WordRAM.Tabulation.RandomTable.resampleCode_execRand`,
  `map_extractTable_eval_resampleComp`, `lookupCode_exec`, `xorLookupCode_exec`: exact execution and
  uniformity of `RandomTable`.
* `Cslib.DataStructure.HashFamily.WordRAM.Tabulation.TabulatedOddStride.bijective_probeSeq`,
  `initCode_execRandWithin`, `evalCode_execWithin`: full-cycle
  permutation property, `O(d * 2 ^ b + log n_max)` initialization, and `O(d)` deterministic
  evaluation of `TabulatedOddStride`.

## References

* [J. L. Carter and M. N. Wegman, *Universal Classes of Hash Functions*][CarterWegman1979]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

public section

namespace Cslib.DataStructure.HashFamily.WordRAM.Tabulation

open Cslib.WordRAM Cslib.Probability
open Cslib.WordRAM.ExactLog
open scoped ENNReal

/-! ## Section 1: Uniform random word-slice filler (`randFillLoop`) -/

/-- Register `0` of `randFillLoop`: write pointer `ptr`. -/
abbrev regPtr : Fin 6 := 0

/-- Register `1` of `randFillLoop`: end pointer `arrBase + len`. -/
abbrev regEnd : Fin 6 := 1

/-- Register `2` of `randFillLoop`: random bitmask `2 ^ bits - 1`. -/
abbrev regMask : Fin 6 := 2

/-- Register `3` of `randFillLoop`: constant `1`. -/
abbrev regOne : Fin 6 := 3

/-- Register `4` of `randFillLoop`: sampled value scratch register. -/
abbrev regVal : Fin 6 := 4

/-- Register `5` of `randFillLoop`: caller-preserved register. -/
abbrev regExtra : Fin 6 := 5

/-- Body of `randFillLoop`: samples `regVal ← rand regMask`, stores `*regPtr ← regVal`, and
advances `regPtr ← regPtr + regOne`. -/
@[expose] def randFillBody : Code .exact 6 :=
  .seq (.rand regVal regMask)
  (.seq (.op (.store regPtr regVal))
        (.op (.exactBin .add regPtr regPtr regOne)))

/-- Structured Word-RAM loop that fills `[regPtr, regEnd)` with independent uniform draws in
`[0, regMask]`. -/
@[expose] def randFillLoop : Code .exact 6 :=
  .loop (.lt regPtr regEnd) randFillBody

/-- Single-iteration state update of `randFillBody` when `Code.rand` draws `v`. -/
@[expose] def randFillStepData (arrBase v : ℕ) (x : Data 6) : Data 6 :=
  ((x.set regVal v).write arrBase v).set regPtr (arrBase + 1)

/-- Explicit `ProbComp (Data 6 × ℕ)` induced by `randFillLoop` over `len` words starting at
`arrBase`. -/
@[expose] def randFillComp (bits arrBase : ℕ) : ℕ → Data 6 → ProbComp (Data 6 × ℕ)
  | 0, x => pure (x, 2)
  | len + 1, x => do
    let k ← ProbComp.unifFin (2 ^ bits - 1)
    let z ← randFillComp bits (arrBase + 1) len (randFillStepData arrBase k.val x)
    pure (z.1, 3 + z.2 + 2)

/-- Extract a contiguous slice of `len` words at `arrBase` as a tuple `Fin len → Fin (2 ^ bits)`. -/
@[expose] def extractSlice (arrBase bits len : ℕ) (mem : ℕ → ℕ) : Fin len → Fin (2 ^ bits) :=
  fun i => wordOfNat bits (mem (arrBase + i.val))

/-- One iteration of `randFillBody` executes in `3` instructions and `1` `rand` call. -/
theorem randFillBody_execRand {w bits arrBase : ℕ} {x : Data 6}
    (hptr : x.regs regPtr = arrBase) (hmask : x.regs regMask = 2 ^ bits - 1)
    (hone : x.regs regOne = 1) (hfit_ptr : Fits w (arrBase + 1))
    (hfit_mask : Fits w (2 ^ bits - 1)) :
    ExecRand w randFillBody x (do
      let k ← ProbComp.unifFin (2 ^ bits - 1)
      pure (randFillStepData arrBase k.val x, 3)) := by
  unfold randFillBody randFillStepData
  wram_rand_exec [hptr, hmask, hone]

/-- **Exact `ExecRand` semantics of `randFillLoop`** over `len` words starting at `arrBase`. -/
theorem randFillLoop_execRand {w bits arrBase : ℕ} (len : ℕ) {x : Data 6}
    (hptr : x.regs regPtr = arrBase) (hend : x.regs regEnd = arrBase + len)
    (hmask : x.regs regMask = 2 ^ bits - 1) (hone : x.regs regOne = 1)
    (hfit_end : Fits w (arrBase + len)) (hfit_mask : Fits w (2 ^ bits - 1)) :
    ExecRand w randFillLoop x (randFillComp bits arrBase len x) := by
  induction len generalizing arrBase x with
  | zero => exact ExecRand.loop_exit (by simp [Cond.Holds, hptr, hend])
  | succ len ih =>
    have hc : (Cond.lt regPtr regEnd).Holds x := by simp [Cond.Holds, hptr, hend]
    have hb := randFillBody_execRand hptr hmask hone (by fits) hfit_mask
    have hiter := ExecRand.loop_iter hc hb fun z hz => by
      supp_cases hz with ⟨k, rfl⟩
      exact ih (arrBase := arrBase + 1)
        (by wram_simp [randFillStepData])
        (by wram_simp [randFillStepData, hend]; omega)
        (by wram_simp [randFillStepData, hmask])
        (by wram_simp [randFillStepData, hone])
        (by rwa [show arrBase + 1 + len = arrBase + (len + 1) by omega])
    simpa only [randFillLoop, randFillComp, bind_assoc, pure_bind] using hiter

/-- `randFillComp bits arrBase len x` makes at most `len` `rand` calls. -/
theorem isQueryBounded_randFillComp (bits arrBase len : ℕ) (x : Data 6) :
    (randFillComp bits arrBase len x).IsQueryBounded len := by
  induction len generalizing arrBase x with
  | zero => exact .pure _ 0
  | succ len ih =>
    dsimp only [randFillComp]
    rw [Nat.add_comm len 1]
    exact (ProbComp.isQueryBounded_unifFin _).bind fun k => by
      simpa only [Nat.add_zero] using (ih _ _).bind fun _ => .pure _ 0

/-- Pathwise postcondition of `randFillComp`: takes `5 * len + 2` instructions, preserves registers
`regEnd`, `regMask`, `regOne`, `regExtra`, fills `[arrBase, arrBase + len)` with `< 2 ^ bits`
words, and preserves all memory outside `[arrBase, arrBase + len)`. -/
theorem mem_support_randFillComp {bits arrBase len : ℕ} {x : Data 6} {z : Data 6 × ℕ}
    (hz : z ∈ (randFillComp bits arrBase len x).support) :
    z.2 = 5 * len + 2 ∧
    z.1.regs regPtr = (if len = 0 then x.regs regPtr else arrBase + len) ∧
    z.1.regs regEnd = x.regs regEnd ∧
    z.1.regs regMask = x.regs regMask ∧
    z.1.regs regOne = x.regs regOne ∧
    z.1.regs regExtra = x.regs regExtra ∧
    (∀ i < len, z.1.mem (arrBase + i) < 2 ^ bits) ∧
    (∀ a, (a < arrBase ∨ arrBase + len ≤ a) → z.1.mem a = x.mem a) := by
  induction len generalizing arrBase x z with
  | zero =>
    dsimp only [randFillComp] at hz
    supp_cases hz
    exact ⟨rfl, by simp, rfl, rfl, rfl, rfl, fun _ hi => by omega, fun _ _ => rfl⟩
  | succ len ih =>
    dsimp only [randFillComp] at hz
    supp_cases hz with ⟨k, z', hz', rfl⟩
    obtain ⟨hsteps, hptr, hend, hmask, hone, hextra, hlt, hframe⟩ := ih hz'
    wram_simp [randFillStepData] at hend hmask hone hextra
    refine ⟨by omega, ?_, hend, hmask, hone, hextra, ?_, ?_⟩
    · rcases eq_or_ne len 0 with rfl | hlen
      · simp [hptr, randFillStepData]
      · simp only [Nat.succ_ne_zero, ↓reduceIte, hptr, ite_eq_right hlen]; omega
    · intro i hi
      rcases eq_or_ne i 0 with rfl | hi0
      · dsimp only
        rw [Nat.add_zero, hframe arrBase (Or.inl (by omega))]
        wram_simp [randFillStepData]
        exact Nat.lt_of_lt_of_le k.isLt (Nat.sub_add_cancel Nat.one_le_two_pow).le
      · simpa only [show arrBase + 1 + (i - 1) = arrBase + i by omega] using
          hlt (i - 1) (by omega)
    · intro a ha
      dsimp only
      rw [hframe a (by omega)]
      wram_simp [randFillStepData]

/-- Extracting `len + 1` words at `arrBase` after one `randFillStepData` step and the remaining
`len` steps equals `Fin.cons` of the first draw and the remaining `len`-word slice. -/
private theorem extractSlice_succ_of_support {bits arrBase len : ℕ} {x : Data 6}
    (k : Fin (2 ^ bits - 1 + 1)) {z : Data 6 × ℕ}
    (hz : z ∈ (randFillComp bits (arrBase + 1) len (randFillStepData arrBase k.val x)).support) :
    extractSlice arrBase bits (len + 1) z.1.mem =
      Fin.cons (finCongr (Nat.sub_add_cancel Nat.one_le_two_pow) k)
        (extractSlice (arrBase + 1) bits len z.1.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hframe⟩ := mem_support_randFillComp hz
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [extractSlice, randFillStepData, hframe arrBase (Or.inl (by omega))]
  · simp only [extractSlice, Fin.cons_succ, Fin.val_succ,
      show arrBase + 1 + i.val = arrBase + (i.val + 1) by omega]

/-- **Uniformity of `randFillComp`**: the slice `extractSlice arrBase bits len z.1.mem` produced by
`randFillComp bits arrBase len x` has the exact product uniform distribution
`PMF.uniformOfFintype (Fin len → Fin (2 ^ bits))`. -/
theorem map_extractSlice_eval_randFillComp (bits arrBase len : ℕ) (x : Data 6) :
    ((randFillComp bits arrBase len x).eval).map (fun z => extractSlice arrBase bits len z.1.mem) =
      PMF.uniformOfFintype (Fin len → Fin (2 ^ bits)) := by
  induction len generalizing arrBase x with
  | zero =>
    ext f
    simp [randFillComp, ProbComp.eval_pure, PMF.map, PMF.pure_apply,
      Subsingleton.elim f (extractSlice arrBase bits 0 x.mem), PMF.uniformOfFintype_apply]
  | succ len ih =>
    let e := finCongr (Nat.sub_add_cancel (Nat.one_le_two_pow (n := bits)))
    dsimp only [randFillComp]
    rw [ProbComp.eval_bind, ProbComp.eval_unifFin, PMF.map_bind,
      ← PMF.pi_uniformOfFintype, PMF.pi_fin_succ, PMF.pi_uniformOfFintype,
      ← PMF.uniformOfFintype_map_equiv e, PMF.bind_map]
    congr 1 with k : 1
    dsimp only [Function.comp_apply]
    rw [bind_pure_comp, ProbComp.eval_map, PMF.map_comp,
      ← ih (arrBase + 1) (randFillStepData arrBase k.val x), PMF.map_comp]
    exact PMF.map_congr_on_support _ _ _ fun z hz =>
      extractSlice_succ_of_support (z := z) k (ProbComp.support_eval _ ▸ hz)

/-! ## Section 2: `RandomTable` — 1-D random table for Cuckoo Hashing -/

namespace RandomTable

/-- Footprint size of `RandomTable M`: `2 ^ M` words at `[base, base + 2 ^ M)`. -/
@[expose] def space (M : ℕ) : ℕ := 2 ^ M

/-- Register `0`: holds the base memory address `base` of the table. -/
abbrev regBase : Fin 6 := 0

/-- Register `1`: holds `M` during `resampleCode`, or index `idx < 2 ^ M` during `lookupCode`. -/
abbrev regM : Fin 6 := 1

/-- Alias for register `1` when used as the lookup index `idx < 2 ^ M`. -/
abbrev regIdx : Fin 6 := 1

/-- Register `2`: receives `Z[idx]` in `lookupCode` or `fx ^^^ Z[idx]` in `xorLookupCode`. -/
abbrev regOut : Fin 6 := 2

/-- Register `3`: scratch register 1. -/
abbrev regT1 : Fin 6 := 3

/-- Register `4`: scratch register 2. -/
abbrev regT2 : Fin 6 := 4

/-- Register `5`: scratch register 3. -/
abbrev regT3 : Fin 6 := 5

/-- Memory representation invariant: `[base, base + 2 ^ M)` holds the entries of
`Z : Fin (2 ^ M) → Fin (2 ^ M)`. -/
def Rep (base M : ℕ) (Z : Fin (2 ^ M) → Fin (2 ^ M)) (mem : ℕ → ℕ) : Prop :=
  ∀ i : Fin (2 ^ M), mem (base + i.val) = (Z i).val

/-- Extract the random table `Z : Fin (2 ^ M) → Fin (2 ^ M)` from memory at `base`. -/
@[expose] def extractTable (base M : ℕ) (mem : ℕ → ℕ) : Fin (2 ^ M) → Fin (2 ^ M) :=
  extractSlice base M (2 ^ M) mem

/-- If every word in `[base, base + 2 ^ M)` is `< 2 ^ M`, then
`Rep base M (extractTable base M mem) mem` holds. -/
theorem rep_extractTable {base M : ℕ} {mem : ℕ → ℕ}
    (h : ∀ i < 2 ^ M, mem (base + i) < 2 ^ M) :
    Rep base M (extractTable base M mem) mem := by
  intro i
  simp [extractTable, extractSlice, h i.val i.isLt]

/-- Injective register permutation mapping `randFillLoop`'s registers into `RandomTable` so that
`regExtra` maps to `regBase` (preserving `regBase`). -/
@[expose] def fillMap : Fin 6 → Fin 6
  | 0 => regT1
  | 1 => regT2
  | 2 => regT3
  | 3 => regOut
  | 4 => regM
  | 5 => regBase

theorem injective_fillMap : Function.Injective fillMap := by
  decide

/-- Deterministic setup before `randFillLoop` in `resampleCode`: computes `2 ^ M`, `2 ^ M - 1`,
`base + 2 ^ M`, and initializes the loop registers. -/
@[expose] def setupCode : Code .exact 6 :=
  .seq (.op (.const regOut 1))
  (.seq (.op (.exactBin .shiftLeft regT2 regOut regM))
  (.seq (.op (.exactBin .sub regT3 regT2 regOut))
  (.seq (.op (.copy regT1 regBase))
        (.op (.exactBin .add regT2 regBase regT2)))))

/-- Closed-form machine data after `setupCode`. -/
@[expose] def setupData (base M : ℕ) (x : Data 6) : Data 6 :=
  ((((x.set regOut 1).set regT2 (2 ^ M)).set regT3 (2 ^ M - 1)).set regT1 base).set
    regT2 (base + 2 ^ M)

/-- Structured Word-RAM program that initializes or resamples `Z[0 .. 2 ^ M - 1]` at `base` using
`2 ^ M` calls to `Code.rand` on `2 ^ M - 1`. -/
@[expose] def resampleCode : Code .exact 6 :=
  .seq setupCode (randFillLoop.rename fillMap)

/-- Alias for `resampleCode` when used for initial table construction. -/
abbrev initCode : Code .exact 6 := resampleCode

/-- Explicit `ProbComp (Data 6 × ℕ)` induced by `resampleCode` at `(base, M)` from `x`. -/
@[expose] noncomputable def resampleComp (base M : ℕ) (x : Data 6) : ProbComp (Data 6 × ℕ) :=
  let s := setupData base M x
  (fun z => (z.1.extend fillMap s, 5 + z.2)) <$>
    randFillComp M base (2 ^ M) (s.comap fillMap)

/-- `setupCode` executes deterministically in `5` instructions when `Fits w (base + 2 ^ M)` and
`Fits w (2 ^ M)`. -/
theorem setupCode_exec {w base M : ℕ} {x : Data 6}
    (hbase : x.regs regBase = base) (hM : x.regs regM = M)
    (hfit_end : Fits w (base + 2 ^ M)) (hfit_pow : Fits w (2 ^ M)) :
    Exec w setupCode x (setupData base M x) 5 := by
  have hpos : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  unfold setupCode setupData
  wram_exec [hbase, hM, Nat.shiftLeft_eq, Nat.one_mul]

/-- **Exact `ExecRand` execution of `RandomTable.resampleCode`**: runs in `5 * 2 ^ M + 7`
instructions and `2 ^ M` `rand` calls. -/
theorem resampleCode_execRand {w base M : ℕ} {x : Data 6}
    (hbase : x.regs regBase = base) (hM : x.regs regM = M)
    (hfit_end : Fits w (base + 2 ^ M)) (hfit_pow : Fits w (2 ^ M)) :
    ExecRand w resampleCode x (resampleComp base M x) := by
  unfold resampleCode
  refine WP.Rand.execRand ?_
  wram_rand_call (setupCode_exec hbase hM hfit_end hfit_pow)
  wram_rand_call (randFillLoop_execRand (bits := M) (arrBase := base) (2 ^ M)
    (by wram_simp [setupData, fillMap]) (by wram_simp [setupData, fillMap])
    (by wram_simp [setupData, fillMap]) (by wram_simp [setupData, fillMap])
    hfit_end (by fits)) renamed injective_fillMap
  simp only [resampleComp, Functor.map_map]

/-- **Uniformity of `RandomTable.resampleComp`**: the extracted table `extractTable base M z.1.mem`
is distributed according to `PMF.uniformOfFintype (Fin (2 ^ M) → Fin (2 ^ M))`. -/
theorem map_extractTable_eval_resampleComp (base M : ℕ) (x : Data 6) :
    ((resampleComp base M x).eval).map (fun z => extractTable base M z.1.mem) =
      PMF.uniformOfFintype (Fin (2 ^ M) → Fin (2 ^ M)) := by
  dsimp only [resampleComp, extractTable]
  rw [ProbComp.eval_map, PMF.map_comp]
  exact map_extractSlice_eval_randFillComp M base (2 ^ M) ((setupData base M x).comap fillMap)

/-- Hoare-style `ExecRandWithin` specification for `RandomTable.resampleCode`: runs in
`5 * 2 ^ M + 7` steps and `2 ^ M` `rand` calls, establishing `Rep`, preserving `regBase`, and
modifying only `[base, base + 2 ^ M)`. -/
theorem resampleCode_execRandWithin {w base M : ℕ} {x : Data 6}
    (hbase : x.regs regBase = base) (hM : x.regs regM = M)
    (hfit_end : Fits w (base + 2 ^ M)) (hfit_pow : Fits w (2 ^ M)) :
    ExecRandWithin w resampleCode x
      (fun y => Rep base M (extractTable base M y.mem) y.mem ∧
        y.regs regBase = base ∧
        (∀ a, (a < base ∨ base + 2 ^ M ≤ a) → y.mem a = x.mem a))
      (5 * 2 ^ M + 7) (2 ^ M) := by
  refine ⟨resampleComp base M x, resampleCode_execRand hbase hM hfit_end hfit_pow,
    (OracleComp.isCostBounded_map_iff _ _ _).mpr (isQueryBounded_randFillComp ..), fun z hz => ?_⟩
  dsimp only [resampleComp] at hz
  supp_cases hz with ⟨z₀, hz₀, rfl⟩
  obtain ⟨hsteps, -, -, -, -, hextra, hlt, hframe⟩ := mem_support_randFillComp hz₀
  refine ⟨⟨rep_extractTable hlt, ?_, hframe⟩, by omega⟩
  wram_simp [hextra, setupData, fillMap, hbase]

/-- Structured Word-RAM program that reads `Z[regIdx]` at `regBase + regIdx` into `regOut` in `2`
deterministic instructions. -/
@[expose] def lookupCode : Code .exact 6 :=
  .seq (.op (.exactBin .add regT1 regBase regIdx))
        (.op (.load regOut regT1))

/-- Final machine data after `lookupCode`. -/
@[expose] def lookupData (x : Data 6) : Data 6 :=
  let addr := x.regs regBase + x.regs regIdx
  (x.set regT1 addr).set regOut (x.mem addr)

/-- `lookupCode` executes in `2` deterministic instructions, preserving memory and `regBase` and
writing `(Z idx).val` into `regOut`. -/
theorem lookupCode_exec {w base M : ℕ} {Z : Fin (2 ^ M) → Fin (2 ^ M)} {x : Data 6}
    (hrep : Rep base M Z x.mem) (idx : Fin (2 ^ M))
    (hbase : x.regs regBase = base) (hidx : x.regs regIdx = idx.val)
    (hfit_end : Fits w (base + 2 ^ M)) :
    Exec w lookupCode x (lookupData x) 2 ∧
    (lookupData x).regs regOut = (Z idx).val ∧
    (lookupData x).regs regBase = base ∧
    (lookupData x).mem = x.mem := by
  refine ⟨?_, by simp [lookupData, hbase, hidx, hrep idx],
    by simp [lookupData, hbase, regBase, regT1, regOut], rfl⟩
  unfold lookupCode lookupData
  wram_exec [hbase, hidx]
  simp only [hbase, hidx]

/-- Structured Word-RAM program that computes `regOut ← regOut ^^^ Z[regIdx]` in `3` deterministic
instructions (computing `f(u) ^^^ Z[g(u)]` when `regOut` holds `f(u)` and `regIdx` holds
`g(u)`). -/
@[expose] def xorLookupCode : Code .exact 6 :=
  .seq (.op (.exactBin .add regT1 regBase regIdx))
  (.seq (.op (.load regT2 regT1))
        (.op (.exactBin .xor regOut regOut regT2)))

/-- Final machine data after `xorLookupCode`. -/
@[expose] def xorLookupData (x : Data 6) : Data 6 :=
  let addr := x.regs regBase + x.regs regIdx
  let zval := x.mem addr
  ((x.set regT1 addr).set regT2 zval).set regOut (x.regs regOut ^^^ zval)

/-- `xorLookupCode` executes in `3` deterministic instructions, preserving memory and `regBase` and
writing `fx.val ^^^ (Z idx).val < 2 ^ M` into `regOut`. -/
theorem xorLookupCode_exec {w base M : ℕ} {Z : Fin (2 ^ M) → Fin (2 ^ M)} {x : Data 6}
    (hrep : Rep base M Z x.mem) (idx fx : Fin (2 ^ M))
    (hbase : x.regs regBase = base) (hidx : x.regs regIdx = idx.val)
    (hfx : x.regs regOut = fx.val)
    (hfit_end : Fits w (base + 2 ^ M)) (hfit_pow : Fits w (2 ^ M)) :
    Exec w xorLookupCode x (xorLookupData x) 3 ∧
    (xorLookupData x).regs regOut = fx.val ^^^ (Z idx).val ∧
    (xorLookupData x).regs regOut < 2 ^ M ∧
    (xorLookupData x).regs regBase = base ∧
    (xorLookupData x).mem = x.mem := by
  have hxor_lt : fx.val ^^^ (Z idx).val < 2 ^ M := Nat.xor_lt_two_pow fx.isLt (Z idx).isLt
  refine ⟨?_, by simp [xorLookupData, hbase, hidx, hfx, hrep idx],
    by simpa [xorLookupData, hbase, hidx, hfx, hrep idx] using hxor_lt,
    by simp [xorLookupData, hbase, regBase, regT1, regT2, regOut], rfl⟩
  unfold xorLookupCode xorLookupData
  wram_exec [hbase, hidx, hfx, hrep idx]
  simp only [hbase, hidx, hfx, hrep idx]

end RandomTable

/-! ## Section 3: `TabulatedOddStride` -/

namespace TabulatedOddStride

/-- Character bit-width `b = max 1 (⌊log₂ (max n_max 2)⌋ / 2)` for `d`-character simple tabulation,
ensuring `1 ≤ b` and `2 ^ b ≤ max 2 n_max` (`2 ^ (2 * b) ≤ max 4 n_max`). -/
@[expose, wram_arith] def charBits (n_max : ℕ) : ℕ :=
  max 1 (Nat.log 2 (max n_max 2) / 2)

/-- `charBits n_max` is always at least `1`. -/
theorem one_le_charBits (n_max : ℕ) : 1 ≤ charBits n_max :=
  Nat.le_max_left 1 _

/-- `charBits n_max` is always positive. -/
theorem charBits_pos (n_max : ℕ) : 0 < charBits n_max :=
  one_le_charBits n_max

/-- The character alphabet size `2 ^ charBits n_max` is at most `max 2 n_max`. -/
theorem two_pow_charBits_le (n_max : ℕ) : 2 ^ charBits n_max ≤ max 2 n_max := by
  have hlog_ge : 1 ≤ Nat.log 2 (max n_max 2) :=
    Nat.le_log_of_pow_le (by decide) (by omega)
  have hle_log : charBits n_max ≤ Nat.log 2 (max n_max 2) := by wram_omega
  calc
    2 ^ charBits n_max ≤ 2 ^ Nat.log 2 (max n_max 2) :=
      Nat.pow_le_pow_right (by decide) hle_log
    _ ≤ max n_max 2 := Nat.pow_log_le_self 2 (by omega)
    _ = max 2 n_max := Nat.max_comm n_max 2

/-- Odd stride `(2 * tab + 1) &&& (2 ^ M - 1) = (2 * tab + 1) % 2 ^ M` in `Fin (2 ^ M)`. -/
@[expose] def oddStride (M tab : ℕ) : Fin (2 ^ M) :=
  ⟨(2 * tab + 1) &&& (2 ^ M - 1), by
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (Nat.two_pow_pos M)⟩

@[simp]
theorem val_oddStride (M tab : ℕ) : (oddStride M tab).val = (2 * tab + 1) % 2 ^ M :=
  Nat.and_two_pow_sub_one_eq_mod (2 * tab + 1) M

/-- When `0 < M`, `(oddStride M tab).val` is odd (`% 2 = 1`). -/
theorem odd_oddStride {M : ℕ} (hM : 0 < M) (tab : ℕ) : (oddStride M tab).val % 2 = 1 := by
  rw [val_oddStride, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 hM.ne')]
  omega

/-- `(oddStride M tab).val` is always coprime to `2 ^ M`. -/
theorem coprime_oddStride_two_pow (M tab : ℕ) : Nat.Coprime (oddStride M tab).val (2 ^ M) := by
  rw [val_oddStride, Nat.Coprime, ← Nat.gcd_rec]
  exact (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))).pow_left M

/-- Double-hashing probe sequence `probeSeq M h₁ tab i = (h₁ + i * oddStride M tab) mod 2 ^ M`
on `Fin (2 ^ M)`. -/
@[expose] def probeSeq (M h₁ tab : ℕ) (i : Fin (2 ^ M)) : Fin (2 ^ M) :=
  ⟨(h₁ + i.val * (oddStride M tab).val) % 2 ^ M, Nat.mod_lt _ (Nat.two_pow_pos M)⟩

/-- Because `oddStride M tab` is coprime to `2 ^ M`, `probeSeq M h₁ tab` is a full-cycle
bijection (permutation) of `Fin (2 ^ M)` for every `M`, initial probe `h₁`, and raw table sum
`tab`. -/
theorem bijective_probeSeq (M h₁ tab : ℕ) : Function.Bijective (probeSeq M h₁ tab) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun i j heq => ?_, rfl⟩
  wlog hij : j.val ≤ i.val
  · exact (this M h₁ tab j i heq.symm (by omega)).symm
  have hmod : j.val * (oddStride M tab).val ≡ i.val * (oddStride M tab).val [MOD 2 ^ M] :=
    Nat.ModEq.add_left_cancel' h₁ (by simpa [probeSeq, Fin.ext_iff, Nat.ModEq] using heq.symm)
  have hdvd_mul : 2 ^ M ∣ (i.val - j.val) * (oddStride M tab).val := by
    rw [Nat.sub_mul]
    exact (Nat.modEq_iff_dvd' (Nat.mul_le_mul_right _ hij)).mp hmod
  have hdvd : 2 ^ M ∣ i.val - j.val :=
    (coprime_oddStride_two_pow M tab).symm.dvd_of_dvd_mul_right hdvd_mul
  have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
  exact Fin.ext (by omega)

/-- Tail-recursive `d`-character simple tabulation accumulator from character offset `j` across
`rem` remaining characters: XORs `T[(j + k) * 2 ^ b + ((u >>> (k * b)) &&& (2 ^ b - 1))]` into
`acc`. -/
@[expose] def simpleTabAux (b d M : ℕ) (T : Fin (d * 2 ^ b) → Fin (2 ^ M)) :
    ℕ → ℕ → ℕ → Fin (2 ^ M) → Fin (2 ^ M)
  | 0, _, _, acc => acc
  | rem + 1, j, u, acc =>
    let ch := u &&& (2 ^ b - 1)
    let idx := j * 2 ^ b + ch
    let entry : Fin (2 ^ M) :=
      if h : idx < d * 2 ^ b then T ⟨idx, h⟩ else ⟨0, Nat.two_pow_pos M⟩
    simpleTabAux b d M T rem (j + 1) (u >>> b)
      ⟨acc.val ^^^ entry.val, Nat.xor_lt_two_pow acc.isLt entry.isLt⟩

/-- `d`-character simple tabulation hash `simpleTab b d M T u : Fin (2 ^ M)`, XORing the table
entries for the first `d` base-`2 ^ b` characters of `u`. -/
@[expose] def simpleTab (b d M : ℕ) (T : Fin (d * 2 ^ b) → Fin (2 ^ M)) (u : ℕ) : Fin (2 ^ M) :=
  simpleTabAux b d M T d 0 u ⟨0, Nat.two_pow_pos M⟩

/-- Tabulated odd stride `tabulatedOddStride b d M T u : Fin (2 ^ M)` obtained by mapping the
`d`-character simple tabulation hash through `oddStride M`. -/
@[expose] def tabulatedOddStride (b d M : ℕ) (T : Fin (d * 2 ^ b) → Fin (2 ^ M)) (u : ℕ) :
    Fin (2 ^ M) :=
  oddStride M (simpleTab b d M T u).val

/-- Memory footprint `4 + d * 2 ^ b` words for a `d`-character simple tabulation table with
character bit-width `b` (4 header words `(b, 2 ^ b, 2 ^ b - 1, 2 ^ M - 1)` followed by
`d * 2 ^ b` random `< 2 ^ M` words). -/
@[expose, wram_arith] def spaceFromB (b d : ℕ) : ℕ := 4 + d * 2 ^ b

/-- Memory footprint `4 + d * 2 ^ (charBits n_max)` words at capacity parameter `n_max`. -/
@[expose] def space (n_max d : ℕ) : ℕ := spaceFromB (charBits n_max) d

/-- Memory representation predicate for `TabulatedOddStride` at `[base, base + 4 + d * 2 ^ b)`:
header words `b`, `2 ^ b`, `2 ^ b - 1`, `2 ^ M - 1` at `base + 0 .. base + 3`, and table entries
`(T i).val` at `base + 4 + i.val` for `i : Fin (d * 2 ^ b)`. -/
@[expose] def Rep (base b d M : ℕ) (T : Fin (d * 2 ^ b) → Fin (2 ^ M)) (mem : ℕ → ℕ) : Prop :=
  mem base = b ∧
  mem (base + 1) = 2 ^ b ∧
  mem (base + 2) = 2 ^ b - 1 ∧
  mem (base + 3) = 2 ^ M - 1 ∧
  ∀ i : Fin (d * 2 ^ b), mem (base + 4 + i.val) = (T i).val

/-- Extract the flat character table `Fin (d * 2 ^ b) → Fin (2 ^ M)` from `[base + 4, ...)`. -/
@[expose] def extractTable (base b d M : ℕ) (mem : ℕ → ℕ) : Fin (d * 2 ^ b) → Fin (2 ^ M) :=
  extractSlice (base + 4) M (d * 2 ^ b) mem

/-- Register `0` of `TabulatedOddStride`: base memory address `base`. -/
abbrev regBase : Fin 9 := 0

/-- Register `1` of `TabulatedOddStride`: holds `n_max` in `initCode` or input key `u` in
`evalCode`. -/
abbrev regKey : Fin 9 := 1

/-- Register `2` of `TabulatedOddStride`: holds `M` in `initCode` or receives the odd stride in
`evalCode`. -/
abbrev regOut : Fin 9 := 2

/-- Register `3` of `TabulatedOddStride`: table pointer scratch register. -/
abbrev regPtr : Fin 9 := 3

/-- Register `4` of `TabulatedOddStride`: end pointer / mask scratch register. -/
abbrev regEnd : Fin 9 := 4

/-- Register `5` of `TabulatedOddStride`: character bit-width `b` / loop bound register. -/
abbrev regB : Fin 9 := 5

/-- Register `6` of `TabulatedOddStride`: character alphabet size `2 ^ b` / sampled value
register. -/
abbrev regPowB : Fin 9 := 6

/-- Register `7` of `TabulatedOddStride`: character mask `2 ^ b - 1` register. -/
abbrev regMaskB : Fin 9 := 7

/-- Register `8` of `TabulatedOddStride`: general scratch register. -/
abbrev regTmp : Fin 9 := 8

/-- Register injection `Fin 3 → Fin 9` mapping `log2Loop`'s `(rem, acc, one)` to
`(regPtr, regB, regTmp)`. -/
@[expose] def logMap9 : Fin 3 → Fin 9
  | ⟨0, _⟩ => regPtr
  | ⟨1, _⟩ => regB
  | ⟨2, _⟩ => regTmp

theorem injective_logMap9 : Function.Injective logMap9 := by
  decide

/-- Register injection `Fin 6 → Fin 9` mapping `randFillLoop`'s `(ptr, end, mask, one, val, extra)`
to `(regPtr, regB, regEnd, regTmp, regPowB, regBase)`. -/
@[expose] def fillMap9 : Fin 6 → Fin 9
  | ⟨0, _⟩ => regPtr
  | ⟨1, _⟩ => regB
  | ⟨2, _⟩ => regEnd
  | ⟨3, _⟩ => regTmp
  | ⟨4, _⟩ => regPowB
  | ⟨5, _⟩ => regBase

theorem injective_fillMap9 : Function.Injective fillMap9 := by
  decide

/-- Structured Word-RAM program that computes `regB ← charBits n_max`
(`= max 1 (⌊log₂ (max n_max 2)⌋ / 2)`) at runtime from `n_max` in `regKey`, using `regPtr`,
`regB`, `regTmp` as scratch registers and preserving `regBase`, `regOut`, and all memory. -/
@[expose] def charBitsCode : Code .exact 9 :=
  .seq (.op (.const regTmp 2))
  (.seq (maxCode regPtr regKey regTmp)
  (.seq (.op (.const regB 0))
  (.seq (.op (.const regTmp 1))
  (.seq (log2Loop.rename logMap9)
  (.seq (.op (.exactBin .shiftRight regB regB regTmp))
        (maxCode regB regB regTmp))))))

/-- State after `charBitsCode` starting from `n_max` in `regKey`. -/
noncomputable def charBitsData (n_max : ℕ) (x : Data 9) : Data 9 :=
  let dPre := (((x.set regTmp 2).set regPtr (max n_max 2)).set regB 0).set regTmp 1
  let dLog := (log2LoopData (max n_max 2) 0 (dPre.comap logMap9)).extend logMap9 dPre
  (dLog.set regB (Nat.log 2 (max n_max 2) / 2)).set regB (charBits n_max)

/-- `charBitsCode` executes deterministically in `4 * Nat.log 2 (max n_max 2) + 12` instructions,
setting `regB = charBits n_max` while preserving `regBase`, `regOut`, and all memory. -/
theorem charBitsCode_exec {w n_max : ℕ} {x : Data 9}
    (hn : x.regs regKey = n_max) (hfit_n : Fits w (max n_max 2)) :
    Exec w charBitsCode x (charBitsData n_max x) (4 * Nat.log 2 (max n_max 2) + 12) ∧
    (charBitsData n_max x).regs regB = charBits n_max ∧
    (charBitsData n_max x).regs regBase = x.regs regBase ∧
    (charBitsData n_max x).regs regOut = x.regs regOut ∧
    (charBitsData n_max x).mem = x.mem := by
  refine ⟨?_, by wram_simp [charBitsData], by wram_simp [charBitsData],
    by wram_simp [charBitsData], rfl⟩
  have hfit_log : Fits w (Nat.log 2 (max n_max 2)) :=
    hfit_n.of_le (Nat.log_le_self 2 (max n_max 2))
  unfold charBitsCode charBitsData
  wram_exec
  refine WP.Exact.of_exec (maxCode_exec regPtr regKey regTmp _) ?_
  wram_exec
  refine WP.Exact.of_exec ((log2Loop_exec (w := w) (max n_max 2) (acc := 0)
    (by wram_simp [logMap9, hn]) (by wram_simp [logMap9]) (by wram_simp [logMap9])
    hfit_n (by simpa only [Nat.zero_add] using hfit_log)).rename injective_logMap9) ?_
  wram_exec [log2LoopData, logMap9, Nat.shiftRight_eq_div_pow, Nat.zero_add]
  refine WP.Exact.of_exec (maxCode_exec regB regB regTmp _) ?_
  exact ⟨by omega, by wram_simp [hn, charBits, log2LoopData, logMap9, Nat.max_comm]⟩

/-- Deterministic 16-instruction setup prefix of `initFromBCode d`: writes the 4 header words
`(b, 2 ^ b, 2 ^ b - 1, 2 ^ M - 1)` to `base + 0 .. base + 3` and sets registers for
`randFillLoop.rename fillMap9` on `[base + 4, base + 4 + d * 2 ^ b)`. -/
@[expose] def setupFromBCode (d : ℕ) : Code .exact 9 :=
  .seq (.op (.store regBase regB))
  (.seq (.op (.const regTmp 1))
  (.seq (.op (.exactBin .shiftLeft regPowB regTmp regB))
  (.seq (.op (.exactBin .add regPtr regBase regTmp))
  (.seq (.op (.store regPtr regPowB))
  (.seq (.op (.exactBin .sub regMaskB regPowB regTmp))
  (.seq (.op (.exactBin .add regPtr regPtr regTmp))
  (.seq (.op (.store regPtr regMaskB))
  (.seq (.op (.exactBin .shiftLeft regEnd regTmp regOut))
  (.seq (.op (.exactBin .sub regEnd regEnd regTmp))
  (.seq (.op (.exactBin .add regPtr regPtr regTmp))
  (.seq (.op (.store regPtr regEnd))
  (.seq (.op (.exactBin .add regPtr regPtr regTmp))
  (.seq (.op (.const regB d))
  (.seq (.op (.exactBin .mul regB regB regPowB))
        (.op (.exactBin .add regB regPtr regB))))))))))))))))

/-- State after `setupFromBCode d`. -/
@[expose] def setupFromBData (base b d M : ℕ) (x : Data 9) : Data 9 :=
  let m0 := (((x.write base b).write (base + 1) (2 ^ b)).write
    (base + 2) (2 ^ b - 1)).write (base + 3) (2 ^ M - 1)
  ((((((m0.set regTmp 1).set regPowB (2 ^ b)).set regPtr (base + 1)).set
    regMaskB (2 ^ b - 1)).set regPtr (base + 2)).set regEnd (2 ^ M)).set
    regEnd (2 ^ M - 1) |>.set regPtr (base + 3) |>.set regPtr (base + 4) |>.set
    regB d |>.set regB (d * 2 ^ b) |>.set regB (base + 4 + d * 2 ^ b)

/-- `setupFromBCode d` executes in `16` deterministic steps. -/
theorem setupFromBCode_exec {w base b d M : ℕ} {x : Data 9}
    (hbase : x.regs regBase = base) (hb : x.regs regB = b) (hM : x.regs regOut = M)
    (hfit_space : Fits w (base + spaceFromB b d))
    (hfit_powB : Fits w (2 ^ b)) (hfit_powM : Fits w (2 ^ M)) (hfit_d : Fits w d) :
    Exec w (setupFromBCode d) x (setupFromBData base b d M x) 16 := by
  wram_exec (disch := first | fits | omega | wram_omega)
    [setupFromBCode, hbase, hb, hM, Nat.shiftLeft_eq, Nat.one_mul]
  ext i : 2
  · fin_cases i <;> rfl
  · rfl

/-- Structured Word-RAM program that initializes a `d`-character simple tabulation table from
`(base, M, b)` in `(regBase, regOut, regB)`. -/
@[expose] def initFromBCode (d : ℕ) : Code .exact 9 :=
  .seq (setupFromBCode d) (randFillLoop.rename fillMap9)

/-- Explicit `ProbComp (Data 9 × ℕ)` produced by `initFromBCode d`. -/
@[expose] noncomputable def initFromBComp (base b d M : ℕ) (x : Data 9) : ProbComp (Data 9 × ℕ) :=
  let s := setupFromBData base b d M x
  (fun z => (z.1.extend fillMap9 s, 16 + z.2)) <$>
    randFillComp M (base + 4) (d * 2 ^ b) (s.comap fillMap9)

/-- Exact `ExecRand` semantics of `initFromBCode d`. -/
theorem initFromBCode_execRand {w base b d M : ℕ} {x : Data 9}
    (hbase : x.regs regBase = base) (hb : x.regs regB = b) (hM : x.regs regOut = M)
    (hfit_space : Fits w (base + spaceFromB b d))
    (hfit_powB : Fits w (2 ^ b)) (hfit_powM : Fits w (2 ^ M)) (hfit_d : Fits w d) :
    ExecRand w (initFromBCode d) x (initFromBComp base b d M x) := by
  unfold initFromBCode
  refine WP.Rand.execRand ?_
  wram_rand_call (setupFromBCode_exec hbase hb hM hfit_space hfit_powB hfit_powM hfit_d)
  wram_rand_call (randFillLoop_execRand (bits := M) (arrBase := base + 4) (d * 2 ^ b)
    (by wram_simp [setupFromBData, fillMap9]) (by wram_simp [setupFromBData, fillMap9])
    (by wram_simp [setupFromBData, fillMap9]) (by wram_simp [setupFromBData, fillMap9])
    (by wram_omega) (by fits)) renamed injective_fillMap9
  simp only [initFromBComp, Functor.map_map]

/-- The character table `extractTable base b d M z.1.mem` produced by `initFromBComp` is uniformly
distributed over `Fin (d * 2 ^ b) → Fin (2 ^ M)`. -/
theorem map_extractTable_eval_initFromBComp (base b d M : ℕ) (x : Data 9) :
    ((initFromBComp base b d M x).eval).map (fun z => extractTable base b d M z.1.mem) =
      PMF.uniformOfFintype (Fin (d * 2 ^ b) → Fin (2 ^ M)) := by
  dsimp only [initFromBComp, extractTable]
  rw [ProbComp.eval_map, PMF.map_comp]
  exact map_extractSlice_eval_randFillComp M (base + 4) (d * 2 ^ b)
    ((setupFromBData base b d M x).comap fillMap9)

/-- Self-contained `initCode d` that computes `b = charBits n_max` from `n_max` in `regKey` and
initializes the `d`-character simple tabulation table at `base` (`regBase`) with `M`-bit entries
(`regOut = M`). -/
@[expose] def initCode (d : ℕ) : Code .exact 9 :=
  .seq charBitsCode (initFromBCode d)

/-- Pathwise postcondition of `initFromBComp`: runs in `5 * (d * 2 ^ b) + 18` instructions and
establishes `Rep base b d M (extractTable base b d M z.1.mem) z.1.mem`, `z.1.regs regBase = base`,
and frame preservation outside `[base, base + spaceFromB b d)`. -/
theorem mem_support_initFromBComp {base b d M : ℕ} {x : Data 9} {z : Data 9 × ℕ}
    (hbase : x.regs regBase = base)
    (hz : z ∈ (initFromBComp base b d M x).support) :
    z.2 = 5 * (d * 2 ^ b) + 18 ∧
    Rep base b d M (extractTable base b d M z.1.mem) z.1.mem ∧
    z.1.regs regBase = base ∧
    (∀ a, (a < base ∨ base + spaceFromB b d ≤ a) → z.1.mem a = x.mem a) := by
  dsimp only [initFromBComp] at hz
  supp_cases hz with ⟨z₀, hz₀, rfl⟩
  obtain ⟨hsteps, -, -, -, -, hextra, hlt, hframe⟩ := mem_support_randFillComp hz₀
  have hdr {a : ℕ} (ha : a < base + 4) :
      z₀.1.mem a = (setupFromBData base b d M x).mem a := hframe a (Or.inl ha)
  refine ⟨by omega, ⟨?_, ?_, ?_, ?_, fun i => by simp [extractTable, extractSlice, hlt _ i.isLt]⟩,
    ?_, fun a ha => ?_⟩
  · change z₀.1.mem base = b; rw [hdr (by omega)]; wram_simp [setupFromBData]
  · change z₀.1.mem (base + 1) = 2 ^ b; rw [hdr (by omega)]; wram_simp [setupFromBData]
  · change z₀.1.mem (base + 2) = 2 ^ b - 1; rw [hdr (by omega)]; wram_simp [setupFromBData]
  · change z₀.1.mem (base + 3) = 2 ^ M - 1; rw [hdr (by omega)]; wram_simp [setupFromBData]
  · wram_simp [hextra, setupFromBData, fillMap9, hbase]
  · change z₀.1.mem a = x.mem a
    rw [hframe a (by wram_omega [ha])]
    wram_simp (disch := wram_omega) [setupFromBData]

/-- Hoare-style `ExecRandWithin` specification for `initFromBCode d`. -/
theorem initFromBCode_execRandWithin {w base b d M : ℕ} {x : Data 9}
    (hbase : x.regs regBase = base) (hb : x.regs regB = b) (hM : x.regs regOut = M)
    (hfit_space : Fits w (base + spaceFromB b d))
    (hfit_powB : Fits w (2 ^ b)) (hfit_powM : Fits w (2 ^ M)) (hfit_d : Fits w d) :
    ExecRandWithin w (initFromBCode d) x
      (fun y => Rep base b d M (extractTable base b d M y.mem) y.mem ∧
        y.regs regBase = base ∧
        (∀ a, (a < base ∨ base + spaceFromB b d ≤ a) → y.mem a = x.mem a))
      (5 * (d * 2 ^ b) + 18) (d * 2 ^ b) := by
  refine ⟨initFromBComp base b d M x,
    initFromBCode_execRand hbase hb hM hfit_space hfit_powB hfit_powM hfit_d,
    (OracleComp.isCostBounded_map_iff _ _ _).mpr (isQueryBounded_randFillComp ..), fun z hz => ?_⟩
  obtain ⟨hsteps, hrep, hbase', hframe'⟩ := mem_support_initFromBComp hbase hz
  exact ⟨⟨hrep, hbase', hframe'⟩, by omega⟩

/-- Explicit `ProbComp (Data 9 × ℕ)` produced by `initCode d` from `(base, n_max, M)`. -/
@[expose] noncomputable def initComp (base n_max d M : ℕ) (x : Data 9) : ProbComp (Data 9 × ℕ) :=
  (fun z => (z.1, (4 * Nat.log 2 (max n_max 2) + 12) + z.2)) <$>
    initFromBComp base (charBits n_max) d M (charBitsData n_max x)

/-- Exact `ExecRand` semantics of `initCode d`. -/
theorem initCode_execRand {w base n_max d M : ℕ} {x : Data 9}
    (hbase : x.regs regBase = base) (hn : x.regs regKey = n_max) (hM : x.regs regOut = M)
    (hfit_n : Fits w (max n_max 2))
    (hfit_space : Fits w (base + space n_max d))
    (hfit_powM : Fits w (2 ^ M)) (hfit_d : Fits w d) :
    ExecRand w (initCode d) x (initComp base n_max d M x) := by
  obtain ⟨hcb, hb_eq, hbase_eq, hout_eq, _⟩ := charBitsCode_exec (w := w) hn hfit_n
  have hfit_powB : Fits w (2 ^ charBits n_max) := by
    have hle := two_pow_charBits_le n_max
    rw [Nat.max_comm 2 n_max] at hle
    fits
  have hinit := initFromBCode_execRand
    (hbase_eq.trans hbase) hb_eq (hout_eq.trans hM) hfit_space hfit_powB hfit_powM hfit_d
  exact hcb.seqRand hinit

/-- **Uniformity of `TabulatedOddStride.initComp`**: the character table extracted from final
memory has the exact uniform distribution over `Fin (d * 2 ^ (charBits n_max)) → Fin (2 ^ M)`. -/
theorem map_extractTable_eval_initComp (base n_max d M : ℕ) (x : Data 9) :
    ((initComp base n_max d M x).eval).map
        (fun z => extractTable base (charBits n_max) d M z.1.mem) =
      PMF.uniformOfFintype (Fin (d * 2 ^ (charBits n_max)) → Fin (2 ^ M)) := by
  dsimp only [initComp]
  rw [ProbComp.eval_map, PMF.map_comp]
  exact map_extractTable_eval_initFromBComp base (charBits n_max) d M (charBitsData n_max x)

/-- Hoare-style `ExecRandWithin` specification for `TabulatedOddStride.initCode d`. -/
theorem initCode_execRandWithin {w base n_max d M : ℕ} {x : Data 9}
    (hbase : x.regs regBase = base) (hn : x.regs regKey = n_max) (hM : x.regs regOut = M)
    (hfit_n : Fits w (max n_max 2))
    (hfit_space : Fits w (base + space n_max d))
    (hfit_powM : Fits w (2 ^ M)) (hfit_d : Fits w d) :
    ExecRandWithin w (initCode d) x
      (fun y =>
        Rep base (charBits n_max) d M (extractTable base (charBits n_max) d M y.mem) y.mem ∧
        y.regs regBase = base ∧
        (∀ a, (a < base ∨ base + space n_max d ≤ a) → y.mem a = x.mem a))
      (4 * Nat.log 2 (max n_max 2) + 5 * (d * 2 ^ (charBits n_max)) + 30)
      (d * 2 ^ (charBits n_max)) := by
  obtain ⟨hcb, hb_eq, hbase_cb, hout_cb, hmem_cb⟩ := charBitsCode_exec (w := w) hn hfit_n
  have hfit_powB : Fits w (2 ^ charBits n_max) := by
    have hle := two_pow_charBits_le n_max; rw [Nat.max_comm 2 n_max] at hle; fits
  unfold initCode
  refine WP.RandWithin.execRandWithin ?_
  wram_rand_call hcb
  wram_rand_call (initFromBCode_execRandWithin (hbase_cb.trans hbase) hb_eq (hout_cb.trans hM)
    hfit_space hfit_powB hfit_powM hfit_d)
  rintro y ⟨hrep, hbase', hframe'⟩
  exact ⟨hrep, hbase', fun a ha => (hframe' a ha).trans (congrFun hmem_cb a)⟩

/-- 12-instruction deterministic setup before `tabLoop` in `evalCode d`: loads `b`, `2 ^ b`,
`2 ^ b - 1` from `base + 0 .. base + 2`, sets `regPtr = base + 4` and
`regEnd = base + 4 + d * 2 ^ b`, and zeros `regOut`. -/
@[expose] def evalSetupCode (d : ℕ) : Code .exact 9 :=
  .seq (.op (.load regB regBase))
  (.seq (.op (.const regTmp 1))
  (.seq (.op (.exactBin .add regPtr regBase regTmp))
  (.seq (.op (.load regPowB regPtr))
  (.seq (.op (.exactBin .add regPtr regPtr regTmp))
  (.seq (.op (.load regMaskB regPtr))
  (.seq (.op (.const regOut 2))
  (.seq (.op (.exactBin .add regPtr regPtr regOut))
  (.seq (.op (.const regOut d))
  (.seq (.op (.exactBin .mul regEnd regOut regPowB))
  (.seq (.op (.exactBin .add regEnd regPtr regEnd))
        (.op (.const regOut 0))))))))))))

/-- State after `evalSetupCode d`. -/
@[expose] def evalSetupData (base b d : ℕ) (x : Data 9) : Data 9 :=
  (((((((((((x.set regB b).set regTmp 1).set regPtr (base + 1)).set
    regPowB (2 ^ b)).set regPtr (base + 2)).set regMaskB (2 ^ b - 1)).set
    regOut 2).set regPtr (base + 4)).set regOut d).set regEnd (d * 2 ^ b)).set
    regEnd (base + 4 + d * 2 ^ b)).set regOut 0

/-- `evalSetupCode d` executes in `12` deterministic steps when `Rep base b d M T x.mem` holds. -/
theorem evalSetupCode_exec {w base b d M : ℕ} {T : Fin (d * 2 ^ b) → Fin (2 ^ M)} {x : Data 9}
    (hrep : Rep base b d M T x.mem) (hbase : x.regs regBase = base)
    (hfit_space : Fits w (base + spaceFromB b d)) (hfit_d : Fits w d) :
    Exec w (evalSetupCode d) x (evalSetupData base b d x) 12 := by
  obtain ⟨hm0, hm1, hm2, -, -⟩ := hrep
  unfold evalSetupCode evalSetupData
  wram_exec (disch := first | fits | omega | wram_omega) [hbase, hm0, hm1, hm2]

/-- Body of `tabLoop` (6 instructions): extracts `ch = regKey &&& regMaskB`, loads
`T[regPtr + ch]`, XORs into `regOut`, shifts `regKey` right by `regB`, and advances `regPtr` by
`regPowB`. -/
@[expose] def tabBody : Code .exact 9 :=
  .seq (.op (.exactBin .and regTmp regKey regMaskB))
  (.seq (.op (.exactBin .add regTmp regPtr regTmp))
  (.seq (.op (.load regTmp regTmp))
  (.seq (.op (.exactBin .xor regOut regOut regTmp))
  (.seq (.op (.exactBin .shiftRight regKey regKey regB))
        (.op (.exactBin .add regPtr regPtr regPowB))))))

/-- Loop over the `d` character tables `[base + 4, base + 4 + d * 2 ^ b)`. -/
@[expose] def tabLoop : Code .exact 9 :=
  .loop (.lt regPtr regEnd) tabBody

/-- `tabLoop` executes deterministically in `8 * rem + 2` instructions from character offset `j`
with `j + rem = d`, accumulating `(simpleTabAux b d M T rem j u acc).val` into `regOut` and
preserving `regBase` and all memory. -/
theorem tabLoop_exec {w base b d M : ℕ} {T : Fin (d * 2 ^ b) → Fin (2 ^ M)} {x : Data 9}
    (hrep : Rep base b d M T x.mem)
    (hfit_space : Fits w (base + spaceFromB b d)) (hfit_powM : Fits w (2 ^ M)) :
    ∀ (rem j u : ℕ) (acc : Fin (2 ^ M)) (d0 : Data 9),
      j + rem = d →
      d0.mem = x.mem →
      d0.regs regBase = base →
      d0.regs regPtr = base + 4 + j * 2 ^ b →
      d0.regs regEnd = base + 4 + d * 2 ^ b →
      d0.regs regB = b →
      d0.regs regPowB = 2 ^ b →
      d0.regs regMaskB = 2 ^ b - 1 →
      d0.regs regKey = u →
      d0.regs regOut = acc.val →
      Fits w u →
      ∃ y : Data 9,
        Exec w tabLoop d0 y (8 * rem + 2) ∧
        y.regs regOut = (simpleTabAux b d M T rem j u acc).val ∧
        y.regs regBase = base ∧
        y.mem = x.mem := by
  intro rem
  induction rem with
  | zero =>
    intro j u acc d0 hj hmem hbase hptr hend _ _ _ _ hout _
    exact ⟨d0, Exec.loop_exit (by simp [Cond.Holds, hptr, hend, show j = d by omega]),
      by simp [simpleTabAux, hout], hbase, hmem⟩
  | succ rem ih =>
    intro j u acc d0 hj hmem hbase hptr hend hb hpowB hmaskB hkey hout hfit_u
    have hmul_le : (j + 1) * 2 ^ b ≤ d * 2 ^ b := Nat.mul_le_mul_right _ (by omega)
    have hmul_lt : j * 2 ^ b < d * 2 ^ b :=
      Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos b)
    have hnext_eq : base + 4 + j * 2 ^ b + 2 ^ b = base + 4 + (j + 1) * 2 ^ b := by ring
    set ch := u &&& (2 ^ b - 1) with hch
    have hch_lt : ch < 2 ^ b := by
      rw [hch, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt u (Nat.two_pow_pos b)
    set idx := j * 2 ^ b + ch
    have hidx_lt : idx < d * 2 ^ b := by
      have : j * 2 ^ b + 2 ^ b = (j + 1) * 2 ^ b := by ring
      omega
    have hentry_mem : d0.mem (base + 4 + j * 2 ^ b + ch) = (T ⟨idx, hidx_lt⟩).val := by
      rw [hmem, show base + 4 + j * 2 ^ b + ch = base + 4 + idx by omega]
      exact hrep.2.2.2.2 ⟨idx, hidx_lt⟩
    set newAcc : Fin (2 ^ M) :=
      ⟨acc.val ^^^ (T ⟨idx, hidx_lt⟩).val, Nat.xor_lt_two_pow acc.isLt (T ⟨idx, hidx_lt⟩).isLt⟩
    have hfit_ch : Fits w ch := hfit_u.of_le Nat.and_le_left
    have hfit_shr : Fits w (u >>> b) := hfit_u.of_le (Nat.shiftRight_le u b)
    refine WP.Exact.exists_exec
      (WP.Exact.loop_iter (by simp only [Cond.Holds, hptr, hend]; omega) ?_)
    wram_exec (disch := first | fits | omega | wram_omega)
      [tabBody, hkey, hmaskB, hptr, hout, hb, hpowB, ← hch, hentry_mem,
        show acc.val ^^^ (T ⟨idx, hidx_lt⟩).val = newAcc.val from rfl]
    wram_call (ih (j + 1) (u >>> b) newAcc _ (by omega) hmem (by wram_simp [hbase])
      (by wram_simp [hnext_eq]) (by wram_simp [hend]) (by wram_simp [hb]) (by wram_simp [hpowB])
      (by wram_simp [hmaskB]) (by wram_simp) (by wram_simp) hfit_shr)
      with y ⟨hy_out, hy_base, hy_mem⟩
    exact ⟨by omega, hy_out.trans (by simp only [simpleTabAux, ch, idx, hidx_lt, ↓reduceDIte,
      newAcc]), hy_base, hy_mem⟩

/-- 7-instruction finishing suffix of `evalCode d`: loads `2 ^ M - 1` from `base + 3` and maps
`acc` in `regOut` to `(2 * acc + 1) &&& (2 ^ M - 1)`. -/
@[expose] def evalFinishCode : Code .exact 9 :=
  .seq (.op (.const regTmp 3))
  (.seq (.op (.exactBin .add regTmp regBase regTmp))
  (.seq (.op (.load regTmp regTmp))
  (.seq (.op (.exactBin .add regOut regOut regOut))
  (.seq (.op (.const regB 1))
  (.seq (.op (.exactBin .add regOut regOut regB))
        (.op (.exactBin .and regOut regOut regTmp)))))))

/-- Complete `d`-character simple tabulation odd-stride evaluation program `evalCode d`. -/
@[expose] def evalCode (d : ℕ) : Code .exact 9 :=
  .seq (evalSetupCode d) (.seq tabLoop evalFinishCode)

/-- **`TabulatedOddStride.evalCode d` correctness and complexity**: for any character table
`T : Fin (d * 2 ^ b) → Fin (2 ^ M)` represented at `base` and key `u` with `Fits w u`,
`evalCode d` halts deterministically in `8 * d + 21 = O(d)` instructions, preserving `regBase`
and all memory and writing `(tabulatedOddStride b d M T u).val` into `regOut`. -/
theorem evalCode_execWithin {w base b d M u : ℕ} {T : Fin (d * 2 ^ b) → Fin (2 ^ M)} {x : Data 9}
    (hrep : Rep base b d M T x.mem)
    (hbase : x.regs regBase = base) (hu : x.regs regKey = u)
    (hfit_space : Fits w (base + spaceFromB b d))
    (hfit_powM : Fits w (2 * 2 ^ M)) (hfit_d : Fits w d) (hfit_u : Fits w u) :
    ∃ y : Data 9,
      ExecWithin w (evalCode d) x y (8 * d + 21) ∧
      y.regs regOut = (tabulatedOddStride b d M T u).val ∧
      y.regs regBase = base ∧
      y.mem = x.mem := by
  unfold evalCode
  refine WP.exists_execWithin (WP.Exact.toWP ?_)
  wram_exec
  refine WP.Exact.of_exec (evalSetupCode_exec hrep hbase hfit_space hfit_d) ?_
  wram_exec
  wram_call (tabLoop_exec hrep hfit_space (by fits) d 0 u ⟨0, Nat.two_pow_pos M⟩ _
    (by omega) rfl (by wram_simp [evalSetupData, hbase])
    (by wram_simp [evalSetupData, Nat.zero_mul])
    (by wram_simp [evalSetupData]) (by wram_simp [evalSetupData]) (by wram_simp [evalSetupData])
    (by wram_simp [evalSetupData]) (by wram_simp [evalSetupData, hu])
    (by wram_simp [evalSetupData]) hfit_u)
    with yLoop ⟨hy_out, hy_base, hy_mem⟩
  change yLoop.regs regOut = (simpleTab b d M T u).val at hy_out
  set tab := simpleTab b d M T u
  have hfit_and : Fits w ((tab.val + tab.val + 1) &&& (2 ^ M - 1)) :=
    (by fits : Fits w (tab.val + tab.val + 1)).of_le Nat.and_le_left
  wram_exec (disch := first | fits | omega | wram_omega)
    [evalFinishCode, hy_base, hy_out, hy_mem, hrep.2.2.2.1]
  exact ⟨by wram_simp [tabulatedOddStride, oddStride, tab, Nat.two_mul],
    by wram_simp [hy_base], hy_mem⟩

end TabulatedOddStride

end Cslib.DataStructure.HashFamily.WordRAM.Tabulation
