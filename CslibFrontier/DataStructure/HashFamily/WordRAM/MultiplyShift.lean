/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Randomized.Structured
public import CslibFrontier.Probability.HashFamily.MultiplyShift
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Tactic.SuppCases

/-!
# Self-contained Word-RAM multiply-shift hashing

This file implements the multiply-shift universal hash family of Dietzfelbinger, Hagerup,
Katajainen, and Penttonen [DietzfelbingerHagerupKatajainenPenttonen1997] as a self-contained pair
of structured Word-RAM programs over `Cslib.WordRAM.Basis.exact`:

* `Cslib.DataStructure.HashFamily.WordRAM.MultiplyShift.initCode w₀`: samples a uniform seed
  `b ∈ [0, 2 ^ (w₀ - 1) - 1]` into register `regB` in `2` instructions and `1` `Instr.rand` call.
* `Cslib.DataStructure.HashFamily.WordRAM.MultiplyShift.evalCode w₀ M`: deterministically computes
  `((2 * b + 1) * x % 2 ^ w₀) / 2 ^ (w₀ - M)` in register `regOut` from seed `b` in `regB` and key
  `x` in `regX` in `9` instructions (`0` `rand` calls) without intermediate word overflow whenever
  `0 < w₀`, `M ≤ w₀`, and `2 * w₀ ≤ w`.

We prove that `initCode w₀` induces the exact uniform distribution
`PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1)))` on the seed register `regB`, that `evalCode w₀ M`
computes `Cslib.Probability.multiplyShift w₀ M b x`, and hence that the Word-RAM evaluation map is
`(2 / 2 ^ M)`-universal (`isUniversalHash_evalData`).

## Main definitions

* `regB`, `regX`, `regOut`, `regT1`, `regT2`: register layout in `Fin 5`.
* `initCode`, `initComp`: seed-sampling code and its exact `ProbComp` semantics.
* `evalCode`, `evalData`: deterministic evaluation code and its closed-form final `Data 5`.

## Main results

* `initCode_execRand`, `initCode_execRandWithin`: exact and Hoare-style execution of `initCode`.
* `map_extractSeed_eval_initComp`: the seed sampled by `initCode` has distribution
  `PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1)))`.
* `evalCode_exec`, `evalCode_execWithin`: exact `9`-instruction execution of `evalCode` computing
  `Cslib.Probability.multiplyShift w₀ M`.
* `isUniversalHash_evalData`: the hash family computed in register `regOut` by `evalCode` under the
  seed distribution of `initCode` is `(2 / 2 ^ M)`-universal.

## References

* [M. Dietzfelbinger, T. Hagerup, J. Katajainen, M. Penttonen, *A Reliable Randomized Algorithm
  for the Closest-Pair Problem*][DietzfelbingerHagerupKatajainenPenttonen1997], Lemma 2.4.
-/

public section

namespace Cslib.DataStructure.HashFamily.WordRAM.MultiplyShift

open Cslib.WordRAM Cslib.Probability
open scoped ENNReal

/-! ## Register layout (`Fin 5`) -/

/-- Register `0`: holds the sampled seed `b < 2 ^ (w₀ - 1)`. -/
abbrev regB : Fin 5 := 0

/-- Register `1`: holds the input key `x < 2 ^ w₀`. -/
abbrev regX : Fin 5 := 1

/-- Register `2`: receives the `M`-bit hash value `multiplyShift w₀ M b x`. -/
abbrev regOut : Fin 5 := 2

/-- Register `3`: first scratch register. -/
abbrev regT1 : Fin 5 := 3

/-- Register `4`: second scratch register. -/
abbrev regT2 : Fin 5 := 4

/-! ## Seed initialization (`initCode`) -/

/-- Structured Word-RAM program that initializes the multiply-shift seed `b ∈ [0, 2 ^ (w₀ - 1) - 1]`
in `regB` using `2` instructions and `1` `rand` call. -/
@[expose]
def initCode (w₀ : ℕ) : Code .exact 5 :=
  .seq (.op (.const regT1 (2 ^ (w₀ - 1) - 1)))
       (.rand regB regT1)

/-- Closed-form machine data after `initCode w₀` samples `k`. -/
@[expose]
def initData (w₀ : ℕ) (d : Data 5) (k : ℕ) : Data 5 :=
  (d.set regT1 (2 ^ (w₀ - 1) - 1)).set regB k

/-- Exact `ProbComp` computation induced by `initCode w₀` from initial data `d`. -/
@[expose]
def initComp (w₀ : ℕ) (d : Data 5) : ProbComp (Data 5 × ℕ) := do
  let k ← ProbComp.unifFin (2 ^ (w₀ - 1) - 1)
  pure (initData w₀ d k.val, 2)

@[simp]
theorem initData_regs_b (w₀ : ℕ) (d : Data 5) (k : ℕ) :
    (initData w₀ d k).regs regB = k := by
  simp [initData]

@[simp]
theorem initData_regs_x (w₀ : ℕ) (d : Data 5) (k : ℕ) :
    (initData w₀ d k).regs regX = d.regs regX := by
  simp [initData, regB, regX, regT1]

@[simp]
theorem initData_regs_out (w₀ : ℕ) (d : Data 5) (k : ℕ) :
    (initData w₀ d k).regs regOut = d.regs regOut := by
  simp [initData, regB, regOut, regT1]

@[simp]
theorem initData_mem (w₀ : ℕ) (d : Data 5) (k : ℕ) :
    (initData w₀ d k).mem = d.mem := by rfl

/-- When `w₀ ≤ w`, `initCode w₀` executes cleanly in `2` instructions and `1` `rand` call with exact
`ProbComp` semantics `initComp w₀ d`. -/
theorem initCode_execRand {w₀ w : ℕ} (hw : w₀ ≤ w) (d : Data 5) :
    ExecRand w (initCode w₀) d (initComp w₀ d) := by
  have hfit : Fits w (2 ^ (w₀ - 1) - 1) := by fits
  have h2 := ExecRand.rand (B := .exact) (w := w) (dst := regB) (src := regT1)
    (x := d.set regT1 (2 ^ (w₀ - 1) - 1)) (by rwa [Data.set_regs_self])
  rw [Data.set_regs_self] at h2
  simpa only [initCode, initComp, initData, ← bind_pure_comp, bind_assoc, pure_bind] using
    (Exec.const hfit).seqRand h2

/-- Hoare-style specification for `initCode w₀`: runs in `2` steps and `1` `rand` call, placing a
seed `< 2 ^ (w₀ - 1)` in `regB` while preserving `regX`, `regOut`, and memory. -/
theorem initCode_execRandWithin {w₀ w : ℕ} (hw : w₀ ≤ w) (d : Data 5) :
    ExecRandWithin w (initCode w₀) d
      (fun d' => d'.regs regB < 2 ^ (w₀ - 1) ∧
        d'.regs regX = d.regs regX ∧
        d'.regs regOut = d.regs regOut ∧
        d'.mem = d.mem) 2 1 := by
  refine ⟨initComp w₀ d, initCode_execRand hw d,
    by simpa only [initComp, Nat.add_zero] using
      (ProbComp.isQueryBounded_unifFin (2 ^ (w₀ - 1) - 1)).bind fun _ => .pure _ 0, ?_⟩
  intro z hz
  dsimp only [initComp] at hz
  supp_cases hz with ⟨k, rfl⟩
  exact ⟨⟨by rw [initData_regs_b]; fits, by simp, by simp, rfl⟩, le_rfl⟩

/-- Extracting the seed `< 2 ^ (w₀ - 1)` from register `regB` of a machine state `d'`, defaulting to
`0` outside the valid range. -/
@[expose]
def extractSeed (w₀ : ℕ) (d' : Data 5) : Fin (2 ^ (w₀ - 1)) :=
  if h : d'.regs regB < 2 ^ (w₀ - 1) then ⟨d'.regs regB, h⟩
  else ⟨0, by positivity⟩

@[simp]
theorem extractSeed_initData (w₀ : ℕ) (d : Data 5) (k : Fin (2 ^ (w₀ - 1) - 1 + 1)) :
    extractSeed w₀ (initData w₀ d k.val) =
      finCongr (Nat.sub_add_cancel Nat.one_le_two_pow) k := by
  have hlt : k.val < 2 ^ (w₀ - 1) :=
    Nat.lt_of_lt_of_le k.isLt (Nat.sub_add_cancel Nat.one_le_two_pow).le
  exact Fin.ext (by simp [extractSeed, hlt])

/-- **Uniformity of the sampled seed**: the distribution of `extractSeed w₀ z.1` under
`(initComp w₀ d).eval` is the exact uniform distribution
`PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1)))`. -/
theorem map_extractSeed_eval_initComp (w₀ : ℕ) (d : Data 5) :
    ((initComp w₀ d).eval).map (fun z => extractSeed w₀ z.1) =
      PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1))) := by
  rw [initComp, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_unifFin, PMF.map_comp]
  have hcomp : ((fun z : Data 5 × ℕ => extractSeed w₀ z.1) ∘
      fun k : Fin (2 ^ (w₀ - 1) - 1 + 1) => (initData w₀ d k.val, 2)) =
      finCongr (Nat.sub_add_cancel Nat.one_le_two_pow) :=
    funext (extractSeed_initData w₀ d)
  rw [hcomp]
  exact PMF.uniformOfFintype_map_equiv (finCongr (Nat.sub_add_cancel Nat.one_le_two_pow))

/-! ## Deterministic hash evaluation (`evalCode`) -/

/-- Structured Word-RAM program that evaluates `multiplyShift w₀ M` in `9` deterministic
instructions (`0` `rand` calls), reading `b` from `regB` and `x` from `regX` and writing the hash
value into `regOut`. -/
@[expose]
def evalCode (w₀ M : ℕ) : Code .exact 5 :=
  .seq (.op (.const regT1 2))
  (.seq (.op (.exactBin .mul regT1 regT1 regB))
  (.seq (.op (.const regT2 1))
  (.seq (.op (.exactBin .add regT1 regT1 regT2))
  (.seq (.op (.exactBin .mul regT1 regT1 regX))
  (.seq (.op (.const regT2 (2 ^ w₀ - 1)))
  (.seq (.op (.exactBin .and regT1 regT1 regT2))
  (.seq (.op (.const regT2 (w₀ - M)))
        (.op (.exactBin .shiftRight regOut regT1 regT2)))))))))

/-- Closed-form final machine data produced by `evalCode w₀ M` from `d`. -/
@[expose]
def evalData (w₀ M : ℕ) (d : Data 5) : Data 5 :=
  let b := d.regs regB
  let x := d.regs regX
  let low := ((2 * b + 1) * x) &&& (2 ^ w₀ - 1)
  (((d.set regT1 low).set regT2 (w₀ - M)).set regOut (low >>> (w₀ - M)))

@[simp]
theorem evalData_regs_out (w₀ M : ℕ) (d : Data 5) :
    (evalData w₀ M d).regs regOut =
      (((2 * d.regs regB + 1) * d.regs regX) &&& (2 ^ w₀ - 1)) >>> (w₀ - M) := by
  simp [evalData]

/-- The output register `regOut` of `evalData w₀ M d` equals
`Cslib.Probability.multiplyShift w₀ M`. -/
theorem evalData_regs_out_eq_multiplyShift (w₀ M : ℕ) (d : Data 5)
    (b : Fin (2 ^ (w₀ - 1))) (x : Fin (2 ^ w₀))
    (hb : d.regs regB = b.val) (hx : d.regs regX = x.val) :
    (evalData w₀ M d).regs regOut = multiplyShift w₀ M b x := by
  rw [evalData_regs_out, hb, hx, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    multiplyShift]

@[simp]
theorem evalData_regs_b (w₀ M : ℕ) (d : Data 5) :
    (evalData w₀ M d).regs regB = d.regs regB := by
  simp [evalData, regB, regOut, regT1, regT2]

@[simp]
theorem evalData_regs_x (w₀ M : ℕ) (d : Data 5) :
    (evalData w₀ M d).regs regX = d.regs regX := by
  simp [evalData, regX, regOut, regT1, regT2]

@[simp]
theorem evalData_mem (w₀ M : ℕ) (d : Data 5) :
    (evalData w₀ M d).mem = d.mem := by rfl

/-- **Exact `9`-instruction execution of `evalCode w₀ M`** without intermediate word overflow when
`0 < w₀`, `2 * w₀ ≤ w`, `d.regs regB < 2 ^ (w₀ - 1)`, and `d.regs regX < 2 ^ w₀`. -/
theorem evalCode_exec {w₀ M w : ℕ} (hw₀ : 0 < w₀) (hw : 2 * w₀ ≤ w)
    {d : Data 5} (hb : d.regs regB < 2 ^ (w₀ - 1)) (hx : d.regs regX < 2 ^ w₀) :
    Exec w (evalCode w₀ M) d (evalData w₀ M d) 9 := by
  unfold evalCode
  wram_exec
  ext i : 2
  · fin_cases i <;> rfl
  · rfl

/-- Bounded-time execution corollary for `evalCode w₀ M` (`9` instructions). -/
theorem evalCode_execWithin {w₀ M w : ℕ} (hw₀ : 0 < w₀) (hw : 2 * w₀ ≤ w)
    {d : Data 5} (hb : d.regs regB < 2 ^ (w₀ - 1)) (hx : d.regs regX < 2 ^ w₀) :
    ExecWithin w (evalCode w₀ M) d (evalData w₀ M d) 9 :=
  (evalCode_exec hw₀ hw hb hx).within

/-- **Universal hashing guarantee for the Word-RAM multiply-shift implementation**:
under the seed distribution of `initCode w₀`, the hash function mapping `x : Fin (2 ^ w₀)` to the
output register `regOut` of `evalData w₀ M` is `(2 / 2 ^ M)`-universal whenever `0 < w₀` and
`M ≤ w₀`. -/
theorem isUniversalHash_evalData {w₀ M : ℕ} (hw₀ : 0 < w₀) (hM : M ≤ w₀) (d : Data 5) :
    IsUniversalHash
      (((initComp w₀ d).eval).map (fun z => extractSeed w₀ z.1))
      (fun b (x : Fin (2 ^ w₀)) =>
        (evalData w₀ M ((d.set regB b.val).set regX x.val)).regs regOut)
      (2 / 2 ^ M) := by
  rw [map_extractSeed_eval_initComp]
  convert isUniversalHash_multiplyShift hw₀ hM using 1
  funext b x
  exact evalData_regs_out_eq_multiplyShift w₀ M _ b x (by simp) (by simp)

end Cslib.DataStructure.HashFamily.WordRAM.MultiplyShift
