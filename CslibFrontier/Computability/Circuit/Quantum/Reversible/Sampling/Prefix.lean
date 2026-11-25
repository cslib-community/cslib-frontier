/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Classical
public import CslibFrontier.Computability.Circuit.Quantum.Uniform
public import CslibFrontier.Foundations.Quantum.Measurement.Readout
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Moving a measured block to the output prefix

`prefixSwapCodes source count` swaps the block beginning at `source` with the first `count`
qubits.  The blocks must be disjoint.  This is a terminal layout adapter: it does not prepare
randomness, run a sampler or change the distribution read from the source block.

## Main definitions

* `Cslib.Quantum.blockReadout`: read a consecutive block of a basis word.
* `Cslib.Quantum.GateCode.prefixSwapCodes`: three CNOTs for each pair of block wires.

## Main results

* `Cslib.Quantum.listOfFn_castLEEmb_eq_blockReadout`: reading a well-formed output prefix agrees
  with the block readout at zero.
* `Cslib.Quantum.GateCode.readBit_classicalRun_prefixSwapCodes`: each prefix bit after the
  adapter is exactly the former source block.
* `Cslib.Quantum.measureOut_eval_prefixSwapCodes`: terminal measurement preserves that exact
  output law.

These layout lemmas are original infrastructure.
-/

public section

namespace Cslib.Quantum

open Turing.MultiTapeTM

/-- Read `count` consecutive qubits beginning at `source`. -/
@[expose] def blockReadout {width : ℕ} (source count : ℕ)
    (x : Fin width → Bool) : Fin count → Bool :=
  fun j => readBit x (source + j)

/-- Reading a prefix through its inclusion into a larger register agrees with the block readout
beginning at zero. -/
theorem listOfFn_castLEEmb_eq_blockReadout {count width : ℕ} (h : count ≤ width) :
    (fun y : Fin width → Bool =>
      List.ofFn fun i : Fin count => y (Fin.castLEEmb h i)) =
      fun y => List.ofFn (blockReadout 0 count y) := by
  funext y
  refine congrArg List.ofFn (funext fun i => ?_)
  rw [blockReadout, readBit_of_lt y (by omega)]
  exact congrArg y (Fin.ext (by simp))

namespace GateCode

/-- Swap the block `source, …, source + count - 1` with the output prefix. -/
def prefixSwapCodes (source count : ℕ) : List GateCode :=
  (List.range count).flatMap fun j => swapWireCodes j (source + j)

@[simp] theorem length_prefixSwapCodes (source count : ℕ) :
    (prefixSwapCodes source count).length = 3 * count := by
  simp [prefixSwapCodes, Nat.mul_comm]

private theorem prefixSwapCodes_succ (source count : ℕ) :
    prefixSwapCodes source (count + 1) =
      prefixSwapCodes source count ++ swapWireCodes count (source + count) := by
  simp [prefixSwapCodes, List.range_succ]

/-- The block-to-prefix adapter is classical and well formed when its two blocks are disjoint and
fit in the register. -/
theorem isClassical_prefixSwapCodes {source count width : ℕ} (hdisjoint : count ≤ source)
    (hfit : source + count ≤ width) : IsClassical width (prefixSwapCodes source count) := by
  intro g hg
  obtain ⟨j, hj, hg⟩ := List.mem_flatMap.mp hg
  have hj' := List.mem_range.mp hj
  exact isClassical_swapWireCodes (by omega) (by omega) (by omega) g hg

/-- Every output-prefix bit after the adapter is the corresponding former source-block bit. -/
theorem readBit_classicalRun_prefixSwapCodes {source count width : ℕ}
    (hdisjoint : count ≤ source) (hfit : source + count ≤ width)
    (x : Fin width → Bool) {j : ℕ} (hj : j < count) :
    readBit (classicalRun (prefixSwapCodes source count) x) j = readBit x (source + j) := by
  induction count generalizing j x with
  | zero => omega
  | succ count ih =>
    rw [prefixSwapCodes_succ, classicalRun_append]
    by_cases hj' : j < count
    · rw [readBit_classicalRun_swapWireCodes_of_ne (by omega) (by omega)]
      exact ih (by omega) (by omega) _ hj'
    · obtain rfl : j = count := by omega
      rw [readBit_classicalRun_swapWireCodes (by omega) (by omega) (by omega)]
      apply readBit_classicalRun_of_forall_ne
      intro g hg htarget
      obtain ⟨i, hi, hgi⟩ := List.mem_flatMap.mp hg
      have := List.mem_range.mp hi
      simp only [swapWireCodes, List.mem_cons, List.not_mem_nil, or_false] at hgi
      rcases hgi with rfl | rfl | rfl <;> simp_all

variable {γ : Type} {enc : γ ↪ List Bool}

/-- Block-to-prefix layout code is generated in polynomial time from unary block positions. -/
theorem computableInPolyTime_prefixSwapCodes {source count : γ → ℕ}
    (hsource : ComputableInPolyTime source enc encUnary)
    (hcount : ComputableInPolyTime count enc encUnary) :
    ComputableInPolyTime (fun a => prefixSwapCodes (source a) (count a)) enc
      (encList encGateCode) := by
  unfold prefixSwapCodes swapWireCodes
  fun_prop

end GateCode

/-- Terminal block-to-prefix swaps preserve the exact measured law of the source block. -/
theorem measureOut_eval_prefixSwapCodes {source count width : ℕ}
    (hdisjoint : count ≤ source) (hfit : source + count ≤ width)
    (ψ : Qubits width) (hψ : ‖ψ‖ = 1) :
    measureOut
        (Circuit.eval (Circuit.ofCodes width (GateCode.prefixSwapCodes source count)) ψ)
        (by rw [Circuit.norm_eval, hψ]) (blockReadout 0 count) =
      measureOut ψ hψ (blockReadout source count) := by
  classical
  refine PMF.ext fun y => ?_
  rw [measureOut_eq_ofReal_measureProb, measureOut_eq_ofReal_measureProb,
    Circuit.measureProb_eval_ofCodes (GateCode.isClassical_prefixSwapCodes hdisjoint hfit),
    measureProb, ← Finset.sum_filter]
  have hout (x : Fin width → Bool) :
      blockReadout 0 count (GateCode.classicalRun (GateCode.prefixSwapCodes source count) x) =
        blockReadout source count x :=
    funext fun j => by
      simpa [blockReadout] using
        GateCode.readBit_classicalRun_prefixSwapCodes hdisjoint hfit x j.isLt
  exact congrArg ENNReal.ofReal (congrArg (Finset.sum · _)
    (Finset.ext fun x => by simp [hout x]))

end Cslib.Quantum
