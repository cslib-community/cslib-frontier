/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.EasyWitness.NEVerifier
import CslibFrontier.Computability.Complexity.Classes.EasyWitness.QuasiPoly.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Tests for the verifiers of `NE` and `NQuasiP`

A concrete verifier, with witnesses of the length of the instance that must equal it
(`verify (x, y) = decide (x = y)`), satisfies every field of
`Cslib.Complexity.EasyWitness.NEVerifier` and of `Cslib.Complexity.EasyWitness.QuasiPolyVerifier`:

* the verifier accepts the pair `([true], [true])` and rejects `([true], [false])`;
* its language is all words (each is its own witness), and it is in `NE` and in `NQuasiP` by
  `NEVerifier.language_mem_NE` and `QuasiPolyVerifier.language_mem_NQuasiP`;
* the explicit time bounds of the fields hold: `(n + 1) (2 n + 1) ≤ 2 * 2 ^ (2 n)` for `NE`, and
  `(n + 1) (2 n + 1) ≤ 4 * 2 ^ (⌊log₂ n⌋ + 1) ^ 2` for `NQuasiP`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Complexity.Classes.EasyWitness.Verifier

open Cslib Cslib.Complexity Cslib.Complexity.EasyWitness Turing Turing.MultiTapeTM

/-- The length of a word is computable in polynomial time, in binary. -/
private theorem polyTime_length :
    ComputableInPolyTime (fun x : List Bool => x.length) encBits encNat :=
  ComputableInO.lengthNat.computableInPolyTime
    (.of_forall_le 1 1 fun l => by simp [encBits_apply])
    (.of_forall_le 1 1 fun l => by simp [encBits_apply])

/-- The time of the equality test on a pair of words. -/
private def eqTime (p : List Bool × List Bool) : ℕ :=
  ((encBits p.1).length + 1) * ((encBits p.1).length + (encBits p.2).length + 1)

/-- The equality test on a pair of words is computable in quadratic time and linear space. -/
private theorem computableInO_eq :
    ComputableInO (fun p : List Bool × List Bool => decide (p.1 = p.2))
      (encPair encBits encBits) encBool eqTime
      (fun p => (encPair encBits encBits p).length) :=
  ComputableInO.eq encBits

/-- The quadratic time bound on witnesses of the length of the instance. -/
private theorem eqTime_le (x y : List Bool) (hy : y.length = x.length) :
    eqTime (x, y) ≤ 2 * 2 ^ (2 * x.length) := by
  have h : x.length + 1 ≤ 2 ^ x.length := Nat.lt_two_pow_self
  have h2 : 2 ^ (2 * x.length) = 2 ^ x.length * 2 ^ x.length := by rw [two_mul, pow_add]
  simp only [eqTime, encBits_apply, hy]
  rw [h2]
  nlinarith

/-- **A verifier for `NE`**: the witness is the instance itself. -/
def neVerifier : NEVerifier where
  witnessLen x := x.length
  verify p := decide (p.1 = p.2)
  time := eqTime
  space p := (encPair encBits encBits p).length
  witnessLen_polyTime := polyTime_length
  verify_computableInO := computableInO_eq
  witnessLen_lt := ⟨1, fun x => by
    have : x.length + 1 < 2 ^ (x.length + 1) := Nat.lt_two_pow_self
    rw [one_mul]
    omega⟩
  time_le := ⟨2, 2, fun x y hy => eqTime_le x y hy⟩

/-- **A verifier for `NQuasiP`**: the witness is the instance itself. -/
def quasiPolyVerifier : QuasiPolyVerifier where
  witnessLen x := x.length
  verify p := decide (p.1 = p.2)
  time := eqTime
  space p := (encPair encBits encBits p).length
  witnessLen_polyTime := polyTime_length
  verify_computableInO := computableInO_eq
  witnessLen_lt := ⟨1, fun x => by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) x.length
    simpa using this⟩
  time_le := ⟨4, 2, fun x y hy => by
    have h : x.length + 1 ≤ 2 ^ (Nat.log 2 x.length + 1) :=
      Nat.lt_pow_succ_log_self (b := 2) (by norm_num) x.length
    have hL : 2 * (Nat.log 2 x.length + 1) ≤ (Nat.log 2 x.length + 1) ^ 2 + 1 := by
      nlinarith [sq_nonneg ((Nat.log 2 x.length : ℤ))]
    have h2 : 2 ^ (2 * (Nat.log 2 x.length + 1)) =
        2 ^ (Nat.log 2 x.length + 1) * 2 ^ (Nat.log 2 x.length + 1) := by rw [two_mul, pow_add]
    have h3 : 2 ^ (2 * (Nat.log 2 x.length + 1)) ≤
        2 * 2 ^ (Nat.log 2 x.length + 1) ^ 2 := by
      calc _ ≤ 2 ^ ((Nat.log 2 x.length + 1) ^ 2 + 1) := Nat.pow_le_pow_right (by norm_num) hL
        _ = _ := by rw [pow_succ, mul_comm]
    simp only [eqTime, encBits_apply, hy]
    rw [h2] at h3
    nlinarith⟩

/-- The verifier accepts a pair of equal words and rejects a pair of different ones. -/
example : neVerifier.verify ([true], [true]) = true ∧
    neVerifier.verify ([true], [false]) = false ∧
    quasiPolyVerifier.verify ([true, false], [true, false]) = true ∧
    quasiPolyVerifier.verify ([true, false], [true]) = false := by decide

/-- Every word is a witness for itself, so the language of each verifier is everything. -/
example : neVerifier.language = Set.univ ∧ quasiPolyVerifier.language = Set.univ := by
  refine ⟨Set.eq_univ_of_forall fun x => ?_, Set.eq_univ_of_forall fun x => ?_⟩
  · exact (neVerifier.mem_language_iff x).2 ⟨x, rfl, by simp [neVerifier]⟩
  · exact (quasiPolyVerifier.mem_language_iff x).2 ⟨x, rfl, by simp [quasiPolyVerifier]⟩

/-- The language of `neVerifier` is in `NE`. -/
example : neVerifier.language ∈ NE encBits := neVerifier.language_mem_NE

/-- The language of `quasiPolyVerifier` is in `NQuasiP`. -/
example : quasiPolyVerifier.language ∈ NQuasiP encBits := quasiPolyVerifier.language_mem_NQuasiP

end CslibFrontierTests.Computability.Complexity.Classes.EasyWitness.Verifier
