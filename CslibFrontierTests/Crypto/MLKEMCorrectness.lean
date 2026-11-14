/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.Correctness
import CslibFrontierTests.Crypto.MLKEMFixture

/-! Checked clients for the source-shaped ML-KEM K-PKE core-noise correctness bridge. -/

public section

namespace CslibFrontierTests.Crypto.MLKEMCorrectness

open Cslib Cslib.Crypto Cslib.Crypto.MLKEM Cslib.Crypto.Protocols
open CslibFrontierTests.Crypto.MLKEM

/-! The finite FIPS parameter records leave exactly the advertised radius after scalar
compression. These are arithmetic facts, not numerical decryption-failure bounds. -/

example : scalarCompressionAllowance mlkem512 = 104 ∧
    727 + scalarCompressionAllowance mlkem512 ≤ 831 ∧ 4 * 831 + 2 < mlkem512.q := by
  decide

example : scalarCompressionAllowance mlkem1024 = 52 ∧
    779 + scalarCompressionAllowance mlkem1024 ≤ 831 ∧ 4 * 831 + 2 < mlkem1024.q := by
  decide

local instance : NeZero mlkem512.q := ⟨by decide⟩

/-- The intended standard-parameter API: any checked upper bound on the exact event gives the
matching K-PKE `DeltaCorrect` bound. -/
example {δ : ℝ} (hδ : coreNoiseFailureProbability mlkem512 727 ≤ δ) :
    (toExplicitCoinPKE mlkem512).DeltaCorrect δ :=
  deltaCorrect_of_coreNoiseFailureProbability_le mlkem512 (T := 727) (B := 831)
    (by decide) (by decide) hδ

/-! A small evaluated positive and negative witness ensures that the event is neither definitionally
empty nor automatically true. With zero matrix, secrets, and vector errors, the core noise is `e₂`. -/

def zeroA : Matrix (Fin toy.k) (Fin toy.k) (Fin toy.n → ZMod toy.q) := 0

def zeroVec : Fin toy.k → Fin toy.n → ZMod toy.q := 0

def largeScalarError : Fin toy.n → ZMod toy.q := ![4, 0]

def boundedScalarError : Fin toy.n → ZMod toy.q := ![3, 0]

example : coreNoiseFailure toy 3 zeroA zeroVec zeroVec zeroVec zeroVec largeScalarError := by
  decide

example : ¬ coreNoiseFailure toy 3 zeroA zeroVec zeroVec zeroVec zeroVec boundedScalarError := by
  decide

end CslibFrontierTests.Crypto.MLKEMCorrectness
