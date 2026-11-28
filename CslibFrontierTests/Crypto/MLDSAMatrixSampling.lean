/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.MLDSA.MatrixSampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-! # Resource and statistical bounds on the auxiliary ML-DSA matrix tape -/

set_option linter.privateModule false

open Cslib Cslib.Probability Cslib.Crypto.MLDSA.FIPS204 Cslib.OracleComp Turing.MultiTapeTM
open scoped Cslib.Probability.PMF

-- A nontrivial runtime sampler, with both dimensions of its resource budget supplied as input.
example (s : Level) : IsPPTOn (encPair encUnary encUnary) (encList (MatrixOracle.encPublicMatrix s))
    (fun p : ℕ × ℕ => List.ofFn <$> replicateFin p.1 (MatrixOracle.sampleMatrixFair s p.2)) :=
  MatrixOracle.isPPTOn_matrixTapeFair s (ComputableInPolyTime.fst _ _)
    (ComputableInPolyTime.snd _ _)

-- The cost certificate rules out every nonbinary random choice on every path.
example (s : Level) (Q R : ℕ) :
    (replicateFin Q (MatrixOracle.sampleMatrixFair s R)).QueriesSatisfy (· = 1) := by
  unfold QueriesSatisfy
  apply (MatrixOracle.cost_matrixTapeFair_le s Q R _).mono
  simp

-- Even at the largest level, sixteen attempts per coefficient suffice for a million-query tape.
example : dist (ProbComp.eval (replicateFin (2 ^ 20) (MatrixOracle.sampleMatrixFair .mlDSA87 16)))
    (PMF.uniformOfFintype (Fin (2 ^ 20) → PublicMatrix .mlDSA87)) ≤ (2 : ℝ)⁻¹ ^ 126 := by
  apply (MatrixOracle.dist_matrixTapeFair_le .mlDSA87 (2 ^ 20) 16).trans
  norm_num [Level.params, Cslib.Crypto.MLDSA.Params.mldsa87]

example : (Level.mlDSA44.params.k * Level.mlDSA44.params.ℓ * 256,
    Level.mlDSA65.params.k * Level.mlDSA65.params.ℓ * 256,
    Level.mlDSA87.params.k * Level.mlDSA87.params.ℓ * 256) = (4096, 7680, 14336) := by decide
