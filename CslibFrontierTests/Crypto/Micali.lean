/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Kilian.Micali
import CslibFrontierTests.Crypto.MerkleTestHash

/-!
# Tests for Micali's computationally sound proofs in the random oracle model

1. **Oracle-program Merkle tree.** On a two-leaf tree under a sixteen-bit hash, `merkleRootProg`,
   `merklePathProg` and `merkleVerifyProg` agree with `merkleRoot`, `merklePath` and `merkleVerify`
   under `OracleComp.evalPure`, accept valid leaf openings
   (`evalPure_merkleVerifyProg_merklePathProg`, `merkleVerifyProg_merklePathProg`), and reject
   flipped leaf bits, wrong-length paths, labels that are not digests, and out-of-range indices.
2. **Micali prover and verifier.** On the one-bit, two-address toy PCP verifier of
   `CslibFrontierTests/Crypto/Kilian.lean`, `micaliProve` and `micaliVerify` accept the witness
   table
   `[true, true]` (and padded `[true, true, false]`) under deterministic evaluation and in the lazy
   random oracle experiment `micaliHonestGame` at every digest length `σ` and repetition count `m`
   (`micaliHonestGame_eq_pure_true`), while rejecting tampered roots, flipped opened bits,
   malformed paths, missing repetitions, and commitments to a rejected table `[true, false]`.
-/

namespace CslibFrontierTests.Crypto.Micali

open Cslib Cslib.Complexity Cslib.Crypto
open CslibFrontierTests.Crypto.MerkleTestHash

/-- A deterministic Merkle hash with sixteen-bit digests. -/
abbrev pHash : List Bool → List Bool := polyHash

/-- Two one-bit leaves. -/
abbrev leaves : List (List Bool) := [[true], [false]]

-- Oracle-program Merkle root and paths agree with pure `merkleRoot` and `merklePath`.
example : OracleComp.evalPure pHash (merkleRootProg leaves) =
    merkleRoot (fun _ => pHash) [] leaves := rfl

example : OracleComp.evalPure pHash (merklePathProg leaves 0) = [pHash [false]] := by
  decide +kernel
example : OracleComp.evalPure pHash (merklePathProg leaves 1) = [pHash [true]] := by
  decide +kernel

-- Valid openings are accepted under both pure evaluation and the lazy random oracle.
example : OracleComp.evalPure pHash (do
    let root ← merkleRootProg leaves
    let path ← merklePathProg leaves 0
    merkleVerifyProg 1 root 0 [true] path) = true :=
  evalPure_merkleVerifyProg_merklePathProg pHash length_polyHash leaves (by decide)

example (σ : ℕ) :
    (OracleComp.runWith (RandomOracle.answer fun _ => BitString.uniformList σ) (do
      let root ← merkleRootProg leaves
      let path ← merklePathProg leaves 1
      merkleVerifyProg 1 root 1 [false] path) (fun _ => none)).map Prod.fst = PMF.pure true :=
  merkleVerifyProg_merklePathProg _
    (fun _ _ ha => BitString.length_of_mem_support_uniformList ha) leaves (by decide)

-- Flipping the leaf bit, giving a path of the wrong length, using an out-of-range index, or giving
-- a label that is not a sixteen-bit digest is rejected by `merkleVerifyProg`.
example : OracleComp.evalPure pHash (do
    let root ← merkleRootProg leaves
    let path ← merklePathProg leaves 0
    merkleVerifyProg 1 root 0 [false] path) = false := by decide +kernel

example : OracleComp.evalPure pHash (do
    let root ← merkleRootProg leaves
    merkleVerifyProg 1 root 0 [true] []) = false := by decide +kernel

example : OracleComp.evalPure pHash (do
    let root ← merkleRootProg leaves
    let path ← merklePathProg leaves 0
    merkleVerifyProg 1 root 2 [true] path) = false := by decide +kernel

example : OracleComp.evalPure pHash (do
    let root ← merkleRootProg leaves
    merkleVerifyProg 1 root 1 [false] [[true]]) = false := by decide +kernel

/-- A toy PCP verifier: one random bit chooses the address `1000` or `5`, and the bit read must be
`true`. -/
def toyVerifier : PCPVerifier (List Bool) where
  coins _ := 1
  queries := fun (_, ρ) => [if ρ.headD false then 5 else 1000]
  verdict := fun (_, answers) => answers == [true]

/-- The statement. -/
abbrev x : List Bool := [true, false]

/-- Deterministic Fiat–Shamir oracle returning both one-bit challenges `[[false], [true]]`. -/
def fixedFS : List Bool × List Bool → List (List Bool) := fun _ => [[false], [true]]

/-- Deterministic combined oracle `(pHash, fixedFS)`. -/
abbrev toyOracle := micaliOracle pHash fixedFS

/-- Honest Micali proof on the witness table `[true, true]`. -/
abbrev honestProof : MicaliProof :=
  micaliProvePure pHash fixedFS toyVerifier x [true, true]

-- The `OracleComp` Micali prover and verifier agree with their pure counterparts.
example : OracleComp.evalPure toyOracle (micaliProve toyVerifier x [true, true]) =
    honestProof := rfl

example : OracleComp.evalPure toyOracle (micaliVerify toyVerifier x honestProof) = true := by
  decide +kernel

-- Completeness theorems apply to any accepted table, including `[true, true, false]`.
example : micaliVerifyPure pHash fixedFS toyVerifier x
    (micaliProvePure pHash fixedFS toyVerifier x [true, true, false]) = true :=
  micaliVerifyPure_micaliProvePure_eq_true length_polyHash (by decide) (by decide +kernel)

example : OracleComp.evalPure toyOracle (do
    let proof ← micaliProve toyVerifier x [true, true, false]
    micaliVerify toyVerifier x proof) = true :=
  micaliVerify_micaliProve_eq_true length_polyHash (by decide) (by decide +kernel)

-- Tampering with the root, flipping an opened bit, giving a wrong-length Merkle path, or dropping
-- a repetition causes `micaliVerify` to reject.
example : OracleComp.evalPure toyOracle
    (micaliVerify toyVerifier x ⟨[], honestProof.response⟩) = false := by decide +kernel

example : OracleComp.evalPure toyOracle
    (micaliVerify toyVerifier x
      ⟨honestProof.root,
        [honestProof.response.getD 0 [],
         [⟨false, ((honestProof.response.getD 1 []).getD 0 ⟨false, []⟩).path⟩]]⟩) = false := by
  decide +kernel

example : OracleComp.evalPure toyOracle
    (micaliVerify toyVerifier x
      ⟨honestProof.root, [honestProof.response.getD 0 [], [⟨true, []⟩]]⟩) = false := by
  decide +kernel

example : OracleComp.evalPure toyOracle
    (micaliVerify toyVerifier x
      ⟨honestProof.root, [honestProof.response.getD 0 []]⟩) = false := by
  decide +kernel

-- Committing honestly to a table `[true, false]` that the PCP verifier rejects is rejected when
-- the Fiat–Shamir oracle includes the challenge `[true]` that inspects the `false` entry.
example : OracleComp.evalPure toyOracle (do
    let proof ← micaliProve toyVerifier x [true, false]
    micaliVerify toyVerifier x proof) = false := by decide +kernel

-- Perfect completeness in the random oracle model at every digest length `σ` and repetition
-- count `m`.
example (σ m : ℕ) :
    micaliHonestGame toyVerifier x [true, true] σ m = PMF.pure true :=
  micaliHonestGame_eq_pure_true toyVerifier (by decide) σ m

end CslibFrontierTests.Crypto.Micali
