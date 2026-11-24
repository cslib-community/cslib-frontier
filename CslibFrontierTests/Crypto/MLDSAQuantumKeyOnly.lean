/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.MLDSA.QuantumKeyOnly
-- `import all` reads `Keccak.fixedBytesEquivBitsLE`'s unexposed body so `decide` can evaluate both
-- directions of the `[128, 1]` byte-boundary check.
import all CslibFrontier.Crypto.Primitives.Hash.Keccak

/-! Byte-register conventions for the coherent ML-DSA key-only verifier. -/

set_option linter.privateModule false

open Cslib Cslib.Crypto Cslib.Crypto.MLDSA.FIPS204
open Cslib.Crypto.MLDSA.FIPS204.QuantumKeyOnly
open Cslib.Probability

-- FIPS 204, Table 1 and Algorithm 28. The address is μ followed by w₁Encode.
example : [Level.mlDSA44, .mlDSA65, .mlDSA87].map Level.commitmentInputBits =
    [6656, 6656, 8704] := by decide

-- Both byte positions and bit significance matter to coherent XOR queries (both directions).
example : ((Keccak.fixedBytesEquivBitsLE 2).symm
    (fun i => decide (i.val = 7 ∨ i.val = 8))).toList = [128, 1] := by decide

example : List.ofFn (Keccak.fixedBytesEquivBitsLE 2 ![128, 1]) =
    List.ofFn (fun i : Fin 16 => decide (i.val = 7 ∨ i.val = 8)) := by decide

-- Ordinary-import client checks for the public grid-table law and SHAKE256 verifier bridge.
example (s : Level) :
    (PMF.uniformOfFintype (DigestTable s)).map
      (fun (H : DigestTable s) (p : SharedDigest.GridPoint s) =>
        expandDigest s (pointReply s H (List.ofFn p.1, p.2.val))) =
      PMF.pi (fun _ : SharedDigest.GridPoint s =>
        (PMF.uniformOfFintype (FixedBytes (digestBytes s))).map (expandDigest s)) :=
  expanded_grid_table_law s

example (s : Level) (bytes : List Byte) (A : PublicMatrix s) (f : Forgery) :
    OracleComp.interpret (m := Id) (pointReply s (Xofs.shake.readDigestRegister s))
      (SharedDigest.verify s bytes A f) = true ↔
      verifyWithExpansion s (fun _ => some A) bytes f.message f.context f.signature =
        some true :=
  verify_readDigestRegister_iff s bytes A f
