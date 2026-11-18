/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.MLDSA.QuantumCommitmentRegister

/-!
# ML-DSA digest-register clients

Check a nonconstant little-endian digest and compose two coherent reads past the digest.
-/

open Cslib Cslib.Crypto Cslib.Crypto.MLDSA.FIPS204 Cslib.Quantum Cslib.Probability

example : Level.mlDSA44.commitmentInputBits = 6656 ∧
    Level.mlDSA65.commitmentInputBits = 6656 ∧ Level.mlDSA87.commitmentInputBits = 8704 := by
  decide

-- A digest with only bit 8 set tests the byte boundary at the raw commitment address.
example (H : Xofs) (s : Level) (w : Fin s.params.k → Fin 256 → ℤ) (μ : BitString 512) :
    let D := fun (_ : BitString s.commitmentInputBits) (j : Fin (8 * digestBytes s)) =>
      decide (j.val = 8)
    Keccak.bytesToBitsLE ((H.withDigestRegister s D).commitmentDigest s w (List.ofFn μ)) =
      List.ofFn (fun j : Fin (8 * digestBytes s) => decide (j.val = 8)) :=
  H.commitmentDigest_withDigestRegister s _ w List.length_ofFn

-- The ML-DSA-44 device XORs 33 bytes, one past the installed digest. Two different wire
-- placements share the same clean scratch registers on an arbitrary initial superposition.
example (H : Xofs) (D : BitString Level.mlDSA44.commitmentInputBits → BitString 256)
    {m : ℕ} (p q : Fin (6656 + 2 + 8 * 33) ↪ Fin m) (ψ : Qubits m) :
    let native := (H.withDigestRegister .mlDSA44 D).queryTable 6656 33
    let run := fun wires state => runValue addStep
      (lookupXorSteps wires (Xofs.digestLookup .mlDSA44) (H.digestResponse .mlDSA44 6656 33))
      state D 2
    run q (run p (cleanLookupState ψ)) =
      cleanLookupState ((xorQuery native q).eval ((xorQuery native p).eval ψ)) := by
  intro native run
  exact (congrArg (run q ·) (H.xorQuery_withDigestRegister .mlDSA44 D 6656 33 m p ψ)).trans
    (H.xorQuery_withDigestRegister .mlDSA44 D 6656 33 m q ((xorQuery native p).eval ψ))
