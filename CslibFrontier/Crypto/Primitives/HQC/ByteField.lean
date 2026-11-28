/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField.Native

/-!
# The HQC byte-field generator

HQC v5.1 uses the polynomial-basis field modulo
`X⁸ + X⁴ + X³ + X + 1` and takes the byte `0x03` as its generator
[HQC2026, §2.1, pp. 6–7; Table 2, p. 9]. The modulus is specified on p. 6, the
least-significant-coefficient-first byte mapping on p. 7, and `α = 0x03` in Table 2 on p. 9.
`Cslib.GF256` uses exactly these conventions.

This module defines the source generator as `X + 1` in `Cslib.BinaryField 8`. The theorem
`rawByte_hqcAlpha` is its first semantic property: the shared executable byte layer represents
that element by raw byte `0x03`. The order-255 proof belongs to the shortened Reed–Solomon
development that uses the generator; it is not asserted here.

## Main definitions

* `Cslib.Crypto.HQC.hqcAlpha`: the source element `X + 1`.

## Main results

* `Cslib.Crypto.HQC.rawByte_hqcAlpha`: the executable representation of `hqcAlpha` is `0x03`.

## References

* [HQC specification, version 5.1][HQC2026], §2.1, pp. 6–7; Table 2, p. 9.
-/

public section

namespace Cslib.Crypto.HQC

open Polynomial

/-- The HQC source generator `α = X + 1` in its degree-eight binary field. -/
noncomputable def hqcAlpha : BinaryField 8 :=
  AdjoinRoot.root (leastIrreducible 8) + 1

/-- The shared executable byte representation of the HQC generator is raw byte `0x03`. -/
theorem rawByte_hqcAlpha :
    GF256.equivBinaryField hqcAlpha = ⟨0x03, by norm_num⟩ := by
  have halpha : hqcAlpha =
      AdjoinRoot.mk (leastIrreducible 8) (polyOfCode 0x03) := by
    rw [hqcAlpha, polyOfCode_three, map_add, map_one, AdjoinRoot.mk_X, add_comm]
  rw [halpha]
  apply Fin.ext
  simpa only [GF256.equivBinaryField] using
    BinaryField.val_equivFin_mk_polyOfCode (w := 8) (c := 0x03) (by norm_num) (by norm_num)

end Cslib.Crypto.HQC
