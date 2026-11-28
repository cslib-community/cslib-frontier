/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Primitives.HQC.ByteField

/-! Known-answer checks for the shared executable GF(256) byte layer and its HQC client. -/

namespace CslibFrontierTests.HQCByteField

open Cslib Cslib.Crypto.HQC

private def rawAlpha : GF256.Byte := ⟨0x03, by norm_num⟩

private theorem field_rawAlpha : GF256.field rawAlpha = hqcAlpha := by
  rw [GF256.field, Equiv.symm_apply_eq]
  simpa [rawAlpha] using rawByte_hqcAlpha.symm

-- A known polynomial-basis product for modulus `0x11b`.
example : GF256.mul (⟨0x57, by norm_num⟩, ⟨0x83, by norm_num⟩) =
    ⟨0xc1, by norm_num⟩ := by decide

-- Addition is bytewise XOR in the same basis.
example :
    let input : GF256.Byte × GF256.Byte :=
      (⟨0x57, by norm_num⟩, ⟨0x83, by norm_num⟩)
    GF256.Native.addCompiler.table.toTM.ComputesTidilyInTimeAndSpace
        (GF256.pairEncoding input) (GF256.encoding (GF256.add input)) 41 0 ∧
      GF256.add input = ⟨0xd4, by norm_num⟩ := by
  dsimp only
  exact ⟨GF256.Native.addCompiler.computes _, by decide⟩

-- The retained inversion machine computes the field inverse of HQC's raw generator byte.
example :
    GF256.Native.invCompiler.table.toTM.ComputesTidilyInTimeAndSpace
        (GF256.encoding rawAlpha) (GF256.encoding (GF256.inv rawAlpha))
        25 0 ∧
      GF256.field (GF256.inv rawAlpha) = hqcAlpha⁻¹ := by
  have hresources := GF256.Native.invCompiler_resourceBounds.1 rawAlpha
  refine ⟨?_, ?_⟩
  · simpa only [hresources.1, hresources.2] using GF256.Native.invCompiler.computes rawAlpha
  rw [GF256.field_inv, field_rawAlpha]

-- The retained streaming machine computes every power of the same HQC generator byte.
example (exponent : ℕ) :
    GF256.Native.powCompiler.table.toTM.ComputesTidilyInTimeAndSpace
        (GF256.powEncoding (rawAlpha, exponent))
        (GF256.encoding (GF256.pow (rawAlpha, exponent)))
        (2 * (GF256.powEncoding (rawAlpha, exponent)).length + 10) 0 ∧
      GF256.field (GF256.pow (rawAlpha, exponent)) = hqcAlpha ^ exponent := by
  have hresources := GF256.Native.powCompiler_resourceBounds.1 (rawAlpha, exponent)
  refine ⟨?_, ?_⟩
  · simpa only [hresources.1, hresources.2] using
      GF256.Native.powCompiler.computes (rawAlpha, exponent)
  rw [GF256.field_pow, field_rawAlpha]

end CslibFrontierTests.HQCByteField
