/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test client)

public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Family

/-!
# Checked client for the growing HQC support-sampler family

These examples exercise the deliberately small `(n, count) = (3, 2)` schedule. They check the
implemented output's length and weight, the oracle-free online description, and the separate
offline generator and installed-artifact accounting. This is not the published HQC parameter
schedule or an HQC security claim.
-/

public section

namespace CslibFrontierTests.HQCSupportSamplerFamily

open Cslib Cslib.Crypto.HQC Cslib.Quantum Cslib.Probability Cslib.BitString

theorem output_shape (s : ℕ) {out : List Bool}
    (hout : out ∈ (growingSupportSamplerFamily.output s [] (fun _ _ => false)
      (ket (fun _ => false)) (norm_ket _)).support) :
    out.length = 3 ∧ out.count true = 2 := by
  rw [output_growingSupportSamplerFamily] at hout
  obtain ⟨word, hword, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  obtain ⟨S, hS, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hword
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp
    (sampleSupport2_mem_powersetCard (by decide) hS)
  exact ⟨List.length_ofFn, by rw [count_true_ofFn, weight_indicatorVector hsub, hcard]⟩

-- The output constraint is inhabited for every security parameter, not a vacuous implication.
example (s : ℕ) :
    ∃ out ∈ (growingSupportSamplerFamily.output s [] (fun _ _ => false)
      (ket (fun _ => false)) (norm_ket _)).support,
      out.length = 3 ∧ out.count true = 2 := by
  obtain ⟨out, hout⟩ := (growingSupportSamplerFamily.output s [] (fun _ _ => false)
    (ket (fun _ => false)) (norm_ket _)).support_nonempty
  exact ⟨out, hout, output_shape s hout⟩

-- Every generated description is oracle-free and fits its exact online resource record.
example (s ℓ : ℕ) :
    OracleCircuit.Within (growingSupportSamplerDescription s ℓ).instructions
        (growingSupportSamplerDescription s ℓ).width
        (encOracleCircuitDescription (growingSupportSamplerDescription s ℓ)).length
        (growingSupportSamplerCircuitResources s ℓ) ∧
      (growingSupportSamplerDescription s ℓ).instructions.queryCount = 0 :=
  ⟨within_growingSupportSamplerCircuitResources s ℓ,
    queryCount_growingSupportSamplerDescription s ℓ⟩

-- Offline generation is polynomial, while the retained generator and generated program are
-- charged as two distinct exact occurrences.
example :
    ∃ certificate : growingSupportSamplerFamily.GeneratorCertificate,
      UniformOracleCircuitFamily.GeneratorResources.IsPolynomial
          (fun s => certificate.resources ⟨s, 0⟩) ∧
        ∀ s,
          Crypto.Game.InstalledArtifact.installedBits
              (growingSupportSamplerInstalledArtifacts certificate s) .generator =
              (Turing.MultiTapeTM.Universal.eDesc certificate.code).length ∧
            Crypto.Game.InstalledArtifact.installedBits
              (growingSupportSamplerInstalledArtifacts certificate s) .generatedProgram =
              (encOracleCircuitDescription (growingSupportSamplerDescription s 0)).length := by
  obtain ⟨certificate, hpoly⟩ := exists_growingSupportSamplerGenerator
  refine ⟨certificate, hpoly, fun s => ⟨?_, ?_⟩⟩
  · exact installedBits_growingSupportSamplerGenerator certificate s
  · exact installedBits_growingSupportSamplerGeneratedProgram certificate s

end CslibFrontierTests.HQCSupportSamplerFamily
