/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.SplitMatrix

/-!
# Adaptive signing with the FIPS 204 challenge expander

The digest oracle returns uniform strings of the prescribed byte length. [NISTFIPS204],
Algorithm 29, expands each digest using SHAKE256. The two loop limits are the minimum
permitted by Appendix C, Table 3, for bounded implementations. An expansion error
ends its signing call, while a rejected response consumes one of the 814 ideal-mask trials.
The public simulator preserves both kinds of failure. The matrix is uniform and the caller
chooses the adaptive signing and digest-query program after receiving the full public key.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.OracleComp Cslib.Probability Cslib.Crypto.Protocols.ROMSignature

/-- The adaptive ROM signing hop for each FIPS parameter set, using the actual bounded SHAKE256
challenge expansion. A fatal expansion stops its call. A response rejection uses one attempt.
The experiments use independent ideal masks and share a uniform matrix with the forger.
The per-pair loss comes from the rounded commitment count over that matrix law. -/
theorem closeTo_simulateSigning_sampleInBall (s : Level)
    (s₁ : Fin s.params.ℓ → Poly) (s₂ : Fin s.params.k → Poly)
    (hs₁ : ∀ i j, |(s₁ i j).valMinAbs| ≤ s.params.η)
    (hs₂ : ∀ i j, |(s₂ i j).valMinAbs| ≤ s.params.η) {α : Type}
    (forger : PublicKey s.params →
      OracleComp (SigningROMSpec s.params (FixedBytes (digestBytes s))) α)
    {S H : ℕ} (hS : ∀ pk, IsCostBounded signingCost (forger pk) S)
    (hH : ∀ pk, IsCostBounded hashCost (forger pk) H) :
    let dist := PMF.uniformOfFintype (FixedBytes (digestBytes s))
    let expand := fun c : FixedBytes (digestBytes s) => sampleInBall s c.toList
    CloseTo ((PMF.uniformOfFintype _).bind fun A =>
      let sk : SecretKey s.params := ⟨A, s₁, s₂⟩
      (runPartialSigningROM s.params 13 (hintLimit s) 814 (by cases s <;> decide)
        dist expand sk (forger sk.publicKey)).map Prod.fst)
      ((PMF.uniformOfFintype _).bind fun A =>
        let pk := (SecretKey.mk A s₁ s₂ : SecretKey s.params).publicKey
        (simulatePartialSigningROM s.params 13 (hintLimit s) 814 (by cases s <;> decide)
          dist expand pk (forger pk)).map Prod.fst)
      ((2 * (S * 814) * H + (S * 814).choose 2 : ℕ) * ENNReal.ofReal
        ((11 / 10) / Real.sqrt (2 ^ s.commitmentBoxBits))) := by
  intro dist expand
  have hp : s.params.Valid := by
    cases s
    · exact Params.valid_mldsa44
    · exact Params.valid_mldsa65
    · exact Params.valid_mldsa87
  have hq : 2 * s.params.γ₁ < s.params.q := by cases s <;> decide
  apply closeTo_uniformMatrix_of_guessProbability s
  intro A
  exact closeTo_partialSigningROM s.params hp hq (by cases s <;> decide) 13 (hintLimit s) 814
    dist expand ⟨A, s₁, s₂⟩ hs₁ hs₂ (fun _ _ hc => inBall_of_sampleInBall hc) (hS _) (hH _)

end Cslib.Crypto.MLDSA.FIPS204
