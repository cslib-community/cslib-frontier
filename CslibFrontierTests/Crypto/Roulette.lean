/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Encryption.Roulette
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Probability.PMF.Expect

/-!
# Internet roulette tests

Asymptotic clients of `CslibFrontier.Crypto.Computational.Encryption.Roulette`:
uniform strict PPT clients of `DEMOneTimeKeyINDCPAOf.negligible_rouletteDEMAdvantage`, and a
counterexample showing that challenge admissibility on `(r, 0)` pairs cannot be dropped.
-/

namespace CslibFrontierTests.Crypto.Roulette

open Cslib Cslib.Crypto Cslib.Crypto.Encryption Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

section AsymptoticClients

/-- A constant-bet PPT adversary has negligible DEM Internet roulette advantage. -/
example {encIndex : Fin 37 ↪ List Bool} {encBet : RouletteBet ↪ List Bool}
    {keyLen : ℕ → ℕ} {encryptSym : ℕ → List Bool → Fin 37 → ProbComp (List Bool)}
    (hdem : DEMOneTimeKeyINDCPAOf encIndex keyLen encryptSym) :
    Negligible (rouletteDEMAdvantage keyLen encryptSym fun _ _ => pure .high) := by
  have hA : Probability.IsPPT encBet fun _ _ => pure RouletteBet.high :=
    (ComputableInPolyTime.const (encIn := encBits) (encOut := encBet) RouletteBet.high).isPPT
  exact hdem.negligible_rouletteDEMAdvantage hA

/-- A ciphertext-reading PPT adversary has negligible DEM Internet roulette advantage. -/
example {encIndex : Fin 37 ↪ List Bool} {encBet : RouletteBet ↪ List Bool}
    {keyLen : ℕ → ℕ} {encryptSym : ℕ → List Bool → Fin 37 → ProbComp (List Bool)}
    (hdem : DEMOneTimeKeyINDCPAOf encIndex keyLen encryptSym) :
    Negligible (rouletteDEMAdvantage keyLen encryptSym fun _ ct =>
      pure (if ct.getD 0 false then .high else .low)) := by
  let chooseBet : List Bool → RouletteBet := fun ct => if ct.getD 0 false then .high else .low
  have hbit : ComputableInPolyTime (fun ct : List Bool => ct.getD 0 false) encBits encBool :=
    ComputableInPolyTime.bitsGetDWithInput .id' (.const 0) false
  have hmap : ComputableInPolyTime (fun b : Bool => if b then RouletteBet.high else .low)
      encBool encBet :=
    ComputableInPolyTime.of_finite _
  have hA : Probability.IsPPT encBet fun _ ct => pure (chooseBet ct) :=
    (hmap.comp hbit).isPPT
  exact hdem.negligible_rouletteDEMAdvantage hA

end AsymptoticClients

section Counterexamples

/-- Necessity of admitting `(r, 0)` pairs: for a transparent cipher and an admissibility predicate
requiring equal challenge messages (`decide (m₀ = m₁)`, which rejects `(1, 0)`), the
semantic-security reduction's advantage is `0` while the concrete Internet roulette advantage is
`18 / 37`. -/
example :
    ∃ (E : Cipher Unit (Fin 37) (Fin 37)) (sampleKey : ProbComp Unit)
      (valid : Fin 37 → Fin 37 → Bool) (A : Fin 37 → ProbComp RouletteBet),
      rouletteAdvantage E sampleKey A = (18 : ℝ≥0) / 37 ∧
        Experiment.advantage
          (E.oneTimeExperiment sampleKey valid
            (rouletteReduction (ProbComp.uniform (Fin 37)) A) false)
          (E.oneTimeExperiment sampleKey valid
            (rouletteReduction (ProbComp.uniform (Fin 37)) A) true) = 0 := by
  let E : Cipher Unit (Fin 37) (Fin 37) := ⟨fun _ r => pure r, fun _ c => pure c⟩
  let sampleKey : ProbComp Unit := pure ()
  let valid : Fin 37 → Fin 37 → Bool := fun m₀ m₁ => decide (m₀ = m₁)
  let betOf : Fin 37 → RouletteBet := fun r => if 19 ≤ r.val then .high else .low
  let A : Fin 37 → ProbComp RouletteBet := fun c => pure (betOf c)
  refine ⟨E, sampleKey, valid, A, ?_, ?_⟩
  · have hwin : ∀ r : Fin 37, rouletteWin r (betOf r) = decide (r.val ≠ 0) := by
      intro r
      fin_cases r <;> decide
    have hcard : ({r : Fin 37 | decide (r.val ≠ 0) = true} : Finset (Fin 37)).card = 36 := by
      decide
    have hprob : Pr[rouletteExperiment E sampleKey A] = 36 / 37 := by
      have heval : ProbComp.eval (rouletteExperiment E sampleKey A) =
          (PMF.uniformOfFintype (Fin 37)).map fun r => decide (r.val ≠ 0) := by
        simp only [rouletteExperiment, E, sampleKey, A, ProbComp.eval_bind, ProbComp.eval_uniform,
          ProbComp.eval_pure, PMF.pure_bind, hwin]
        rfl
      change ((ProbComp.eval (rouletteExperiment E sampleKey A)) true).toReal = 36 / 37
      rw [heval, Probability.PMF.toReal_uniformOfFintype_map_apply_true,
        Finset.dens_eq_card_div_card, hcard, Fintype.card_fin]
      norm_num
    apply NNReal.eq
    rw [rouletteAdvantage, coe_nndist, Real.dist_eq, hprob]
    norm_num
  · have heval_eq :
        ProbComp.eval (E.oneTimeExperiment sampleKey valid
            (rouletteReduction (ProbComp.uniform (Fin 37)) A) false) =
          ProbComp.eval (E.oneTimeExperiment sampleKey valid
            (rouletteReduction (ProbComp.uniform (Fin 37)) A) true) := by
      simp only [Cipher.oneTimeExperiment, lrExperiment, rouletteReduction, E, sampleKey, valid,
        A, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.pure_bind]
      congr 1; funext r
      by_cases hr : r.1.msg₀ = r.1.msg₁ <;> simp [hr]
    simp [Experiment.advantage, heval_eq]

end Counterexamples

end CslibFrontierTests.Crypto.Roulette
