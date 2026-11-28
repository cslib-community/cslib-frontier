/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LinearSystemPerfect
import CslibFrontier.Computability.PCP.TwoProverGame.Naimark
import CslibFrontier.Computability.PCP.TwoProverGame.Tsirelson
import CslibFrontier.Foundations.Quantum.Naimark
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Polar

/-! # Naimark dilation

Checked clients of the Naimark dilation: an isometry extends to a unitary, the dilation of a POVM
is projective and compresses to it, the dilation of a strategy has the same answers and winning
probability (the optimal CHSH strategy keeps winning with probability `cos²(π/8)`), and perfect
strategies for linear constraint system games give operator solutions in the state with no
assumption on their measurements.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Naimark

open Matrix Cslib Cslib.Quantum Cslib.PCP Cslib.PCP.TwoProverGame
open BitString (signVal)
open scoped Real MatrixOrder ComplexOrder

/-- An isometry extends to a unitary. -/
example {n ι : Type} [Fintype n] [DecidableEq n] [DecidableEq ι] (V : Matrix n ι ℂ)
    (hV : Vᴴ * V = 1) {j : ι → n} (hj : Function.Injective j) :
    ∃ U ∈ unitaryGroup n ℂ, ∀ k i, U k (j i) = V k i :=
  exists_unitary_extension V hV hj

/-- The dilation of a POVM is projective and compresses to it. -/
example {ι A : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] (M : POVM A ι)
    (a₀ a : A) :
    (M.dilate a₀).effect a * (M.dilate a₀).effect a = (M.dilate a₀).effect a ∧
      (ancillaEmbed a₀)ᴴ * (M.dilate a₀).effect a * ancillaEmbed a₀ = M.effect a :=
  ⟨M.dilate_effect_mul_self a₀ a, M.compress_dilate a₀ a⟩

private noncomputable def halfEffect : POVM Bool Unit where
  effect _ := (1 / 2 : ℝ) • (1 : Matrix Unit Unit ℂ)
  posSemidef _ := (PosSemidef.one : (1 : Matrix Unit Unit ℂ).PosSemidef).smul (by norm_num)
  sum_effect := by rw [Fintype.sum_bool, ← add_smul]; norm_num

/-- The fair binary POVM has zero observable. Its dilated observable sends the embedded
one-dimensional register entirely into the complementary ancilla subspace. -/
example :
    let e := ancillaEmbed (ι := Unit) false
    let P := e * eᴴ
    let A := (halfEffect.dilate false).observable
    P * A * e = 0 ∧ (1 - P) * A * e ≠ 0 := by
  intro e P A
  have hc : eᴴ * A * e = 0 := by
    dsimp only [A, POVM.observable]
    rw [Matrix.mul_sub, Matrix.sub_mul,
      halfEffect.compress_dilate false false, halfEffect.compress_dilate false true]
    exact sub_self _
  have hp : P * A * e = 0 := by
    change (e * eᴴ) * A * e = 0
    rw [Matrix.mul_assoc, Matrix.mul_assoc e, ← Matrix.mul_assoc eᴴ A e, hc, Matrix.mul_zero]
  refine ⟨hp, fun hz => ?_⟩
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, hp, sub_zero] at hz
  have hA : A * A = 1 := Measurement.observable_mul_self (halfEffect.isProjective_dilate false)
  have he : e = 0 := by
    have h := congrArg (A * ·) hz
    rwa [← Matrix.mul_assoc, hA, Matrix.one_mul, Matrix.mul_zero] at h
  have h : eᴴ * e = 1 := conjTranspose_ancillaEmbed_mul false
  rw [he, Matrix.mul_zero] at h
  exact zero_ne_one h

/-- The projective dilation of the optimal CHSH strategy is still optimal. -/
example : chsh.quantumWinProb (chshEPR.dilate false false) = Real.cos (π / 8) ^ 2 := by
  rw [quantumWinProb_dilate, quantumWinProb_chsh_chshEPR]

/-- Every strategy has a projective strategy winning with the same probability. -/
example {X Y A B ι κ : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty A] [Nonempty B]
    (G : TwoProverGame X Y A B) (S : QuantumStrategy X Y A B ι κ) :
    ∃ S' : QuantumStrategy X Y A B (ι × A) (κ × B),
      (∀ x, (S'.alice x).toMeasurement.IsProjective) ∧
      (∀ y, (S'.bob y).toMeasurement.IsProjective) ∧ G.quantumWinProb S' = G.quantumWinProb S :=
  ⟨S.dilate (Classical.arbitrary A) (Classical.arbitrary B), S.isProjective_alice_dilate _ _,
    S.isProjective_bob_dilate _ _, G.quantumWinProb_dilate S _ _⟩

open scoped Matrix.Norms.L2Operator in
/-- A perfect strategy for a linear constraint system game gives operator relations in the state:
Bob's observables multiply to `(-1)^{parity}` over each equation. -/
example {V E ι κ : Type} [Fintype V] [DecidableEq V] [Finite E] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (L : LinearSystem V E) {μ : PMF (E × V)}
    (S : QuantumStrategy E V (V → Bool) Bool ι κ) (hne : ∀ e, ∃ v, μ (e, v) ≠ 0)
    (hμ : ∀ e, ∀ v ∈ L.support e, μ (e, v) ≠ 0) (h : (L.game μ).quantumWinProb S = 1) (e : E) :
    ((L.support e).toList.map (S.stateSolution L hne hμ h).op).prod
      ≈[(S.dilate (fun _ => false) false).toCommuting.state; 0] (signVal (L.parity e) : ℂ) • 1 :=
  (S.stateSolution L hne hμ h).prod_eq e _ (List.Perm.refl _)

/-- The one equation `x₀ ⊕ x₁ = 0` on two variables. -/
def evenPair : LinearSystem (Fin 2) Unit where
  support _ := Finset.univ
  parity _ := false

/-- The all-zero assignment satisfies `evenPair`. -/
theorem evenPair_satisfies (e : Unit) : evenPair.Satisfies e (fun _ => false) := by
  cases e
  decide

/-- The uniform question distribution on `evenPair`. -/
noncomputable def evenPairQuestions : PMF (Unit × Fin 2) :=
  Cslib.Probability.PMF.uniformOfFintype (Unit × Fin 2)

theorem evenPairQuestions_ne_zero (q : Unit × Fin 2) : evenPairQuestions q ≠ 0 := by
  simp [evenPairQuestions, Cslib.Probability.PMF.uniformOfFintype_apply]

/-- The deterministic strategy playing the all-zero assignment is a perfect tensor-product
strategy for `evenPair`. -/
theorem quantumWinProb_evenPair :
    (evenPair.game evenPairQuestions).quantumWinProb
      (QuantumStrategy.ofDeterministic (fun _ : Unit => fun _ : Fin 2 => false)
        (fun _ : Fin 2 => false)) = 1 := by
  rw [TwoProverGame.quantumWinProb_ofDeterministic, TwoProverGame.winProb]
  have h : (evenPair.game evenPairQuestions).questions.toOuterMeasure
      {q | (evenPair.game evenPairQuestions).accepts q.1 q.2 (fun _ => false) false} = 1 := by
    refine (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr fun q _ => ?_
    exact ⟨evenPair_satisfies q.1, fun _ => rfl⟩
  rw [h, ENNReal.toReal_one]

open scoped Matrix.Norms.L2Operator in
/-- **Concrete client.** Naimark dilation turns the perfect deterministic strategy for `evenPair`
into a state-dependent operator solution; the product of Bob's observables over the equation is
`1` in the dilated state. -/
example :
    let S := QuantumStrategy.ofDeterministic (fun _ : Unit => fun _ : Fin 2 => false)
      (fun _ : Fin 2 => false)
    let Z := S.stateSolution evenPair (fun _ => ⟨0, evenPairQuestions_ne_zero _⟩)
      (fun _ _ _ => evenPairQuestions_ne_zero _) quantumWinProb_evenPair
    ((evenPair.support ()).toList.map Z.op).prod
      ≈[(S.dilate (fun _ => false) false).toCommuting.state; 0] (1 : ℂ) • 1 := by
  intro S Z
  simpa [evenPair] using Z.prod_eq () _ (List.Perm.refl _)

end CslibFrontierTests.Naimark
