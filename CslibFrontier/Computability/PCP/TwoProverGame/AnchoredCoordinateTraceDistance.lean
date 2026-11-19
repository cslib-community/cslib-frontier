/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.AnchoredCoordinateInformation
public import CslibFrontier.Foundations.Quantum.DensityMatrix.ClassicalQuantumPinsker

/-!
# Conditional trace deviations after anchored wins

In the original winning transcript, revealing one more unchecked question changes the other
player's reduced state by a small squared trace norm on average. Quantum Pinsker's inequality
gives the summed form of the intermediate estimate in
[Bavarian, Vidick and Yuen, equation (43)][BavarianVidickYuen2022]
(arXiv:1509.07466v2, §5.2, printed p. 25) and its counterpart with the players exchanged.
The bound uses the full trace norm and natural logarithms. The sums also admit an empty
unchecked set.
-/

public section

namespace Cslib.PCP.AnchoredDependency

open Quantum Matrix
open ParallelRepetition (Revealed)
open scoped unitInterval

variable {X Y A B ι κ : Type*} {n m : ℕ}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (G : TwoProverGame X Y A B) (α : I) (C : Finset (Fin n))

local notation "Free" => {i : Fin n // i ∉ C}
local notation "Info" => Revealed (Option X) (Option Y) C
local notation "Answer" => ((C → A) × (C → B))
local notation "RepeatedStrategy" => QuantumStrategy (Fin n → Option X) (Fin n → Option Y)
  (Fin n → A) (Fin n → B) ι κ

/-- Alice's squared trace deviation, averaged over the winning transcript and the
revealed Bob question and summed over the unchecked coordinates. -/
theorem exists_alice_sum_conditionalTraceNormSq_le_after_wins [DecidableEq Y] [Nonempty A]
    [Nonempty B] (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support) :
    let P := ((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
      (bobTranscriptProjection C e)
    ∃ ρ : (Info × Answer) × (Fin m → Option Y) → Matrix ι ι ℂ,
      (∀ z, IsDensityMatrix (ρ z)) ∧
      (∀ (t : Info) (a : C → A) (b : C → B) (y : Fin m → Option Y),
        ((t, a, b), y) ∈ P.support →
        ρ ((t, a, b), y) = normalizeDensity (partialTraceRight (pureState
          (S.averagedCheckedVector C (aliceQuestionsGivenInfo G α C t)
            (PMF.pure (completeBobQuestions C e t y)) a b)))) ∧
      sumConditionalTraceNormSq P ρ ≤
        2 * (Real.log (Fintype.card Answer) -
          Real.log ((transcriptLaw G α C S).toOuterMeasure (winsOnChecked G α C)).toReal) := by
  classical
  obtain ⟨ρ, hρ, hbranch, hbound⟩ :=
    exists_anchored_coordinateInformation_le_after_wins G α C S e hs
  exact ⟨ρ, hρ, hbranch, sumConditionalTraceNormSq_le_of_information_bound _ hρ hbound⟩

/-- Bob's squared trace deviation, averaged over the winning transcript and the
revealed Alice question and summed over the unchecked coordinates. -/
theorem exists_bob_sum_conditionalTraceNormSq_le_after_wins [DecidableEq X] [Nonempty A]
    [Nonempty B] (S : RepeatedStrategy) (e : Fin m ≃ Free)
    (hs : ∃ z ∈ winsOnChecked G α C, z ∈ (transcriptLaw G α C S).support) :
    let P := ((transcriptLaw G α C S).filter (winsOnChecked G α C) hs).map
      (aliceTranscriptProjection C e)
    ∃ ρ : (Info × Answer) × (Fin m → Option X) → Matrix κ κ ℂ,
      (∀ z, IsDensityMatrix (ρ z)) ∧
      (∀ (t : Info) (a : C → A) (b : C → B) (x : Fin m → Option X),
        ((t, a, b), x) ∈ P.support →
        ρ ((t, a, b), x) = normalizeDensity (partialTraceLeft (pureState
          (S.averagedCheckedVector C (PMF.pure (completeAliceQuestions C e t x))
            (bobQuestionsGivenInfo G α C t) a b)))) ∧
      sumConditionalTraceNormSq P ρ ≤
        2 * (Real.log (Fintype.card Answer) -
          Real.log ((transcriptLaw G α C S).toOuterMeasure (winsOnChecked G α C)).toReal) := by
  classical
  obtain ⟨ρ, hρ, hbranch, hbound⟩ :=
    exists_bob_anchored_coordinateInformation_le_after_wins G α C S e hs
  exact ⟨ρ, hρ, hbranch, sumConditionalTraceNormSq_le_of_information_bound _ hρ hbound⟩

end Cslib.PCP.AnchoredDependency
