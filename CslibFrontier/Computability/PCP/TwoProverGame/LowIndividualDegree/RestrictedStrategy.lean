/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.Slices
public import CslibFrontier.Foundations.Quantum.Algebra.CStar

/-!
# Strategies restricted to a last-coordinate slice

Pull back each player's questions to the slice and coarse-grain the outcomes of each
measurement by restricting the line answers. This leaves the state unchanged and preserves
projectivity. We bound the three average branch losses at fixed axis and diagonal degree
bounds, in the setting of [Ji, Natarajan, Vidick, Wright and Yuen, Lemma 6.6]
[JNVWY2020LowIndividualDegree]. For the upper-dimensional Figure 2 test the diagonal bound
is the upper dimension times the axis bound. The slice verifier uses that same diagonal bound.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Cslib.Probability.PMF (uniformOfFintype)

variable {F 𝒜 : Type*} {m : ℕ} [Field F] [Fintype F] [DecidableEq F]

section Ring

variable [Ring 𝒜] [PartialOrder 𝒜] [IsOrderedAddMonoid 𝒜] [Algebra ℂ 𝒜]

/-- The strategy on a slice uses the original measurements on the lifted questions and
restricts each player's answer separately. -/
noncomputable def restrictStrategy (x : F)
    (S : CommutingStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) 𝒜) :
    CommutingStrategy (Question F m) (Question F m) (Answer F m) (Answer F m) 𝒜 :=
  S.relabel (appendQuestion x) (appendQuestion x) (restrictAnswer x) (restrictAnswer x)

/-- Restricting the questions and answers leaves the shared state unchanged. -/
theorem restrictStrategy_state (x : F)
    (S : CommutingStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) 𝒜) :
    (restrictStrategy x S).state = S.state := by
  unfold restrictStrategy CommutingStrategy.relabel
  rfl

end Ring

section CStar

variable [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- Restricting a strategy with projective measurements preserves projectivity for both players. -/
theorem restrictStrategy_isProjective (x : F)
    (S : CommutingStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) 𝒜)
    (hA : ∀ q, (S.alice q).IsProjective) (hB : ∀ q, (S.bob q).IsProjective) :
    (∀ q, ((restrictStrategy x S).alice q).IsProjective) ∧
      (∀ q, ((restrictStrategy x S).bob q).IsProjective) := by
  let _ : DecidableEq (Answer F m) := Classical.decEq _
  unfold restrictStrategy CommutingStrategy.relabel
  constructor
  · intro q
    exact (hA (appendQuestion x q)).map (restrictAnswer x)
  · intro q
    exact (hB (appendQuestion x q)).map (restrictAnswer x)

end CStar

section CFC

variable [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜] [Algebra ℂ 𝒜]
  [TopologicalSpace 𝒜] [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint]
  [NonnegSpectrumClass ℝ 𝒜] [IsOrderedAddMonoid 𝒜]

theorem restrictStrategy_answers (x : F)
    (S : CommutingStrategy (Question F (m + 1)) (Question F (m + 1))
      (Answer F (m + 1)) (Answer F (m + 1)) 𝒜) :
    (restrictStrategy x S).answers = restrictAnswerLaw x S.answers := by
  funext q₁ q₂
  unfold restrictStrategy restrictAnswerLaw
  exact S.answers_relabel _ _ _ _ q₁ q₂

/-- The slice strategies have average consistency loss at most the original consistency
loss. Their average axis and diagonal losses are at most `(n + 2) / (n + 1)` times the
respective original losses, with both degree caps fixed. -/
theorem commutingBranchLoss_restrict_le (n d D : ℕ) (b : Branch)
    (S : CommutingStrategy (Question F (n + 2)) (Question F (n + 2))
      (Answer F (n + 2)) (Answer F (n + 2)) 𝒜) :
    (if b = .consistency then 1 else (n + 1 : ℝ)) *
        (∑ x, (uniformOfFintype F x).toReal *
          (1 - (branchGameWithDiagonalCap n d D b).commutingWinProb (restrictStrategy x S))) ≤
      (if b = .consistency then 1 else (n + 2 : ℝ)) *
        (1 - (branchGameWithDiagonalCap (n + 1) d D b).commutingWinProb S) := by
  simp only [TwoProverGame.commutingWinProb, restrictStrategy_answers]
  exact branchLoss_restrict_le n d D b S.answers

end CFC

end Cslib.PCP.LowIndividualDegree
