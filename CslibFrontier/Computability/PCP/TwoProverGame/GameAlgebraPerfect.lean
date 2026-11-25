/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.GameAlgebra
public import CslibFrontier.Computability.PCP.TwoProverGame.Synchronous
import CslibFrontier.Foundations.Quantum.Algebra.Consistency
import CslibFrontier.Probability.PMF.Event
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Perfect commuting strategies for synchronous games

The verifier's rejecting tuples all have probability zero in a perfect strategy.
A representation of its game algebra in a tracial C*-algebra gives such a
strategy through the commuting GNS actions. Conversely, re-realize a perfect
synchronous strategy from the trace on its generated algebra. On the closed
algebra of the left operators, the cyclic vector is separating by density of the
commuting right action. This faithfulness turns the zero-probability conditions
into the operator relations.

The correspondence is [Helton, Meyer, Paulsen and Satriano, Theorem 3.2(3)][HeltonEtAl2019].
The score formulation requires full support on question pairs because the source
uses pointwise perfection.
-/

public section

namespace Cslib.PCP.TwoProverGame

open Cslib.Quantum
open scoped ComplexOrder InnerProductSpace Pointwise

universe u

variable {X A : Type*} [Fintype A] (G : TwoProverGame X X A A)

section Perfect

variable {B : Type u} [Ring B] [PartialOrder B] [Algebra ℂ B]

/-- A commuting strategy has zero probability for every rejected answer at every question pair. -/
@[expose] def IsPerfectCommuting (S : CommutingStrategy X X A A B) : Prop :=
  ∀ x y a b, ¬ G.accepts x y a b → S.prob x y a b = 0

/-- A pointwise perfect strategy for a synchronous game is synchronous. -/
theorem IsPerfectCommuting.isSynchronous {S : CommutingStrategy X X A A B}
    (h : G.IsPerfectCommuting S) (hG : G.IsSynchronous) : S.IsSynchronous :=
  fun x a b hab => h x x a b (hG x a b hab)

variable [StarRing B] [StarOrderedRing B] [TopologicalSpace B]
  [ContinuousFunctionalCalculus ℝ B IsSelfAdjoint] [NonnegSpectrumClass ℝ B]

private theorem sampled_perfect_iff (S : CommutingStrategy X X A A B) :
    G.commutingWinProb S = 1 ↔
      ∀ x y, (x, y) ∈ G.questions.support →
        ∀ a b, ¬ G.accepts x y a b → S.prob x y a b = 0 := by
  change ((G.questions.bind fun q => (S.answers q.1 q.2).map fun ab => (q, ab)).toOuterMeasure
    {z | G.AcceptsRound z}).toReal = 1 ↔ _
  rw [← ENNReal.toReal_one, ENNReal.toReal_eq_toReal_iff'
    (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _) ENNReal.one_ne_top,
    PMF.toOuterMeasure_apply_eq_one_iff, Set.subset_def]
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff, Prod.exists]
  simp only [PMF.mem_support_iff, S.answers_apply, ne_eq, ENNReal.ofReal_eq_zero,
    Set.mem_ofPred_eq]
  refine ⟨fun h x y hxy a b hr => le_antisymm
      (by_contra fun hp => hr (h _ ⟨x, y, hxy, a, b, hp, rfl⟩)) (S.prob_nonneg x y a b), ?_⟩
  rintro h _ ⟨x, y, hxy, a, b, hab, rfl⟩
  exact by_contra fun hr => hab (h x y hxy a b hr).le

/-- Pointwise perfection implies winning with probability one for any question distribution. -/
theorem IsPerfectCommuting.commutingWinProb_eq_one {S : CommutingStrategy X X A A B}
    (h : G.IsPerfectCommuting S) : G.commutingWinProb S = 1 :=
  (G.sampled_perfect_iff S).mpr fun x y _ => h x y

/-- With full support, winning with probability one is equivalent to pointwise perfection. -/
theorem commutingWinProb_eq_one_iff_isPerfectCommuting (S : CommutingStrategy X X A A B)
    (hfull : ∀ x y, (x, y) ∈ G.questions.support) :
    G.commutingWinProb S = 1 ↔ G.IsPerfectCommuting S :=
  ⟨fun h x y => (G.sampled_perfect_iff S).mp h x y (hfull x y),
    fun h => h.commutingWinProb_eq_one G⟩

end Perfect

section FromRepresentation

variable {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The images of the generators under a representation are a projective measurement. -/
def GameAlgebra.measurement (π : G.GameAlgebra →⋆ₐ[ℂ] B) (x : X) : Measurement A B where
  effect a := π (GameAlgebra.effect G x a)
  nonneg a := by
    have hp : star (π (GameAlgebra.effect G x a)) * π (GameAlgebra.effect G x a) =
      π (GameAlgebra.effect G x a) := by
      rw [← map_star, GameAlgebra.star_effect, ← map_mul, GameAlgebra.effect_mul_self]
    rw [← hp]
    exact star_mul_self_nonneg _
  sum_effect := by rw [← map_sum, GameAlgebra.sum_effect, map_one]

/-- Representations send the game generators to projective measurements. -/
theorem GameAlgebra.measurement_isProjective (π : G.GameAlgebra →⋆ₐ[ℂ] B) (x : X) :
    (GameAlgebra.measurement G π x).IsProjective := by
  intro a
  change π (GameAlgebra.effect G x a) * π (GameAlgebra.effect G x a) = π (GameAlgebra.effect G x a)
  rw [← map_mul, GameAlgebra.effect_mul_self]

/-- A tracial representation gives a pointwise perfect strategy through the GNS actions. -/
theorem GameAlgebra.isPerfectCommuting_ofTracial (π : G.GameAlgebra →⋆ₐ[ℂ] B)
    (τ : AlgState B) (hτ : τ.IsTracial) :
    G.IsPerfectCommuting (CommutingStrategy.ofTracial τ hτ (GameAlgebra.measurement G π)) := by
  intro x y a b h
  apply Complex.ofReal_injective
  rw [CommutingStrategy.ofTracial_prob]
  change τ (π (GameAlgebra.effect G x a) * π (GameAlgebra.effect G y b)) = _
  rw [← map_mul, GameAlgebra.effect_mul_eq_zero_of_rejected G x y a b h, map_zero, map_zero,
    Complex.ofReal_zero]

end FromRepresentation

section ToRepresentation

open MulOpposite

variable {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

private theorem gns_faithful (τ : AlgState B) (hτ : τ.IsTracial) (P : X → Measurement A B) :
    (CommutingStrategy.ofTracial τ hτ P).aliceState.IsFaithful := by
  let S := CommutingStrategy.ofTracial τ hτ P
  intro z hz
  let T := S.aliceAlgebra.subtype z
  let ξ : τ.toPositiveLinearMap.GNS := τ.toPreGNS 1
  rw [CommutingStrategy.aliceState_apply] at hz
  change (CommutingStrategy.ofTracial τ hτ P).state (S.aliceAlgebra.subtype (star z * z)) = 0 at hz
  rw [map_mul, map_star, CommutingStrategy.ofTracial_state_apply] at hz
  change inner ℂ ξ ((star T * T) ξ) = 0 at hz
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right] at hz
  have hξ : T ξ = 0 := inner_self_eq_zero.mp hz
  have hcomm (a : B) : Commute T (τ.gnsRight hτ (op a)) := by
    let R := τ.gnsRight hτ (op a)
    have hc : S.aliceAlgebra ≤ StarSubalgebra.centralizer ℂ {R} := by
      refine S.aliceAlgebra_le
        (by
          rw [StarSubalgebra.coe_centralizer]
          exact Set.isClosed_centralizer _) fun x b => ?_
      refine (StarSubalgebra.mem_centralizer_iff ℂ).mpr ?_
      rintro _ rfl
      dsimp only [S]
      rw [CommutingStrategy.ofTracial_alice_effect,
        show star R = τ.gnsRight hτ (op (star a)) by simp [R, ← map_star]]
      exact ⟨(τ.commute_gnsLeft_gnsRight hτ ((P x).effect b) a).symm.eq,
        (τ.commute_gnsLeft_gnsRight hτ ((P x).effect b) (star a)).symm.eq⟩
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hc z.property) R rfl).1.symm
  suffices hT : T = 0 from Subtype.ext hT
  refine τ.gns_ext fun a => ?_
  have hpre : (τ.toPreGNS a : τ.toPositiveLinearMap.GNS) = τ.gnsRight hτ (op a) ξ := by
    rw [show ξ = τ.toPreGNS 1 from rfl, τ.gnsRight_toPreGNS, one_mul]
  rw [hpre, ← mul_apply_eq_comp, (hcomm a).eq, mul_apply_eq_comp, hξ, map_zero, zero_apply]

private theorem projective_of_synchronous_of_faithful
    (S : CommutingStrategy X X A A B) (hS : S.IsSynchronous) (hfaith : S.aliceState.IsFaithful)
    (x : X) : (S.aliceMeasurements x).IsProjective := by
  intro a
  let E := (S.aliceMeasurements x).effect a
  let d := E - E * E
  have hd : 0 ≤ d := sub_nonneg.mpr ((S.aliceMeasurements x).effect_mul_self_le a)
  have hzero : S.aliceState d = 0 := by
    have hE : (E : B) = (S.alice x).effect a := S.aliceMeasurements_effect x a
    rw [show d = E - E * E from rfl, map_sub, ← hS.ofReal_prob_eq_aliceState,
      CommutingStrategy.aliceState_apply, hE, ← S.state.ofReal_re_apply ((S.alice x).nonneg a),
      ← S.sum_prob_bob x x a, hS.sum_prob_eq_diag, sub_self]
  have hy : CFC.sqrt d = 0 := hfaith (CFC.sqrt d) (by
    rw [(CFC.sqrt_nonneg d).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self d hd, hzero])
  have hdz : d = 0 := by rw [← CFC.sqrt_mul_sqrt_self d hd, hy, zero_mul]
  exact (sub_eq_zero.mp hdz).symm

private theorem product_eq_zero_of_trace_zero {C : Type u} [Ring C] [StarRing C] [Algebra ℂ C]
    [PartialOrder C] (τ : AlgState C) (hτ : τ.IsTracial)
    (hfaith : τ.IsFaithful)
    {P Q : C} (hP : IsSelfAdjoint P) (hQ : IsSelfAdjoint Q) (hPP : P * P = P)
    (hQQ : Q * Q = Q) (hzero : τ (P * Q) = 0) : P * Q = 0 := by
  apply hfaith
  rw [star_mul, hP.star_eq, hQ.star_eq, mul_assoc Q P, ← mul_assoc P P Q, hPP,
    hτ Q (P * Q), mul_assoc P Q Q, hQQ, hzero]

private noncomputable def representation_of_faithful (S : CommutingStrategy X X A A B)
    (hS : G.IsPerfectCommuting S) (hsyn : S.IsSynchronous) (hfaith : S.aliceState.IsFaithful) :
    G.GameAlgebra →⋆ₐ[ℂ] S.aliceAlgebra := by
  let Q := S.aliceMeasurements
  have hQ (x : X) : (Q x).IsProjective :=
    projective_of_synchronous_of_faithful S hsyn hfaith x
  refine GameAlgebra.lift G (fun x a => (Q x).effect a)
    (fun x a => ((Q x).nonneg a).isSelfAdjoint) (fun x a => hQ x a)
    (fun x => (Q x).sum_effect) ?_
  intro x y a b hr
  apply product_eq_zero_of_trace_zero S.aliceState hsyn.aliceState_isTracial hfaith
    ((Q x).nonneg a).isSelfAdjoint ((Q y).nonneg b).isSelfAdjoint (hQ x a) (hQ y b)
  rw [← hsyn.ofReal_prob_eq_aliceState, hS x y a b hr, Complex.ofReal_zero]

/-- Every pointwise perfect commuting strategy for a synchronous game gives a unital
star representation with a faithful tracial state. -/
theorem exists_faithful_tracial_representation (hG : G.IsSynchronous)
    (S : CommutingStrategy X X A A B) (hS : G.IsPerfectCommuting S) :
    ∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C) (_ : StarOrderedRing C),
      ∃ τ : AlgState C, τ.IsTracial ∧ τ.IsFaithful ∧ Nonempty (G.GameAlgebra →⋆ₐ[ℂ] C) := by
  have hsyn := hS.isSynchronous G hG
  let τ := S.aliceState
  let P := S.aliceMeasurements
  let T := CommutingStrategy.ofTracial τ hsyn.aliceState_isTracial P
  have hprob (x y : X) (a b : A) : T.prob x y a b = S.prob x y a b := by
    apply Complex.ofReal_injective
    change ((CommutingStrategy.ofTracial τ hsyn.aliceState_isTracial P).prob x y a b : ℂ) = _
    rw [CommutingStrategy.ofTracial_prob]
    exact (hsyn.ofReal_prob_eq_aliceState x y a b).symm
  have hT : G.IsPerfectCommuting T := fun x y a b hr => (hprob x y a b).trans (hS x y a b hr)
  have hTs := hT.isSynchronous G hG
  have hfaith := gns_faithful τ hsyn.aliceState_isTracial P
  exact ⟨T.aliceAlgebra, inferInstance, inferInstance, inferInstance, T.aliceState,
    hTs.aliceState_isTracial, hfaith, ⟨representation_of_faithful G T hT hTs hfaith⟩⟩

/-- A synchronous game has a perfect commuting strategy exactly when its algebra has a unital
star representation in a C*-algebra with a faithful tracial state. -/
theorem exists_isPerfectCommuting_iff (hG : G.IsSynchronous) :
    (∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C) (_ : StarOrderedRing C),
      ∃ S : CommutingStrategy X X A A C, G.IsPerfectCommuting S) ↔
    (∃ (C : Type u) (_ : CStarAlgebra C) (_ : PartialOrder C) (_ : StarOrderedRing C),
      ∃ τ : AlgState C, τ.IsTracial ∧ τ.IsFaithful ∧ Nonempty (G.GameAlgebra →⋆ₐ[ℂ] C)) :=
  ⟨fun ⟨_, _, _, _, S, hS⟩ => G.exists_faithful_tracial_representation hG S hS,
    fun ⟨_, _, _, _, τ, hτ, _, ⟨π⟩⟩ => ⟨_, inferInstance, inferInstance, inferInstance,
      CommutingStrategy.ofTracial τ hτ (GameAlgebra.measurement G π),
      GameAlgebra.isPerfectCommuting_ofTracial G π τ hτ⟩⟩

end ToRepresentation

end Cslib.PCP.TwoProverGame
