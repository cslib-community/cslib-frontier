/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LinearSystemConverse
import CslibFrontier.Foundations.Quantum.Algebra.CStar
import CslibFrontier.Foundations.Quantum.Algebra.Involution
import CslibFrontier.Foundations.Quantum.Algebra.JointMeasurement

/-! # Perfect strategies and state-dependent operator solutions

Checked clients of the converse direction for linear constraint system games: orthogonality of
projective effects in a C⋆-algebra, the bound `‖cx‖_φ ≤ ‖c‖ ‖x‖_φ`, perfect strategies never
giving rejected answers, and Bob's observables of a perfect projective strategy forming an
operator solution in the state. The round trip operator solution → perfect strategy →
state-dependent operator solution is checked, in general and for a satisfying assignment.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LinearSystemConverse

open Cslib Cslib.Quantum Cslib.PCP
open BitString (signVal)
open scoped ComplexOrder

variable {𝒜 : Type} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

/-- Distinct effects of a projective measurement are orthogonal. -/
example {α : Type} [Fintype α] (M : Measurement α 𝒜) (hM : M.IsProjective) {a b : α}
    (hab : a ≠ b) : M.effect a * M.effect b = 0 :=
  hM.mul_eq_zero hab

/-- The state norm is controlled by the C⋆-norm. -/
example (φ : AlgState 𝒜) (c x : 𝒜) : φ.norm (c * x) ≤ ‖c‖ * φ.norm x :=
  φ.norm_mul_le c x

/-- A perfect projective strategy for a linear constraint system game gives Bob observables that
commute within every equation and multiply to `(-1)^{parity}`, in the shared state. -/
example {V E : Type} [Fintype V] [DecidableEq V] [Finite E] (L : LinearSystem V E)
    {μ : PMF (E × V)} (S : CommutingStrategy E V (V → Bool) Bool 𝒜)
    (hne : ∀ e, ∃ v, μ (e, v) ≠ 0) (hμ : ∀ e, ∀ v ∈ L.support e, μ (e, v) ≠ 0)
    (hA : ∀ e, (S.alice e).IsProjective) (hB : ∀ v, (S.bob v).IsProjective)
    (h : (L.game μ).commutingWinProb S = 1) (e : E) (l : List V)
    (hl : l.Perm (L.support e).toList) :
    (l.map fun v => (S.bob v).observable).prod ≈[S.state; 0]
      (signVal (L.parity e) : ℂ) • 1 :=
  (CommutingStrategy.stateSolution L S hne hμ hA hB h).prod_eq e l hl

/-- Coarse-graining keeps a measurement projective. -/
example {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (M : Measurement α 𝒜)
    (hM : M.IsProjective) (f : α → β) : (M.map f).IsProjective :=
  hM.map f

/-- **Round trip.** The strategy of an operator solution, with Bob holding observables agreeing
with it in the state, is projective and perfect, so it gives back a state-dependent operator
solution, whose observables are Bob's. -/
example {V E : Type} [Fintype V] [DecidableEq V] [Finite E] (L : LinearSystem V E)
    (X : L.OperatorSolution 𝒜) (Y : V → 𝒜) (hY : ∀ v, IsSelfAdjoint (Y v))
    (hY' : ∀ v, Y v * Y v = 1) (φ : AlgState 𝒜) (hXY : ∀ u v, Commute (X.op u) (Y v))
    (hagree : ∀ v, X.op v ≈[φ; 0] Y v) (μ : PMF (E × V)) (hne : ∀ e, ∃ v, μ (e, v) ≠ 0)
    (hμ : ∀ e, ∀ v ∈ L.support e, μ (e, v) ≠ 0) :
    ∃ Z : L.StateSolution φ, ∀ v, Z.op v = (Measurement.ofInvolution (hY v) (hY' v)).observable :=
  ⟨CommutingStrategy.stateSolution L (X.strategy Y hY hY' φ hXY) hne hμ
    X.isProjective_eqMeasurement (fun v => Measurement.isProjective_ofInvolution (hY v) (hY' v))
    (X.commutingWinProb_strategy_of_agreement Y hY hY' φ hXY hagree μ), fun _ => rfl⟩

/-- The identity state on `ℂ`. -/
noncomputable def complexState : AlgState ℂ where
  toFun z := z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  monotone' _ _ h := h
  map_one' := rfl

/-- **Round trip for a satisfying assignment**, under a question distribution of full support:
the scalars `(-1)^{s_v}` of a satisfying assignment `s` come back as a state-dependent operator
solution in `ℂ`. -/
noncomputable example {V E : Type} [Fintype V] [DecidableEq V] [Finite E] [Nonempty V]
    (L : LinearSystem V E) (s : V → Bool) (hs : ∀ e, L.Satisfies e s) (μ : PMF (E × V))
    (hμ : ∀ q, μ q ≠ 0) : L.StateSolution complexState :=
  let X := LinearSystem.OperatorSolution.ofAssignment s hs
  CommutingStrategy.stateSolution (μ := μ) L
    (X.strategy X.op X.isSelfAdjoint X.mul_self complexState fun _ _ => Commute.all _ _)
    (fun _ => ⟨Classical.arbitrary V, hμ _⟩) (fun _ _ _ => hμ _)
    X.isProjective_eqMeasurement
    (fun v => Measurement.isProjective_ofInvolution (X.isSelfAdjoint v) (X.mul_self v))
    (X.commutingWinProb_strategy_of_agreement _ _ _ _ _ (fun _ => AlgState.approx_self _ _) _)

/-- Rejected answers have probability `0` in a perfect strategy. -/
example {V E : Type} [Fintype V] [DecidableEq V] [Finite E] (L : LinearSystem V E)
    {μ : PMF (E × V)} (S : CommutingStrategy E V (V → Bool) Bool 𝒜)
    (h : (L.game μ).commutingWinProb S = 1) {e : E} {v : V} (hμ : μ (e, v) ≠ 0) {a : V → Bool}
    {b : Bool} (hrej : ¬ (L.game μ).accepts e v a b) : S.prob e v a b = 0 :=
  TwoProverGame.commutingProb_eq_zero_of_not_accepts (L.game μ) h hμ hrej

end CslibFrontierTests.LinearSystemConverse
