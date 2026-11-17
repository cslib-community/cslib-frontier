/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Commuting
public import CslibFrontier.Foundations.Quantum.Algebra.JointMeasurement
import CslibFrontier.Probability.PMF

/-!
# Linear constraint system games

A *binary linear constraint system* (`Cslib.PCP.LinearSystem`) has equations `e` over Boolean
variables `V`: the variables in `support e` must have parity `parity e`. Its game
(`Cslib.PCP.LinearSystem.game`), for a distribution `μ` of pairs of an equation and a variable,
asks Alice for an assignment satisfying the equation `e` and Bob for the value of the variable
`v`, and accepts when Alice's assignment satisfies `e` and agrees with Bob's bit on `v` whenever
`v` occurs in `e` [Cleve and Mittal][CleveMittal2014]. The magic square is the system of its six
rows and columns.

An **operator solution** (`Cslib.PCP.LinearSystem.OperatorSolution`) replaces the variables by
`±1` observables: self-adjoint involutions commuting within every equation, whose product over
each equation is the sign `(-1)^{parity e}`. A satisfying assignment is an operator solution in
`ℂ`, but there are systems, such as the magic square, with operator solutions and no satisfying
assignment.

**Operator solutions give perfect strategies** [Cleve and Mittal][CleveMittal2014]: if Alice
measures each equation jointly in an operator solution `X` (`Cslib.Quantum.Measurement.ofCommuting`)
and Bob measures each variable `v` by an observable `Y_v` commuting with Alice's and agreeing
perfectly with `X_v` in the shared state, they win with probability `1` for every question
distribution, in every commuting-operator model
(`Cslib.PCP.LinearSystem.OperatorSolution.commutingWinProb_strategy`). Outcomes violating the
equation vanish because of the product relation (`Cslib.Quantum.jointProj_eq_zero`), and
disagreement on `v` vanishes after exchanging Bob's `Y_v` for Alice's `X_v` inside the state
(`Cslib.Quantum.AlgState.apply_mul_signProj_eq_of_approx_zero`).

## Main definitions

* `Cslib.PCP.LinearSystem`: a binary linear constraint system.
* `Cslib.PCP.LinearSystem.game`: its game.
* `Cslib.PCP.LinearSystem.OperatorSolution`: operator solutions.
* `Cslib.PCP.LinearSystem.OperatorSolution.strategy`: the strategy of an operator solution.

## Main results

* `Cslib.PCP.prod_boolSign_eq`: the sign of an assignment is the sign of its parity.
* `Cslib.PCP.LinearSystem.OperatorSolution.commutingWinProb_strategy`: operator solutions with
  perfect agreement win with certainty.

## References

* [R. Cleve and R. Mittal, *Characterization of binary constraint system
  games*][CleveMittal2014]
-/

@[expose] public section

namespace Cslib.PCP

open Finset Quantum

variable {V E : Type*}

/-- The parity of the assignment `a` on the finite set `s`. -/
def setParity (s : Finset V) (a : V → Bool) : Bool :=
  decide (Odd (s.filter fun v => a v = true).card)

/-- The product of the signs of an assignment on `s` is the sign of its parity. -/
theorem prod_boolSign_eq (s : Finset V) (a : V → Bool) :
    ∏ v ∈ s, boolSign (a v) = boolSign (setParity s a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [setParity]
  | insert w s hw ih =>
    rw [prod_insert hw, ih]
    unfold setParity
    rw [filter_insert]
    cases h : a w
    · simp
    · have hw' : w ∉ s.filter fun v => a v = true := by simp [hw]
      simp only [↓reduceIte, card_insert_of_notMem hw']
      by_cases ho : Odd (s.filter fun v => a v = true).card
      · have : ¬ Odd ((s.filter fun v => a v = true).card + 1) := by
          rw [Nat.odd_add_one]; exact not_not.mpr ho
        simp [ho, this]
      · have : Odd ((s.filter fun v => a v = true).card + 1) := by
          rw [Nat.odd_add_one]; exact ho
        simp [ho, this]

/-- A **binary linear constraint system**: each equation `e` asks that the variables in
`support e` have parity `parity e`. -/
structure LinearSystem (V E : Type*) where
  /-- The variables of the equation `e`. -/
  support : E → Finset V
  /-- The required parity of the equation `e`. -/
  parity : E → Bool

namespace LinearSystem

variable (L : LinearSystem V E)

/-- The assignment `a` satisfies the equation `e`. -/
def Satisfies (e : E) (a : V → Bool) : Prop :=
  setParity (L.support e) a = L.parity e

instance (e : E) (a : V → Bool) : Decidable (L.Satisfies e a) :=
  inferInstanceAs (Decidable (_ = _))

/-- The **game** of a linear constraint system with question distribution `μ`: Alice receives an
equation and answers an assignment, Bob receives a variable and answers a bit; they win when the
assignment satisfies the equation and agrees with Bob's bit on the variable, if it occurs. -/
noncomputable def game (μ : PMF (E × V)) : TwoProverGame E V (V → Bool) Bool where
  questions := μ
  accepts e v a b := L.Satisfies e a ∧ (v ∈ L.support e → a v = b)

instance (μ : PMF (E × V)) (e : E) (v : V) (a : V → Bool) (b : Bool) [DecidableEq V] :
    Decidable ((L.game μ).accepts e v a b) :=
  inferInstanceAs (Decidable (L.Satisfies e a ∧ (v ∈ L.support e → a v = b)))

/-- An **operator solution** of a linear constraint system: `±1` observables commuting within
every equation, whose product over the equation `e` is `(-1)^{parity e}`. -/
structure OperatorSolution (𝒜 : Type*) [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] where
  /-- The observable of the variable `v`. -/
  op : V → 𝒜
  isSelfAdjoint : ∀ v, IsSelfAdjoint (op v)
  mul_self : ∀ v, op v * op v = 1
  commute : ∀ e, ∀ u ∈ L.support e, ∀ w ∈ L.support e, Commute (op u) (op w)
  prod_eq : ∀ e, jointProd (fun v : L.support e => op v)
    (fun u w => commute e u u.2 w w.2) = boolSign (L.parity e) • 1

namespace OperatorSolution

variable {L} {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [Algebra ℂ 𝒜] [StarModule ℂ 𝒜] (X : L.OperatorSolution 𝒜)

/-- The observables of the equation `e`. -/
def eqOp (e : E) : L.support e → 𝒜 :=
  fun v => X.op v

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarModule ℂ 𝒜] in
theorem eqOp_commute (e : E) (u w : L.support e) : Commute (X.eqOp e u) (X.eqOp e w) :=
  X.commute e u u.2 w w.2

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarModule ℂ 𝒜] in
theorem eqOp_isSelfAdjoint (e : E) (u : L.support e) : IsSelfAdjoint (X.eqOp e u) :=
  X.isSelfAdjoint u

omit [PartialOrder 𝒜] [StarOrderedRing 𝒜] [StarModule ℂ 𝒜] in
theorem eqOp_mul_self (e : E) (u : L.support e) : X.eqOp e u * X.eqOp e u = 1 :=
  X.mul_self u

variable [DecidableEq V]

/-- An assignment of the variables of an equation, extended by `false`. -/
def extend (s : Finset V) (a : s → Bool) (v : V) : Bool :=
  if h : v ∈ s then a ⟨v, h⟩ else false

variable [Fintype V]

/-- Alice's measurement of the equation `e`: the joint measurement of its observables. -/
noncomputable def eqMeasurement (e : E) : Measurement (V → Bool) 𝒜 :=
  (Measurement.ofCommuting (X.eqOp e) (X.eqOp_commute e) (X.eqOp_isSelfAdjoint e)
    (X.eqOp_mul_self e)).map (extend (L.support e))

/-- The strategy of an operator solution `X` for Alice and observables `Y` for Bob in the state
`φ`, when Alice's observables commute with Bob's. -/
noncomputable def strategy (Y : V → 𝒜) (hY : ∀ v, IsSelfAdjoint (Y v))
    (hY' : ∀ v, Y v * Y v = 1) (φ : AlgState 𝒜) (hXY : ∀ u v, Commute (X.op u) (Y v)) :
    CommutingStrategy E V (V → Bool) Bool 𝒜 where
  state := φ
  alice := X.eqMeasurement
  bob v := Measurement.ofInvolution (hY v) (hY' v)
  commute e v a b := by
    refine Commute.sum_left _ _ _ fun a' _ => ?_
    rw [Measurement.ofCommuting_effect]
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute
      (a := signProj (Y v) b) (jointProj_mem_jointAlg _ _ a') ?_).symm
    rintro _ ⟨u, rfl⟩
    exact (hXY u v).symm.signProj_left b

variable [SelfAdjointDecompose 𝒜]

/-- In the strategy of an operator solution with perfect agreement, rejected answers have
probability `0`. -/
theorem apply_effect_mul_effect_eq_zero (Y : V → 𝒜) (φ : AlgState 𝒜)
    (hagree : ∀ v, X.op v ≈[φ; 0] Y v) (μ : PMF (E × V)) {e : E} {v : V} {a : V → Bool}
    {b : Bool} (hrej : ¬ (L.game μ).accepts e v a b) :
    φ ((X.eqMeasurement e).effect a * signProj (Y v) b) = 0 := by
  simp only [eqMeasurement, Measurement.map_effect, Measurement.ofCommuting_effect, sum_mul,
    map_sum]
  refine Finset.sum_eq_zero fun a' ha' => ?_
  have hext : extend (L.support e) a' = a := (mem_filter.mp ha').2
  have hval : ∀ w (hw : w ∈ L.support e), a' ⟨w, hw⟩ = a w := fun w hw => by
    simp [← hext, extend, hw]
  simp only [game, not_and] at hrej
  by_cases hsat : L.Satisfies e a
  · obtain ⟨hv, hne⟩ : ∃ hv : v ∈ L.support e, a v ≠ b := by
      by_contra h
      push Not at h
      exact hrej hsat h
    have hz : jointProj (X.eqOp e) (X.eqOp_commute e) a' * signProj (X.op v) b = 0 :=
      jointProj_mul_signProj_of_ne (X.eqOp e) (X.eqOp_commute e) (X.eqOp_mul_self e)
        (j := ⟨v, hv⟩) (by rw [hval]; exact hne)
    rw [← AlgState.apply_mul_signProj_eq_of_approx_zero (hagree v), hz, map_zero]
  · have hval' : ∀ i : L.support e, a' i = a i := fun i => hval i i.2
    have hprod : ∏ i, boolSign (a' i) = boolSign (setParity (L.support e) a) :=
      calc ∏ i, boolSign (a' i) = ∏ i : L.support e, boolSign (a i) :=
            Finset.prod_congr rfl fun i _ => by rw [hval' i]
        _ = ∏ w ∈ L.support e, boolSign (a w) :=
          Finset.prod_coe_sort (L.support e) (fun w => boolSign (a w))
        _ = boolSign (setParity (L.support e) a) := prod_boolSign_eq _ _
    have hz : jointProj (X.eqOp e) (X.eqOp_commute e) a' = 0 :=
      jointProj_eq_zero (X.eqOp e) (X.eqOp_commute e) (X.eqOp_mul_self e) (X.prod_eq e)
        (by rw [hprod]; exact fun h => hsat (boolSign_injective h).symm)
    rw [hz, zero_mul, map_zero]

variable [TopologicalSpace 𝒜] [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint]
  [NonnegSpectrumClass ℝ 𝒜] [Finite E]

/-- **Operator solutions win with certainty** [Cleve and Mittal][CleveMittal2014]: if Alice
measures the equations jointly in an operator solution `X`, and Bob measures each variable by an
observable `Y_v` commuting with Alice's and agreeing perfectly with `X_v` in the state, they win the
game of the linear constraint system with probability `1`, for every question distribution. -/
theorem commutingWinProb_strategy (Y : V → 𝒜) (hY : ∀ v, IsSelfAdjoint (Y v))
    (hY' : ∀ v, Y v * Y v = 1) (φ : AlgState 𝒜) (hXY : ∀ u v, Commute (X.op u) (Y v))
    (hagree : ∀ v, X.op v ≈[φ; 0] Y v) (μ : PMF (E × V)) :
    (L.game μ).commutingWinProb (X.strategy Y hY hY' φ hXY) = 1 := by
  have := Fintype.ofFinite E
  set S := X.strategy Y hY hY' φ hXY
  have hsum : ∀ e v,
      (∑ a, ∑ b, if (L.game μ).accepts e v a b then S.prob e v a b else 0) = 1 := fun e v => by
    rw [← S.sum_prob e v]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · rfl
    · have := X.apply_effect_mul_effect_eq_zero Y φ hagree μ h
      simp only [CommutingStrategy.prob]
      change 0 = (φ ((X.eqMeasurement e).effect a * signProj (Y v) b)).re
      rw [this, Complex.zero_re]
  rw [TwoProverGame.commutingWinProb_eq_sum]
  simp only [hsum, mul_one]
  rw [← Fintype.sum_prod_type']
  exact Cslib.Probability.PMF.sum_toReal μ

end OperatorSolution

end LinearSystem

end Cslib.PCP
