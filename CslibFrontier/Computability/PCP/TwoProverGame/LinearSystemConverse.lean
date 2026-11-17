/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LinearSystem
public import CslibFrontier.Foundations.Quantum.Algebra.Consistency
public import CslibFrontier.Foundations.Quantum.Algebra.CStar
import CslibFrontier.Probability.PMF

/-!
# Perfect strategies give operator solutions in the state

The converse direction of the characterization of linear constraint system games
[Cleve and Mittal][CleveMittal2014]: a perfect strategy yields an operator solution. Here it is
proved in the form that holds in every commuting-operator model, *in the shared state*: if a
projective commuting-operator strategy in a C⋆-algebra wins the game of a linear constraint system
with certainty, for a question distribution of full support, then Bob's `±1` observables
`B_v = F_v(0) - F_v(1)` form a **state-dependent operator solution**
(`Cslib.PCP.LinearSystem.StateSolution`): they are self-adjoint involutions, the observables of each
equation commute in the state, `B_u B_w ≈ B_w B_u` with error `0`, and their product over each
equation `e` is `(-1)^{parity e}` in the state
(`Cslib.PCP.CommutingStrategy.stateSolution`). Passing from relations
in the state to relations in an algebra (the GNS representation restricted to the cyclic subspace)
is not formalized here.

The proof follows the paper:

* a perfect strategy wins every question with certainty, so every rejected answer has probability
  `0` (`Cslib.PCP.TwoProverGame.commutingProb_eq_zero_of_not_accepts`);
* hence Alice never answers an assignment violating her equation, `E_e(a) ≈ 0`, and her marginal
  observable `A_{e,v} = ∑_a σ_{a_v} E_e(a)` agrees perfectly with Bob's `B_v`
  (`Cslib.Quantum.Measurement.sum_norm_sub_sq_le_of_agreement`);
* the marginals of one projective measurement multiply pointwise, so the product of the `A_{e,v}`
  over `e` is `∑_a σ_{parity(a)} E_e(a) ≈ (-1)^{parity e}`;
* Bob's products are transferred to Alice's inside the state, in reverse order, because each `B_v`
  commutes with Alice's operators and agrees with `A_{e,v}`.

## Main definitions

* `Cslib.PCP.LinearSystem.StateSolution`: state-dependent operator solutions.

## Main results

* `Cslib.PCP.TwoProverGame.commutingProb_eq_zero_of_not_accepts`: perfect strategies never give
  rejected answers.
* `Cslib.PCP.CommutingStrategy.stateSolution`: perfect projective
  strategies give state-dependent operator solutions.

## References

* [R. Cleve and R. Mittal, *Characterization of binary constraint system
  games*][CleveMittal2014]
-/

@[expose] public section

namespace Cslib.PCP

open Finset Quantum

/-! ### Perfect strategies -/

namespace TwoProverGame

variable {X Y A B 𝒜 : Type*} [Finite X] [Finite Y] [Fintype A] [Fintype B]
  (G : TwoProverGame X Y A B) [Ring 𝒜] [StarRing 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
  [Algebra ℂ 𝒜] [TopologicalSpace 𝒜] [ContinuousFunctionalCalculus ℝ 𝒜 IsSelfAdjoint]
  [NonnegSpectrumClass ℝ 𝒜]

/-- A strategy that wins with certainty wins every question of positive probability with
certainty. -/
theorem sum_accepts_eq_one_of_commutingWinProb_eq_one
    [∀ x y a b, Decidable (G.accepts x y a b)] {S : CommutingStrategy X Y A B 𝒜}
    (h : G.commutingWinProb S = 1) {x : X} {y : Y} (hq : G.questions (x, y) ≠ 0) :
    ∑ a, ∑ b, (if G.accepts x y a b then S.prob x y a b else 0) = 1 := by
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  set w : X → Y → ℝ := fun x y => ∑ a, ∑ b, if G.accepts x y a b then S.prob x y a b else 0
  have hw : ∀ x y, w x y ≤ 1 := fun x y => by
    rw [← S.sum_prob x y]
    refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
    split_ifs
    · exact le_rfl
    · exact S.prob_nonneg x y a b
  have hμ : ∑ x, ∑ y, (G.questions (x, y)).toReal = 1 := by
    rw [← Fintype.sum_prod_type']
    exact Cslib.Probability.PMF.sum_toReal G.questions
  rw [commutingWinProb_eq_sum] at h
  have hzero : ∑ x, ∑ y, (G.questions (x, y)).toReal * (1 - w x y) = 0 := by
    simp only [mul_sub, mul_one, sum_sub_distrib, hμ]
    rw [h, sub_self]
  have hnn : ∀ x y, 0 ≤ (G.questions (x, y)).toReal * (1 - w x y) := fun x y =>
    mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr (hw x y))
  have hx := (sum_eq_zero_iff_of_nonneg fun x _ => sum_nonneg fun y _ => hnn x y).mp hzero x
    (mem_univ x)
  have hxy := (sum_eq_zero_iff_of_nonneg fun y _ => hnn x y).mp hx y (mem_univ y)
  have hpos : (G.questions (x, y)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hq, PMF.apply_ne_top _ _⟩
  have := (mul_eq_zero.mp hxy).resolve_left hpos
  linarith

/-- A strategy that wins with certainty never gives a rejected answer to a question of positive
probability. -/
theorem commutingProb_eq_zero_of_not_accepts {S : CommutingStrategy X Y A B 𝒜}
    (h : G.commutingWinProb S = 1) {x : X} {y : Y} (hq : G.questions (x, y) ≠ 0) {a : A} {b : B}
    (hrej : ¬ G.accepts x y a b) : S.prob x y a b = 0 := by
  classical
  have h₀ := G.sum_accepts_eq_one_of_commutingWinProb_eq_one h hq
  have h₁ : ∑ a, ∑ b, (S.prob x y a b - if G.accepts x y a b then S.prob x y a b else 0) = 0 := by
    simp only [sum_sub_distrib, S.sum_prob, h₀, sub_self]
  have hnn : ∀ a b, 0 ≤ S.prob x y a b - (if G.accepts x y a b then S.prob x y a b else 0) :=
    fun a b => by split_ifs <;> simp [S.prob_nonneg]
  have ha := (sum_eq_zero_iff_of_nonneg fun a _ => sum_nonneg fun b _ => hnn a b).mp h₁ a
    (mem_univ a)
  have hb := (sum_eq_zero_iff_of_nonneg fun b _ => hnn a b).mp ha b (mem_univ b)
  simpa [hrej] using hb

end TwoProverGame

/-! ### State-dependent operator solutions -/

namespace LinearSystem

variable {V E : Type*} (L : LinearSystem V E)

/-- A **state-dependent operator solution** of a linear constraint system: `±1` observables whose
observables in each equation commute in the state `φ`, and whose product over each equation `e`
is `(-1)^{parity e}` in the state. -/
structure StateSolution {𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]
    (φ : AlgState 𝒜) where
  /-- The observable of the variable `v`. -/
  op : V → 𝒜
  isSelfAdjoint : ∀ v, IsSelfAdjoint (op v)
  mul_self : ∀ v, op v * op v = 1
  commute : ∀ e, ∀ u ∈ L.support e, ∀ w ∈ L.support e, op u * op w ≈[φ; 0] op w * op u
  prod_eq : ∀ e, ((L.support e).toList.map op).prod ≈[φ; 0] boolSign (L.parity e) • 1

end LinearSystem

namespace CommutingStrategy

variable {V E 𝒜 : Type*} [CStarAlgebra 𝒜] [PartialOrder 𝒜] [StarOrderedRing 𝒜]

section Algebra

variable {φ : AlgState 𝒜}

/-- A finite sum of operators `0`-close to `0` is `0`-close to `0`. -/
theorem sum_approx_zero {ι : Type*} (s : Finset ι) (f : ι → 𝒜) (h : ∀ i ∈ s, f i ≈[φ; 0] 0) :
    ∑ i ∈ s, f i ≈[φ; 0] 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact AlgState.approx_self φ _ |>.mono le_rfl |> fun h => by simpa using h
  | insert j s hj ih =>
    rw [sum_insert hj]
    simpa using (h j (mem_insert_self j s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

/-- **Transfer of products**: if each `B_v` agrees with `A_v` and commutes with every `A_w`, the
product of the `B_v` along a list agrees with the product of the `A_v` along the reversed list. -/
theorem list_prod_approx (Bo Al : V → 𝒜) (l : List V) (hagree : ∀ v ∈ l, Bo v ≈[φ; 0] Al v)
    (hcomm : ∀ u ∈ l, ∀ w ∈ l, Commute (Bo u) (Al w)) :
    (l.map Bo).prod ≈[φ; 0] (l.reverse.map Al).prod := by
  induction l with
  | nil => simpa using AlgState.approx_self φ 1
  | cons v l ih =>
    have ih' := ih (fun u hu => hagree u (List.mem_cons_of_mem v hu))
      (fun u hu w hw => hcomm u (List.mem_cons_of_mem v hu) w (List.mem_cons_of_mem v hw))
    have hc : Commute (Bo v) (l.reverse.map Al).prod :=
      Commute.list_prod_right _ _ fun x hx => by
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
        exact hcomm v List.mem_cons_self w (List.mem_cons_of_mem v (List.mem_reverse.mp hw))
    have h₁ := ih'.mul_left_zero (Bo v)
    have h₂ := (hagree v List.mem_cons_self).mul_left_zero (l.reverse.map Al).prod
    rw [hc.eq] at h₁
    simpa [List.prod_append] using h₁.trans h₂

end Algebra

variable [Fintype V] [DecidableEq V] {S : CommutingStrategy E V (V → Bool) Bool 𝒜}

/-- Alice's marginal observable `A_{e,v} = ∑_a σ_{a_v} E_e(a)` of the variable `v` in the equation
`e`. -/
noncomputable def marginalObservable (S : CommutingStrategy E V (V → Bool) Bool 𝒜) (e : E)
    (v : V) : 𝒜 :=
  ∑ a, boolSign (a v) • (S.alice e).effect a

theorem marginalObservable_eq (S : CommutingStrategy E V (V → Bool) Bool 𝒜) (e : E) (v : V) :
    S.marginalObservable e v = ((S.alice e).map fun a => a v).observable := by
  simp only [marginalObservable, Measurement.observable, Measurement.map_effect]
  rw [← sum_filter_add_sum_filter_not univ fun a => a v = false]
  rw [sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  · refine sum_congr ?_ fun a ha => by rw [(mem_filter.mp ha).2, boolSign_false, one_smul]
    ext a; simp
  · refine sum_congr ?_ fun a ha => ?_
    · ext a; simp
    · have : a v = true := by simpa using (mem_filter.mp ha).2
      rw [this, boolSign_true, neg_one_smul]

/-- Products of marginal observables of a projective measurement multiply pointwise. -/
theorem list_prod_marginalObservable (e : E) (hA : (S.alice e).IsProjective) (l : List V) :
    (l.map (S.marginalObservable e)).prod = ∑ a, (l.map fun v => boolSign (a v)).prod •
      (S.alice e).effect a := by
  induction l with
  | nil => simp [(S.alice e).sum_effect]
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, ih, marginalObservable,
      hA.sum_smul_mul_sum_smul]
    simp

variable [Finite E] in
/-- In a perfect strategy, Alice never answers an assignment violating her equation. -/
theorem effect_approx_zero_of_not_satisfies (L : LinearSystem V E) {μ : PMF (E × V)}
    (hμ : ∀ q, μ q ≠ 0) (h : (L.game μ).commutingWinProb S = 1) {e : E} {a : V → Bool}
    (ha : ¬ L.Satisfies e a) : (S.alice e).effect a ≈[S.state; 0] 0 := by
  obtain ⟨q, -⟩ := μ.support_nonempty
  set v := q.2
  have hprob : ∀ b, S.prob e v a b = 0 := fun b =>
    TwoProverGame.commutingProb_eq_zero_of_not_accepts (L.game μ) h (hμ (e, v))
      (fun hacc => ha hacc.1)
  have hre : (S.state ((S.alice e).effect a)).re = 0 := by
    rw [← mul_one ((S.alice e).effect a), ← (S.bob v).sum_effect, mul_sum, map_sum,
      Complex.re_sum]
    exact sum_eq_zero fun b _ => hprob b
  have hE : S.state ((S.alice e).effect a) = 0 := by
    rw [← S.state.ofReal_re_apply ((S.alice e).nonneg a), hre, Complex.ofReal_zero]
  exact AlgState.approx_zero_of_apply_eq_zero ((S.alice e).nonneg a) ((S.alice e).effect_le_one a)
    hE

variable [Finite E] in
/-- In a perfect strategy, Alice's marginal observable of a variable of her equation agrees
perfectly with Bob's observable. -/
theorem marginalObservable_approx (L : LinearSystem V E) {μ : PMF (E × V)} (hμ : ∀ q, μ q ≠ 0)
    (h : (L.game μ).commutingWinProb S = 1) {e : E} {v : V} (hv : v ∈ L.support e) :
    S.marginalObservable e v ≈[S.state; 0] (S.bob v).observable := by
  set M := (S.alice e).map fun a => a v
  set F := S.bob v
  have hcomm : ∀ b, Commute (M.effect b) (F.effect b) := fun b =>
    Commute.sum_left _ _ _ fun a _ => S.commute e v a b
  have hzero : ∀ a b, a v ≠ b → S.prob e v a b = 0 := fun a b hab =>
    TwoProverGame.commutingProb_eq_zero_of_not_accepts (L.game μ) h (hμ (e, v))
      (fun hacc => hab (hacc.2 hv))
  have hagr : Measurement.agreement S.state M F = 1 := by
    have hM : Measurement.agreement S.state M F =
        ∑ b, ∑ a ∈ univ.filter (fun a : V → Bool => a v = b), S.prob e v a b := by
      simp only [Measurement.agreement, M, F, Measurement.map_effect, sum_mul, map_sum,
        Complex.re_sum]
      rfl
    rw [hM, ← S.sum_prob e v, sum_comm]
    refine sum_congr rfl fun b _ => sum_filter_of_ne fun a _ hne => ?_
    by_contra hab
    exact hne (hzero a b hab)
  have hcl := Measurement.sum_norm_sub_sq_le_of_agreement S.state M F hcomm (ε := 0)
    (by rw [hagr]; norm_num)
  have hb : ∀ b, M.effect b ≈[S.state; 0] F.effect b := fun b => by
    have hnn : ∀ c ∈ univ, 0 ≤ S.state.norm (M.effect c - F.effect c) ^ 2 := fun c _ => sq_nonneg _
    have := (sum_eq_zero_iff_of_nonneg hnn).mp (le_antisymm (by simpa using hcl)
      (sum_nonneg hnn)) b (mem_univ b)
    exact le_of_eq (pow_eq_zero_iff two_ne_zero |>.mp this)
  rw [marginalObservable_eq]
  exact ((hb false).sub (hb true)).mono (by norm_num)

omit [StarOrderedRing 𝒜] in
/-- Bob's observables commute with Alice's marginal observables. -/
theorem commute_observable_marginalObservable (e : E) (u w : V) :
    Commute (S.bob u).observable (S.marginalObservable e w) := by
  refine Commute.sum_right _ _ _ fun a _ => Commute.smul_right ?_ _
  exact ((S.commute e u a false).symm.sub_left (S.commute e u a true).symm)

variable [Finite E] (L : LinearSystem V E) {μ : PMF (E × V)}

/-- **Perfect strategies give operator solutions in the state** [Cleve and Mittal][CleveMittal2014]:
if a projective commuting-operator strategy wins the game of a linear constraint system with
certainty, for a question distribution of full support, then Bob's `±1` observables form an
operator solution in the shared state. -/
noncomputable def stateSolution
    (S : CommutingStrategy E V (V → Bool) Bool 𝒜) (hμ : ∀ q, μ q ≠ 0)
    (hA : ∀ e, (S.alice e).IsProjective) (hB : ∀ v, (S.bob v).IsProjective)
    (h : (L.game μ).commutingWinProb S = 1) : L.StateSolution S.state where
  op v := (S.bob v).observable
  isSelfAdjoint v := (S.bob v).isSelfAdjoint_observable
  mul_self v := Measurement.observable_mul_self (hB v)
  commute e u hu w hw := by
    have ag : ∀ v ∈ L.support e, (S.bob v).observable ≈[S.state; 0] S.marginalObservable e v :=
      fun v hv => (S.marginalObservable_approx L hμ h hv).symm
    have hc : ∀ x y, Commute (S.bob x).observable (S.marginalObservable e y) :=
      fun x y => S.commute_observable_marginalObservable e x y
    have mem : ∀ v ∈ [u, w], (S.bob v).observable ≈[S.state; 0] S.marginalObservable e v := by
      intro v hv
      rcases List.mem_pair.mp hv with rfl | rfl
      exacts [ag _ hu, ag _ hw]
    have mem' : ∀ v ∈ [w, u], (S.bob v).observable ≈[S.state; 0] S.marginalObservable e v :=
      fun v hv => mem v (by simp only [List.mem_cons, List.not_mem_nil] at hv ⊢; tauto)
    have t₁ := list_prod_approx (fun v => (S.bob v).observable) (S.marginalObservable e) [u, w]
      mem (fun x _ y _ => hc x y)
    have t₂ := list_prod_approx (fun v => (S.bob v).observable) (S.marginalObservable e) [w, u]
      mem' (fun x _ y _ => hc x y)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at t₁ t₂
    have hcommA : S.marginalObservable e w * S.marginalObservable e u =
        S.marginalObservable e u * S.marginalObservable e w := by
      simp only [marginalObservable, (hA e).sum_smul_mul_sum_smul, mul_comm]
    rw [hcommA] at t₁
    exact (t₁.trans t₂.symm).mono (by norm_num)
  prod_eq e := by
    set l := (L.support e).toList
    have ag : ∀ v ∈ l, (S.bob v).observable ≈[S.state; 0] S.marginalObservable e v :=
      fun v hv => (S.marginalObservable_approx L hμ h (Finset.mem_toList.mp hv)).symm
    have t := list_prod_approx (fun v => (S.bob v).observable) (S.marginalObservable e) l ag
      (fun x _ y _ => S.commute_observable_marginalObservable e x y)
    have hsign : ∀ a : V → Bool, (l.reverse.map fun v => boolSign (a v)).prod =
        boolSign (setParity (L.support e) a) := fun a => by
      rw [List.map_reverse, List.prod_reverse, Finset.prod_map_toList, prod_boolSign_eq]
    have hprod : (l.reverse.map (S.marginalObservable e)).prod =
        ∑ a, boolSign (setParity (L.support e) a) • (S.alice e).effect a := by
      rw [list_prod_marginalObservable e (hA e)]
      simp only [hsign]
    have hsol : ∑ a, boolSign (setParity (L.support e) a) • (S.alice e).effect a ≈[S.state; 0]
        boolSign (L.parity e) • (1 : 𝒜) := by
      have hsum := sum_approx_zero (φ := S.state) univ (fun a =>
          (boolSign (setParity (L.support e) a) - boolSign (L.parity e)) • (S.alice e).effect a)
        fun a _ => by
          by_cases hs : L.Satisfies e a
          · rw [LinearSystem.Satisfies] at hs
            rw [hs, sub_self, zero_smul]
            exact AlgState.approx_self _ _
          · simpa using (S.effect_approx_zero_of_not_satisfies L hμ h hs).smul
              (boolSign (setParity (L.support e) a) - boolSign (L.parity e))
      rw [AlgState.Approx] at hsum ⊢
      convert hsum using 2
      rw [sub_zero, ← (S.alice e).sum_effect, smul_sum, ← sum_sub_distrib]
      simp only [sub_smul]
    rw [hprod] at t
    exact (t.trans hsol).mono (by norm_num)

end CommutingStrategy

end Cslib.PCP
