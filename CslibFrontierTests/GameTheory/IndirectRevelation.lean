/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.Domains
public import CslibFrontier.GameTheory.Mechanism.Indirect
public import CslibFrontier.GameTheory.Mechanism.MultiUnit
public import CslibFrontier.GameTheory.Mechanism.Randomized
public import CslibFrontier.GameTheory.SocialChoice.GibbardSatterthwaiteReduction
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Indirect mechanisms, revelation principles, and multi-unit auctions: client checks

This `module` tests the public surface of:
* `CslibFrontier.GameTheory.SocialChoice.GibbardSatterthwaiteReduction` (single-voter monotonicity
  and Nisan's induced social welfare function on 3-voter majority rule over `Bool`, plus failure of
  single-voter monotonicity for anti-majority rule);
* `CslibFrontier.GameTheory.Mechanism.Domains` (VCG run directly on `Vickrey.singleItemFeasible`
  agreeing with `Vickrey.mechanism` on `![3, 5, 4]`, `toMechanismOn` subtype embedding, and
  separation between `IsIROn` on nonnegative valuations vs `Set.univ`);
* `CslibFrontier.GameTheory.Mechanism.Randomized` (explicit expected-utility and branch-manipulation
  check on `coinFlipMechanism`, plus universal-to-expected truthfulness on a uniform mixture of two
  distinct VCG rules);
* `CslibFrontier.GameTheory.Mechanism.Indirect` (a 2-player incomplete-information game whose
  ex-post Nash equilibrium is not dominant until restricted to `Set.range` via Proposition 9.23,
  dominant-strategy revelation simulation of a proxy/scaled-bid auction, and discrete Bayesian
  revelation simulation via `BayesianGame.ofPMF` and `BayesianMechanism.revelation`);
* `CslibFrontier.GameTheory.Mechanism.MultiUnit` (2-unit, 3-bidder `(k + 1)`-st price vs
  discriminatory `(j + 1)`-st price shading on `![10, 8, 5]`, plus excess supply `k > |ι|`).
-/

@[expose] public section

namespace CslibFrontierTests.GameTheory.IndirectRevelation

open Cslib.GameTheory Cslib.GameTheory.SingleParameter
open Cslib.GameTheory.SocialChoice

/-! ### 1. Nisan's SWF and single-voter monotonicity (`GibbardSatterthwaiteReduction`) -/

section NisanSWF

open SocialChoiceFunction

open Classical in
/-- Three-voter majority rule on `Bool`: `true` wins iff at least two of the three voters rank
`true` above `false`. -/
noncomputable def boolMajority : SocialChoiceFunction (Fin 3) Bool := fun P =>
  decide (2 ≤ (Finset.univ.filter fun i : Fin 3 => (P i).Prefers true false).card)

open Classical in
theorem isSingleMonotone_boolMajority : boolMajority.IsSingleMonotone := by
  intro P Q i hPQ hne
  have hcard_le : ∀ {R S : Profile (Fin 3) Bool},
      (∀ j : Fin 3, (R j).Prefers true false → (S j).Prefers true false) →
      (Finset.univ.filter fun j => (R j).Prefers true false).card ≤
        (Finset.univ.filter fun j => (S j).Prefers true false).card := fun h =>
    Finset.card_le_card fun j hj =>
      Finset.mem_filter.2 ⟨Finset.mem_univ j, h j (Finset.mem_filter.1 hj).2⟩
  cases hP : boolMajority P <;> cases hQ : boolMajority Q
  · exact absurd (hP.trans hQ.symm) hne
  · -- `boolMajority P = false` and `boolMajority Q = true`: voter `i` switched `false ≻ true` to
    -- `true ≻ false`.
    have hcP : (Finset.univ.filter fun j : Fin 3 => (P j).Prefers true false).card < 2 := by
      unfold boolMajority at hP
      exact of_decide_eq_false hP |> not_le.1
    have hcQ : 2 ≤ (Finset.univ.filter fun j : Fin 3 => (Q j).Prefers true false).card := by
      unfold boolMajority at hQ
      exact of_decide_eq_true hQ
    have hPi : ¬ (P i).Prefers true false := fun h => by
      have hle : (Finset.univ.filter fun j : Fin 3 => (Q j).Prefers true false).card ≤
          (Finset.univ.filter fun j : Fin 3 => (P j).Prefers true false).card :=
        hcard_le fun j hj => by
          rcases eq_or_ne j i with rfl | hji
          · exact h
          · rw [hPQ j hji]; exact hj
      omega
    have hQi : (Q i).Prefers true false := by
      by_contra h
      have hle : (Finset.univ.filter fun j : Fin 3 => (Q j).Prefers true false).card ≤
          (Finset.univ.filter fun j : Fin 3 => (P j).Prefers true false).card :=
        hcard_le fun j hj => by
          rcases eq_or_ne j i with rfl | hji
          · exact absurd hj h
          · rw [hPQ j hji]; exact hj
      omega
    exact ⟨(P i).prefers_of_not_prefers Bool.false_ne_true.symm hPi, hQi⟩
  · -- Symmetric case `boolMajority P = true` and `boolMajority Q = false`.
    have hcP : 2 ≤ (Finset.univ.filter fun j : Fin 3 => (P j).Prefers true false).card := by
      unfold boolMajority at hP
      exact of_decide_eq_true hP
    have hcQ : (Finset.univ.filter fun j : Fin 3 => (Q j).Prefers true false).card < 2 := by
      unfold boolMajority at hQ
      exact of_decide_eq_false hQ |> not_le.1
    have hQi : ¬ (Q i).Prefers true false := fun h => by
      have hle : (Finset.univ.filter fun j : Fin 3 => (P j).Prefers true false).card ≤
          (Finset.univ.filter fun j : Fin 3 => (Q j).Prefers true false).card :=
        hcard_le fun j hj => by
          rcases eq_or_ne j i with rfl | hji
          · exact h
          · rw [← hPQ j hji]; exact hj
      omega
    have hPi : (P i).Prefers true false := by
      by_contra h
      have hle : (Finset.univ.filter fun j : Fin 3 => (P j).Prefers true false).card ≤
          (Finset.univ.filter fun j : Fin 3 => (Q j).Prefers true false).card :=
        hcard_le fun j hj => by
          rcases eq_or_ne j i with rfl | hji
          · exact absurd hj h
          · rw [← hPQ j hji]; exact hj
      omega
    exact ⟨hPi, (Q i).prefers_of_not_prefers Bool.false_ne_true.symm hQi⟩
  · exact absurd (hP.trans hQ.symm) hne

open Classical in
theorem surjective_boolMajority : Function.Surjective boolMajority := by
  obtain ⟨r⟩ := Ranking.nonempty Bool
  intro b
  cases b
  · refine ⟨fun _ => r.toTop false, ?_⟩
    unfold boolMajority
    have hempty : (Finset.univ.filter fun i : Fin 3 =>
        ((r.toTop false).Prefers true false)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro _ _
      exact (r.toTop false).asymm (r.isTop_toTop false true Bool.false_ne_true.symm)
    rw [hempty, Finset.card_empty]
    decide
  · refine ⟨fun _ => r.toTop true, ?_⟩
    unfold boolMajority
    have huniv : (Finset.univ.filter fun i : Fin 3 =>
        ((r.toTop true).Prefers true false)) = Finset.univ := by
      rw [Finset.filter_true_of_mem]
      intro _ _
      exact r.isTop_toTop true false Bool.false_ne_true
    rw [huniv, Finset.card_univ, Fintype.card_fin]
    decide

open Classical in
theorem not_isDictatorial_boolMajority : ¬ boolMajority.IsDictatorial := by
  rintro ⟨i, hi⟩
  obtain ⟨r⟩ := Ranking.nonempty Bool
  let rTrue := r.toTop true
  let rFalse := r.toTop false
  let P : Profile (Fin 3) Bool := fun j => if j = i then rTrue else rFalse
  have hcard : (Finset.univ.filter fun j : Fin 3 => (P j).Prefers true false).card = 1 := by
    have hset : (Finset.univ.filter fun j : Fin 3 => (P j).Prefers true false) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, P]
      rcases eq_or_ne j i with rfl | hj
      · simp only [↓reduceIte, iff_true]
        exact r.isTop_toTop true false Bool.false_ne_true
      · rw [ite_eq_right hj]
        exact iff_of_false (rFalse.asymm (r.isTop_toTop false true Bool.false_ne_true.symm)) hj
    rw [hset, Finset.card_singleton]
  have hP : boolMajority P = false := by
    unfold boolMajority
    rw [hcard]
    decide
  have hpref : (P i).Prefers false true := by
    have := hi P true (surjective_boolMajority true)
    rw [hP] at this
    exact this Bool.false_ne_true.symm
  have htop : (P i).Prefers true false := by
    simp only [P, ↓reduceIte]
    exact r.isTop_toTop true false Bool.false_ne_true
  exact (P i).asymm htop hpref

/-- Nonvacuity of Nisan's Lemmas 9.10–9.11: on two alternatives (`Bool`), 3-voter majority rule is
single-voter monotone, strategy-proof, onto, and non-dictatorial, and its `nisanSWF` is an
antisymmetric Pareto IIA social welfare function with no dictator (showing Arrow's `|A| ≥ 3`
hypothesis is what rules this out for three or more alternatives). -/
example :
    let hf := isSingleMonotone_iff_isStrategyProof.1 isSingleMonotone_boolMajority
    let F := boolMajority.nisanSWF hf surjective_boolMajority
    F.IsPareto ∧ F.IsIIA ∧ ¬ F.IsDictatorial ∧
      ∀ P a b, (F P).AtLeast a b → (F P).AtLeast b a → a = b := by
  intro hf F
  obtain ⟨hPar, hIIA, hND⟩ :=
    nisanSWF_isPareto_and_isIIA_and_not_isDictatorial hf surjective_boolMajority
      not_isDictatorial_boolMajority
  exact ⟨hPar, hIIA, hND, fun P _ _ => nisanSWF_antisymm hf surjective_boolMajority P⟩

/-- Anti-majority rule (`fun P => !(boolMajority P)`) fails single-voter monotonicity: switching one
voter on a unanimous `false` profile still chooses `true`, and switching a second voter flips the
outcome from `true` to `false` when that voter prefers `true` to `false`. -/
example : ¬ (SocialChoiceFunction.IsSingleMonotone fun P => !(boolMajority P)) := by
  classical
  intro hm
  obtain ⟨r⟩ := Ranking.nonempty Bool
  let rT := r.toTop true
  let rF := r.toTop false
  let P : Profile (Fin 3) Bool := ![rT, rF, rF]
  let Q : Profile (Fin 3) Bool := ![rT, rT, rF]
  have hPQ : ∀ j : Fin 3, j ≠ 1 → P j = Q j := by
    intro j hj
    fin_cases j
    · rfl
    · exact absurd rfl hj
    · rfl
  have hP : boolMajority P = false := by
    unfold boolMajority
    have hset : (Finset.univ.filter fun j : Fin 3 => (P j).Prefers true false) = {0} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      fin_cases j
      · simp only [P, Matrix.cons_val_zero, Fin.zero_eta, iff_true]
        exact r.isTop_toTop true false Bool.false_ne_true
      · simp only [P, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.mk_one,
          show (1 : Fin 3) ≠ 0 by decide, iff_false]
        exact rF.asymm (r.isTop_toTop false true Bool.false_ne_true.symm)
      · exact iff_of_false (rF.asymm (r.isTop_toTop false true Bool.false_ne_true.symm))
          (by decide)
    rw [hset, Finset.card_singleton]
    decide
  have hQ : boolMajority Q = true := by
    unfold boolMajority
    have hsub : ({0, 1} : Finset (Fin 3)) ⊆
        Finset.univ.filter fun j : Fin 3 => (Q j).Prefers true false := by
      intro j hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ j, ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact r.isTop_toTop true false Bool.false_ne_true
      · exact r.isTop_toTop true false Bool.false_ne_true
    have hcard := Finset.card_le_card hsub
    have hpair : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
    rw [hpair] at hcard
    exact decide_eq_true hcard
  have hne : (!(boolMajority P)) ≠ (!(boolMajority Q)) := by rw [hP, hQ]; decide
  have hstep := (hm (P := P) (Q := Q) 1 hPQ hne).2
  dsimp only at hstep
  rw [hP, hQ] at hstep
  exact rT.asymm (r.isTop_toTop true false Bool.false_ne_true) hstep

end NisanSWF

/-! ### 2. Restricted domains and `singleItemFeasible` VCG bridge (`Domains`) -/

section DomainsBridge

/-- VCG run directly on `Vickrey.singleItemFeasible` (pulled back along `Subtype.val`) agrees with
`Vickrey.mechanism` on `![3, 5, 4]`: bidder `1` gets `1` and pays `4`, while `0` and `2` pay `0`. -/
example :
    let M := (Mechanism.vcg (Vickrey.vcgOutcome (ι := Fin 3))).toSingleParameter Subtype.val
    let b : Fin 3 → ℝ := ![3, 5, 4]
    M.allocation b 1 = 1 ∧ M.payment b 1 = 4 ∧ M.payment b 0 = 0 ∧ M.payment b 2 = 0 := by
  intro M b
  have hb : 0 ≤ b := fun i => by fin_cases i <;> norm_num [b]
  have hw : Vickrey.Wins b 1 := by
    intro j hj
    fin_cases j
    · norm_num [b]
    · exact absurd rfl hj
    · norm_num [b]
  rw [show M.allocation b = Vickrey.mechanism.allocation b from
        Vickrey.vcg_singleItemFeasible_allocation hb,
      show M.payment b = Vickrey.mechanism.payment b from
        Vickrey.vcg_singleItemFeasible_payment hb]
  refine ⟨Vickrey.allocation_eq_one_iff.2 hw, ?_, ?_, ?_⟩
  · change Vickrey.highestOtherBid b 1 * Vickrey.allocation b 1 = 4
    rw [Vickrey.allocation_eq_one_iff.2 hw, mul_one]
    refine le_antisymm (Vickrey.highestOtherBid_le_iff.2 ⟨by norm_num, fun j hj => ?_⟩) ?_
    · fin_cases j
      · norm_num [b]
      · exact absurd rfl hj
      · norm_num [b]
    · exact le_of_eq_of_le (by norm_num [b])
        (Vickrey.le_highestOtherBid (b := b) (i := 1) (j := 2) (by decide))
  · change Vickrey.highestOtherBid b 0 * Vickrey.allocation b 0 = 0
    rw [Vickrey.allocation_eq_zero_iff.2 fun h => absurd (h.unique hw) (by decide), mul_zero]
  · change Vickrey.highestOtherBid b 2 * Vickrey.allocation b 2 = 0
    rw [Vickrey.allocation_eq_zero_iff.2 fun h => absurd (h.unique hw) (by decide), mul_zero]

/-- Embedding `Vickrey.mechanism` into `Mechanism (Fin 2) Vickrey.singleItemFeasible` via
`toMechanismOn` yields a DSIC and IR direct mechanism on `Mechanism.linearDomain Subtype.val`. -/
example :
    let hfeas : ∀ b : Fin 2 → ℝ, 0 ≤ b →
        Vickrey.mechanism.allocation b ∈ Vickrey.singleItemFeasible :=
      fun b _ => Vickrey.allocation_mem_singleItemFeasible b
    let M := Vickrey.mechanism.toMechanismOn hfeas
    M.IsDSICOn (Mechanism.linearDomain Subtype.val) ∧
      M.IsIROn (Mechanism.linearDomain Subtype.val) := by
  intro hfeas M
  have hne : ∀ i : Fin 2, ∃ ω ∈ Vickrey.singleItemFeasible (ι := Fin 2), ω i ≠ 0 :=
    fun i => ⟨(Vickrey.singleWinner i).val, (Vickrey.singleWinner i).property,
      by simp only [Vickrey.singleWinner_apply_self]; norm_num⟩
  exact ⟨(Vickrey.mechanism.isDSIC_iff_isDSICOn_toMechanismOn hfeas hne).1 Vickrey.mechanism_isDSIC,
    (Vickrey.mechanism.isIR_iff_isIROn_toMechanismOn hfeas hne).1 Vickrey.mechanism_isIR⟩

/-- Why `Mechanism.vcg_isIROn` requires nonnegative valuations on `V`: for the single-outcome rule
`fun _ => ()` on `Unit`, VCG is `IsIROn` on `{v | 0 ≤ v}` (`vcg_isIROn`), yet fails `IsIROn` on
`Set.univ` because a negative valuation `fun _ => -1` gets utility `-1 < 0`. -/
example :
    let f : (Unit → Unit → ℝ) → Unit := fun _ => ()
    (Mechanism.vcg f).IsIROn (fun _ => {v : Unit → ℝ | 0 ≤ v}) ∧
      ¬ (Mechanism.vcg f).IsIROn (fun _ => Set.univ) := by
  intro f
  have hwm : Mechanism.IsWelfareMaximizingOn f (fun _ => {v : Unit → ℝ | 0 ≤ v}) := by
    intro b _ ω
    cases ω
    exact le_rfl
  refine ⟨Mechanism.vcg_isIROn hwm fun _ _ hv => hv, fun hIR => ?_⟩
  have h := hIR () (fun _ _ => -1) (fun _ => Set.mem_univ _)
  have hpiv : Mechanism.clarkePivot (Ω := Unit) () (fun _ _ => (-1 : ℝ)) = 0 := by
    have hempty : (Finset.univ : Finset Unit).erase () = ∅ := by decide
    refine le_antisymm (Finset.sup'_le _ _ fun _ _ => ?_) ?_
    · rw [hempty, Finset.sum_empty]
    · have := Finset.le_sup' (fun ω : Unit => ∑ j ∈ (Finset.univ : Finset Unit).erase (), (-1 : ℝ))
        (Finset.mem_univ ())
      rwa [hempty, Finset.sum_empty] at this
  have hpay : (Mechanism.vcg f).payment (fun _ _ => (-1 : ℝ)) () = 0 := by
    change Mechanism.clarkePivot () _ - ∑ j ∈ (Finset.univ : Finset Unit).erase (), (-1 : ℝ) = 0
    have hempty : (Finset.univ : Finset Unit).erase () = ∅ := by decide
    rw [hpiv, hempty, Finset.sum_empty, sub_zero]
  simp only [Cslib.GameTheory.Mechanism.utility, f, hpay, sub_zero] at h
  norm_num at h

end DomainsBridge

/-! ### 3. Randomized mechanisms (`Randomized`) -/

section RandomizedChecks

/-- Concrete evaluation of `coinFlipMechanism`: for `v = (10, 4)`, expected utility is `6` at every
reported profile (hence `IsTruthfulInExpectation`), whereas on `coinFlipBranch true` misreporting
`(0, 5)` increases ex-post utility from `8` to `10`. -/
example :
    let v : Bool → ℝ := fun c => if c then 10 else 4
    let misreport : Unit → Bool → ℝ := fun _ c => if c then 0 else 5
    RandomizedMechanism.coinFlipMechanism.expectedUtility () v misreport = 6 ∧
      RandomizedMechanism.coinFlipMechanism.expectedUtility () v (fun _ => v) = 6 ∧
      (RandomizedMechanism.coinFlipBranch true).utility () v (fun _ => v) = 8 ∧
      (RandomizedMechanism.coinFlipBranch true).utility () v misreport = 10 := by
  intro v misreport
  rw [RandomizedMechanism.coinFlipMechanism_expectedUtility,
    RandomizedMechanism.coinFlipMechanism_expectedUtility]
  simp only [Cslib.GameTheory.Mechanism.utility, RandomizedMechanism.coinFlipBranch, v, misreport]
  norm_num

/-- Constant outcome mechanism with zero payment on `Bool` for testing randomized mixtures. -/
noncomputable def constZeroMech (c : Bool) : Mechanism (Fin 2) Bool where
  outcome _ := c
  payment _ _ := 0

theorem constZeroMech_injective : Function.Injective constZeroMech := by
  intro c₁ c₂ h
  exact congrArg (fun M => M.outcome 0) h

/-- Nonvacuity of `IsUniversallyDSICOn.isTruthfulInExpectationOn_of_support_finite` on a genuine
2-branch mixture (not a point mass): tossing a fair coin between two constant zero-payment
mechanisms (`true` vs `false`) has support of size `2`, is universally DSIC, and is therefore
truthful in expectation. -/
example :
    let R : RandomizedMechanism (Fin 2) Bool :=
      ⟨(Cslib.Probability.PMF.uniformOfFintype Bool).map constZeroMech⟩
    constZeroMech true ≠ constZeroMech false ∧
      R.IsUniversallyDSIC ∧ R.IsTruthfulInExpectation := by
  intro R
  have hne : constZeroMech true ≠ constZeroMech false :=
    fun h => Bool.noConfusion (constZeroMech_injective h)
  have hsupp : R.dist.support = {constZeroMech true, constZeroMech false} := by
    ext M
    simp only [R, PMF.support_map, Set.mem_image,
      Cslib.Probability.PMF.mem_support_uniformOfFintype, true_and, Bool.exists_bool,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hU : R.IsUniversallyDSIC := by
    intro M hM i b v _ _
    rw [hsupp, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl <;>
      simp only [Cslib.GameTheory.Mechanism.utility, constZeroMech, le_rfl]
  have hfin : R.dist.support.Finite := by
    rw [hsupp]
    exact (Set.finite_singleton _).insert _
  exact ⟨hne, hU, hU.isTruthfulInExpectationOn_of_support_finite hfin⟩

end RandomizedChecks

/-! ### 4. Incomplete-information games and Revelation Principles (`Indirect`) -/

section RevelationChecks

/-- A 2-player incomplete-information game with types `Bool` and actions `Fin 3` separating
`IsExPostNash` from `IsDominantStrategyEquilibrium` and illustrating **Proposition 9.23**:
action `2` is never played under `s i b = if b then 1 else 0`, so `s` is ex-post Nash; yet if the
opponent played `2`, only `2` would pay `1 > 0`, so `s` is **not** dominant until the action spaces
are restricted to `Set.range (s i) = {0, 1}` via `restrictRange`. -/
def spoilerGame : IncompleteInfoGame (Fin 2) (fun _ => Bool) (fun _ => Fin 3) where
  utility i ti x :=
    if x (1 - i) = 2 then (if x i = 2 then 1 else 0)
    else if x i = (if ti then 1 else 0) then 2 else 0

/-- Truth-revealing encoding of `Bool` into `Fin 3`, omitting action `2` from its range. -/
def boolToFin3 (b : Bool) : Fin 3 := if b then 1 else 0

example :
    spoilerGame.IsExPostNash (fun _ => boolToFin3) ∧
      ¬ spoilerGame.IsDominantStrategyEquilibrium (fun _ => boolToFin3) ∧
      (spoilerGame.restrictRange (fun _ => boolToFin3)).IsDominantStrategyEquilibrium
        (fun _ t => ⟨boolToFin3 t, ⟨t, rfl⟩⟩) := by
  have hEx : spoilerGame.IsExPostNash (fun _ => boolToFin3) := by
    intro i t xi'
    have hopp : boolToFin3 (t (1 - i)) ≠ 2 := by
      cases t (1 - i) <;> decide
    have hne_i : 1 - i ≠ i := by fin_cases i <;> decide
    simp only [spoilerGame, Function.update_self, Function.update_of_ne hne_i]
    rw [ite_eq_right hopp, ite_eq_right hopp]
    simp only [boolToFin3]
    split_ifs <;> norm_num
  have hNotDom : ¬ spoilerGame.IsDominantStrategyEquilibrium (fun _ => boolToFin3) := by
    intro hDom
    have h := hDom 0 false (fun _ => 2)
    simp only [spoilerGame, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 2) - 0 ≠ 0), boolToFin3] at h
    norm_num at h
  exact ⟨hEx, hNotDom, hEx.isDominantStrategyEquilibrium_restrictRange⟩

/-- **Dominant-Strategy Revelation Principle (Proposition 9.25)** on a scaled-signal single-item
auction: each bidder `i : Fin 2` submits a signal `xᵢ : ℝ` interpreted as twice its valuation, and
the highest-signal bidder wins and pays half the opponent's signal. Doubling one's true value
(`s i v = 2 * v`) is a dominant-strategy equilibrium, whereas unscaled reporting (`id`) is not;
`revelation s` turns this indirect mechanism into a truthful direct mechanism charging exact
second-price payments. -/
noncomputable def doubledSignalAuction : IndirectMechanism (Fin 2) (fun _ => ℝ) (Fin 2) where
  outcome x := if x 1 ≤ x 0 then 0 else 1
  payment x i := if (if x 1 ≤ x 0 then (0 : Fin 2) else 1) = i then x (1 - i) / 2 else 0

/-- Two-bidder single-item valuation: value `v` if `winner = i`, and `0` otherwise. -/
def twoBidderSingleItemVal (i : Fin 2) (v : ℝ) (winner : Fin 2) : ℝ :=
  if winner = i then v else 0

theorem doubledSignalAuction_equilibrium :
    (doubledSignalAuction.toIncompleteInfoGame twoBidderSingleItemVal).IsDominantStrategyEquilibrium
      (fun _ v => 2 * v) := by
  intro i v x
  dsimp only at x
  fin_cases i
  · have h10 : (1 : Fin 2) - 0 = 1 := by decide
    simp only [Fin.zero_eta, IndirectMechanism.toIncompleteInfoGame, doubledSignalAuction,
      twoBidderSingleItemVal, h10, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
    by_cases h1 : x 1 ≤ x 0 <;> by_cases h2 : x 1 ≤ 2 * v <;>
      simp only [h1, h2, ↓reduceIte, Fin.reduceEq] <;> linarith
  · have h11 : (1 : Fin 2) - 1 = 0 := by decide
    simp only [Fin.mk_one, IndirectMechanism.toIncompleteInfoGame, doubledSignalAuction,
      twoBidderSingleItemVal, h11, Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    by_cases h1 : x 1 ≤ x 0 <;> by_cases h2 : 2 * v ≤ x 0 <;>
      simp only [h1, h2, ↓reduceIte, Fin.reduceEq] <;> linarith

example :
    let s : Fin 2 → ℝ → ℝ := fun _ v => 2 * v
    let D := doubledSignalAuction.revelation s
    ¬ (doubledSignalAuction.toIncompleteInfoGame twoBidderSingleItemVal).IsExPostNash
        (fun _ => id) ∧
      D.IsTruthful twoBidderSingleItemVal ∧
      D.outcome ![3, 5] = 1 ∧ D.payment ![3, 5] 1 = 3 ∧ D.payment ![3, 5] 0 = 0 := by
  intro s D
  have hNotId : ¬ (doubledSignalAuction.toIncompleteInfoGame twoBidderSingleItemVal).IsExPostNash
      (fun _ => id) := by
    intro hEx
    -- At `t = ![4, 5]`, if player `0` plays `4` (`id`) and `1` plays `5`, player `1` wins (`5 > 4`)
    -- and pays `4 / 2 = 2` (so player `0` gets `0`), whereas if player `0` bids `6`, player `0`
    -- wins at price `5 / 2 = 2.5` for utility `4 - 2.5 = 1.5 > 0`!
    have h := hEx 0 ![4, 5] 6
    simp only [IndirectMechanism.toIncompleteInfoGame, doubledSignalAuction,
      twoBidderSingleItemVal, Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), id_eq] at h
    norm_num at h
  refine ⟨hNotId, doubledSignalAuction.revelation_isTruthful doubledSignalAuction_equilibrium,
    ?_, ?_, ?_⟩
  · simp only [D, IndirectMechanism.revelation, doubledSignalAuction, s]
    norm_num
  · simp only [D, IndirectMechanism.revelation, doubledSignalAuction, s]
    norm_num
  · simp only [D, IndirectMechanism.revelation, doubledSignalAuction, s]
    norm_num

/-- **Bayesian Revelation Principle (Proposition 9.44)** on a discrete `BayesianMechanism` built
from `PMF` priors: one buyer (`Unit`) has valuation `4` (`true`) or `0` (`false`) under a uniform
prior on `Bool`, and submits an inverted bit `x : Bool` where `false` buys the item at posted price
`1` and `true` declines (`0`). Playing `s _ b := !b` is a Bayes–Nash equilibrium (while `id` is
not), and `M.revelation s` is truthful in the Bayesian sense with identical interim payments. -/
noncomputable def invertedPostedPrice :
    BayesianMechanism Unit (fun _ => Bool) (fun _ => Bool) Bool where
  outcome x := !(x ())
  payment x _ := if !(x ()) then 1 else 0
  prior _ := (Cslib.Probability.PMF.uniformOfFintype Bool).toMeasure
  valuation _ t ω := if t && ω then 4 else 0

example :
    let s : Unit → Bool → Bool := fun _ b => !b
    invertedPostedPrice.toBayesianGame.IsBayesNash s ∧
      ¬ invertedPostedPrice.toBayesianGame.IsBayesNash (fun _ => id) ∧
      (invertedPostedPrice.revelation s).IsTruthful ∧
      (invertedPostedPrice.revelation s).interimPayment (fun _ => id) () true =
        invertedPostedPrice.interimPayment s () false := by
  intro s
  have hprob : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.pi invertedPostedPrice.prior) := by
    dsimp only [invertedPostedPrice]
    infer_instance
  have hutil : ∀ (σ : Unit → Bool → Bool) (ti xi : Bool),
      invertedPostedPrice.toBayesianGame.interimUtility σ () ti xi =
        (if ti && !xi then 4 else 0) - (if !xi then 1 else 0) := by
    intro σ ti xi
    simp only [BayesianGame.interimUtility, BayesianMechanism.toBayesianGame,
      IndirectMechanism.toIncompleteInfoGame, invertedPostedPrice, Function.update_self,
      MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  have hBN : invertedPostedPrice.toBayesianGame.IsBayesNash s := by
    rw [BayesianGame.isBayesNash_iff]
    intro i ti xi'
    cases i
    rw [hutil, hutil]
    cases ti <;> cases xi' <;> simp only [s] <;> norm_num
  have hNotId : ¬ invertedPostedPrice.toBayesianGame.IsBayesNash (fun _ => id) := by
    rw [BayesianGame.isBayesNash_iff]
    intro h
    have := h () true false
    rw [hutil, hutil] at this
    norm_num [id_eq] at this
  exact ⟨hBN, hNotId, BayesianMechanism.revelation_isTruthful hBN,
    BayesianMechanism.revelation_interimPayment_eq invertedPostedPrice s () true⟩

end RevelationChecks

/-! ### 5. Multi-unit `k`-item auctions (`MultiUnit`) -/

section MultiUnitChecks

open SingleParameter.MultiUnit

/-- **2-unit, 3-bidder `(k + 1)`-st price vs discriminatory `(j + 1)`-st price** ([Nisan2007],
§9.3.5.4, p. 221):
on bids `b = ![10, 8, 5]`, bidders `0` and `1` win one item each;
* under `MultiUnit.mechanism 2`, both winners pay the 3rd-highest bid `5`, and the auction is DSIC,
  IR, and welfare-maximizing;
* under `MultiUnit.nextBidMechanism 2`, bidder `0` (with true value `10`) pays the 2nd-highest bid
  `8` for utility `2`, whereas shading to `![6, 8, 5]` drops bidder `0` to 2nd place (`rank = 1`,
  still winning!) at price `5` for utility `5 > 2`, witnessing `¬ (nextBidMechanism 2).IsDSIC`. -/
example :
    let b : Fin 3 → ℝ := ![10, 8, 5]
    let bShaded : Fin 3 → ℝ := ![6, 8, 5]
    allocation 2 b 0 = 1 ∧ allocation 2 b 1 = 1 ∧ allocation 2 b 2 = 0 ∧
      (mechanism 2).payment b 0 = 5 ∧ (mechanism 2).payment b 1 = 5 ∧
      (mechanism 2).payment b 2 = 0 ∧
      (mechanism (ι := Fin 3) 2).IsDSIC ∧ (mechanism (ι := Fin 3) 2).IsIR ∧
      (nextBidMechanism 2).utility 0 10 b = 2 ∧
      (nextBidMechanism 2).utility 0 10 bShaded = 5 ∧
      ¬ (nextBidMechanism (ι := Fin 3) 2).IsDSIC := by
  classical
  intro b bShaded
  have hb0 : 0 ≤ b := fun i => by fin_cases i <;> norm_num [b]
  have hbS0 : 0 ≤ bShaded := fun i => by fin_cases i <;> norm_num [bShaded]
  have hr0 : rank b 0 = 0 := rank_eq_zero_of_gt fun j hj => by
    fin_cases j <;> first | exact absurd rfl hj | norm_num [b]
  have hr1 : rank b 1 = 1 :=
    rank_eq_one_of_between (top := 0) (by norm_num [b]) fun j hj1 hj0 => by
      fin_cases j <;> first | exact absurd rfl hj0 | exact absurd rfl hj1 | norm_num [b]
  have hr2 : rank b 2 = 2 := by
    have hset : (Finset.univ.filter fun j : Fin 3 => Beats b j 2) = {0, 1} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      fin_cases j <;> simp only [Beats, b, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceEq] <;> norm_num
    rw [rank, hset]
    decide
  have hrS0 : rank bShaded 0 = 1 :=
    rank_eq_one_of_between (top := 1) (by norm_num [bShaded]) fun j hj0 hj1 => by
      fin_cases j <;> first | exact absurd rfl hj0 | exact absurd rfl hj1 | norm_num [bShaded]
  have hrS2 : rank bShaded 2 = 2 := by
    have hset : (Finset.univ.filter fun j : Fin 3 => Beats bShaded j 2) = {0, 1} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      fin_cases j <;> simp only [Beats, bShaded, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceEq] <;> norm_num
    rw [rank, hset]
    decide
  have ha0 : allocation 2 b 0 = 1 := allocation_eq_one_iff.2 (by rw [Wins, hr0]; omega)
  have ha1 : allocation 2 b 1 = 1 := allocation_eq_one_iff.2 (by rw [Wins, hr1]; omega)
  have ha2 : allocation 2 b 2 = 0 := allocation_eq_zero_iff.2 (by rw [Wins, hr2]; omega)
  have haS0 : allocation 2 bShaded 0 = 1 := allocation_eq_one_iff.2 (by rw [Wins, hrS0]; omega)
  have hbRank2 : bidAtRank 2 b = 5 := by
    rw [bidAtRank_eq_of_rank_nonneg hb0 hr2]
    norm_num [b]
  have hbRank1 : bidAtRank 1 b = 8 := by
    rw [bidAtRank_eq_of_rank_nonneg hb0 hr1]
    norm_num [b]
  have hbSRank2 : bidAtRank 2 bShaded = 5 := by
    rw [bidAtRank_eq_of_rank_nonneg hbS0 hrS2]
    norm_num [bShaded]
  refine ⟨ha0, ha1, ha2, ?_, ?_, ?_, mechanism_isDSIC 2, mechanism_isIR 2, ?_, ?_,
    not_isDSIC_nextBidMechanism (by omega) (by rw [Fintype.card_fin]; omega)⟩
  · simp only [mechanism, hbRank2, ha0, mul_one]
  · simp only [mechanism, hbRank2, ha1, mul_one]
  · simp only [mechanism, ha2, mul_zero]
  · simp only [SingleParameter.Mechanism.utility, nextBidMechanism, hr0, zero_add, hbRank1, ha0]
    norm_num
  · simp only [SingleParameter.Mechanism.utility, nextBidMechanism, hrS0, hbSRank2, haS0]
    norm_num

/-- Excess-supply edge case (`Fintype.card ι ≤ k`): with `3` identical items and `2` bidders bidding
`![7, 4]`, both bidders win an item and both pay `0`. -/
example :
    let b : Fin 2 → ℝ := ![7, 4]
    allocation 3 b 0 = 1 ∧ allocation 3 b 1 = 1 ∧
      (mechanism 3).payment b 0 = 0 ∧ (mechanism 3).payment b 1 = 0 := by
  intro b
  have ha : ∀ i : Fin 2, allocation 3 b i = 1 := fun i =>
    allocation_eq_one_iff.2 ((rank_lt_card b i).trans_le (by rw [Fintype.card_fin]; omega))
  have hp : bidAtRank 3 b = 0 := bidAtRank_of_card_le b (by rw [Fintype.card_fin]; omega)
  exact ⟨ha 0, ha 1, by simp only [mechanism, hp, zero_mul],
    by simp only [mechanism, hp, zero_mul]⟩

end MultiUnitChecks

end CslibFrontierTests.GameTheory.IndirectRevelation
