/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.GameTheory.Mechanism.Roberts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for taxation principle, weak/cyclic monotonicity, and Roberts' theorem

Concrete witnesses covering every positive theorem and boundary/failure case of
`CslibFrontier.GameTheory.Mechanism.Taxation` and `CslibFrontier.GameTheory.Mechanism.Roberts`:

* **Taxation principle** ([Nisan2007], Proposition 9.27): concrete price extraction and a non-DSIC
  constant-outcome mechanism with report-dependent payments that fails both DSIC and taxation.
* **Weighted Groves** ([Nisan2007], Proposition 9.31): concrete two-agent, three-outcome affine
  maximizer with strict weights `w = ![2, 1]` and outcome boosts `c = ![0, 1, 2]`, checking
  concrete outcome and payments.
* **Negative weight counterexample** (omitted constraint `kᵢ ≥ 0` in [Lavi2007], Definition 12.23):
  `argmin` (`w = ![-1]`) fails weak monotonicity and is not DSIC-implementable.
* **Non-convex WMON vs. cyclic monotonicity**: rock–paper–scissors 3-point domain satisfying
  `IsWeaklyMonotoneOn` (all 2-cycles nonnegative) yet failing `IsCyclicallyMonotoneOn` (a negative
  3-cycle summing to `-3`), hence not DSIC-implementable ([Nisan2007], p. 227 remark).
* **Dictatorship witness** (literal slip `wᵢ ∈ ℝ⁺` in [Nisan2007], Definition 9.30): a two-agent,
  three-outcome dictatorship is neutral, surjective, DSIC (with zero payments), and an affine
  maximizer with `w = ![1, 0]`, yet admits **no** representation with strictly positive weights.
* **Zero-weight adverse tie-breaking**: an affine maximizer with `w = ![1, 0]` that breaks ties of
  agent `0` against agent `1` satisfies `IsAffineMaximizerFor` yet fails WMON and implementability,
  showing why `weightedGroves_isDSIC_of_nonneg` requires weight-zero agents to be dummies.
* **Exercise 12.6** ([Lavi2007], p. 329): a two-agent, four-outcome finite domain admitting a DSIC
  mechanism (hence `IsPADOn`) that violates `IsGeneralizedWMONOn`.
* **Tightness of `|Ω| ≥ 3` in Roberts' theorem**: the `AND` rule on `Bool` for two agents is
  surjective and DSIC (with zero payments) yet is not an affine maximizer.
* **Nonvacuity**: concrete instantiations of Roberts' theorem (surjective, neutral, and finite-range
  non-surjective on `Fin 4` with image `{0, 1, 2}`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.Roberts

open Cslib.GameTheory Cslib.GameTheory.Mechanism

/-! ### Helper: deterministic argmax over `Fin 3` -/

private noncomputable def argmax3 (s : Fin 3 → ℝ) : Fin 3 :=
  if s 1 ≤ s 0 ∧ s 2 ≤ s 0 then 0 else if s 2 ≤ s 1 then 1 else 2

private theorem le_argmax3 (s : Fin 3 → ℝ) (k : Fin 3) : s k ≤ s (argmax3 s) := by
  simp only [argmax3]
  split_ifs with h0 h1
  · fin_cases k
    · exact le_rfl
    · exact h0.1
    · exact h0.2
  · fin_cases k
    · by_contra hlt
      exact h0 ⟨not_le.1 hlt |>.le, h1.trans (not_le.1 hlt |>.le)⟩
    · exact le_rfl
    · exact h1
  · fin_cases k
    · by_contra hlt
      have hs0 : s 2 ≤ s 0 := not_le.1 hlt |>.le
      have hs1 : s 1 < s 2 := not_le.1 h1
      exact h0 ⟨hs1.le.trans hs0, hs0⟩
    · exact (not_le.1 h1).le
    · exact le_rfl

private theorem argmax3_eq_of_strict {s : Fin 3 → ℝ} {x : Fin 3}
    (hx : ∀ y, y ≠ x → s y < s x) : argmax3 s = x := by
  by_contra hne
  have hle := le_argmax3 s x
  have hlt := hx (argmax3 s) hne
  linarith

/-! ### Weighted Groves with `w = ![2, 1]`, `c = ![0, 1, 2]` (Proposition 9.31) -/

private def weights21 : Fin 2 → ℝ := ![2, 1]
private def boosts012 : Fin 3 → ℝ := ![0, 1, 2]

private noncomputable def weightedRule21 (b : Fin 2 → Fin 3 → ℝ) : Fin 3 :=
  argmax3 (affineScore weights21 boosts012 b)

private theorem weightedRule21_isAffine :
    IsAffineMaximizerFor weightedRule21 Set.univ weights21 boosts012 := fun b =>
  ⟨Set.mem_univ _, fun ω _ => le_argmax3 (affineScore weights21 boosts012 b) ω⟩

private theorem weights21_pos : ∀ i : Fin 2, 0 < weights21 i := fun i => by
  fin_cases i <;> norm_num [weights21]

private noncomputable def weightedMech21 : Mechanism (Fin 2) (Fin 3) :=
  weightedGroves weightedRule21 weights21 boosts012 (fun _ _ => 0)

/-- The weighted Groves mechanism with `w = (2, 1)` and `c = (0, 1, 2)` is DSIC and chooses the
expected outcome and payments on `b₀ = (1, 0, 2)`, `b₁ = (3, 1, 0)`. -/
theorem weightedMech21_spec :
    weightedMech21.IsDSIC ∧
      let b : Fin 2 → Fin 3 → ℝ := ![![1, 0, 2], ![3, 1, 0]]
      weightedMech21.outcome b = 2 ∧
        weightedMech21.payment b 0 = -1 ∧
        weightedMech21.payment b 1 = -6 := by
  have hdsic : weightedMech21.IsDSIC :=
    weightedGroves_isDSIC weightedRule21_isAffine weights21_pos fun _ _ _ => rfl
  refine ⟨hdsic, ?_⟩
  let b : Fin 2 → Fin 3 → ℝ := ![![1, 0, 2], ![3, 1, 0]]
  have h0 : affineScore weights21 boosts012 b 0 = 5 := by
    simp [affineScore, weights21, boosts012, b, Fin.sum_univ_two]; norm_num
  have h1 : affineScore weights21 boosts012 b 1 = 2 := by
    simp [affineScore, weights21, boosts012, b, Fin.sum_univ_two]; norm_num
  have h2 : affineScore weights21 boosts012 b 2 = 6 := by
    simp [affineScore, weights21, boosts012, b, Fin.sum_univ_two]; norm_num
  have hr : weightedRule21 b = 2 :=
    argmax3_eq_of_strict fun y hy => by
      fin_cases y
      · dsimp only [Fin.zero_eta, Fin.isValue]; linarith
      · dsimp only [Fin.mk_one, Fin.isValue]; linarith
      · exact absurd rfl hy
  have hout : weightedMech21.outcome b = 2 := by
    simp [weightedMech21, hr]
  have hp0 : weightedMech21.payment b 0 = -1 := by
    have her : Finset.univ.erase (0 : Fin 2) = {1} := by decide
    simp only [weightedMech21, weightedGroves_payment, hr, her, Finset.sum_singleton]
    norm_num [weights21, boosts012, b]
  have hp1 : weightedMech21.payment b 1 = -6 := by
    have her : Finset.univ.erase (1 : Fin 2) = {0} := by decide
    simp only [weightedMech21, weightedGroves_payment, hr, her, Finset.sum_singleton]
    norm_num [weights21, boosts012, b]
  exact ⟨hout, hp0, hp1⟩

/-- Taxation principle failure witness: a constant-outcome mechanism charging agent `i` its own
reported value of outcome `0` fails DSIC and violates the taxation principle. -/
theorem badPayment_not_isDSIC :
    let M : Mechanism Unit (Fin 2) := ⟨fun _ => 0, fun b i => b i 0⟩
    ¬ M.IsDSIC := by
  intro M hdsic
  have h := hdsic () (fun _ => ![0, 0]) ![1, 0]
  norm_num [Mechanism.utility, M, Function.update_self] at h

/-- Positive witness of the taxation principle: extracting outcome prices from `weightedMech21`
and verifying the optimization condition. -/
theorem taxation_weightedMech21 (b : Fin 2 → Fin 3 → ℝ) (i : Fin 2) :
    ∃ p : Fin 3 → ℝ,
      (∀ v : Fin 3 → ℝ,
        weightedMech21.payment (Function.update b i v) i =
          p (weightedMech21.outcome (Function.update b i v))) ∧
      (∀ v : Fin 3 → ℝ, ∀ a ∈ Set.range (fun v' => weightedMech21.outcome (Function.update b i v')),
        v a - p a ≤
          v (weightedMech21.outcome (Function.update b i v)) -
            p (weightedMech21.outcome (Function.update b i v))) :=
  (isDSIC_iff_taxation.1 weightedMech21_spec.1) i b

/-! ### Negative-weight counterexample (omitted `kᵢ ≥ 0` in Lavi 2007, Def. 12.23) -/

private noncomputable def argmin2 (b : Unit → Fin 2 → ℝ) : Fin 2 :=
  if b () 0 ≤ b () 1 then 0 else 1

/-- `argmin` maximizes the affine score with negative weight `w = -1`, yet fails WMON and is not
DSIC-implementable. -/
theorem argmin2_not_wmon_not_implementable :
    IsAffineMaximizerFor argmin2 Set.univ (fun _ => (-1 : ℝ)) (fun _ => 0) ∧
      ¬ IsWeaklyMonotone argmin2 ∧ ¬ IsImplementable argmin2 := by
  have haff : IsAffineMaximizerFor argmin2 Set.univ (fun _ => (-1 : ℝ)) (fun _ => 0) := by
    intro b
    refine ⟨Set.mem_univ _, fun ω _ => ?_⟩
    simp only [affineScore, zero_add, Finset.univ_unique, PUnit.default_eq_unit,
      Finset.sum_singleton, argmin2]
    split_ifs with h
    · fin_cases ω
      · exact le_rfl
      · change -1 * b () 1 ≤ -1 * b () 0; linarith
    · fin_cases ω
      · change -1 * b () 0 ≤ -1 * b () 1; linarith
      · exact le_rfl
  have hnw : ¬ IsWeaklyMonotone argmin2 := fun hw => by
    have h := hw () (fun _ => ![0, 0]) ![0, 1] ![1, 0]
    norm_num [argmin2, Function.update_self] at h
  exact ⟨haff, hnw, fun hi => hnw hi.isWeaklyMonotone⟩

/-! ### Non-convex domain separating WMON from cyclic monotonicity (Nisan 2007, p. 227) -/

private def rpsVal0 : Fin 3 → ℝ := ![0, 1, -2]
private def rpsVal1 : Fin 3 → ℝ := ![-2, 0, 1]
private def rpsVal2 : Fin 3 → ℝ := ![1, -2, 0]

private def rpsDomain : Unit → Set (Fin 3 → ℝ) := fun _ => {rpsVal0, rpsVal1, rpsVal2}

private noncomputable def rpsRule (b : Unit → Fin 3 → ℝ) : Fin 3 :=
  if b () = rpsVal0 then 0 else if b () = rpsVal1 then 1 else 2

private theorem rpsVal_ne : rpsVal0 ≠ rpsVal1 ∧ rpsVal1 ≠ rpsVal2 ∧ rpsVal0 ≠ rpsVal2 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrFun h 0; norm_num [rpsVal0, rpsVal1] at this
  · have := congrFun h 0; norm_num [rpsVal1, rpsVal2] at this
  · have := congrFun h 0; norm_num [rpsVal0, rpsVal2] at this

/-- On the 3-point rock–paper–scissors domain, `rpsRule` satisfies WMON (every 2-cycle is `≥ 0`),
yet has a 3-cycle of weight `-3 < 0`, so it fails `IsCyclicallyMonotoneOn` and is **not**
DSIC-implementable. -/
theorem rpsRule_wmon_not_cyclically_monotone :
    IsWeaklyMonotoneOn rpsRule rpsDomain ∧
      ¬ IsCyclicallyMonotoneOn rpsRule rpsDomain ∧
      ¬ IsImplementableOn rpsRule rpsDomain := by
  have hr0 : ∀ b : Unit → Fin 3 → ℝ, rpsRule (Function.update b () rpsVal0) = 0 := fun b => by
    simp only [rpsRule, Function.update_self, ↓reduceIte]
  have hr1 : ∀ b : Unit → Fin 3 → ℝ, rpsRule (Function.update b () rpsVal1) = 1 := fun b => by
    simp only [rpsRule, Function.update_self, rpsVal_ne.1.symm, ↓reduceIte]
  have hr2 : ∀ b : Unit → Fin 3 → ℝ, rpsRule (Function.update b () rpsVal2) = 2 := fun b => by
    simp only [rpsRule, Function.update_self, rpsVal_ne.2.2.symm, rpsVal_ne.2.1.symm, ↓reduceIte]
  have hwmon : IsWeaklyMonotoneOn rpsRule rpsDomain := by
    rintro u b v v' _ hv hv'
    cases u
    rcases hv with rfl | rfl | rfl <;> rcases hv' with rfl | rfl | rfl
    · rw [hr0]
    · rw [hr0, hr1]; norm_num [rpsVal0, rpsVal1]
    · rw [hr0, hr2]; norm_num [rpsVal0, rpsVal2]
    · rw [hr1, hr0]; norm_num [rpsVal1, rpsVal0]
    · rw [hr1]
    · rw [hr1, hr2]; norm_num [rpsVal1, rpsVal2]
    · rw [hr2, hr0]; norm_num [rpsVal2, rpsVal0]
    · rw [hr2, hr1]; norm_num [rpsVal2, rpsVal1]
    · rw [hr2]
  have hncyc : ¬ IsCyclicallyMonotoneOn rpsRule rpsDomain := fun hc => by
    let cyc : Fin 3 → Fin 3 → ℝ := ![rpsVal0, rpsVal1, rpsVal2]
    have hmem : ∀ t : Fin 3, cyc t ∈ rpsDomain () := fun t => by
      fin_cases t <;> simp [cyc, rpsDomain]
    have h := hc () (fun _ => rpsVal0) (fun j hj => absurd rfl hj) 2 cyc hmem
    rw [Fin.sum_univ_three] at h
    have hc0 : cyc 0 = rpsVal0 := rfl
    have hc1 : cyc 1 = rpsVal1 := rfl
    have hc2 : cyc 2 = rpsVal2 := rfl
    have h01 : (0 : Fin 3) + 1 = 1 := rfl
    have h12 : (1 : Fin 3) + 1 = 2 := rfl
    have h20 : (2 : Fin 3) + 1 = 0 := rfl
    rw [h01, h12, h20, hc0, hc1, hc2, hr0, hr1, hr2] at h
    norm_num [rpsVal0, rpsVal1, rpsVal2] at h
  exact ⟨hwmon, hncyc, fun hi => hncyc (isImplementableOn_iff_isCyclicallyMonotoneOn.1 hi)⟩

/-! ### Dictatorship with zero weight (`w = ![1, 0]`, slip in Nisan 2007 Def. 9.30) -/

private noncomputable def dictatorRule (b : Fin 2 → Fin 3 → ℝ) : Fin 3 := argmax3 (b 0)

/-- The dictatorship of player `0` on `Fin 3` is neutral, surjective, DSIC with zero payments, an
affine maximizer with `w = (1, 0)`, and has **no** affine-maximizer representation with strictly
positive weights `w i > 0` for all `i`. -/
theorem dictatorRule_no_positive_weights :
    IsNeutral dictatorRule ∧
      Function.Surjective dictatorRule ∧
      (weightedGroves dictatorRule ![1, 0] 0 (fun _ _ => 0)).IsDSIC ∧
      IsAffineMaximizer dictatorRule ∧
      ¬ ∃ (w : Fin 2 → ℝ) (c : Fin 3 → ℝ),
          (∀ i, 0 < w i) ∧ IsAffineMaximizerFor dictatorRule Set.univ w c := by
  have hneut : IsNeutral dictatorRule := fun v x hx =>
    argmax3_eq_of_strict fun y hy => hx 0 y hy
  have haff : IsAffineMaximizerFor dictatorRule Set.univ ![1, 0] 0 := by
    intro b
    refine ⟨Set.mem_univ _, fun ω _ => ?_⟩
    simp only [affineScore, Pi.zero_apply, zero_add, Fin.sum_univ_two, Matrix.cons_val_zero,
      one_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, add_zero]
    exact le_argmax3 (b 0) ω
  have hdummy : ∀ i : Fin 2, (![(1 : ℝ), 0] i = 0) →
      ∀ b v, dictatorRule (Function.update b i v) = dictatorRule b := by
    intro i hi b v
    fin_cases i
    · norm_num at hi
    · change dictatorRule (Function.update b 1 v) = dictatorRule b
      simp only [dictatorRule, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  have hdsic : (weightedGroves dictatorRule ![1, 0] 0 (fun _ _ => 0)).IsDSIC :=
    weightedGroves_isDSIC_of_nonneg haff (fun i => by fin_cases i <;> norm_num) hdummy
      fun _ _ _ => rfl
  refine ⟨hneut, hneut.surjective, hdsic,
    ⟨Set.univ, ![1, 0], 0, fun i => by fin_cases i <;> norm_num, ⟨0, by norm_num⟩, haff⟩, ?_⟩
  rintro ⟨w, c, hw, hmax⟩
  let m : ℝ := (w 0 + |c 1 - c 0| + 1) / w 1
  let b : Fin 2 → Fin 3 → ℝ := ![![1, 0, -1], ![0, m, 0]]
  have hout : dictatorRule b = 0 := argmax3_eq_of_strict fun y hy => by
    fin_cases y
    · exact absurd rfl hy
    · norm_num [b]
    · norm_num [b]
  have hle := (hmax b).2 1 (Set.mem_univ _)
  rw [hout] at hle
  simp only [affineScore, Fin.sum_univ_two] at hle
  have hwm : w 1 * m = w 0 + |c 1 - c 0| + 1 := mul_div_cancel₀ _ (hw 1).ne'
  have hb00 : b 0 0 = 1 := rfl
  have hb01 : b 0 1 = 0 := rfl
  have hb10 : b 1 0 = 0 := rfl
  have hb11 : b 1 1 = m := rfl
  rw [hb00, hb01, hb10, hb11] at hle
  linarith [le_abs_self (c 1 - c 0), neg_le_abs (c 1 - c 0)]

/-! ### Adverse tie-breaking at zero weight -/

private noncomputable def badTieRule (b : Fin 2 → Fin 3 → ℝ) : Fin 3 :=
  if b 0 0 = b 0 1 ∧ b 0 2 ≤ b 0 0 then
    if b 1 0 ≤ b 1 1 then 0 else 1
  else argmax3 (b 0)

/-- With `w = (1, 0)`, `badTieRule` always maximizes `1 * b 0 ω + 0 * b 1 ω`, yet it breaks ties
of agent `0` to *minimize* agent `1`'s value on `{0, 1}`. Hence it violates WMON and is not
DSIC-implementable. -/
theorem badTieRule_affine_not_implementable :
    IsAffineMaximizerFor badTieRule Set.univ ![1, 0] 0 ∧
      ¬ IsWeaklyMonotone badTieRule ∧ ¬ IsImplementable badTieRule := by
  have haff : IsAffineMaximizerFor badTieRule Set.univ ![1, 0] 0 := by
    intro b
    refine ⟨Set.mem_univ _, fun ω _ => ?_⟩
    simp only [affineScore, Pi.zero_apply, zero_add, Fin.sum_univ_two, Matrix.cons_val_zero,
      one_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one, zero_mul, add_zero, badTieRule]
    split_ifs with htie h1
    · fin_cases ω
      · exact le_rfl
      · change b 0 1 ≤ b 0 0; linarith [htie.1]
      · change b 0 2 ≤ b 0 0; exact htie.2
    · fin_cases ω
      · change b 0 0 ≤ b 0 1; linarith [htie.1]
      · exact le_rfl
      · change b 0 2 ≤ b 0 1; linarith [htie.1, htie.2]
    · exact le_argmax3 (b 0) ω
  have hnw : ¬ IsWeaklyMonotone badTieRule := fun hw => by
    let b : Fin 2 → Fin 3 → ℝ := ![![0, 0, -1], ![0, 0, 0]]
    have h := hw 1 b ![0, 1, 0] ![1, 0, 0]
    have h1 : badTieRule (Function.update b 1 ![0, 1, 0]) = 0 := by
      simp only [badTieRule, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
        Function.update_self]
      norm_num [b]
    have h2 : badTieRule (Function.update b 1 ![1, 0, 0]) = 1 := by
      simp only [badTieRule, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
        Function.update_self]
      norm_num [b]
    rw [h1, h2] at h
    norm_num at h
  exact ⟨haff, hnw, fun hi => hnw hi.isWeaklyMonotone⟩

/-! ### Exercise 12.6 (Lavi 2007, p. 329): DSIC without Generalized-WMON -/

private def exU0 : Fin 4 → ℝ := ![0, 0, 0, 0]
private def exU1 : Fin 4 → ℝ := ![2, 1, 3, 0]
private def exW0 : Fin 4 → ℝ := ![0, 0, 0, 0]
private def exW1 : Fin 4 → ℝ := ![2, 1, 0, 3]

private def exDom : Fin 2 → Set (Fin 4 → ℝ)
  | 0 => {exU0, exU1}
  | 1 => {exW0, exW1}

private noncomputable def exOutcome (b : Fin 2 → Fin 4 → ℝ) : Fin 4 :=
  if b 0 = exU0 then
    if b 1 = exW0 then 0 else 3
  else
    if b 1 = exW0 then 2 else 1

private noncomputable def exPay (b : Fin 2 → Fin 4 → ℝ) : Fin 2 → ℝ
  | 0 => if b 0 = exU0 then 0 else 1 / 2
  | 1 => if b 1 = exW0 then 0 else 1 / 2

private theorem ex_ne : exU0 ≠ exU1 ∧ exW0 ≠ exW1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrFun h 0; norm_num [exU0, exU1] at this
  · have := congrFun h 0; norm_num [exW0, exW1] at this

/-- Solution to [Lavi2007], Exercise 12.6 (p. 329): on the finite domain `exDom`, the mechanism
`⟨exOutcome, exPay⟩` is DSIC (so `exOutcome` is implementable and satisfies `IsPADOn`), yet
`exOutcome` violates `IsGeneralizedWMONOn` at `(exU0, exW0) ↦ 0` vs `(exU1, exW1) ↦ 1`. -/
theorem ex12_6_isDSICOn_not_generalizedWMON :
    (⟨exOutcome, exPay⟩ : Mechanism (Fin 2) (Fin 4)).IsDSICOn exDom ∧
      IsPADOn exOutcome exDom ∧
      ¬ IsGeneralizedWMONOn exOutcome exDom := by
  have hdsic : (⟨exOutcome, exPay⟩ : Mechanism (Fin 2) (Fin 4)).IsDSICOn exDom := by
    intro i b v hb hv
    have hb0 : b 0 = exU0 ∨ b 0 = exU1 := by simpa [exDom] using hb 0
    have hb1 : b 1 = exW0 ∨ b 1 = exW1 := by simpa [exDom] using hb 1
    fin_cases i
    · have hv' : v = exU0 ∨ v = exU1 := by simpa [exDom] using hv
      change v (exOutcome b) - exPay b 0 ≤
        v (exOutcome (Function.update b 0 v)) - exPay (Function.update b 0 v) 0
      simp only [exOutcome, exPay, Function.update_self,
        Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      rcases hb0 with h0 | h0 <;> rcases hb1 with h1 | h1 <;> rcases hv' with rfl | rfl <;>
        simp only [h0, h1, ex_ne.1.symm, ex_ne.2.symm, ↓reduceIte] <;>
        norm_num [exU0, exU1]
    · have hv' : v = exW0 ∨ v = exW1 := by simpa [exDom] using hv
      change v (exOutcome b) - exPay b 1 ≤
        v (exOutcome (Function.update b 1 v)) - exPay (Function.update b 1 v) 1
      simp only [exOutcome, exPay, Function.update_self,
        Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      rcases hb0 with h0 | h0 <;> rcases hb1 with h1 | h1 <;> rcases hv' with rfl | rfl <;>
        simp only [h0, h1, ex_ne.1.symm, ex_ne.2.symm, ↓reduceIte] <;>
        norm_num [exW0, exW1]
  have hpad : IsPADOn exOutcome exDom := hdsic.isWeaklyMonotoneOn.isPADOn
  have hngw : ¬ IsGeneralizedWMONOn exOutcome exDom := fun hgw => by
    let p0 : Fin 2 → Fin 4 → ℝ := ![exU0, exW0]
    let p1 : Fin 2 → Fin 4 → ℝ := ![exU1, exW1]
    have hp0 : ∀ i, p0 i ∈ exDom i := fun i => by fin_cases i <;> simp [p0, exDom]
    have hp1 : ∀ i, p1 i ∈ exDom i := fun i => by fin_cases i <;> simp [p1, exDom]
    have ho0 : exOutcome p0 = 0 := by simp [exOutcome, p0]
    have ho1 : exOutcome p1 = 1 := by
      simp [exOutcome, p1, ex_ne.1.symm, ex_ne.2.symm]
    obtain ⟨i, hi⟩ := hgw p0 p1 hp0 hp1 (by rw [ho0, ho1]; decide)
    rw [ho0, ho1] at hi
    fin_cases i
    · norm_num [p0, p1, exU0, exU1] at hi
    · norm_num [p0, p1, exW0, exW1] at hi
  exact ⟨hdsic, hpad, hngw⟩

/-! ### Tightness of `3 ≤ |Ω|` in Roberts' theorem (`|Ω| = 2`, `Bool`) -/

private noncomputable def andRule (b : Fin 2 → Bool → ℝ) : Bool :=
  decide (b 0 false ≤ b 0 true ∧ b 1 false ≤ b 1 true)

/-- On `|Ω| = 2` (`Bool`), the unanimity-for-`true` (`AND`) rule is surjective and DSIC with zero
payments, yet is **not** an affine maximizer. This witnesses that `3 ≤ Fintype.card Ω` is tight in
Roberts' theorem ([Nisan2007], p. 228). -/
theorem andRule_surjective_dsic_not_affine :
    Function.Surjective andRule ∧
      (⟨andRule, fun _ _ => 0⟩ : Mechanism (Fin 2) Bool).IsDSIC ∧
      ¬ IsAffineMaximizer andRule := by
  have honto : Function.Surjective andRule := by
    intro a
    cases a
    · refine ⟨fun _ x => if x then 0 else 1, ?_⟩
      simp [andRule]
    · refine ⟨fun _ x => if x then 1 else 0, ?_⟩
      simp [andRule]
  have hdsic : (⟨andRule, fun _ _ => 0⟩ : Mechanism (Fin 2) Bool).IsDSIC := by
    intro i b v
    simp only [Mechanism.utility, sub_zero]
    fin_cases i
    · change v (andRule b) ≤ v (andRule (Function.update b 0 v))
      simp only [andRule, Function.update_self, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      by_cases h1 : b 1 false ≤ b 1 true
      · by_cases h0 : b 0 false ≤ b 0 true <;> by_cases hv : v false ≤ v true <;>
          simp [h0, h1, hv]
        linarith
      · simp [h1]
    · change v (andRule b) ≤ v (andRule (Function.update b 1 v))
      simp only [andRule, Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      by_cases h0 : b 0 false ≤ b 0 true
      · by_cases h1 : b 1 false ≤ b 1 true <;> by_cases hv : v false ≤ v true <;>
          simp [h0, h1, hv]
        linarith
      · simp [h0]
  refine ⟨honto, hdsic, ?_⟩
  rintro ⟨A, w, c, hw, ⟨i₀, hi₀⟩, hmax⟩
  have htrue_mem : true ∈ A := by
    obtain ⟨b, hb⟩ := honto true
    rw [← hb]; exact (hmax b).1
  have hfalse_mem : false ∈ A := by
    obtain ⟨b, hb⟩ := honto false
    rw [← hb]; exact (hmax b).1
  let d : ℝ := c false - c true
  have hzero : andRule (fun _ _ => 0) = true := by simp [andRule]
  have hd_le : d ≤ 0 := by
    have h := (hmax (fun _ _ => 0)).2 false hfalse_mem
    rw [hzero] at h
    simp only [affineScore, Fin.sum_univ_two, mul_zero, add_zero] at h
    linarith
  fin_cases i₀
  · let x : ℝ := (|d| + w 1 + 1) / w 0
    let b : Fin 2 → Bool → ℝ := ![fun a => if a then x else 0, fun a => if a then -1 else 0]
    have hbf : andRule b = false := by
      simp only [andRule, b, Matrix.cons_val_one, Matrix.cons_val_fin_one, decide_eq_false_iff_not]
      intro h; norm_num at h
    have h := (hmax b).2 true htrue_mem
    rw [hbf] at h
    simp only [affineScore, Fin.sum_univ_two] at h
    have hwx : w 0 * x = |d| + w 1 + 1 := mul_div_cancel₀ _ hi₀.ne'
    have h0t : b 0 true = x := rfl
    have h0f : b 0 false = 0 := rfl
    have h1t : b 1 true = -1 := rfl
    have h1f : b 1 false = 0 := rfl
    rw [h0t, h0f, h1t, h1f] at h
    linarith [neg_le_abs d]
  · let x : ℝ := (|d| + w 0 + 1) / w 1
    let b : Fin 2 → Bool → ℝ := ![fun a => if a then -1 else 0, fun a => if a then x else 0]
    have hbf : andRule b = false := by
      simp only [andRule, b, Matrix.cons_val_zero, decide_eq_false_iff_not]
      intro h; norm_num at h
    have h := (hmax b).2 true htrue_mem
    rw [hbf] at h
    simp only [affineScore, Fin.sum_univ_two] at h
    have hwx : w 1 * x = |d| + w 0 + 1 := mul_div_cancel₀ _ hi₀.ne'
    have h0t : b 0 true = -1 := rfl
    have h0f : b 0 false = 0 := rfl
    have h1t : b 1 true = x := rfl
    have h1f : b 1 false = 0 := rfl
    rw [h0t, h0f, h1t, h1f] at h
    linarith [neg_le_abs d]

/-! ### Nonvacuity checks for Roberts' theorems (surjective, neutral, finite-range) -/

/-- Non-surjective rule on `Fin 4` whose range is `{0, 1, 2}` (card `3`). -/
private noncomputable def range3Rule (b : Fin 2 → Fin 4 → ℝ) : Fin 4 :=
  (weightedRule21 fun i k => b i k.castSucc).castSucc

/-- Instantiates the finite-range (non-surjective) Roberts theorem on `range3Rule`. -/
theorem range3Rule_roberts_nonvacuous :
    ∃ (w : Fin 2 → ℝ) (c : Fin 4 → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
        IsAffineMaximizerFor range3Rule (Set.range range3Rule) w c := by
  have honto3 : Function.Surjective weightedRule21 := by
    intro a
    let b : Fin 2 → Fin 3 → ℝ := fun _ k => if k = a then 10 else 0
    refine ⟨b, argmax3_eq_of_strict fun y hy => ?_⟩
    fin_cases a <;> fin_cases y <;>
      first
      | exact absurd rfl hy
      | (simp [affineScore, weights21, boosts012, b, Fin.sum_univ_two]; norm_num)
  have hrange : Set.range range3Rule = {0, 1, 2} := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      have hval := (weightedRule21 fun i k => b i k.castSucc).isLt
      simp only [range3Rule, Set.mem_insert_iff, Set.mem_singleton_iff]
      match h : weightedRule21 (fun i k => b i k.castSucc) with
      | 0 => left; rfl
      | 1 => right; left; rfl
      | 2 => right; right; rfl
    · intro hx
      have hcast : ∀ a : Fin 3, (a.castSucc : Fin 4) ∈ Set.range range3Rule := fun a => by
        obtain ⟨b, hb⟩ := honto3 a
        refine ⟨fun i j => if h : j.val < 3 then b i ⟨j.val, h⟩ else 0, ?_⟩
        simp only [range3Rule]
        have hsub : (fun i (k : Fin 3) =>
            if h : k.castSucc.val < 3 then b i ⟨k.castSucc.val, h⟩ else 0) = b := by
          ext i k
          simp only [Fin.val_castSucc, k.isLt, ↓reduceDIte, Fin.eta]
        rw [hsub, hb]
      rcases hx with rfl | rfl | rfl
      · exact hcast 0
      · exact hcast 1
      · exact hcast 2
  have hfin : (Set.range range3Rule).Finite := Set.toFinite _
  have hcard : 3 ≤ (Set.range range3Rule).ncard := by
    rw [hrange]
    have : ({(0 : Fin 4), 1, 2} : Set (Fin 4)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by decide), Set.ncard_insert_of_notMem (by decide),
        Set.ncard_singleton]
    omega
  have haff : IsAffineMaximizerFor range3Rule (Set.range range3Rule) weights21
      (fun x => if h : x.val < 3 then boosts012 ⟨x.val, h⟩ else 0) := by
    intro b
    refine ⟨Set.mem_range_self b, fun ω hω => ?_⟩
    rw [hrange] at hω
    have hlt : ω.val < 3 := by rcases hω with rfl | rfl | rfl <;> decide
    set a : Fin 3 := ⟨ω.val, hlt⟩
    have haeq : a.castSucc = ω := Fin.ext rfl
    have hres := (weightedRule21_isAffine fun i k => b i k.castSucc).2 a (Set.mem_univ _)
    have h1 : (weightedRule21 fun i k => b i k.castSucc).castSucc.val < 3 :=
      (weightedRule21 fun i k => b i k.castSucc).isLt
    simp only [affineScore, range3Rule, hlt, h1, ↓reduceDIte] at hres ⊢
    exact hres
  have hwmon : IsWeaklyMonotone range3Rule := (haff.isImplementable weights21_pos).isWeaklyMonotone
  exact exists_isAffineMaximizerFor_range_of_isWeaklyMonotone hfin hcard hwmon

/-- Nonvacuity check of surjective and neutral Roberts' theorems on `dictatorRule`. -/
theorem dictatorRule_roberts_nonvacuous :
    (∃ (w : Fin 2 → ℝ) (c : Fin 3 → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ IsAffineMaximizerFor dictatorRule Set.univ w c) ∧
    (∃ w : Fin 2 → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      ∀ (b : Fin 2 → Fin 3 → ℝ) (ω : Fin 3),
        ∑ i, w i * b i ω ≤ ∑ i, w i * b i (dictatorRule b)) := by
  have himp : IsImplementable dictatorRule := by
    rw [← weightedGroves_outcome dictatorRule ![1, 0] 0 (fun _ _ => 0)]
    exact ⟨(weightedGroves dictatorRule ![1, 0] 0 (fun _ _ => 0)).payment,
      dictatorRule_no_positive_weights.2.2.1⟩
  exact ⟨exists_isAffineMaximizerFor_of_isImplementable (by decide)
      dictatorRule_no_positive_weights.2.1 himp,
    exists_weightedWelfare_of_isNeutral_of_isImplementable (by decide)
      dictatorRule_no_positive_weights.1 himp⟩

end CslibFrontierTests.GameTheory.Roberts
