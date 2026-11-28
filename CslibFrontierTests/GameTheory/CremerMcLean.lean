/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Mechanism.CremerMcLean
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Crémer–McLean correlated-type full surplus extraction: checked finite witnesses

This `module` tests the public surface (using ordinary `import`s only, without unfolding unexposed
bodies) of `CslibFrontier.GameTheory.Mechanism.CremerMcLean` across three concrete finite priors:

1. **`2 × 2` correlated binary single-item auction vs independent uniform prior**:
   - Under `corrBinaryPrior` (`Pr(b, b) = 1/3`, `Pr(b, ¬b) = 1/6`), `HasFullBeliefRank` holds and
     adding the explicit opponent-only side transfer `(-1/3, +2/3)` to the second-price baseline
     `binaryVCG` yields `corrBinaryCM`, which satisfies `IsExPostEfficient`, `IsTruthful`,
     `IsInterimIR`, and `ExtractsFullSurplus` with exact seller expected revenue `2/3` equal to
     expected first-best welfare.
   - Under the uniform independent product prior `indepBinaryPrior` (`Pr = 1/4` each), both
     `HasConvexIndependentBeliefs` and `HasFullBeliefRank` fail, `binaryVCG` extracts only `1/4` of
     expected welfare `3/4` (leaving positive bidder rent), and on `{1, 2}` single-item auction
     valuations (`posAuctionVal`) *no* ex-post efficient, BIC, interim-IR mechanism extracts the
     full surplus.
2. **`4 × 3` rhombus-in-simplex prior separating Bayesian from dominant-strategy extraction**:
   - `rhombusPrior` (`T 0 = Fin 4`, `T 1 = Fin 3`) places player `0`'s four conditional beliefs at
     the vertices of a convex quadrilateral in `Δ(Fin 3)` while keeping player `1`'s three
     conditional beliefs linearly independent in `Δ(Fin 4)`.
   - `¬ rhombusPrior.HasFullBeliefRank` (witnessed by left-kernel vector `![1, 1, -1, -1]`, so
     dominant-strategy universal extraction fails), while `rhombusPrior.HasConvexIndependentBeliefs`
     holds (certified by explicit integer separating lotteries), so Bayesian + interim-IR full
     surplus extraction succeeds for every valuation profile on every nonempty finite outcome set.
3. **`3 × 2` collinear-beliefs impossibility witness**:
   - `collinearPrior` (`T 0 = Fin 3`, `T 1 = Bool`) makes type `1`'s conditional belief `(1/2, 1/2)`
     the midpoint of type `0`'s `(3/4, 1/4)` and type `2`'s `(1/4, 3/4)`, refuting
     `HasConvexIndependentBeliefs` and exhibiting an explicit nonnegative binary valuation
     `collinearVal` on which every ex-post efficient, BIC, interim-IR mechanism leaves at least `1`
     unit of weighted interim information rent and therefore cannot extract full surplus.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.CremerMcLean

open Cslib.GameTheory Finset Matrix

/-! ### Finite-index quantifier and opponent-profile helpers -/

section Helpers

theorem forall_fin3 {P : Fin 3 → Prop} : (∀ a : Fin 3, P a) ↔ P 0 ∧ P 1 ∧ P 2 := by
  rw [Fin.forall_iff_succ, Fin.forall_fin_two]
  rfl

theorem forall_fin4 {P : Fin 4 → Prop} : (∀ a : Fin 4, P a) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  rw [Fin.forall_iff_succ, forall_fin3]
  rfl

theorem fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i
  rw [Fin.forall_fin_two]
  decide

theorem fin3_cases (a : Fin 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  revert a
  rw [forall_fin3]
  decide

@[simp]
theorem vec2_apply_one {α : Type*} (a b : α) : ![a, b] (1 : Fin 2) = b :=
  rfl

/-- In a 2-player game (`ι = Fin 2`), the unique opponent index `{j : Fin 2 // j ≠ i}` of `i`. -/
def otherFin2 : (i : Fin 2) → {j : Fin 2 // j ≠ i}
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨0, by decide⟩

@[simp]
theorem otherFin2_zero_val : (otherFin2 0).val = 1 :=
  rfl

@[simp]
theorem otherFin2_one_val : (otherFin2 1).val = 0 :=
  rfl

theorem eq_one_of_ne_zero {j : Fin 2} (hj : j ≠ 0) : j = 1 :=
  (fin2_eq_zero_or_one j).resolve_left hj

theorem eq_zero_of_ne_one {j : Fin 2} (hj : j ≠ 1) : j = 0 :=
  (fin2_eq_zero_or_one j).resolve_right hj

theorem subsingleton_oppFin2 (i : Fin 2) : Subsingleton {j : Fin 2 // j ≠ i} := by
  rcases fin2_eq_zero_or_one i with rfl | rfl
  · exact ⟨fun ⟨_, ha⟩ ⟨_, hb⟩ =>
      Subtype.ext ((eq_one_of_ne_zero ha).trans (eq_one_of_ne_zero hb).symm)⟩
  · exact ⟨fun ⟨_, ha⟩ ⟨_, hb⟩ =>
      Subtype.ext ((eq_zero_of_ne_one ha).trans (eq_zero_of_ne_one hb).symm)⟩

/-- For `ι = Fin 2` and type family `T`, opponent profiles `OppProfile T 0` are canonically
equivalent to `T 1`. -/
def oppEquiv0 {T : Fin 2 → Type*} : T 1 ≃ OppProfile T 0 where
  toFun x j := (eq_one_of_ne_zero j.property).symm ▸ x
  invFun t_opp := t_opp ⟨1, by decide⟩
  left_inv _ := rfl
  right_inv t_opp := by
    funext ⟨j, hj⟩
    cases eq_one_of_ne_zero hj
    rfl

@[simp]
theorem oppEquiv0_apply_one {T : Fin 2 → Type*} (x : T 1) (h : (1 : Fin 2) ≠ 0) :
    oppEquiv0 (T := T) x ⟨1, h⟩ = x :=
  rfl

/-- For `ι = Fin 2` and type family `T`, opponent profiles `OppProfile T 1` are canonically
equivalent to `T 0`. -/
def oppEquiv1 {T : Fin 2 → Type*} : T 0 ≃ OppProfile T 1 where
  toFun x j := (eq_zero_of_ne_one j.property).symm ▸ x
  invFun t_opp := t_opp ⟨0, by decide⟩
  left_inv _ := rfl
  right_inv t_opp := by
    funext ⟨j, hj⟩
    cases eq_zero_of_ne_one hj
    rfl

@[simp]
theorem oppEquiv1_apply_zero {T : Fin 2 → Type*} (x : T 0) (h : (0 : Fin 2) ≠ 1) :
    oppEquiv1 (T := T) x ⟨0, h⟩ = x :=
  rfl

@[simp]
theorem extendProfile_opp0_zero {T : Fin 2 → Type*} (a : T 0) (b : T 1) :
    extendProfile 0 a (oppEquiv0 b) 0 = a :=
  extendProfile_self 0 a (oppEquiv0 b)

@[simp]
theorem extendProfile_opp0_one {T : Fin 2 → Type*} (a : T 0) (b : T 1) :
    extendProfile 0 a (oppEquiv0 b) 1 = b :=
  (extendProfile_of_ne (by decide : (1 : Fin 2) ≠ 0) a (oppEquiv0 b)).trans
    (oppEquiv0_apply_one b (by decide))

@[simp]
theorem extendProfile_opp1_zero {T : Fin 2 → Type*} (b : T 1) (a : T 0) :
    extendProfile 1 b (oppEquiv1 a) 0 = a :=
  (extendProfile_of_ne (by decide : (0 : Fin 2) ≠ 1) b (oppEquiv1 a)).trans
    (oppEquiv1_apply_zero a (by decide))

@[simp]
theorem extendProfile_opp1_one {T : Fin 2 → Type*} (b : T 1) (a : T 0) :
    extendProfile 1 b (oppEquiv1 a) 1 = b :=
  extendProfile_self 1 b (oppEquiv1 a)

/-- For homogeneous 2-player type spaces `fun _ : Fin 2 => α`, `OppProfile` is canonically `α`. -/
def oppEquivHom {α : Type*} (i : Fin 2) : α ≃ OppProfile (fun _ : Fin 2 => α) i where
  toFun x _ := x
  invFun t_opp := t_opp (otherFin2 i)
  left_inv _ := rfl
  right_inv t_opp := by
    funext j
    have := subsingleton_oppFin2 i
    rw [Subsingleton.elim j (otherFin2 i)]

@[simp]
theorem oppEquivHom_apply {α : Type*} (i : Fin 2) (x : α) (j : {j : Fin 2 // j ≠ i}) :
    oppEquivHom i x j = x :=
  rfl

theorem sum_oppHom {α : Type*} [Fintype α] (i : Fin 2)
    (f : OppProfile (fun _ : Fin 2 => α) i → ℝ) :
    ∑ t_opp, f t_opp = ∑ x : α, f (oppEquivHom i x) :=
  (Fintype.sum_equiv (oppEquivHom i) (fun x => f (oppEquivHom i x)) f (fun _ => rfl)).symm

theorem sum_opp0 {T : Fin 2 → Type*} [∀ i, Fintype (T i)]
    (f : OppProfile T 0 → ℝ) :
    ∑ t_opp, f t_opp = ∑ x : T 1, f (oppEquiv0 x) :=
  (Fintype.sum_equiv oppEquiv0 (fun x => f (oppEquiv0 x)) f (fun _ => rfl)).symm

theorem sum_opp1 {T : Fin 2 → Type*} [∀ i, Fintype (T i)]
    (f : OppProfile T 1 → ℝ) :
    ∑ t_opp, f t_opp = ∑ x : T 0, f (oppEquiv1 x) :=
  (Fintype.sum_equiv oppEquiv1 (fun x => f (oppEquiv1 x)) f (fun _ => rfl)).symm

theorem extendProfile_hom_zero {α : Type*} (a b : α) :
    extendProfile (T := fun _ : Fin 2 => α) 0 a (oppEquivHom 0 b) = ![a, b] := by
  funext j
  rcases fin2_eq_zero_or_one j with rfl | rfl
  · exact extendProfile_self 0 a (oppEquivHom 0 b)
  · exact extendProfile_of_ne (by decide : (1 : Fin 2) ≠ 0) a (oppEquivHom 0 b)

theorem extendProfile_hom_one {α : Type*} (a b : α) :
    extendProfile (T := fun _ : Fin 2 => α) 1 b (oppEquivHom 1 a) = ![a, b] := by
  funext j
  rcases fin2_eq_zero_or_one j with rfl | rfl
  · exact extendProfile_of_ne (by decide : (0 : Fin 2) ≠ 1) b (oppEquivHom 1 a)
  · exact extendProfile_self 1 b (oppEquivHom 1 a)

theorem sum_fin2_bool (g : (Fin 2 → Bool) → ℝ) :
    ∑ t : Fin 2 → Bool, g t =
      g ![false, false] + g ![false, true] + g ![true, false] + g ![true, true] := by
  rw [sum_profile_eq (T := fun _ : Fin 2 => Bool) 0]
  simp only [sum_oppHom, Fintype.sum_bool, extendProfile_hom_zero]
  ring

theorem prod_oppFin2_const (i : Fin 2) (c : ℝ) :
    (∏ _j : {j : Fin 2 // j ≠ i}, c) = c := by
  rcases fin2_eq_zero_or_one i with rfl | rfl
  · have hcard : (univ : Finset {j : Fin 2 // j ≠ 0}).card = 1 := by decide
    rw [prod_const, hcard, pow_one]
  · have hcard : (univ : Finset {j : Fin 2 // j ≠ 1}).card = 1 := by decide
    rw [prod_const, hcard, pow_one]

end Helpers

/-! ### 1. `2 × 2` correlated binary single-item auction vs independent uniform prior -/

section BinaryAuction

/-- Positively correlated symmetric binary prior on `Fin 2 → Bool`: matching types have probability
`1/3` each and mismatched types have probability `1/6` each. -/
noncomputable def corrBinaryPrior : CorrelatedPrior (Fin 2) (fun _ => Bool) where
  prob t := if t 0 = t 1 then 1 / 3 else 1 / 6
  prob_nonneg t := by split_ifs <;> norm_num
  sum_prob_eq_one := by
    rw [sum_fin2_bool]
    simp only [Matrix.cons_val_zero, vec2_apply_one]
    norm_num
  sum_prob_extendProfile_pos := by
    rw [Fin.forall_fin_two]
    constructor
    · rw [Bool.forall_bool]
      refine ⟨?_, ?_⟩ <;>
      · rw [sum_oppHom, Fintype.sum_bool]
        simp only [extendProfile_hom_zero, Matrix.cons_val_zero, vec2_apply_one]
        norm_num
    · rw [Bool.forall_bool]
      refine ⟨?_, ?_⟩ <;>
      · rw [sum_oppHom, Fintype.sum_bool]
        simp only [extendProfile_hom_one, Matrix.cons_val_zero, vec2_apply_one]
        norm_num

theorem corrBinaryPrior_marginal (i : Fin 2) (ti : Bool) :
    corrBinaryPrior.marginal i ti = 1 / 2 := by
  rcases fin2_eq_zero_or_one i with rfl | rfl
  · cases ti <;>
    · rw [CorrelatedPrior.marginal_apply, sum_oppHom, Fintype.sum_bool]
      simp only [corrBinaryPrior, extendProfile_hom_zero, Matrix.cons_val_zero, vec2_apply_one]
      norm_num
  · cases ti <;>
    · rw [CorrelatedPrior.marginal_apply, sum_oppHom, Fintype.sum_bool]
      simp only [corrBinaryPrior, extendProfile_hom_one, Matrix.cons_val_zero, vec2_apply_one]
      norm_num

theorem corrBinaryPrior_condBelief (i : Fin 2) (ti b : Bool) :
    corrBinaryPrior.condBelief i ti (oppEquivHom i b) = if ti = b then 2 / 3 else 1 / 3 := by
  rcases fin2_eq_zero_or_one i with rfl | rfl
  · cases ti <;> cases b <;>
    · rw [CorrelatedPrior.condBelief_apply, corrBinaryPrior_marginal]
      simp only [corrBinaryPrior, extendProfile_hom_zero, Matrix.cons_val_zero, vec2_apply_one]
      norm_num
  · cases ti <;> cases b <;>
    · rw [CorrelatedPrior.condBelief_apply, corrBinaryPrior_marginal]
      simp only [corrBinaryPrior, extendProfile_hom_one, Matrix.cons_val_zero, vec2_apply_one]
      norm_num

/-- `corrBinaryPrior` satisfies the Crémer–McLean full belief-rank condition (`det = 1/3 ≠ 0`). -/
theorem hasFullBeliefRank_corrBinaryPrior : corrBinaryPrior.HasFullBeliefRank := by
  intro i
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  have hf := congr_fun hc (oppEquivHom i false)
  have ht := congr_fun hc (oppEquivHom i true)
  simp only [Fintype.sum_bool, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    corrBinaryPrior_condBelief] at hf ht
  cases b <;> norm_num at hf ht <;> linarith

/-- Binary `{0, 1}` single-item auction valuations on `Option (Fin 2)`. -/
def binaryAuctionVal (i : Fin 2) (ti : Bool) : Option (Fin 2) → ℝ
  | none => 0
  | some j => if j = i then (if ti then 1 else 0) else 0

/-- Second-price (VCG) direct mechanism for `binaryAuctionVal`, breaking ties in favor of player
`0`. -/
def binaryVCG : IndirectMechanism (Fin 2) (fun _ => Bool) (Option (Fin 2)) where
  outcome t := if t 0 then some 0 else if t 1 then some 1 else none
  payment t i := if i = 0 then (if t 0 && t 1 then 1 else 0) else 0

theorem isExPostEfficient_binaryVCG : binaryVCG.IsExPostEfficient binaryAuctionVal := by
  intro t ω
  rcases Bool.eq_false_or_eq_true (t 0) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (t 1) with h1 | h1 <;>
    cases ω with
    | none => simp only [Fin.sum_univ_two, binaryVCG, binaryAuctionVal, h0, h1]; norm_num
    | some j =>
      rcases fin2_eq_zero_or_one j with rfl | rfl <;>
        simp only [Fin.sum_univ_two, binaryVCG, binaryAuctionVal, h0, h1] <;> norm_num

theorem isTruthful_binaryVCG : binaryVCG.IsTruthful binaryAuctionVal := by
  rw [IndirectMechanism.isTruthful_iff]
  intro t i ti'
  have hext : t = ![t 0, t 1] := by
    funext j
    rcases fin2_eq_zero_or_one j with rfl | rfl <;> rfl
  rcases Bool.eq_false_or_eq_true (t 0) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (t 1) with h1 | h1
  all_goals
    rw [h0, h1] at hext
    rw [hext]
    rcases fin2_eq_zero_or_one i with rfl | rfl <;> cases ti'
    all_goals
      dsimp only [binaryVCG, binaryAuctionVal]
      norm_num [Function.update]

/-- Explicit Crémer–McLean side-bet mechanism on top of `binaryVCG`: each bidder pays `-1/3` when
its opponent reports `false` and `+2/3` when its opponent reports `true`. -/
noncomputable def corrBinaryCM :
    IndirectMechanism (Fin 2) (fun _ => Bool) (Option (Fin 2)) :=
  binaryVCG.withOpponentTransfer fun i t_opp =>
    if t_opp (otherFin2 i) then 2 / 3 else -(1 / 3)

theorem isExPostEfficient_corrBinaryCM : corrBinaryCM.IsExPostEfficient binaryAuctionVal :=
  (IndirectMechanism.isExPostEfficient_withOpponentTransfer _ _ _).2 isExPostEfficient_binaryVCG

theorem isTruthful_corrBinaryCM : corrBinaryCM.IsTruthful binaryAuctionVal :=
  (IndirectMechanism.isTruthful_withOpponentTransfer _ _ _).2 isTruthful_binaryVCG

theorem corrBinaryCM_interimUtility_zero (i : Fin 2) (ti : Bool) :
    corrBinaryPrior.interimUtility binaryAuctionVal corrBinaryCM i ti ti = 0 := by
  rcases fin2_eq_zero_or_one i with rfl | rfl
  · cases ti <;>
    · rw [CorrelatedPrior.interimUtility_apply, sum_oppHom, Fintype.sum_bool]
      simp only [corrBinaryPrior_condBelief, corrBinaryCM,
        IndirectMechanism.withOpponentTransfer_outcome,
        IndirectMechanism.withOpponentTransfer_payment, extendProfile_hom_zero, oppProj_apply,
        otherFin2_zero_val, binaryVCG, binaryAuctionVal, Matrix.cons_val_zero, vec2_apply_one]
      norm_num
  · cases ti <;>
    · rw [CorrelatedPrior.interimUtility_apply, sum_oppHom, Fintype.sum_bool]
      simp only [corrBinaryPrior_condBelief, corrBinaryCM,
        IndirectMechanism.withOpponentTransfer_outcome,
        IndirectMechanism.withOpponentTransfer_payment, extendProfile_hom_one, oppProj_apply,
        otherFin2_one_val, binaryVCG, binaryAuctionVal, Matrix.cons_val_zero, vec2_apply_one]
      norm_num

theorem isInterimIR_corrBinaryCM :
    corrBinaryPrior.IsInterimIR binaryAuctionVal corrBinaryCM :=
  fun i ti => (corrBinaryCM_interimUtility_zero i ti).ge

theorem extractsFullSurplus_corrBinaryCM :
    corrBinaryPrior.ExtractsFullSurplus binaryAuctionVal corrBinaryCM :=
  corrBinaryPrior.extractsFullSurplus_of_forall_interimUtility_eq_zero
    corrBinaryCM_interimUtility_zero

/-- Expected seller revenue of `corrBinaryCM` under `corrBinaryPrior` equals the exact expected
first-best welfare `2/3`. -/
theorem corrBinaryCM_expected_revenue :
    (∑ t, corrBinaryPrior.prob t * ∑ i, corrBinaryCM.payment t i) = 2 / 3 ∧
    (∑ t, corrBinaryPrior.prob t * ∑ i, binaryAuctionVal i (t i) (corrBinaryCM.outcome t)) =
      2 / 3 := by
  have hwel : (∑ t, corrBinaryPrior.prob t *
      ∑ i, binaryAuctionVal i (t i) (corrBinaryCM.outcome t)) = 2 / 3 := by
    rw [sum_fin2_bool]
    simp only [corrBinaryPrior, corrBinaryCM, IndirectMechanism.withOpponentTransfer_outcome,
      Fin.sum_univ_two, binaryVCG, binaryAuctionVal, Matrix.cons_val_zero, vec2_apply_one]
    norm_num
  have hExt := extractsFullSurplus_corrBinaryCM
  rw [CorrelatedPrior.ExtractsFullSurplus] at hExt
  exact ⟨hExt.trans hwel, hwel⟩

/-- Uniform independent prior (`Pr = 1/4` on each of the four binary profiles), built via
`CorrelatedPrior.product`. -/
noncomputable def indepBinaryPrior : CorrelatedPrior (Fin 2) (fun _ => Bool) :=
  CorrelatedPrior.product (fun _ _ => 1 / 2)
    (fun _ => isMixedStrategy_iff.2 ⟨fun _ => by norm_num, by rw [Fintype.sum_bool]; norm_num⟩)
    (fun _ _ => by norm_num)

theorem not_hasConvexIndependentBeliefs_indepBinaryPrior :
    ¬ indepBinaryPrior.HasConvexIndependentBeliefs :=
  CorrelatedPrior.not_hasConvexIndependentBeliefs_product _ _ _ (i₀ := (0 : Fin 2))

theorem not_hasFullBeliefRank_indepBinaryPrior :
    ¬ indepBinaryPrior.HasFullBeliefRank :=
  CorrelatedPrior.not_hasFullBeliefRank_product _ _ _ (i₀ := (0 : Fin 2))

/-- Under `indepBinaryPrior`, `binaryVCG` yields expected welfare `3/4` but expected revenue only
`1/4`, leaving positive expected bidder rent. -/
theorem binaryVCG_revenue_lt_welfare_indepBinaryPrior :
    (∑ t, indepBinaryPrior.prob t * ∑ i, binaryVCG.payment t i) = 1 / 4 ∧
    (∑ t, indepBinaryPrior.prob t * ∑ i, binaryAuctionVal i (t i) (binaryVCG.outcome t)) =
      3 / 4 ∧
    ¬ indepBinaryPrior.ExtractsFullSurplus binaryAuctionVal binaryVCG := by
  have hrev : (∑ t, indepBinaryPrior.prob t * ∑ i, binaryVCG.payment t i) = 1 / 4 := by
    rw [sum_fin2_bool]
    simp only [indepBinaryPrior, CorrelatedPrior.product_prob, Fin.prod_univ_two,
      Fin.sum_univ_two, binaryVCG, Matrix.cons_val_zero, vec2_apply_one]
    norm_num
  have hwel : (∑ t, indepBinaryPrior.prob t *
      ∑ i, binaryAuctionVal i (t i) (binaryVCG.outcome t)) = 3 / 4 := by
    rw [sum_fin2_bool]
    simp only [indepBinaryPrior, CorrelatedPrior.product_prob, Fin.prod_univ_two,
      Fin.sum_univ_two, binaryVCG, binaryAuctionVal, Matrix.cons_val_zero, vec2_apply_one]
    norm_num
  refine ⟨hrev, hwel, ?_⟩
  rw [CorrelatedPrior.ExtractsFullSurplus, hrev, hwel]
  norm_num

/-- Strictly positive `{1, 2}` single-item auction valuations on `Option (Fin 2)`: under
`indepBinaryPrior`, *no* ex-post efficient, BIC, interim-IR mechanism can extract full surplus. -/
def posAuctionVal (i : Fin 2) (ti : Bool) : Option (Fin 2) → ℝ
  | none => 0
  | some j => if j = i then (if ti then 2 else 1) else 0

theorem not_exists_isBIC_extractsFullSurplus_posAuctionVal_indepBinaryPrior :
    ¬ ∃ D : IndirectMechanism (Fin 2) (fun _ => Bool) (Option (Fin 2)),
        D.IsExPostEfficient posAuctionVal ∧
        indepBinaryPrior.IsBIC posAuctionVal D ∧
        indepBinaryPrior.IsInterimIR posAuctionVal D ∧
        indepBinaryPrior.ExtractsFullSurplus posAuctionVal D := by
  rintro ⟨D, hEff, hBIC, hIR, hExt⟩
  have hzero := (indepBinaryPrior.extractsFullSurplus_iff_forall_interimUtility_eq_zero hIR).1 hExt
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin 2, D.outcome ![false, false] = some i₀ := by
    cases h : D.outcome ![false, false] with
    | none =>
      have key := hEff ![false, false] (some 0)
      simp only [h, Fin.sum_univ_two, posAuctionVal, Matrix.cons_val_zero, vec2_apply_one] at key
      norm_num at key
    | some i₀ => exact ⟨i₀, rfl⟩
  let w : {b : Bool // b ≠ false} → ℝ := fun _ => 1
  have huniv : (univ : Finset {b : Bool // b ≠ false}) = {⟨true, by decide⟩} := by
    ext ⟨b, hb⟩
    cases b
    · exact absurd rfl hb
    · simp only [mem_univ, mem_singleton]
  have hcomb : ∑ b : {b : Bool // b ≠ false}, w b • indepBinaryPrior.condBelief i₀ b.val =
      indepBinaryPrior.condBelief i₀ false := by
    funext t_opp
    rw [huniv, sum_singleton]
    simp only [w, one_smul, indepBinaryPrior, CorrelatedPrior.product_condBelief]
  have hrent := indepBinaryPrior.le_interimUtility_add_sum_of_convexComb hBIC
    (fun _ => zero_le_one) hcomb
  simp only [hzero, mul_zero, sum_const_zero, zero_add] at hrent
  rw [huniv, sum_singleton] at hrent
  dsimp only [w] at hrent
  simp only [one_mul, sum_oppHom, Fintype.sum_bool, indepBinaryPrior,
    CorrelatedPrior.product_condBelief, prod_oppFin2_const] at hrent
  have hext_ff : extendProfile (T := fun _ : Fin 2 => Bool) i₀ false (oppEquivHom i₀ false) =
      ![false, false] := by
    rcases fin2_eq_zero_or_one i₀ with rfl | rfl
    · exact extendProfile_hom_zero false false
    · exact extendProfile_hom_one false false
  rw [hext_ff, hi₀] at hrent
  have hnonneg_ft : 0 ≤ posAuctionVal i₀ true
        (D.outcome (extendProfile i₀ false (oppEquivHom i₀ true))) -
      posAuctionVal i₀ false
        (D.outcome (extendProfile i₀ false (oppEquivHom i₀ true))) := by
    cases D.outcome (extendProfile i₀ false (oppEquivHom i₀ true)) with
    | none => simp only [posAuctionVal]; norm_num
    | some j =>
      rcases fin2_eq_zero_or_one i₀ with rfl | rfl <;>
        rcases fin2_eq_zero_or_one j with rfl | rfl <;>
        simp only [posAuctionVal] <;> norm_num
  have hval_win : posAuctionVal i₀ true (some i₀) - posAuctionVal i₀ false (some i₀) = 1 := by
    rcases fin2_eq_zero_or_one i₀ with rfl | rfl <;> simp only [posAuctionVal] <;> norm_num
  rw [hval_win] at hrent
  linarith

end BinaryAuction

/-! ### 2. `4 × 3` rhombus-in-simplex prior separating `IsBIC` from `IsTruthful` -/

section RhombusSeparation

/-- Asymmetric type family `T 0 = Fin 4`, `T 1 = Fin 3`. -/
abbrev RhombusType : Fin 2 → Type
  | 0 => Fin 4
  | 1 => Fin 3

instance instFintypeRhombusType : ∀ i, Fintype (RhombusType i)
  | 0 => inferInstanceAs (Fintype (Fin 4))
  | 1 => inferInstanceAs (Fintype (Fin 3))

/-- Unnormalized positive integer weights `[[6, 2, 4], [2, 6, 4], [5, 5, 2], [3, 3, 6]]` summing
to `48`, with uniform row sums `12` and uniform column sums `16`. -/
def rhombusWeight : Matrix (Fin 4) (Fin 3) ℝ :=
  !![6, 2, 4; 2, 6, 4; 5, 5, 2; 3, 3, 6]

/-- The `4 × 3` joint prior `rhombusWeight (t 0) (t 1) / 48`. -/
noncomputable def rhombusPrior : CorrelatedPrior (Fin 2) RhombusType where
  prob t := rhombusWeight (t 0) (t 1) / 48
  prob_nonneg t := by
    have : ∀ (a : Fin 4) (b : Fin 3), 0 ≤ rhombusWeight a b / 48 := by
      rw [forall_fin4]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [forall_fin3] <;> refine ⟨?_, ?_, ?_⟩ <;>
        simp only [rhombusWeight] <;> norm_num
    exact this (t 0) (t 1)
  sum_prob_eq_one := by
    rw [sum_profile_eq (T := RhombusType) 0]
    simp only [sum_opp0, extendProfile_opp0_zero, extendProfile_opp0_one]
    change ∑ a : Fin 4, ∑ b : Fin 3, rhombusWeight a b / 48 = 1
    simp only [Fin.sum_univ_four, Fin.sum_univ_three, rhombusWeight]
    norm_num
  sum_prob_extendProfile_pos := by
    rw [Fin.forall_fin_two]
    constructor
    · change ∀ a : Fin 4, 0 < ∑ t_opp : OppProfile RhombusType 0, _
      rw [forall_fin4]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · rw [sum_opp0]
        simp only [extendProfile_opp0_zero, extendProfile_opp0_one]
        change 0 < ∑ b : Fin 3, rhombusWeight _ b / 48
        simp only [Fin.sum_univ_three, rhombusWeight]
        norm_num
    · change ∀ b : Fin 3, 0 < ∑ t_opp : OppProfile RhombusType 1, _
      rw [forall_fin3]
      refine ⟨?_, ?_, ?_⟩ <;>
      · rw [sum_opp1]
        simp only [extendProfile_opp1_zero, extendProfile_opp1_one]
        change 0 < ∑ a : Fin 4, rhombusWeight a _ / 48
        simp only [Fin.sum_univ_four, rhombusWeight]
        norm_num

theorem rhombusPrior_marginal_zero (a : RhombusType 0) :
    rhombusPrior.marginal 0 a = 1 / 4 := by
  revert a
  change ∀ x : Fin 4, rhombusPrior.marginal 0 x = 1 / 4
  rw [forall_fin4]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [CorrelatedPrior.marginal_apply, sum_opp0]
    simp only [rhombusPrior, extendProfile_opp0_zero, extendProfile_opp0_one]
    change (∑ b : Fin 3, rhombusWeight _ b / 48) = 1 / 4
    simp only [Fin.sum_univ_three, rhombusWeight]
    norm_num

theorem rhombusPrior_marginal_one (b : RhombusType 1) :
    rhombusPrior.marginal 1 b = 1 / 3 := by
  revert b
  change ∀ y : Fin 3, rhombusPrior.marginal 1 y = 1 / 3
  rw [forall_fin3]
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [CorrelatedPrior.marginal_apply, sum_opp1]
    simp only [rhombusPrior, extendProfile_opp1_zero, extendProfile_opp1_one]
    change (∑ a : Fin 4, rhombusWeight a _ / 48) = 1 / 3
    simp only [Fin.sum_univ_four, rhombusWeight]
    norm_num

theorem rhombusPrior_condBelief_zero (a : RhombusType 0) (b : RhombusType 1) :
    rhombusPrior.condBelief 0 a (oppEquiv0 b) = rhombusWeight a b / 12 := by
  rw [CorrelatedPrior.condBelief_apply, rhombusPrior_marginal_zero]
  simp only [rhombusPrior, extendProfile_opp0_zero, extendProfile_opp0_one]
  ring

theorem rhombusPrior_condBelief_one (b : RhombusType 1) (a : RhombusType 0) :
    rhombusPrior.condBelief 1 b (oppEquiv1 a) = rhombusWeight a b / 16 := by
  rw [CorrelatedPrior.condBelief_apply, rhombusPrior_marginal_one]
  simp only [rhombusPrior, extendProfile_opp1_zero, extendProfile_opp1_one]
  ring

/-- `rhombusPrior` fails `HasFullBeliefRank`: four belief rows in `ℝ³` satisfy
`B₀ 0 + B₀ 1 - B₀ 2 - B₀ 3 = 0`. -/
theorem not_hasFullBeliefRank_rhombusPrior : ¬ rhombusPrior.HasFullBeliefRank := by
  intro hRank
  have hLI := Fintype.linearIndependent_iff.1 (hRank 0)
  let c : Fin 4 → ℝ := ![1, 1, -1, -1]
  have hc0 : ∑ a : RhombusType 0, c a • rhombusPrior.condBelief 0 a = 0 := by
    funext t_opp
    obtain ⟨b, rfl⟩ := oppEquiv0.surjective t_opp
    change (∑ a : Fin 4, c a * rhombusPrior.condBelief 0 a (oppEquiv0 b)) = 0
    rw [Fin.sum_univ_four]
    repeat rw [rhombusPrior_condBelief_zero]
    revert b
    change ∀ y : Fin 3, _
    rw [forall_fin3]
    refine ⟨?_, ?_, ?_⟩ <;> simp only [c, rhombusWeight, Matrix.cons_val_zero] <;>
      norm_num
  have h0 : c (0 : Fin 4) = 0 := hLI c hc0 (0 : Fin 4)
  simp only [c, Matrix.cons_val_zero] at h0
  norm_num at h0

/-- Explicit integer separating lotteries certifying convex independence for player `0`'s four
conditional belief rows. -/
def rhombusLottery0 : Fin 4 → Fin 3 → ℝ
  | 0 => ![-1, 1, 1]
  | 1 => ![1, -1, 1]
  | 2 => ![-1, -1, 5]
  | 3 => ![1, 1, -1]

/-- Explicit integer separating lotteries certifying convex independence for player `1`'s three
conditional belief rows. -/
def rhombusLottery1 : Fin 3 → Fin 4 → ℝ
  | 0 => ![-3, 3, 0, 4]
  | 1 => ![3, -3, 0, 4]
  | 2 => ![0, 0, 3, -1]

/-- Despite failing `HasFullBeliefRank`, `rhombusPrior` satisfies `HasConvexIndependentBeliefs`. -/
theorem hasConvexIndependentBeliefs_rhombusPrior :
    rhombusPrior.HasConvexIndependentBeliefs := by
  rw [CorrelatedPrior.hasConvexIndependentBeliefs_iff, Fin.forall_fin_two]
  constructor
  · change ∀ r : Fin 4, _
    intro r
    rw [CorrelatedPrior.condBelief_notMem_convexHull_iff_exists_separating_lottery]
    refine ⟨fun t_opp => rhombusLottery0 r (oppEquiv0.symm t_opp), ?_, ?_⟩
    · simp only [mulVec, dotProduct, sum_opp0, Equiv.symm_apply_apply]
      change (∑ b : Fin 3, rhombusPrior.condBelief 0 r (oppEquiv0 b) * rhombusLottery0 r b) = 0
      rw [Fin.sum_univ_three]
      repeat rw [rhombusPrior_condBelief_zero]
      revert r
      rw [forall_fin4]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [rhombusWeight, rhombusLottery0] <;> norm_num
    · intro a hne
      simp only [mulVec, dotProduct, sum_opp0, Equiv.symm_apply_apply]
      change 0 < ∑ b : Fin 3, rhombusPrior.condBelief 0 a (oppEquiv0 b) * rhombusLottery0 r b
      rw [Fin.sum_univ_three]
      repeat rw [rhombusPrior_condBelief_zero]
      revert r a hne
      change ∀ (r a : Fin 4), a ≠ r → _
      rw [forall_fin4]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [forall_fin4] <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
        intro hne <;> (try exact absurd rfl hne) <;>
      · simp only [rhombusWeight, rhombusLottery0]
        norm_num
  · change ∀ r : Fin 3, _
    intro r
    rw [CorrelatedPrior.condBelief_notMem_convexHull_iff_exists_separating_lottery]
    refine ⟨fun t_opp => rhombusLottery1 r (oppEquiv1.symm t_opp), ?_, ?_⟩
    · simp only [mulVec, dotProduct, sum_opp1, Equiv.symm_apply_apply]
      change (∑ a : Fin 4, rhombusPrior.condBelief 1 r (oppEquiv1 a) * rhombusLottery1 r a) = 0
      rw [Fin.sum_univ_four]
      repeat rw [rhombusPrior_condBelief_one]
      revert r
      rw [forall_fin3]
      refine ⟨?_, ?_, ?_⟩ <;> simp only [rhombusWeight, rhombusLottery1] <;> norm_num
    · intro b hne
      simp only [mulVec, dotProduct, sum_opp1, Equiv.symm_apply_apply]
      change 0 < ∑ a : Fin 4, rhombusPrior.condBelief 1 b (oppEquiv1 a) * rhombusLottery1 r a
      rw [Fin.sum_univ_four]
      repeat rw [rhombusPrior_condBelief_one]
      revert r b hne
      change ∀ (r b : Fin 3), b ≠ r → _
      rw [forall_fin3]
      refine ⟨?_, ?_, ?_⟩ <;> rw [forall_fin3] <;> refine ⟨?_, ?_, ?_⟩ <;>
        intro hne <;> (try exact absurd rfl hne) <;>
      · simp only [rhombusWeight, rhombusLottery1]
        norm_num

/-- **Strict separation between Theorems 1 and 2 on `rhombusPrior`**: on `Ω = Bool`, universal
`IsTruthful` full surplus extraction fails, whereas universal `IsBIC` full surplus extraction
holds. -/
theorem rhombusPrior_separates_isBIC_from_isTruthful :
    (¬ ∀ val : (∀ i, RhombusType i → Bool → ℝ), (∀ i ti ω, 0 ≤ val i ti ω) →
        ∃ D : IndirectMechanism (Fin 2) RhombusType Bool,
          D.IsExPostEfficient val ∧
          D.IsTruthful val ∧
          rhombusPrior.IsInterimIR val D ∧
          rhombusPrior.ExtractsFullSurplus val D) ∧
    (∀ val : (∀ i, RhombusType i → Bool → ℝ), (∀ i ti ω, 0 ≤ val i ti ω) →
        ∃ D : IndirectMechanism (Fin 2) RhombusType Bool,
          D.IsExPostEfficient val ∧
          rhombusPrior.IsBIC val D ∧
          rhombusPrior.IsInterimIR val D ∧
          rhombusPrior.ExtractsFullSurplus val D) :=
  ⟨mt (rhombusPrior.hasFullBeliefRank_iff_forall_exists_isTruthful Bool).2
      not_hasFullBeliefRank_rhombusPrior,
    (rhombusPrior.hasConvexIndependentBeliefs_iff_forall_exists_isBIC Bool).1
      hasConvexIndependentBeliefs_rhombusPrior⟩

end RhombusSeparation

/-! ### 3. `3 × 2` collinear-beliefs impossibility witness -/

section CollinearImpossibility

/-- Type family `T 0 = Fin 3`, `T 1 = Bool`. -/
abbrev CollinearType : Fin 2 → Type
  | 0 => Fin 3
  | 1 => Bool

instance instFintypeCollinearType : ∀ i, Fintype (CollinearType i)
  | 0 => inferInstanceAs (Fintype (Fin 3))
  | 1 => inferInstanceAs (Fintype Bool)

instance instDecidableEqCollinearType : ∀ i, DecidableEq (CollinearType i)
  | 0 => inferInstanceAs (DecidableEq (Fin 3))
  | 1 => inferInstanceAs (DecidableEq Bool)

/-- Unnormalized positive weights `[[3, 1], [2, 2], [1, 3]]` summing to `12`. -/
def collinearWeight (a : Fin 3) (b : Bool) : ℝ :=
  match a, b with
  | 0, false => 3
  | 0, true => 1
  | 1, false => 2
  | 1, true => 2
  | 2, false => 1
  | 2, true => 3

/-- The `3 × 2` joint prior `collinearWeight (t 0) (t 1) / 12`, under which player `0`'s conditional
beliefs on `Bool` are `(3/4, 1/4)`, `(1/2, 1/2)`, and `(1/4, 3/4)`. -/
noncomputable def collinearPrior : CorrelatedPrior (Fin 2) CollinearType where
  prob t := collinearWeight (t 0) (t 1) / 12
  prob_nonneg t := by
    have : ∀ (a : Fin 3) (b : Bool), 0 ≤ collinearWeight a b / 12 := by
      rw [forall_fin3]
      refine ⟨?_, ?_, ?_⟩ <;> rw [Bool.forall_bool] <;> refine ⟨?_, ?_⟩ <;>
        simp only [collinearWeight] <;> norm_num
    exact this (t 0) (t 1)
  sum_prob_eq_one := by
    rw [sum_profile_eq (T := CollinearType) 0]
    simp only [sum_opp0, extendProfile_opp0_zero, extendProfile_opp0_one]
    change ∑ a : Fin 3, ∑ b : Bool, collinearWeight a b / 12 = 1
    simp only [Fin.sum_univ_three, Fintype.sum_bool, collinearWeight]
    norm_num
  sum_prob_extendProfile_pos := by
    rw [Fin.forall_fin_two]
    constructor
    · change ∀ a : Fin 3, 0 < ∑ t_opp : OppProfile CollinearType 0, _
      rw [forall_fin3]
      refine ⟨?_, ?_, ?_⟩ <;>
      · rw [sum_opp0]
        simp only [extendProfile_opp0_zero, extendProfile_opp0_one]
        change 0 < ∑ b : Bool, collinearWeight _ b / 12
        simp only [Fintype.sum_bool, collinearWeight]
        norm_num
    · change ∀ b : Bool, 0 < ∑ t_opp : OppProfile CollinearType 1, _
      rw [Bool.forall_bool]
      refine ⟨?_, ?_⟩ <;>
      · rw [sum_opp1]
        simp only [extendProfile_opp1_zero, extendProfile_opp1_one]
        change 0 < ∑ a : Fin 3, collinearWeight a _ / 12
        simp only [Fin.sum_univ_three, collinearWeight]
        norm_num

theorem collinearPrior_marginal_zero (a : CollinearType 0) :
    collinearPrior.marginal 0 a = 1 / 3 := by
  revert a
  change ∀ x : Fin 3, collinearPrior.marginal 0 x = 1 / 3
  rw [forall_fin3]
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [CorrelatedPrior.marginal_apply, sum_opp0]
    simp only [collinearPrior, extendProfile_opp0_zero, extendProfile_opp0_one]
    change (∑ b : Bool, collinearWeight _ b / 12) = 1 / 3
    simp only [Fintype.sum_bool, collinearWeight]
    norm_num

theorem collinearPrior_condBelief_zero (a : CollinearType 0) (b : CollinearType 1) :
    collinearPrior.condBelief 0 a (oppEquiv0 b) = collinearWeight a b / 4 := by
  rw [CorrelatedPrior.condBelief_apply, collinearPrior_marginal_zero]
  simp only [collinearPrior, extendProfile_opp0_zero, extendProfile_opp0_one]
  ring

/-- Type `1`'s conditional belief `(1/2, 1/2)` is the exact midpoint of type `0`'s `(3/4, 1/4)` and
type `2`'s `(1/4, 3/4)`. -/
theorem collinearPrior_midpoint :
    collinearPrior.condBelief 0 (1 : Fin 3) =
      (1 / 2 : ℝ) • collinearPrior.condBelief 0 (0 : Fin 3) +
        (1 / 2 : ℝ) • collinearPrior.condBelief 0 (2 : Fin 3) := by
  funext t_opp
  obtain ⟨b, rfl⟩ := oppEquiv0.surjective t_opp
  change collinearPrior.condBelief 0 (1 : Fin 3) (oppEquiv0 b) =
    (1 / 2 : ℝ) * collinearPrior.condBelief 0 (0 : Fin 3) (oppEquiv0 b) +
      (1 / 2 : ℝ) * collinearPrior.condBelief 0 (2 : Fin 3) (oppEquiv0 b)
  rw [collinearPrior_condBelief_zero, collinearPrior_condBelief_zero,
    collinearPrior_condBelief_zero]
  cases b <;> simp only [collinearWeight] <;> norm_num

theorem univ_fin3_ne_one :
    (univ : Finset {a : Fin 3 // a ≠ 1}) = {⟨0, by decide⟩, ⟨2, by decide⟩} := by
  ext ⟨a, ha⟩
  rcases fin3_cases a with rfl | rfl | rfl
  · decide +revert
  · exact absurd rfl ha
  · decide +revert

theorem not_hasConvexIndependentBeliefs_collinearPrior :
    ¬ collinearPrior.HasConvexIndependentBeliefs := by
  rw [CorrelatedPrior.hasConvexIndependentBeliefs_iff]
  push Not
  refine ⟨0, (1 : Fin 3), (collinearPrior.condBelief_mem_convexHull_iff 0 (1 : Fin 3)).2 ?_⟩
  let w : {a : Fin 3 // a ≠ 1} → ℝ := fun _ => 1 / 2
  refine ⟨w, isMixedStrategy_iff.2 ⟨fun _ => by norm_num, ?_⟩, ?_⟩
  · rw [univ_fin3_ne_one, sum_pair (by decide)]
    dsimp only [w]
    norm_num
  · rw [univ_fin3_ne_one, sum_pair (by decide)]
    exact collinearPrior_midpoint.symm

/-- Explicit nonnegative valuation on `Ω = Bool` (`false` gives `0`; `true` gives `1` to player `0`
of middle type `1` and `2` to extreme types `0` and `2`, and `0` to player `1`). -/
def collinearVal : ∀ i : Fin 2, CollinearType i → Bool → ℝ
  | 0, a, true => if a = (1 : Fin 3) then 1 else 2
  | 0, _, false => 0
  | 1, _, _ => 0

/-- Under `collinearPrior` and `collinearVal`, *every* ex-post efficient, BIC, interim-IR mechanism
leaves strictly positive interim rent (`(U(0) + U(2))/2 ≥ U(1) + 1`), so no such mechanism extracts
the full surplus. -/
theorem not_exists_isBIC_extractsFullSurplus_collinearPrior :
    ¬ ∃ D : IndirectMechanism (Fin 2) CollinearType Bool,
        D.IsExPostEfficient collinearVal ∧
        collinearPrior.IsBIC collinearVal D ∧
        collinearPrior.IsInterimIR collinearVal D ∧
        collinearPrior.ExtractsFullSurplus collinearVal D := by
  rintro ⟨D, hEff, hBIC, hIR, hExt⟩
  have hzero := (collinearPrior.extractsFullSurplus_iff_forall_interimUtility_eq_zero hIR).1 hExt
  have hout : ∀ t, D.outcome t = true := fun t => by
    cases h : D.outcome t with
    | true => rfl
    | false =>
      have key := hEff t true
      rw [h] at key
      rcases fin3_cases (t 0) with h0 | h0 | h0 <;>
        simp only [Fin.sum_univ_two, collinearVal, h0] at key <;> norm_num at key
  let w : {a : Fin 3 // a ≠ (1 : Fin 3)} → ℝ := fun _ => 1 / 2
  have hcomb : ∑ a : {a : Fin 3 // a ≠ (1 : Fin 3)}, w a • collinearPrior.condBelief 0 a.val =
      collinearPrior.condBelief 0 (1 : Fin 3) := by
    rw [univ_fin3_ne_one, sum_pair (by decide)]
    exact collinearPrior_midpoint.symm
  have hrent :=
    collinearPrior.le_interimUtility_add_sum_of_convexComb (i₀ := 0) (ti₀ := (1 : Fin 3))
      hBIC (fun _ => by norm_num) hcomb
  simp only [hzero, mul_zero, sum_const_zero, zero_add, hout] at hrent
  rw [univ_fin3_ne_one, sum_pair (by decide)] at hrent
  dsimp only [w] at hrent
  simp only [sum_opp0, Fintype.sum_bool, collinearVal, ↓reduceIte] at hrent
  repeat rw [collinearPrior_condBelief_zero] at hrent
  simp only [collinearWeight] at hrent
  norm_num at hrent

end CollinearImpossibility

end CslibFrontierTests.GameTheory.CremerMcLean
