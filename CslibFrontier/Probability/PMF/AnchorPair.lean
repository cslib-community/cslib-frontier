/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Coin
public import CslibFrontier.Probability.Conditioning

/-!
# Independent erasure of a pair

For each component of a pair, independently sample whether to retain it or replace it
with `none`. The resulting distribution records the original joint mass when both
components survive and the corresponding marginal when one survives.
-/

public section

open scoped unitInterval ENNReal

namespace Cslib.Probability.PMF

/-- Replace either component of a joint draw by `none`, with independent replacement flags. -/
@[expose] noncomputable def anchorPair {X Y : Type*} (μ : PMF (X × Y)) (α β : I) :
    PMF (Option X × Option Y) :=
  (coin α).bind fun i => (coin β).bind fun j =>
    μ.map fun q => (if i then none else some q.1, if j then none else some q.2)

/-- Exchanging the two components also exchanges their erasure rates. -/
theorem map_swap_anchorPair {X Y : Type*} (μ : PMF (X × Y)) (α β : I) :
    (anchorPair μ α β).map Prod.swap = anchorPair (μ.map Prod.swap) β α := by
  simp only [anchorPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
  exact PMF.bind_comm _ _ _

/-- If only one question is retained, its law is the corresponding original marginal.
The two anchor flags contribute their independent masses in each case. -/
theorem anchorPair_apply {X Y : Type*} (μ : PMF (X × Y)) (α β : I)
    (x : Option X) (y : Option Y) :
    anchorPair μ α β (x, y) =
      match x, y with
      | none, none => ENNReal.ofReal (α : ℝ) * ENNReal.ofReal (β : ℝ)
      | some x, none =>
        ENNReal.ofReal (1 - (α : ℝ)) * ENNReal.ofReal (β : ℝ) * (μ.map Prod.fst) x
      | none, some y =>
        ENNReal.ofReal (α : ℝ) * ENNReal.ofReal (1 - (β : ℝ)) * (μ.map Prod.snd) y
      | some x, some y =>
        ENNReal.ofReal (1 - (α : ℝ)) * ENNReal.ofReal (1 - (β : ℝ)) * μ (x, y) := by
  classical
  cases x <;> cases y
  case some.some x y =>
    have hm : (∑' q : X × Y, if x = q.1 ∧ y = q.2 then μ q else 0) =
        μ (x, y) := by
      rw [tsum_eq_single (x, y)]
      · simp
      · rintro ⟨x', y'⟩ h
        exact ite_eq_right fun hp => h (Prod.ext hp.1.symm hp.2.symm)
    simp [anchorPair, PMF.bind_apply, tsum_fintype, coin_apply, PMF.map_apply, mul_assoc, hm]
  all_goals
    simp [anchorPair, PMF.bind_apply, tsum_fintype, coin_apply, PMF.map_apply, mul_assoc]

/-- The first marginal depends only on the first erasure rate. -/
theorem map_fst_anchorPair_apply {X Y : Type*} (μ : PMF (X × Y)) (α β : I) (m : Option X) :
    ((anchorPair μ α β).map Prod.fst) m =
      match m with
      | none => ENNReal.ofReal (α : ℝ)
      | some x => ENNReal.ofReal (1 - (α : ℝ)) * (μ.map Prod.fst) x := by
  classical
  cases m <;> simp [anchorPair, PMF.map_bind, PMF.map_comp, Function.comp_def,
    PMF.bind_const, PMF.bind_apply, tsum_fintype, coin_apply, PMF.map_apply]

/-- Changing only the first erasure rate does not change the conditional law of the second
outcome at a supported first outcome whose slice is retained under the new rate. -/
theorem conditionalSnd_anchorPair_left_rate {X Y : Type*} (μ : PMF (X × Y))
    (α α' β : I) (m : Option X)
    (hm : m ∈ ((anchorPair μ α β).map Prod.fst).support)
    (hα' : coin α' m.isNone ≠ 0) :
    conditionalSnd (anchorPair μ α β) m = conditionalSnd (anchorPair μ α' β) m := by
  let P := anchorPair μ α β
  let Q := anchorPair μ α' β
  let c := coin α m.isNone
  let d := coin α' m.isNone
  have hscale (y : Option Y) : d * P (m, y) = c * Q (m, y) := by
    cases m <;> cases y <;>
      simp only [P, Q, c, d, anchorPair_apply, coin_apply, Option.isNone, ite_true,
        Bool.false_eq_true, ite_false] <;> ac_rfl
  exact conditionalSnd_eq_of_scaled_slices P Q m m d c hm hα' (PMF.apply_ne_top _ _) hscale

/-- The second erase flag stays independent of any supported first outcome. -/
theorem conditionalSnd_anchorPair_none {X Y : Type*} (μ : PMF (X × Y)) (α β : I) (m : Option X)
    (hm : m ∈ ((anchorPair μ α β).map Prod.fst).support) :
    conditionalSnd (anchorPair μ α β) m none = ENNReal.ofReal (β : ℝ) := by
  let P := anchorPair μ α β
  apply (ENNReal.mul_right_inj ((PMF.mem_support_iff _ _).mp hm) (PMF.apply_ne_top _ _)).mp
  change (P.map Prod.fst) m * conditionalSnd P m none = _
  rw [marginal_mul_conditionalSnd]
  cases m with
  | none => simp only [P, anchorPair_apply, map_fst_anchorPair_apply]
  | some x =>
    simp only [P, anchorPair_apply, map_fst_anchorPair_apply]
    ac_rfl

end Cslib.Probability.PMF
