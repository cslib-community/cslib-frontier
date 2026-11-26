/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevOddErrors
public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.DepthTwoInputs
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Truncated depth-two circuits for Andreev's function

This module builds the circuits of Theorem 7 of C. Reitwiessner, *Depth-Two Threshold Circuits
for Andreev's Function* (preprint, November 2026) for Andreev's function [Andreev1987]. Based on
the truncated-vote error analysis of `AndreevOddErrors`, the truncated vote
`andreevTruncatedVote b m r R` becomes a depth-two threshold circuit, and the parameters are
chosen.

`f_R` is a staircase of `2 R + 2` steps (`altLinearTrunc_eq_sum`, in `DepthTwo.lean`), so the
truncated score `P_R` is `2 X_∅` plus a weighted sum of the indicators `[θ_k ≤ X_S ± D_S]` over
the nonempty prefix subsets `S`, both reflected forms and the steps `k`
(`andreevTruncatedScore_eq_sum`). `andreevTruncatedCircuit b m r R` has these
`4 (2 ^ r - 1) (R + 1)` indicators as bottom gates. Their weights are `-2 χ_S(c)` on the table and
`±1` on the blocks in `S`, so they are sign-coherent (`isSignCoherent_andreevTruncatedBottomOp`).
The output gate, built with `depthTwoInputs`, also reads the table bits for the affine term
(`eval_andreevTruncatedCircuit`).

## Main definitions

* `AndreevTruncatedBottomIndex`: the bottom gates, by subset, reflected form and step.
* `andreevTruncatedCircuit`: the truncated circuit.
* `andreevVoteLevel`: the number `r` of characters kept in Part 2.

## Main results

* `eval_andreevTruncatedCircuit`, `size_andreevTruncatedCircuit`,
  `depth_andreevTruncatedCircuit_le`, `wireCount_andreevTruncatedCircuit_le`,
  `isSignCoherent_andreevTruncatedBottomOp`: the circuit computes the truncated vote with
  `4 (2 ^ r - 1) (R + 1) + 1` gates at depth `2`, with sign-coherent bottom gates.
* `card_eval_andreevTruncatedCircuit_ne_subcubeEval_le`: it differs from the subcube vote on at
  most a `(16 v / 2 ^ r) exp (-R² / (16 v))` fraction of the inputs.
* `card_eval_andreevTruncatedCircuit_ne_andreev_le`,
  `half_add_mul_le_card_eval_andreevTruncatedCircuit_eq_andreev`: Thm. 7, Parts 1 and 2, as
  explicit finite statements for all `k, m`.
* `size_andreevTruncatedCircuit_le_of_balanced`, `andreevTruncatedCircuit_part_two_of_balanced`:
  at balance `k m = N`, Part 1 with at most `64 n √(n log (1 / δ))` gates, and Part 2 with at most
  `2600 ε² n √(n log (1 / ε))` gates and `5300 ε² n² √(n log (1 / ε))` active wires, for
  `1 / √N ≤ ε ≤ 1 / 8`.

## Differences from the preprint

* The constants of the `O(·)` bounds are explicit and not optimized. Gates are counted with the
  output gate, and `n` is used in place of `N = n / 2` where that is simpler.
* The preprint takes `δ = 1 / 2 - ε` in Part 1 for `1 / 8 < ε < 1 / 2`; that case is the Part 1
  statement with this `δ` and is not restated.

## References

* [A. E. Andreev, *On a method for obtaining more than quadratic effective lower bounds for the
  complexity of π-schemes*][Andreev1987]
* C. Reitwiessner, *Depth-Two Threshold Circuits for Andreev's Function*, preprint (November
  2026), Theorem 7 (`thm:avgupper`).
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset Real

/-! ### The circuit -/

/-- A bottom gate of `andreevTruncatedCircuit b m r R`, the indicator `[θ_k ≤ X_S ± D_S]`. -/
structure AndreevTruncatedBottomIndex (b r R : ℕ) where
  /-- The nonempty prefix subset `S`. -/
  subset : Finset (Fin b)
  /-- `S` is a nonempty subset of the first `r` blocks. -/
  mem : subset ∈ andreevPrefixSubsetsNonempty b r
  /-- The reflected form: `X_S + D_S` for `true` and `X_S - D_S` for `false`. -/
  form : Bool
  /-- The step `k < 2 R + 2` of the staircase of `f_R`. -/
  step : Fin (2 * R + 2)

/-- The bottom-gate index as a triple of a subset, a form and a step. -/
def AndreevTruncatedBottomIndex.equivProd (b r R : ℕ) :
    AndreevTruncatedBottomIndex b r R ≃
      {S : Finset (Fin b) // S ∈ andreevPrefixSubsetsNonempty b r} × Bool × Fin (2 * R + 2) where
  toFun i := (⟨i.subset, i.mem⟩, i.form, i.step)
  invFun := fun ⟨⟨S, hS⟩, τ, k⟩ => ⟨S, hS, τ, k⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (b r R : ℕ) : Fintype (AndreevTruncatedBottomIndex b r R) :=
  Fintype.ofEquiv _ (AndreevTruncatedBottomIndex.equivProd b r R).symm

theorem card_andreevTruncatedBottomIndex (b r R : ℕ) :
    Fintype.card (AndreevTruncatedBottomIndex b r R) =
      4 * #(andreevPrefixSubsetsNonempty b r) * (R + 1) := by
  rw [Fintype.card_congr (AndreevTruncatedBottomIndex.equivProd b r R)]
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool, Fintype.card_fin]
  ring

/-- Numbering of the bottom gates of `andreevTruncatedCircuit b m r R`. -/
noncomputable def andreevTruncatedBottomEquiv (b r R : ℕ) :
    AndreevTruncatedBottomIndex b r R ≃ Fin (4 * #(andreevPrefixSubsetsNonempty b r) * (R + 1)) :=
  Fintype.equivFinOfCardEq (card_andreevTruncatedBottomIndex b r R)

/-- The shift `±(|S| m / 2 - ⌊|S| m / 2⌋)` of the reflected form `X_S ± D_S` from its centred
weighted bit sum (`cast_andreevReflectedForm_eq`). -/
noncomputable def andreevReflectedOffset {b : ℕ} (m : ℕ) (S : Finset (Fin b)) (τ : Bool) : ℝ :=
  (if τ then 1 else -1) * ((#S * m : ℝ) / 2 - andreevWindowCenter m S)

/-- The bottom gate `[θ_k ≤ X_S ± D_S]` of `andreevTruncatedCircuit b m r R`, as a gate on all
inputs with weights `andreevReflectedWeight`. -/
noncomputable abbrev andreevTruncatedBottomOp (b m r R : ℕ)
    (j : Fin (4 * #(andreevPrefixSubsetsNonempty b r) * (R + 1))) : Op :=
  let idx := (andreevTruncatedBottomEquiv b r R).symm j
  { arity := 2 ^ b + b * m
    weight := andreevReflectedWeight b m idx.subset idx.form
    threshold := (altLinearTruncThreshold R idx.step : ℝ) -
      andreevReflectedOffset m idx.subset idx.form +
        (∑ i, andreevReflectedWeight b m idx.subset idx.form i) / 2 }

/-- The weight of the output gate on bottom gate `(S, τ, k)`: `-η_S (f_R(θ_k) - f_R(θ_k - 1))`. -/
noncomputable def andreevTruncatedTopWeight (b m r R : ℕ)
    (j : Fin (4 * #(andreevPrefixSubsetsNonempty b r) * (R + 1))) : ℝ :=
  -((andreevReflectionSign m ((andreevTruncatedBottomEquiv b r R).symm j).subset *
    altLinearTruncStep R ((andreevTruncatedBottomEquiv b r R).symm j).step : ℤ) : ℝ)

/-- The input weights of the output gate: `4` on the table bits (the affine term `-2 X_∅`) and `0`
on the address bits. -/
noncomputable def andreevTruncatedInputWeight (b m : ℕ) : Fin (2 ^ b + b * m) → ℝ :=
  Fin.addCases (fun _ => 4) (fun _ => 0)

/-- **The truncated circuit** (preprint, proof of Thm. 7): a depth-two threshold circuit with
`4 (2 ^ r - 1) (R + 1)` sign-coherent bottom gates `[θ_k ≤ X_S ± D_S]` and an output gate that
also reads the table bits. It computes the truncated vote `andreevTruncatedVote b m r R`
(`eval_andreevTruncatedCircuit`). -/
noncomputable def andreevTruncatedCircuit (b m r R : ℕ) : Circuit signature (2 ^ b + b * m) 1 :=
  depthTwoInputs (andreevTruncatedBottomOp b m r R) (fun _ => id)
    (andreevTruncatedTopWeight b m r R) (andreevTruncatedInputWeight b m)
    ((1 - andreevVoteThreshold b r + 2 * 2 ^ b : ℤ) : ℝ)

/-- Bottom gate `(S, τ, k)` outputs `[θ_k ≤ X_S ± D_S]`. -/
theorem interpretation_andreevTruncatedBottomOp (b m r R : ℕ)
    (j : Fin (4 * #(andreevPrefixSubsetsNonempty b r) * (R + 1)))
    (w : BitString (2 ^ b + b * m)) :
    interpretation (andreevTruncatedBottomOp b m r R j) w =
      let idx := (andreevTruncatedBottomEquiv b r R).symm j
      decide (altLinearTruncThreshold R idx.step ≤
        andreevReflectedForm b m idx.subset idx.form w) := by
  set idx := (andreevTruncatedBottomEquiv b r R).symm j
  have hU := cast_andreevReflectedForm_eq b m idx.subset idx.form w
  have hsum : ∑ i, andreevReflectedWeight b m idx.subset idx.form i * (((w i).toNat : ℝ) - 1 / 2) =
      ∑ i, andreevReflectedWeight b m idx.subset idx.form i * ((w i).toNat : ℝ) -
        (∑ i, andreevReflectedWeight b m idx.subset idx.form i) / 2 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul]
    ring
  simp only [interpretation, andreevTruncatedBottomOp, decide_eq_decide, ← @Int.cast_le ℝ, hU, hsum]
  refine sub_nonneg.symm.trans ((iff_of_eq (congrArg (0 ≤ ·) ?_)).trans sub_nonneg)
  dsimp only [andreevReflectedOffset]; ring

/-- The truncated score in staircase form:
`P_R = 2 X_∅ + ∑_{S, τ, k} η_S (f_R(θ_k) - f_R(θ_k - 1)) [θ_k ≤ X_S ± D_S]`. -/
theorem andreevTruncatedScore_eq_sum (b m r R : ℕ) (w : BitString (2 ^ b + b * m)) :
    andreevTruncatedScore b m r R w = 2 * andreevTableScore b m ∅ w +
      ∑ idx : AndreevTruncatedBottomIndex b r R,
        andreevReflectionSign m idx.subset * altLinearTruncStep R idx.step *
          (decide (altLinearTruncThreshold R idx.step ≤
            andreevReflectedForm b m idx.subset idx.form w)).toNat := by
  rw [andreevTruncatedScore, ← (AndreevTruncatedBottomIndex.equivProd b r R).symm.sum_comp,
    Fintype.sum_prod_type, ← sum_coe_sort]
  congr 1
  refine sum_congr rfl fun S _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_bool, altLinearTrunc_eq_sum,
    altLinearTrunc_eq_sum, mul_add, mul_sum, mul_sum]
  simp only [altLinearTruncStep, altLinearTruncThreshold, mul_assoc]
  rfl

/-- The table score of `∅` is `N - 2 ∑_c x_c`. -/
private theorem cast_andreevTableScore_empty (b m : ℕ) (w : BitString (2 ^ b + b * m)) :
    (andreevTableScore b m ∅ w : ℝ) =
      2 ^ b - 2 * ∑ idx : Fin (2 ^ b), ((w (Fin.castAdd (b * m) idx)).toNat : ℝ) := by
  rw [andreevTableScore, Int.cast_sum, ← (BitString.equivFin b).sum_comp]
  simp only [chi_empty, one_mul, andreevTable, andreevTableIndex, Int.cast_sub, Int.cast_one,
    Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, sum_sub_distrib, sum_const, card_univ,
    BitString.card, nsmul_eq_mul, mul_one, ← mul_sum]
  push_cast
  ring

/-- **The truncated circuit computes the truncated vote.** -/
theorem eval_andreevTruncatedCircuit (b m r R : ℕ) (w : BitString (2 ^ b + b * m)) (o : Fin 1) :
    (andreevTruncatedCircuit b m r R).eval interpretation w o = andreevTruncatedVote b m r R w := by
  rw [andreevTruncatedCircuit, eval_depthTwoInputs, andreevTruncatedVote]
  simp only [id, interpretation_andreevTruncatedBottomOp]
  have htop : ∑ j, andreevTruncatedTopWeight b m r R j *
      ((let idx := (andreevTruncatedBottomEquiv b r R).symm j
        decide (altLinearTruncThreshold R idx.step ≤
          andreevReflectedForm b m idx.subset idx.form w)).toNat : ℝ) =
      -((andreevTruncatedScore b m r R w - 2 * andreevTableScore b m ∅ w : ℤ) : ℝ) := by
    rw [andreevTruncatedScore_eq_sum, add_sub_cancel_left, Int.cast_sum, ← sum_neg_distrib,
      ← (andreevTruncatedBottomEquiv b r R).symm.sum_comp]
    refine sum_congr rfl fun idx _ => ?_
    simp only [andreevTruncatedTopWeight]
    push_cast; ring
  have hinput : ∑ i, andreevTruncatedInputWeight b m i * ((w i).toNat : ℝ) =
      2 * 2 ^ b - 2 * (andreevTableScore b m ∅ w : ℝ) := by
    rw [cast_andreevTableScore_empty, Fin.sum_univ_add]
    simp only [andreevTruncatedInputWeight, Fin.addCases_left, Fin.addCases_right, zero_mul,
      sum_const_zero, add_zero, ← mul_sum]
    ring
  rw [htop, hinput, decide_eq_decide]
  refine Iff.trans ?_ (by omega : 1 - andreevVoteThreshold b r ≤
    -andreevTruncatedScore b m r R w ↔ _)
  rw [← @Int.cast_le ℝ]
  constructor <;> intro h <;> push_cast at h ⊢ <;> linarith only [h]

/-- `andreevTruncatedCircuit b m r R` has `4 (2 ^ r - 1) (R + 1)` bottom gates and one output
gate. -/
theorem size_andreevTruncatedCircuit {b r : ℕ} (hr : r ≤ b) (m R : ℕ) :
    (andreevTruncatedCircuit b m r R).size = 4 * (2 ^ r - 1) * (R + 1) + 1 := by
  rw [andreevTruncatedCircuit, size_depthTwoInputs, card_andreevPrefixSubsetsNonempty hr]

theorem depth_andreevTruncatedCircuit_le (b m r R : ℕ) :
    (andreevTruncatedCircuit b m r R).depth ≤ 2 :=
  depth_depthTwoInputs_le _ _ _ _ _

/-- `andreevTruncatedCircuit b m r R` has at most `(G + 1) n + G + 1 + n` active wires for
`G = 4 (2 ^ r - 1) (R + 1)` bottom gates and `n = N + k m` inputs. -/
theorem wireCount_andreevTruncatedCircuit_le {b r : ℕ} (hr : r ≤ b) (m R : ℕ) :
    (andreevTruncatedCircuit b m r R).wireCount ≤
      (4 * (2 ^ r - 1) * (R + 1) + 1) * (2 ^ b + b * m) +
        (4 * (2 ^ r - 1) * (R + 1) + 1 + (2 ^ b + b * m)) := by
  rw [andreevTruncatedCircuit, ← card_andreevPrefixSubsetsNonempty hr]
  exact wireCount_depthTwoInputs_le (andreevTruncatedBottomOp b m r R) (fun _ => id)
    (andreevTruncatedTopWeight b m r R) (andreevTruncatedInputWeight b m)
    ((1 - andreevVoteThreshold b r + 2 * 2 ^ b : ℤ) : ℝ) (A := 2 ^ b + b * m) fun _ => le_rfl

/-- **The bottom gates are sign-coherent**: inside every address block, the weights of a bottom
gate are all `1`, all `-1` or all `0`. -/
theorem isSignCoherent_andreevTruncatedBottomOp (b m r R : ℕ)
    (j : Fin (4 * #(andreevPrefixSubsetsNonempty b r) * (R + 1))) :
    IsSignCoherent (andreevBlockVar b m) (argWeight (andreevTruncatedBottomOp b m r R j) id) := by
  rw [argWeight_id]
  intro i
  simp only [andreevReflectedWeight, andreevBlockVar, Fin.addCases_right, Equiv.symm_apply_apply]
  by_cases hi : i ∈ ((andreevTruncatedBottomEquiv b r R).symm j).subset <;>
    cases ((andreevTruncatedBottomEquiv b r R).symm j).form
  · exact .inr fun _ => by simp [hi]
  all_goals exact .inl fun _ => by simp [hi]

/-! ### Theorem 7 -/

/-- **Disagreement of the truncated circuit with the subcube vote**: on at most a
`(16 v / q) exp (-R² / (16 v))` fraction of the inputs. -/
theorem card_eval_andreevTruncatedCircuit_ne_subcubeEval_le {b r : ℕ} (hr : r ≤ b) (m R : ℕ) :
    (#{w : BitString (2 ^ b + b * m) |
        (andreevTruncatedCircuit b m r R).eval interpretation w 0 ≠ andreevSubcubeEval b m r w} :
        ℝ) ≤
      2 ^ (2 ^ b + b * m) * (16 * andreevVarianceProxy b m / 2 ^ r *
        exp (-((R : ℝ) ^ 2 / (16 * andreevVarianceProxy b m)))) := by
  simpa only [eval_andreevTruncatedCircuit] using
    card_andreevTruncatedVote_ne_subcubeEval_le_exp hr m R

/-- **Thm. 7, Part 1, explicit form**: for `δ > 0`, the truncated circuit at `q = N` with radius
`R = andreevTruncationRadius b m b δ` differs from `andreev b m` on at most a `δ` fraction of the
inputs. It has `4 (N - 1) (R + 1) + 1` gates (`size_andreevTruncatedCircuit`) and
sign-coherent bottom gates (`isSignCoherent_andreevTruncatedBottomOp`). -/
theorem card_eval_andreevTruncatedCircuit_ne_andreev_le (b m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (#{w : BitString (2 ^ b + b * m) |
        (andreevTruncatedCircuit b m b (andreevTruncationRadius b m b δ)).eval interpretation w 0 ≠
          andreev b m w} : ℝ) ≤
      δ * 2 ^ (2 ^ b + b * m) := by
  simpa only [eval_andreevTruncatedCircuit] using
    card_andreevTruncatedVote_ne_andreev_le_of_radius b m hδ

/-- **Thm. 7, Part 2, explicit form**: if `32 ε² N ≤ q = 2 ^ r < N` and `ε > 0`, the truncated
circuit with radius `R = andreevTruncationRadius b m r ε` agrees with `andreev b m` on at least a
`1 / 2 + ε` fraction of the inputs. -/
theorem half_add_mul_le_card_eval_andreevTruncatedCircuit_eq_andreev {b r : ℕ} (hr : r < b)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) (hq : 32 * ε ^ 2 * 2 ^ b ≤ 2 ^ r) :
    (1 / 2 + ε) * 2 ^ (2 ^ b + b * m) ≤
      (#{w : BitString (2 ^ b + b * m) |
        (andreevTruncatedCircuit b m r (andreevTruncationRadius b m r ε)).eval interpretation w 0 =
          andreev b m w} : ℝ) := by
  simpa only [eval_andreevTruncatedCircuit] using
    half_add_mul_le_card_andreevTruncatedVote_eq_andreev hr m hε hq

/-- The radius is at most `4 √(v log (16 v / (q δ))) + 1`. -/
theorem andreevTruncationRadius_le (b m r : ℕ) (δ : ℝ) :
    (andreevTruncationRadius b m r δ : ℝ) ≤
      4 * Real.sqrt (andreevVarianceProxy b m *
        Real.log (16 * andreevVarianceProxy b m / (2 ^ r * δ))) + 1 :=
  (Nat.ceil_lt_add_one (by positivity)).le

/-- At balance (`k m = N`), `v = 5 N / 4`. -/
private theorem andreevVarianceProxy_of_balanced {b m : ℕ} (hbal : b * m = 2 ^ b) :
    andreevVarianceProxy b m = 5 / 4 * 2 ^ b := by
  unfold andreevVarianceProxy
  rw [← Nat.cast_mul, hbal, Nat.cast_pow, Nat.cast_ofNat]
  ring

private theorem balanced_radius_le {b m r : ℕ} (hbal : b * m = 2 ^ b)
    {δ L A C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) (hA : 20 * A ≤ C ^ 2)
    (hlog : Real.log (16 * andreevVarianceProxy b m / (2 ^ r * δ)) ≤ A * L) :
    (andreevTruncationRadius b m r δ : ℝ) ≤ C * Real.sqrt (2 ^ b * L) + 1 := by
  refine (andreevTruncationRadius_le b m r δ).trans (add_le_add_left ?_ 1)
  rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 4 by norm_num), ← Real.sqrt_mul (sq_nonneg _),
    ← Real.sqrt_sq hC, ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  rw [andreevVarianceProxy_of_balanced hbal] at hlog ⊢
  linarith only [mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 20 * (2 : ℝ) ^ b),
    mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ (2 : ℝ) ^ b * L)]

private theorem size_andreevTruncatedCircuit_real_le {b r : ℕ} (hr : r ≤ b) (m R : ℕ) :
    ((andreevTruncatedCircuit b m r R).size : ℝ) ≤ 4 * (2 : ℝ) ^ r * (R + 1) + 1 := by
  have hsub : ((2 ^ r - 1 : ℕ) : ℝ) ≤ 2 ^ r := by exact_mod_cast Nat.sub_le _ _
  rw [size_andreevTruncatedCircuit hr]
  push_cast
  gcongr

/-- **Thm. 7, Part 1, at balance**: if `k m = N` and `0 < δ ≤ 1 / 2`, the truncated circuit with
radius `andreevTruncationRadius b m b δ` has at most `64 n √(n log (1 / δ))` gates, so
`O(n ^ (3 / 2) √(log (1 / δ)))`. -/
theorem size_andreevTruncatedCircuit_le_of_balanced {b m : ℕ} (hbal : b * m = 2 ^ b) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ((andreevTruncatedCircuit b m b (andreevTruncationRadius b m b δ)).size : ℝ) ≤
      64 * (2 ^ b + b * m : ℕ) * Real.sqrt ((2 ^ b + b * m : ℕ) * Real.log (1 / δ)) := by
  set N : ℝ := 2 ^ b
  set L := Real.log (1 / δ)
  have hv : andreevVarianceProxy b m = 5 / 4 * N := andreevVarianceProxy_of_balanced hbal
  have hN : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hL : Real.log 2 ≤ L :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; linarith only [hδ2])
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hL2 : (1 : ℝ) / 2 ≤ L := hl2.trans hL
  -- `log (20 / δ) ≤ 6 L`, as `log 20 ≤ log 32 = 5 log 2`.
  have h20 : Real.log (16 * andreevVarianceProxy b m / (2 ^ b * δ)) ≤ 6 * L := by
    rw [hv, show 16 * (5 / 4 * N) / (2 ^ b * δ) = 20 * (1 / δ) by simp only [N]; field_simp; ring,
      Real.log_mul (by norm_num) (by positivity)]
    have hlog20 : Real.log 20 ≤ 5 * Real.log 2 := by
      simpa using Real.log_le_log (by norm_num) (show (20 : ℝ) ≤ 2 ^ 5 by norm_num)
    linarith only [hL, hl2, hlog20]
  set R := andreevTruncationRadius b m b δ
  have hNL : 1 / 2 ≤ N * L := by
    simpa only [one_mul] using mul_le_mul hN hL2 (by norm_num) (by linarith only [hN])
  have hR : (R : ℝ) ≤ 11 * Real.sqrt (N * L) + 1 :=
    balanced_radius_le hbal (by linarith only [hL2]) (by norm_num) (by norm_num) h20
  have hX : 1 / 2 ≤ Real.sqrt (N * L) := by
    rw [Real.le_sqrt (by norm_num) (by linarith only [hNL])]
    linarith only [hNL]
  calc ((andreevTruncatedCircuit b m b R).size : ℝ) ≤ 4 * N * (R + 1) + 1 :=
        size_andreevTruncatedCircuit_real_le le_rfl m R
    _ ≤ 64 * N * Real.sqrt (N * L) := by
        have hR' : (R : ℝ) + 1 ≤ 15 * Real.sqrt (N * L) := by linarith only [hR, hX]
        have h1 : 1 / 2 ≤ N * Real.sqrt (N * L) := by
          simpa only [one_mul] using mul_le_mul hN hX (by norm_num) (by linarith only [hN])
        linarith only [mul_le_mul_of_nonneg_left hR' (by linarith only [hN] : (0 : ℝ) ≤ 4 * N), h1]
    _ ≤ 64 * (2 ^ b + b * m : ℕ) * Real.sqrt ((2 ^ b + b * m : ℕ) * L) := by
        have hn : N ≤ ((2 ^ b + b * m : ℕ) : ℝ) := by
          simp only [N]; exact_mod_cast Nat.le_add_right _ _
        have hL0 : 0 ≤ L := by linarith only [hL2]
        gcongr

/-- Every real number is at most some power of two. -/
theorem exists_le_two_pow (x : ℝ) : ∃ r : ℕ, x ≤ 2 ^ r :=
  (pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)).imp fun _ h => h.le

/-- The least `r` with `32 ε² N ≤ 2 ^ r`: the number of characters kept in Part 2. -/
noncomputable def andreevVoteLevel (b : ℕ) (ε : ℝ) : ℕ :=
  Nat.find (exists_le_two_pow (32 * ε ^ 2 * 2 ^ b))

theorem le_two_pow_andreevVoteLevel (b : ℕ) (ε : ℝ) :
    32 * ε ^ 2 * 2 ^ b ≤ 2 ^ andreevVoteLevel b ε :=
  Nat.find_spec (exists_le_two_pow _)

theorem andreevVoteLevel_le {b k : ℕ} {ε : ℝ} (h : 32 * ε ^ 2 * 2 ^ b ≤ 2 ^ k) :
    andreevVoteLevel b ε ≤ k :=
  Nat.find_min' (exists_le_two_pow _) h

/-- For `1 / √N ≤ ε ≤ 1 / 8`, the vote level satisfies `r < k` and `2 ^ r ≤ 64 ε² N`. -/
theorem andreevVoteLevel_spec {b : ℕ} {ε : ℝ} (hε : 1 / Real.sqrt (2 ^ b) ≤ ε)
    (hε8 : ε ≤ 1 / 8) :
    andreevVoteLevel b ε < b ∧ (2 : ℝ) ^ andreevVoteLevel b ε ≤ 64 * ε ^ 2 * 2 ^ b := by
  have hN : (0 : ℝ) < 2 ^ b := by positivity
  have hε0 : 0 < ε := lt_of_lt_of_le (by positivity) hε
  have hεN : 1 ≤ ε ^ 2 * 2 ^ b := by
    have h := pow_le_pow_left₀ (by positivity) hε 2
    rwa [div_pow, Real.sq_sqrt hN.le, one_pow, div_le_iff₀ hN] at h
  have hε2 : ε ^ 2 ≤ 1 / 64 := (pow_le_pow_left₀ hε0.le hε8 2).trans_eq (by norm_num)
  set r := andreevVoteLevel b ε
  -- `b ≥ 1`, as `N ≥ 64`.
  have hb : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr fun hb0 => by
    rw [hb0, pow_zero, mul_one] at hεN
    linarith only [hεN, hε2]
  constructor
  · -- `32 ε² N ≤ N / 2 = 2 ^ (b - 1)`.
    have hle : r ≤ b - 1 := andreevVoteLevel_le (by
      rw [show (2 : ℝ) ^ b = 2 * 2 ^ (b - 1) by
        rw [← pow_succ', Nat.sub_add_cancel hb]]
      linarith only [mul_le_mul_of_nonneg_right hε2 (by positivity : (0 : ℝ) ≤ 2 ^ (b - 1))])
    omega
  · rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · simp only [hr0, pow_zero]; linarith only [hεN]
    · have hlt : ¬ 32 * ε ^ 2 * 2 ^ b ≤ (2 : ℝ) ^ (r - 1) := fun h =>
        absurd (andreevVoteLevel_le h) (by omega)
      rw [show (2 : ℝ) ^ r = 2 * 2 ^ (r - 1) by rw [← pow_succ', Nat.sub_add_cancel hr0]]
      linarith only [lt_of_not_ge hlt]

/-- **Thm. 7, Part 2, at balance**: if `k m = N` and `1 / √N ≤ ε ≤ 1 / 8`, the truncated circuit
with `r = andreevVoteLevel b ε` and radius `andreevTruncationRadius b m r ε` agrees with
`andreev b m` on at least a `1 / 2 + ε` fraction of the inputs, has at most
`2600 ε² n √(n log (1 / ε))` gates and at most `5300 ε² n² √(n log (1 / ε))` active wires, so
`O(ε² n ^ (3 / 2) √(log (1 / ε)))` gates and `O(ε² n ^ (5 / 2) √(log (1 / ε)))` wires. -/
theorem andreevTruncatedCircuit_part_two_of_balanced {b m : ℕ} (hbal : b * m = 2 ^ b) {ε : ℝ}
    (hε : 1 / Real.sqrt (2 ^ b) ≤ ε) (hε8 : ε ≤ 1 / 8) :
    let r := andreevVoteLevel b ε
    let C := andreevTruncatedCircuit b m r (andreevTruncationRadius b m r ε)
    let n : ℝ := (2 ^ b + b * m : ℕ)
    (1 / 2 + ε) * 2 ^ (2 ^ b + b * m) ≤
        (#{w : BitString (2 ^ b + b * m) | C.eval interpretation w 0 = andreev b m w} : ℝ) ∧
      (C.size : ℝ) ≤ 2600 * ε ^ 2 * n * Real.sqrt (n * Real.log (1 / ε)) ∧
      (C.wireCount : ℝ) ≤ 5300 * ε ^ 2 * n ^ 2 * Real.sqrt (n * Real.log (1 / ε)) := by
  intro r C n
  obtain ⟨hrb, hq⟩ := andreevVoteLevel_spec hε hε8
  set N : ℝ := 2 ^ b
  have hv : andreevVarianceProxy b m = 5 / 4 * N := andreevVarianceProxy_of_balanced hbal
  have hN : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hε0 : 0 < ε := lt_of_lt_of_le (by positivity) hε
  have hεN : 1 ≤ ε ^ 2 * N := by
    have h := pow_le_pow_left₀ (by positivity) hε 2
    rwa [div_pow, Real.sq_sqrt (by positivity), one_pow, div_le_iff₀ (by positivity)] at h
  have hq32 : 32 * ε ^ 2 * N ≤ 2 ^ r := le_two_pow_andreevVoteLevel b ε
  set L := Real.log (1 / ε)
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hL : 3 * Real.log 2 ≤ L := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log (by norm_num)
      (show (2 : ℝ) ^ 3 ≤ 1 / ε by rw [le_div_iff₀ hε0]; linarith only [hε8])
  have hL1 : 1 ≤ L := by linarith only [hL, hl2]
  refine ⟨half_add_mul_le_card_eval_andreevTruncatedCircuit_eq_andreev hrb m hε0 hq32, ?_⟩
  -- The radius: `16 v / (q ε) ≤ 5 / (8 ε³) ≤ ε⁻³`, so `R ≤ 8 √(N L) + 1`.
  set R := andreevTruncationRadius b m r ε
  have hlog : Real.log (16 * andreevVarianceProxy b m / (2 ^ r * ε)) ≤ 3 * L := by
    rw [hv]
    have hle : 16 * (5 / 4 * N) / (2 ^ r * ε) ≤ (1 / ε) ^ 3 := by
      rw [div_le_iff₀ (by positivity),
        show (1 / ε) ^ 3 * (2 ^ r * ε) = 2 ^ r / ε ^ 2 by field_simp,
        le_div_iff₀ (by positivity)]
      linarith only [hq32, hεN]
    calc Real.log (16 * (5 / 4 * N) / (2 ^ r * ε)) ≤ Real.log ((1 / ε) ^ 3) := by gcongr
      _ = 3 * L := by rw [Real.log_pow]; push_cast; ring
  have hNL1 : 1 ≤ N * L := one_le_mul_of_one_le_of_one_le hN hL1
  have hR : (R : ℝ) ≤ 8 * Real.sqrt (N * L) + 1 :=
    balanced_radius_le hbal (by linarith only [hL1]) (by norm_num) (by norm_num) hlog
  have hX : 1 ≤ Real.sqrt (N * L) := Real.one_le_sqrt.2 hNL1
  have hn : N ≤ n := by simp only [N, n]; exact_mod_cast Nat.le_add_right _ _
  have hL0 : 0 ≤ L := by linarith only [hL1]
  -- Gates: `G + 1 ≤ 4 q (R + 1) + 1 ≤ 2600 ε² N √(N L)`.
  have hsize : (C.size : ℝ) ≤ 2600 * ε ^ 2 * N * Real.sqrt (N * L) := by
    refine (size_andreevTruncatedCircuit_real_le hrb.le m R).trans ?_
    have hG : 4 * (2 : ℝ) ^ r * (R + 1) ≤ 4 * (64 * ε ^ 2 * N) * (R + 1) := by gcongr
    have hR' : (R : ℝ) + 1 ≤ 10 * Real.sqrt (N * L) := by linarith only [hR, hX]
    have h1 : 1 ≤ ε ^ 2 * N * Real.sqrt (N * L) := one_le_mul_of_one_le_of_one_le hεN hX
    linarith only [hG, h1,
      mul_le_mul_of_nonneg_left hR' (by positivity : (0 : ℝ) ≤ 256 * ε ^ 2 * N)]
  have hsize' : (C.size : ℝ) ≤ 2600 * ε ^ 2 * n * Real.sqrt (n * L) := hsize.trans (by gcongr)
  refine ⟨hsize', ?_⟩
  -- Wires: `(G + 1) n + G + 1 + n ≤ (G + 1) (n + 1) + n`.
  have hw' : (C.wireCount : ℝ) ≤ (C.size : ℝ) * n + C.size + n := by
    dsimp only [n]
    exact_mod_cast (wireCount_andreevTruncatedCircuit_le hrb.le m R).trans_eq
      (by rw [size_andreevTruncatedCircuit hrb.le m R]; omega)
  have hn1 : 1 ≤ n := hN.trans hn
  have hεn : 1 ≤ ε ^ 2 * n := hεN.trans (by gcongr)
  have hX' : 1 ≤ Real.sqrt (n * L) := hX.trans (by gcongr)
  have hterm1 : (C.size : ℝ) * n + C.size ≤ 5200 * (ε ^ 2 * n ^ 2 * Real.sqrt (n * L)) := by
    calc (C.size : ℝ) * n + C.size = (C.size : ℝ) * (n + 1) := by ring
      _ ≤ (C.size : ℝ) * (2 * n) :=
          mul_le_mul_of_nonneg_left (by linarith only [hn1]) (Nat.cast_nonneg _)
      _ ≤ 2600 * ε ^ 2 * n * Real.sqrt (n * L) * (2 * n) := by gcongr
      _ = 5200 * (ε ^ 2 * n ^ 2 * Real.sqrt (n * L)) := by ring
  have hterm2 : n ≤ ε ^ 2 * n ^ 2 * Real.sqrt (n * L) := by
    calc n = 1 * n * 1 := by ring
      _ ≤ (ε ^ 2 * n) * n * Real.sqrt (n * L) := by gcongr
      _ = ε ^ 2 * n ^ 2 * Real.sqrt (n * L) := by ring
  linarith only [hw', hterm1, hterm2]

end Cslib.Circuits.Boolean.WeightedThreshold
