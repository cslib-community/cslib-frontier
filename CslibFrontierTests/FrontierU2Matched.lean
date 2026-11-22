/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Frontier.Basis.PairAtlas
import CslibFrontier.Computability.Circuit.Frontier.Basis.U2
import CslibFrontier.Computability.Circuit.Frontier.Correlation.RealRank
import CslibFrontier.Computability.Circuit.Frontier.FanInTwo
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian.CostLambda

/-!
# Checked tests for `U₂` pair-compressed layouts, `cost_λ`, and real-rank correlation

Exercises across the `module` boundary:
1. `PairAtlas`: `decide` evaluation of `pairMatrix`/`pairCount`, unambiguous `2`- and `3`-rectangle
   covers across `COPY`, `XOR`, and `U₂`, and the `2 < 3 < 4` rank separation on `AND → XOR`.
2. `Basis.U2`: `SimpleGraph.exists_isMatching_mul_eight_ge` on `K₄` (`⊤ : SimpleGraph (Fin 4)`),
   `Boolean.DeMorgan.isU2`, and `Boolean.isU2`.
3. `Layouts.Gaussian.CostLambda`: strict numerical improvement `4.57597 < 4.6362`,
   `u2CubicPairBound_gaussian`, and unconditional `4.6362 n` worst-case, nondeterministic, and
   average-case `U₂` / De Morgan / Boolean lower bounds.
4. `Correlation.RealRank`: `rank_signMatrix < rank_communicationMatrix < nonnegRank` on `andXorSet`,
   `sq_correlation_quadForm_mul_le_rank_signMatrix`, and unconditional `2.8006 n` `U₂` correlation
   bounds (`2.78798 < 2.8006`).
-/

set_option linter.privateModule false

open Cslib Cslib.Circuits Cslib.Circuits.Frontier Matrix Real Filter Asymptotics

namespace CslibFrontierTests.FrontierU2Matched

/-! ### 1. `PairAtlas` across the `module` boundary -/

example : Basis.pairCount Basis.copyRel Basis.copyRel (true, true) (true, true) = 1 ∧
    Basis.pairMatrix Basis.copyRel Basis.copyRel (true, true) (true, true) = true ∧
    Basis.andXorMatrix (true, false) (true, true) = true := by
  decide

example : Basis.HasUnambiguousRectangles (Basis.pairMatrix Basis.copyRel Basis.copyRel) 2 :=
  Basis.hasUnambiguousRectangles_copy_copy

example (n₁ n₂ : Bool) :
    Basis.HasUnambiguousRectangles (Basis.pairMatrix (Basis.xorRel n₁) (Basis.xorRel n₂)) 2 :=
  Basis.hasUnambiguousRectangles_xor_xor n₁ n₂

example : Basis.HasUnambiguousRectangles
    (Basis.pairMatrix (Basis.andTypeRel false false false 2)
      (Basis.andTypeRel true false true 0)) 3 :=
  Basis.hasUnambiguousRectangles_u2 (.gate false false false) (.gate true false true 0)

example : (Communication.signMatrix ℝ Basis.andXorMatrix).rank = 2 ∧
    (Communication.communicationMatrix ℝ Basis.andXorMatrix).rank = 3 ∧
    (Communication.communicationMatrix (ZMod 2) Basis.andXorMatrix).rank = 3 ∧
    (Communication.communicationMatrix ℝ Basis.andXorMatrix).nonnegRank = 4 :=
  ⟨Basis.rank_signMatrix_andXorMatrix_real,
    Basis.rank_andXorMatrix_real,
    Basis.rank_andXorMatrix_zmod2,
    Basis.nonnegRank_andXorMatrix_real⟩

/-! ### 2. `Basis.U2`: `7/8` matching on `K₄` and `IsU2` instances -/

example : ∃ M : (⊤ : SimpleGraph (Fin 4)).Subgraph, M.IsMatching ∧ M.verts.ncard = 4 := by
  have h3 : ∀ v : Fin 4, ((⊤ : SimpleGraph (Fin 4)).neighborSet v).ncard = 3 := by
    intro v
    have hset : (⊤ : SimpleGraph (Fin 4)).neighborSet v = ({v}ᶜ : Set (Fin 4)) := by
      ext w
      simp [SimpleGraph.neighborSet, ne_comm]
    rw [hset]
    have hc := Set.ncard_add_ncard_compl ({v} : Set (Fin 4))
    rw [Set.ncard_singleton, Nat.card_fin] at hc
    omega
  obtain ⟨M, hM, hcov⟩ := (⊤ : SimpleGraph (Fin 4)).exists_isMatching_mul_eight_ge h3
  rw [Nat.card_fin] at hcov
  have hle : M.verts.ncard ≤ 4 := (Set.ncard_le_card M.verts).trans_eq (Nat.card_fin 4)
  exact ⟨M, hM, by omega⟩

example : Boolean.DeMorgan.interpretation.IsU2 ∧ Boolean.interpretation.IsU2 :=
  ⟨Boolean.DeMorgan.isU2, Boolean.isU2⟩

/-! ### 3. `CostLambda`: numerical comparisons and `4.6362 n` `U₂` lower bounds -/

example : (457597 / 100000 : ℝ) < 46362 / 10000 ∧
    (46362 / 10000 : ℝ) < 46754 / 10000 ∧
    (46754 / 10000 : ℝ) < 46871 / 10000 ∧
    (278798 / 100000 : ℝ) < 28006 / 10000 := by
  norm_num

example : U2CubicPairBound Gaussian.gaussianCoefficient (271212 / 1000000) :=
  Gaussian.u2CubicPairBound_gaussian

example : (46362 / 10000 : ℝ) ≤
      1 + (1 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
        ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient)) ∧
    (28007 / 10000 : ℝ) ≤
      1 + (1 / 2 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
        ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient)) :=
  ⟨Gaussian.u2CircuitCoefficient_ge_46362,
    Gaussian.u2CorrelationThreshold_ge_28007⟩

example {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (Acc : Set Bool)
      (c : Circuit Boolean.DeMorgan.signature (n + k) 1),
        c.NondeterministicDecides Boolean.DeMorgan.interpretation Acc (S n) →
          (46362 / 10000 - 1 / 10000 : ℝ) * n < c.innerSize := by
  filter_upwards [eventually_46362_div_10000_sub_mul_lt_innerSize_u2_nondeterministic.{0} hSK
    (ε := 1 / 10000) (by norm_num)] with n hn k Acc c hdec
  exact hn k Boolean.DeMorgan.signature Boolean.DeMorgan.interpretation Acc c
    Boolean.DeMorgan.isU2 hdec

example {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K) :
    (∀ᶠ n in atTop, ∀ (Acc : Set Bool) (c : Circuit Boolean.DeMorgan.signature n 1),
      c.Decides Boolean.DeMorgan.interpretation Acc (S n) →
        (46362 / 10000 - 1 / 10000 : ℝ) * n < c.innerSize) ∧
    (∀ᶠ n in atTop, ∀ (Acc : Set Bool) (c : Circuit Boolean.signature n 1),
      c.Decides Boolean.interpretation Acc (S n) →
        (46362 / 10000 - 1 / 10000 : ℝ) * n < c.innerSize) :=
  ⟨eventually_46362_div_10000_sub_mul_lt_innerSize_deMorgan hSK (by norm_num),
    eventually_46362_div_10000_sub_mul_lt_innerSize_boolean hSK (by norm_num)⟩

example {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} {b : ℕ → ℝ}
    (hbias : ∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ)) :
    ∃ γ > 0, ∀ᶠ n in atTop, ∀ (Acc : Set Bool) (c : Circuit Boolean.DeMorgan.signature n 1),
      (c.innerSize : ℝ) ≤ (46362 / 10000 - 1 / 10000) * n →
        agreement (S n) {x | c.eval Boolean.DeMorgan.interpretation x 0 ∈ Acc} ≤
          1 / 2 + b n + Real.exp (-(γ * n)) :=
  eventually_agreement_le_deMorgan_46362 hbias hK (by norm_num)

/-! ### 4. `RealRank`: `2 < 3 < 4` separation and `2.8006 n` `U₂` correlation -/

open Classical in
example :
    (Communication.signMatrix ℝ (cutFun andXorSet andXorCut)).rank <
      (Communication.communicationMatrix ℝ (cutFun andXorSet andXorCut)).rank ∧
    ((Communication.communicationMatrix ℝ (cutFun andXorSet andXorCut)).rank : ℕ∞) <
      (Communication.communicationMatrix ℝ (cutFun andXorSet andXorCut)).nonnegRank := by
  rw [rank_signMatrix_andXorSet, rank_communicationMatrix_andXorSet,
    nonnegRank_communicationMatrix_andXorSet]
  norm_num

open Classical in
example (Q : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    correlation {x | Cslib.BitString.quadForm Q x} andXorSet ^ 2 *
      2 ^ (Q + Qᵀ).cutRank andXorCut ≤ 2 :=
  (sq_correlation_quadForm_mul_le_rank_signMatrix Q andXorSet andXorCut).trans_eq
    (by rw [rank_signMatrix_andXorSet]; norm_num)

example : ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
    ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), I.IsU2 → (C.innerSize : ℝ) ≤ 28006 / 10000 * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_hardForm_le_u2_28006

example : ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
    ∀ (Acc : Set Bool) (C : Circuit Boolean.DeMorgan.signature n 1),
      (C.innerSize : ℝ) ≤ 28006 / 10000 * n →
        |correlation {x | hardForm n x}
          {x | C.eval Boolean.DeMorgan.interpretation x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_hardForm_le_deMorgan_28006

end CslibFrontierTests.FrontierU2Matched
