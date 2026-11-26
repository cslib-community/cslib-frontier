/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Basis.PairAtlas
public import CslibFrontier.Computability.Circuit.Frontier.Basis.U2
public import CslibFrontier.Computability.Circuit.Frontier.Correlation
public import CslibFrontier.Computability.Circuit.Frontier.Correlation.Rectangle
public import CslibFrontier.Computability.Communication.Rank
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.RealRankLindsey
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Real-rank communication bounds and unconditional `2.8006 n` `U₂` correlation

Applies the real-rank Lindsey lemma (`Foundations.LinearAlgebra.Matrix.RealRankLindsey`) to
`Cslib.Communication.signMatrix` and `Cslib.Communication.communicationMatrix` across coordinate
cuts `X ⊆ ι` (`cutFun T X`) and derives unconditional `2.8006 n` quadratic-form correlation bounds
for `U₂` circuits:

* **Real-rank correlation bound** (`sq_correlation_quadForm_mul_le_rank_signMatrix`,
  `sq_correlation_quadForm_mul_le_rank_communicationMatrix_add_one`). Specializing
  `Matrix.sq_sum_matrix_bilinear_mul_two_pow_rank_le` to `Communication.signMatrix ℝ (cutFun T X)`
  gives `correlation S T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X ≤ (signMatrix ℝ (cutFun T X)).rank` and, via
  `Communication.rank_signMatrix_le`, `≤ (communicationMatrix ℝ (cutFun T X)).rank + 1`.
* **`AND → XOR` separation** (`rank_signMatrix_andXorSet`, `rank_communicationMatrix_andXorSet`,
  `nonnegRank_communicationMatrix_andXorSet`). Across `{0, 1} | {2, 3}`, the `4`-bit `AND → XOR`
  relation has `(signMatrix).rank = 2 < (communicationMatrix).rank = 3 < nonnegRank = 4`.
* **Unconditional `2.8006 n` `U₂` quadratic-form correlation bounds**
  (`eventually_abs_correlation_quadForm_le_u2_gaussian`,
  `eventually_abs_correlation_hardForm_le_u2`,
  `exists_eventually_abs_correlation_hardForm_le_of_lt_u2`,
  `exists_eventually_abs_correlation_hardForm_le_u2_28006`). Bounds correlation with any
  high-cut-rank quadratic form — and in particular with `hardForm n` (whose submatrix-robust block
  is **chosen nonconstructively by `Classical.choose`**) — by `2^{-Ω(n)}` for every `U₂` circuit up
  to `2.8006 n` inner gates (`c* ≥ 28007 / 10000 > 28006 / 10000`).

The real-rank quadratic-form correlation bound (`sq_correlation_quadForm_mul_le_rank_signMatrix`)
and the unconditional `2.8006 n` `U₂` correlation bounds are original to this library.

## Main definitions

* `Cslib.Circuits.Frontier.cutFun`: Boolean communication function of `T ⊆ (ι → Bool)` across a
  coordinate cut `X : Set ι`.
* `Cslib.Circuits.Frontier.andXorSet`, `Cslib.Circuits.Frontier.andXorCut`: `4`-bit `AND → XOR`
  witness separating `signMatrix` rank (`2`), `communicationMatrix` rank (`3`), and `nonnegRank`
  (`4`).

## Main results

* `Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_rank_signMatrix`,
  `Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_rank_communicationMatrix_add_one`:
  quadratic-form correlation bounded by real rank across any cut `X`.
* `Cslib.Circuits.Frontier.rank_signMatrix_andXorSet`,
  `Cslib.Circuits.Frontier.rank_communicationMatrix_andXorSet`,
  `Cslib.Circuits.Frontier.nonnegRank_communicationMatrix_andXorSet`: `2 < 3 < 4` rank separation.
* `Cslib.Circuits.Frontier.eventually_abs_correlation_quadForm_le_u2_gaussian`,
  `Cslib.Circuits.Frontier.eventually_abs_correlation_hardForm_le_u2`,
  `Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le_of_lt_u2`,
  `Cslib.Circuits.Frontier.exists_eventually_abs_correlation_hardForm_le_u2_28006`: unconditional
  `U₂` quadratic-form correlation bounds up to `2.8006 n` inner gates.

## References

* [S. Jukna, *Extremal Combinatorics*, Ch. 14][Jukna2011]
* [S. Fiorini, S. Massar, S. Pokutta, H. R. Tiwary, and R. de Wolf, *Exponential Lower Bounds for
  Polytopes in Combinatorial Optimization*, Section 3.1][FioriniMassarPokuttaTiwaryDeWolf2015]
-/

public section

namespace Cslib.Circuits.Frontier

open Set Matrix
open scoped Finset

section CutMatrices

variable {ι : Type*}

/-- Boolean communication function of `T ⊆ (ι → Bool)` across the coordinate cut `X : Set ι`,
gluing `p : X → Bool` and `q : ↥Xᶜ → Bool` via `Equiv.piEquivPiSubtypeProd`. -/
noncomputable def cutFun (T : Set (ι → Bool)) (X : Set ι) (p : X → Bool) (q : ↥Xᶜ → Bool) :
    Bool :=
  letI := Classical.propDecidable
  decide ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm (p, q) ∈ T)

variable [Fintype ι] [DecidableEq ι]

/-- Equivalence between `Bool` and `ZMod 2` via `BitString.bitVal`. -/
private def boolEquivZMod2 : Bool ≃ ZMod 2 where
  toFun := BitString.bitVal (ZMod 2)
  invFun z := z == 1
  left_inv b := by cases b <;> decide
  right_inv z := by revert z; decide

open Classical in
/-- **Correlation through real sign-matrix rank.** For any quadratic form `Q` over `𝔽₂`, target set
`T ⊆ (ι → Bool)`, and coordinate cut `X ⊆ ι`,
`correlation {x | BitString.quadForm Q x} T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X ≤
  (Communication.signMatrix ℝ (cutFun T X)).rank`. -/
theorem sq_correlation_quadForm_mul_le_rank_signMatrix
    (Q : Matrix ι ι (ZMod 2)) (T : Set (ι → Bool)) (X : Set ι) :
    correlation {x | BitString.quadForm Q x} T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X ≤
      (Communication.signMatrix ℝ (cutFun T X)).rank := by
  set S := {x : ι → Bool | BitString.quadForm Q x}
  set N : ℝ := (Fintype.card (ι → Bool) : ℝ)
  have hNn : N = 2 ^ Fintype.card ι := by simp [N, Fintype.card_bool]
  have hn : Fintype.card X + Fintype.card ↥Xᶜ = Fintype.card ι := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact ncard_add_ncard_compl X
  let e := Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool
  let eX : (X → Bool) ≃ (X → ZMod 2) := Equiv.piCongrRight fun _ => boolEquivZMod2
  let eY : (↥Xᶜ → Bool) ≃ (↥Xᶜ → ZMod 2) := Equiv.piCongrRight fun _ => boolEquivZMod2
  let C := (Q + Qᵀ).submatrix ((↑) : X → ι) ((↑) : ↥Xᶜ → ι)
  let g : (X → ZMod 2) → ℝ := fun u =>
    (-1) ^ (u ⬝ᵥ Q.submatrix ((↑) : X → ι) ((↑) : X → ι) *ᵥ u).val
  let h : (↥Xᶜ → ZMod 2) → ℝ := fun w =>
    (-1) ^ (w ⬝ᵥ Q.submatrix ((↑) : ↥Xᶜ → ι) ((↑) : ↥Xᶜ → ι) *ᵥ w).val
  set Mz : Matrix (X → ZMod 2) (↥Xᶜ → ZMod 2) ℝ :=
    (Communication.signMatrix ℝ (cutFun T X)).submatrix eX.symm eY.symm
  have hsum : correlation S T * N =
      ∑ u : X → ZMod 2, ∑ w : ↥Xᶜ → ZMod 2, Mz u w * g u * h w * (-1 : ℝ) ^ (u ⬝ᵥ C *ᵥ w).val := by
    rw [correlation_mul_card_eq_sum, ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (e.trans (Equiv.prodCongr eX eY)) _ _ fun x => ?_
    simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
    have hq := dotProduct_mulVec_self_eq_add Q X fun i => BitString.bitVal (ZMod 2) (x i)
    have hS : (if x ∈ S then (1 : ℝ) else -1) =
        -(-1 : ℝ) ^ ((fun i => BitString.bitVal (ZMod 2) (x i)) ⬝ᵥ
          Q *ᵥ fun i => BitString.bitVal (ZMod 2) (x i)).val := by
      rw [BitString.neg_one_pow_val_eq]
      simp only [S, mem_ofPred_eq]
      split_ifs <;> simp
    have hT : Mz (eX (e x).1) (eY (e x).2) = if x ∈ T then -1 else 1 := by
      simp only [Mz, submatrix_apply, Equiv.symm_apply_apply, Communication.signMatrix_apply,
        cutFun]
      have hex : e.symm (e x) = x := e.symm_apply_apply x
      change (if decide (e.symm ((e x).1, (e x).2) ∈ T) = true then (-1 : ℝ) else 1) = _
      rw [Prod.mk.eta, hex]
      by_cases hxT : x ∈ T <;> simp [hxT]
    have hw : (if (x ∈ S ↔ x ∈ T) then (1 : ℝ) else -1) =
        -(if x ∈ T then -1 else 1) * (if x ∈ S then 1 else -1) := by
      by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;> simp [hxS, hxT]
    rw [hw, ← hT, hS, hq, ZMod.neg_one_pow_val_add, ZMod.neg_one_pow_val_add]
    have hg_eq : X.domRestrict (fun i => BitString.bitVal (ZMod 2) (x i)) = eX (e x).1 := rfl
    have hh_eq : Xᶜ.domRestrict (fun i => BitString.bitVal (ZMod 2) (x i)) = eY (e x).2 := rfl
    rw [hg_eq, hh_eq]
    dsimp only [g, h, C]
    ring
  have hL := Matrix.sq_sum_matrix_bilinear_mul_two_pow_rank_le C Mz g h
    (fun _ => by simp [g]) (fun _ => by simp [h])
  have hCR : (2 : ℝ) ^ C.rank = 2 ^ (Q + Qᵀ).cutRank X := by
    rw [((Q + Qᵀ).cutRank_eq_rank X).symm]
  have hMrankR : (Mz.rank : ℝ) = (Communication.signMatrix ℝ (cutFun T X)).rank :=
    congrArg Nat.cast (Matrix.rank_submatrix _ eX.symm eY.symm)
  set Fsq : ℝ := ∑ u, ∑ w, Mz u w ^ 2
  have hMsq : Fsq = N := by
    have h1 : ∀ u w, Mz u w ^ 2 = 1 := by
      intro u w
      simp only [Mz, submatrix_apply, Communication.signMatrix_apply]
      split_ifs <;> norm_num
    dsimp only [Fsq]
    simp_rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [Fintype.card_pi, Fintype.card_pi]
    simp only [Fintype.card_congr boolEquivZMod2.symm, Fintype.card_bool, Finset.prod_const,
      Finset.card_univ]
    push_cast
    rw [← pow_add, hn, hNn]
  have hprod : (2 : ℝ) ^ Fintype.card X * 2 ^ Fintype.card ↥Xᶜ = N := by
    rw [hNn, ← pow_add, hn]
  have hNN : 0 < N * N := by rw [hNn]; positivity
  have hbound : correlation S T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X * (N * N) ≤
      (Communication.signMatrix ℝ (cutFun T X)).rank * (N * N) := by
    calc correlation S T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X * (N * N)
        = (correlation S T * N) ^ 2 * 2 ^ (Q + Qᵀ).cutRank X := by ring
      _ ≤ (Mz.rank : ℝ) * Fsq * 2 ^ Fintype.card X * 2 ^ Fintype.card ↥Xᶜ := by
          rw [hsum, ← hCR]
          exact hL
      _ = (Communication.signMatrix ℝ (cutFun T X)).rank * (N * N) := by
          rw [hMrankR, hMsq, mul_assoc ((Communication.signMatrix ℝ (cutFun T X)).rank * N), hprod]
          ring
  exact le_of_mul_le_mul_right hbound hNN

open Classical in
/-- **Correlation through `{0, 1}` real communication-matrix rank.** Across any coordinate cut
`X ⊆ ι`, `correlation {x | BitString.quadForm Q x} T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X ≤
  (Communication.communicationMatrix ℝ (cutFun T X)).rank + 1`. -/
theorem sq_correlation_quadForm_mul_le_rank_communicationMatrix_add_one
    (Q : Matrix ι ι (ZMod 2)) (T : Set (ι → Bool)) (X : Set ι) :
    correlation {x | BitString.quadForm Q x} T ^ 2 * 2 ^ (Q + Qᵀ).cutRank X ≤
      (Communication.communicationMatrix ℝ (cutFun T X)).rank + 1 :=
  (sq_correlation_quadForm_mul_le_rank_signMatrix Q T X).trans
    (by exact_mod_cast Communication.rank_signMatrix_le (cutFun T X))

end CutMatrices

/-! ### Explicit `2 < 3 < 4` separation on the `AND → XOR` relation -/

/-- The `4`-bit `AND → XOR` input set `{x : Fin 4 → Bool | (x 2 && x 0) == (x 3 ^^ x 1)}`, matching
`Basis.andXorMatrix` across the cut `andXorCut = {0, 1}` (`(x 0, x 1) = (b, d)` on `X` and
`(x 2, x 3) = (a, c)` on `Xᶜ`). -/
@[expose]
def andXorSet : Set (Fin 4 → Bool) :=
  {x | Basis.andXorMatrix (x 0, x 1) (x 2, x 3) = true}

/-- The left half `{0, 1} ⊆ Fin 4` of the `AND → XOR` cut. -/
@[expose]
def andXorCut : Set (Fin 4) :=
  {i | i.val < 2}

private def andXorLeftEquiv : (andXorCut → Bool) ≃ Bool × Bool where
  toFun p := (p ⟨0, by simp [andXorCut]⟩, p ⟨1, by simp [andXorCut]⟩)
  invFun bd i := if i.1.val = 0 then bd.1 else bd.2
  left_inv p := by
    ext ⟨i, hi⟩
    fin_cases i
    · rfl
    · rfl
    · simp [andXorCut] at hi
    · simp [andXorCut] at hi
  right_inv := fun ⟨_, _⟩ => rfl

private def andXorRightEquiv : (↥andXorCutᶜ → Bool) ≃ Bool × Bool where
  toFun q := (q ⟨2, by simp [andXorCut]⟩, q ⟨3, by simp [andXorCut]⟩)
  invFun ac i := if i.1.val = 2 then ac.1 else ac.2
  left_inv q := by
    ext ⟨i, hi⟩
    fin_cases i
    · simp [andXorCut] at hi
    · simp [andXorCut] at hi
    · rfl
    · rfl
  right_inv := fun ⟨_, _⟩ => rfl

private theorem cutFun_andXorSet (p : andXorCut → Bool) (q : ↥andXorCutᶜ → Bool) :
    cutFun andXorSet andXorCut p q =
      Basis.andXorMatrix (andXorLeftEquiv p) (andXorRightEquiv q) := by
  classical
  rw [Bool.eq_iff_iff]
  dsimp only [cutFun]
  rw [decide_eq_true_eq]
  simp only [andXorSet, mem_ofPred_eq]
  let e := Equiv.piEquivPiSubtypeProd (· ∈ andXorCut) fun _ => Bool
  have h0 : e.symm (p, q) 0 = p ⟨0, by simp [andXorCut]⟩ :=
    dite_eq_left (by simp [andXorCut])
  have h1 : e.symm (p, q) 1 = p ⟨1, by simp [andXorCut]⟩ :=
    dite_eq_left (by simp [andXorCut])
  have h2 : e.symm (p, q) 2 = q ⟨2, by simp [andXorCut]⟩ :=
    dite_eq_right (by simp [andXorCut])
  have h3 : e.symm (p, q) 3 = q ⟨3, by simp [andXorCut]⟩ :=
    dite_eq_right (by simp [andXorCut])
  change Basis.andXorMatrix (e.symm (p, q) 0, e.symm (p, q) 1)
    (e.symm (p, q) 2, e.symm (p, q) 3) = true ↔ _
  rw [h0, h1, h2, h3]
  rfl

open Classical in
/-- Across `andXorCut`, the `{-1, 1}` sign matrix of `andXorSet` has real rank `2`. -/
theorem rank_signMatrix_andXorSet :
    (Communication.signMatrix ℝ (cutFun andXorSet andXorCut)).rank = 2 := by
  have heq : Communication.signMatrix ℝ (cutFun andXorSet andXorCut) =
      (Communication.signMatrix ℝ Basis.andXorMatrix).submatrix andXorLeftEquiv
        andXorRightEquiv := by
    ext p q
    simp [Communication.signMatrix, cutFun_andXorSet]
  rw [heq, Matrix.rank_submatrix, Basis.rank_signMatrix_andXorMatrix_real]

open Classical in
/-- Across `andXorCut`, the `{0, 1}` communication matrix of `andXorSet` has real rank `3`. -/
theorem rank_communicationMatrix_andXorSet :
    (Communication.communicationMatrix ℝ (cutFun andXorSet andXorCut)).rank = 3 := by
  have heq : Communication.communicationMatrix ℝ (cutFun andXorSet andXorCut) =
      (Communication.communicationMatrix ℝ Basis.andXorMatrix).submatrix andXorLeftEquiv
        andXorRightEquiv := by
    ext p q
    simp [Communication.communicationMatrix, cutFun_andXorSet]
  rw [heq, Matrix.rank_submatrix, Basis.rank_andXorMatrix_real]

/-- Across `andXorCut`, the `{0, 1}` communication matrix of `andXorSet` has nonnegative rank `4`
(strictly exceeding both `(signMatrix ℝ (cutFun andXorSet andXorCut)).rank = 2` and
`(communicationMatrix ℝ (cutFun andXorSet andXorCut)).rank = 3`). -/
theorem nonnegRank_communicationMatrix_andXorSet :
    (Communication.communicationMatrix ℝ (cutFun andXorSet andXorCut)).nonnegRank = 4 := by
  have heq : Communication.communicationMatrix ℝ (cutFun andXorSet andXorCut) =
      (Communication.communicationMatrix ℝ Basis.andXorMatrix).submatrix andXorLeftEquiv
        andXorRightEquiv := by
    ext p q
    simp [Communication.communicationMatrix, cutFun_andXorSet]
  have hinv : Communication.communicationMatrix ℝ Basis.andXorMatrix =
      (Communication.communicationMatrix ℝ (cutFun andXorSet andXorCut)).submatrix
        andXorLeftEquiv.symm andXorRightEquiv.symm := by
    rw [heq, submatrix_submatrix, Equiv.self_comp_symm, Equiv.self_comp_symm, submatrix_id_id]
  rw [← Basis.nonnegRank_andXorMatrix_real]
  refine le_antisymm ?_ ?_
  · rw [heq]; exact Matrix.nonnegRank_submatrix_le _ _ _
  · rw [hinv]; exact Matrix.nonnegRank_submatrix_le _ _ _

/-! ### Unconditional `2.8006 n` `U₂` quadratic-form correlation bounds -/

section U2Correlation

open Filter Asymptotics

universe v

/-- **Unconditional `U₂` quadratic-form correlation bound.** With `p = gaussianCoefficient` and
`B_pair = 271212 / 1000000`, set `δ := 2 p - B_pair`, `A := (7/8) B_pair + (1/8)(2p)`,
`L_{U₂} := 1 + (1 - δ) / A`, and `c*_{U₂} := 1 + (1/2 - δ) / A` (`≥ 2.8007`). For every
`c ≥ 1 / 2`, every `γ < (c*_{U₂} - c) / (2 L_{U₂})`, and every family `Q_n` whose polar matrix has
bisection cut rank `⌊n/2⌋ - o(n)`, eventually every `U₂` circuit with at most `c n` inner gates has
correlation at most `2^{-γ n}` with `BitString.quadForm (Q n)`. -/
theorem eventually_abs_correlation_quadForm_le_u2_gaussian {c γ : ℝ} (hc : 1 / 2 ≤ c)
    (hγ : γ <
      (1 + (1 / 2 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
          ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient)) - c) /
        (2 * (1 + (1 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
          ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient)))))
    (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2)) (e : ℕ → ℝ)
    (he : e =o[atTop] fun n => (n : ℝ))
    (hQ : ∀ᶠ n in atTop, ∀ U : Set (Fin n), U.ncard = n / 2 →
      ((n / 2 : ℕ) : ℝ) ≤ (Q n + (Q n)ᵀ).cutRank U + e n) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), I.IsU2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | BitString.quadForm (Q n) x} {x | C.eval I x 0 ∈ Acc}| ≤
          (2 : ℝ) ^ (-γ * n) :=
  eventually_abs_correlation_quadForm_le_u2 Gaussian.gaussianCoefficient_pos (by norm_num)
    Gaussian.le_two_mul_gaussianCoefficient Gaussian.u2CubicPairBound_gaussian
    (by linarith [Gaussian.two_mul_gaussianCoefficient_le])
    (by linarith [Gaussian.two_mul_gaussianCoefficient_le]) hc hγ Q e he hQ

/-- **Exponentially small `U₂` correlation with `hardForm n`** (whose submatrix-robust block is
chosen nonconstructively by `Classical.choose`). -/
theorem eventually_abs_correlation_hardForm_le_u2 {c γ : ℝ} (hc : 1 / 2 ≤ c)
    (hγ : γ <
      (1 + (1 / 2 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
          ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient)) - c) /
        (2 * (1 + (1 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
          ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient))))) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (C : Circuit σ n 1), I.IsU2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  eventually_abs_correlation_quadForm_le_u2_gaussian hc hγ hardMatrix _ isLittleO_hardDeficiency
    (Eventually.of_forall half_le_cutRank_hardMatrix_add)

/-- **Every gate-count coefficient strictly below `c*_{U₂}` (`≥ 2.8007`).** Note that `hardForm` is
chosen nonconstructively via `Classical.choose`. -/
theorem exists_eventually_abs_correlation_hardForm_le_of_lt_u2 {c : ℝ}
    (hc : c <
      1 + (1 / 2 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
        ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient))) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool)
      (Acc : Set Bool) (C : Circuit σ n 1), I.IsU2 → (C.innerSize : ℝ) ≤ c * n →
        |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  set c' := max c (1 / 2)
  set c_star := 1 + (1 / 2 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
    ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient))
  set L_u2 := 1 + (1 - (2 * Gaussian.gaussianCoefficient - 271212 / 1000000)) /
    ((7 / 8) * (271212 / 1000000) + (1 / 8) * (2 * Gaussian.gaussianCoefficient))
  have hL : 0 < L_u2 := by
    have := Gaussian.u2CircuitCoefficient_ge_46362
    dsimp only [L_u2]; linarith
  have hc' : c' < c_star := max_lt hc (by
    have := Gaussian.u2CorrelationThreshold_ge_28007
    dsimp only [c_star]; linarith)
  set r := (c_star - c') / (2 * L_u2)
  have hr : 0 < r := div_pos (by linarith) (by positivity)
  refine ⟨r / 2, by positivity, ?_⟩
  filter_upwards [eventually_abs_correlation_hardForm_le_u2.{v} (le_max_right c (1 / 2))
    (γ := r / 2) (half_lt_self hr)] with n hn σ I Acc C hU2 hsize
  exact hn σ I Acc C hU2
    (hsize.trans (mul_le_mul_of_nonneg_right (le_max_left c _) (Nat.cast_nonneg n)))

/-- **Unconditional `2.8006 n` `U₂` quadratic-form correlation bound (`28006 / 10000`).** Some fixed
`γ > 0` bounds, for all large `n`, the correlation of every `U₂` circuit with at most `2.8006 n`
inner gates with `hardForm n` (chosen nonconstructively by `Classical.choose`) by `2^{-γ n}`. -/
theorem exists_eventually_abs_correlation_hardForm_le_u2_28006 :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool)
      (Acc : Set Bool) (C : Circuit σ n 1), I.IsU2 →
        (C.innerSize : ℝ) ≤ 28006 / 10000 * n →
          |correlation {x | hardForm n x} {x | C.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) :=
  exists_eventually_abs_correlation_hardForm_le_of_lt_u2
    (by linarith [Gaussian.u2CorrelationThreshold_ge_28007])

/-- **Unconditional `2.8006 n` De Morgan correlation bound** with `hardForm n` (nonconstructive via
`Classical.choose`). -/
theorem exists_eventually_abs_correlation_hardForm_le_deMorgan_28006 :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (Acc : Set Bool)
      (C : Circuit Boolean.DeMorgan.signature n 1),
        (C.innerSize : ℝ) ≤ 28006 / 10000 * n →
          |correlation {x | hardForm n x}
            {x | C.eval Boolean.DeMorgan.interpretation x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := exists_eventually_abs_correlation_hardForm_le_u2_28006.{0}
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn Acc C hsize
  exact hn Boolean.DeMorgan.signature Boolean.DeMorgan.interpretation Acc C
    Boolean.DeMorgan.isU2 hsize

/-- **Unconditional `2.8006 n` Boolean correlation bound** with `hardForm n` (nonconstructive via
`Classical.choose`). -/
theorem exists_eventually_abs_correlation_hardForm_le_boolean_28006 :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (Acc : Set Bool)
      (C : Circuit Boolean.signature n 1),
        (C.innerSize : ℝ) ≤ 28006 / 10000 * n →
          |correlation {x | hardForm n x}
            {x | C.eval Boolean.interpretation x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, hev⟩ := exists_eventually_abs_correlation_hardForm_le_u2_28006.{0}
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hev] with n hn Acc C hsize
  exact hn Boolean.signature Boolean.interpretation Acc C Boolean.isU2 hsize

end U2Correlation

end Cslib.Circuits.Frontier
