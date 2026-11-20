/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Order
import CslibFrontier.Foundations.LinearAlgebra.Matrix.UnitaryGroup

/-!
# Combining local alignments on bipartite vectors

A noisy left filter with a Gram matrix dominating the two ordinary left filters
controls their action on the same residual vector. This lets a left alignment at a
fixed right filter extend to a second right filter, using a right unitary that aligns
the noisy branches. The Gram-matrix proof applies also to singular filters.

## Main results

* `Cslib.Quantum.norm_sub_joint_alignment_le`: compare two branches using independent
  local unitaries, an auxiliary right alignment and two Gram matrix bounds.

## References

* [Bavarian, Vidick and Yuen, Claim 5.19, equations (77)–(81)][BavarianVidickYuen2022]
  (arXiv:1509.07466v2, §5.4, printed pp. 31–33).
-/

public section

namespace Cslib.Quantum

open Matrix
open scoped Kronecker MatrixOrder ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "act" => toEuclideanCLM (𝕜 := ℂ)

private theorem act_tensor_comp (A C : Matrix ι ι ℂ) (B D : Matrix κ κ ℂ)
    (ψ : EuclideanSpace ℂ (ι × κ)) :
    act (A ⊗ₖ B) (act (C ⊗ₖ D) ψ) = act ((A * C) ⊗ₖ (B * D)) ψ := by
  rw [← mul_apply_eq_comp, ← map_mul, ← mul_kronecker_mul]

private theorem norm_left_tensor_le_of_gram_le {A M : Matrix ι ι ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : (c • (Mᴴ * M) - Aᴴ * A).PosSemidef) (ψ : EuclideanSpace ℂ (ι × κ)) :
    ‖act (A ⊗ₖ (1 : Matrix κ κ ℂ)) ψ‖ ≤
      Real.sqrt c * ‖act (M ⊗ₖ (1 : Matrix κ κ ℂ)) ψ‖ := by
  have hone : (1 : Matrix κ κ ℂ).PosSemidef := by
    simpa only [conjTranspose_one, one_mul] using
      posSemidef_conjTranspose_mul_self (1 : Matrix κ κ ℂ)
  have hpos := h.kronecker hone
  have he : (c • (Mᴴ * M) - Aᴴ * A) ⊗ₖ (1 : Matrix κ κ ℂ) =
      c • ((Mᴴ * M) ⊗ₖ (1 : Matrix κ κ ℂ)) - (Aᴴ * A) ⊗ₖ (1 : Matrix κ κ ℂ) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [sub_mul, mul_assoc]
  rw [he] at hpos
  apply Matrix.norm_toLp_mulVec_le_of_gram_le hc _ ψ
  simpa only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, one_mul] using hpos

private theorem norm_tensor_unitary_sub {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hA : A ∈ unitaryGroup ι ℂ) (hB : B ∈ unitaryGroup κ ℂ)
    (v w : EuclideanSpace ℂ (ι × κ)) :
    ‖act (A ⊗ₖ B) v - act (A ⊗ₖ B) w‖ = ‖v - w‖ := by
  rw [← map_sub]
  exact (mem_unitaryGroup_iff_forall_norm_toEuclideanCLM _).mp
    (kronecker_mem_unitary hA hB) _

/-- Two local unitaries align the joint branch. The first two errors compare the ordinary
branches with one filter fixed, and the third compares the noisy branches on Bob's system.
The two Gram bounds control how much the noisy error can grow on the ordinary branches. -/
theorem norm_sub_joint_alignment_le (A₀ A₁ M U : Matrix ι ι ℂ)
    (B₀ B₁ V W : Matrix κ κ ℂ) (ψ : EuclideanSpace ℂ (ι × κ))
    (hU : U ∈ unitaryGroup ι ℂ)
    (hW : W ∈ unitaryGroup κ ℂ) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (h₀ : (c₀ • (Mᴴ * M) - A₀ᴴ * A₀).PosSemidef)
    (h₁ : (c₁ • (Mᴴ * M) - A₁ᴴ * A₁).PosSemidef) :
    ‖act (U ⊗ₖ V) (act (A₀ ⊗ₖ B₀) ψ) - act (A₁ ⊗ₖ B₁) ψ‖ ≤
      ‖act ((1 : Matrix ι ι ℂ) ⊗ₖ V) (act (A₀ ⊗ₖ B₀) ψ) - act (A₀ ⊗ₖ B₁) ψ‖ +
      ‖act (U ⊗ₖ (1 : Matrix κ κ ℂ)) (act (A₀ ⊗ₖ B₀) ψ) - act (A₁ ⊗ₖ B₀) ψ‖ +
      (Real.sqrt c₀ + Real.sqrt c₁) *
        ‖act ((1 : Matrix ι ι ℂ) ⊗ₖ W) (act (M ⊗ₖ B₁) ψ) - act (M ⊗ₖ B₀) ψ‖ := by
  let z := act ((1 : Matrix ι ι ℂ) ⊗ₖ W) (act ((1 : Matrix ι ι ℂ) ⊗ₖ B₁) ψ) -
    act ((1 : Matrix ι ι ℂ) ⊗ₖ B₀) ψ
  have hz (A : Matrix ι ι ℂ) :
      act (A ⊗ₖ (1 : Matrix κ κ ℂ)) z =
        act ((1 : Matrix ι ι ℂ) ⊗ₖ W) (act (A ⊗ₖ B₁) ψ) - act (A ⊗ₖ B₀) ψ := by
    simp only [z, map_sub, act_tensor_comp, one_mul, mul_one]
  have ht (a b c : EuclideanSpace ℂ (ι × κ)) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    simpa only [dist_eq_norm] using dist_triangle a b c
  let φ (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) := act (A ⊗ₖ B) ψ
  let left := act (U ⊗ₖ (1 : Matrix κ κ ℂ))
  let right := act ((1 : Matrix ι ι ℂ) ⊗ₖ W)
  have hcomm (v : EuclideanSpace ℂ (ι × κ)) : right (left v) = left (right v) := by
    simp only [left, right, act_tensor_comp, one_mul, mul_one]
  have hA : ‖left (φ A₀ B₁) - φ A₁ B₁‖ ≤
      ‖left (φ A₀ B₀) - φ A₁ B₀‖ +
        (Real.sqrt c₀ + Real.sqrt c₁) * ‖right (φ M B₁) - φ M B₀‖ := by
    rw [← norm_tensor_unitary_sub (one_mem (unitaryGroup ι ℂ)) hW, show
      act ((1 : Matrix ι ι ℂ) ⊗ₖ W) = right from rfl, hcomm]
    have htri₀ := ht (left (right (φ A₀ B₁))) (left (φ A₀ B₀)) (right (φ A₁ B₁))
    have htri₁ := ht (left (φ A₀ B₀)) (φ A₁ B₀) (right (φ A₁ B₁))
    change ‖act (U ⊗ₖ (1 : Matrix κ κ ℂ)) _ -
      act (U ⊗ₖ (1 : Matrix κ κ ℂ)) _‖ + _ ≥ _ at htri₀
    rw [norm_tensor_unitary_sub hU (one_mem _)] at htri₀
    have ha := norm_left_tensor_le_of_gram_le hc₀ h₀ z
    have hb := norm_left_tensor_le_of_gram_le hc₁ h₁ z
    rw [hz, hz] at ha hb
    rw [norm_sub_rev (φ A₁ B₀)] at htri₁
    dsimp only [φ, right] at htri₀ htri₁ ⊢
    rw [add_mul]
    linarith only [htri₀, htri₁, ha, hb]
  let bob := act ((1 : Matrix ι ι ℂ) ⊗ₖ V)
  have hsplit (v : EuclideanSpace ℂ (ι × κ)) : act (U ⊗ₖ V) v = left (bob v) := by
    simp only [left, bob, act_tensor_comp, mul_one, one_mul]
  rw [hsplit]
  refine (ht (left (bob (φ A₀ B₀))) (left (φ A₀ B₁)) (φ A₁ B₁)).trans ?_
  have hleft := norm_tensor_unitary_sub hU (one_mem (unitaryGroup κ ℂ))
    (bob (φ A₀ B₀)) (φ A₀ B₁)
  change ‖left (bob (φ A₀ B₀)) - left (φ A₀ B₁)‖ = _ at hleft
  rw [hleft, add_assoc]
  exact add_le_add le_rfl hA

end Cslib.Quantum
