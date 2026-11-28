/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.CompressedKeyOnly
public import CslibFrontier.Crypto.Computational.SIS.Hermite
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool

/-!
# Distinct responses to the same ML-DSA challenge

Section 6.2.2 of [CRYSTALS-Dilithium v3.1][BaiEtAl2021Dilithium] treats the case where two
different responses to one challenge recover the same commitment. Subtracting the two
verification equations cancels the public-key term and produces a short nonzero vector in
the kernel of `[I | A]`. The two blocks have the joint bound of equation (8).
-/

public section

namespace Cslib.Crypto.MLDSA

open Cslib.Probability

variable {P : Params}

/-- The high bits recovered by the compressed verifier from a decoded signature. -/
@[expose] def CompressedSignature.recover (σ : CompressedSignature P) (d : ℕ) (pk : PublicKey P) :
    Fin P.k → Fin P.n → ℤ :=
  fun i => useHintVec P.q P.γ₂ (σ.h i) (compressedVerifierCommitment P d pk σ.z σ.c i)

private def residual (d : ℕ) (pk : PublicKey P) (σ : CompressedSignature P) :
    Fin P.k → Fin P.n → ZMod P.q :=
  fun i j => hintResidual P.q P.γ₂ (σ.h i j) (compressedVerifierCommitment P d pk σ.z σ.c i j)

private def difference {a n q : ℕ} (x y : Fin a → Fin n → ZMod q) : Fin a → Fin n → ℤ :=
  fun i j => (x i j).valMinAbs - (y i j).valMinAbs

/-- Equation (8)'s integer witness, with the difference of the two hint residuals in the
identity block and the difference of the two responses in the matrix block. -/
def responseDifference (d : ℕ) (pk : PublicKey P) (σ σ' : CompressedSignature P) :
    Fin (P.k + P.ℓ) → Fin P.n → ℤ :=
  Fin.append (difference (residual d pk σ) (residual d pk σ')) (difference σ.z σ'.z)

/-- The same-challenge case of Dilithium v3.1 §6.2.2. Distinct decoded responses recovering
the same commitment yield an integer MSIS solution at the source radius. -/
theorem isSolution_responseDifference (hP : P.Valid) (hγq : 4 * P.γ₂ < P.q)
    (d : ℕ) (pk : PublicKey P) {σ σ' : CompressedSignature P} (hne : σ ≠ σ')
    (hc : σ.c = σ'.c) (hw : σ.recover d pk = σ'.recover d pk)
    (hz : ResponseShort P σ.z) (hz' : ResponseShort P σ'.z) :
    ModuleSIS.IsSolution (ModuleSIS.hermiteMatrix pk.A)
      (max (2 * (P.γ₁ - P.β)) (4 * P.γ₂ + 2)) (responseDifference d pk σ σ') := by
  let : NeZero P.q := ⟨by have := hP.one_lt_q; lia⟩
  let u := residual d pk σ
  let v := residual d pk σ'
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hzz : σ.z = σ'.z := funext fun i => funext fun j => ZMod.injective_valMinAbs <| by
      simpa [responseDifference, difference, sub_eq_zero] using
        congrFun (congrFun he (Fin.natAdd P.k i)) j
    refine hne (CompressedSignature.ext hzz (funext fun i => funext fun j => ?_) hc)
    apply useHint_injective hP.γ₂_pos hP.two_mul_γ₂_dvd hγq
      (compressedVerifierCommitment P d pk σ'.z σ'.c i j)
    simpa only [CompressedSignature.recover, useHintVec, hzz, hc] using
      congrFun (congrFun hw i) j
  · refine Fin.addCases (fun i j => ?_) (fun i j => ?_)
    · simp only [responseDifference, Fin.append_left, difference, residual]
      apply le_trans (abs_sub _ _)
      have h := abs_hintResidual_valMinAbs_le hP.γ₂_pos hP.two_mul_γ₂_dvd hγq
      have h₁ := h (σ.h i j) (compressedVerifierCommitment P d pk σ.z σ.c i j)
      have h₂ := h (σ'.h i j) (compressedVerifierCommitment P d pk σ'.z σ'.c i j)
      have hmax := Nat.le_max_right (2 * (P.γ₁ - P.β)) (4 * P.γ₂ + 2)
      lia
    · simp only [responseDifference, Fin.append_right, difference]
      apply le_trans (abs_sub _ _)
      have h₁ := hz i j
      have h₂ := hz' i j
      have hmax := Nat.le_max_left (2 * (P.γ₁ - P.β)) (4 * P.γ₂ + 2)
      lia
  · have hcast : (fun i j => ((responseDifference d pk σ σ' i j : ℤ) : ZMod P.q)) =
        Fin.append (u - v) (σ.z - σ'.z) := by
      funext i
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
        funext j <;> simp [responseDifference, difference, u, v]
    have hlinear : moduleSISMap pk.A (σ.z - σ'.z) =
        moduleSISMap pk.A σ.z - moduleSISMap pk.A σ'.z :=
      eq_sub_iff_add_eq.mpr (by rw [← moduleSISMap_add, sub_add_cancel])
    rw [hcast, ModuleSIS.moduleSISMap_hermiteMatrix, hlinear]
    funext i j
    have h := congrArg (fun w : Fin P.k → Fin P.n → ℤ =>
      ((w i j * (2 * P.γ₂ : ℕ) : ℤ) : ZMod P.q)) hw
    simp only [CompressedSignature.recover, useHintVec, useHint_mul_eq_add_hintResidual] at h
    simp only [u, v, residual, Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    simp only [compressedVerifierCommitment, hc, Pi.sub_apply] at h ⊢
    linear_combination h

/-- A collision finder sees the public matrix and can choose the public vector along with
both decoded signatures. -/
structure ResponsePair (P : Params) where
  /-- Full vector from which the verifier computes the rounded public term. -/
  t : Fin P.k → Fin P.n → ZMod P.q
  /-- First decoded signature. -/
  first : CompressedSignature P
  /-- Second decoded signature. -/
  second : CompressedSignature P

variable (find : Matrix (Fin P.k) (Fin P.ℓ) (Fin P.n → ZMod P.q) → ProbComp (ResponsePair P))

/-- Draw a uniform matrix. The finder wins by returning distinct short responses to a common
challenge that recover the same commitment under its chosen public vector. -/
noncomputable def responseCollisionGame [NeZero P.q] (d : ℕ) : Game := by
  classical
  exact (PMF.uniformOfFintype _).bind fun A => (find A).eval.map fun p =>
    let pk : PublicKey P := ⟨A, p.t⟩
    decide (p.first ≠ p.second ∧ p.first.c = p.second.c ∧
      p.first.recover d pk = p.second.recover d pk ∧ ResponseShort P p.first.z ∧
      ResponseShort P p.second.z)

/-- Run the finder once on the challenge matrix and return its response difference. -/
def responseCollisionSolver (d : ℕ)
    (A : Matrix (Fin P.k) (Fin P.ℓ) (Fin P.n → ZMod P.q)) :
    ProbComp (Fin (P.k + P.ℓ) → Fin P.n → ℤ) :=
  (fun (p : ResponsePair P) => responseDifference d ⟨A, p.t⟩ p.first p.second) <$> find A

/-- Concrete MSIS bound for the same-challenge, same-commitment case of §6.2.2. -/
theorem succProbability_responseCollisionGame_le_hermite [NeZero P.q] (hP : P.Valid)
    (hγq : 4 * P.γ₂ < P.q) (d : ℕ) :
    (responseCollisionGame find d).succProbability ≤
      Game.succProbability (ModuleSIS.hermiteExperiment (max (2 * (P.γ₁ - P.β)) (4 * P.γ₂ + 2))
        (responseCollisionSolver find d)).eval := by
  classical
  apply Game.succProbability_mono
  simp only [responseCollisionGame, ModuleSIS.hermiteExperiment, ProbComp.eval_bind,
    ProbComp.eval_uniform, responseCollisionSolver, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.bind_map]
  apply Probability.PMF.bind_apply_mono_on_support
  intro A _
  apply Probability.PMF.map_true_mono
  intro p _ hw
  simp only [decide_eq_true_eq] at hw ⊢
  obtain ⟨hne, hc, he, hz, hz'⟩ := hw
  exact isSolution_responseDifference hP hγq d ⟨A, p.t⟩ hne hc he hz hz'

end Cslib.Crypto.MLDSA
