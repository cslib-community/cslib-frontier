/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Algebra.Covering.Duality
import CslibFrontier.Foundations.Algebra.Covering.Gauge

/-!
# Spectral points below upper functionals, and duality for tensors

The tensor forms of Proposition A.5 (prop:gauge) and Theorem A.6 (thm:duality) of *VP ≠ VNP over
every field* [AnthropicVPVNP2026]. Both are proved in the monoid of classes of tensors with its
covering relation (`Cslib.PartyTensor.tensorCovering`), with the results of
`Cslib.Covering.IsUpperFunctional.exists_map_mul` and
`Cslib.Covering.exists_coveredBy_pow_of_certificate`.

* Below every upper functional `P` there is a spectral point that respects every triple
  `(x, y, c)` which `P` respects (`Cslib.PartyTensor.UpperFunctional.exists_spectralPoint_le`).
* If every spectral point satisfies `F C ≤ max_β F (A β)`, then for every `ε > 0` and all large
  `N`, the power `C ^ N` is covered by at most `2 ^ (ε N)` products of `N` factors from the `A β`
  (`Cslib.PartyTensor.exists_coveredBy_pow_of_forall_le`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Paper.Gauges` (the tensor part).

## Main results

* `Cslib.PartyTensor.UpperFunctional.exists_spectralPoint_le`.
* `Cslib.PartyTensor.exists_coveredBy_pow_of_forall_le`.
-/

public section

namespace Cslib.PartyTensor

open Finset Covering

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- **Paper: Proposition A.5 (prop:gauge).** Every upper functional `P` dominates a spectral point
that respects every triple which `P` respects. `P` respects `(x, y, c)` if
`P (t * x) ≤ c * P (t * y)` for all `t`. -/
theorem UpperFunctional.exists_spectralPoint_le (P : UpperFunctional K I) :
    ∃ F : SpectralPoint K I, (∀ t, F t ≤ P t) ∧
      ∀ (x y : PartyTensor K I) (c : ℝ), 0 ≤ c → (∀ t, P (t * x) ≤ c * P (t * y)) →
        ∀ t, F (t * x) ≤ c * F (t * y) := by
  obtain ⟨F, hF, hmul, hle, hk⟩ := P.isUpperFunctional_lift.exists_map_mul
  refine ⟨{
      toFun t := F (toAntisymmetrization (· ≤ ·) t)
      nonneg _ := hF.nonneg _
      map_one := hF.map_one
      le_sum _ _ hb := hF.le_sum _ _ (tensorCovering_coveredBy.2 hb)
      map_mul _ _ := by rw [toAntisymmetrization_mul, hmul] },
    fun _ => hle _, fun x y c hc h t => ?_⟩
  have h1 := hk _ _ c hc (UpperFunctional.respects_lift h) (toAntisymmetrization (· ≤ ·) t)
  rwa [← toAntisymmetrization_mul, ← toAntisymmetrization_mul] at h1

/-- Copies of a tensor `s` with `1 ≤ s` cover every tensor, in the monoid of classes. -/
private theorem exists_coveredBy_copies [Nonempty I] (t : PartyTensor K I) {s : PartyTensor K I}
    (hs : 1 ≤ s) : ∃ r : ℕ, (tensorCovering K I).CoveredBy (toAntisymmetrization (· ≤ ·) t)
      (fun _ : Fin r => toAntisymmetrization (· ≤ ·) s) :=
  ⟨_, tensorCovering_coveredBy.2 ((coveredBy_one_of_le_unit (le_unit_card t)).mono fun _ => hs)⟩

/-- **Paper: Theorem A.6 (thm:duality).** Let `C ≠ 0` and `A β` be tensors on `I`, not all zero,
such that every spectral point satisfies `F C ≤ max_β F (A β)`. Then for every `ε > 0` and all
large `N`, the power `C ^ N` is covered by at most `2 ^ (ε N)` products of `N` factors from the
`A β`. The family is indexed by any finite type `B`. -/
theorem exists_coveredBy_pow_of_forall_le [Nonempty I] {B : Type} [Fintype B] [DecidableEq B]
    {C : PartyTensor K I} {A : B → PartyTensor K I} (hC : ∃ x, C.entry x ≠ 0)
    (hA : ∃ β x, (A β).entry x ≠ 0) (h : ∀ F : SpectralPoint K I, ∃ β, F C ≤ F (A β)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ (m : ℕ) (v : Fin m → B → ℕ), (m : ℝ) ≤ 2 ^ (ε * N) ∧
      (∀ i, ∑ β, v i β = N) ∧ (C ^ N).CoveredBy fun i => prod fun β => A β ^ v i β := by
  -- η = 2^(-ε/2)
  have hη : (0 : ℝ) < 2 ^ (-(ε / 2)) := by positivity
  have hη1 : (2 : ℝ) ^ (-(ε / 2)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hinv : ((2 : ℝ) ^ (-(ε / 2)))⁻¹ = 2 ^ (ε / 2) :=
      by rw [← Real.rpow_neg (by norm_num), neg_neg]
  have hsq : ∀ N : ℕ, ((2 : ℝ) ^ (ε / 2)) ^ N * ((2 : ℝ) ^ (ε / 2)) ^ N = 2 ^ (ε * N) := by
    intro N
    rw [← mul_pow, ← Real.rpow_add (by norm_num), add_halves, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  have hone (t : Antisymmetrization (PartyTensor K I) (· ≤ ·)) :
      ∃ r : ℕ, (tensorCovering K I).CoveredBy t (fun _ : Fin r => 1) :=
    toAntisymmetrization_ofAntisymmetrization (· ≤ ·) t ▸
      exists_coveredBy_copies (ofAntisymmetrization (· ≤ ·) t) le_rfl
  obtain ⟨β₀, hβ₀⟩ := hA
  by_cases hcert : ∃ k W,
      Nonempty (Certificate (tensorCovering K I) (toAntisymmetrization (· ≤ ·) C)
      (fun β => toAntisymmetrization (· ≤ ·) (A β)) (2 ^ (-(ε / 2))) 1 k W) ∧ W < 1
  · -- `1` has a certificate of weight below `1`
    obtain ⟨k, W, ⟨c⟩, hW⟩ := hcert
    obtain ⟨y, hy⟩ := hβ₀
    obtain ⟨n, hcA⟩ := exists_coveredBy_copies C (one_le_of_entry_ne_zero hy)
    have hbase : (1 : ℝ) < 2 ^ (ε / 2) := Real.one_lt_rpow one_lt_two (by linarith)
    obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt (((n : ℝ) + 1) ^ (k + 1)) hbase
    refine ⟨N₀, fun N hN => ?_⟩
    obtain ⟨κ, _, v, hcard, hv, hc⟩ := exists_coveredBy_pow_of_certificate hη hη1 hcA c hW N
    let e := Fintype.equivFin κ
    refine ⟨Fintype.card κ, fun i => v (e.symm i), ?_, fun i => hv _, ?_⟩
    · rw [hinv] at hcard
      refine hcard.trans (le_trans ?_ (hsq N).le)
      gcongr
      exact hN₀.le.trans (pow_le_pow_right₀ hbase.le hN)
    simp only [← toAntisymmetrization_pow, ← toAntisymmetrization_prod] at hc
    exact (tensorCovering_coveredBy.1 hc).reindex e.symm
  · -- otherwise the infimum of the weights of certificates is an upper functional, and
    -- Proposition A.5 (prop:gauge) contradicts the hypothesis
    exfalso
    push Not at hcert
    obtain ⟨hp, hA⟩ := isUpperFunctional_sInf_certificate (D := tensorCovering K I)
      (C := toAntisymmetrization (· ≤ ·) C) (A := fun β => toAntisymmetrization (· ≤ ·) (A β)) hη
      hone fun k W ⟨c⟩ => hcert k W ⟨c⟩
    obtain ⟨F, -, hk⟩ := (UpperFunctional.ofIsUpperFunctional hp).exists_spectralPoint_le
    obtain ⟨β, hβ⟩ := h F
    have h2 := hk (A β) C _ hη.le (fun t => by
      have h5 := hA β (toAntisymmetrization (· ≤ ·) t)
      rw [← toAntisymmetrization_mul, ← toAntisymmetrization_mul] at h5
      simpa only [UpperFunctional.ofIsUpperFunctional_apply] using h5) 1
    rw [F.congr (antisymmRel_one_mul _), F.congr (antisymmRel_one_mul _)] at h2
    obtain ⟨x, hx⟩ := hC
    exact not_lt_of_ge (hβ.trans h2)
      ((mul_lt_mul_of_pos_right hη1 (by linarith [F.one_le hx])).trans_eq (one_mul _))

end Cslib.PartyTensor
