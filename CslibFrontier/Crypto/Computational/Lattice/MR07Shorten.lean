/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.LatticeReduction.Potential
public import CslibFrontier.Algorithms.LinearAlgebra.BareissElimination
public import CslibFrontier.Crypto.Computational.Lattice.GIVP
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Nat.Log

/-!
# Finite lattice basis shortening step for `GIVP` from `IncGDD`

This module formalizes the finite geometric shortening step, exact executable rational orthogonal
target construction, Hadamard potential-drop iteration bound, and deterministic oracle-loop
soundness underlying [MicciancioRegev2007], Lemma 5.10 (December 27, 2005 author's copy, §5.3,
p. 24).

Given a full-rank family `S` of `n = rank L` linearly independent vectors in a lattice `L`, either
`S` already solves `GIVP^φ_{8γ}` (`‖S‖ ≤ 8γ φ(L)`), or `(L, S, ‖S‖ / 8)` is a valid instance of
`IncGDD^φ_{γ, 8}` (`isSolution_givp_or_isValidInstance_incGDD`). Selecting a longest vector `S i*`
(`‖S i*‖ = ‖S‖`) and a target `t` orthogonal to `{S j : j ≠ i*}` with
`(1/2) ‖S‖ ≤ ‖t‖ ≤ (9/16) ‖S‖`, any `IncGDD^φ_{γ, 8}` solution `u ∈ L` (`‖u - t‖ ≤ (1/4) ‖S‖`)
preserves linear independence, never increases `‖S‖`, and shrinks `sqNormProd S = ∏ j, ‖S j‖²` by
at least `(13/16)²` (`shortenStep_of_incGDD`).

When `L` has integral inner products (`∀ x ∈ L, ∀ y ∈ L, ∃ z : ℤ, ⟪x, y⟫ = z`, as discharged for
integer-span lattices by `Cslib.Algorithms.LatticeReduction.exists_int_inner_of_mem_span`),
Hadamard's inequality via `Cslib.Algorithms.LatticeReduction.one_le_gramPrefixDet` bounds
`sqNormProd S ≥ 1`, so any chain of shortening steps starting from `‖S₀ i‖² ≤ B` has length
strictly less than `shortenRoundBound n B = 2 * n * (Nat.log 2 B + 1)`
(`shortenSteps_lt_bound`). For rational families `S : Fin (m + 1) → Fin (m + 1) → ℚ`,
`ratOrthoTarget` computes a valid rational target without square roots using
`Cslib.LinearAlgebra.ratKernelBasis` and `Nat.sqrt` (`ratOrthoTarget_spec`).

Both a halting round-indexed oracle loop (`shortenLoop`, `shortenLoop_isSolution_givp`) and an
unconditional fixed-iteration guarded step (`shortenGuardedStep`, `shortenGuardedStep_invariants`,
`shortenGuardedStep_of_incGDD`, `shortenGuardedIter_isSolution_givp`) are provided for downstream
randomized PPT reductions. This module proves the finite deterministic/guarded shortening steps
only; probabilistic amplification, strict-PPT accounting, and the asymptotic `GIVP`/`SIVP` to
`SIS` reduction are separate work.

## Main definitions

* `Cslib.Crypto.MR07Shorten.sqNormProd`: product of squared norms `∏ j, ‖S j‖²`.
* `Cslib.Crypto.MR07Shorten.shortenRoundBound`: explicit round bound `2 * n * (Nat.log 2 B + 1)`.
* `Cslib.Crypto.MR07Shorten.sqNormRat`, `Cslib.Crypto.MR07Shorten.toEuclidean`,
  `Cslib.Crypto.MR07Shorten.maxSqNormIndex`, `Cslib.Crypto.MR07Shorten.ratOrthoScale`,
  `Cslib.Crypto.MR07Shorten.omitRowTable`, `Cslib.Crypto.MR07Shorten.ratOrthoTarget`: executable
  irrational-free rational orthogonal target construction.
* `Cslib.Crypto.MR07Shorten.ValidTargetOracle`, `Cslib.Crypto.MR07Shorten.shortenLoopFrom`,
  `Cslib.Crypto.MR07Shorten.shortenLoop`, `Cslib.Crypto.MR07Shorten.shortenGuardedStep`:
  round-indexed oracle loop and unconditional guarded shortening step.

## Main results

* `Cslib.Crypto.MR07Shorten.shortenStep_norm_le`, `Cslib.Crypto.MR07Shorten.shortenStep_pi_norm_le`,
  `Cslib.Crypto.MR07Shorten.shortenStep_sqNormProd_le`,
  `Cslib.Crypto.MR07Shorten.shortenStep_linearIndependent`,
  `Cslib.Crypto.MR07Shorten.shortenStep_of_incGDD`: one-round shortening invariants.
* `Cslib.Crypto.MR07Shorten.isSolution_givp_or_isValidInstance_incGDD`: dichotomy between solving
  `GIVP^φ_{8γ}` and forming a valid `IncGDD^φ_{γ, 8}` instance.
* `Cslib.Crypto.MR07Shorten.one_le_sqNormProd`, `Cslib.Crypto.MR07Shorten.shortenSteps_lt_bound`:
  Hadamard lower bound and finite iteration cap.
* `Cslib.Crypto.MR07Shorten.ratOrthoTarget_spec`: orthogonality and `(1/2, 9/16]` norm bounds for
  `ratOrthoTarget`.
* `Cslib.Crypto.MR07Shorten.shortenLoop_isSolution_givp`,
  `Cslib.Crypto.MR07Shorten.shortenGuardedStep_invariants`,
  `Cslib.Crypto.MR07Shorten.shortenGuardedStep_of_incGDD`,
  `Cslib.Crypto.MR07Shorten.shortenGuardedIter_isSolution_givp`: finite deterministic and
  fixed-iteration guarded shortening loop soundness.

## References

* [D. Micciancio and O. Regev, *Worst-Case to Average-Case Reductions Based on Gaussian
  Measures*][MicciancioRegev2007], Lemma 5.10 (December 27, 2005 author's copy, §5.3, p. 24).
-/

public section

open Cslib.Algorithms.LatticeReduction InnerProductSpace Module
open scoped RealInnerProductSpace

namespace Cslib.Crypto

namespace MR07Shorten

/-! ### 1. Abstract Euclidean One-Round Shortening Geometry -/

section NormedGeometry

variable {E : Type*} [NormedAddCommGroup E] {n : ℕ}

/-- Product of squared Euclidean norms of a family of vectors, used as the shortening potential. -/
@[expose] noncomputable def sqNormProd (S : Fin n → E) : ℝ :=
  ∏ j : Fin n, ‖S j‖ ^ 2

/-- The squared-norm product is nonnegative. -/
theorem sqNormProd_nonneg (S : Fin n → E) : 0 ≤ sqNormProd S :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

/-- If every vector has squared norm at most `B`, then `sqNormProd S ≤ B ^ n`. -/
theorem sqNormProd_le_pow {S : Fin n → E} {B : ℝ} (hB : ∀ i, ‖S i‖ ^ 2 ≤ B) :
    sqNormProd S ≤ B ^ n := by
  calc sqNormProd S ≤ ∏ _j : Fin n, B :=
        Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) fun j _ => hB j
    _ = B ^ n := by simp

private theorem pi_norm_update_le {S : Fin n → E} {i : Fin n} {u : E} (hu : ‖u‖ ≤ ‖S‖) :
    ‖Function.update S i u‖ ≤ ‖S‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg S)).2
    ((Function.forall_update_iff S fun _ v => ‖v‖ ≤ ‖S‖).2 ⟨hu, fun j _ => norm_le_pi_norm S j⟩)

/-- The replacement vector `u` has norm at most `(13 / 16) * ‖S‖`. -/
theorem shortenStep_norm_le {S : Fin n → E} {t u : E}
    (ht_hi : ‖t‖ ≤ (9 / 16 : ℝ) * ‖S‖)
    (hu_dist : ‖u - t‖ ≤ (1 / 4 : ℝ) * ‖S‖) :
    ‖u‖ ≤ (13 / 16 : ℝ) * ‖S‖ := by
  have htri : ‖u‖ ≤ ‖u - t‖ + ‖t‖ := by
    simpa only [sub_add_cancel] using norm_add_le (u - t) t
  linarith

/-- Monotone norm invariant: replacing `S i` by `u` never increases `‖S‖`. -/
theorem shortenStep_pi_norm_le {S : Fin n → E} {i : Fin n} {t u : E}
    (ht_hi : ‖t‖ ≤ (9 / 16 : ℝ) * ‖S‖)
    (hu_dist : ‖u - t‖ ≤ (1 / 4 : ℝ) * ‖S‖) :
    ‖Function.update S i u‖ ≤ ‖S‖ :=
  pi_norm_update_le (by linarith [shortenStep_norm_le ht_hi hu_dist, norm_nonneg S])

/-- Strict potential drop: replacing a longest vector `S i` (`‖S i‖ = ‖S‖`) multiplies
`sqNormProd S` by at most `(13 / 16) ^ 2`. -/
theorem shortenStep_sqNormProd_le {S : Fin n → E} {i : Fin n} {t u : E}
    (hi : ‖S i‖ = ‖S‖)
    (ht_hi : ‖t‖ ≤ (9 / 16 : ℝ) * ‖S‖)
    (hu_dist : ‖u - t‖ ≤ (1 / 4 : ℝ) * ‖S‖) :
    sqNormProd (Function.update S i u) ≤ (13 / 16 : ℝ) ^ 2 * sqNormProd S := by
  have hu : ‖u‖ ^ 2 ≤ (13 / 16 : ℝ) ^ 2 * ‖S i‖ ^ 2 := by
    rw [← mul_pow, hi]
    exact pow_le_pow_left₀ (norm_nonneg u) (shortenStep_norm_le ht_hi hu_dist) 2
  unfold sqNormProd
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self,
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)],
    ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hu (Finset.prod_nonneg fun _ _ => sq_nonneg _)

/-- Dichotomy: a full-rank family `S` in `L` either already solves `GIVP^φ_{8γ}` or forms a valid
`IncGDD^φ_{γ, 8}` instance at radius `r = ‖S‖ / 8`. -/
theorem isSolution_givp_or_isValidInstance_incGDD [NormedSpace ℝ E]
    (φ : Submodule ℤ E → ℝ) (γ : ℝ)
    (L : Submodule ℤ E) (S : Fin (finrank ℤ L) → E)
    (hS_li : LinearIndependent ℝ S) (hS_mem : ∀ j, S j ∈ L) :
    GIVP.IsSolution φ (8 * γ) L S ∨ IncGDD.IsValidInstance φ γ L S (‖S‖ / 8) := by
  by_cases h : γ * φ L < ‖S‖ / 8
  · exact Or.inr ⟨hS_li, hS_mem, h⟩
  · exact Or.inl ⟨hS_li, hS_mem, fun j => (norm_le_pi_norm S j).trans (by linarith)⟩

end NormedGeometry

section InnerProductGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

private theorem pi_norm_pos_of_linearIndependent {S : Fin n → E} (hS : LinearIndependent ℝ S)
    (i : Fin n) : 0 < ‖S‖ :=
  lt_of_lt_of_le (norm_pos_iff.mpr (hS.ne_zero i)) (norm_le_pi_norm S i)

/-- Replacing the longest vector `S i*` by any vector `u` within `(1 / 4) * ‖S‖` of a target `t`
orthogonal to `{S j : j ≠ i*}` of norm `‖t‖ ≥ (1 / 2) * ‖S‖` preserves linear independence. -/
theorem shortenStep_linearIndependent {S : Fin n → E} (hS : LinearIndependent ℝ S)
    {i : Fin n} {t u : E}
    (ht_orth : ∀ j, j ≠ i → ⟪t, S j⟫ = 0)
    (ht_lo : (1 / 2 : ℝ) * ‖S‖ ≤ ‖t‖)
    (hu_dist : ‖u - t‖ ≤ (1 / 4 : ℝ) * ‖S‖) :
    LinearIndependent ℝ (Function.update S i u) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hci : c i = 0 := by
    by_contra hne
    let w : E := ∑ j ∈ Finset.univ.erase i, (-(c j / c i)) • S j
    have hu_eq : u = w := by
      have hsplit : c i • u + ∑ j ∈ Finset.univ.erase i, c j • S j = 0 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self] at hc
        rwa [Finset.sum_congr rfl fun j hj => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]] at hc
      have hcu : c i • u = -(∑ j ∈ Finset.univ.erase i, c j • S j) :=
        eq_neg_of_add_eq_zero_left hsplit
      calc u = (c i)⁻¹ • (c i • u) := (inv_smul_smul₀ hne u).symm
        _ = (c i)⁻¹ • -(∑ j ∈ Finset.univ.erase i, c j • S j) := by rw [hcu]
        _ = ∑ j ∈ Finset.univ.erase i, (-(c j / c i)) • S j := by
          rw [smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul, ← neg_smul]
          congr 1
          ring
    have horth_w : ⟪t, w⟫ = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [inner_smul_right, ht_orth j (Finset.ne_of_mem_erase hj), mul_zero]
    have hnorm_sq : ‖w - t‖ ^ 2 = ‖w‖ ^ 2 + ‖t‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_comm, horth_w]
      ring
    have ht_le : ‖t‖ ≤ ‖u - t‖ := by
      rw [hu_eq]
      have h1 : ‖t‖ ^ 2 ≤ ‖w - t‖ ^ 2 := by linarith [sq_nonneg ‖w‖]
      nlinarith [norm_nonneg t, norm_nonneg (w - t)]
    have hSpos : 0 < ‖S‖ := pi_norm_pos_of_linearIndependent hS i
    linarith
  have hS_zero : ∑ j : Fin n, c j • S j = 0 := by
    rw [← hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hji : j = i
    · subst hji; simp [hci]
    · simp [Function.update_of_ne hji]
  exact Fintype.linearIndependent_iff.mp hS c hS_zero

/-- Bridge from `IncGDD.IsSolution 8 L S t (‖S‖ / 8) u` to the one-round shortening invariants. -/
theorem shortenStep_of_incGDD {L : Submodule ℤ E} {S : Fin (finrank ℤ L) → E}
    (hS_li : LinearIndependent ℝ S) (hS_mem : ∀ j, S j ∈ L)
    {i : Fin (finrank ℤ L)} (hi : ‖S i‖ = ‖S‖) {t u : E}
    (ht_orth : ∀ j, j ≠ i → ⟪t, S j⟫ = 0)
    (ht_lo : (1 / 2 : ℝ) * ‖S‖ ≤ ‖t‖)
    (ht_hi : ‖t‖ ≤ (9 / 16 : ℝ) * ‖S‖)
    (hu : IncGDD.IsSolution 8 L S t (‖S‖ / 8) u) :
    LinearIndependent ℝ (Function.update S i u) ∧
      (∀ j, Function.update S i u j ∈ L) ∧
      ‖Function.update S i u‖ ≤ ‖S‖ ∧
      sqNormProd (Function.update S i u) ≤ (13 / 16 : ℝ) ^ 2 * sqNormProd S := by
  have hu_dist : ‖u - t‖ ≤ (1 / 4 : ℝ) * ‖S‖ := by linarith [hu.dist_le]
  exact ⟨shortenStep_linearIndependent hS_li ht_orth ht_lo hu_dist,
    (Function.forall_update_iff S fun _ v => v ∈ L).2 ⟨hu.mem, fun j _ => hS_mem j⟩,
    shortenStep_pi_norm_le ht_hi hu_dist, shortenStep_sqNormProd_le hi ht_hi hu_dist⟩

/-! ### 2. Hadamard Potential Lower Bound & Finite Iteration Bound -/

/-- Hadamard lower bound for linearly independent families with integral Gram matrix,
proved via `Cslib.Algorithms.LatticeReduction.one_le_gramPrefixDet`. -/
theorem one_le_sqNormProd {S : Fin n → E} (hS : LinearIndependent ℝ S)
    (hGram : HasIntegralGram S) : 1 ≤ sqNormProd S := by
  have hdet : 1 ≤ gramPrefixDet S n := one_le_gramPrefixDet hS hGram le_rfl
  rw [gramPrefixDet, Finset.filter_true_of_mem fun j _ => j.isLt] at hdet
  exact hdet.trans <| Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) fun j _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_gramSchmidt_le ℝ S j) 2

end InnerProductGeometry

/-- Explicit polynomial iteration cap `2 * n * (Nat.log 2 B + 1)` on shortening rounds. -/
@[expose] def shortenRoundBound (n B : ℕ) : ℕ :=
  2 * n * (Nat.log 2 B + 1)

/-- In dimension zero, `shortenRoundBound 0 B = 0`. -/
theorem shortenRoundBound_zero_left (B : ℕ) : shortenRoundBound 0 B = 0 := by
  simp [shortenRoundBound]

private theorem pow_shortenRoundBound_mul_lt_one {n B : ℕ} (hn : 0 < n) :
    ((13 / 16 : ℝ) ^ 2) ^ (shortenRoundBound n B) * (B : ℝ) ^ n < 1 := by
  set L := Nat.log 2 B + 1
  have hBL : (B : ℝ) < (2 : ℝ) ^ L := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) B
  have hbase : ((13 / 16 : ℝ) ^ 2) ^ 2 < 1 / 2 := by norm_num
  have hstep1 : (((13 / 16 : ℝ) ^ 2) ^ 2) ^ L ≤ (1 / 2 : ℝ) ^ L := by gcongr
  have hone_term : (((13 / 16 : ℝ) ^ 2) ^ 2) ^ L * (B : ℝ) < 1 := by
    calc (((13 / 16 : ℝ) ^ 2) ^ 2) ^ L * (B : ℝ)
        ≤ (1 / 2 : ℝ) ^ L * (B : ℝ) := mul_le_mul_of_nonneg_right hstep1 (Nat.cast_nonneg B)
      _ < (1 / 2 : ℝ) ^ L * (2 : ℝ) ^ L := mul_lt_mul_of_pos_left hBL (by positivity)
      _ = 1 := by rw [← mul_pow]; norm_num
  have hrew : ((13 / 16 : ℝ) ^ 2) ^ (shortenRoundBound n B) * (B : ℝ) ^ n =
      ((((13 / 16 : ℝ) ^ 2) ^ 2) ^ L * (B : ℝ)) ^ n := by
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    congr 1
    dsimp only [shortenRoundBound, L]
    ring
  rw [hrew]
  exact pow_lt_one₀ (by positivity) hone_term hn.ne'

/-- Pure `ℕ`-exponent potential-drop bound: a chain of shortening steps starting from `S₀` with
`∀ i, ‖S₀ i‖ ^ 2 ≤ B` has length strictly less than `shortenRoundBound n B` whenever `0 < n`. -/
theorem shortenSteps_lt_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n B k : ℕ} (hn : 0 < n) {seq : ℕ → Fin n → E}
    (hB : ∀ i, ‖seq 0 i‖ ^ 2 ≤ (B : ℝ))
    (hstep : ∀ j < k, sqNormProd (seq (j + 1)) ≤ (13 / 16 : ℝ) ^ 2 * sqNormProd (seq j))
    (hli : LinearIndependent ℝ (seq k)) (hGram : HasIntegralGram (seq k)) :
    k < shortenRoundBound n B := by
  by_contra! hge
  have hchain : ∀ m ≤ k, sqNormProd (seq m) ≤ ((13 / 16 : ℝ) ^ 2) ^ m * sqNormProd (seq 0) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      have hm' : m < k := Nat.lt_of_succ_le hm
      calc sqNormProd (seq (m + 1))
          ≤ (13 / 16 : ℝ) ^ 2 * sqNormProd (seq m) := hstep m hm'
        _ ≤ (13 / 16 : ℝ) ^ 2 * (((13 / 16 : ℝ) ^ 2) ^ m * sqNormProd (seq 0)) :=
            mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hm')) (by positivity)
        _ = ((13 / 16 : ℝ) ^ 2) ^ (m + 1) * sqNormProd (seq 0) := by rw [pow_succ']; ring
  have hk_bound :
      sqNormProd (seq k) ≤ ((13 / 16 : ℝ) ^ 2) ^ (shortenRoundBound n B) * (B : ℝ) ^ n := by
    have hpow_le : ((13 / 16 : ℝ) ^ 2) ^ k ≤ ((13 / 16 : ℝ) ^ 2) ^ (shortenRoundBound n B) :=
      pow_le_pow_of_le_one (by positivity) (by norm_num) hge
    calc sqNormProd (seq k)
        ≤ ((13 / 16 : ℝ) ^ 2) ^ k * sqNormProd (seq 0) := hchain k le_rfl
      _ ≤ ((13 / 16 : ℝ) ^ 2) ^ (shortenRoundBound n B) * (B : ℝ) ^ n :=
          mul_le_mul hpow_le (sqNormProd_le_pow hB) (sqNormProd_nonneg _) (by positivity)
  have hlt1 := pow_shortenRoundBound_mul_lt_one (B := B) hn
  have hone : (1 : ℝ) ≤ sqNormProd (seq k) := one_le_sqNormProd hli hGram
  linarith

/-! ### 3. Exact Executable Rational Orthogonal Target (`BareissElimination.ratKernelBasis`) -/

section RationalTarget

/-- Squared Euclidean norm of a rational vector `v : Fin n → ℚ`. -/
@[expose] def sqNormRat {n : ℕ} (v : Fin n → ℚ) : ℚ :=
  ∑ k : Fin n, (v k) ^ 2

/-- Embedding of `Fin n → ℚ` into `EuclideanSpace ℝ (Fin n)`. -/
@[expose] noncomputable def toEuclidean {n : ℕ} (v : Fin n → ℚ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => (v k : ℝ))

/-- Casting `sqNormRat v` to `ℝ` equals `‖toEuclidean v‖ ^ 2`. -/
theorem sqNormRat_cast_eq_norm_sq {n : ℕ} (v : Fin n → ℚ) :
    (sqNormRat v : ℝ) = ‖toEuclidean v‖ ^ 2 := by
  rw [sqNormRat, toEuclidean, EuclideanSpace.norm_sq_eq]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

/-- Every nonzero rational vector has strictly positive `sqNormRat`. -/
theorem sqNormRat_pos_of_ne_zero {n : ℕ} {v : Fin n → ℚ} (hv : v ≠ 0) : 0 < sqNormRat v := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  exact Finset.sum_pos' (fun j _ => sq_nonneg (v j)) ⟨k, Finset.mem_univ k, sq_pos_of_ne_zero hk⟩

/-- Computable exact rational index maximizing squared Euclidean norm among
`S : Fin (m + 1) → Fin (m + 1) → ℚ`. -/
@[expose] def maxSqNormIndex {m : ℕ} (S : Fin (m + 1) → Fin (m + 1) → ℚ) : Fin (m + 1) :=
  (List.finRange (m + 1)).foldl
    (fun best j => if sqNormRat (S best) < sqNormRat (S j) then j else best) 0

private theorem sqNormRat_le_foldl {m : ℕ} (S : Fin (m + 1) → Fin (m + 1) → ℚ) :
    ∀ (l : List (Fin (m + 1))) (init : Fin (m + 1)),
      sqNormRat (S init) ≤
        sqNormRat (S (l.foldl
          (fun best j => if sqNormRat (S best) < sqNormRat (S j) then j else best) init)) ∧
      ∀ x ∈ l, sqNormRat (S x) ≤
        sqNormRat (S (l.foldl
          (fun best j => if sqNormRat (S best) < sqNormRat (S j) then j else best) init))
  | [], init => ⟨le_rfl, by simp⟩
  | a :: l, init => by
    simp only [List.foldl_cons]
    set next := if sqNormRat (S init) < sqNormRat (S a) then a else init
    have hinit : sqNormRat (S init) ≤ sqNormRat (S next) := by
      dsimp only [next]; split_ifs with h <;> linarith
    have ha : sqNormRat (S a) ≤ sqNormRat (S next) := by
      dsimp only [next]; split_ifs with h <;> linarith
    obtain ⟨h1, h2⟩ := sqNormRat_le_foldl S l next
    refine ⟨hinit.trans h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ha.trans h1
    · exact h2 x hx'

/-- Every vector in `S` has squared norm at most that of `S (maxSqNormIndex S)`. -/
theorem sqNormRat_le_maxSqNormIndex {m : ℕ} (S : Fin (m + 1) → Fin (m + 1) → ℚ)
    (j : Fin (m + 1)) :
    sqNormRat (S j) ≤ sqNormRat (S (maxSqNormIndex S)) :=
  (sqNormRat_le_foldl S _ 0).2 j (List.mem_finRange j)

/-- The vector selected by `maxSqNormIndex S` attains the Pi supremum norm `‖S‖`. -/
theorem norm_maxSqNormIndex_eq_pi_norm {m : ℕ} (S : Fin (m + 1) → Fin (m + 1) → ℚ) :
    ‖toEuclidean (S (maxSqNormIndex S))‖ = ‖fun j => toEuclidean (S j)‖ := by
  apply le_antisymm
  · exact norm_le_pi_norm (fun j => toEuclidean (S j)) (maxSqNormIndex S)
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro j
    have hsq : ‖toEuclidean (S j)‖ ^ 2 ≤ ‖toEuclidean (S (maxSqNormIndex S))‖ ^ 2 := by
      rw [← sqNormRat_cast_eq_norm_sq, ← sqNormRat_cast_eq_norm_sq]
      exact_mod_cast sqNormRat_le_maxSqNormIndex S j
    nlinarith [norm_nonneg (toEuclidean (S j)), norm_nonneg (toEuclidean (S (maxSqNormIndex S)))]

/-- Irrational-free rational scaling factor `ρ = (Nat.sqrt (64 * p * d) + 1) / (16 * d)` where
`p / d = sqS / sqV`, unconditionally satisfying
`(1 / 4) * (sqS / sqV) < ρ ^ 2 ≤ (9 / 16) ^ 2 * (sqS / sqV)`. -/
@[expose] def ratOrthoScale (sqS sqV : ℚ) : ℚ :=
  let q := sqS / sqV
  let p := q.num.toNat
  let d := q.den
  ((Nat.sqrt (64 * p * d) + 1 : ℕ) : ℚ) / (16 * (d : ℚ))

/-- Exact rational sandwich on `(ratOrthoScale sqS sqV) ^ 2` for positive rational squared norms. -/
theorem ratOrthoScale_sq_bounds {sqS sqV : ℚ} (hS : 0 < sqS) (hV : 0 < sqV) :
    (1 / 4 : ℚ) * (sqS / sqV) < (ratOrthoScale sqS sqV) ^ 2 ∧
      (ratOrthoScale sqS sqV) ^ 2 ≤ (9 / 16 : ℚ) ^ 2 * (sqS / sqV) := by
  unfold ratOrthoScale
  dsimp only
  set q : ℚ := sqS / sqV
  have hq_pos : 0 < q := div_pos hS hV
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq_pos
  set p : ℕ := q.num.toNat
  set d : ℕ := q.den
  have hp_pos : 0 < p := by omega
  have hd_pos : 0 < d := q.den_nz.bot_lt
  have hq_eq : q = (p : ℚ) / (d : ℚ) := by
    have h1 : (p : ℤ) = q.num := Int.toNat_of_nonneg hnum_pos.le
    calc q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
      _ = (p : ℚ) / (d : ℚ) := by dsimp only [d]; rw [← h1]; simp
  set m : ℕ := p * d
  have hm_pos : 1 ≤ m := Nat.mul_pos hp_pos hd_pos
  set k : ℕ := Nat.sqrt (64 * m)
  have hlo_nat : 64 * m < (k + 1) ^ 2 := by
    simpa only [sq] using Nat.lt_succ_sqrt (64 * m)
  have hle_nat : k ^ 2 ≤ 64 * m := by
    simpa only [sq] using Nat.sqrt_le (64 * m)
  have hk_le : k ≤ 8 * m := by
    have h1 : k ^ 2 ≤ (8 * m) ^ 2 := by
      calc k ^ 2 ≤ 64 * m := hle_nat
        _ ≤ 64 * (m * m) := Nat.mul_le_mul_left 64 (Nat.le_mul_of_pos_right m hm_pos)
        _ = (8 * m) ^ 2 := by ring
    exact (Nat.pow_le_pow_iff_left two_ne_zero).mp h1
  have hhi_nat : (k + 1) ^ 2 ≤ 81 * m := by
    calc (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
      _ ≤ 64 * m + 2 * (8 * m) + m := by omega
      _ = 81 * m := by ring
  have hd_q : (0 : ℚ) < (d : ℚ) := Nat.cast_pos.mpr hd_pos
  have hlo_q : (64 * (p : ℚ) * (d : ℚ)) < ((k + 1 : ℕ) : ℚ) ^ 2 := by
    have : 64 * p * d < (k + 1) ^ 2 := by simpa [m, mul_assoc] using hlo_nat
    exact_mod_cast this
  have hhi_q : ((k + 1 : ℕ) : ℚ) ^ 2 ≤ 81 * (p : ℚ) * (d : ℚ) := by
    have : (k + 1) ^ 2 ≤ 81 * p * d := by simpa [m, mul_assoc] using hhi_nat
    exact_mod_cast this
  have hsq_eq : (((k + 1 : ℕ) : ℚ) / (16 * (d : ℚ))) ^ 2 =
      ((k + 1 : ℕ) : ℚ) ^ 2 / (256 * (d : ℚ) ^ 2) := by
    rw [div_pow]; ring
  have hk_def : Nat.sqrt (64 * p * d) = k := by simp [k, m, mul_assoc]
  rw [hk_def, hsq_eq, hq_eq]
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    have h1 : (1 / 4 : ℚ) * ((p : ℚ) / (d : ℚ)) * (256 * (d : ℚ) ^ 2) =
        64 * (p : ℚ) * (d : ℚ) := by field_simp; ring
    linarith
  · rw [div_le_iff₀ (by positivity)]
    have h2 : (9 / 16 : ℚ) ^ 2 * ((p : ℚ) / (d : ℚ)) * (256 * (d : ℚ) ^ 2) =
        81 * (p : ℚ) * (d : ℚ) := by field_simp; ring
    linarith

/-- `m × (m + 1)` `RatTable` whose rows are `{S j : j ≠ i}` ordered by `i.succAbove`. -/
@[expose] def omitRowTable {m : ℕ} (S : Fin (m + 1) → Fin (m + 1) → ℚ) (i : Fin (m + 1)) :
    Cslib.LinearAlgebra.RatTable :=
  Cslib.RowTable.ofMatrix (Matrix.of fun a k => S (i.succAbove a) k)

/-- Entry evaluation of `omitRowTable S i`. -/
theorem omitRowTable_toMatrix_apply {m : ℕ} (S : Fin (m + 1) → Fin (m + 1) → ℚ)
    (i : Fin (m + 1)) (a : Fin m) (k : Fin (m + 1)) :
    (omitRowTable S i).toMatrix a k = S (i.succAbove a) k := by
  simp [omitRowTable]

/-- Executable rational orthogonal target `t = ρ • v ∈ ℚ^{m+1}` computed via `ratKernelBasis` on
`omitRowTable S (maxSqNormIndex S)` and scaled by `ratOrthoScale`. -/
@[expose] def ratOrthoTarget {m : ℕ} (S : Fin (m + 1) → Fin (m + 1) → ℚ) : Fin (m + 1) → ℚ :=
  let iStar := maxSqNormIndex S
  let M := omitRowTable S iStar
  let vList := (Cslib.LinearAlgebra.ratKernelBasis M).headD []
  let v : Fin (m + 1) → ℚ := fun k => vList.getD k.val 0
  let ρ := ratOrthoScale (sqNormRat (S iStar)) (sqNormRat v)
  fun k => ρ * v k

private theorem list_headD_eq_getElem_zero {α : Type*} {l : List α} {d : α} (hl : 0 < l.length) :
    l.headD d = l[0]'hl := by
  cases l with
  | nil => simp at hl
  | cons x xs => rfl

/-- Specification of `ratOrthoTarget`: for any linearly independent rational family
`S : Fin (m + 1) → Fin (m + 1) → ℚ`, `t := toEuclidean (ratOrthoTarget S)` is orthogonal to every
`S j` with `j ≠ maxSqNormIndex S` and satisfies `(1 / 2) * ‖S‖ < ‖t‖ ≤ (9 / 16) * ‖S‖`. -/
theorem ratOrthoTarget_spec {m : ℕ} (S : Fin (m + 1) → Fin (m + 1) → ℚ)
    (hS : LinearIndependent ℝ (fun j => toEuclidean (S j))) :
    (∀ j, j ≠ maxSqNormIndex S →
      ⟪toEuclidean (ratOrthoTarget S), toEuclidean (S j)⟫ = 0) ∧
    (1 / 2 : ℝ) * ‖fun j => toEuclidean (S j)‖ < ‖toEuclidean (ratOrthoTarget S)‖ ∧
    ‖toEuclidean (ratOrthoTarget S)‖ ≤ (9 / 16 : ℝ) * ‖fun j => toEuclidean (S j)‖ := by
  set iStar := maxSqNormIndex S
  let M := omitRowTable S iStar
  let res := Cslib.LinearAlgebra.rationalElim M
  obtain ⟨_, _, _, _, hrank_eq, _, _, _, _, _, hker_len, hli, hspan⟩ :=
    Cslib.LinearAlgebra.rationalElim_spec M
  change res.rank = M.toMatrix.rank at hrank_eq
  change res.kernelBasis.length = m + 1 - res.rank at hker_len
  have hrank_le : M.toMatrix.rank ≤ m := by
    simpa [M, omitRowTable] using Matrix.rank_le_card_height M.toMatrix
  have hker_pos : 0 < res.kernelBasis.length := by omega
  have hhead : (Cslib.LinearAlgebra.ratKernelBasis M).headD [] = res.kernelBasis[0]'hker_pos :=
    list_headD_eq_getElem_zero hker_pos
  let v : Fin (m + 1) → ℚ := fun k => (res.kernelBasis[0]'hker_pos).getD k.val 0
  have hv_ne : v ≠ 0 := by
    change LinearIndependent ℚ (fun idx : Fin res.kernelBasis.length =>
      fun k : Fin (m + 1) => res.kernelBasis[idx.val].getD k.val 0) at hli
    exact hli.ne_zero ⟨0, hker_pos⟩
  have hv_ker : M.toMatrix.mulVec v = 0 := by
    have hmem : (v : Fin M.numCols → ℚ) ∈
        Submodule.span ℚ (Set.range fun idx : Fin res.kernelBasis.length =>
          (fun j : Fin M.numCols => res.kernelBasis[idx.val].getD j.val 0)) :=
      Submodule.subset_span ⟨⟨0, hker_pos⟩, rfl⟩
    rw [hspan] at hmem
    exact (LinearMap.mem_ker (f := M.toMatrix.mulVecLin)).mp hmem
  have hv_orth : ∀ j, j ≠ iStar → ∑ k : Fin (m + 1), v k * S j k = 0 := by
    intro j hj
    obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hj
    have ha := congr_fun hv_ker a
    change ∑ k : Fin (m + 1), (omitRowTable S iStar).toMatrix a k * v k = 0 at ha
    have ha' : ∑ k : Fin (m + 1), S (iStar.succAbove a) k * v k = 0 := by
      simpa only [omitRowTable_toMatrix_apply] using ha
    simpa only [mul_comm] using ha'
  set ρ := ratOrthoScale (sqNormRat (S iStar)) (sqNormRat v)
  have ht_eq : ratOrthoTarget S = fun k => ρ * v k := by
    funext k
    change ratOrthoScale (sqNormRat (S iStar))
      (sqNormRat fun k => ((Cslib.LinearAlgebra.ratKernelBasis M).headD []).getD k.val 0) *
      ((Cslib.LinearAlgebra.ratKernelBasis M).headD []).getD k.val 0 = ρ * v k
    rw [hhead]
  have hS_pos : 0 < sqNormRat (S iStar) :=
    sqNormRat_pos_of_ne_zero fun h0 => hS.ne_zero iStar (by ext k; simp [toEuclidean, h0])
  have hv_pos : 0 < sqNormRat v := sqNormRat_pos_of_ne_zero hv_ne
  obtain ⟨hlo_q, hhi_q⟩ := ratOrthoScale_sq_bounds hS_pos hv_pos
  have hnorm_t_sq : ‖toEuclidean (ratOrthoTarget S)‖ ^ 2 =
      (ρ : ℝ) ^ 2 * ‖toEuclidean v‖ ^ 2 := by
    rw [← sqNormRat_cast_eq_norm_sq, ← sqNormRat_cast_eq_norm_sq, ht_eq, sqNormRat, sqNormRat,
      ← Rat.cast_pow, ← Rat.cast_mul, Finset.mul_sum]
    exact congrArg (Rat.cast (K := ℝ)) (Finset.sum_congr rfl fun _ _ => by ring)
  have hpi_eq : ‖fun j => toEuclidean (S j)‖ = ‖toEuclidean (S iStar)‖ :=
    (norm_maxSqNormIndex_eq_pi_norm S).symm
  have ht_sq_lo : (1 / 4 : ℝ) * ‖fun j => toEuclidean (S j)‖ ^ 2 <
      ‖toEuclidean (ratOrthoTarget S)‖ ^ 2 := by
    have hlo_q' : (1 / 4 : ℚ) * sqNormRat (S iStar) < ρ ^ 2 * sqNormRat v := by
      have := mul_lt_mul_of_pos_right hlo_q hv_pos
      rwa [mul_assoc, div_mul_cancel₀ _ hv_pos.ne'] at this
    have hlo_r : (1 / 4 : ℝ) * (sqNormRat (S iStar) : ℝ) < (ρ : ℝ) ^ 2 * (sqNormRat v : ℝ) := by
      simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using
        (Rat.cast_lt (K := ℝ)).mpr hlo_q'
    rwa [sqNormRat_cast_eq_norm_sq, sqNormRat_cast_eq_norm_sq, ← hnorm_t_sq, ← hpi_eq] at hlo_r
  have ht_sq_hi : ‖toEuclidean (ratOrthoTarget S)‖ ^ 2 ≤
      (9 / 16 : ℝ) ^ 2 * ‖fun j => toEuclidean (S j)‖ ^ 2 := by
    have hhi_q' : ρ ^ 2 * sqNormRat v ≤ (9 / 16 : ℚ) ^ 2 * sqNormRat (S iStar) := by
      have := mul_le_mul_of_nonneg_right hhi_q hv_pos.le
      rwa [mul_assoc, div_mul_cancel₀ _ hv_pos.ne'] at this
    have hhi_r :
        (ρ : ℝ) ^ 2 * (sqNormRat v : ℝ) ≤ (9 / 16 : ℝ) ^ 2 * (sqNormRat (S iStar) : ℝ) := by
      simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr hhi_q'
    rwa [sqNormRat_cast_eq_norm_sq, sqNormRat_cast_eq_norm_sq, ← hnorm_t_sq, ← hpi_eq] at hhi_r
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [toEuclidean, toEuclidean, EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, dotProduct, ht_eq]
    have hsum : ∑ k : Fin (m + 1), ((S j k : ℚ) : ℝ) * ((ρ * v k : ℚ) : ℝ) =
        (ρ : ℝ) * ((∑ k : Fin (m + 1), v k * S j k : ℚ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsum, hv_orth j hj, Rat.cast_zero, mul_zero]
  · nlinarith [norm_nonneg (toEuclidean (ratOrthoTarget S)),
      norm_nonneg (fun j => toEuclidean (S j))]
  · nlinarith [norm_nonneg (toEuclidean (ratOrthoTarget S)),
      norm_nonneg (fun j => toEuclidean (S j))]

end RationalTarget

/-! ### 4. Finite Deterministic Oracle-Loop & Guarded-Step Reductions (MR07 Lemma 5.10) -/

section ShortenLoop

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Predicate that `stepTarget S = (i*, t)` supplies a valid orthogonal shortening target for
any linearly independent family `S` in `L`. -/
@[expose] def ValidTargetOracle (L : Submodule ℤ E)
    (stepTarget : (Fin (finrank ℤ L) → E) → Fin (finrank ℤ L) × E) : Prop :=
  ∀ S : Fin (finrank ℤ L) → E, LinearIndependent ℝ S → (∀ j, S j ∈ L) →
    let (i, t) := stepTarget S
    ‖S i‖ = ‖S‖ ∧ (∀ j, j ≠ i → ⟪t, S j⟫ = 0) ∧
      (1 / 2 : ℝ) * ‖S‖ ≤ ‖t‖ ∧ ‖t‖ ≤ (9 / 16 : ℝ) * ‖S‖

/-- Finite shortening loop starting at round index `r` with `fuel` rounds remaining.
At round `r`, queries `oracles r` on the current family `S`, target `(stepTarget S).2`, and radius
`‖S‖ / 8`; if the returned candidate `u` lies in `L` and satisfies `‖u - t‖ ≤ (1 / 4) * ‖S‖`,
replaces `S i` by `u` and advances to round `r + 1`; otherwise halts and returns `S`.

Passing round-indexed `oracles : ℕ → ...` supports both deterministic single-oracle loops
(`fun _ => oracle`) and randomized independent-round reductions (where round `r` depends only on
the state reached after rounds `0, …, r - 1` and fresh randomness at round `r`). -/
@[expose] noncomputable def shortenLoopFrom (L : Submodule ℤ E)
    (stepTarget : (Fin (finrank ℤ L) → E) → Fin (finrank ℤ L) × E)
    (oracles : ℕ → (Fin (finrank ℤ L) → E) → E → ℝ → Option E) :
    ℕ → ℕ → (Fin (finrank ℤ L) → E) → (Fin (finrank ℤ L) → E)
  | _, 0, S => S
  | r, fuel + 1, S =>
    let (i, t) := stepTarget S
    match oracles r S t (‖S‖ / 8) with
    | some u =>
      haveI := Classical.propDecidable (u ∈ L ∧ ‖u - t‖ ≤ (1 / 4 : ℝ) * ‖S‖)
      if u ∈ L ∧ ‖u - t‖ ≤ (1 / 4 : ℝ) * ‖S‖ then
        shortenLoopFrom L stepTarget oracles (r + 1) fuel (Function.update S i u)
      else
        S
    | none => S

/-- Finite shortening loop starting from round `0` for at most `fuel` rounds. -/
noncomputable abbrev shortenLoop (L : Submodule ℤ E)
    (stepTarget : (Fin (finrank ℤ L) → E) → Fin (finrank ℤ L) × E)
    (oracles : ℕ → (Fin (finrank ℤ L) → E) → E → ℝ → Option E)
    (fuel : ℕ) (S : Fin (finrank ℤ L) → E) : Fin (finrank ℤ L) → E :=
  shortenLoopFrom L stepTarget oracles 0 fuel S

omit [InnerProductSpace ℝ E] in
private theorem shortenLoopFrom_succ_none (L : Submodule ℤ E)
    (stepTarget : (Fin (finrank ℤ L) → E) → Fin (finrank ℤ L) × E)
    (oracles : ℕ → (Fin (finrank ℤ L) → E) → E → ℝ → Option E)
    (r fuel : ℕ) (S : Fin (finrank ℤ L) → E)
    (hcall : oracles r S (stepTarget S).2 (‖S‖ / 8) = none) :
    shortenLoopFrom L stepTarget oracles r (fuel + 1) S = S := by
  simp only [shortenLoopFrom, hcall]

omit [InnerProductSpace ℝ E] in
private theorem shortenLoopFrom_succ_some_pos (L : Submodule ℤ E)
    (stepTarget : (Fin (finrank ℤ L) → E) → Fin (finrank ℤ L) × E)
    (oracles : ℕ → (Fin (finrank ℤ L) → E) → E → ℝ → Option E)
    (r fuel : ℕ) (S : Fin (finrank ℤ L) → E) {u : E}
    (hcall : oracles r S (stepTarget S).2 (‖S‖ / 8) = some u)
    (hvalid : u ∈ L ∧ ‖u - (stepTarget S).2‖ ≤ (1 / 4 : ℝ) * ‖S‖) :
    shortenLoopFrom L stepTarget oracles r (fuel + 1) S =
      shortenLoopFrom L stepTarget oracles (r + 1) fuel
        (Function.update S (stepTarget S).1 u) := by
  simp only [shortenLoopFrom, hcall, hvalid, and_self, ↓reduceIte]

omit [InnerProductSpace ℝ E] in
private theorem shortenLoopFrom_succ_some_neg (L : Submodule ℤ E)
    (stepTarget : (Fin (finrank ℤ L) → E) → Fin (finrank ℤ L) × E)
    (oracles : ℕ → (Fin (finrank ℤ L) → E) → E → ℝ → Option E)
    (r fuel : ℕ) (S : Fin (finrank ℤ L) → E) {u : E}
    (hcall : oracles r S (stepTarget S).2 (‖S‖ / 8) = some u)
    (hvalid : ¬ (u ∈ L ∧ ‖u - (stepTarget S).2‖ ≤ (1 / 4 : ℝ) * ‖S‖)) :
    shortenLoopFrom L stepTarget oracles r (fuel + 1) S = S := by
  simp only [shortenLoopFrom, hcall, hvalid, ↓reduceIte]

private theorem shortenLoopFrom_invariant (L : Submodule ℤ E)
    (stepTarget : (Fin (finrank ℤ L) → E) → Fin (finrank ℤ L) × E)
    (oracles : ℕ → (Fin (finrank ℤ L) → E) → E → ℝ → Option E)
    (hTarget : ValidTargetOracle L stepTarget) :
    ∀ (fuel r : ℕ) (S : Fin (finrank ℤ L) → E),
      LinearIndependent ℝ S → (∀ j, S j ∈ L) →
      let Sout := shortenLoopFrom L stepTarget oracles r fuel S
      LinearIndependent ℝ Sout ∧ (∀ j, Sout j ∈ L) ∧ ‖Sout‖ ≤ ‖S‖ ∧
      ((∃ k < fuel,
          let Sk := shortenLoopFrom L stepTarget oracles r k S
          Sout = Sk ∧
          match oracles (r + k) Sk (stepTarget Sk).2 (‖Sk‖ / 8) with
          | some u => ¬ (u ∈ L ∧ ‖u - (stepTarget Sk).2‖ ≤ (1 / 4 : ℝ) * ‖Sk‖)
          | none => True) ∨
        sqNormProd Sout ≤ ((13 / 16 : ℝ) ^ 2) ^ fuel * sqNormProd S)
  | 0, r, S, hli, hmem =>
    ⟨hli, hmem, le_rfl, Or.inr (by simp [shortenLoopFrom])⟩
  | fuel + 1, r, S, hli, hmem => by
    have ⟨hi, horth, hlo, hhi⟩ := hTarget S hli hmem
    cases hcall : oracles r S (stepTarget S).2 (‖S‖ / 8) with
    | none =>
      dsimp only
      rw [shortenLoopFrom_succ_none L stepTarget oracles r fuel S hcall]
      exact ⟨hli, hmem, le_rfl, Or.inl ⟨0, Nat.zero_lt_succ fuel, rfl, by
        simp [shortenLoopFrom, hcall]⟩⟩
    | some u =>
      by_cases hvalid : u ∈ L ∧ ‖u - (stepTarget S).2‖ ≤ (1 / 4 : ℝ) * ‖S‖
      · have hpos := shortenLoopFrom_succ_some_pos L stepTarget oracles r fuel S hcall hvalid
        dsimp only
        rw [hpos]
        have hli' : LinearIndependent ℝ (Function.update S (stepTarget S).1 u) :=
          shortenStep_linearIndependent hli horth hlo hvalid.2
        have hmem' : ∀ j, Function.update S (stepTarget S).1 u j ∈ L :=
          (Function.forall_update_iff S fun _ v => v ∈ L).2 ⟨hvalid.1, fun j _ => hmem j⟩
        have hpot' : sqNormProd (Function.update S (stepTarget S).1 u) ≤
            (13 / 16 : ℝ) ^ 2 * sqNormProd S :=
          shortenStep_sqNormProd_le hi hhi hvalid.2
        obtain ⟨hli_o, hmem_o, hnorm_o, hor⟩ :=
          shortenLoopFrom_invariant L stepTarget oracles hTarget fuel (r + 1) _ hli' hmem'
        refine ⟨hli_o, hmem_o, hnorm_o.trans (shortenStep_pi_norm_le hhi hvalid.2), ?_⟩
        rcases hor with ⟨k, hk, heq, hhalt⟩ | hpot_o
        · left
          refine ⟨k + 1, Nat.succ_lt_succ hk, ?_, ?_⟩
          · rwa [shortenLoopFrom_succ_some_pos L stepTarget oracles r k S hcall hvalid]
          · rwa [shortenLoopFrom_succ_some_pos L stepTarget oracles r k S hcall hvalid,
              show r + (k + 1) = r + 1 + k by omega]
        · right
          calc sqNormProd (shortenLoopFrom L stepTarget oracles (r + 1) fuel
                  (Function.update S (stepTarget S).1 u))
              ≤ ((13 / 16 : ℝ) ^ 2) ^ fuel *
                  sqNormProd (Function.update S (stepTarget S).1 u) := hpot_o
            _ ≤ ((13 / 16 : ℝ) ^ 2) ^ fuel * ((13 / 16 : ℝ) ^ 2 * sqNormProd S) := by gcongr
            _ = ((13 / 16 : ℝ) ^ 2) ^ (fuel + 1) * sqNormProd S := by rw [pow_succ]; ring
      · dsimp only
        rw [shortenLoopFrom_succ_some_neg L stepTarget oracles r fuel S hcall hvalid]
        exact ⟨hli, hmem, le_rfl, Or.inl ⟨0, Nat.zero_lt_succ fuel, rfl, by
          simpa only [add_zero, shortenLoopFrom, hcall] using hvalid⟩⟩

/-- Finite round-by-round soundness of the MR07 Lemma 5.10 shortening loop: starting from a
full-rank family `S₀` in a lattice `L` with integral inner products (`∀ x ∈ L, ∀ y ∈ L,
∃ z : ℤ, ⟪x, y⟫ = z`) and `∀ j, ‖S₀ j‖ ^ 2 ≤ B`, if for every round `k < shortenRoundBound
(finrank ℤ L) B` the `k`-th oracle succeeds on the visited state `S_k := shortenLoop ... k S₀`
whenever `S_k` is a valid `IncGDD^φ_{γ, 8}` instance, then `shortenLoop` outputs a `GIVP^φ_{8γ}`
solution `S_out` with `‖S_out‖ ≤ ‖S₀‖`.

Quantifying `hOracle` solely over the single visited state `S_k` at each round `k` supports
union-bounding per-round failure probability directly across independent coin tapes. -/
theorem shortenLoop_isSolution_givp (φ : Submodule ℤ E → ℝ) (γ : ℝ)
    (L : Submodule ℤ E)
    (stepTarget : (Fin (finrank ℤ L) → E) → Fin (finrank ℤ L) × E)
    (oracles : ℕ → (Fin (finrank ℤ L) → E) → E → ℝ → Option E)
    (hTarget : ValidTargetOracle L stepTarget)
    (hL_gram : ∀ x ∈ L, ∀ y ∈ L, ∃ z : ℤ, ⟪x, y⟫ = z)
    (B : ℕ) (S₀ : Fin (finrank ℤ L) → E)
    (hS₀_li : LinearIndependent ℝ S₀) (hS₀_mem : ∀ j, S₀ j ∈ L)
    (hB : ∀ j, ‖S₀ j‖ ^ 2 ≤ (B : ℝ))
    (hOracle : ∀ k < shortenRoundBound (finrank ℤ L) B,
      let Sk := shortenLoop L stepTarget oracles k S₀
      IncGDD.IsValidInstance φ γ L Sk (‖Sk‖ / 8) →
      ∃ u, oracles k Sk (stepTarget Sk).2 (‖Sk‖ / 8) = some u ∧
        IncGDD.IsSolution 8 L Sk (stepTarget Sk).2 (‖Sk‖ / 8) u) :
    let S_out := shortenLoop L stepTarget oracles (shortenRoundBound (finrank ℤ L) B) S₀
    GIVP.IsSolution φ (8 * γ) L S_out ∧ ‖S_out‖ ≤ ‖S₀‖ := by
  by_cases hn : finrank ℤ L = 0
  · simp only [hn, shortenRoundBound_zero_left, shortenLoop, shortenLoopFrom]
    refine ⟨⟨hS₀_li, hS₀_mem, fun j => absurd j.isLt (by omega)⟩, le_rfl⟩
  · have hnpos : 0 < finrank ℤ L := Nat.pos_of_ne_zero hn
    set K := shortenRoundBound (finrank ℤ L) B
    obtain ⟨hli_o, hmem_o, hnorm_o, hor⟩ :=
      shortenLoopFrom_invariant L stepTarget oracles hTarget K 0 S₀ hS₀_li hS₀_mem
    refine ⟨?_, hnorm_o⟩
    rcases hor with ⟨k, hk, heq, hhalt⟩ | hpot_o
    · simp only [zero_add] at hhalt
      rcases isSolution_givp_or_isValidInstance_incGDD φ γ L
          (shortenLoop L stepTarget oracles K S₀) hli_o hmem_o with hsol | hval
      · exact hsol
      · rw [shortenLoop, heq] at hval
        obtain ⟨u, hcall, hsol⟩ := hOracle k hk hval
        rw [hcall] at hhalt
        exact False.elim (hhalt ⟨hsol.mem, by linarith [hsol.dist_le]⟩)
    · have h1 : (1 : ℝ) ≤ sqNormProd (shortenLoop L stepTarget oracles K S₀) :=
        one_le_sqNormProd hli_o fun i j => hL_gram _ (hmem_o i) _ (hmem_o j)
      have hlt1 := pow_shortenRoundBound_mul_lt_one (B := B) hnpos
      have hleB := mul_le_mul_of_nonneg_left (sqNormProd_le_pow hB)
        (by positivity : (0 : ℝ) ≤ ((13 / 16 : ℝ) ^ 2) ^ K)
      linarith

/-- Unconditional guarded shortening step for fixed-iteration loops (`IsPPTOn.iterateWith_spec`):
replaces `S i` by `u` when `u ∈ L`, `‖u‖ < ‖S i‖`, and `Function.update S i u` is linearly
independent, and otherwise leaves `S` unchanged. -/
@[expose] noncomputable def shortenGuardedStep (L : Submodule ℤ E) (S : Fin (finrank ℤ L) → E)
    (i : Fin (finrank ℤ L)) (u : E) : Fin (finrank ℤ L) → E :=
  haveI := Classical.propDecidable
    (u ∈ L ∧ ‖u‖ < ‖S i‖ ∧ LinearIndependent ℝ (Function.update S i u))
  if u ∈ L ∧ ‖u‖ < ‖S i‖ ∧ LinearIndependent ℝ (Function.update S i u) then
    Function.update S i u
  else
    S

/-- Unconditional support invariants of `shortenGuardedStep`: holds for every candidate `u : E`. -/
theorem shortenGuardedStep_invariants {L : Submodule ℤ E} {S : Fin (finrank ℤ L) → E}
    (hS_li : LinearIndependent ℝ S) (hS_mem : ∀ j, S j ∈ L)
    (i : Fin (finrank ℤ L)) (u : E) :
    let S' := shortenGuardedStep L S i u
    LinearIndependent ℝ S' ∧ (∀ j, S' j ∈ L) ∧ ‖S'‖ ≤ ‖S‖ := by
  dsimp only [shortenGuardedStep]
  split_ifs with h
  · exact ⟨h.2.2, (Function.forall_update_iff S fun _ v => v ∈ L).2 ⟨h.1, fun j _ => hS_mem j⟩,
      pi_norm_update_le (h.2.1.le.trans (norm_le_pi_norm S i))⟩
  · exact ⟨hS_li, hS_mem, le_rfl⟩

/-- On every valid `IncGDD` shortening candidate, `shortenGuardedStep` accepts and contracts
`sqNormProd` by at most `(13 / 16) ^ 2`. -/
theorem shortenGuardedStep_of_incGDD {L : Submodule ℤ E} {S : Fin (finrank ℤ L) → E}
    (hS_li : LinearIndependent ℝ S)
    {i : Fin (finrank ℤ L)} (hi : ‖S i‖ = ‖S‖) {t u : E}
    (ht_orth : ∀ j, j ≠ i → ⟪t, S j⟫ = 0)
    (ht_lo : (1 / 2 : ℝ) * ‖S‖ ≤ ‖t‖)
    (ht_hi : ‖t‖ ≤ (9 / 16 : ℝ) * ‖S‖)
    (hu : IncGDD.IsSolution 8 L S t (‖S‖ / 8) u) :
    shortenGuardedStep L S i u = Function.update S i u ∧
      sqNormProd (shortenGuardedStep L S i u) ≤ (13 / 16 : ℝ) ^ 2 * sqNormProd S := by
  have hu_dist : ‖u - t‖ ≤ (1 / 4 : ℝ) * ‖S‖ := by linarith [hu.dist_le]
  have hSpos : 0 < ‖S‖ := pi_norm_pos_of_linearIndependent hS_li i
  have hlt : ‖u‖ < ‖S i‖ := by linarith [shortenStep_norm_le ht_hi hu_dist]
  have hli' := shortenStep_linearIndependent hS_li ht_orth ht_lo hu_dist
  have hcond : u ∈ L ∧ ‖u‖ < ‖S i‖ ∧ LinearIndependent ℝ (Function.update S i u) :=
    ⟨hu.mem, hlt, hli'⟩
  have heq : shortenGuardedStep L S i u = Function.update S i u := by
    simp only [shortenGuardedStep, hcond, and_self, ↓reduceIte]
  exact ⟨heq, heq ▸ shortenStep_sqNormProd_le hi ht_hi hu_dist⟩

/-- Fixed-iteration guarded-loop soundness (tailored for `IsPPTOn.iterateWith_spec`):
any sequence `seq` stepping by `shortenGuardedStep` from `S₀` preserves `LinearIndependent`,
membership in `L`, and `‖seq k‖ ≤ ‖S₀‖` unconditionally at every step, and reaches a
`GIVP^φ_{8γ}` solution by step `K = shortenRoundBound (finrank ℤ L) B` whenever every valid
`IncGDD` round `k < K` receives an `IncGDD.IsSolution`. -/
theorem shortenGuardedIter_isSolution_givp (φ : Submodule ℤ E → ℝ) (γ : ℝ)
    (L : Submodule ℤ E)
    (stepTarget : (Fin (finrank ℤ L) → E) → Fin (finrank ℤ L) × E)
    (hTarget : ValidTargetOracle L stepTarget)
    (hL_gram : ∀ x ∈ L, ∀ y ∈ L, ∃ z : ℤ, ⟪x, y⟫ = z)
    (B : ℕ) (seq : ℕ → Fin (finrank ℤ L) → E) (cand : ℕ → E)
    (hS₀_li : LinearIndependent ℝ (seq 0)) (hS₀_mem : ∀ j, seq 0 j ∈ L)
    (hB : ∀ j, ‖seq 0 j‖ ^ 2 ≤ (B : ℝ))
    (hstep : ∀ k < shortenRoundBound (finrank ℤ L) B,
      seq (k + 1) = shortenGuardedStep L (seq k) (stepTarget (seq k)).1 (cand k))
    (hGood : ∀ k < shortenRoundBound (finrank ℤ L) B,
      IncGDD.IsValidInstance φ γ L (seq k) (‖seq k‖ / 8) →
      IncGDD.IsSolution 8 L (seq k) (stepTarget (seq k)).2 (‖seq k‖ / 8) (cand k)) :
    let K := shortenRoundBound (finrank ℤ L) B
    GIVP.IsSolution φ (8 * γ) L (seq K) ∧ ‖seq K‖ ≤ ‖seq 0‖ := by
  set K := shortenRoundBound (finrank ℤ L) B
  have hinv : ∀ k ≤ K,
      LinearIndependent ℝ (seq k) ∧ (∀ j, seq k j ∈ L) ∧ ‖seq k‖ ≤ ‖seq 0‖ := by
    intro k hk
    induction k with
    | zero => exact ⟨hS₀_li, hS₀_mem, le_rfl⟩
    | succ k ih =>
      have hkl : k < K := Nat.lt_of_succ_le hk
      obtain ⟨hli, hmem, hnorm⟩ := ih hkl.le
      rw [hstep k hkl]
      obtain ⟨hli', hmem', hnorm'⟩ := shortenGuardedStep_invariants hli hmem _ _
      exact ⟨hli', hmem', hnorm'.trans hnorm⟩
  have hmono_norm : ∀ a b, a ≤ b → b ≤ K → ‖seq b‖ ≤ ‖seq a‖ := by
    intro a b hab hbK
    induction b with
    | zero => rw [Nat.le_zero.mp hab]
    | succ b ih =>
      rcases eq_or_lt_of_le hab with rfl | hlt
      · exact le_rfl
      · have hbl : b < K := Nat.lt_of_succ_le hbK
        obtain ⟨hli, hmem, _⟩ := hinv b hbl.le
        have h1 : ‖seq (b + 1)‖ ≤ ‖seq b‖ := by
          rw [hstep b hbl]
          exact (shortenGuardedStep_invariants hli hmem _ _).2.2
        exact h1.trans (ih (Nat.le_of_lt_succ hlt) hbl.le)
  obtain ⟨hliK, hmemK, hnormK⟩ := hinv K le_rfl
  refine ⟨?_, hnormK⟩
  by_cases hn : finrank ℤ L = 0
  · exact ⟨hliK, hmemK, fun j => absurd j.isLt (by omega)⟩
  · have hnpos : 0 < finrank ℤ L := Nat.pos_of_ne_zero hn
    by_contra hnot
    have hval_all : ∀ k < K, IncGDD.IsValidInstance φ γ L (seq k) (‖seq k‖ / 8) := by
      intro k hk
      obtain ⟨hlik, hmemk, _⟩ := hinv k hk.le
      rcases isSolution_givp_or_isValidInstance_incGDD φ γ L (seq k) hlik hmemk with
        hsol | hval
      · exfalso
        apply hnot
        refine ⟨hliK, hmemK, fun j => ?_⟩
        have hle_k : ‖seq k‖ ≤ 8 * γ * φ L :=
          (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hsol.norm_le ⟨0, hnpos⟩))).2
            hsol.norm_le
        exact (norm_le_pi_norm (seq K) j).trans ((hmono_norm k K hk.le le_rfl).trans hle_k)
      · exact hval
    have hdrop : ∀ k < K, sqNormProd (seq (k + 1)) ≤ (13 / 16 : ℝ) ^ 2 * sqNormProd (seq k) := by
      intro k hk
      obtain ⟨hlik, hmemk, _⟩ := hinv k hk.le
      have ⟨hi, horth, hlo, hhi⟩ := hTarget (seq k) hlik hmemk
      rw [hstep k hk]
      exact (shortenGuardedStep_of_incGDD hlik hi horth hlo hhi
        (hGood k hk (hval_all k hk))).2
    have hlt := shortenSteps_lt_bound hnpos hB hdrop hliK
      (fun i j => hL_gram _ (hmemK i) _ (hmemK j))
    exact Nat.lt_irrefl K hlt

end ShortenLoop

end MR07Shorten

end Cslib.Crypto
