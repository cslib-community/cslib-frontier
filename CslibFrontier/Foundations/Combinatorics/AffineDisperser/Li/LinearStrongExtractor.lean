/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.SumsetCorrelationBreaker
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Toeplitz
import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.Data.BitString.Sign.BigOperators
import CslibFrontier.Foundations.Data.Code.BinaryJohnson
import CslibFrontier.Foundations.Data.Code.Concatenation
import CslibFrontier.Foundations.Data.Code.Hadamard
import CslibFrontier.Foundations.Data.Code.ReedSolomon
import CslibFrontier.Probability.BitString.ToeplitzHash
import CslibFrontier.Probability.Extractor.LeftoverHash
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.StatisticalDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Logic.Function.DependsOn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Explicit `𝔽₂`-linear strong seeded extractors

This module constructs unconditional explicit `𝔽₂`-linear strong seeded extractors
(`Cslib.AffineDisperser.Li.IsLinearStrongExtractor`) toward #7793, reusing existing Toeplitz
matrix, binary field, Reed–Solomon, Hadamard, and binary Johnson machinery:

1. **Linear Toeplitz hashing (`toeplitzLinearExt`)**: multiplying `x : BitString n` by a random
   `m × n` Boolean Toeplitz matrix (without an additive offset) is a two-universal family
   (`isTwoUniversal_toeplitzLinear`) and hence an `IsLinearStrongExtractor` with seed length
   `m + n - 1` whenever `m + 2 log₂ δ⁻¹ ≤ k` (`isLinearStrongExtractor_toeplitz`), improving on the
   `m * n`-bit seed of `BitString.LinearHash` while preserving `𝔽₂`-linearity in `x`.

2. **Explicit computable weak designs (`WeakDesign`, `rrvWeakDesign`)**: following the
   Raz–Reingold–Vadhan method of conditional expectations ([Vadhan2012], Section 6.2.3, locator not
   verified against primary PDF), `rrvWeakDesign t d m` deterministically builds `m` blocks of size
   `t` inside `Fin (t * d)` satisfying `∑ j < i, 2 ^ #(block i ∩ block j) ≤ i * ((d + 1) / d) ^ t`.
   For `d = 2 * t`, this gives a weak design with parameter `r = 2` and universe size `2 * t ^ 2`
   (`rrvWeakDesignTwo`).

3. **`𝔽₂`-linear concatenated Reed–Solomon + Hadamard list-decodable code (`rsHadamardCode`)**:
   evaluating a polynomial over `BinaryField w` of degree `< (n + w - 1) / w` and encoding each
   evaluation via `BitString.hadamardCode` yields an `𝔽₂`-linear binary code of block length
   `2 ^ (w + w)` whose list size at agreement `1 / 2 + δ` is strictly below `1 / (2 * δ ^ 2)` via
   the binary Johnson bound (`card_filter_rsHadamardCode_agree_mul_lt_one`).

4. **Trevisan–RRV `𝔽₂`-linear strong seeded extractor (`trevisanExt`, `trevisanRRVExt`)**:
   evaluating a linear list-decodable code along the blocks of a weak design yields an
   `IsLinearStrongExtractor` (`isLinearStrongExtractor_trevisan`). Instantiating with
   `rrvWeakDesignTwo` and `rsHadamardCode` gives an unconditional explicit `𝔽₂`-linear strong
   `(k, ε)`-extractor (`isLinearStrongExtractor_trevisanRRV`) with polylogarithmic seed length
   `8 * w ^ 2 = O(log²(n * m / ε))` and output length `m = Ω(k)` (specifically
   `2 * m + 3 * log₂(m / ε) + 2 ≤ k`). Achieving optimal logarithmic seed length `O(log(n / ε))`
   and completing [Li2023] Theorem 7.13 remains open in #7793.

## Main definitions

* `Cslib.AffineDisperser.Li.toeplitzLinearExt`: linear Toeplitz strong seeded extractor.
* `Cslib.AffineDisperser.Li.WeakDesign`: weak combinatorial designs for Trevisan–RRV extraction.
* `Cslib.AffineDisperser.Li.rrvWeakDesign`, `Cslib.AffineDisperser.Li.rrvWeakDesignTwo`: explicit
  computable RRV weak designs via conditional expectations.
* `Cslib.AffineDisperser.Li.rsHadamardCode`: `𝔽₂`-linear concatenated Reed–Solomon + Hadamard code
  over `BinaryField w`.
* `Cslib.AffineDisperser.Li.trevisanExt`, `Cslib.AffineDisperser.Li.trevisanRRVExt`: Trevisan–RRV
  `𝔽₂`-linear strong seeded extractor.

## Main results

* `Cslib.AffineDisperser.Li.isLinearStrongExtractor_toeplitz`: linear Toeplitz hashing is an
  `IsLinearStrongExtractor` with seed length `m + n - 1`.
* `Cslib.AffineDisperser.Li.card_filter_rsHadamardCode_agree_mul_lt_one`: binary Johnson
  list-decoding bound for `rsHadamardCode`.
* `Cslib.AffineDisperser.Li.isLinearStrongExtractor_trevisan`: strong extraction and `𝔽₂`-linearity
  of `trevisanExt` from any weak design and linear list-decodable code.
* `Cslib.AffineDisperser.Li.isLinearStrongExtractor_trevisanRRV`: unconditional explicit
  `IsLinearStrongExtractor` with seed length `8 * w ^ 2 = O(log²(n * m / ε))` and `m = Ω(k)`.

## References

* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, Section 4.6][KatzLindell2020]
* [X. Li, *Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More*][Li2023],
  ECCC TR23-023 revision 1
* [N. Nisan, A. Wigderson, *Hardness vs Randomness*][NisanWigderson1994]
* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Chapter 6 (Trevisan extractor and RRV weak designs;
  locator not verified against primary PDF)
-/

public section

namespace Cslib.AffineDisperser.Li

open Cslib Cslib.BitString Cslib.Code Cslib.Probability Cslib.Probability.PMF Finset Matrix
open scoped ENNReal

/-! ### 1. Linear Toeplitz strong seeded extractor -/

section Toeplitz

/-- **Linear Toeplitz extractor**: multiplies `x : BitString n` by the `m × n` Boolean Toeplitz
matrix with diagonals `a : BitString (m + n - 1)`. -/
@[expose] def toeplitzLinearExt (n m : ℕ) (x : BitString n) (a : BitString (m + n - 1)) :
    BitString m :=
  Matrix.toeplitz a *ᵥ x

/-- Linear Boolean Toeplitz hashing is `2⁻ᵐ`-Δ-universal (and hence two-universal). -/
theorem isTwoUniversal_toeplitzLinear (n m : ℕ) :
    IsTwoUniversal (PMF.uniformOfFintype (BitString (m + n - 1)))
      (fun a x => toeplitzLinearExt n m x a) := by
  refine (IsDeltaUniversalHash.of_map_sub_eq_uniform fun x y hxy => ?_).isTwoUniversal
  have hsub : (fun a : BitString (m + n - 1) =>
      toeplitzLinearExt n m x a - toeplitzLinearExt n m y a) =
      fun a => Matrix.toeplitz a *ᵥ (x - y) :=
    funext fun a => (Matrix.mulVec_sub (Matrix.toeplitz a) x y).symm
  rw [hsub]
  let hom : BitString (m + n - 1) →+ BitString m :=
    { toFun := fun a => Matrix.toeplitz a *ᵥ (x - y)
      map_zero' := by simp [Matrix.toeplitz_zero]
      map_add' := fun a b => by rw [Matrix.toeplitz_add, Matrix.add_mulVec] }
  exact uniformOfFintype_map_addHom hom
    (BitString.toeplitz_mulVec_surjective_bool (m := m) (sub_ne_zero.mpr hxy))

/-- **Linear Toeplitz hashing is an `𝔽₂`-linear strong seeded extractor**: with seed length
`m + n - 1`, `toeplitzLinearExt n m` extracts `m` bits with error `δ / 2` from any source of
min-entropy at least `m + 2 log₂ δ⁻¹`. -/
theorem isLinearStrongExtractor_toeplitz (n m : ℕ) {δ : ℝ} (hδ : 0 < δ) {k : ℝ}
    (hk : m + 2 * Real.logb 2 δ⁻¹ ≤ k) :
    IsLinearStrongExtractor (toeplitzLinearExt n m) k (δ / 2) := by
  refine ⟨(isTwoUniversal_toeplitzLinear n m).isStrongExtractor_of_logb_le hδ ?_, fun a x y => ?_⟩
  · rwa [BitString.logb_card]
  · exact Matrix.mulVec_add (Matrix.toeplitz a) x y

end Toeplitz

/-! ### 2. Weak combinatorial designs and explicit RRV construction -/

section WeakDesigns

/-- A **weak `(ℓ, t, m, r)`-design**: `m` subsets of `Fin ℓ`, each of size `t`, such that for every
block index `i : Fin m`, the sum of `2 ^ #(block i ∩ block j)` over earlier blocks `j < i` is at
most `r * m` (compare [Vadhan2012], Section 6.2.3, locator not verified against primary PDF). -/
structure WeakDesign (ℓ t m : ℕ) (r : ℝ) where
  /-- The `i`-th block of the weak design. -/
  block : Fin m → Finset (Fin ℓ)
  /-- Every block has `t` elements. -/
  card_block (i : Fin m) : #(block i) = t
  /-- Sum of `2 ^ |block i ∩ block j|` over `j < i` is at most `r * m`. -/
  sum_two_pow_inter_le (i : Fin m) :
    ∑ j : Fin i, (2 : ℝ) ^ #(block i ∩ block (Fin.castLE i.isLt.le j)) ≤ r * m

namespace WeakDesign

variable {ℓ t m : ℕ} {r : ℝ} {α : Type*}

/-- The bits of `z` in the `i`-th block of `D`, in increasing order of position. -/
@[expose] def restrict (D : WeakDesign ℓ t m r) (i : Fin m) (z : Fin ℓ → α) : Fin t → α :=
  z ∘ (D.block i).orderEmbOfFin (D.card_block i)

/-- Overwrite the `i`-th block of `w` with `x` in increasing order of position. -/
private def extend (D : WeakDesign ℓ t m r) (i : Fin m) (x : Fin t → α) (w : Fin ℓ → α) :
    Fin ℓ → α := fun k =>
  if h : k ∈ D.block i then x (((D.block i).orderIsoOfFin (D.card_block i)).symm ⟨k, h⟩)
  else w k

/-- Positions inside the `i`-th block of `D` that also lie in the `j`-th block. -/
private def overlap (D : WeakDesign ℓ t m r) (i j : Fin m) : Finset (Fin t) :=
  {k | (D.block i).orderEmbOfFin (D.card_block i) k ∈ D.block j}

private theorem restrict_extend (D : WeakDesign ℓ t m r) (i : Fin m) (x : Fin t → α)
    (w : Fin ℓ → α) : D.restrict i (D.extend i x w) = x := by
  ext k
  simp only [restrict, Function.comp_apply, extend, orderEmbOfFin_mem, ↓reduceDIte]
  congr 1
  rw [OrderIso.symm_apply_eq]
  exact Subtype.ext (coe_orderIsoOfFin_apply _ _ k).symm

private theorem extend_restrict (D : WeakDesign ℓ t m r) (i : Fin m) (z : Fin ℓ → α) :
    D.extend i (D.restrict i z) z = z := by
  ext k
  by_cases hk : k ∈ D.block i
  · rw [extend, dite_eq_left hk, restrict, Function.comp_apply, ← coe_orderIsoOfFin_apply,
      OrderIso.apply_symm_apply]
  · rw [extend, dite_eq_right hk]

/-- The overlap positions inside block `i` are in bijection with `block i ∩ block j`. -/
private theorem card_overlap (D : WeakDesign ℓ t m r) (i j : Fin m) :
    #(D.overlap i j) = #(D.block i ∩ D.block j) := by
  rw [← card_map ((D.block i).orderEmbOfFin (D.card_block i)).toEmbedding]
  congr 1
  ext p
  simp only [overlap, mem_map, mem_filter, mem_univ, true_and, mem_inter,
    RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨orderEmbOfFin_mem _ _ k, hk⟩
  · rintro ⟨hi, hj⟩
    obtain ⟨k, rfl⟩ : p ∈ Set.range ((D.block i).orderEmbOfFin (D.card_block i)) := by
      simpa using hi
    exact ⟨k, hj, rfl⟩

/-- With bits outside block `i` fixed to `w`, block `j` of `D.extend i x w` depends on `x` only
through `D.overlap i j`. -/
private theorem dependsOn_restrict_extend (D : WeakDesign ℓ t m r) (i j : Fin m) (w : Fin ℓ → α) :
    DependsOn (fun x : Fin t → α => D.restrict j (D.extend i x w)) (D.overlap i j) := by
  intro x y hxy
  ext k
  simp only [restrict, Function.comp_apply, extend]
  split_ifs with h
  · refine hxy _ ?_
    rw [mem_coe, overlap, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [← coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    exact orderEmbOfFin_mem _ _ k
  · rfl

/-- Swapping block `i` of `w` with `x` is an involution on `(Fin ℓ → α) × (Fin t → α)`. -/
private theorem involutive_extend_restrict (D : WeakDesign ℓ t m r) (i : Fin m) :
    Function.Involutive fun p : (Fin ℓ → α) × (Fin t → α) =>
      (D.extend i p.2 p.1, D.restrict i p.1) := by
  rintro ⟨w, x⟩
  refine Prod.ext (funext fun k => ?_) (D.restrict_extend i x w)
  by_cases hk : k ∈ D.block i
  · simp only [extend, restrict, dite_eq_left hk, Function.comp_apply]
    rw [← coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  · simp only [extend, dite_eq_right hk]

/-- Sampling a uniform seed `z : Fin ℓ → α` is equivalent to sampling `w` and block `i`
independently and overwriting block `i` of `w`. -/
private theorem uniformOfFintype_bind_eq [Fintype α] [Nonempty α] {β : Type*}
    (D : WeakDesign ℓ t m r) (i : Fin m) (F : (Fin ℓ → α) → PMF β) :
    (PMF.uniformOfFintype (Fin ℓ → α)).bind F =
      (PMF.uniformOfFintype (Fin ℓ → α)).bind fun w =>
        (PMF.uniformOfFintype (Fin t → α)).bind fun x => F (D.extend i x w) :=
  (uniformOfFintype_bind_bind_fst_equiv
    (Function.Involutive.toPerm _ (D.involutive_extend_restrict (α := α) i)) F).symm

end WeakDesign

/-! #### Explicit computable RRV weak design via conditional expectations -/

/-- Exact integer minimizer over `Fin d` (for `0 < d`). -/
private def argMinFin : (d : ℕ) → 0 < d → (Fin d → ℕ) → Fin d
  | 0, hd, _ => absurd hd (Nat.lt_irrefl 0)
  | 1, _, _ => 0
  | d + 2, _, f =>
      let prev := argMinFin (d + 1) (Nat.succ_pos d) (fun i => f i.castSucc)
      if f (Fin.last (d + 1)) < f prev.castSucc then Fin.last (d + 1) else prev.castSucc

private theorem argMinFin_le : ∀ (d : ℕ) (hd : 0 < d) (f : Fin d → ℕ) (x : Fin d),
    f (argMinFin d hd f) ≤ f x
  | 0, hd, _, _ => absurd hd (Nat.lt_irrefl 0)
  | 1, _, _, x => by
      have hx : x = 0 := Subsingleton.elim x 0
      subst hx
      exact le_rfl
  | d + 2, _, f, x => by
      dsimp only [argMinFin]
      set prev := argMinFin (d + 1) (Nat.succ_pos d) (fun i => f i.castSucc)
      have ih := argMinFin_le (d + 1) (Nat.succ_pos d) (fun i => f i.castSucc)
      refine Fin.lastCases ?_ (fun i => ?_) x
      · split_ifs with h
        · exact le_rfl
        · exact Nat.le_of_not_lt h
      · split_ifs with h
        · exact (le_of_lt h).trans (ih i)
        · exact ih i

private theorem mul_argMinFin_le_sum {d : ℕ} (hd : 0 < d) (f : Fin d → ℕ) :
    d * f (argMinFin d hd f) ≤ ∑ x : Fin d, f x := by
  calc d * f (argMinFin d hd f)
      = ∑ _x : Fin d, f (argMinFin d hd f) := by simp
    _ ≤ ∑ x : Fin d, f x := Finset.sum_le_sum fun x _ => argMinFin_le d hd f x

/-- Conditional-expectation integer potential after choosing the first `u` coordinates of a new
function `Fin t → Fin d` against a list `prev` of earlier functions. -/
private def rrvPotential {t d : ℕ} (prev : List (Fin t → Fin d)) :
    (u : ℕ) → u ≤ t → (Fin u → Fin d) → ℕ :=
  fun u hu chosen =>
    (prev.map fun g =>
      (∏ a : Fin u, if chosen a = g ⟨a.1, lt_of_lt_of_le a.2 hu⟩ then 2 * d else d) *
        (d + 1) ^ (t - u)).sum

private theorem rrvPotential_zero {t d : ℕ} (prev : List (Fin t → Fin d)) :
    rrvPotential prev 0 (Nat.zero_le t) Fin.elim0 = prev.length * (d + 1) ^ t := by
  simp [rrvPotential]

private theorem sum_rrvPotential_snoc {t d : ℕ} (prev : List (Fin t → Fin d))
    {u : ℕ} (hu : u < t) (chosen : Fin u → Fin d) :
    ∑ v : Fin d, rrvPotential prev (u + 1) hu (Fin.snoc (α := fun _ => Fin d) chosen v) =
      d * rrvPotential prev u hu.le chosen := by
  have hsingle (g : Fin t → Fin d) :
      (∑ v : Fin d,
        (∏ a : Fin (u + 1),
          if Fin.snoc (α := fun _ => Fin d) chosen v a = g ⟨a.1, lt_of_lt_of_le a.2 hu⟩
          then 2 * d else d) *
        (d + 1) ^ (t - (u + 1))) =
      d * ((∏ a : Fin u, if chosen a = g ⟨a.1, lt_of_lt_of_le a.2 hu.le⟩ then 2 * d else d) *
        (d + 1) ^ (t - u)) := by
    have hprod (v : Fin d) :
        (∏ a : Fin (u + 1),
          if Fin.snoc (α := fun _ => Fin d) chosen v a = g ⟨a.1, lt_of_lt_of_le a.2 hu⟩
          then 2 * d else d) =
        (∏ a : Fin u, if chosen a = g ⟨a.1, lt_of_lt_of_le a.2 hu.le⟩ then 2 * d else d) *
          (if v = g ⟨u, hu⟩ then 2 * d else d) := by
      rw [Fin.prod_univ_castSucc]
      simp [Fin.snoc_castSucc, Fin.snoc_last]
    simp_rw [hprod]
    have hsumv : (∑ v : Fin d, if v = g ⟨u, hu⟩ then 2 * d else d) = d * (d + 1) := by
      have hsplit : ∀ v : Fin d,
          (if v = g ⟨u, hu⟩ then 2 * d else d) = d + (if v = g ⟨u, hu⟩ then d else 0) :=
        fun v => by split_ifs <;> omega
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
      ring
    have hpow : (d + 1) ^ (t - u) = (d + 1) * (d + 1) ^ (t - (u + 1)) := by
      rw [show t - u = t - (u + 1) + 1 by omega, pow_succ']
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsumv, hpow]
    ring
  induction prev with
  | nil => simp [rrvPotential]
  | cons g gs ih =>
    simp only [rrvPotential, List.map_cons, List.sum_cons, Finset.sum_add_distrib, mul_add]
    rw [hsingle g]
    exact congrArg (_ + ·) ih

/-- Greedily choose the prefix of length `u ≤ t` minimizing `rrvPotential`. -/
private def rrvBuildPrefix {t d : ℕ} (hd : 0 < d) (prev : List (Fin t → Fin d)) :
    (u : ℕ) → u ≤ t → (Fin u → Fin d)
  | 0, _ => Fin.elim0
  | u + 1, hu =>
      let chosen := rrvBuildPrefix hd prev u (Nat.le_of_succ_le hu)
      Fin.snoc (α := fun _ => Fin d) chosen
        (argMinFin d hd fun v =>
          rrvPotential prev (u + 1) hu (Fin.snoc (α := fun _ => Fin d) chosen v))

private theorem rrvPotential_rrvBuildPrefix_le {t d : ℕ} (hd : 0 < d)
    (prev : List (Fin t → Fin d)) :
    ∀ (u : ℕ) (hu : u ≤ t),
      rrvPotential prev u hu (rrvBuildPrefix hd prev u hu) ≤ prev.length * (d + 1) ^ t
  | 0, _ => by
      simp only [rrvBuildPrefix]
      rw [rrvPotential_zero]
  | u + 1, hu => by
      have ih := rrvPotential_rrvBuildPrefix_le hd prev u (Nat.le_of_succ_le hu)
      let chosen := rrvBuildPrefix hd prev u (Nat.le_of_succ_le hu)
      have hmin := mul_argMinFin_le_sum hd
        (fun v => rrvPotential prev (u + 1) hu (Fin.snoc (α := fun _ => Fin d) chosen v))
      rw [sum_rrvPotential_snoc prev hu chosen] at hmin
      exact (Nat.le_of_mul_le_mul_left hmin hd).trans ih

/-- Build `m` functions `Fin t → Fin d` sequentially by conditional expectations. -/
private def rrvFunctions (t d : ℕ) (hd : 0 < d) : (m : ℕ) → List (Fin t → Fin d)
  | 0 => []
  | m + 1 =>
      let prev := rrvFunctions t d hd m
      prev ++ [rrvBuildPrefix hd prev t le_rfl]

private theorem length_rrvFunctions (t d : ℕ) (hd : 0 < d) (m : ℕ) :
    (rrvFunctions t d hd m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [rrvFunctions, ih]

private theorem getElem_rrvFunctions_prefix {t d : ℕ} (hd : 0 < d) :
    ∀ {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) (i : ℕ) (hi : i < m₁),
      (rrvFunctions t d hd m₂)[i]'(by rw [length_rrvFunctions]; omega) =
        (rrvFunctions t d hd m₁)[i]'(by rw [length_rrvFunctions]; omega) := by
  intro m₁ m₂ h
  induction h with
  | refl => intro _ _; rfl
  | @step k hk ih =>
      intro i hi
      simp only [rrvFunctions]
      rw [List.getElem_append_left (by rw [length_rrvFunctions]; exact lt_of_lt_of_le hi hk)]
      exact ih i hi

/-- The graph of `f : Fin t → Fin d` embedded in `Fin (t * d)`. -/
private def graphBlock {t d : ℕ} (f : Fin t → Fin d) : Finset (Fin (t * d)) :=
  Finset.univ.map ⟨fun u : Fin t => finProdFinEquiv (u, f u),
    fun _ _ h => congrArg Prod.fst (finProdFinEquiv.injective h)⟩

private theorem card_graphBlock {t d : ℕ} (f : Fin t → Fin d) : #(graphBlock f) = t := by
  rw [graphBlock, Finset.card_map, Finset.card_univ, Fintype.card_fin]

private theorem card_inter_graphBlock {t d : ℕ} (f g : Fin t → Fin d) :
    #(graphBlock f ∩ graphBlock g) = #{u : Fin t | f u = g u} := by
  have heq : graphBlock f ∩ graphBlock g =
      ({u : Fin t | f u = g u} : Finset (Fin t)).map
        ⟨fun u : Fin t => finProdFinEquiv (u, f u),
          fun _ _ h => congrArg Prod.fst (finProdFinEquiv.injective h)⟩ := by
    ext p
    simp only [graphBlock, Finset.mem_inter, Finset.mem_map, Finset.mem_univ, true_and,
      Finset.mem_filter]
    constructor
    · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
      change finProdFinEquiv (u, f u) = p at hu
      change finProdFinEquiv (v, g v) = p at hv
      have huv := finProdFinEquiv.injective (hu.trans hv.symm)
      obtain ⟨rfl, hfg⟩ := Prod.ext_iff.mp huv
      exact ⟨u, hfg, hu⟩
    · rintro ⟨u, hfg, hu⟩
      change finProdFinEquiv (u, f u) = p at hu
      exact ⟨⟨u, hu⟩, ⟨u, by change finProdFinEquiv (u, g u) = p; rw [← hfg, hu]⟩⟩
  rw [heq, Finset.card_map]

private theorem prod_two_mul_ite_eq {t d : ℕ} (f g : Fin t → Fin d) :
    (∏ a : Fin t, if f a = g a then 2 * d else d) =
      d ^ t * 2 ^ #{u : Fin t | f u = g u} := by
  have hfac (a : Fin t) :
      (if f a = g a then 2 * d else d) = d * (if f a = g a then 2 else 1) := by
    split_ifs <;> ring
  simp_rw [hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]

private theorem list_sum_eq_sum_fin {l : List ℕ} :
    l.sum = ∑ i : Fin l.length, l[i.1] := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.sum_cons, List.length_cons, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      List.getElem_cons_zero, List.getElem_cons_succ, ih]

/-- **Explicit computable RRV weak design**: for any `t`, `d > 0`, and `m`, deterministically
produces a `WeakDesign (t * d) t m (((d + 1 : ℝ) / d) ^ t)` via conditional expectations. -/
def rrvWeakDesign (t d m : ℕ) (hd : 0 < d) :
    WeakDesign (t * d) t m (((d + 1 : ℝ) / d) ^ t) where
  block i := graphBlock ((rrvFunctions t d hd m)[i.1]'(by rw [length_rrvFunctions]; exact i.2))
  card_block i := card_graphBlock _
  sum_two_pow_inter_le i := by
    set prev := rrvFunctions t d hd i.1
    have hfi : (rrvFunctions t d hd m)[i.1]'(by rw [length_rrvFunctions]; exact i.2) =
        rrvBuildPrefix hd prev t le_rfl := by
      have hpre := getElem_rrvFunctions_prefix (t := t) hd (Nat.succ_le_of_lt i.2) i.1
        (Nat.lt_succ_self i.1)
      rw [hpre]
      simp only [rrvFunctions, prev]
      rw [List.getElem_append_right (by rw [length_rrvFunctions])]
      simp [length_rrvFunctions]
    have hpot := rrvPotential_rrvBuildPrefix_le hd prev t le_rfl
    rw [length_rrvFunctions] at hpot
    have hpot_eq : rrvPotential prev t le_rfl (rrvBuildPrefix hd prev t le_rfl) =
        d ^ t * ∑ j : Fin i,
          2 ^ #(graphBlock (rrvBuildPrefix hd prev t le_rfl) ∩
            graphBlock ((rrvFunctions t d hd m)[j.1]'(by
              rw [length_rrvFunctions]; exact lt_trans j.2 i.2))) := by
      unfold rrvPotential
      simp only [Nat.sub_self, pow_zero, mul_one]
      have hlen : prev.length = i.1 := length_rrvFunctions t d hd i.1
      rw [list_sum_eq_sum_fin]
      have hmap_len : (prev.map fun g =>
          ∏ a : Fin t, if rrvBuildPrefix hd prev t le_rfl a = g a then 2 * d else d).length =
          i.1 := by rw [List.length_map, hlen]
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (finCongr hmap_len) _ _ fun j => ?_
      simp only [List.getElem_map, finCongr_apply, Fin.val_cast]
      rw [prod_two_mul_ite_eq, ← card_inter_graphBlock]
      have hj_eq : prev[j.1]'(by rw [hlen]; exact j.2.trans_eq hmap_len) =
          (rrvFunctions t d hd m)[j.1]'(by
            rw [length_rrvFunctions]; exact lt_trans (j.2.trans_eq hmap_len) i.2) :=
        (getElem_rrvFunctions_prefix hd i.2.le j.1 (j.2.trans_eq hmap_len)).symm
      rw [hj_eq]
    rw [hpot_eq] at hpot
    have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
    have hpot_r : (d : ℝ) ^ t * (∑ j : Fin i,
        (2 : ℝ) ^ #(graphBlock ((rrvFunctions t d hd m)[i.1]'(by
          rw [length_rrvFunctions]; exact i.2)) ∩
          graphBlock ((rrvFunctions t d hd m)[j.1]'(by
            rw [length_rrvFunctions]; exact lt_trans j.2 i.2)))) ≤
        (i.1 : ℝ) * ((d : ℝ) + 1) ^ t := by
      rw [hfi]
      exact_mod_cast hpot
    have hdiv : (∑ j : Fin i,
        (2 : ℝ) ^ #(graphBlock ((rrvFunctions t d hd m)[i.1]'(by
          rw [length_rrvFunctions]; exact i.2)) ∩
          graphBlock ((rrvFunctions t d hd m)[j.1]'(by
            rw [length_rrvFunctions]; exact lt_trans j.2 i.2)))) ≤
        (i.1 : ℝ) * (((d : ℝ) + 1) / d) ^ t := by
      rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
      linarith
    have him : (i.1 : ℝ) ≤ m := by exact_mod_cast i.2.le
    refine hdiv.trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left him (by positivity)

/-- Setting `d = 2 * t` (for `0 < t`) gives `((2 * t + 1) / (2 * t)) ^ t ≤ 2`, yielding an
explicit weak design with parameter `r = 2` and universe size `2 * t ^ 2`. -/
def rrvWeakDesignTwo (t m : ℕ) (ht : 0 < t) : WeakDesign (t * (2 * t)) t m 2 :=
  let D := rrvWeakDesign t (2 * t) m (by omega)
  { block := D.block
    card_block := D.card_block
    sum_two_pow_inter_le := fun i => by
      refine (D.sum_two_pow_inter_le i).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg m)
      have ht_pos : (0 : ℝ) < t := by exact_mod_cast ht
      have hbase : ((2 * t : ℕ) + 1 : ℝ) / (2 * t : ℕ) = 1 + (2 * (t : ℝ))⁻¹ := by
        push_cast; field_simp
      rw [hbase]
      have hexp : (1 + (2 * (t : ℝ))⁻¹) ^ t ≤ Real.exp ((1 : ℝ) / 2) := by
        calc (1 + (2 * (t : ℝ))⁻¹) ^ t
            ≤ (Real.exp ((2 * (t : ℝ))⁻¹)) ^ t :=
              pow_le_pow_left₀ (by positivity)
                (by linarith [Real.add_one_le_exp ((2 * (t : ℝ))⁻¹)]) t
          _ = Real.exp ((t : ℝ) * (2 * (t : ℝ))⁻¹) := by rw [← Real.exp_nat_mul]
          _ = Real.exp ((1 : ℝ) / 2) := by congr 1; field_simp
      have hexp2 : Real.exp ((1 : ℝ) / 2) ≤ 2 := by
        have hsq : Real.exp ((1 : ℝ) / 2) ^ 2 ≤ (2 : ℝ) ^ 2 := by
          rw [sq, ← Real.exp_add]
          norm_num
          linarith [Real.exp_one_lt_d9]
        exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) two_ne_zero).mp hsq
      exact hexp.trans hexp2 }

end WeakDesigns

/-! ### 3. `𝔽₂`-linear concatenated Reed–Solomon + Hadamard list-decodable code -/

section RSHadamard

/-- Number of `w`-bit chunks needed to hold an `n`-bit message: `⌈n / w⌉ = (n + w - 1) / w`. -/
@[expose] def rsDeg (n w : ℕ) : ℕ :=
  (n + w - 1) / w

private theorem rsDeg_le (n w : ℕ) (hw : 0 < w) : rsDeg n w ≤ n := by
  unfold rsDeg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.div_eq_of_lt (show w - 1 < w by omega)]
  · rw [Nat.div_le_iff_le_mul_add_pred hw]
    have hmul : 1 * (w - 1) ≤ n * (w - 1) := Nat.mul_le_mul_right _ hn
    have h1 : w * n = n * (w - 1) + n := by
      rw [mul_comm]
      conv_lhs => rw [show w = (w - 1) + 1 by omega, Nat.mul_add, mul_one]
    omega

/-- The `c`-th `w`-bit chunk of `x : BitString n`, viewed as an element of `BinaryField w`. -/
private noncomputable def rsChunk (n w : ℕ) (hw : w ≠ 0) (x : BitString n)
    (c : Fin (rsDeg n w)) : BinaryField w :=
  (BinaryField.equivBits hw).symm fun j : Fin w =>
    if h : c.1 * w + j.1 < n then x ⟨c.1 * w + j.1, h⟩ else false

private theorem rsChunk_add (n w : ℕ) (hw : w ≠ 0) (x y : BitString n)
    (c : Fin (rsDeg n w)) :
    rsChunk n w hw (x + y) c = rsChunk n w hw x c + rsChunk n w hw y c := by
  unfold rsChunk
  rw [← map_add]
  congr 1
  funext j
  by_cases h : c.1 * w + j.1 < n
  · simp [h]
  · simp [h, ← Bool.zero_eq_false]

private theorem rsChunk_injective (n w : ℕ) (hw : w ≠ 0) :
    Function.Injective (rsChunk n w hw) := by
  intro x y h
  funext i
  have hw0 : 0 < w := Nat.pos_of_ne_zero hw
  have hlt : i.1 / w < rsDeg n w := by
    unfold rsDeg
    rw [Nat.div_lt_iff_lt_mul hw0]
    have hrem : i.1 / w * w ≤ i.1 := by
      rw [mul_comm]; exact Nat.mul_div_le i.1 w
    have hdiv : n ≤ (n + w - 1) / w * w := by
      have h1 := Nat.div_add_mod (n + w - 1) w
      have h2 := Nat.mod_lt (n + w - 1) hw0
      have h3 : w * ((n + w - 1) / w) = (n + w - 1) / w * w := mul_comm _ _
      omega
    have hi : i.1 < n := i.2
    have hmul_comm : w * ((n + w - 1) / w) = (n + w - 1) / w * w := mul_comm _ _
    omega
  have hc := congrArg (BinaryField.equivBits hw) (congrFun h ⟨i.1 / w, hlt⟩)
  simp only [rsChunk, AddEquiv.apply_symm_apply] at hc
  have hj := congrFun hc ⟨i.1 % w, Nat.mod_lt i.1 hw0⟩
  have hidx : i.1 / w * w + i.1 % w = i.1 := by
    rw [mul_comm]; exact Nat.div_add_mod i.1 w
  have hbound : i.1 / w * w + i.1 % w < n := hidx.symm ▸ i.2
  simp only [hbound, ↓reduceDIte] at hj
  simpa only [Fin.ext_iff, hidx] using hj

/-- Reed–Solomon polynomial evaluation over `BinaryField w` of the `n`-bit message `x`. -/
private noncomputable def rsEval (n w : ℕ) (hw : w ≠ 0) (x : BitString n)
    (a : BinaryField w) : BinaryField w :=
  ∑ c : Fin (rsDeg n w), rsChunk n w hw x c * a ^ c.1

private theorem rsEval_add (n w : ℕ) (hw : w ≠ 0) (x y : BitString n) (a : BinaryField w) :
    rsEval n w hw (x + y) a = rsEval n w hw x a + rsEval n w hw y a := by
  simp only [rsEval, rsChunk_add, add_mul, Finset.sum_add_distrib]

/-- **Explicit `𝔽₂`-linear concatenated Reed–Solomon + Hadamard code**: encodes `x : BitString n`
as a binary word on `BitString (w + w)` by evaluating the degree-`< rsDeg n w` polynomial of `x`
over `BinaryField w` at the first `w` index bits and taking the Hadamard inner product with the
second `w` index bits. -/
noncomputable def rsHadamardCode (n w : ℕ) (hw : w ≠ 0) (x : BitString n)
    (idx : BitString (w + w)) : Bool :=
  let p := (Fin.appendEquiv w w).symm idx
  BinaryField.equivBits hw (rsEval n w hw x ((BinaryField.equivBits hw).symm p.1)) ⬝ᵥ p.2

/-- `rsHadamardCode` is `𝔽₂`-linear in the message `x`. -/
theorem rsHadamardCode_add (n w : ℕ) (hw : w ≠ 0) (x y : BitString n)
    (idx : BitString (w + w)) :
    rsHadamardCode n w hw (x + y) idx =
      rsHadamardCode n w hw x idx + rsHadamardCode n w hw y idx := by
  simp only [rsHadamardCode, rsEval_add, map_add, add_dotProduct]

/-- **Minimum relative distance of `rsHadamardCode`**: distinct messages `x ≠ y` have Hamming
distance at least `(1 / 2 - rsDeg n w / (2 * 2 ^ w)) * 2 ^ (w + w)`. -/
theorem hammingDist_rsHadamardCode_ge (n w : ℕ) (hw : w ≠ 0) {x y : BitString n} (hxy : x ≠ y) :
    ((1 / 2 : ℝ) - (rsDeg n w : ℝ) / (2 * (2 : ℝ) ^ w)) * (2 : ℝ) ^ (w + w) ≤
      (hammingDist (rsHadamardCode n w hw x) (rsHadamardCode n w hw y) : ℝ) := by
  -- Transport `hammingDist` along `BitString (w + w) ≃ BinaryField w × BitString w`.
  let e : BinaryField w × BitString w ≃ BitString (w + w) :=
    (Equiv.prodCongr (BinaryField.equivBits hw).toEquiv (Equiv.refl _)).trans (Fin.appendEquiv w w)
  have hcode (m : BitString n) (p : BinaryField w × BitString w) :
      rsHadamardCode n w hw m (e p) =
        hadamardCode (BinaryField.equivBits hw (rsEval n w hw m p.1)) p.2 := by
    simp only [rsHadamardCode, e, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
      AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, hadamardCode_apply]
    change BinaryField.equivBits hw
      (rsEval n w hw m ((BinaryField.equivBits hw).symm (BinaryField.equivBits hw p.1))) ⬝ᵥ p.2 = _
    rw [AddEquiv.symm_apply_apply]
  have hdist_eq : hammingDist (rsHadamardCode n w hw x) (rsHadamardCode n w hw y) =
      hammingDist (Code.concat (fun a : BinaryField w => hadamardCode (BinaryField.equivBits hw a))
        (rsEval n w hw x))
        (Code.concat (fun a : BinaryField w => hadamardCode (BinaryField.equivBits hw a))
          (rsEval n w hw y)) := by
    unfold hammingDist
    refine Finset.card_equiv e.symm fun idx => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change rsHadamardCode n w hw x idx ≠ rsHadamardCode n w hw y idx ↔
      hadamardCode (BinaryField.equivBits hw (rsEval n w hw x (e.symm idx).1)) (e.symm idx).2 ≠
        hadamardCode (BinaryField.equivBits hw (rsEval n w hw y (e.symm idx).1)) (e.symm idx).2
    rw [← hcode x (e.symm idx), ← hcode y (e.symm idx), e.apply_symm_apply]
  rw [hdist_eq]
  have hinner : ∀ a b : BinaryField w, a ≠ b →
      2 ^ (w - 1) ≤ hammingDist (hadamardCode (BinaryField.equivBits hw a))
        (hadamardCode (BinaryField.equivBits hw b)) := by
    intro a b hab
    have hne : BinaryField.equivBits hw a ≠ BinaryField.equivBits hw b :=
      fun h => hab ((BinaryField.equivBits hw).injective h)
    have h2 := BitString.two_mul_hammingDist_hadamardCode hne
    rw [Fintype.card_fin] at h2
    have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
      conv_lhs => rw [show w = (w - 1) + 1 by omega, pow_succ']
    omega
  have hconcat := Code.mul_hammingDist_le_hammingDist_concat hinner
    (rsEval n w hw x) (rsEval n w hw y)
  -- Bound the outer Reed–Solomon distance `hammingDist (rsEval x) (rsEval y)`.
  have houter : 2 ^ w - rsDeg n w ≤ hammingDist (rsEval n w hw x) (rsEval n w hw y) := by
    by_cases hdeg : rsDeg n w ≤ 2 ^ w
    · have heval (m : BitString n) (a : BinaryField w) :
          (((Polynomial.degreeLTEquiv (BinaryField w) (rsDeg n w)).symm (rsChunk n w hw m) :
            Polynomial (BinaryField w))).eval a = rsEval n w hw m a := by
        rw [Polynomial.eval_eq_sum_degreeLTEquiv
          ((Polynomial.degreeLTEquiv (BinaryField w) (rsDeg n w)).symm (rsChunk n w hw m)).2,
          Subtype.coe_eta, LinearEquiv.apply_symm_apply]
        rfl
      have hmem (m : BitString n) :
          rsEval n w hw m ∈ Code.reedSolomon (id : BinaryField w → BinaryField w) (rsDeg n w) := by
        refine Code.mem_reedSolomon.mpr ?_
        let P := (Polynomial.degreeLTEquiv (BinaryField w) (rsDeg n w)).symm (rsChunk n w hw m)
        exact ⟨P.1, Polynomial.mem_degreeLT.mp P.2, funext fun a => heval m a⟩
      have hne_eval : rsEval n w hw x ≠ rsEval n w hw y := by
        intro heq
        let P := (Polynomial.degreeLTEquiv (BinaryField w) (rsDeg n w)).symm (rsChunk n w hw x)
        let Q := (Polynomial.degreeLTEquiv (BinaryField w) (rsDeg n w)).symm (rsChunk n w hw y)
        have hPQ : P.1 = Q.1 := by
          refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq Finset.univ ?_ fun a _ => ?_
          · have hsub : (P.1 - Q.1).degree < rsDeg n w :=
              Polynomial.mem_degreeLT.mp (Submodule.sub_mem _ P.2 Q.2)
            refine hsub.trans_le ?_
            rw [Finset.card_univ, BinaryField.card hw]
            exact_mod_cast hdeg
          · rw [heval x a, heval y a, heq]
        apply hxy
        exact rsChunk_injective n w hw
          ((Polynomial.degreeLTEquiv (BinaryField w) (rsDeg n w)).symm.injective (Subtype.ext hPQ))
      have hmin := Code.le_minDist_reedSolomon (F := BinaryField w) Function.injective_id
        (rsDeg n w)
      have hdist := Nat.cast_le.mp (Code.le_minDist_iff.mp hmin _ (hmem x) _ (hmem y) hne_eval)
      rw [BinaryField.card hw] at hdist
      omega
    · omega
  have h2w : (2 : ℝ) ^ (w - 1) * 2 = (2 : ℝ) ^ w := by
    conv_rhs => rw [show w = (w - 1) + 1 by omega, pow_succ]
  have hsub_le : (2 : ℝ) ^ w - (rsDeg n w : ℝ) ≤ ((2 ^ w - rsDeg n w : ℕ) : ℝ) := by
    rcases le_total (rsDeg n w) (2 ^ w) with hle | hle
    · rw [Nat.cast_sub hle]; push_cast; rfl
    · rw [Nat.sub_eq_zero_of_le hle]; push_cast
      linarith [show (2 : ℝ) ^ w ≤ (rsDeg n w : ℝ) by exact_mod_cast hle]
  calc ((1 / 2 : ℝ) - (rsDeg n w : ℝ) / (2 * (2 : ℝ) ^ w)) * (2 : ℝ) ^ (w + w)
      = (2 : ℝ) ^ (w - 1) * ((2 : ℝ) ^ w - (rsDeg n w : ℝ)) := by
        rw [pow_add]
        have hpos : (2 : ℝ) ^ w ≠ 0 := by positivity
        field_simp
        nlinarith [h2w]
    _ ≤ (2 : ℝ) ^ (w - 1) * ((2 ^ w - rsDeg n w : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsub_le (by positivity)
    _ ≤ _ := by exact_mod_cast (Nat.mul_le_mul_left _ houter).trans hconcat

/-- **Binary Johnson list-decoding bound for `rsHadamardCode`**: whenever `0 ≤ δ` and
`rsDeg n w / (2 * 2 ^ w) ≤ δ ^ 2`, every received word `recv : BitString (w + w) → Bool` agrees
with strictly fewer than `1 / (2 * δ ^ 2)` codewords on at least a `1 / 2 + δ` fraction of
coordinates. -/
theorem card_filter_rsHadamardCode_agree_mul_lt_one (n w : ℕ) (hw : w ≠ 0)
    {δ : ℝ} (hδ : 0 ≤ δ) (hparam : (rsDeg n w : ℝ) / (2 * (2 : ℝ) ^ w) ≤ δ ^ 2)
    (recv : BitString (w + w) → Bool) :
    (#({x : BitString n |
        (1 / 2 + δ) * (2 : ℝ) ^ (w + w) ≤
          #{idx : BitString (w + w) | rsHadamardCode n w hw x idx = recv idx}} :
        Finset (BitString n)) : ℝ) * (2 * δ ^ 2) < 1 := by
  have hcard : (Fintype.card (BitString (w + w)) : ℝ) = (2 : ℝ) ^ (w + w) := by
    simp [Fintype.card_bool, Fintype.card_fin]
  have hcorr : ∀ x y : BitString n, x ≠ y →
      ∑ idx : BitString (w + w),
        signVal (rsHadamardCode n w hw x idx) * signVal (rsHadamardCode n w hw y idx) ≤
      2 * δ ^ 2 * Fintype.card (BitString (w + w)) := by
    intro x y hxy
    rw [BitString.sum_signVal_mul_signVal_eq_card_sub, hcard]
    have hd := hammingDist_rsHadamardCode_ge n w hw hxy
    have hmul : ((1 / 2 : ℝ) - δ ^ 2) * (2 : ℝ) ^ (w + w) ≤
        ((1 / 2 : ℝ) - (rsDeg n w : ℝ) / (2 * (2 : ℝ) ^ w)) * (2 : ℝ) ^ (w + w) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  exact Code.card_mul_two_mul_sq_lt_one (rsHadamardCode n w hw) recv hδ
    (fun x _ y _ hxy => hcorr x y hxy)
    (fun x hx => by
      rw [hcard]
      exact (Finset.mem_filter.mp hx).2)

end RSHadamard

/-! ### 4. Trevisan–RRV `𝔽₂`-linear strong seeded extractor -/

section Trevisan

/-- **Trevisan's extractor** from a weak design `D` and binary code `enc`: bit `i` of the output
evaluates `enc x` on the `i`-th block of the seed `z`. -/
@[expose] def trevisanExt {ℓ t m n : ℕ} {r : ℝ} (D : WeakDesign ℓ t m r)
    (enc : BitString n → BitString t → Bool) (x : BitString n) (z : BitString ℓ) : BitString m :=
  fun i => enc x (D.restrict i z)

/-- The `i`-th hybrid distribution in the strong-extractor Trevisan proof: pairs the seed `z` with
`trevisanExt D enc x z` on coordinates `< i` and uniform random bits on coordinates `≥ i`. -/
private noncomputable def trevHybrid {ℓ t m n : ℕ} {r : ℝ} (D : WeakDesign ℓ t m r)
    (enc : BitString n → BitString t → Bool) (X : PMF (BitString n)) (i : ℕ) :
    PMF (BitString ℓ × BitString m) :=
  X.bind fun x =>
    (PMF.uniformOfFintype (BitString ℓ)).bind fun z =>
      (PMF.uniformOfFintype (BitString m)).map fun u =>
        (z, fun j : Fin m => if j.1 < i then trevisanExt D enc x z j else u j)

private theorem trevHybrid_zero {ℓ t m n : ℕ} {r : ℝ} (D : WeakDesign ℓ t m r)
    (enc : BitString n → BitString t → Bool) (X : PMF (BitString n)) :
    trevHybrid D enc X 0 = PMF.uniformOfFintype (BitString ℓ × BitString m) := by
  simp only [trevHybrid, Nat.not_lt_zero, ↓reduceIte, PMF.bind_const]
  exact uniformOfFintype_prod (BitString ℓ) (BitString m)

private theorem trevHybrid_m {ℓ t m n : ℕ} {r : ℝ} (D : WeakDesign ℓ t m r)
    (enc : BitString n → BitString t → Bool) (X : PMF (BitString n)) :
    trevHybrid D enc X m =
      X.bind fun x => (PMF.uniformOfFintype (BitString ℓ)).map fun z =>
        (z, trevisanExt D enc x z) := by
  unfold trevHybrid
  refine congrArg (X.bind ·) (funext fun x => ?_)
  simp only [PMF.map, Function.comp_def]
  refine congrArg ((PMF.uniformOfFintype (BitString ℓ)).bind ·) (funext fun z => ?_)
  have hfun : (fun u : BitString m =>
      PMF.pure (z, fun j : Fin m => if j.1 < m then trevisanExt D enc x z j else u j)) =
      fun _ => PMF.pure (z, trevisanExt D enc x z) :=
    funext fun _ => congrArg PMF.pure (Prod.ext rfl (funext fun j => by simp [j.2]))
  rw [hfun, PMF.bind_const]

/-- Next-bit predictor for a distinguisher `T : BitString ℓ × BitString m → Bool` that observes
both the seed `z` and the output string `y`. -/
private def strongGuess {ℓ t m : ℕ} {r : ℝ} (D : WeakDesign ℓ t m r)
    (T : BitString ℓ × BitString m → Bool) (i : Fin m)
    (w : BitString ℓ) (b : Bool) (u : BitString m)
    (prefixBits : (j : Fin i) → (D.overlap i (Fin.castLE i.isLt.le j) → Bool) → Bool)
    (z_i : BitString t) : Bool :=
  let z := D.extend i z_i w
  let y : BitString m := fun j =>
    if h : j.1 < i.1 then prefixBits ⟨j.1, h⟩ (fun k => z_i k.1)
    else if j = i then b else u j
  if T (z, y) then b else !b

/-- Overlap truth tables of `enc x` for all positions `j < i` with outside seed bits fixed to `w`.
-/
private def overlapTables {ℓ t m n : ℕ} {r : ℝ} (D : WeakDesign ℓ t m r)
    (enc : BitString n → BitString t → Bool) (i : Fin m) (w : BitString ℓ) (x : BitString n) :
    (j : Fin i) → (D.overlap i (Fin.castLE i.isLt.le j) → Bool) → Bool :=
  fun j v =>
    let blk := fun k =>
      if h : k ∈ D.overlap i (Fin.castLE i.isLt.le j) then v ⟨k, h⟩ else false
    enc x (D.restrict (Fin.castLE i.isLt.le j) (D.extend i blk w))

private theorem overlapTables_eval {ℓ t m n : ℕ} {r : ℝ} (D : WeakDesign ℓ t m r)
    (enc : BitString n → BitString t → Bool) (i : Fin m) (w : BitString ℓ) (x : BitString n)
    (j : Fin i) (z_i : BitString t) :
    overlapTables D enc i w x j (fun k => z_i k.1) =
      trevisanExt D enc x (D.extend i z_i w) (Fin.castLE i.isLt.le j) := by
  simp only [overlapTables, trevisanExt]
  exact congrArg (enc x) (D.dependsOn_restrict_extend i (Fin.castLE i.isLt.le j) w
    (fun k hk => by simp [Finset.mem_coe.mp hk]))

/-- Exact Yao next-bit identity for a seed-observing distinguisher `T`: the average agreement of
`strongGuess` over `(x, w, b, u, z_i)` equals `1 / 2 + (Pr[T(H_{i+1})] - Pr[T(H_i)])`. -/
private theorem strongGuess_avg_eq {ℓ t m n : ℕ} {r : ℝ} (D : WeakDesign ℓ t m r)
    (enc : BitString n → BitString t → Bool) (X : PMF (BitString n))
    (T : BitString ℓ × BitString m → Bool) (i : Fin m) :
    ∑ w : BitString ℓ, ((PMF.uniformOfFintype (BitString ℓ)) w).toReal *
      ∑ b : Bool, ((PMF.uniformOfFintype Bool) b).toReal *
        ∑ u : BitString m, ((PMF.uniformOfFintype (BitString m)) u).toReal *
          ∑ x : BitString n, (X x).toReal *
            ((#{z_i : BitString t |
                strongGuess D T i w b u (overlapTables D enc i w x) z_i = enc x z_i} : ℝ) /
              (2 : ℝ) ^ t) =
      1 / 2 + (((trevHybrid D enc X (i.1 + 1)).map T true).toReal -
        ((trevHybrid D enc X i.1).map T true).toReal) := by
  have hcard_t : (Fintype.card (BitString t) : ℝ) = (2 : ℝ) ^ t := by
    simp [Fintype.card_bool, Fintype.card_fin]
  have hinner_b (x : BitString n) (w : BitString ℓ) (u : BitString m) (z_i : BitString t) :
      let z := D.extend i z_i w
      let y_of (c : Bool) : BitString m := fun j =>
        if j.1 < i.1 then trevisanExt D enc x z j else if j = i then c else u j
      ∑ b : Bool, ((PMF.uniformOfFintype Bool) b).toReal *
        (if strongGuess D T i w b u (overlapTables D enc i w x) z_i = enc x z_i
          then (1 : ℝ) else 0) =
      1 / 2 + (if T (z, y_of (enc x z_i)) = true then (1 : ℝ) else 0) -
        ∑ c : Bool, ((PMF.uniformOfFintype Bool) c).toReal *
          (if T (z, y_of c) = true then (1 : ℝ) else 0) := by
    dsimp only
    have hy_eq (b : Bool) :
        (fun j : Fin m =>
          if h : j.1 < i.1 then overlapTables D enc i w x ⟨j.1, h⟩ (fun k => z_i k.1)
          else if j = i then b else u j) =
        fun j : Fin m =>
          if j.1 < i.1 then trevisanExt D enc x (D.extend i z_i w) j
          else if j = i then b else u j := by
      funext j
      by_cases hj : j.1 < i.1
      · simp only [hj, ↓reduceDIte, ↓reduceIte]
        exact overlapTables_eval D enc i w x ⟨j.1, hj⟩ z_i
      · simp only [hj, ↓reduceDIte, ↓reduceIte]
    rw [Fintype.sum_bool, Fintype.sum_bool]
    simp only [strongGuess, hy_eq, PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat,
      ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    cases enc x z_i <;> cases T (D.extend i z_i w, fun j =>
      if j.1 < i.1 then trevisanExt D enc x (D.extend i z_i w) j
      else if j = i then true else u j) <;>
      cases T (D.extend i z_i w, fun j =>
        if j.1 < i.1 then trevisanExt D enc x (D.extend i z_i w) j
        else if j = i then false else u j) <;>
      norm_num
  -- Rewrite `((trevHybrid ...).map T true).toReal` using `D.uniformOfFintype_bind_eq i`.
  have hhyb_eval (k : ℕ) :
      ((trevHybrid D enc X k).map T true).toReal =
        ∑ x : BitString n, (X x).toReal *
          ∑ w : BitString ℓ, ((PMF.uniformOfFintype (BitString ℓ)) w).toReal *
            ∑ z_i : BitString t, ((PMF.uniformOfFintype (BitString t)) z_i).toReal *
              ∑ u : BitString m, ((PMF.uniformOfFintype (BitString m)) u).toReal *
                (if T (D.extend i z_i w, fun j : Fin m =>
                    if j.1 < k then trevisanExt D enc x (D.extend i z_i w) j else u j) = true
                  then (1 : ℝ) else 0) := by
    have hmap : (trevHybrid D enc X k).map T =
        X.bind fun x =>
          (PMF.uniformOfFintype (BitString ℓ)).bind fun w =>
            (PMF.uniformOfFintype (BitString t)).bind fun z_i =>
              (PMF.uniformOfFintype (BitString m)).map fun u =>
                T (D.extend i z_i w, fun j : Fin m =>
                  if j.1 < k then trevisanExt D enc x (D.extend i z_i w) j else u j) := by
      unfold trevHybrid
      rw [PMF.map_bind]
      refine congrArg (X.bind ·) (funext fun x => ?_)
      rw [PMF.map_bind, D.uniformOfFintype_bind_eq i]
      simp only [PMF.map_comp, Function.comp_def]
    have htrue (p : PMF Bool) :
        (p true).toReal = ∑ b : Bool, (p b).toReal * if b = true then (1 : ℝ) else 0 := by
      rw [Fintype.sum_bool]
      simp
    rw [hmap, htrue, sum_bind_mul]
    refine Finset.sum_congr rfl fun x _ => congrArg ((X x).toReal * ·) ?_
    rw [sum_bind_mul]
    refine Finset.sum_congr rfl fun w _ => congrArg (_ * ·) ?_
    rw [sum_bind_mul]
    refine Finset.sum_congr rfl fun z_i _ => congrArg (_ * ·) ?_
    rw [sum_map_mul]
  have hhyb_i :
      ((trevHybrid D enc X i.1).map T true).toReal =
        ∑ x : BitString n, (X x).toReal *
          ∑ w : BitString ℓ, ((PMF.uniformOfFintype (BitString ℓ)) w).toReal *
            ∑ z_i : BitString t, ((PMF.uniformOfFintype (BitString t)) z_i).toReal *
              ∑ u : BitString m, ((PMF.uniformOfFintype (BitString m)) u).toReal *
                ∑ c : Bool, ((PMF.uniformOfFintype Bool) c).toReal *
                  (if T (D.extend i z_i w, fun j : Fin m =>
                      if j.1 < i.1 then trevisanExt D enc x (D.extend i z_i w) j
                      else if j = i then c else u j) = true
                    then (1 : ℝ) else 0) := by
    rw [hhyb_eval i.1]
    refine Finset.sum_congr rfl fun x _ => congrArg _ <|
      Finset.sum_congr rfl fun w _ => congrArg _ <|
        Finset.sum_congr rfl fun z_i _ => congrArg _ ?_
    -- `(u, c) ↦ (u[i ↦ c], u i)` is a weight-preserving bijection of `BitString m × Bool`.
    let G (v : BitString m) : ℝ := if T (D.extend i z_i w, fun j : Fin m =>
      if j.1 < i.1 then trevisanExt D enc x (D.extend i z_i w) j else v j) = true then 1 else 0
    let e : BitString m × Bool ≃ BitString m × Bool :=
      ⟨fun p => (Function.update p.1 i p.2, p.1 i), fun p => (Function.update p.1 i p.2, p.1 i),
        fun p => by simp, fun p => by simp⟩
    calc ∑ u, ((PMF.uniformOfFintype (BitString m)) u).toReal * G u
        = ∑ p : BitString m × Bool, ((PMF.uniformOfFintype (BitString m)) p.1).toReal *
            (((PMF.uniformOfFintype Bool) p.2).toReal * G p.1) := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul, PMF.sum_toReal, one_mul]
      _ = ∑ p : BitString m × Bool, ((PMF.uniformOfFintype (BitString m)) p.1).toReal *
            (((PMF.uniformOfFintype Bool) p.2).toReal * G (Function.update p.1 i p.2)) :=
          (Fintype.sum_equiv e _ _ fun p => by simp [e, PMF.uniformOfFintype_apply]).symm
      _ = _ := by
          rw [Fintype.sum_prod_type]
          simp only [Finset.mul_sum, G, Function.update_apply]
  have hhyb_succ :
      ((trevHybrid D enc X (i.1 + 1)).map T true).toReal =
        ∑ x : BitString n, (X x).toReal *
          ∑ w : BitString ℓ, ((PMF.uniformOfFintype (BitString ℓ)) w).toReal *
            ∑ z_i : BitString t, ((PMF.uniformOfFintype (BitString t)) z_i).toReal *
              ∑ u : BitString m, ((PMF.uniformOfFintype (BitString m)) u).toReal *
                (if T (D.extend i z_i w, fun j : Fin m =>
                    if j.1 < i.1 then trevisanExt D enc x (D.extend i z_i w) j
                    else if j = i then enc x z_i else u j) = true
                  then (1 : ℝ) else 0) := by
    rw [hhyb_eval (i.1 + 1)]
    refine Finset.sum_congr rfl fun x _ => congrArg _ <|
      Finset.sum_congr rfl fun w _ => congrArg _ <|
        Finset.sum_congr rfl fun z_i _ => congrArg _ <|
          Finset.sum_congr rfl fun u _ => ?_
    congr 3
    refine congrArg (fun v => T (D.extend i z_i w, v)) (funext fun j => ?_)
    rcases lt_trichotomy j.1 i.1 with hlt | heq | hgt
    · simp [hlt, Nat.lt_succ_of_lt hlt]
    · obtain rfl := Fin.ext heq
      simp only [Nat.lt_succ_self, ↓reduceIte, lt_irrefl, trevisanExt, WeakDesign.restrict_extend]
    · simp [show ¬ j.1 < i.1 by omega, show ¬ j.1 < i.1 + 1 by omega,
        Fin.ne_of_gt (show i < j from hgt)]
  -- Expand the LHS sum over `z_i` and commute sums to match `hinner_b`.
  have hcard_sum (x : BitString n) (w : BitString ℓ) (b : Bool) (u : BitString m) :
      ((#{z_i : BitString t |
          strongGuess D T i w b u (overlapTables D enc i w x) z_i = enc x z_i} : ℝ) /
        (2 : ℝ) ^ t) =
      ∑ z_i : BitString t, ((PMF.uniformOfFintype (BitString t)) z_i).toReal *
        (if strongGuess D T i w b u (overlapTables D enc i w x) z_i = enc x z_i
          then (1 : ℝ) else 0) := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun z_i _ => ?_
    rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, hcard_t,
      div_eq_inv_mul]
    split_ifs <;> simp
  simp_rw [hcard_sum]
  -- Reorder sums `(w, b, u, x, z_i) -> (x, w, z_i, u, b)`.
  have hreord :
      (∑ w : BitString ℓ, ((PMF.uniformOfFintype (BitString ℓ)) w).toReal *
        ∑ b : Bool, ((PMF.uniformOfFintype Bool) b).toReal *
          ∑ u : BitString m, ((PMF.uniformOfFintype (BitString m)) u).toReal *
            ∑ x : BitString n, (X x).toReal *
              ∑ z_i : BitString t, ((PMF.uniformOfFintype (BitString t)) z_i).toReal *
                (if strongGuess D T i w b u (overlapTables D enc i w x) z_i = enc x z_i
                  then (1 : ℝ) else 0)) =
      ∑ x : BitString n, (X x).toReal *
        ∑ w : BitString ℓ, ((PMF.uniformOfFintype (BitString ℓ)) w).toReal *
          ∑ z_i : BitString t, ((PMF.uniformOfFintype (BitString t)) z_i).toReal *
            ∑ u : BitString m, ((PMF.uniformOfFintype (BitString m)) u).toReal *
              ∑ b : Bool, ((PMF.uniformOfFintype Bool) b).toReal *
                (if strongGuess D T i w b u (overlapTables D enc i w x) z_i = enc x z_i
                  then (1 : ℝ) else 0) := by
    simp only [Finset.mul_sum, ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv
      { toFun := fun p => (p.2.2.2.1, (p.1, (p.2.2.2.2, (p.2.2.1, p.2.1))))
        invFun := fun q => (q.2.1, (q.2.2.2.2, (q.2.2.2.1, (q.1, q.2.2.1))))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl } _ _ fun p => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  rw [hreord, hhyb_succ, hhyb_i]
  simp_rw [hinner_b]
  have hsum_const : ∀ (c : ℝ),
      ∑ x : BitString n, (X x).toReal *
        ∑ w : BitString ℓ, ((PMF.uniformOfFintype (BitString ℓ)) w).toReal *
          ∑ z_i : BitString t, ((PMF.uniformOfFintype (BitString t)) z_i).toReal *
            ∑ u : BitString m, ((PMF.uniformOfFintype (BitString m)) u).toReal * c = c := by
    intro c
    simp_rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hsum_const (1 / 2), add_sub_assoc]

/-- **Trevisan's strong extractor theorem (weak-design + linear list-decodable code)**:
if `D : WeakDesign ℓ t m r` (`0 < m`), `enc : BitString n → BitString t → Bool` is `𝔽₂`-linear in
`x` and every received word agrees with at most `L` codewords on at least a `1 / 2 + ε / (2 * m)`
fraction of `BitString t`, and `L * 2 ^ (r * m) * 2 ^ (-k) ≤ ε / (2 * m)`, then
`trevisanExt D enc` is an `IsLinearStrongExtractor` with parameters `(k, ε)`. -/
theorem isLinearStrongExtractor_trevisan {ℓ t m n : ℕ} {r k ε L : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hL : 0 ≤ L)
    (D : WeakDesign ℓ t m r)
    (enc : BitString n → BitString t → Bool)
    (hlin : ∀ (x y : BitString n) (u : BitString t), enc (x + y) u = enc x u + enc y u)
    (hlist : ∀ recv : BitString t → Bool,
      (#({x : BitString n |
          (1 / 2 + ε / (2 * m)) * (2 : ℝ) ^ t ≤
            #{z_i : BitString t | enc x z_i = recv z_i}} : Finset (BitString n)) : ℝ) ≤ L)
    (hk : L * (2 : ℝ) ^ (r * m) * (2 : ℝ) ^ (-k) ≤ ε / (2 * m)) :
    IsLinearStrongExtractor (trevisanExt D enc) k ε := by
  classical
  refine ⟨?_, fun z x y => funext fun i => hlin x y (D.restrict i z)⟩
  intro X hX
  by_contra hlt
  push Not at hlt
  set RealDist := X.bind fun x => (PMF.uniformOfFintype (BitString ℓ)).map fun z =>
    (z, trevisanExt D enc x z)
  set UnifDist := PMF.uniformOfFintype (BitString ℓ × BitString m)
  let T : BitString ℓ × BitString m → Bool :=
    fun p => decide ((UnifDist p).toReal < (RealDist p).toReal)
  have hdist_T : dist RealDist UnifDist =
      ((RealDist.map T) true).toReal - ((UnifDist.map T) true).toReal := by
    rw [dist_eq_sum_filter_lt, map_apply_toReal, map_apply_toReal, ← Finset.sum_sub_distrib,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : (UnifDist p).toReal < (RealDist p).toReal <;> simp [T, h]
  have htele : ((RealDist.map T) true).toReal - ((UnifDist.map T) true).toReal =
      ∑ i : Fin m, (((trevHybrid D enc X (i.1 + 1)).map T true).toReal -
        ((trevHybrid D enc X i.1).map T true).toReal) := by
    have h1 : RealDist = trevHybrid D enc X m := (trevHybrid_m D enc X).symm
    have h0 : UnifDist = trevHybrid D enc X 0 := (trevHybrid_zero D enc X).symm
    rw [h1, h0]
    rw [Fin.sum_univ_eq_sum_range (fun j => ((trevHybrid D enc X (j + 1)).map T true).toReal -
      ((trevHybrid D enc X j).map T true).toReal)]
    exact (Finset.sum_range_sub (fun j => ((trevHybrid D enc X j).map T true).toReal) m).symm
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  -- Pigeonhole over the `m` hybrid gaps to pick `i : Fin m` with gap `> ε / m`.
  obtain ⟨i, -, hi_gap⟩ : ∃ i ∈ (Finset.univ : Finset (Fin m)),
      ε / m < ((trevHybrid D enc X (i.1 + 1)).map T true).toReal -
        ((trevHybrid D enc X i.1).map T true).toReal := by
    refine Finset.exists_lt_of_sum_lt ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_div_cancel₀ _ hm_pos.ne']
    linarith
  -- By `strongGuess_avg_eq`, some `(w₀, b₀, u₀)` achieves average agreement `> 1 / 2 + ε / m`.
  have havg := strongGuess_avg_eq D enc X T i
  have havg_gt : 1 / 2 + ε / m <
      ∑ w : BitString ℓ, ((PMF.uniformOfFintype (BitString ℓ)) w).toReal *
        ∑ b : Bool, ((PMF.uniformOfFintype Bool) b).toReal *
          ∑ u : BitString m, ((PMF.uniformOfFintype (BitString m)) u).toReal *
            ∑ x : BitString n, (X x).toReal *
              ((#{z_i : BitString t |
                  strongGuess D T i w b u (overlapTables D enc i w x) z_i = enc x z_i} : ℝ) /
                (2 : ℝ) ^ t) := by linarith
  have hex_avg {α : Type} [Fintype α] (μ : PMF α) (f : α → ℝ) {c : ℝ}
      (hc : c < ∑ a, (μ a).toReal * f a) : ∃ a, c < f a := by
    obtain ⟨a, -, ha⟩ := Finset.exists_lt_of_sum_lt (f := fun a => (μ a).toReal * c)
      (g := fun a => (μ a).toReal * f a) (by rwa [← Finset.sum_mul, PMF.sum_toReal, one_mul])
    exact ⟨a, lt_of_mul_lt_mul_left ha ENNReal.toReal_nonneg⟩
  obtain ⟨w₀, hw₀⟩ := hex_avg _ _ havg_gt
  obtain ⟨b₀, hb₀⟩ := hex_avg _ _ hw₀
  obtain ⟨u₀, hu₀⟩ := hex_avg _ _ hb₀
  -- Count `x` whose agreement reaches `1 / 2 + ε / (2 * m)`.
  let agree (x : BitString n) : ℝ :=
    (#{z_i : BitString t |
        strongGuess D T i w₀ b₀ u₀ (overlapTables D enc i w₀ x) z_i = enc x z_i} : ℝ) /
      (2 : ℝ) ^ t
  let B : Finset (BitString n) := Finset.univ.filter fun x => 1 / 2 + ε / (2 * m) ≤ agree x
  have hagree_le_one (x : BitString n) : agree x ≤ 1 := by
    dsimp only [agree]
    rw [div_le_one (by positivity)]
    have hc : #{z_i : BitString t |
        strongGuess D T i w₀ b₀ u₀ (overlapTables D enc i w₀ x) z_i = enc x z_i} ≤
        Fintype.card (BitString t) := Finset.card_le_univ _
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
      (Nat.cast_le (α := ℝ)).mpr hc
  have hB_mass : ε / (2 * m) < ∑ x ∈ B, (X x).toReal := by
    have hsplit : ∑ x : BitString n, (X x).toReal * agree x ≤
        (∑ x ∈ B, (X x).toReal) + (1 / 2 + ε / (2 * m)) := by
      calc _ ≤ ∑ x : BitString n, ((if 1 / 2 + ε / (2 * m) ≤ agree x then (X x).toReal else 0) +
            (X x).toReal * (1 / 2 + ε / (2 * m))) := by
            refine Finset.sum_le_sum fun x _ => ?_
            have h0 := ENNReal.toReal_nonneg (a := X x)
            have h1 := hagree_le_one x
            have hc : (0 : ℝ) ≤ 1 / 2 + ε / (2 * m) := by positivity
            split_ifs with h
            · linarith only [mul_le_of_le_one_right h0 h1, mul_nonneg h0 hc]
            · rw [zero_add]
              exact mul_le_mul_of_nonneg_left (le_of_not_ge h) h0
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_mul,
            PMF.sum_toReal, one_mul]
    have hhalf : ε / m = ε / (2 * m) + ε / (2 * m) := by field_simp; ring
    linarith
  -- Upper bound `#B` by `L * 2 ^ (r * m)` via overlap table enumeration + list decoding.
  let TableType := (j : Fin i) → (D.overlap i (Fin.castLE i.isLt.le j) → Bool) → Bool
  have hB_sub : B ⊆ Finset.univ.biUnion fun τ : TableType =>
      Finset.univ.filter fun x : BitString n =>
        (1 / 2 + ε / (2 * m)) * (2 : ℝ) ^ t ≤
          #{z_i : BitString t | enc x z_i = strongGuess D T i w₀ b₀ u₀ τ z_i} := by
    intro x hx
    refine Finset.mem_biUnion.mpr ⟨overlapTables D enc i w₀ x, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hx' : 1 / 2 + ε / (2 * m) ≤ agree x := (Finset.mem_filter.mp hx).2
    rw [le_div_iff₀ (by positivity)] at hx'
    refine hx'.trans_eq ?_
    congr 2
    ext z_i
    simp [eq_comm]
  have hcard_table : (Fintype.card TableType : ℝ) ≤ (2 : ℝ) ^ (r * m) := by
    have hcard_nat : Fintype.card TableType =
        ∏ j : Fin i, 2 ^ (2 ^ #(D.overlap i (Fin.castLE i.isLt.le j))) := by
      simp [TableType, Fintype.card_pi, Fintype.card_bool]
    rw [hcard_nat, Nat.cast_prod]
    have hprod_eq : (∏ j : Fin i, ((2 ^ (2 ^ #(D.overlap i (Fin.castLE i.isLt.le j))) : ℕ) : ℝ)) =
        (2 : ℝ) ^ (∑ j : Fin i, (2 : ℝ) ^ #(D.overlap i (Fin.castLE i.isLt.le j))) := by
      rw [Real.rpow_sum_of_pos two_pos]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2 : ℝ), Nat.cast_pow, Nat.cast_ofNat]
    rw [hprod_eq]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    simpa only [D.card_overlap] using D.sum_two_pow_inter_le i
  have hB_card : (#B : ℝ) ≤ L * (2 : ℝ) ^ (r * m) := by
    calc (#B : ℝ)
        ≤ ∑ τ : TableType,
            (#(Finset.univ.filter fun x : BitString n =>
              (1 / 2 + ε / (2 * m)) * (2 : ℝ) ^ t ≤
                #{z_i : BitString t | enc x z_i = strongGuess D T i w₀ b₀ u₀ τ z_i}) : ℝ) := by
          exact_mod_cast (Finset.card_le_card hB_sub).trans Finset.card_biUnion_le
      _ ≤ ∑ _τ : TableType, L := Finset.sum_le_sum fun τ _ => hlist (strongGuess D T i w₀ b₀ u₀ τ)
      _ = (Fintype.card TableType : ℝ) * L := by simp
      _ ≤ L * (2 : ℝ) ^ (r * m) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hcard_table hL
  have hmass_upper : ∑ x ∈ B, (X x).toReal ≤ L * (2 : ℝ) ^ (r * m) * (2 : ℝ) ^ (-k) := by
    calc ∑ x ∈ B, (X x).toReal
        ≤ ∑ _x ∈ B, (2 : ℝ) ^ (-k) := Finset.sum_le_sum fun x _ => (le_minEntropy_iff X).mp hX x
      _ = (#B : ℝ) * (2 : ℝ) ^ (-k) := by simp
      _ ≤ L * (2 : ℝ) ^ (r * m) * (2 : ℝ) ^ (-k) :=
          mul_le_mul_of_nonneg_right hB_card (by positivity)
  linarith

/-- **Explicit Trevisan–RRV `𝔽₂`-linear strong seeded extractor**: instantiates `trevisanExt` with
`rrvWeakDesignTwo (w + w) m` (seed length `8 * w ^ 2`) and `rsHadamardCode n w`. -/
noncomputable def trevisanRRVExt (n m w : ℕ) (hw : 0 < w)
    (x : BitString n) (z : BitString ((w + w) * (2 * (w + w)))) : BitString m :=
  trevisanExt (rrvWeakDesignTwo (w + w) m (by omega)) (rsHadamardCode n w hw.ne') x z

/-- **Unconditional explicit `𝔽₂`-linear strong seeded extractor with polylogarithmic seed length**:
for every `n`, `m > 0`, `ε > 0`, and binary-field degree `w > 0` satisfying
`2 * n * m ^ 2 ≤ ε ^ 2 * 2 ^ w` (i.e., `w = O(log (n * m / ε))`, seed length
`(w + w) * (2 * (w + w)) = 8 * w ^ 2 = O(log²(n * m / ε))`), `trevisanRRVExt n m w` is an
`IsLinearStrongExtractor` extracting `m` bits with error `ε` from any source of min-entropy
`k ≥ 2 * m + 3 * log₂ (m / ε) + 2`. -/
theorem isLinearStrongExtractor_trevisanRRV {n m w : ℕ} (hm : 0 < m) (hw : 0 < w)
    {k ε : ℝ} (hε : 0 < ε)
    (hw_bound : 2 * (n : ℝ) * (m : ℝ) ^ 2 ≤ ε ^ 2 * (2 : ℝ) ^ w)
    (hk : 2 * (m : ℝ) + 3 * Real.logb 2 ((m : ℝ) / ε) + 2 ≤ k) :
    IsLinearStrongExtractor (trevisanRRVExt n m w hw) k ε := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  set δ : ℝ := ε / (2 * (m : ℝ))
  have hδ_pos : 0 < δ := by positivity
  have hparam : (rsDeg n w : ℝ) / (2 * (2 : ℝ) ^ w) ≤ δ ^ 2 := by
    have hdeg_le : (rsDeg n w : ℝ) ≤ n := by exact_mod_cast rsDeg_le n w hw
    calc (rsDeg n w : ℝ) / (2 * (2 : ℝ) ^ w)
        ≤ (n : ℝ) / (2 * (2 : ℝ) ^ w) := by gcongr
      _ ≤ (ε / (2 * (m : ℝ))) ^ 2 := by
          rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have hlist : ∀ recv : BitString (w + w) → Bool,
      (#({x : BitString n |
          (1 / 2 + δ) * (2 : ℝ) ^ (w + w) ≤
            #{z_i : BitString (w + w) | rsHadamardCode n w hw.ne' x z_i = recv z_i}} :
        Finset (BitString n)) : ℝ) ≤ 1 / (2 * δ ^ 2) := by
    intro recv
    have hlt := card_filter_rsHadamardCode_agree_mul_lt_one n w hw.ne' hδ_pos.le hparam recv
    exact (le_div_iff₀ (by positivity)).mpr hlt.le
  refine isLinearStrongExtractor_trevisan hm hε (by positivity : (0 : ℝ) ≤ 1 / (2 * δ ^ 2))
    (rrvWeakDesignTwo (w + w) m (by omega)) (rsHadamardCode n w hw.ne')
    (rsHadamardCode_add n w hw.ne') hlist ?_
  have hratio_pos : 0 < (m : ℝ) / ε := div_pos hm_pos hε
  have hpow : (2 : ℝ) ^ (2 * (m : ℝ) + 3 * Real.logb 2 ((m : ℝ) / ε) + 2) ≤ (2 : ℝ) ^ k :=
    Real.rpow_le_rpow_of_exponent_le one_le_two hk
  have hlog_pow : (2 : ℝ) ^ (3 * Real.logb 2 ((m : ℝ) / ε)) = ((m : ℝ) / ε) ^ 3 := by
    rw [mul_comm (3 : ℝ), Real.rpow_mul zero_le_two,
      Real.rpow_logb two_pos (by norm_num) hratio_pos, Real.rpow_ofNat]
  have hexpand : (2 : ℝ) ^ (2 * (m : ℝ) + 3 * Real.logb 2 ((m : ℝ) / ε) + 2) =
      4 * ((m : ℝ) / ε) ^ 3 * (2 : ℝ) ^ (2 * (m : ℝ)) := by
    rw [Real.rpow_add two_pos, Real.rpow_add two_pos, hlog_pow, Real.rpow_ofNat]
    ring
  rw [hexpand] at hpow
  have hsimp : 1 / (2 * δ ^ 2) * (2 : ℝ) ^ (2 * (m : ℝ)) * (2 : ℝ) ^ (-k) =
      (2 * (m : ℝ) ^ 2 / ε ^ 2) * (2 : ℝ) ^ (2 * (m : ℝ)) / (2 : ℝ) ^ k := by
    simp only [δ, Real.rpow_neg zero_le_two]
    field_simp
  rw [hsimp, div_le_iff₀ (by positivity)]
  have hmul : (ε / (2 * (m : ℝ))) * (4 * ((m : ℝ) / ε) ^ 3 * (2 : ℝ) ^ (2 * (m : ℝ))) =
      2 * (m : ℝ) ^ 2 / ε ^ 2 * (2 : ℝ) ^ (2 * (m : ℝ)) := by
    field_simp
    ring
  nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ ε / (2 * (m : ℝ)))]

end Trevisan

end Cslib.AffineDisperser.Li
