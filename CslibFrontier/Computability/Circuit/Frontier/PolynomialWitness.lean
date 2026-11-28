/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.FanInTwo
public import CslibFrontier.Computability.Circuit.Frontier.Nondeterministic
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Circuit.Frontier.Witness
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Combinatorics.Hoeffding
import CslibFrontier.Foundations.Combinatorics.SetFamily.ShadowDegeneracy
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases
import CslibFrontier.Tactic.LRATTauto

/-!
# Low-degree polynomial witnesses for worst-case and average-case frontier bounds

Counting over *all* Boolean functions (`Cslib.Circuits.Frontier.exists_rectangleFree_family` and
`exists_rectangleBias_family`) uses `2 ^ n` bits of description. By contrast, quadratic forms over
`𝔽₂` have succinct `O(n ^ 2)`-bit descriptions (`Cslib.Circuits.Frontier.hardForm`), but on balanced
cuts a quadratic form can be constant on `2 ^ (n / 2) × 2 ^ (n / 2)` affine cosets, capping
quadratic correlation bounds at `(1 + L₃) / 2 ≈ 2.787986 n` gates rather than `L₃ ≈ 4.575972 n`.

Raising the algebraic degree from `2` to `4` (quartic polynomials over `𝔽₂`, and more generally
degree `2 p` for any `p ≥ 2`, with `O(n ^ (2 p))` bits of description) eliminates large
monochromatic and biased rectangles across *all* cuts simultaneously, reaching the full
`L₃ ≈ 4.575972 n` frontier threshold both in the worst case (including nondeterministic circuits)
and on average (`agreement ≤ 1 / 2 + (n + 1) ^ (-β) + exp (-γ n)` for every `β < (p - 1) / 2`, so
every `β < 1 / 2` already at degree `4`).

## Proof overview

1. **Graded-weight monomial footprint.** Ordering monomials `I : Finset (Fin m)` by
   `monomialCode I = #I · 2 ^ m + ∑_{i ∈ I} 2 ^ i`, the *footprint* `Δ(A)` of a set
   `A ⊆ Bool ^ m` consists of those monomials whose evaluation column on `A` over `ZMod 2` is not
   in the span of earlier columns. By `BitString.mem_lowDegree_self`, `Δ(A)` spans `A → ZMod 2`
   (`|A| ≤ #Δ(A)`), its columns are linearly independent, and multiplication of monomials
   (`BitString.monomial_mul`) makes `Δ(A)` a down-closed set system.
2. **Hypergraph-degeneracy shadow bound** (`Finset.card_filter_card_ge_le` in
   `Foundations/Combinatorics/SetFamily/ShadowDegeneracy`). For any down-closed family `Δ`,
   `p ≥ 1` and `d : ℕ` with `p! · #Δ_p ≤ d ^ p`, minimum-degree vertex peeling on the `p`-uniform
   layer proves `#Δ_{≥ p} ≤ (#Δ_1) ^ (p - 1) · 2 ^ d` purely in `ℕ`. Hence any `A` of size at least
   `polyThreshold p s = s + s ^ (p - 1) · 2 ^ ⌈(p! s) ^ (1 / p)⌉₊` has at least `s` linearly
   independent degree-`≤ p` monomial columns, and Gaussian pivot selection extracts `s` inputs in
   `A` whose `s × s` monomial evaluation matrix is invertible over `ZMod 2`.
3. **Kronecker surjectivity on `s × s` sub-rectangles.** Across any cut `(X, Xᶜ)` of `Fin n`,
   pairing `s` pivot inputs on `X` with `s` pivot inputs on `Xᶜ` embeds `s ^ 2` cross-monomials
   `I ∪ J` of degree at most `2 p` whose evaluation map `C ↦ M₁ C M₂ᵀ` is a bijection on `s × s`
   matrices over `ZMod 2`. A uniformly random degree-`≤ 2 p` polynomial over `ZMod 2` is therefore
   *uniformly distributed* on that `s × s` sub-rectangle!
4. **Union bound and greedy rectangle peeling.** Taking `s = n + 2` gives two-sided
   `polyThreshold p (n + 2)`-rectangle-free degree-`≤ 2 p` polynomials, and flipping `f ↦ 1 - f`
   ensures density `|S| ≥ 2 ^ (n - 1)` (`exists_lowDegree_rectangleFree`). Taking
   `s = Θ(n / b ^ 2)` with Hoeffding's inequality and greedy disjoint `s × s` peeling bounds the
   bias by `b` on all rectangles above threshold `⌈polyThreshold p s / (b / 2)⌉₊ + 1`
   (`exists_lowDegree_rectangleBias`). Since `log (polyThreshold p s) = O(s ^ (1 / p)) = o(n)`
   whenever `b_n = (n + 1) ^ (-β)` with `β < (p - 1) / 2`, instantiating `FanInTwo` and
   `Nondeterministic` gives `4.57597 n` worst-case and average-case bounds at degree `4` (`p = 2`).

Low-degree witness existence in this asymptotic regime already follows from the stronger sumset
extraction theorem of [AlrabiahGoodmanMosheiffRibeiro2025], ECCC TR24-093 revision 1, Theorem 2
(p. 8): degree `2 p` suffices at entropy `O(p (n / ε ^ 2) ^ (1 / p))`. Coordinate rectangles
are special cases of sumset sources. This module supplies a direct finite-counting proof for
coordinate rectangles, the explicit `polyThreshold` estimates, and the downstream `4.57597 n`
frontier applications (via `layoutBound_switched` from [Gaspers2026]); it does not formalize the
general sumset theorem. Its polynomial families are chosen nonconstructively from
`BitString.lowDegree (ZMod 2) (Fin n) (2 * p)`, with `O(n ^ (2 p))` bits of description; no uniform
polynomial-time construction or language in `P` is established here.

## Main definitions

* `Cslib.Circuits.Frontier.polyThreshold`: the subexponential rectangle threshold
  `s + s ^ (p - 1) * 2 ^ ⌈(p! * s) ^ (1 / p)⌉₊` for degree-`2 p` polynomial witnesses.

## Main results

* `Cslib.Circuits.Frontier.exists_lowDegree_rectangleFree`,
  `Cslib.Circuits.Frontier.exists_quartic_rectangleFree`: dense rectangle-free sets computed by
  degree-`2 p` (and degree-`4` quartic) polynomials over `ZMod 2`.
* `Cslib.Circuits.Frontier.exists_lowDegree_denseRectangleFree_family`,
  `Cslib.Circuits.Frontier.exists_quartic_denseRectangleFree_family`: families of low-degree and
  quartic polynomial witnesses satisfying `DenseRectangleFree`.
* `Cslib.Circuits.Frontier.exists_quartic_switched_lt_innerSize`,
  `Cslib.Circuits.Frontier.exists_quartic_switched_lt_innerSize_nondeterministic`: degree-`4`
  quartic polynomial families requiring `(L₃ - ε) n` (`> 4.57597 n`) deterministic and
  nondeterministic fan-in-two inner gates.
* `Cslib.Circuits.Frontier.exists_lowDegree_rectangleBias`: quantitative `RectangleBias` for
  degree-`2 p` polynomials over `ZMod 2`.
* `Cslib.Circuits.Frontier.exists_lowDegree_rectangleBias_family`,
  `Cslib.Circuits.Frontier.exists_quartic_agreement_le_switched`,
  `Cslib.Circuits.Frontier.exists_quartic_agreement_le_457597_div_100000`,
  `Cslib.Circuits.Frontier.exists_quartic_abs_correlation_le_switched`,
  `Cslib.Circuits.Frontier.exists_quartic_abs_correlation_le_457597_div_100000`: degree-`4`
  quartic polynomial families achieving `agreement ≤ 1 / 2 + (n + 1) ^ (-β) + exp (-γ n)` and
  `|correlation| ≤ 2 (n + 1) ^ (-β) + 2 exp (-γ n)` for every `0 < β < 1 / 2` all the way up to
  `L₃ ≈ 4.575972 n` (`457597 / 100000 · n`) gates.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*][AlonSpencer2016]
* [O. Alrabiah, J. Goodman, J. Mosheiff, J. Ribeiro, *Low-Degree Polynomials Are Good
  Extractors*][AlrabiahGoodmanMosheiffRibeiro2025], ECCC TR24-093 revision 1, Theorem 2 (p. 8)
* [S. Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster
  Exponential Algorithms*][Gaspers2026]
* [A. A. Razborov, *Lower bounds on the size of bounded depth circuits over a complete basis with
  logical addition*][Razborov1987]
-/

public section

namespace Cslib.Circuits.Frontier

open Finset Asymptotics Real
open Filter (atTop Tendsto eventually_ge_atTop)
open scoped BigOperators

/-- The subexponential rectangle threshold for degree-`2 p` polynomial witnesses at rank `s`:
`s + s ^ (p - 1) · 2 ^ ⌈(p! · s) ^ (1 / p)⌉₊`. For `p = 2` (quartic polynomials),
`log (polyThreshold 2 s) = O(√s)`. -/
@[expose] noncomputable def polyThreshold (p s : ℕ) : ℕ :=
  s + s ^ (p - 1) * 2 ^ ⌈((p.factorial * s : ℕ) : ℝ) ^ (1 / (p : ℝ))⌉₊

private theorem factorial_mul_le_ceil_rpow_pow {p s : ℕ} (hp : 1 ≤ p) :
    p.factorial * s ≤ (⌈((p.factorial * s : ℕ) : ℝ) ^ (1 / (p : ℝ))⌉₊) ^ p := by
  set x : ℝ := ((p.factorial * s : ℕ) : ℝ)
  have hx : 0 ≤ x := Nat.cast_nonneg _
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hle : x ^ (1 / (p : ℝ)) ≤ (⌈x ^ (1 / (p : ℝ))⌉₊ : ℝ) := Nat.le_ceil _
  have hpow : (x ^ (1 / (p : ℝ))) ^ p ≤ (⌈x ^ (1 / (p : ℝ))⌉₊ : ℝ) ^ p :=
    pow_le_pow_left₀ (by positivity) hle p
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, one_div_mul_cancel hp0.ne', Real.rpow_one] at hpow
  have hcast : ((p.factorial * s : ℕ) : ℝ) ≤ ((⌈x ^ (1 / (p : ℝ))⌉₊ ^ p : ℕ) : ℝ) := by
    simpa only [x, Nat.cast_pow] using hpow
  exact Nat.cast_le.mp hcast

/-! ### Graded-weight monomial footprint and pivot extraction -/

section Footprint

private def monomialWeight {m : ℕ} (I : Finset (Fin m)) : ℕ :=
  ∑ i ∈ I, 2 ^ (i : ℕ)

private theorem monomialWeight_lt_two_pow {m : ℕ} (I : Finset (Fin m)) :
    monomialWeight I < 2 ^ m := by
  let emb : Fin m ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have hmap : monomialWeight I = ∑ r ∈ I.map emb, 2 ^ r := (Finset.sum_map I emb (2 ^ ·)).symm
  have hsub : I.map emb ⊆ Finset.range m := by
    intro r hr
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hr
    exact mem_range.mpr i.isLt
  have hle : ∑ r ∈ I.map emb, 2 ^ r ≤ ∑ r ∈ Finset.range m, 2 ^ r :=
    Finset.sum_le_sum_of_subset hsub
  rw [Nat.geomSum_eq le_rfl, Nat.div_one] at hle
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  omega

private theorem monomialWeight_injective {m : ℕ} :
    Function.Injective (monomialWeight (m := m)) := by
  induction m with
  | zero =>
    intro I J _
    ext i
    exact i.elim0
  | succ m ih =>
    let pull (S : Finset (Fin (m + 1))) : Finset (Fin m) :=
      Finset.univ.filter fun i : Fin m => i.castSucc ∈ S
    have hsplit (S : Finset (Fin (m + 1))) :
        monomialWeight S = monomialWeight (pull S) +
          (if Fin.last m ∈ S then 2 ^ m else 0) := by
      have h1 : monomialWeight S =
          ∑ i : Fin (m + 1), if i ∈ S then 2 ^ (i : ℕ) else 0 := by
        rw [monomialWeight, Finset.sum_ite_mem, Finset.univ_inter]
      have h2 : monomialWeight (pull S) =
          ∑ i : Fin m, if i.castSucc ∈ S then 2 ^ (i : ℕ) else 0 := by
        rw [monomialWeight, Finset.sum_filter]
      rw [h1, Fin.sum_univ_castSucc, h2]
      simp only [Fin.val_castSucc, Fin.val_last]
    intro I J hIJ
    have hltI := monomialWeight_lt_two_pow (pull I)
    have hltJ := monomialWeight_lt_two_pow (pull J)
    rw [hsplit I, hsplit J] at hIJ
    have hlast : Fin.last m ∈ I ↔ Fin.last m ∈ J := by
      by_cases hI : Fin.last m ∈ I <;> by_cases hJ : Fin.last m ∈ J <;>
        simp_all only [↓reduceIte] <;> omega
    have hp : pull I = pull J := ih (by
      by_cases hI : Fin.last m ∈ I
      · have hJ : Fin.last m ∈ J := hlast.mp hI
        simp only [hI, hJ, ↓reduceIte] at hIJ
        omega
      · have hJ : Fin.last m ∉ J := fun h => hI (hlast.mpr h)
        simp only [hI, hJ, ↓reduceIte] at hIJ
        omega)
    ext k
    refine Fin.lastCases hlast (fun i => ?_) k
    have hmem : i ∈ pull I ↔ i ∈ pull J := by rw [hp]
    simpa only [pull, mem_filter, Finset.mem_univ, true_and] using hmem

private def monomialCode {m : ℕ} (I : Finset (Fin m)) : ℕ :=
  #I * 2 ^ m + monomialWeight I

private theorem monomialCode_injective {m : ℕ} :
    Function.Injective (monomialCode (m := m)) := by
  intro I J h
  simp only [monomialCode] at h
  have hI := monomialWeight_lt_two_pow I
  have hJ := monomialWeight_lt_two_pow J
  have hc : #I = #J := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (#I + 1) * 2 ^ m ≤ #J * 2 ^ m := Nat.mul_le_mul_right _ hlt
      nlinarith
    · have : (#J + 1) * 2 ^ m ≤ #I * 2 ^ m := Nat.mul_le_mul_right _ hgt
      nlinarith
  rw [hc] at h
  exact monomialWeight_injective (by omega)

private theorem monomialCode_union_lt_of_lt {m : ℕ} {K J D : Finset (Fin m)}
    (hKJ : monomialCode K < monomialCode J) (hJD : Disjoint J D) :
    monomialCode (K ∪ D) < monomialCode (J ∪ D) := by
  simp only [monomialCode] at hKJ ⊢
  have hwK := monomialWeight_lt_two_pow K
  have hwJ := monomialWeight_lt_two_pow J
  have hwKD := monomialWeight_lt_two_pow (K ∪ D)
  have hcJD : #(J ∪ D) = #J + #D := card_union_of_disjoint hJD
  have hwJD : monomialWeight (J ∪ D) = monomialWeight J + monomialWeight D :=
    Finset.sum_union hJD
  have hcKD : #(K ∪ D) ≤ #K + #D := card_union_le K D
  have hwKD_le : monomialWeight (K ∪ D) ≤ monomialWeight K + monomialWeight D := by
    have hsum := Finset.sum_union_inter (s₁ := K) (s₂ := D) (f := fun i : Fin m => 2 ^ (i : ℕ))
    change monomialWeight (K ∪ D) + _ = monomialWeight K + monomialWeight D at hsum
    omega
  have hcKJ : #K ≤ #J := by
    by_contra! hgt
    have : (#J + 1) * 2 ^ m ≤ #K * 2 ^ m := Nat.mul_le_mul_right _ hgt
    nlinarith
  rcases lt_or_eq_of_le (hcKD.trans (Nat.add_le_add_right hcKJ #D)) with hlt | heq
  · have : (#(K ∪ D) + 1) * 2 ^ m ≤ #(J ∪ D) * 2 ^ m := by
      rw [hcJD]
      exact Nat.mul_le_mul_right _ hlt
    nlinarith
  · have hcK_eq : #K = #J := by omega
    have hwKJ : monomialWeight K < monomialWeight J := by nlinarith
    rw [heq, hcJD]
    nlinarith

private def monomialCol {m : ℕ} (A : Set (Fin m → Bool)) (I : Finset (Fin m)) : A → ZMod 2 :=
  fun a => BitString.monomial (ZMod 2) I a.1

private theorem monomialCol_mul {m : ℕ} (A : Set (Fin m → Bool)) (I J : Finset (Fin m)) :
    monomialCol A I * monomialCol A J = monomialCol A (I ∪ J) := by
  funext a
  change BitString.monomial (ZMod 2) I a.1 * BitString.monomial (ZMod 2) J a.1 = _
  rw [← Pi.mul_apply, BitString.monomial_mul]
  rfl

private noncomputable def footprint {m : ℕ} (A : Set (Fin m → Bool)) :
    Finset (Finset (Fin m)) :=
  open Classical in
  Finset.univ.filter fun I =>
    monomialCol A I ∉ Submodule.span (ZMod 2)
      (monomialCol A '' {K : Finset (Fin m) | monomialCode K < monomialCode I})

private theorem mem_span_footprint {m : ℕ} (A : Set (Fin m → Bool)) (I : Finset (Fin m)) :
    monomialCol A I ∈ Submodule.span (ZMod 2)
      (monomialCol A '' (footprint A : Set (Finset (Fin m)))) := by
  by_cases hI : I ∈ footprint A
  · exact Submodule.subset_span ⟨I, hI, rfl⟩
  · simp only [footprint, mem_filter, Finset.mem_univ, true_and, not_not] at hI
    refine Submodule.span_le.mpr ?_ hI
    rintro _ ⟨K, hK, rfl⟩
    exact mem_span_footprint A K
termination_by monomialCode I

private theorem footprint_downClosed {m : ℕ} {A : Set (Fin m → Bool)} {I J : Finset (Fin m)}
    (hJI : J ⊆ I) (hI : I ∈ footprint A) : J ∈ footprint A := by
  by_contra hJ
  simp only [footprint, mem_filter, Finset.mem_univ, true_and, not_not] at hJ
  set D := I \ J
  have hJD : Disjoint J D := disjoint_sdiff_self_right
  have hJunion : J ∪ D = I := union_sdiff_of_subset hJI
  let mulD : (A → ZMod 2) →ₗ[ZMod 2] (A → ZMod 2) :=
    { toFun := fun v => v * monomialCol A D
      map_add' := fun u v => add_mul u v _
      map_smul' := fun r v => by
        simp only [RingHom.id_apply]
        exact smul_mul_assoc r v _ }
  have hmem : mulD (monomialCol A J) ∈
      Submodule.map mulD (Submodule.span (ZMod 2)
        (monomialCol A '' {K : Finset (Fin m) | monomialCode K < monomialCode J})) :=
    Submodule.mem_map_of_mem hJ
  rw [Submodule.map_span] at hmem
  have hmulJ : mulD (monomialCol A J) = monomialCol A I := by
    change monomialCol A J * monomialCol A D = monomialCol A I
    rw [monomialCol_mul, hJunion]
  rw [hmulJ] at hmem
  have hle : Submodule.span (ZMod 2)
      (mulD '' (monomialCol A '' {K : Finset (Fin m) | monomialCode K < monomialCode J})) ≤
      Submodule.span (ZMod 2)
        (monomialCol A '' {K' : Finset (Fin m) | monomialCode K' < monomialCode I}) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨K, hK, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨K ∪ D, ?_, ?_⟩
    · rw [← hJunion]
      exact monomialCode_union_lt_of_lt hK hJD
    · exact (monomialCol_mul A K D).symm
  have hcontr := hle hmem
  simp only [footprint, mem_filter, Finset.mem_univ, true_and] at hI
  exact hI hcontr

private theorem sum_footprint_eq_zero {m : ℕ} (A : Set (Fin m → Bool))
    (g : footprint A → ZMod 2) (hsum : ∑ I : footprint A, g I • monomialCol A I.1 = 0) :
    g = 0 := by
  classical
  by_contra hne
  have hex : ∃ I : footprint A, g I ≠ 0 := Function.ne_iff.mp hne
  set supp : Finset (footprint A) := Finset.univ.filter fun I => g I ≠ 0
  have hsupp_ne : supp.Nonempty := by
    obtain ⟨I, hI⟩ := hex
    exact ⟨I, mem_filter.mpr ⟨Finset.mem_univ I, hI⟩⟩
  obtain ⟨I₀, hI₀, hmax⟩ := exists_max_image supp (fun I : footprint A => monomialCode I.1) hsupp_ne
  have hsum_supp : ∑ I ∈ supp, g I • monomialCol A I.1 = 0 := by
    rw [← hsum]
    exact Finset.sum_subset (subset_univ supp) fun I _ hIn => by
      simp only [supp, mem_filter, Finset.mem_univ, true_and, not_not] at hIn
      rw [hIn, zero_smul]
  have hgI₀ : g I₀ = 1 := by
    have hne := (mem_filter.mp hI₀).2
    generalize g I₀ = z at hne ⊢
    fin_cases z
    · exact absurd rfl hne
    · rfl
  have hsplit := Finset.add_sum_erase supp (fun I : footprint A => g I • monomialCol A I.1) hI₀
  rw [hsum_supp, hgI₀, one_smul] at hsplit
  have hcol_eq : monomialCol A I₀.1 = - ∑ I ∈ supp.erase I₀, g I • monomialCol A I.1 :=
    eq_neg_of_add_eq_zero_left hsplit
  have hmem_span : monomialCol A I₀.1 ∈ Submodule.span (ZMod 2)
      (monomialCol A '' {K : Finset (Fin m) | monomialCode K < monomialCode I₀.1}) := by
    rw [hcol_eq]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun I hI => Submodule.smul_mem _ _ ?_)
    obtain ⟨hneI, hIsupp⟩ := mem_erase.mp hI
    have hle_code : monomialCode I.1 ≤ monomialCode I₀.1 := hmax I hIsupp
    have hne_code : monomialCode I.1 ≠ monomialCode I₀.1 := fun heq =>
      hneI (Subtype.ext (monomialCode_injective heq))
    exact Submodule.subset_span ⟨I.1, lt_of_le_of_ne hle_code hne_code, rfl⟩
  have hfp := I₀.2
  simp only [footprint, mem_filter, Finset.mem_univ, true_and] at hfp
  exact hfp hmem_span

private theorem ncard_le_card_footprint {m : ℕ} (A : Set (Fin m → Bool)) :
    A.ncard ≤ #(footprint A) := by
  classical
  let Ψ : (footprint A → ZMod 2) → (A → ZMod 2) :=
    fun c => ∑ I : footprint A, c I • monomialCol A I.1
  have hΨ_surj : Function.Surjective Ψ := by
    let W : Submodule (ZMod 2) (A → ZMod 2) :=
      { carrier := Set.range Ψ
        zero_mem' := ⟨0, by simp [Ψ]⟩
        add_mem' := by
          rintro _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
          exact ⟨c₁ + c₂, by simp only [Ψ, Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
        smul_mem' := by
          rintro r _ ⟨c, rfl⟩
          exact ⟨r • c, by simp only [Ψ, Pi.smul_apply, smul_assoc, Finset.smul_sum]⟩ }
    have hspan_le : Submodule.span (ZMod 2)
        (monomialCol A '' (footprint A : Set (Finset (Fin m)))) ≤ W := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨I, hI, rfl⟩
      refine ⟨fun J => if J = ⟨I, hI⟩ then 1 else 0, ?_⟩
      simp only [Ψ]
      rw [Fintype.sum_eq_single (⟨I, hI⟩ : footprint A)]
      · simp
      · intro J hJ
        simp [hJ]
    intro g
    let gExt : (Fin m → Bool) → ZMod 2 := fun x => if hx : x ∈ A then g ⟨x, hx⟩ else 0
    let res : ((Fin m → Bool) → ZMod 2) →ₗ[ZMod 2] (A → ZMod 2) :=
      { toFun := fun f a => f a.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hres_g : res gExt = g := funext fun ⟨x, hx⟩ => by
      change (if hx' : x ∈ A then g ⟨x, hx'⟩ else 0) = g ⟨x, hx⟩
      simp only [hx, ↓reduceDIte]
    have hg_low := BitString.mem_lowDegree_self (R := ZMod 2) gExt
    have hmem_res : g ∈ Submodule.map res (BitString.lowDegree (ZMod 2) (Fin m)
        (Fintype.card (Fin m))) := ⟨gExt, hg_low, hres_g⟩
    rw [BitString.lowDegree, Submodule.map_span] at hmem_res
    have hres_le : Submodule.span (ZMod 2)
        (res '' (BitString.monomial (ZMod 2) '' {S | #S ≤ Fintype.card (Fin m)})) ≤ W := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨_, ⟨S, -, rfl⟩, rfl⟩
      exact hspan_le (mem_span_footprint A S)
    exact hres_le hmem_res
  have hcard := Fintype.card_le_of_surjective Ψ hΨ_surj
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_coe] at hcard
  have hA : A.ncard = Fintype.card A := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [hA]
  exact (Nat.pow_le_pow_iff_right one_lt_two).mp hcard

private theorem le_card_footprint_le_of_polyThreshold {m p s : ℕ} (hp : 1 ≤ p)
    {A : Set (Fin m → Bool)} (hA : polyThreshold p s ≤ A.ncard) :
    s ≤ #{I ∈ footprint A | #I ≤ p} := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · exact Nat.zero_le _
  by_contra! hlt
  have hlt_p : #{I ∈ footprint A | #I < p} < s :=
    (Finset.card_le_card fun I hI => by
      simp only [mem_filter] at hI ⊢
      exact ⟨hI.1, hI.2.le⟩).trans_lt hlt
  have hle_1 : #{I ∈ footprint A | #I = 1} ≤ s :=
    (Finset.card_le_card fun I hI => by
      simp only [mem_filter] at hI ⊢
      exact ⟨hI.1, hI.2 ▸ hp⟩).trans hlt.le
  have hle_p : #{I ∈ footprint A | #I = p} ≤ s :=
    (Finset.card_le_card fun I hI => by
      simp only [mem_filter] at hI ⊢
      exact ⟨hI.1, hI.2.le⟩).trans hlt.le
  let d := ⌈((p.factorial * s : ℕ) : ℝ) ^ (1 / (p : ℝ))⌉₊
  have hcap : p.factorial * #{I ∈ footprint A | #I = p} ≤ d ^ p :=
    (Nat.mul_le_mul_left _ hle_p).trans (factorial_mul_le_ceil_rpow_pow hp)
  have hge_p : #{I ∈ footprint A | p ≤ #I} ≤ s ^ (p - 1) * 2 ^ d := by
    calc #{I ∈ footprint A | p ≤ #I}
        ≤ #{I ∈ footprint A | #I = 1} ^ (p - 1) * 2 ^ d :=
          card_filter_card_ge_le hp (@footprint_downClosed m A) hcap
      _ ≤ s ^ (p - 1) * 2 ^ d := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hle_1 _)
  have hsplit : #(footprint A) =
      #{I ∈ footprint A | p ≤ #I} + #{I ∈ footprint A | #I < p} := by
    have := card_filter_add_card_filter_not (s := footprint A)
      (fun I : Finset (Fin m) => p ≤ #I)
    simpa only [not_le] using this.symm
  have hpt_eq : polyThreshold p s = s + s ^ (p - 1) * 2 ^ d := rfl
  have hcard_fp := ncard_le_card_footprint A
  omega

private theorem injective_mulVec_of_row_independent {s : ℕ} (M : Fin s → Fin s → ZMod 2)
    (hM : ∀ r : Fin s → ZMod 2, (fun j => ∑ i, r i * M i j) = 0 → r = 0) :
    Function.Injective (fun (w : Fin s → ZMod 2) (i : Fin s) => ∑ j, M i j * w j) := by
  let f (r : Fin s → ZMod 2) (j : Fin s) : ZMod 2 := ∑ i, r i * M i j
  have hf_inj : Function.Injective f := fun r₁ r₂ heq => by
    have h0 : f (r₁ - r₂) = 0 := by
      funext j
      simp only [f, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (congrFun heq j)
    exact sub_eq_zero.mp (hM _ h0)
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  intro w₁ w₂ heq
  funext k
  obtain ⟨u, hu⟩ := hf_surj (fun j => if j = k then 1 else 0)
  have hswap (w : Fin s → ZMod 2) : ∑ i, u i * ∑ j, M i j * w j = w k := by
    calc ∑ i, u i * ∑ j, M i j * w j
        = ∑ j, f u j * w j := by
          simp only [f, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, (if j = k then (1 : ZMod 2) else 0) * w j := by rw [hu]
      _ = w k := by
          rw [Fintype.sum_eq_single k (fun j hj => by simp [hj])]
          simp
  rw [← hswap w₁, ← hswap w₂]
  exact Finset.sum_congr rfl fun i _ => congrArg (u i * ·) (congrFun heq i)

private theorem exists_pivot_rows {α : Type*} {s : ℕ} (N : α → Fin s → ZMod 2)
    (hcol : ∀ c : Fin s → ZMod 2, (fun x => ∑ j, c j * N x j) = 0 → c = 0) :
    ∃ a : Fin s → α, ∀ r : Fin s → ZMod 2, (fun j => ∑ i, r i * N (a i) j) = 0 → r = 0 := by
  induction s with
  | zero =>
    exact ⟨Fin.elim0, fun r _ => funext fun i => i.elim0⟩
  | succ s ih =>
    have hcol' : ∀ c : Fin s → ZMod 2,
        (fun x => ∑ j : Fin s, c j * N x j.succ) = 0 → c = 0 := by
      intro c hc
      let c0 : Fin (s + 1) → ZMod 2 := Fin.cons (α := fun _ => ZMod 2) 0 c
      have hfull : (fun x => ∑ j : Fin (s + 1), c0 j * N x j) = 0 := by
        funext x
        rw [Fin.sum_univ_succ]
        simp only [c0, Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add]
        exact congrFun hc x
      have h0 := hcol c0 hfull
      funext j
      simpa only [c0, Fin.cons_succ, Pi.zero_apply] using congrFun h0 j.succ
    obtain ⟨a₀, ha₀⟩ := ih (fun x j => N x j.succ) hcol'
    let colMap (c : Fin s → ZMod 2) (i : Fin s) : ZMod 2 := ∑ j, c j * N (a₀ i) j.succ
    have hcol_eq : colMap = fun c i => ∑ j, N (a₀ i) j.succ * c j := by
      ext c i
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hcolB_inj : Function.Injective colMap := by
      rw [hcol_eq]
      exact injective_mulVec_of_row_independent (fun i j => N (a₀ i) j.succ) ha₀
    have hcolB_surj : Function.Surjective colMap := Finite.injective_iff_surjective.mp hcolB_inj
    obtain ⟨coeff, hcoeff⟩ := hcolB_surj fun i => N (a₀ i) 0
    let w (x : α) : ZMod 2 := N x 0 - ∑ j : Fin s, coeff j * N x j.succ
    have hw_ne : w ≠ 0 := by
      intro hw0
      let c : Fin (s + 1) → ZMod 2 := Fin.cons (α := fun _ => ZMod 2) 1 (-coeff)
      have hc0 : (fun x => ∑ j : Fin (s + 1), c j * N x j) = 0 := by
        funext x
        rw [Fin.sum_univ_succ]
        simp only [c, Fin.cons_zero, Fin.cons_succ, one_mul, Pi.neg_apply, neg_mul,
          Finset.sum_neg_distrib, ← sub_eq_add_neg]
        exact congrFun hw0 x
      have := congrFun (hcol c hc0) 0
      simp [c] at this
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : α, w x₀ ≠ 0 := Function.ne_iff.mp hw_ne
    have hw_a₀ : ∀ i : Fin s, w (a₀ i) = 0 := fun i =>
      sub_eq_zero.mpr (congrFun hcoeff i).symm
    let aNew : Fin (s + 1) → α := Fin.cons (α := fun _ => α) x₀ a₀
    refine ⟨aNew, fun r hr => ?_⟩
    have hr0_sum : r 0 * w x₀ =
        (∑ i : Fin (s + 1), r i * N (aNew i) 0) -
          ∑ j : Fin s, coeff j * ∑ i : Fin (s + 1), r i * N (aNew i) j.succ := by
      have h1 : ∑ j : Fin s, coeff j * ∑ i : Fin (s + 1), r i * N (aNew i) j.succ =
          ∑ i : Fin (s + 1), r i * ∑ j : Fin s, coeff j * N (aNew i) j.succ := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [h1, ← Finset.sum_sub_distrib, Fin.sum_univ_succ]
      simp only [aNew, Fin.cons_zero, Fin.cons_succ]
      have htail :
          ∑ i : Fin s, (r i.succ * N (a₀ i) 0 -
            r i.succ * ∑ j : Fin s, coeff j * N (a₀ i) j.succ) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [← mul_sub, show N (a₀ i) 0 - _ = w (a₀ i) from rfl, hw_a₀ i, mul_zero]
      rw [htail, add_zero, ← mul_sub]
    have hr_at (j : Fin (s + 1)) : ∑ i : Fin (s + 1), r i * N (aNew i) j = 0 :=
      congrFun hr j
    rw [hr_at 0, Finset.sum_eq_zero fun j _ => by rw [hr_at j.succ, mul_zero], sub_zero] at hr0_sum
    have hr0 : r 0 = 0 := by
      generalize r 0 = z at hr0_sum ⊢
      fin_cases z
      · rfl
      · change (1 : ZMod 2) * w x₀ = 0 at hr0_sum
        rw [one_mul] at hr0_sum
        exact absurd hr0_sum hx₀
    have htail_zero : (fun j : Fin s => ∑ i : Fin s, r i.succ * N (a₀ i) j.succ) = 0 := by
      funext j
      have := hr_at j.succ
      rw [Fin.sum_univ_succ, hr0, zero_mul, zero_add] at this
      simpa only [aNew, Fin.cons_succ, Pi.zero_apply] using this
    have hr_succ := ha₀ (fun i => r i.succ) htail_zero
    funext i
    exact Fin.cases hr0 (fun i' => congrFun hr_succ i') i

private theorem exists_pivots_of_polyThreshold {α : Type*} [Finite α]
    {p s : ℕ} (hp : 1 ≤ p) {A : Set (α → Bool)} (hA : polyThreshold p s ≤ A.ncard) :
    ∃ (a : Fin s → (α → Bool)) (J : Fin s ↪ {I : Finset α // #I ≤ p}),
      Function.Injective a ∧ (∀ i, a i ∈ A) ∧
      ∀ r : Fin s → ZMod 2,
        (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J j).1 (a i)) = 0 → r = 0 := by
  cases nonempty_fintype α
  classical
  set m := Fintype.card α
  let e : α ≃ Fin m := Fintype.equivFin α
  let tr : (α → Bool) ≃ (Fin m → Bool) := Equiv.arrowCongr e (Equiv.refl Bool)
  set A' : Set (Fin m → Bool) := tr '' A
  have hA' : polyThreshold p s ≤ A'.ncard := by
    rwa [Set.ncard_image_of_injective A tr.injective]
  have hcard := le_card_footprint_le_of_polyThreshold hp hA'
  obtain ⟨Sub, hSub_sub, hSub_card⟩ := exists_subset_card_eq hcard
  let eSub : Fin s ≃ Sub := Fintype.equivOfCardEq (by simp [hSub_card])
  let J' (j : Fin s) : Finset (Fin m) := (eSub j).1
  have hJ'_mem (j : Fin s) : J' j ∈ footprint A' ∧ #(J' j) ≤ p :=
    mem_filter.mp (hSub_sub (eSub j).2)
  have hJ'_inj : Function.Injective J' := fun j₁ j₂ h => eSub.injective (Subtype.ext h)
  have hcol : ∀ c : Fin s → ZMod 2,
      (fun a' : A' => ∑ j : Fin s, c j * monomialCol A' (J' j) a') = 0 → c = 0 := by
    intro c hc
    let g (I : footprint A') : ZMod 2 :=
      if h : ∃ j : Fin s, J' j = I.1 then c h.choose else 0
    have hsum : ∑ I : footprint A', g I • monomialCol A' I.1 = 0 := by
      funext a'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      let embJ : Fin s ↪ footprint A' :=
        ⟨fun j => ⟨J' j, (hJ'_mem j).1⟩, fun j₁ j₂ h => hJ'_inj (Subtype.mk.inj h)⟩
      have h1 : ∑ I : footprint A', g I * monomialCol A' I.1 a' =
          ∑ j : Fin s, c j * monomialCol A' (J' j) a' := by
        rw [← Finset.sum_subset (subset_univ (Finset.univ.map embJ))]
        · rw [Finset.sum_map]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hex : ∃ j' : Fin s, J' j' = (embJ j).1 := ⟨j, rfl⟩
          have hg_eq : g (embJ j) = c j := by
            simp only [g, hex, ↓reduceDIte]
            rw [hJ'_inj hex.choose_spec]
          rw [hg_eq]
          rfl
        · intro I _ hIn
          have hnex : ¬ ∃ j : Fin s, J' j = I.1 := fun ⟨j, hj⟩ =>
            hIn (Finset.mem_map.mpr ⟨j, Finset.mem_univ j, Subtype.ext hj⟩)
          have hg0_I : g I = 0 := by
            simp only [g, hnex, ↓reduceDIte]
          rw [hg0_I, zero_mul]
      rw [h1]
      exact congrFun hc a'
    have hg0 := sum_footprint_eq_zero A' g hsum
    funext j
    have hex : ∃ j' : Fin s, J' j' = J' j := ⟨j, rfl⟩
    have hgj : g ⟨J' j, (hJ'_mem j).1⟩ = 0 := congrFun hg0 ⟨J' j, (hJ'_mem j).1⟩
    have hgj_eq : g ⟨J' j, (hJ'_mem j).1⟩ = c j := by
      simp only [g, hex, ↓reduceDIte]
      rw [hJ'_inj hex.choose_spec]
    exact hgj_eq.symm.trans hgj
  obtain ⟨a'_sub, ha'_rows⟩ := exists_pivot_rows (fun (a' : A') j => monomialCol A' (J' j) a') hcol
  let a (i : Fin s) : α → Bool := tr.symm (a'_sub i).1
  have ha_mem (i : Fin s) : a i ∈ A := by
    obtain ⟨x, hx, hxeq⟩ := (a'_sub i).2
    have : a i = x := by
      simp only [a, ← hxeq, Equiv.symm_apply_apply]
    exact this ▸ hx
  let mapSet (S : Finset (Fin m)) : Finset α := S.map e.symm.toEmbedding
  let J : Fin s ↪ {I : Finset α // #I ≤ p} :=
    ⟨fun j => ⟨mapSet (J' j), by simp only [mapSet, card_map]; exact (hJ'_mem j).2⟩,
      fun j₁ j₂ h => hJ'_inj (Finset.map_injective e.symm.toEmbedding (Subtype.mk.inj h))⟩
  have hmon (i j : Fin s) :
      BitString.monomial (ZMod 2) (J j).1 (a i) = monomialCol A' (J' j) (a'_sub i) := by
    change (∏ x ∈ (J' j).map e.symm.toEmbedding, BitString.bitVal (ZMod 2) (a i x)) =
      ∏ k ∈ J' j, BitString.bitVal (ZMod 2) ((a'_sub i).1 k)
    rw [Finset.prod_map]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hk : a i (e.symm k) = (a'_sub i).1 k :=
      congrFun (tr.apply_symm_apply (a'_sub i).1) k
    rw [Equiv.coe_toEmbedding, hk]
  have hrows : ∀ r : Fin s → ZMod 2,
      (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J j).1 (a i)) = 0 → r = 0 := by
    intro r hr
    refine ha'_rows r ?_
    funext j
    simpa only [hmon] using congrFun hr j
  have ha_inj : Function.Injective a := by
    intro i₁ i₂ heq
    by_contra hne
    let r (i : Fin s) : ZMod 2 := (if i = i₁ then 1 else 0) + (if i = i₂ then 1 else 0)
    have hr_zero : (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J j).1 (a i)) = 0 := by
      funext j
      simp only [r, add_mul, Finset.sum_add_distrib, Pi.zero_apply]
      rw [Fintype.sum_eq_single i₁ (fun i hi => by simp [hi]),
        Fintype.sum_eq_single i₂ (fun i hi => by simp [hi])]
      simp only [↓reduceIte, one_mul, heq]
      exact CharTwo.add_self_eq_zero _
    have hr0 := congrFun (hrows r hr_zero) i₁
    simp only [r, ↓reduceIte, hne, add_zero, Pi.zero_apply, one_ne_zero] at hr0
  exact ⟨a, J, ha_inj, ha_mem, hrows⟩

end Footprint

/-! ### Kronecker surjectivity and exact uniformity on `s × s` sub-rectangles -/

section Kronecker

private abbrev PolyIdx (n D : ℕ) := {S : Finset (Fin n) // #S ≤ D}

private def evalPoly {n D : ℕ} (c : PolyIdx n D → ZMod 2) (x : Fin n → Bool) : ZMod 2 :=
  ∑ S : PolyIdx n D, c S * BitString.monomial (ZMod 2) S.1 x

private theorem evalPoly_mem_lowDegree {n D : ℕ} (c : PolyIdx n D → ZMod 2) :
    evalPoly c ∈ BitString.lowDegree (ZMod 2) (Fin n) D := by
  have h : evalPoly c = ∑ S : PolyIdx n D, c S • BitString.monomial (ZMod 2) S.1 := by
    funext x
    simp only [evalPoly, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact Submodule.sum_mem _ fun S _ =>
    Submodule.smul_mem _ _ (BitString.monomial_mem_lowDegree S.2)

private theorem bijective_kronecker_bilinear {s : ℕ} (M₁ M₂ : Fin s → Fin s → ZMod 2)
    (hM₁ : ∀ r : Fin s → ZMod 2, (fun j => ∑ i, r i * M₁ i j) = 0 → r = 0)
    (hM₂ : ∀ r : Fin s → ZMod 2, (fun j => ∑ i, r i * M₂ i j) = 0 → r = 0) :
    Function.Bijective (fun (C : Fin s × Fin s → ZMod 2) (q : Fin s × Fin s) =>
      ∑ j₁ : Fin s, ∑ j₂ : Fin s, M₁ q.1 j₁ * C (j₁, j₂) * M₂ q.2 j₂) := by
  have mulVec_inj : ∀ (M : Fin s → Fin s → ZMod 2),
      (∀ r : Fin s → ZMod 2, (fun j => ∑ i, r i * M i j) = 0 → r = 0) →
      ∀ w : Fin s → ZMod 2, (∀ i, ∑ j, M i j * w j = 0) → w = 0 :=
    fun M hM w hw => @injective_mulVec_of_row_independent s M hM w 0 <|
      funext fun i => by simp [hw i]
  have h1 := mulVec_inj M₁ hM₁
  have h2 := mulVec_inj M₂ hM₂
  let L (C : Fin s × Fin s → ZMod 2) (q : Fin s × Fin s) : ZMod 2 :=
    ∑ j₁ : Fin s, ∑ j₂ : Fin s, M₁ q.1 j₁ * C (j₁, j₂) * M₂ q.2 j₂
  have hL_inj : Function.Injective L := by
    intro C₁ C₂ heq
    set D := C₁ - C₂
    have hD : ∀ i k : Fin s, ∑ j₂, M₂ k j₂ * (∑ j₁, M₁ i j₁ * D (j₁, j₂)) = 0 := by
      intro i k
      have hk : L C₁ (i, k) - L C₂ (i, k) = 0 := sub_eq_zero.mpr (congrFun heq (i, k))
      calc ∑ j₂, M₂ k j₂ * ∑ j₁, M₁ i j₁ * D (j₁, j₂)
          = ∑ j₁, ∑ j₂, M₁ i j₁ * (C₁ (j₁, j₂) - C₂ (j₁, j₂)) * M₂ k j₂ := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => by
              simp only [D, Pi.sub_apply]; ring
        _ = L C₁ (i, k) - L C₂ (i, k) := by
            simp only [L, sub_mul, mul_sub, Finset.sum_sub_distrib]
        _ = 0 := hk
    have hD0 : D = 0 := by
      funext ⟨j₁, j₂⟩
      have hinner : ∀ i, ∑ j₁', M₁ i j₁' * D (j₁', j₂) = 0 := fun i =>
        congrFun (h2 (fun j₂' => ∑ j₁', M₁ i j₁' * D (j₁', j₂')) (hD i)) j₂
      exact congrFun (h1 (fun j₁' => D (j₁', j₂)) hinner) j₁
    exact sub_eq_zero.mp hD0
  exact ⟨hL_inj, Finite.injective_iff_surjective.mp hL_inj⟩

private theorem card_filter_evalPoly_mul_two_pow {n p s : ℕ} (X : Set (Fin n))
    [DecidablePred (· ∈ X)]
    (a : Fin s → (X → Bool)) (J₁ : Fin s ↪ {I : Finset X // #I ≤ p})
    (b : Fin s → (↥Xᶜ → Bool)) (J₂ : Fin s ↪ {I : Finset ↥Xᶜ // #I ≤ p})
    (ha_rows : ∀ r : Fin s → ZMod 2,
      (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J₁ j).1 (a i)) = 0 → r = 0)
    (hb_rows : ∀ r : Fin s → ZMod 2,
      (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J₂ j).1 (b i)) = 0 → r = 0)
    (P : (Fin s × Fin s → ZMod 2) → Prop) [DecidablePred P] :
    (#{c : PolyIdx n (2 * p) → ZMod 2 | P (fun q => evalPoly c
      ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm (a q.1, b q.2)))} *
        2 ^ (s * s)) =
      2 ^ Fintype.card (PolyIdx n (2 * p)) * #{T : Fin s × Fin s → ZMod 2 | P T} := by
  classical
  let eCut := Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool
  let z (q : Fin s × Fin s) : Fin n → Bool := eCut.symm (a q.1, b q.2)
  let emb₁ : X ↪ Fin n := ⟨Subtype.val, Subtype.val_injective⟩
  let emb₂ : ↥Xᶜ ↪ Fin n := ⟨Subtype.val, Subtype.val_injective⟩
  let μFun (q : Fin s × Fin s) : PolyIdx n (2 * p) :=
    ⟨(J₁ q.1).1.map emb₁ ∪ (J₂ q.2).1.map emb₂, (card_union_le _ _).trans <| by
      rw [card_map, card_map, two_mul]; exact Nat.add_le_add (J₁ q.1).2 (J₂ q.2).2⟩
  have hμ_inj : Function.Injective μFun := by
    intro q₁ q₂ h
    have hval := congrArg Subtype.val h
    have hX : ∀ q : Fin s × Fin s,
        (μFun q).1.filter (· ∈ X) = (J₁ q.1).1.map emb₁ := fun q => by
      ext i
      simp only [μFun, mem_filter, Finset.mem_union, Finset.mem_map, emb₁, emb₂]
      constructor
      · rintro ⟨(⟨x, hx, rfl⟩ | ⟨x, _, rfl⟩), hiX⟩
        · exact ⟨x, hx, rfl⟩
        · exact absurd hiX x.2
      · rintro ⟨x, hx, rfl⟩
        exact ⟨Or.inl ⟨x, hx, rfl⟩, x.2⟩
    have hXc : ∀ q : Fin s × Fin s,
        (μFun q).1.filter (· ∉ X) = (J₂ q.2).1.map emb₂ := fun q => by
      ext i
      simp only [μFun, mem_filter, Finset.mem_union, Finset.mem_map, emb₁, emb₂]
      constructor
      · rintro ⟨(⟨x, _, rfl⟩ | ⟨x, hx, rfl⟩), hni⟩
        · exact absurd x.2 hni
        · exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨Or.inr ⟨x, hx, rfl⟩, x.2⟩
    have h1 : (J₁ q₁.1).1.map emb₁ = (J₁ q₂.1).1.map emb₁ := by
      rw [← hX q₁, ← hX q₂, hval]
    have h2 : (J₂ q₁.2).1.map emb₂ = (J₂ q₂.2).1.map emb₂ := by
      rw [← hXc q₁, ← hXc q₂, hval]
    exact Prod.ext
      (J₁.injective (Subtype.ext (Finset.map_injective emb₁ h1)))
      (J₂.injective (Subtype.ext (Finset.map_injective emb₂ h2)))
  let μ : Fin s × Fin s ↪ PolyIdx n (2 * p) := ⟨μFun, hμ_inj⟩
  let M₁ (i j : Fin s) : ZMod 2 := BitString.monomial (ZMod 2) (J₁ j).1 (a i)
  let M₂ (k j : Fin s) : ZMod 2 := BitString.monomial (ZMod 2) (J₂ j).1 (b k)
  have hmon_μ (j₁ j₂ i k : Fin s) :
      BitString.monomial (ZMod 2) (μ (j₁, j₂)).1 (z (i, k)) = M₁ i j₁ * M₂ k j₂ := by
    have hmul : BitString.monomial (ZMod 2) (μ (j₁, j₂)).1 (z (i, k)) =
        BitString.monomial (ZMod 2) ((J₁ j₁).1.map emb₁) (z (i, k)) *
          BitString.monomial (ZMod 2) ((J₂ j₂).1.map emb₂) (z (i, k)) := by
      change (BitString.monomial (ZMod 2) ((J₁ j₁).1.map emb₁ ∪ (J₂ j₂).1.map emb₂)) (z (i, k)) = _
      rw [← BitString.monomial_mul]
      rfl
    have hzX (x : X) : z (i, k) x.1 = a i x :=
      congrFun (congrArg Prod.fst (eCut.apply_symm_apply (a i, b k))) x
    have hzXc (x : ↥Xᶜ) : z (i, k) x.1 = b k x :=
      congrFun (congrArg Prod.snd (eCut.apply_symm_apply (a i, b k))) x
    rw [hmul]
    congr 1
    · simp only [BitString.monomial, Finset.prod_map, emb₁, Function.Embedding.coeFn_mk, M₁]
      exact Finset.prod_congr rfl fun x _ => by rw [hzX x]
    · simp only [BitString.monomial, Finset.prod_map, emb₂, Function.Embedding.coeFn_mk, M₂]
      exact Finset.prod_congr rfl fun x _ => by rw [hzXc x]
  set Rest := {S : PolyIdx n (2 * p) // S ∉ Set.range μ}
  let eRange : Fin s × Fin s ≃ {S : PolyIdx n (2 * p) // S ∈ Set.range μ} :=
    Equiv.ofInjective μ μ.injective
  let eIdx : (Fin s × Fin s) ⊕ Rest ≃ PolyIdx n (2 * p) :=
    (Equiv.sumCongr eRange (Equiv.refl Rest)).trans (Equiv.sumCompl (· ∈ Set.range μ))
  let eCoeff : ((Fin s × Fin s → ZMod 2) × (Rest → ZMod 2)) ≃ (PolyIdx n (2 * p) → ZMod 2) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).symm.trans (eIdx.arrowCongr (Equiv.refl _))
  have heval_split (C : Fin s × Fin s → ZMod 2) (cr : Rest → ZMod 2) (q : Fin s × Fin s) :
      evalPoly (eCoeff (C, cr)) (z q) =
        (∑ S : Rest, cr S * BitString.monomial (ZMod 2) S.1.1 (z q)) +
          ∑ j₁ : Fin s, ∑ j₂ : Fin s, M₁ q.1 j₁ * C (j₁, j₂) * M₂ q.2 j₂ := by
    simp only [evalPoly]
    rw [← eIdx.sum_comp (fun S => eCoeff (C, cr) S * BitString.monomial (ZMod 2) S.1 (z q)),
      Fintype.sum_sum_type, add_comm, Fintype.sum_prod_type]
    simp only [eCoeff, Equiv.trans_apply, Equiv.arrowCongr_apply, Function.comp_apply,
      Equiv.symm_apply_apply, Equiv.refl_apply, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr]
    refine congrArg₂ (· + ·) rfl (sum_congr rfl fun j₁ _ => sum_congr rfl fun j₂ _ => ?_)
    rw [show eIdx (Sum.inl (j₁, j₂)) = μ (j₁, j₂) from rfl, hmon_μ]
    ring
  have hL_bij := bijective_kronecker_bilinear M₁ M₂ ha_rows hb_rows
  have hfiber (cr : Rest → ZMod 2) :
      ∑ C : Fin s × Fin s → ZMod 2, ite (P fun q => evalPoly (eCoeff (C, cr)) (z q)) 1 0 =
        #{T : Fin s × Fin s → ZMod 2 | P T} := by
    let R₀ (q : Fin s × Fin s) : ZMod 2 :=
      ∑ S : Rest, cr S * BitString.monomial (ZMod 2) S.1.1 (z q)
    let Φ (C : Fin s × Fin s → ZMod 2) : Fin s × Fin s → ZMod 2 :=
      R₀ + fun q => ∑ j₁ : Fin s, ∑ j₂ : Fin s, M₁ q.1 j₁ * C (j₁, j₂) * M₂ q.2 j₂
    let eΦ := Equiv.ofBijective Φ ((Equiv.addLeft R₀).bijective.comp hL_bij)
    rw [card_filter, ← eΦ.sum_comp fun T => ite (P T) 1 0]
    exact sum_congr rfl fun C _ =>
      congrArg (fun T => ite (P T) 1 0) (funext (heval_split C cr))
  have hcount_pair : #{c : PolyIdx n (2 * p) → ZMod 2 | P (fun q => evalPoly c (z q))} =
      2 ^ Fintype.card Rest * #{T : Fin s × Fin s → ZMod 2 | P T} := by
    rw [card_filter, ← eCoeff.sum_comp, Fintype.sum_prod_type_right,
      Finset.sum_congr rfl fun cr _ => hfiber cr, sum_const, card_univ, Fintype.card_fun,
      ZMod.card, smul_eq_mul]
  have hcard_idx : Fintype.card (PolyIdx n (2 * p)) = s * s + Fintype.card Rest := by
    have := Fintype.card_congr eIdx
    simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using this.symm
  rw [hcount_pair, hcard_idx, pow_add, mul_right_comm, mul_comm (2 ^ Fintype.card Rest)]

/-- Union bound over `s × s` pivot grids. Some set `bad` of coefficient vectors contains every `c`
whose table of values on a pivot grid `(X, a, b)` (independent pivot rows on both sides of the cut)
satisfies `P`, and `#bad * 2 ^ (s * s) ≤ 2 ^ (n + n s) * 2 ^ #PolyIdx * #{T | P T}`. -/
private theorem exists_pivotGrid_bad {n p s : ℕ} (P : (Fin s × Fin s → ZMod 2) → Prop)
    [DecidablePred P] :
    ∃ bad : Finset (PolyIdx n (2 * p) → ZMod 2),
      #bad * 2 ^ (s * s) ≤
        2 ^ (n + n * s) * (2 ^ Fintype.card (PolyIdx n (2 * p)) * #{T | P T}) ∧
      ∀ (c : PolyIdx n (2 * p) → ZMod 2) (X : Set (Fin n)) [DecidablePred (· ∈ X)]
        (a : Fin s → (X → Bool))
        (J₁ : Fin s ↪ {I : Finset X // #I ≤ p}) (b : Fin s → (↥Xᶜ → Bool))
        (J₂ : Fin s ↪ {I : Finset ↥Xᶜ // #I ≤ p}),
        (∀ r : Fin s → ZMod 2,
          (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J₁ j).1 (a i)) = 0 → r = 0) →
        (∀ r : Fin s → ZMod 2,
          (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J₂ j).1 (b i)) = 0 → r = 0) →
        P (fun q => evalPoly c
          ((Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool).symm (a q.1, b q.2))) →
        c ∈ bad := by
  classical
  let Good (X : Set (Fin n)) (w : Fin s → Fin n → Bool) : Prop :=
    (∃ J₁ : Fin s ↪ {I : Finset X // #I ≤ p}, ∀ r : Fin s → ZMod 2,
      (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J₁ j).1 (X.domRestrict (w i))) = 0 →
        r = 0) ∧
    (∃ J₂ : Fin s ↪ {I : Finset ↥Xᶜ // #I ≤ p}, ∀ r : Fin s → ZMod 2,
      (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J₂ j).1 (Xᶜ.domRestrict (w i))) = 0 →
        r = 0)
  let E (u : Set (Fin n) × (Fin s → Fin n → Bool)) : Finset (PolyIdx n (2 * p) → ZMod 2) :=
    {c | Good u.1 u.2 ∧ P fun q => evalPoly c
      ((Equiv.piEquivPiSubtypeProd (· ∈ u.1) fun _ => Bool).symm
        (u.1.domRestrict (u.2 q.1), u.1ᶜ.domRestrict (u.2 q.2)))}
  refine ⟨Finset.univ.biUnion E, ?_, fun c X inst a J₁ b J₂ ha hb hP => ?_⟩
  · have hE (u : Set (Fin n) × (Fin s → Fin n → Bool)) :
        #(E u) * 2 ^ (s * s) ≤ 2 ^ Fintype.card (PolyIdx n (2 * p)) * #{T | P T} := by
      by_cases hu : Good u.1 u.2
      · obtain ⟨⟨J₁, hJ₁⟩, ⟨J₂, hJ₂⟩⟩ := hu
        refine (Nat.mul_le_mul_right _ (card_le_card fun c hc => ?_)).trans_eq
          (card_filter_evalPoly_mul_two_pow u.1 _ J₁ _ J₂ hJ₁ hJ₂ P)
        simp only [E, mem_filter, Finset.mem_univ, true_and] at hc ⊢
        exact hc.2
      · simp [E, hu]
    calc #(Finset.univ.biUnion E) * 2 ^ (s * s)
        ≤ ∑ u, #(E u) * 2 ^ (s * s) := by
          rw [← sum_mul]; exact Nat.mul_le_mul_right _ card_biUnion_le
      _ ≤ ∑ _u : Set (Fin n) × (Fin s → Fin n → Bool),
            2 ^ Fintype.card (PolyIdx n (2 * p)) * #{T | P T} := sum_le_sum fun u _ => hE u
      _ = _ := by
          rw [sum_const, card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_set,
            Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
            Fintype.card_fin, ← pow_mul, ← pow_add]
  · obtain rfl : inst = fun _ => Classical.propDecidable _ := Subsingleton.elim _ _
    let eCut := Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool
    let w (i : Fin s) : Fin n → Bool := eCut.symm (a i, b i)
    have hwX (i : Fin s) : X.domRestrict (w i) = a i :=
      congrArg Prod.fst (eCut.apply_symm_apply (a i, b i))
    have hwXc (i : Fin s) : Xᶜ.domRestrict (w i) = b i :=
      congrArg Prod.snd (eCut.apply_symm_apply (a i, b i))
    refine mem_biUnion.mpr ⟨(X, w), Finset.mem_univ _, mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨⟨J₁, fun r hr => ha r (by simpa only [hwX] using hr)⟩,
        ⟨J₂, fun r hr => hb r (by simpa only [hwXc] using hr)⟩⟩, ?_⟩⟩
    simpa only [hwX, hwXc] using hP

end Kronecker

/-! ### Worst-case dense rectangle-free low-degree polynomials -/

/-- **Low-degree rectangle-free witnesses.** For every `p ≥ 1` and `n : ℕ`, there is a polynomial
`f ∈ BitString.lowDegree (ZMod 2) (Fin n) (2 * p)` of degree at most `2 p` over `ZMod 2` such that
both `{x | f x = 0}` and `{x | f x = 1}` are `polyThreshold p (n + 2)`-rectangle-free and
`2 ^ (n - 1) ≤ {x | f x = 1}.ncard`. -/
theorem exists_lowDegree_rectangleFree {p : ℕ} (hp : 1 ≤ p) (n : ℕ) :
    ∃ f ∈ BitString.lowDegree (ZMod 2) (Fin n) (2 * p),
      (∀ v : ZMod 2, RectangleFree {x | f x = v} (polyThreshold p (n + 2))) ∧
      2 ^ (n - 1) ≤ {x | f x = 1}.ncard := by
  classical
  set s := n + 2
  set K := polyThreshold p s
  set M := Fintype.card (PolyIdx n (2 * p))
  let isConst (T : Fin s × Fin s → ZMod 2) : Prop :=
    (∀ q, T q = 0) ∨ (∀ q, T q = 1)
  have hcard_const : #{T : Fin s × Fin s → ZMod 2 | isConst T} ≤ 2 := by
    have hsub : ({T : Fin s × Fin s → ZMod 2 | isConst T} : Finset _) ⊆
        {(fun _ => (0 : ZMod 2)), (fun _ => (1 : ZMod 2))} := by
      intro T hT
      have hTc : isConst T := (mem_filter.mp hT).2
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact hTc.imp (fun h => funext h) (fun h => funext h)
    exact (Finset.card_le_card hsub).trans (card_insert_le _ _)
  obtain ⟨bad, hbad_card, hbad_mem⟩ := exists_pivotGrid_bad (n := n) (p := p) isConst
  have hcount : #bad < 2 ^ M := by
    have hsum := hbad_card.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left (2 ^ M) hcard_const))
    have hss : s * s = n + n * s + (n + 4) := by simp only [s]; ring
    rw [hss, pow_add] at hsum
    -- Cancel `2 ^ (n + n * s)`: `16 * #bad ≤ #bad * 2 ^ (n + 4) ≤ 2 ^ M * 2`.
    have h2 : #bad * 2 ^ (n + 4) ≤ 2 ^ M * 2 :=
      Nat.le_of_mul_le_mul_left (by linarith only [hsum]) (by positivity : 0 < 2 ^ (n + n * s))
    have h16 := Nat.mul_le_mul_left #bad
      (show 16 ≤ 2 ^ (n + 4) from pow_add 2 n 4 ▸ Nat.le_mul_of_pos_left _ (by positivity))
    have : 0 < 2 ^ M := by positivity
    omega
  have hlt_univ : #bad < #(Finset.univ : Finset (PolyIdx n (2 * p) → ZMod 2)) := by
    simpa only [card_univ, Fintype.card_fun, ZMod.card] using hcount
  obtain ⟨c, -, hc_bad⟩ := exists_mem_notMem_of_card_lt_card hlt_univ
  have hc_good : ∀ v : ZMod 2, RectangleFree {x | evalPoly c x = v} K := by
    by_contra hnc
    push Not at hnc
    obtain ⟨v, hv⟩ := hnc
    rw [rectangleFree_iff] at hv
    push Not at hv
    obtain ⟨X, A, B, hAB, hA, hB⟩ := hv
    obtain ⟨a, J₁, -, ha_mem, ha_rows⟩ := exists_pivots_of_polyThreshold hp hA
    obtain ⟨b, J₂, -, hb_mem, hb_rows⟩ := exists_pivots_of_polyThreshold hp hB
    let eCut := Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool
    have hmem_rect (q : Fin s × Fin s) : eCut.symm (a q.1, b q.2) ∈ rectangle X A B := by
      have h₁ : X.domRestrict (eCut.symm (a q.1, b q.2)) = a q.1 :=
        congrArg Prod.fst (eCut.apply_symm_apply _)
      have h₂ : Xᶜ.domRestrict (eCut.symm (a q.1, b q.2)) = b q.2 :=
        congrArg Prod.snd (eCut.apply_symm_apply _)
      rw [mem_rectangle, h₁, h₂]
      exact ⟨ha_mem q.1, hb_mem q.2⟩
    refine hc_bad (hbad_mem c X a J₁ b J₂ ha_rows hb_rows ?_)
    fin_cases v
    · exact Or.inl fun q => hAB (hmem_rect q)
    · exact Or.inr fun q => hAB (hmem_rect q)
  set f₀ := evalPoly c
  have hf₀_mem : f₀ ∈ BitString.lowDegree (ZMod 2) (Fin n) (2 * p) := evalPoly_mem_lowDegree c
  by_cases hdense : 2 ^ (n - 1) ≤ {x | f₀ x = 1}.ncard
  · exact ⟨f₀, hf₀_mem, hc_good, hdense⟩
  · refine ⟨1 - f₀, BitString.one_sub_mem_lowDegree hf₀_mem, fun v => ?_, ?_⟩
    · have hset : {x : Fin n → Bool | (1 - f₀) x = v} = {x | f₀ x = 1 - v} := by
        ext x
        simp only [Pi.sub_apply, Pi.one_apply, Set.mem_ofPred_eq]
        rw [sub_eq_iff_eq_add, eq_sub_iff_add_eq, add_comm, eq_comm]
      rw [hset]
      exact hc_good (1 - v)
    · have hset : {x : Fin n → Bool | (1 - f₀) x = 1} = {x | f₀ x = 1}ᶜ := by
        ext x
        simp only [Pi.sub_apply, Pi.one_apply, Set.mem_ofPred_eq, Set.mem_compl_iff, sub_eq_self]
        generalize f₀ x = z
        fin_cases z
        · exact ⟨fun _ h => (by cases h), fun _ => rfl⟩
        · exact ⟨fun h _ => (by cases h), fun h => absurd rfl h⟩
      rw [hset]
      have htot := Set.ncard_add_ncard_compl {x : Fin n → Bool | f₀ x = 1}
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at htot
      rcases n with _ | n'
      · simp at htot; omega
      · have hd : n' + 1 - 1 = n' := Nat.add_sub_cancel n' 1
        rw [hd] at hdense ⊢
        rw [pow_succ] at htot
        omega

/-- **Quartic rectangle-free witnesses (`deg ≤ 4`).** For every `n : ℕ`, there is a quartic
polynomial `f ∈ BitString.lowDegree (ZMod 2) (Fin n) 4` over `ZMod 2` such that both
`{x | f x = 0}` and `{x | f x = 1}` are `polyThreshold 2 (n + 2)`-rectangle-free and
`2 ^ (n - 1) ≤ {x | f x = 1}.ncard`. -/
theorem exists_quartic_rectangleFree (n : ℕ) :
    ∃ f ∈ BitString.lowDegree (ZMod 2) (Fin n) 4,
      (∀ v : ZMod 2, RectangleFree {x | f x = v} (polyThreshold 2 (n + 2))) ∧
      2 ^ (n - 1) ≤ {x | f x = 1}.ncard := by
  simpa using exists_lowDegree_rectangleFree (p := 2) (by decide) n

/-! ### Quantitative `RectangleBias` for low-degree polynomials -/

private theorem abs_inter_sub_half_le {α : Type*} [Finite α] (R S : Set α) :
    |((R ∩ S).ncard : ℝ) - R.ncard / 2| ≤ R.ncard / 2 := by
  have h1 : ((R ∩ S).ncard : ℝ) ≤ R.ncard := by
    exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite R)
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (R ∩ S).ncard]

/-- The bias of `S` on a disjoint union is at most the sum of the biases on the two parts. -/
private theorem abs_inter_union_sub_half_le {α : Type*} [Finite α] {R₁ R₂ : Set α}
    (h : Disjoint R₁ R₂) (S : Set α) :
    |(((R₁ ∪ R₂) ∩ S).ncard : ℝ) - (R₁ ∪ R₂).ncard / 2| ≤
      |((R₁ ∩ S).ncard : ℝ) - R₁.ncard / 2| + |((R₂ ∩ S).ncard : ℝ) - R₂.ncard / 2| := by
  rw [Set.union_inter_distrib_right,
    Set.ncard_union_eq (h.mono Set.inter_subset_left Set.inter_subset_left), Set.ncard_union_eq h]
  push_cast
  convert abs_add_le (((R₁ ∩ S).ncard : ℝ) - R₁.ncard / 2) (((R₂ ∩ S).ncard : ℝ) - R₂.ncard / 2)
    using 2
  ring

/-- Abstract 2D greedy `s × s` rectangle peeling: if every `s × s` pivot sub-rectangle has bias at
most `b₀`, and sides of size at least `K₀` contain `s`-element pivot subsets, then every rectangle
with both sides of size at least `K` (where `K₀ ≤ b₀ * K`) has bias at most `2 b₀`. Parameterizing
over abstract `s, K₀, K` avoids unfolding `Nat.ceil` or `polyThreshold` during elaboration. -/
private theorem rectangleBias_of_pivot_blocks {n p s K₀ K : ℕ} {b₀ : ℝ}
    (hs1 : 1 ≤ s) (hb₀ : 0 < b₀) (hK₀_le : (K₀ : ℝ) ≤ b₀ * K)
    {S : Set (Fin n → Bool)}
    (hpiv_X : ∀ (X : Set (Fin n)) {A : Set (X → Bool)}, K₀ ≤ A.ncard →
      ∃ (a : Fin s → (X → Bool)) (J₁ : Fin s ↪ {I : Finset X // #I ≤ p}),
        Function.Injective a ∧ (∀ i, a i ∈ A) ∧
        ∀ r : Fin s → ZMod 2,
          (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J₁ j).1 (a i)) = 0 → r = 0)
    (hpiv_Xc : ∀ (X : Set (Fin n)) {B : Set (↥Xᶜ → Bool)}, K₀ ≤ B.ncard →
      ∃ (b' : Fin s → (↥Xᶜ → Bool)) (J₂ : Fin s ↪ {I : Finset ↥Xᶜ // #I ≤ p}),
        Function.Injective b' ∧ (∀ i, b' i ∈ B) ∧
        ∀ r : Fin s → ZMod 2,
          (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J₂ j).1 (b' i)) = 0 → r = 0)
    (hblock : ∀ (X : Set (Fin n)) (a : Fin s → (X → Bool))
        (J₁ : Fin s ↪ {I : Finset X // #I ≤ p})
        (b' : Fin s → (↥Xᶜ → Bool)) (J₂ : Fin s ↪ {I : Finset ↥Xᶜ // #I ≤ p}),
      Function.Injective a → Function.Injective b' →
      (∀ r : Fin s → ZMod 2,
        (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J₁ j).1 (a i)) = 0 → r = 0) →
      (∀ r : Fin s → ZMod 2,
        (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J₂ j).1 (b' i)) = 0 → r = 0) →
      |((rectangle X (Set.range a) (Set.range b') ∩ S).ncard : ℝ) - (s * s : ℕ) / 2| ≤
        b₀ * (s * s : ℕ)) :
    RectangleBias S K (2 * b₀) := by
  intro X A B hA hB
  have bias_good_left : ∀ (a : Fin s → (X → Bool)) (J₁ : Fin s ↪ {I : Finset X // #I ≤ p}),
      Function.Injective a →
      (∀ r : Fin s → ZMod 2,
        (fun j => ∑ i, r i * BitString.monomial (ZMod 2) (J₁ j).1 (a i)) = 0 → r = 0) →
      ∀ (B' : Set (↥Xᶜ → Bool)),
        |((rectangle X (Set.range a) B' ∩ S).ncard : ℝ) -
            (rectangle X (Set.range a) B').ncard / 2| ≤
          b₀ * (s * B'.ncard : ℕ) + (s * K₀ : ℕ) / 2 := by
    intro a J₁ ha_inj ha_rows B'
    have hA₀_card : (Set.range a).ncard = s := by
      rw [Set.ncard_range_of_injective ha_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
    induction B' using (_root_.measure Set.ncard).wf.induction with
    | h B' ih =>
      by_cases hB' : K₀ ≤ B'.ncard
      · obtain ⟨b', J₂, hb_inj, hb_mem, hb_rows⟩ := hpiv_Xc X hB'
        set B₀ := Set.range b'
        have hB₀_sub : B₀ ⊆ B' := Set.range_subset_iff.mpr hb_mem
        have hB₀_card : B₀.ncard = s := by
          rw [Set.ncard_range_of_injective hb_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
        have hcard_sdiff : (B' \ B₀).ncard + s = B'.ncard :=
          hB₀_card ▸ Set.ncard_sdiff_add_ncard_of_subset hB₀_sub
        have hrest := ih (B' \ B₀) ((Nat.lt_add_of_pos_right hs1).trans_eq hcard_sdiff)
        have hblk := hblock X a J₁ b' J₂ ha_inj hb_inj ha_rows hb_rows
        set R₁ := rectangle X (Set.range a) B₀
        set R₂ := rectangle X (Set.range a) (B' \ B₀)
        have hdisj : Disjoint R₁ R₂ :=
          Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₂.2.2 hx₁.2
        have hunion : rectangle X (Set.range a) B' = R₁ ∪ R₂ := by
          ext x
          simp only [R₁, R₂, mem_rectangle, Set.mem_union, Set.mem_sdiff]
          lrat_tauto [@hB₀_sub (Xᶜ.domRestrict x)]
        have hn₁ : R₁.ncard = s * s := by rw [ncard_rectangle, hA₀_card, hB₀_card]
        rw [hunion]
        refine (abs_inter_union_sub_half_le hdisj S).trans ?_
        rw [hn₁]
        have hlin_b : b₀ * (s * s : ℕ) + b₀ * (s * (B' \ B₀).ncard : ℕ) =
            b₀ * (s * B'.ncard : ℕ) := by
          rw [← hcard_sdiff]; push_cast; ring
        linarith
      · have hR_card : (rectangle X (Set.range a) B').ncard = s * B'.ncard := by
          rw [ncard_rectangle, hA₀_card]
        have hle : ((rectangle X (Set.range a) B').ncard : ℝ) ≤ (s * K₀ : ℕ) := by
          rw [hR_card]
          exact_mod_cast Nat.mul_le_mul_left s (by omega)
        linarith [abs_inter_sub_half_le (rectangle X (Set.range a) B') S,
          mul_nonneg hb₀.le (Nat.cast_nonneg (α := ℝ) (s * B'.ncard))]
  have bias_any : ∀ (A' : Set (X → Bool)) (B' : Set (↥Xᶜ → Bool)),
      |((rectangle X A' B' ∩ S).ncard : ℝ) - (rectangle X A' B').ncard / 2| ≤
        b₀ * (A'.ncard * B'.ncard : ℕ) +
          ((A'.ncard * K₀ : ℕ) : ℝ) / 2 + ((K₀ * B'.ncard : ℕ) : ℝ) / 2 := by
    intro A' B'
    induction A' using (_root_.measure Set.ncard).wf.induction with
    | h A' ih =>
      by_cases hA' : K₀ ≤ A'.ncard
      · obtain ⟨a, J₁, ha_inj, ha_mem, ha_rows⟩ := hpiv_X X hA'
        set A₀ := Set.range a
        have hA₀_sub : A₀ ⊆ A' := Set.range_subset_iff.mpr ha_mem
        have hA₀_card : A₀.ncard = s := by
          rw [Set.ncard_range_of_injective ha_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
        have hcard_sdiff : (A' \ A₀).ncard + s = A'.ncard :=
          hA₀_card ▸ Set.ncard_sdiff_add_ncard_of_subset hA₀_sub
        have hgood := bias_good_left a J₁ ha_inj ha_rows B'
        have hrest := ih (A' \ A₀) ((Nat.lt_add_of_pos_right hs1).trans_eq hcard_sdiff)
        set R₁ := rectangle X A₀ B'
        set R₂ := rectangle X (A' \ A₀) B'
        have hdisj : Disjoint R₁ R₂ :=
          Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₂.1.2 hx₁.1
        have hunion : rectangle X A' B' = R₁ ∪ R₂ := by
          ext x
          simp only [R₁, R₂, mem_rectangle, Set.mem_union, Set.mem_sdiff]
          lrat_tauto [@hA₀_sub (X.domRestrict x)]
        rw [hunion]
        refine (abs_inter_union_sub_half_le hdisj S).trans ?_
        have hlin₁_b : b₀ * (s * B'.ncard : ℕ) + b₀ * ((A' \ A₀).ncard * B'.ncard : ℕ) =
            b₀ * (A'.ncard * B'.ncard : ℕ) := by
          rw [← hcard_sdiff]; push_cast; ring
        have hlin₂ : ((s * K₀ : ℕ) : ℝ) + ((A' \ A₀).ncard * K₀ : ℕ) = (A'.ncard * K₀ : ℕ) := by
          rw [← hcard_sdiff]; push_cast; ring
        linarith
      · have hle : ((rectangle X A' B').ncard : ℝ) ≤ (K₀ * B'.ncard : ℕ) := by
          rw [ncard_rectangle]
          exact_mod_cast Nat.mul_le_mul_right B'.ncard (by omega)
        linarith [abs_inter_sub_half_le (rectangle X A' B') S,
          mul_nonneg hb₀.le (Nat.cast_nonneg (α := ℝ) (A'.ncard * B'.ncard)),
          Nat.cast_nonneg (α := ℝ) (A'.ncard * K₀)]
  have hK₀A : (K₀ : ℝ) ≤ b₀ * A.ncard :=
    hK₀_le.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hA) hb₀.le)
  have hK₀B : (K₀ : ℝ) ≤ b₀ * B.ncard :=
    hK₀_le.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hB) hb₀.le)
  have hrem₁ : ((A.ncard * K₀ : ℕ) : ℝ) ≤ b₀ * (A.ncard * B.ncard : ℕ) := by
    push_cast
    have := mul_le_mul_of_nonneg_left hK₀B (Nat.cast_nonneg (α := ℝ) A.ncard)
    linarith
  have hrem₂ : ((K₀ * B.ncard : ℕ) : ℝ) ≤ b₀ * (A.ncard * B.ncard : ℕ) := by
    push_cast
    have := mul_le_mul_of_nonneg_right hK₀A (Nat.cast_nonneg (α := ℝ) B.ncard)
    linarith
  have hmain := bias_any A B
  rw [ncard_rectangle] at hmain ⊢
  linarith

/-- **Quantitative `RectangleBias` for low-degree polynomials.** For every `p ≥ 1`, `n : ℕ`, and
`b > 0`, let `s = ⌈(n + 2) / (b ^ 2 / 2)⌉₊ + 2` and
`K = ⌈polyThreshold p s / (b / 2)⌉₊ + 1`. Then some polynomial
`f ∈ BitString.lowDegree (ZMod 2) (Fin n) (2 * p)` satisfies `RectangleBias {x | f x = 1} K b`. -/
theorem exists_lowDegree_rectangleBias {p : ℕ} (hp : 1 ≤ p) (n : ℕ) {b : ℝ} (hb : 0 < b) :
    let s := ⌈((n : ℝ) + 2) / (b ^ 2 / 2)⌉₊ + 2
    let K := ⌈(polyThreshold p s : ℝ) / (b / 2)⌉₊ + 1
    ∃ f ∈ BitString.lowDegree (ZMod 2) (Fin n) (2 * p),
      RectangleBias {x | f x = 1} K b := by
  classical
  intro s K
  rcases le_or_gt (1 / 2) b with hb_half | hb_half
  · refine ⟨0, Submodule.zero_mem _, fun X A B hA hB => ?_⟩
    exact (rectangleBias_one_half _ K X A B hA hB).trans
      (mul_le_mul_of_nonneg_right hb_half (Nat.cast_nonneg _))
  set b₀ := b / 2
  have hb₀ : 0 < b₀ := by positivity
  have hs1 : 1 ≤ s := by simp only [s]; omega
  have hsb₀ : ((n : ℝ) + 2) ≤ 2 * b₀ ^ 2 * s := by
    have hdiv_pos : 0 < b ^ 2 / 2 := by positivity
    have h2b₀ : 2 * b₀ ^ 2 = b ^ 2 / 2 := by simp only [b₀]; ring
    have hceil : ((n : ℝ) + 2) / (b ^ 2 / 2) ≤ (s : ℝ) := by
      have h1 := Nat.le_ceil (((n : ℝ) + 2) / (b ^ 2 / 2))
      have h2 : (s : ℝ) = (⌈((n : ℝ) + 2) / (b ^ 2 / 2)⌉₊ : ℝ) + 2 := by
        simp only [s]; push_cast; rfl
      linarith
    rw [h2b₀, mul_comm]
    exact (div_le_iff₀ hdiv_pos).mp hceil
  have hs_gt_n : n + 2 ≤ s := by
    have hb2_lt : b ^ 2 / 2 < 1 := by nlinarith
    have hdiv_ge : (n : ℝ) + 2 ≤ ((n : ℝ) + 2) / (b ^ 2 / 2) :=
      le_div_self (by positivity) (by positivity) hb2_lt.le
    have hceil := hdiv_ge.trans (Nat.le_ceil _)
    have hn_le : n + 2 ≤ ⌈((n : ℝ) + 2) / (b ^ 2 / 2)⌉₊ := by
      have hcast : ((n + 2 : ℕ) : ℝ) ≤ (⌈((n : ℝ) + 2) / (b ^ 2 / 2)⌉₊ : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using hceil
      exact Nat.cast_le.mp hcast
    simp only [s]; omega
  set M := Fintype.card (PolyIdx n (2 * p))
  let isBiased (T : Fin s × Fin s → ZMod 2) : Prop :=
    b₀ * (s * s : ℕ) < |(#{q : Fin s × Fin s | T q = 1} : ℝ) - (s * s : ℕ) / 2|
  have hcard_biased : (#{T : Fin s × Fin s → ZMod 2 | isBiased T} : ℝ) ≤
      2 * 2 ^ (s * s) * exp (-(2 * b₀ ^ 2 * (s * s : ℕ))) := by
    let eBool : ZMod 2 ≃ Bool :=
      { toFun := fun z => decide (z = 1)
        invFun := fun b' => if b' then 1 else 0
        left_inv := fun z => by fin_cases z <;> rfl
        right_inv := fun b' => by cases b' <;> rfl }
    let eTab : (Fin s × Fin s → ZMod 2) ≃ (Fin s × Fin s → Bool) :=
      Equiv.arrowCongr (Equiv.refl _) eBool
    have hbij : #{T : Fin s × Fin s → ZMod 2 | isBiased T} ≤
        #{g : Fin s × Fin s → Bool |
          b₀ * #(Finset.univ : Finset (Fin s × Fin s)) ≤
            |(#{q ∈ (Finset.univ : Finset (Fin s × Fin s)) | g q = true} : ℝ) -
              #(Finset.univ : Finset (Fin s × Fin s)) / 2|} := by
      rw [← Finset.card_map eTab.toEmbedding]
      refine Finset.card_le_card fun g hg => ?_
      obtain ⟨T, hT, rfl⟩ := Finset.mem_map.mp hg
      have hTb : isBiased T := (mem_filter.mp hT).2
      rw [mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [card_univ, Fintype.card_prod, Fintype.card_fin, Equiv.coe_toEmbedding]
      have hcnt : #{q : Fin s × Fin s | eTab T q = true} = #{q : Fin s × Fin s | T q = 1} :=
        congrArg Finset.card (Finset.ext fun q => by simp [eTab, eBool])
      rw [hcnt]
      exact hTb.le
    calc (#{T : Fin s × Fin s → ZMod 2 | isBiased T} : ℝ)
        ≤ _ := Nat.cast_le.mpr hbij
      _ ≤ 2 * 2 ^ Fintype.card (Fin s × Fin s) *
            exp (-(2 * (b₀ * #(Finset.univ : Finset (Fin s × Fin s))) ^ 2 /
              #(Finset.univ : Finset (Fin s × Fin s)))) :=
          BitString.card_filter_le_abs_card_filter_sub_half_le Finset.univ (by positivity)
      _ = 2 * 2 ^ (s * s) * exp (-(2 * b₀ ^ 2 * (s * s : ℕ))) := by
          simp only [card_univ, Fintype.card_prod, Fintype.card_fin]
          have hss_ne : ((s * s : ℕ) : ℝ) ≠ 0 := by positivity
          congr 2
          push_cast
          field_simp
  obtain ⟨bad, hbad_card, hbad_mem⟩ := exists_pivotGrid_bad (n := n) (p := p) isBiased
  have hbad_lt : (#bad : ℝ) < 2 ^ M := by
    have hcast : (#bad : ℝ) * 2 ^ (s * s) ≤
        2 ^ (n + n * s) * (2 ^ M * #{T : Fin s × Fin s → ZMod 2 | isBiased T}) := by
      exact_mod_cast hbad_card
    calc (#bad : ℝ)
        ≤ (2 : ℝ) ^ (n + n * s + 1) * exp (-(2 * b₀ ^ 2 * (s * s : ℕ))) * 2 ^ M := by
          rw [← mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < 2 ^ (s * s))]
          refine hcast.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            hcard_biased (by positivity)) (by positivity)).trans_eq ?_)
          ring
      _ < 2 ^ M := by
          refine mul_lt_of_lt_one_left (by positivity) ?_
          refine (mul_le_mul_of_nonneg_right (Real.two_pow_le_exp _) (exp_pos _).le).trans_lt ?_
          rw [← exp_add, exp_lt_one_iff]
          have hns : (n : ℝ) + 2 ≤ s := by exact_mod_cast hs_gt_n
          have hmul_s : ((n : ℝ) + 2) * s ≤ 2 * b₀ ^ 2 * (s * s : ℕ) := by
            push_cast
            have := mul_le_mul_of_nonneg_right hsb₀ (Nat.cast_nonneg (α := ℝ) s)
            nlinarith
          push_cast
          nlinarith
  have hbad_nat : #bad < #(Finset.univ : Finset (PolyIdx n (2 * p) → ZMod 2)) := by
    rw [card_univ, Fintype.card_fun, ZMod.card]
    exact_mod_cast hbad_lt
  obtain ⟨c, -, hc_good⟩ := exists_mem_notMem_of_card_lt_card hbad_nat
  have hK₀_le : (polyThreshold p s : ℝ) ≤ b₀ * K := by
    have hceil : (polyThreshold p s : ℝ) / b₀ ≤ K := by
      have h1 := Nat.le_ceil ((polyThreshold p s : ℝ) / b₀)
      have h2 : (K : ℝ) = (⌈(polyThreshold p s : ℝ) / b₀⌉₊ : ℝ) + 1 := by
        simp only [K, b₀]; push_cast; rfl
      linarith
    rw [mul_comm]
    exact (div_le_iff₀ hb₀).mp hceil
  have hbias_2b₀ : RectangleBias {x | evalPoly c x = 1} K (2 * b₀) := by
    refine rectangleBias_of_pivot_blocks hs1 hb₀ hK₀_le
      (fun X _ hA => exists_pivots_of_polyThreshold hp hA)
      (fun X _ hB => exists_pivots_of_polyThreshold hp hB) ?_
    intro X a J₁ b' J₂ ha_inj hb_inj ha_rows hb_rows
    let eCut := Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => Bool
    have hnbiased : ¬ isBiased fun q => evalPoly c (eCut.symm (a q.1, b' q.2)) :=
      fun hb' => hc_good (hbad_mem c X a J₁ b' J₂ ha_rows hb_rows hb')
    simp only [isBiased, not_lt] at hnbiased
    let zMap (q : Fin s × Fin s) : Fin n → Bool := eCut.symm (a q.1, b' q.2)
    have hz_inj : Function.Injective zMap := fun q₁ q₂ h => by
      have hp := eCut.symm.injective h
      exact Prod.ext (ha_inj (Prod.mk.inj hp).1) (hb_inj (Prod.mk.inj hp).2)
    have hrect_eq : rectangle X (Set.range a) (Set.range b') ∩ {x | evalPoly c x = 1} =
        zMap '' (↑({q : Fin s × Fin s | evalPoly c (zMap q) = 1} : Finset _) : Set _) := by
      ext x
      simp only [Set.mem_inter_iff, mem_rectangle, Set.mem_range, Set.mem_ofPred_eq,
        Set.mem_image, coe_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨⟨i, hi⟩, ⟨k, hk⟩⟩, hx1⟩
        have hzx : zMap (i, k) = x := by
          apply eCut.injective
          rw [show eCut (zMap (i, k)) = (a i, b' k) from eCut.apply_symm_apply _]
          exact Prod.ext hi hk
        exact ⟨(i, k), hzx.symm ▸ hx1, hzx⟩
      · rintro ⟨⟨i, k⟩, h1, rfl⟩
        refine ⟨⟨⟨i, ?_⟩, ⟨k, ?_⟩⟩, h1⟩
        · change a i = (eCut (zMap (i, k))).1; simp only [zMap, Equiv.apply_symm_apply]
        · change b' k = (eCut (zMap (i, k))).2; simp only [zMap, Equiv.apply_symm_apply]
    rw [hrect_eq, Set.ncard_image_of_injective _ hz_inj, Set.ncard_coe_finset]
    exact hnbiased
  have hb_eq : 2 * b₀ = b := by simp only [b₀]; ring
  rw [hb_eq] at hbias_2b₀
  exact ⟨evalPoly c, evalPoly_mem_lowDegree c, hbias_2b₀⟩

/-! ### Asymptotics of `polyThreshold` and `4.57597 n` circuit lower bounds -/

private theorem log_polyThreshold_le {p k : ℕ} (hp : 1 ≤ p) (hk : 1 ≤ k) :
    Real.log (polyThreshold p k) ≤
      ((p : ℝ) ^ 2 + (p.factorial : ℝ) ^ (1 / (p : ℝ)) * Real.log 2) *
        (k : ℝ) ^ (1 / (p : ℝ)) + 3 * Real.log 2 := by
  let d := ⌈((p.factorial * k : ℕ) : ℝ) ^ (1 / (p : ℝ))⌉₊
  have hpt_def : polyThreshold p k = k + k ^ (p - 1) * 2 ^ d := rfl
  have hk_pow : k ≤ k ^ p := Nat.le_self_pow (by omega) k
  have hk_pm1 : k ^ (p - 1) ≤ k ^ p := Nat.pow_le_pow_right hk (by omega)
  have h2d : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have hpt_pos : 0 < polyThreshold p k := by rw [hpt_def]; omega
  have hpt_le : polyThreshold p k ≤ 2 * k ^ p * 2 ^ d := by
    rw [hpt_def]
    have h1 : k ≤ k ^ p * 2 ^ d := hk_pow.trans (Nat.le_mul_of_pos_right _ h2d)
    have h2 : k ^ (p - 1) * 2 ^ d ≤ k ^ p * 2 ^ d := Nat.mul_le_mul_right _ hk_pm1
    have h3 : 2 * k ^ p * 2 ^ d = k ^ p * 2 ^ d + k ^ p * 2 ^ d := by ring
    omega
  have hlog_le : Real.log (polyThreshold p k) ≤
      Real.log 2 + p * Real.log k + d * Real.log 2 := by
    calc Real.log (polyThreshold p k)
        ≤ Real.log ((2 * k ^ p * 2 ^ d : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast hpt_pos) (by exact_mod_cast hpt_le)
      _ = Real.log 2 + p * Real.log k + d * Real.log 2 := by
          push_cast
          rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog_k : Real.log k ≤ (p : ℝ) * (k : ℝ) ^ (1 / (p : ℝ)) := by
    set y := (k : ℝ) ^ (1 / (p : ℝ))
    have hy_pos : 0 < y := Real.rpow_pos_of_pos hk_pos _
    have hly : Real.log y = (1 / (p : ℝ)) * Real.log k := Real.log_rpow hk_pos _
    have hle := Real.log_le_sub_one_of_pos hy_pos
    rw [hly, one_div, inv_mul_le_iff₀ hp_pos] at hle
    linarith
  have hd_le : (d : ℝ) ≤ (p.factorial : ℝ) ^ (1 / (p : ℝ)) * (k : ℝ) ^ (1 / (p : ℝ)) + 1 := by
    have hlt : (d : ℝ) ≤ ((p.factorial * k : ℕ) : ℝ) ^ (1 / (p : ℝ)) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hmul : ((p.factorial * k : ℕ) : ℝ) ^ (1 / (p : ℝ)) =
        (p.factorial : ℝ) ^ (1 / (p : ℝ)) * (k : ℝ) ^ (1 / (p : ℝ)) := by
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  nlinarith [mul_le_mul_of_nonneg_left hlog_k hp_pos.le,
    mul_le_mul_of_nonneg_right hd_le hlog2_pos.le]

private theorem isLittleO_natCast_rpow_id {θ : ℝ} (hθ : θ < 1) :
    (fun n : ℕ => (n : ℝ) ^ θ) =o[atTop] fun n : ℕ => (n : ℝ) := by
  refine isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn h0
    exact absurd h0 (by positivity)
  · have hlim : Tendsto (fun x : ℝ => x ^ (θ - 1)) atTop (nhds 0) := by
      simpa only [neg_sub] using tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)
    refine (hlim.comp tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp_apply]
    rw [Real.rpow_sub hn_pos, Real.rpow_one]

private theorem isLittleO_log_polyThreshold {p : ℕ} (hp : 2 ≤ p) {s : ℕ → ℕ}
    (hs1 : ∀ᶠ n in atTop, 1 ≤ s n) {α : ℝ} (hαp : α < p)
    (hsO : (fun n : ℕ => (s n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ α) :
    (fun n : ℕ => Real.log (polyThreshold p (s n))) =o[atTop] fun n : ℕ => (n : ℝ) := by
  have hp1 : 1 ≤ p := by omega
  have hp_pos : (0 : ℝ) < p := by positivity
  set C := (p : ℝ) ^ 2 + (p.factorial : ℝ) ^ (1 / (p : ℝ)) * Real.log 2
  have hsrpow : (fun n : ℕ => (s n : ℝ) ^ (1 / (p : ℝ))) =o[atTop] fun n : ℕ => (n : ℝ) := by
    have hO : (fun n : ℕ => (s n : ℝ) ^ (1 / (p : ℝ))) =O[atTop]
        fun n : ℕ => ((n : ℝ) ^ α) ^ (1 / (p : ℝ)) :=
      hsO.rpow (by positivity) (Filter.Eventually.of_forall fun n => by positivity)
    have heq : (fun n : ℕ => ((n : ℝ) ^ α) ^ (1 / (p : ℝ))) =ᶠ[atTop]
        fun n : ℕ => (n : ℝ) ^ (α / p) := by
      filter_upwards [eventually_ge_atTop 1] with n _
      rw [← Real.rpow_mul (Nat.cast_nonneg n), mul_one_div]
    exact (hO.trans_eventuallyEq heq).trans_isLittleO
      (isLittleO_natCast_rpow_id ((div_lt_one hp_pos).mpr hαp))
  have hdom : (fun n : ℕ => C * (s n : ℝ) ^ (1 / (p : ℝ)) + 3 * Real.log 2) =o[atTop]
      fun n : ℕ => (n : ℝ) :=
    (hsrpow.const_mul_left C).add (isLittleO_const_id_atTop (3 * Real.log 2)).natCast_atTop
  refine (IsBigO.of_bound 1 ?_).trans_isLittleO hdom
  filter_upwards [hs1] with n hn
  have hpt1 : (1 : ℝ) ≤ polyThreshold p (s n) := by
    rw [polyThreshold]
    exact_mod_cast hn.trans (Nat.le_add_right _ _)
  have hnonneg : 0 ≤ Real.log (polyThreshold p (s n)) := Real.log_nonneg hpt1
  have hub := log_polyThreshold_le hp1 hn
  rw [one_mul, Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (hnonneg.trans hub)]
  exact hub

/-- **Low-degree polynomial families satisfy `DenseRectangleFree`.** For every `p ≥ 2`, there is a
family of degree-`≤ 2 p` polynomials `f n ∈ BitString.lowDegree (ZMod 2) (Fin n) (2 * p)` over
`ZMod 2` such that `S n = {x | f n x = 1}` satisfies
`DenseRectangleFree S (polyThreshold p (· + 2))` and `2 ^ (n - 1) ≤ (S n).ncard`. -/
theorem exists_lowDegree_denseRectangleFree_family {p : ℕ} (hp : 2 ≤ p) :
    ∃ f : ∀ n, (Fin n → Bool) → ZMod 2,
      (∀ n, f n ∈ BitString.lowDegree (ZMod 2) (Fin n) (2 * p)) ∧
      DenseRectangleFree (fun n => {x | f n x = 1}) (fun n => polyThreshold p (n + 2)) ∧
      ∀ n, 2 ^ (n - 1) ≤ {x | f n x = 1}.ncard := by
  choose f hf_deg hfree hdense using fun n =>
    exists_lowDegree_rectangleFree (by omega : 1 ≤ p) n
  refine ⟨f, hf_deg, ⟨Filter.Eventually.of_forall fun n => hfree n 1, ?_,
    isLittleO_deficit_of_two_pow_le_ncard hdense⟩, hdense⟩
  have h1lt : (1 : ℝ) < p := by
    have : 1 < p := by omega
    exact_mod_cast this
  refine isLittleO_log_polyThreshold hp (Filter.Eventually.of_forall fun n => by omega) h1lt ?_
  refine IsBigO.of_bound 3 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.rpow_one, Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  linarith

/-- **Quartic polynomial families (`deg ≤ 4`) satisfy `DenseRectangleFree`.** -/
theorem exists_quartic_denseRectangleFree_family :
    ∃ f : ∀ n, (Fin n → Bool) → ZMod 2,
      (∀ n, f n ∈ BitString.lowDegree (ZMod 2) (Fin n) 4) ∧
      DenseRectangleFree (fun n => {x | f n x = 1}) (fun n => polyThreshold 2 (n + 2)) ∧
      ∀ n, 2 ^ (n - 1) ≤ {x | f n x = 1}.ncard := by
  simpa using exists_lowDegree_denseRectangleFree_family (p := 2) le_rfl

universe v in
/-- **Worst-case `4.57597 n` circuit lower bound for quartic (`deg ≤ 4`) polynomials.** There is a
family of quartic polynomials `f n ∈ BitString.lowDegree (ZMod 2) (Fin n) 4` (`O(n ^ 4)` bits of
description) such that for every `ε > 0` and all large `n`, every fan-in-two circuit deciding
`{x | f n x = 1}` over any basis has more than `(1 + 2π / (3 arccos (5 / 6)) - ε) n` inner gates
(in particular more than `(457597 / 100000 - ε) n` inner gates). -/
theorem exists_quartic_switched_lt_innerSize :
    ∃ f : ∀ n, (Fin n → Bool) → ZMod 2,
      (∀ n, f n ∈ BitString.lowDegree (ZMod 2) (Fin n) 4) ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ᶠ n in atTop,
        ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
          (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc {x | f n x = 1} →
            (1 + 2 * π / (3 * arccos (5 / 6)) - ε) * n < c.innerSize := by
  obtain ⟨f, hf_deg, hSK, -⟩ := exists_quartic_denseRectangleFree_family
  exact ⟨f, hf_deg, fun hε => eventually_switched_sub_mul_lt_innerSize.{0, v} hSK hε⟩

universe v in
/-- **Nondeterministic `4.57597 n` circuit lower bound for quartic (`deg ≤ 4`) polynomials.** The
quartic family of `exists_quartic_denseRectangleFree_family` also requires more than
`(1 + 2π / (3 arccos (5 / 6)) - ε) n` inner gates for every nondeterministic fan-in-two circuit
with *any* number `k` of witness inputs. -/
theorem exists_quartic_switched_lt_innerSize_nondeterministic :
    ∃ f : ∀ n, (Fin n → Bool) → ZMod 2,
      (∀ n, f n ∈ BitString.lowDegree (ZMod 2) (Fin n) 4) ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ᶠ n in atTop,
        ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
          (c : Circuit σ (n + k) 1),
          c.FanInAtMost 2 → c.NondeterministicDecides I Acc {x | f n x = 1} →
            (1 + 2 * π / (3 * arccos (5 / 6)) - ε) * n < c.innerSize := by
  obtain ⟨f, hf_deg, hSK, -⟩ := exists_quartic_denseRectangleFree_family
  exact ⟨f, hf_deg, fun hε =>
    eventually_switched_sub_mul_lt_innerSize_of_nondeterministicDecides.{0, v} hSK hε⟩

/-- **Low-degree polynomial families with polynomially decaying `RectangleBias` and
`log K = o(n)`.** For every `p ≥ 2` and `0 < β < (p - 1) / 2`, there exist a family of
degree-`≤ 2 p` polynomials `f n ∈ BitString.lowDegree (ZMod 2) (Fin n) (2 * p)` and thresholds
`K : ℕ → ℕ` with `Real.log (K n) = o(n)` such that `{x | f n x = 1}` has `RectangleBias` at most
`(n + 1) ^ (-β)` above `K n` for every `n`. -/
theorem exists_lowDegree_rectangleBias_family {p : ℕ} (hp : 2 ≤ p) {β : ℝ} (hβ0 : 0 < β)
    (hβp : β < ((p : ℝ) - 1) / 2) :
    ∃ (f : ∀ n, (Fin n → Bool) → ZMod 2) (K : ℕ → ℕ),
      (∀ n, f n ∈ BitString.lowDegree (ZMod 2) (Fin n) (2 * p)) ∧
      (∀ n, RectangleBias {x | f n x = 1} (K n) (((n : ℝ) + 1) ^ (-β))) ∧
      (fun n : ℕ => Real.log (K n)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
  let b (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-β)
  have hb_pos (n : ℕ) : 0 < b n := Real.rpow_pos_of_pos (by positivity) _
  let s (n : ℕ) : ℕ := ⌈((n : ℝ) + 2) / (b n ^ 2 / 2)⌉₊ + 2
  let K (n : ℕ) : ℕ := ⌈(polyThreshold p (s n) : ℝ) / (b n / 2)⌉₊ + 1
  choose f hf_deg hbias using fun n =>
    exists_lowDegree_rectangleBias (by omega : 1 ≤ p) n (hb_pos n)
  refine ⟨f, K, hf_deg, hbias, ?_⟩
  have hsO : (fun n : ℕ => (s n : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 + 2 * β) := by
    refine IsBigO.of_bound ((12 : ℝ) * (2 : ℝ) ^ (2 * β)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hn1_le : (n : ℝ) + 1 ≤ 2 * n := by linarith
    have hb_sq : b n ^ 2 = ((n : ℝ) + 1) ^ (-(2 * β)) := by
      simp only [b]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      push_cast; ring_nf
    have hdiv_eq : ((n : ℝ) + 2) / (b n ^ 2 / 2) =
        2 * ((n : ℝ) + 2) * ((n : ℝ) + 1) ^ (2 * β) := by
      rw [hb_sq, div_div_eq_mul_div, div_eq_mul_inv, ← Real.rpow_neg (by positivity), neg_neg]
      ring
    have hrpow_le : ((n : ℝ) + 1) ^ (2 * β) ≤ (2 : ℝ) ^ (2 * β) * (n : ℝ) ^ (2 * β) := by
      calc ((n : ℝ) + 1) ^ (2 * β) ≤ (2 * (n : ℝ)) ^ (2 * β) :=
            Real.rpow_le_rpow (by positivity) hn1_le (by positivity)
        _ = (2 : ℝ) ^ (2 * β) * (n : ℝ) ^ (2 * β) :=
            Real.mul_rpow two_pos.le (Nat.cast_nonneg n)
    have hceil_lt : (s n : ℝ) ≤ 2 * ((n : ℝ) + 2) * ((n : ℝ) + 1) ^ (2 * β) + 3 := by
      have h1 := (Nat.ceil_lt_add_one (by positivity :
        (0 : ℝ) ≤ ((n : ℝ) + 2) / (b n ^ 2 / 2))).le
      have h2 : (s n : ℝ) = (⌈((n : ℝ) + 2) / (b n ^ 2 / 2)⌉₊ : ℝ) + 2 := by
        simp only [s]; push_cast; rfl
      linarith [hdiv_eq]
    have hnrpow : (n : ℝ) * (n : ℝ) ^ (2 * β) = (n : ℝ) ^ (1 + 2 * β) := by
      calc (n : ℝ) * (n : ℝ) ^ (2 * β)
          = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (2 * β) := by rw [Real.rpow_one]
        _ = (n : ℝ) ^ (1 + 2 * β) := (Real.rpow_add hn0 1 (2 * β)).symm
    have h1_le_rpow : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * β) * (n : ℝ) ^ (1 + 2 * β) := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * β) := Real.one_le_rpow one_le_two (by positivity)
      have : (1 : ℝ) ≤ (n : ℝ) ^ (1 + 2 * β) := Real.one_le_rpow hn1 (by positivity)
      nlinarith
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
    have hn2_le : 2 * ((n : ℝ) + 2) ≤ 6 * (n : ℝ) := by linarith
    have hprod_le : 2 * ((n : ℝ) + 2) * ((n : ℝ) + 1) ^ (2 * β) ≤
        6 * (2 : ℝ) ^ (2 * β) * (n : ℝ) ^ (1 + 2 * β) := by
      calc 2 * ((n : ℝ) + 2) * ((n : ℝ) + 1) ^ (2 * β)
          ≤ (6 * (n : ℝ)) * ((2 : ℝ) ^ (2 * β) * (n : ℝ) ^ (2 * β)) :=
            mul_le_mul hn2_le hrpow_le (by positivity) (by positivity)
        _ = 6 * (2 : ℝ) ^ (2 * β) * ((n : ℝ) * (n : ℝ) ^ (2 * β)) := by ring
        _ = 6 * (2 : ℝ) ^ (2 * β) * (n : ℝ) ^ (1 + 2 * β) := by rw [hnrpow]
    linarith
  have hlog_pt : (fun n : ℕ => Real.log (polyThreshold p (s n))) =o[atTop] fun n : ℕ => (n : ℝ) :=
    isLittleO_log_polyThreshold hp (Filter.Eventually.of_forall fun n => by simp only [s]; omega)
      (by linarith) hsO
  have hdom : (fun n : ℕ => Real.log (polyThreshold p (s n)) +
      β * Real.log ((n : ℝ) + 1) + Real.log 8) =o[atTop] fun n : ℕ => (n : ℝ) :=
    (hlog_pt.add ((isLittleO_log_add 1).const_mul_left β)).add
      (isLittleO_const_id_atTop (Real.log 8)).natCast_atTop
  refine (IsBigO.of_bound 1 ?_).trans_isLittleO hdom
  filter_upwards [eventually_ge_atTop 1] with n _
  have hpt1 : (1 : ℝ) ≤ polyThreshold p (s n) := by
    rw [polyThreshold]
    have : 1 ≤ s n := by simp only [s]; omega
    exact_mod_cast this.trans (Nat.le_add_right _ _)
  have hK1 : (1 : ℝ) ≤ K n := by
    have h0 : (0 : ℝ) ≤ (⌈(polyThreshold p (s n) : ℝ) / (b n / 2)⌉₊ : ℝ) := Nat.cast_nonneg _
    have hK_eq : (K n : ℝ) = (⌈(polyThreshold p (s n) : ℝ) / (b n / 2)⌉₊ : ℝ) + 1 := by
      simp only [K]; push_cast; rfl
    linarith
  have hb_inv : 1 / (b n / 2) = 2 * ((n : ℝ) + 1) ^ β := by
    simp only [b, one_div_div]
    rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity), neg_neg]
  have hK_le : (K n : ℝ) ≤ 8 * (polyThreshold p (s n) : ℝ) * ((n : ℝ) + 1) ^ β := by
    have hc := (Nat.ceil_lt_add_one (by positivity :
      (0 : ℝ) ≤ (polyThreshold p (s n) : ℝ) / (b n / 2))).le
    have hdiv : (polyThreshold p (s n) : ℝ) / (b n / 2) =
        2 * (polyThreshold p (s n) : ℝ) * ((n : ℝ) + 1) ^ β := by
      rw [div_eq_mul_one_div, hb_inv]; ring
    have hr1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ β :=
      Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) n]) hβ0.le
    have hK_eq : (K n : ℝ) = (⌈(polyThreshold p (s n) : ℝ) / (b n / 2)⌉₊ : ℝ) + 1 := by
      simp only [K]; push_cast; rfl
    nlinarith
  have hub : Real.log (K n) ≤
      Real.log (polyThreshold p (s n)) + β * Real.log ((n : ℝ) + 1) + Real.log 8 := by
    calc Real.log (K n)
        ≤ Real.log (8 * (polyThreshold p (s n) : ℝ) * ((n : ℝ) + 1) ^ β) :=
          Real.log_le_log (by positivity) hK_le
      _ = Real.log (polyThreshold p (s n)) + β * Real.log ((n : ℝ) + 1) + Real.log 8 := by
          rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity)]
          ring
  have hnonneg : 0 ≤ Real.log (K n) := Real.log_nonneg hK1
  rw [one_mul, Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (hnonneg.trans hub)]
  exact hub

universe v in
/-- **Average-case `4.57597 n` lower bound for quartic (`deg ≤ 4`) polynomials.** For every
`0 < β < 1 / 2`, there is a family of quartic polynomials
`f n ∈ BitString.lowDegree (ZMod 2) (Fin n) 4` (`O(n ^ 4)` bits of description) such that for every
`ε > 0` there is a `γ > 0` with the following property: for all large `n`, every fan-in-two circuit
with at most `(1 + 2π / (3 arccos (5 / 6)) - ε) n` inner gates agrees with `{x | f n x = 1}` on at
most a `1 / 2 + (n + 1) ^ (-β) + exp (-γ n)` fraction of `Bool ^ n`. -/
theorem exists_quartic_agreement_le_switched {β : ℝ} (hβ0 : 0 < β) (hβ_half : β < 1 / 2) :
    ∃ f : ∀ n, (Fin n → Bool) → ZMod 2,
      (∀ n, f n ∈ BitString.lowDegree (ZMod 2) (Fin n) 4) ∧
      ∀ {ε : ℝ}, 0 < ε → ∃ γ > 0, ∀ᶠ n in atTop,
        ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
          (c : Circuit σ n 1), c.FanInAtMost 2 →
          (c.innerSize : ℝ) ≤ (1 + 2 * π / (3 * arccos (5 / 6)) - ε) * n →
            agreement {x | f n x = 1} {x | c.eval I x 0 ∈ Acc} ≤
              1 / 2 + ((n : ℝ) + 1) ^ (-β) + Real.exp (-(γ * n)) := by
  have hβ2 : β < (((2 : ℕ) : ℝ) - 1) / 2 := by push_cast; linarith
  obtain ⟨f, K, hf_deg, hbias, hlogK⟩ :=
    exists_lowDegree_rectangleBias_family (p := 2) le_rfl hβ0 hβ2
  refine ⟨f, by simpa using hf_deg, fun {ε} hε => ?_⟩
  obtain ⟨γ, hγ, H⟩ := averageCaseBound_switched.{0, v} ε hε
  exact ⟨γ, hγ, H Bool (fun n => {x | f n x = 1}) K (fun n => ((n : ℝ) + 1) ^ (-β))
    (Filter.Eventually.of_forall hbias) hlogK⟩

universe v in
/-- **Rational `4.57597 n` average-case lower bound for quartic (`deg ≤ 4`) polynomials.** Under
the hypotheses of `exists_quartic_agreement_le_switched`, every fan-in-two circuit with at most
`(457597 / 100000 - ε) n` inner gates agrees with `{x | f n x = 1}` on at most a
`1 / 2 + (n + 1) ^ (-β) + exp (-γ n)` fraction of `Bool ^ n`. -/
theorem exists_quartic_agreement_le_457597_div_100000 {β : ℝ} (hβ0 : 0 < β)
    (hβ_half : β < 1 / 2) :
    ∃ f : ∀ n, (Fin n → Bool) → ZMod 2,
      (∀ n, f n ∈ BitString.lowDegree (ZMod 2) (Fin n) 4) ∧
      ∀ {ε : ℝ}, 0 < ε → ∃ γ > 0, ∀ᶠ n in atTop,
        ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
          (c : Circuit σ n 1), c.FanInAtMost 2 →
          (c.innerSize : ℝ) ≤ (457597 / 100000 - ε) * n →
            agreement {x | f n x = 1} {x | c.eval I x 0 ∈ Acc} ≤
              1 / 2 + ((n : ℝ) + 1) ^ (-β) + Real.exp (-(γ * n)) := by
  obtain ⟨f, hf_deg, H⟩ := exists_quartic_agreement_le_switched.{v} hβ0 hβ_half
  refine ⟨f, hf_deg, fun {ε} hε => ?_⟩
  obtain ⟨γ, hγ, hEv⟩ := H hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hEv] with n hn σ I Acc c hfan hsize
  exact hn σ I Acc c hfan (hsize.trans (mul_le_mul_of_nonneg_right
    (by linarith [Switched.circuitCoefficient_ge_457597]) (Nat.cast_nonneg n)))

universe v in
/-- **Two-sided correlation `4.57597 n` lower bound for quartic (`deg ≤ 4`) polynomials.** For every
`0 < β < 1 / 2`, there is a family of quartic polynomials
`f n ∈ BitString.lowDegree (ZMod 2) (Fin n) 4` such that for every `ε > 0` there is a `γ > 0` with
`|correlation {x | f n x = 1} {x | c.eval I x 0 ∈ Acc}| ≤ 2 (n + 1) ^ (-β) + 2 exp (-γ n)` for all
large `n` and every fan-in-two circuit with at most `(1 + 2π / (3 arccos (5 / 6)) - ε) n` inner
gates. -/
theorem exists_quartic_abs_correlation_le_switched {β : ℝ} (hβ0 : 0 < β) (hβ_half : β < 1 / 2) :
    ∃ f : ∀ n, (Fin n → Bool) → ZMod 2,
      (∀ n, f n ∈ BitString.lowDegree (ZMod 2) (Fin n) 4) ∧
      ∀ {ε : ℝ}, 0 < ε → ∃ γ > 0, ∀ᶠ n in atTop,
        ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
          (c : Circuit σ n 1), c.FanInAtMost 2 →
          (c.innerSize : ℝ) ≤ (1 + 2 * π / (3 * arccos (5 / 6)) - ε) * n →
            |correlation {x | f n x = 1} {x | c.eval I x 0 ∈ Acc}| ≤
              2 * ((n : ℝ) + 1) ^ (-β) + 2 * Real.exp (-(γ * n)) := by
  obtain ⟨f, hf_deg, H⟩ := exists_quartic_agreement_le_switched.{v} hβ0 hβ_half
  refine ⟨f, hf_deg, fun {ε} hε => ?_⟩
  obtain ⟨γ, hγ, hEv⟩ := H hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hEv] with n hn σ I Acc c hfan hsize
  have h1 := hn σ I Acc c hfan hsize
  have h2 := hn σ I Accᶜ c hfan hsize
  have hcompl : {x : Fin n → Bool | c.eval I x 0 ∈ Accᶜ} = {x | c.eval I x 0 ∈ Acc}ᶜ := rfl
  rw [hcompl] at h2
  have hc1 := correlation_eq_two_mul_agreement_sub_one {x | f n x = 1} {x | c.eval I x 0 ∈ Acc}
  have hc2 := correlation_eq_two_mul_agreement_sub_one {x | f n x = 1} {x | c.eval I x 0 ∈ Acc}ᶜ
  rw [correlation_compl_right] at hc2
  rw [abs_le]
  constructor <;> linarith

universe v in
/-- **Rational `4.57597 n` two-sided correlation bound for quartic (`deg ≤ 4`) polynomials.** Under
the hypotheses of `exists_quartic_abs_correlation_le_switched`, every fan-in-two circuit with at
most `(457597 / 100000 - ε) n` inner gates has correlation at most
`2 (n + 1) ^ (-β) + 2 exp (-γ n)` in absolute value with `{x | f n x = 1}`. -/
theorem exists_quartic_abs_correlation_le_457597_div_100000 {β : ℝ} (hβ0 : 0 < β)
    (hβ_half : β < 1 / 2) :
    ∃ f : ∀ n, (Fin n → Bool) → ZMod 2,
      (∀ n, f n ∈ BitString.lowDegree (ZMod 2) (Fin n) 4) ∧
      ∀ {ε : ℝ}, 0 < ε → ∃ γ > 0, ∀ᶠ n in atTop,
        ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
          (c : Circuit σ n 1), c.FanInAtMost 2 →
          (c.innerSize : ℝ) ≤ (457597 / 100000 - ε) * n →
            |correlation {x | f n x = 1} {x | c.eval I x 0 ∈ Acc}| ≤
              2 * ((n : ℝ) + 1) ^ (-β) + 2 * Real.exp (-(γ * n)) := by
  obtain ⟨f, hf_deg, H⟩ := exists_quartic_abs_correlation_le_switched.{v} hβ0 hβ_half
  refine ⟨f, hf_deg, fun {ε} hε => ?_⟩
  obtain ⟨γ, hγ, hEv⟩ := H hε
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [hEv] with n hn σ I Acc c hfan hsize
  exact hn σ I Acc c hfan (hsize.trans (mul_le_mul_of_nonneg_right
    (by linarith [Switched.circuitCoefficient_ge_457597]) (Nat.cast_nonneg n)))

end Cslib.Circuits.Frontier
