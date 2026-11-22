/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Compiler.GateSweep.Uniform
public import CslibFrontier.Computability.Circuit.Frontier.Correlation.Rectangle
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Sqrt
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quadratic-form correlation via disjoint-block-robust polar matrices and node cuts

For circuits of bounded fan-in `r ≥ 3`, a single gate may read `r` inputs at once, so a layout need
not have any layer that has read an exact bisection of the inputs. Instead, a two-coloring
`A ⊆ Compiler.Node c` splits the reachable inputs into three disjoint sets:

* `L`, whose consumer supports lie wholly inside `A`;
* `R'`, whose consumer supports lie wholly inside `Aᶜ`;
* `O`, whose consumer supports straddle the cut.

Fixing any assignment `a : O → Bool` to the straddling inputs reduces `BitString.quadForm Q` on the
remaining coordinates `Oᶜ` to a quadratic form `Q_a` whose polar matrix is the principal submatrix
`(Q + Qᵀ).submatrix (↑) (↑)` (`Matrix.dotProduct_mulVec_self_eq_add` together with `z * z = z` and
`z + z = 0` over `𝔽₂`). On each slice `a`, inputs sharing the circuit output and the trace values of
straddling inner gates `G_cut` form a rectangle across `(L, R')` by
`Compiler.eval_splice_signalFrontier` and `Compiler.trace_gate_splice_signalFrontier`. Lindsey's
lemma and Cauchy–Schwarz across slices then give

`correlation² · 2 ^ ((Q + Qᵀ).blockRank L R') ≤ 2 · 2 ^ |G_cut|`

(`sq_correlation_quadForm_mul_le_of_node_cut`).

When the polar matrix `Q + Qᵀ` has high rank on every square block `S × T` with `Disjoint S T`
(`Matrix.DisjointBlockRobust`, shown to exist with deficiency `2 ⌊√n⌋ + 1` in
`Matrix.exists_disjointBlockRobust`), combining `Compiler.exists_node_cut_margin` with the unread
input bound yields `2 ^ (-γ n)` correlation below `((k₀ + 1) / (r + 2 ^ k₀ - k₀ - 1) - ε) n` inner
gates for all `r ≥ 2` and `k₀ ≥ 1`, hence `Ω(log r) · n` in `(r - 1) * c.innerSize`.

## Main definitions

* `Matrix.DisjointBlockRobust M t`: every disjoint `k × k` block of `M` has rank at least `k - t`.
* `Matrix.symmHardForm n`: an `n × n` matrix over `𝔽₂` whose polar matrix is disjoint-block-robust
  with deficiency `2 ⌊√n⌋ + 1`.
* `Cslib.Circuits.Frontier.quadFormGateSweepCoefficient r k₀`: the gate-count threshold
  `(k₀ + 1) / (r + 2 ^ k₀ - k₀ - 1)`.

## Main results

* `Matrix.exists_disjointBlockRobust`: counting existence over upper-triangular `𝔽₂` matrices.
* `Cslib.Circuits.Frontier.sq_correlation_quadForm_mul_le_of_node_cut`: slice correlation bound
  across any node cut `A ⊆ Compiler.Node c`.
* `Cslib.Circuits.Frontier.exists_eventually_abs_correlation_quadForm_le_gateSweep`: exponential
  correlation bound below `quadFormGateSweepCoefficient r k₀` for all `r ≥ 2` and `k₀ ≥ 1`.
* `Cslib.Circuits.Frontier.exists_eventually_abs_correlation_symmHardForm_le_log`: unconditional
  `(log₂ r - log₂ log₂ r - 2 - ε) n` correlation bound against `Matrix.symmHardForm`.
-/

public section

/-! ### Disjoint-block-robust matrices and counting existence -/

namespace Matrix

variable {ι K : Type*} [Field K]

/-- `M` is *disjoint-block-robust* with deficiency `t`: every square block `S × T` of `M` on
disjoint index sets `S` and `T` with `k` rows and `k` columns has rank at least `k - t`. -/
@[nolint unusedArguments, expose]
def DisjointBlockRobust [Finite ι] (M : Matrix ι ι K) (t : ℕ) : Prop :=
  ∀ (S T : Set ι), Disjoint S T → S.ncard = T.ncard → S.ncard ≤ M.blockRank S T + t

/-- A larger deficiency is weaker. -/
theorem DisjointBlockRobust.mono [Finite ι] {M : Matrix ι ι K} {t t' : ℕ}
    (hM : M.DisjointBlockRobust t) (ht : t ≤ t') : M.DisjointBlockRobust t' :=
  fun S T hST hcard => (hM S T hST hcard).trans (Nat.add_le_add_left ht _)

/-- Every disjoint block of a disjoint-block-robust matrix has rank at least its smaller side minus
the deficiency. -/
theorem DisjointBlockRobust.min_le [Finite ι] {M : Matrix ι ι K} {t : ℕ}
    (hM : M.DisjointBlockRobust t) {S T : Set ι} (hST : Disjoint S T) :
    min S.ncard T.ncard ≤ M.blockRank S T + t := by
  obtain ⟨S', hS', hS'c⟩ := Set.exists_subset_card_eq (min_le_left S.ncard T.ncard)
  obtain ⟨T', hT', hT'c⟩ := Set.exists_subset_card_eq (min_le_right S.ncard T.ncard)
  have h := hM S' T' (hST.mono hS' hT') (hS'c.trans hT'c.symm)
  rw [hS'c] at h
  exact h.trans (Nat.add_le_add_right (M.blockRank_mono hS' hT') t)

/-- Every cut `U` of a disjoint-block-robust matrix has cut rank at least `min |U| |Uᶜ| - t`. -/
theorem DisjointBlockRobust.min_le_cutRank_add [Finite ι] {M : Matrix ι ι K} {t : ℕ}
    (hM : M.DisjointBlockRobust t) (U : Set ι) :
    min U.ncard Uᶜ.ncard ≤ M.cutRank U + t :=
  hM.min_le disjoint_compl_right

section Counting

open Finset

private abbrev UpperIdx (n : ℕ) : Type :=
  {p : Fin n × Fin n // p.1 < p.2}

private def toUpper {n : ℕ} (u : UpperIdx n → ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => if h : i < j then u ⟨(i, j), h⟩ else 0

private def polarUpper {n : ℕ} (u : UpperIdx n → ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  toUpper u + (toUpper u)ᵀ

private def ordPair {n : ℕ} {i j : Fin n} (hne : i ≠ j) : UpperIdx n :=
  ⟨(min i j, max i j), min_lt_max.mpr hne⟩

private theorem polarUpper_apply_of_ne {n : ℕ} (u : UpperIdx n → ZMod 2) {i j : Fin n}
    (hne : i ≠ j) : polarUpper u i j = u (ordPair hne) := by
  simp only [polarUpper, toUpper, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
  by_cases hij : i < j
  · have hnji : ¬ j < i := lt_asymm hij
    simp only [hij, hnji, ↓reduceDIte, add_zero]
    congr 1
    exact Subtype.ext (Prod.ext (min_eq_left hij.le).symm (max_eq_right hij.le).symm)
  · have hji : j < i := lt_of_le_of_ne (not_lt.mp hij) hne.symm
    simp only [hij, hji, ↓reduceDIte, zero_add]
    congr 1
    exact Subtype.ext (Prod.ext (min_eq_right hji.le).symm (max_eq_left hji.le).symm)

private theorem ordPair_eq_iff {n : ℕ} {i₁ j₁ i₂ j₂ : Fin n} (h₁ : i₁ ≠ j₁) (h₂ : i₂ ≠ j₂)
    (heq : ordPair h₁ = ordPair h₂) :
    (i₁ = i₂ ∧ j₁ = j₂) ∨ (i₁ = j₂ ∧ j₁ = i₂) := by
  have hval : (min i₁ j₁, max i₁ j₁) = (min i₂ j₂, max i₂ j₂) := congrArg Subtype.val heq
  obtain ⟨hmin, hmax⟩ := Prod.mk.inj hval
  rcases le_total i₁ j₁ with le₁ | le₁ <;> rcases le_total i₂ j₂ with le₂ | le₂
  · rw [min_eq_left le₁, min_eq_left le₂] at hmin
    rw [max_eq_right le₁, max_eq_right le₂] at hmax
    exact Or.inl ⟨hmin, hmax⟩
  · rw [min_eq_left le₁, min_eq_right le₂] at hmin
    rw [max_eq_right le₁, max_eq_left le₂] at hmax
    exact Or.inr ⟨hmin, hmax⟩
  · rw [min_eq_right le₁, min_eq_left le₂] at hmin
    rw [max_eq_left le₁, max_eq_right le₂] at hmax
    exact Or.inr ⟨hmax, hmin⟩
  · rw [min_eq_right le₁, min_eq_right le₂] at hmin
    rw [max_eq_left le₁, max_eq_left le₂] at hmax
    exact Or.inl ⟨hmax, hmin⟩

private def colVec {n : ℕ} (R : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Set (Fin n)) (j : Fin n) :
    S → ZMod 2 :=
  fun i => R i j

private theorem exists_spanning_columns {n : ℕ} (R : Matrix (Fin n) (Fin n) (ZMod 2))
    (S T : Finset (Fin n)) :
    ∃ T' ⊆ T, #T' = R.blockRank ↑S ↑T ∧
      ∀ j ∈ T, colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T') := by
  classical
  let v : (↑T : Set (Fin n)) → (↑S : Set (Fin n)) → ZMod 2 := fun j => colVec R ↑S j
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' (ZMod 2) v
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  refine ⟨Finset.univ.image fun x => (a x : Fin n), ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨x, -, rfl⟩ := mem_image.mp hj
    exact (a x).2
  · rw [show (fun x => (a x : Fin n)) = Subtype.val ∘ a from rfl,
      card_image_of_injective _ (Subtype.val_injective.comp ha), card_univ,
      ← finrank_span_eq_card hli, hspan, ← blockRank_transpose]
    rfl
  · have hrange :
        Set.range (v ∘ a) = colVec R ↑S '' ↑(Finset.univ.image fun x => (a x : Fin n)) := by
      ext y
      simp only [Set.mem_range, Function.comp_apply, coe_image, coe_univ, Set.image_univ,
        Set.mem_image, v]
      exact ⟨fun ⟨x, hx⟩ => ⟨a x, ⟨x, rfl⟩, hx⟩, fun ⟨_, ⟨x, rfl⟩, hx⟩ => ⟨x, hx⟩⟩
    intro j hj
    rw [← hrange, hspan]
    exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

open Classical in
private noncomputable def spannedUpper {n : ℕ} (S T T' : Finset (Fin n)) :
    Finset (UpperIdx n → ZMod 2) :=
  {u | ∀ j ∈ T, colVec (polarUpper u) ↑S j ∈
    Submodule.span (ZMod 2) (colVec (polarUpper u) ↑S '' ↑T')}

open Classical in
private noncomputable def spanCoeff {n : ℕ} (R : Matrix (Fin n) (Fin n) (ZMod 2))
    (S T' : Finset (Fin n)) (j : Fin n) : T' → ZMod 2 :=
  if h : colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T') then
    Classical.choose ((Submodule.mem_span_image_finset_iff_exists_fun (ZMod 2)).mp h)
  else 0

private theorem spanCoeff_spec {n : ℕ} {R : Matrix (Fin n) (Fin n) (ZMod 2)}
    {S T' : Finset (Fin n)} {j : Fin n}
    (h : colVec R ↑S j ∈ Submodule.span (ZMod 2) (colVec R ↑S '' ↑T')) :
    ∑ l, spanCoeff R S T' j l • colVec R ↑S l = colVec R ↑S j := by
  unfold spanCoeff
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec ((Submodule.mem_span_image_finset_iff_exists_fun (ZMod 2)).mp h)

private theorem card_spannedUpper_mul_le {n : ℕ} {S T T' : Finset (Fin n)}
    (hST : Disjoint S T) (hT'T : T' ⊆ T) :
    #(spannedUpper S T T') * 2 ^ (#S * #(T \ T')) ≤
      2 ^ (#(T \ T') * #T') * 2 ^ Fintype.card (UpperIdx n) := by
  classical
  set D := T \ T'
  have hSD : Disjoint S D := hST.mono_right sdiff_subset
  let toW : {p : Fin n × Fin n // p ∈ S ×ˢ D} → UpperIdx n
    | ⟨⟨i, j⟩, hp⟩ =>
      ordPair (Finset.disjoint_coe.mpr hSD |>.ne_of_mem (mem_product.mp hp).1 (mem_product.mp hp).2)
  have htoW_inj : Function.Injective toW := by
    rintro ⟨⟨i₁, j₁⟩, hp₁⟩ ⟨⟨i₂, j₂⟩, hp₂⟩ heq
    obtain ⟨hi₁, hj₁⟩ := mem_product.mp hp₁
    obtain ⟨hi₂, hj₂⟩ := mem_product.mp hp₂
    rcases ordPair_eq_iff _ _ heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd hj₂ (Finset.disjoint_left.mp hSD hi₁)
  let W : Finset (UpperIdx n) := (S ×ˢ D).attach.image toW
  have hcardW : #W = #S * #D := by
    rw [card_image_of_injective _ htoW_inj, card_attach, card_product]
  let Z : Finset (UpperIdx n) := Wᶜ
  have hcardZ : #Z + #S * #D = Fintype.card (UpperIdx n) := by
    rw [← hcardW]
    exact card_compl_add_card W
  let Φ : (UpperIdx n → ZMod 2) → (D → T' → ZMod 2) × (Z → ZMod 2) :=
    fun u => (fun j => spanCoeff (polarUpper u) S T' j.val, fun p => u p.val)
  have hinj : Set.InjOn Φ (spannedUpper S T T') := by
    intro u₁ hu₁ u₂ hu₂ h
    obtain ⟨hc, hz⟩ := Prod.mk.inj h
    have h₁ := (mem_filter.mp hu₁).2
    have h₂ := (mem_filter.mp hu₂).2
    funext q
    by_cases hqZ : q ∈ Z
    · exact congrFun hz ⟨q, hqZ⟩
    · have hqW : q ∈ W := by simpa [Z] using hqZ
      obtain ⟨⟨⟨i, j⟩, hp⟩, -, rfl⟩ := mem_image.mp hqW
      obtain ⟨hiS, hjD⟩ := mem_product.mp hp
      have hjT : j ∈ T := (mem_sdiff.mp hjD).1
      have hne_ij : i ≠ j := Finset.disjoint_coe.mpr hSD |>.ne_of_mem hiS hjD
      have eq₁ := polarUpper_apply_of_ne u₁ hne_ij
      have eq₂ := polarUpper_apply_of_ne u₂ hne_ij
      change u₁ (ordPair hne_ij) = u₂ (ordPair hne_ij)
      rw [← eq₁, ← eq₂]
      have e₁ := congrFun (spanCoeff_spec (h₁ j hjT)) ⟨i, hiS⟩
      have e₂ := congrFun (spanCoeff_spec (h₂ j hjT)) ⟨i, hiS⟩
      have hcj : spanCoeff (polarUpper u₁) S T' j = spanCoeff (polarUpper u₂) S T' j :=
        congrFun hc ⟨j, hjD⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, colVec] at e₁ e₂
      rw [← e₁, ← e₂, hcj]
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      have hlT : l.val ∈ T := hT'T l.prop
      have hne_il : i ≠ l.val := Finset.disjoint_coe.mpr hST |>.ne_of_mem hiS hlT
      have hlZ : ordPair hne_il ∈ Z := by
        rw [Finset.mem_compl]
        intro hmemW
        obtain ⟨⟨⟨i', j'⟩, hp'⟩, -, heq'⟩ := mem_image.mp hmemW
        obtain ⟨hi'S, hj'D⟩ := mem_product.mp hp'
        rcases ordPair_eq_iff _ _ heq' with ⟨_, hlj⟩ | ⟨hij', _⟩
        · exact (mem_sdiff.mp (hlj ▸ hj'D)).2 l.prop
        · exact Finset.disjoint_left.mp hST (hij' ▸ hi'S) hlT
      rw [polarUpper_apply_of_ne u₁ hne_il, polarUpper_apply_of_ne u₂ hne_il]
      exact congrFun hz ⟨ordPair hne_il, hlZ⟩
  have hcard := card_le_card_of_injOn Φ (fun _ _ => mem_univ _) hinj
  rw [card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
    ZMod.card, Fintype.card_coe, Fintype.card_coe, Fintype.card_coe] at hcard
  calc #(spannedUpper S T T') * 2 ^ (#S * #D)
      ≤ (2 ^ #T') ^ #D * 2 ^ #Z * 2 ^ (#S * #D) := Nat.mul_le_mul_right _ hcard
    _ = 2 ^ (#D * #T') * 2 ^ Fintype.card (UpperIdx n) := by
        rw [mul_assoc, ← pow_add, hcardZ, ← pow_mul, mul_comm #T']

private theorem card_spannedUpper_mul_two_pow_sq_le {n t : ℕ} {S T T' : Finset (Fin n)}
    (hST_disj : Disjoint S T) (hT'T : T' ⊆ T) (hlt : #T' + t < #S) (hST : #S = #T) :
    #(spannedUpper S T T') * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ Fintype.card (UpperIdx n) := by
  have hsplit := card_sdiff_add_card_eq_card hT'T
  set d := #(T \ T')
  have hd : t + 1 ≤ d := by omega
  have H := card_spannedUpper_mul_le hST_disj hT'T
  rw [hST, ← hsplit] at H
  have hpow : 2 ^ ((t + 1) ^ 2) ≤ 2 ^ (d * d) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have key : #(spannedUpper S T T') * 2 ^ (d * d) * 2 ^ (d * #T') ≤
      2 ^ Fintype.card (UpperIdx n) * 2 ^ (d * #T') := by
    calc #(spannedUpper S T T') * 2 ^ (d * d) * 2 ^ (d * #T')
        = #(spannedUpper S T T') * 2 ^ ((d + #T') * d) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          ring
      _ ≤ 2 ^ (d * #T') * 2 ^ Fintype.card (UpperIdx n) := H
      _ = _ := mul_comm _ _
  calc #(spannedUpper S T T') * 2 ^ ((t + 1) ^ 2)
      ≤ #(spannedUpper S T T') * 2 ^ (d * d) := Nat.mul_le_mul_left _ hpow
    _ ≤ _ := Nat.le_of_mul_le_mul_right key (by positivity)

open Classical in
private noncomputable def deficientUpperOn {n : ℕ} (t : ℕ) (S T : Finset (Fin n)) :
    Finset (UpperIdx n → ZMod 2) :=
  {u | Disjoint S T ∧ #S = #T ∧ (polarUpper u).blockRank ↑S ↑T + t < #S}

private theorem card_deficientUpperOn_mul_le {n : ℕ} (t : ℕ) (S T : Finset (Fin n)) :
    #(deficientUpperOn t S T) * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ n * 2 ^ Fintype.card (UpperIdx n) := by
  classical
  let 𝒯 := T.powerset.filter fun T' => Disjoint S T ∧ #T' + t < #S ∧ #S = #T
  have hsub : deficientUpperOn t S T ⊆ 𝒯.biUnion fun T' => spannedUpper S T T' := by
    intro u hu
    obtain ⟨hdisj, hST, hdef⟩ := (mem_filter.mp hu).2
    obtain ⟨T', hT', hcard, hspan⟩ := exists_spanning_columns (polarUpper u) S T
    refine mem_biUnion.mpr ⟨T', mem_filter.mpr ⟨mem_powerset.mpr hT', hdisj, by omega, hST⟩, ?_⟩
    exact mem_filter.mpr ⟨mem_univ _, hspan⟩
  have hone : ∀ T' ∈ 𝒯, #(spannedUpper S T T') * 2 ^ ((t + 1) ^ 2) ≤
      2 ^ Fintype.card (UpperIdx n) := fun T' hT' => by
    obtain ⟨hT'T, hdisj, hlt, hST⟩ := mem_filter.mp hT'
    exact card_spannedUpper_mul_two_pow_sq_le hdisj (mem_powerset.mp hT'T) hlt hST
  have h𝒯 : #𝒯 ≤ 2 ^ n := by
    calc #𝒯 ≤ #T.powerset := card_filter_le _ _
      _ = 2 ^ #T := card_powerset T
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (card_le_univ T |>.trans (by simp))
  calc #(deficientUpperOn t S T) * 2 ^ ((t + 1) ^ 2)
      ≤ (∑ T' ∈ 𝒯, #(spannedUpper S T T')) * 2 ^ ((t + 1) ^ 2) :=
        Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ T' ∈ 𝒯, #(spannedUpper S T T') * 2 ^ ((t + 1) ^ 2) := Finset.sum_mul ..
    _ ≤ ∑ _T' ∈ 𝒯, 2 ^ Fintype.card (UpperIdx n) := Finset.sum_le_sum hone
    _ = #𝒯 * 2 ^ Fintype.card (UpperIdx n) := by rw [sum_const, smul_eq_mul]
    _ ≤ 2 ^ n * 2 ^ Fintype.card (UpperIdx n) := Nat.mul_le_mul_right _ h𝒯

/-- **Polar matrices of upper-triangular forms are disjoint-block-robust, by counting.** If
`3 n < (t + 1) ^ 2`, some `n × n` matrix `Q` over `𝔽₂` has `(Q + Qᵀ).DisjointBlockRobust t`. -/
theorem exists_disjointBlockRobust_of_lt {n t : ℕ} (ht : 3 * n < (t + 1) ^ 2) :
    ∃ Q : Matrix (Fin n) (Fin n) (ZMod 2), (Q + Qᵀ).DisjointBlockRobust t := by
  classical
  set U := Fintype.card (UpperIdx n)
  let pairs : Finset (Finset (Fin n) × Finset (Fin n)) := univ ×ˢ univ
  let bad := pairs.biUnion fun p => deficientUpperOn t p.1 p.2
  have hbad : #bad * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ n * 2 ^ n * (2 ^ n * 2 ^ U) := by
    calc #bad * 2 ^ ((t + 1) ^ 2)
        ≤ (∑ p ∈ pairs, #(deficientUpperOn t p.1 p.2)) * 2 ^ ((t + 1) ^ 2) :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ p ∈ pairs, #(deficientUpperOn t p.1 p.2) * 2 ^ ((t + 1) ^ 2) := Finset.sum_mul ..
      _ ≤ ∑ _p ∈ pairs, 2 ^ n * 2 ^ U :=
          Finset.sum_le_sum fun p _ => card_deficientUpperOn_mul_le t p.1 p.2
      _ = 2 ^ n * 2 ^ n * (2 ^ n * 2 ^ U) := by
          rw [sum_const, smul_eq_mul, card_product, card_univ, Fintype.card_finset,
            Fintype.card_fin]
  have hlt : #bad < Fintype.card (UpperIdx n → ZMod 2) := by
    rw [Fintype.card_fun, ZMod.card]
    change #bad < 2 ^ U
    by_contra hge
    push Not at hge
    have h₁ : 2 ^ U * 2 ^ ((t + 1) ^ 2) ≤ 2 ^ n * 2 ^ n * (2 ^ n * 2 ^ U) :=
      (Nat.mul_le_mul_right _ hge).trans hbad
    have h₂ : 2 ^ n * 2 ^ n * (2 ^ n * 2 ^ U) < 2 ^ U * 2 ^ ((t + 1) ^ 2) := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨u, -, hu⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨toUpper u, fun S T hST hcard => ?_⟩
  by_contra hcon
  push Not at hcon
  apply hu
  refine mem_biUnion.mpr ⟨(S.toFinset, T.toFinset), mem_product.mpr ⟨mem_univ _, mem_univ _⟩, ?_⟩
  refine mem_filter.mpr ⟨mem_univ _, ?_, ?_, ?_⟩
  · rwa [← Finset.disjoint_coe, Set.coe_toFinset, Set.coe_toFinset]
  · rw [← Set.ncard_eq_toFinset_card', ← Set.ncard_eq_toFinset_card']
    exact hcard
  · simp only [Set.coe_toFinset, polarUpper]
    rw [← Set.ncard_eq_toFinset_card']
    exact hcon

/-- **Disjoint-block-robust polar matrices exist.** For every `n`, some `n × n` matrix `Q` over `𝔽₂`
has `(Q + Qᵀ).DisjointBlockRobust (2 ⌊√n⌋ + 1)`. -/
theorem exists_disjointBlockRobust (n : ℕ) :
    ∃ Q : Matrix (Fin n) (Fin n) (ZMod 2), (Q + Qᵀ).DisjointBlockRobust (2 * Nat.sqrt n + 1) := by
  refine exists_disjointBlockRobust_of_lt ?_
  have h := Nat.lt_succ_sqrt' n
  have hsq : (2 * Nat.sqrt n + 1 + 1) ^ 2 = 4 * (Nat.sqrt n + 1) ^ 2 := by ring
  rw [hsq]
  rw [Nat.succ_eq_add_one] at h
  omega

/-- An `n × n` matrix over `𝔽₂` (chosen nonconstructively via `Matrix.exists_disjointBlockRobust`)
whose polar matrix is disjoint-block-robust with deficiency `2 ⌊√n⌋ + 1`. -/
noncomputable def symmHardForm (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  (exists_disjointBlockRobust n).choose

/-- The polar matrix of `Matrix.symmHardForm n` is disjoint-block-robust with deficiency
`2 ⌊√n⌋ + 1`. -/
theorem disjointBlockRobust_symmHardForm (n : ℕ) :
    (symmHardForm n + (symmHardForm n)ᵀ).DisjointBlockRobust (2 * Nat.sqrt n + 1) :=
  (exists_disjointBlockRobust n).choose_spec

end Counting

end Matrix

/-! ### Slice correlation and node-cut bounds -/

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics Matrix
open scoped BigOperators

universe v

private theorem zmod_two_mul_self (z : ZMod 2) : z * z = z := by
  decide +revert

private theorem zmod_two_add_self (z : ZMod 2) : z + z = 0 := by
  decide +revert

@[simp]
private theorem correlation_compl_left {ι U : Type*}
    (S T : Set (ι → U)) : correlation Sᶜ T = -correlation S T := by
  have hs₁ : {x : ι → U | x ∈ Sᶜ ↔ x ∈ T} = {x | x ∈ S ↔ x ∈ Tᶜ} := by
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq]
    tauto
  have hs₂ : {x : ι → U | x ∈ Sᶜ ↔ x ∈ Tᶜ} = {x | x ∈ S ↔ x ∈ T} := by
    ext x
    simp only [mem_compl_iff, mem_ofPred_eq]
    tauto
  rw [correlation, correlation, agreement, agreement, hs₁, hs₂, ← agreement, ← agreement, neg_sub]

private def sliceEquiv {n : ℕ} (O : Set (Fin n)) [DecidablePred (· ∈ O)] :
    (Fin n → Bool) ≃ (O → Bool) × (↥Oᶜ → Bool) where
  toFun x := (fun i => x i.val, fun j => x j.val)
  invFun p i := if h : i ∈ O then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩
  left_inv x := funext fun i => by by_cases h : i ∈ O <;> simp [h]
  right_inv := fun ⟨a, y⟩ => Prod.ext
    (funext fun ⟨i, hi⟩ => dite_eq_left hi)
    (funext fun ⟨j, hj⟩ => dite_eq_right hj)

private theorem sliceEquiv_symm_of_mem {n : ℕ} {O : Set (Fin n)} [DecidablePred (· ∈ O)]
    (a : O → Bool) (y : ↥Oᶜ → Bool) {i : Fin n} (hi : i ∈ O) :
    (sliceEquiv O).symm (a, y) i = a ⟨i, hi⟩ :=
  dite_eq_left hi

private theorem sliceEquiv_symm_of_not_mem {n : ℕ} {O : Set (Fin n)} [DecidablePred (· ∈ O)]
    (a : O → Bool) (y : ↥Oᶜ → Bool) {i : Fin n} (hi : i ∉ O) :
    (sliceEquiv O).symm (a, y) i = y ⟨i, hi⟩ :=
  dite_eq_right hi

/-- **Slice quadratic form.** Fixing `a : O → Bool` on a coordinate set `O ⊆ Fin n` turns
`BitString.quadForm Q` on the remaining coordinates `Oᶜ` into either `BitString.quadForm Q_a` or
its negation, where `Q_a + Q_aᵀ = (Q + Qᵀ).submatrix (↑) (↑)`. -/
private theorem exists_slice_quadForm {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (O : Set (Fin n)) [DecidablePred (· ∈ O)] (a : O → Bool) :
    ∃ Q_a : Matrix ↥Oᶜ ↥Oᶜ (ZMod 2),
      Q_a + Q_aᵀ = (Q + Qᵀ).submatrix ((↑) : ↥Oᶜ → Fin n) ((↑) : ↥Oᶜ → Fin n) ∧
      ({y : ↥Oᶜ → Bool | BitString.quadForm Q ((sliceEquiv O).symm (a, y))} =
          {y | BitString.quadForm Q_a y} ∨
        {y : ↥Oᶜ → Bool | BitString.quadForm Q ((sliceEquiv O).symm (a, y))} =
          {y | BitString.quadForm Q_a y}ᶜ) := by
  let bit := BitString.bitVal (ZMod 2)
  let u : O → ZMod 2 := fun i => bit (a i)
  let C : Matrix O ↥Oᶜ (ZMod 2) := (Q + Qᵀ).submatrix ((↑) : O → Fin n) ((↑) : ↥Oᶜ → Fin n)
  let d : ↥Oᶜ → ZMod 2 := Cᵀ *ᵥ u
  let Q_a : Matrix ↥Oᶜ ↥Oᶜ (ZMod 2) :=
    Q.submatrix ((↑) : ↥Oᶜ → Fin n) ((↑) : ↥Oᶜ → Fin n) + Matrix.diagonal d
  refine ⟨Q_a, ?_, ?_⟩
  · ext i j
    simp only [Q_a, Matrix.add_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      have hd0 : d i + d i = 0 := zmod_two_add_self (d i)
      linear_combination hd0
    · have hji : j ≠ i := Ne.symm hij
      simp only [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hji, add_zero]
  · let c₀ : ZMod 2 := u ⬝ᵥ Q.submatrix ((↑) : O → Fin n) ((↑) : O → Fin n) *ᵥ u
    have hval (y : ↥Oᶜ → Bool) :
        (fun i => BitString.bitVal (ZMod 2) ((sliceEquiv O).symm (a, y) i)) ⬝ᵥ
            Q *ᵥ (fun i => BitString.bitVal (ZMod 2) ((sliceEquiv O).symm (a, y) i)) =
          c₀ + (fun j => BitString.bitVal (ZMod 2) (y j)) ⬝ᵥ
            Q_a *ᵥ (fun j => BitString.bitVal (ZMod 2) (y j)) := by
      let v : Fin n → ZMod 2 := fun i => bit ((sliceEquiv O).symm (a, y) i)
      let w : ↥Oᶜ → ZMod 2 := fun j => bit (y j)
      have hvO : O.domRestrict v = u :=
        funext fun ⟨i, hi⟩ => congrArg bit (sliceEquiv_symm_of_mem a y hi)
      have hvOc : Oᶜ.domRestrict v = w :=
        funext fun ⟨j, hj⟩ => congrArg bit (sliceEquiv_symm_of_not_mem a y hj)
      have hsplit := Matrix.dotProduct_mulVec_self_eq_add Q O v
      rw [hvO, hvOc] at hsplit
      have hdiag : u ⬝ᵥ C *ᵥ w = w ⬝ᵥ Matrix.diagonal d *ᵥ w := by
        have hL : u ⬝ᵥ C *ᵥ w = ∑ j : ↥Oᶜ, d j * w j := by
          simp only [d, dotProduct, mulVec, Matrix.transpose_apply, Finset.mul_sum,
            Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
        have hR : w ⬝ᵥ Matrix.diagonal d *ᵥ w = ∑ j : ↥Oᶜ, d j * w j := by
          simp only [dotProduct, mulVec, Matrix.diagonal_apply, ite_mul, zero_mul,
            Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
          refine Finset.sum_congr rfl fun j _ => ?_
          calc w j * (d j * w j) = d j * (w j * w j) := by ring
            _ = d j * w j := by rw [zmod_two_mul_self]
        exact hL.trans hR.symm
      have hQa : w ⬝ᵥ Q_a *ᵥ w =
          w ⬝ᵥ Q.submatrix ((↑) : ↥Oᶜ → Fin n) ((↑) : ↥Oᶜ → Fin n) *ᵥ w +
            w ⬝ᵥ Matrix.diagonal d *ᵥ w := by
        simp only [Q_a, Matrix.add_mulVec, dotProduct_add]
      change v ⬝ᵥ Q *ᵥ v = c₀ + w ⬝ᵥ Q_a *ᵥ w
      rw [hsplit, hdiag, hQa]
      ring
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) c₀ with hc₀ | hc₀
    · refine Or.inl (Set.ext fun y => ?_)
      simp only [mem_ofPred_eq, BitString.quadForm_eq_true_iff]
      rw [hval y, hc₀, zero_add]
    · refine Or.inr (Set.ext fun y => ?_)
      simp only [mem_compl_iff, mem_ofPred_eq, BitString.quadForm_eq_true_iff]
      rw [hval y, hc₀]
      exact (by decide : ∀ z : ZMod 2, (1 + z = 1) ↔ ¬ (z = 1)) _

/-- Correlation decomposes as the uniform average of slice correlations across `O → Bool`. -/
private theorem correlation_mul_card_slice {n : ℕ} (S T : Set (Fin n → Bool))
    (O : Set (Fin n)) [DecidablePred (· ∈ O)]
    (e : (Fin n → Bool) ≃ (O → Bool) × (↥Oᶜ → Bool)) :
    correlation S T * Fintype.card (O → Bool) =
      ∑ a : O → Bool, correlation {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T} := by
  classical
  have hY : (0 : ℝ) < Fintype.card (↥Oᶜ → Bool) := by positivity
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) =
      (Fintype.card (O → Bool) : ℝ) * Fintype.card (↥Oᶜ → Bool) := by
    have hnat : Fintype.card (Fin n → Bool) =
        Fintype.card (O → Bool) * Fintype.card (↥Oᶜ → Bool) :=
      (Fintype.card_congr e).trans (Fintype.card_prod _ _)
    exact_mod_cast hnat
  have htot := correlation_mul_card_eq_sum S T
  rw [← e.symm.sum_comp, Fintype.sum_prod_type] at htot
  have hslice (a : O → Bool) :
      (∑ y : ↥Oᶜ → Bool, if (e.symm (a, y) ∈ S ↔ e.symm (a, y) ∈ T) then (1 : ℝ) else -1) =
        correlation {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T} *
          Fintype.card (↥Oᶜ → Bool) :=
    (correlation_mul_card_eq_sum {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T}).symm
  simp_rw [hslice] at htot
  rw [← Finset.sum_mul, hcard] at htot
  nlinarith

/-- **Correlation across a circuit node cut.** For any node cut `A ⊆ Compiler.Node c`, let `L` and
`R'` be the reachable inputs whose consumer supports lie wholly in `A` and wholly in `Aᶜ`, and let
`G_cut` be the inner gates whose support straddles `A`. Then

`correlation² · 2 ^ ((Q + Qᵀ).blockRank L R') ≤ 2 · 2 ^ |G_cut|`. -/
theorem sq_correlation_quadForm_mul_le_of_node_cut {σ : Signature.{v}} {n : ℕ}
    (I : Interpretation σ Bool) (Acc : Set Bool) (c : Circuit σ n 1)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (A : Set (Compiler.Node c)) :
    let L := {i : Fin n | ∃ hi : Compiler.Reach c (.input i),
      Compiler.support c (.input i hi) ⊆ A}
    let R' := {i : Fin n | ∃ hi : Compiler.Reach c (.input i),
      Compiler.support c (.input i hi) ⊆ Aᶜ}
    let G_cut := {g : Compiler.InnerGate c |
      Compiler.ActiveSignal.gate g ∈ Compiler.signalFrontier c A}
    correlation {x | BitString.quadForm Q x} {x | c.eval I x 0 ∈ Acc} ^ 2 *
        2 ^ (Q + Qᵀ).blockRank L R' ≤
      2 * 2 ^ G_cut.ncard := by
  classical
  intro L R' G_cut
  have := Fintype.ofFinite G_cut
  set O : Set (Fin n) := (L ∪ R')ᶜ
  let e := sliceEquiv O
  set S : Set (Fin n → Bool) := {x | BitString.quadForm Q x}
  set T : Set (Fin n → Bool) := {x | c.eval I x 0 ∈ Acc}
  have hLR_disj : Disjoint L R' := by
    refine Set.disjoint_left.mpr fun i ⟨hi, hsubA⟩ ⟨_, hsubAc⟩ => ?_
    obtain ⟨u, hu⟩ := Compiler.support_nonempty (.input i hi)
    exact hsubAc hu (hsubA hu)
  let X_cut : Set ↥Oᶜ := {j : ↥Oᶜ | j.val ∈ L}
  have himgL : (Subtype.val '' X_cut : Set (Fin n)) = L := by
    ext i
    simp only [mem_image, X_cut, mem_ofPred_eq, Subtype.exists]
    exact ⟨fun ⟨_, _, hiL, rfl⟩ => hiL,
      fun hiL => ⟨i, fun hiO => hiO (Or.inl hiL), hiL, rfl⟩⟩
  have himgR : (Subtype.val '' X_cutᶜ : Set (Fin n)) = R' := by
    ext i
    simp only [mem_image, mem_compl_iff, X_cut, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨j, hjOc⟩, hnjL, rfl⟩
      have hLR : j ∈ L ∪ R' := not_not.mp hjOc
      exact hLR.resolve_left hnjL
    · intro hiR
      exact ⟨⟨i, not_not.mpr (Or.inr hiR)⟩, Set.disjoint_right.mp hLR_disj hiR, rfl⟩
  have hslice_bound (a : O → Bool) :
      correlation {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T} ^ 2 *
          2 ^ (Q + Qᵀ).blockRank L R' ≤
        2 * 2 ^ G_cut.ncard := by
    obtain ⟨Q_a, hpolar, hSa⟩ := exists_slice_quadForm Q O a
    have hrank : (Q_a + Q_aᵀ).cutRank X_cut = (Q + Qᵀ).blockRank L R' := by
      rw [hpolar, Matrix.cutRank,
        (Q + Qᵀ).blockRank_submatrix Subtype.val_injective Subtype.val_injective X_cut X_cutᶜ,
        himgL, himgR]
    let T_a : Set (↥Oᶜ → Bool) := {y | e.symm (a, y) ∈ T}
    let msg : (↥Oᶜ → Bool) → Bool × (G_cut → Bool) := fun y =>
      (decide (c.eval I (e.symm (a, y)) 0 ∈ Acc),
        fun g => c.program.trace I (e.symm (a, y)) (Compiler.ActiveSignal.gate g.val).wire)
    have hT_msg : ∀ y₁ y₂, msg y₁ = msg y₂ → (y₁ ∈ T_a ↔ y₂ ∈ T_a) := by
      intro y₁ y₂ h
      have hdec := (Prod.mk.inj h).1
      simpa [T_a, T] using hdec
    have hrect_msg : ∀ y₀ : ↥Oᶜ → Bool, ∃ (B₁ : Set (X_cut → Bool)) (B₂ : Set (↥X_cutᶜ → Bool)),
        {y | msg y = msg y₀} = rectangle X_cut B₁ B₂ := by
      intro y₀
      let cls : Set (↥Oᶜ → Bool) := {y | msg y = msg y₀}
      refine ⟨X_cut.domRestrict '' cls, X_cutᶜ.domRestrict '' cls, ?_⟩
      ext y
      constructor
      · intro hy
        exact ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩
      · rintro ⟨⟨y₁, hy₁, hdom₁⟩, ⟨y₂, hy₂, hdom₂⟩⟩
        change msg y = msg y₀
        have hcut : ∀ w ∈ Compiler.signalFrontier c A,
            c.program.trace I (e.symm (a, y₁)) w.wire =
              c.program.trace I (e.symm (a, y₂)) w.wire := by
          intro w hw
          cases w with
          | input i hi =>
            have hniL : i ∉ L := by
              rintro ⟨_, hsubA⟩
              obtain ⟨u, hu, huAc⟩ := hw.2
              exact huAc (hsubA hu)
            have hniR : i ∉ R' := by
              rintro ⟨_, hsubAc⟩
              obtain ⟨u, hu, huA⟩ := hw.1
              exact hsubAc hu huA
            have hiO : i ∈ O := fun hLR => hLR.elim hniL hniR
            change (sliceEquiv O).symm (a, y₁) i = (sliceEquiv O).symm (a, y₂) i
            rw [sliceEquiv_symm_of_mem a y₁ hiO, sliceEquiv_symm_of_mem a y₂ hiO]
          | gate g =>
            have hg₁ := congrFun (Prod.mk.inj hy₁).2 ⟨g, hw⟩
            have hg₂ := congrFun (Prod.mk.inj hy₂).2 ⟨g, hw⟩
            exact hg₁.trans hg₂.symm
        have hzx : EqOn (e.symm (a, y)) (e.symm (a, y₁)) (Compiler.nodeReadIn c A) := by
          intro i ⟨hi, u, hu, huA⟩
          change (sliceEquiv O).symm (a, y) i = (sliceEquiv O).symm (a, y₁) i
          by_cases hiO : i ∈ O
          · rw [sliceEquiv_symm_of_mem a y hiO, sliceEquiv_symm_of_mem a y₁ hiO]
          · have hiLR : i ∈ L ∪ R' := not_not.mp hiO
            have hniR : i ∉ R' := fun ⟨_, hsubAc⟩ => hsubAc hu huA
            have hiL : i ∈ L := hiLR.resolve_right hniR
            rw [sliceEquiv_symm_of_not_mem a y hiO, sliceEquiv_symm_of_not_mem a y₁ hiO]
            exact (congrFun hdom₁ ⟨⟨i, hiO⟩, hiL⟩).symm
        have hzy : EqOn (e.symm (a, y)) (e.symm (a, y₂)) (Compiler.nodeReadIn c A)ᶜ := by
          intro i hni
          change (sliceEquiv O).symm (a, y) i = (sliceEquiv O).symm (a, y₂) i
          by_cases hiO : i ∈ O
          · rw [sliceEquiv_symm_of_mem a y hiO, sliceEquiv_symm_of_mem a y₂ hiO]
          · have hniL : i ∉ L := by
              rintro ⟨hi, hsubA⟩
              obtain ⟨u, hu⟩ := Compiler.support_nonempty (.input i hi)
              exact hni ⟨hi, u, hu, hsubA hu⟩
            rw [sliceEquiv_symm_of_not_mem a y hiO, sliceEquiv_symm_of_not_mem a y₂ hiO]
            exact (congrFun hdom₂ ⟨⟨i, hiO⟩, hniL⟩).symm
        have heval := Compiler.eval_splice_signalFrontier I hcut hzx hzy 0
        have hdec : decide (c.eval I (e.symm (a, y)) 0 ∈ Acc) =
            decide (c.eval I (e.symm (a, y₀)) 0 ∈ Acc) := by
          by_cases hoA : Compiler.Node.output 0 ∈ A
          · rw [heval.1 hoA]
            exact (Prod.mk.inj hy₁).1
          · rw [heval.2 hoA]
            exact (Prod.mk.inj hy₂).1
        have htr : (fun g : G_cut =>
            c.program.trace I (e.symm (a, y)) (Compiler.ActiveSignal.gate g.val).wire) =
            fun g : G_cut =>
              c.program.trace I (e.symm (a, y₀)) (Compiler.ActiveSignal.gate g.val).wire := by
          funext g
          have hstep := Compiler.trace_gate_splice_signalFrontier I hcut hzx hzy g.val
          by_cases hgA : Compiler.Node.gate g.val ∈ A
          · rw [hstep.1 hgA]
            exact congrFun (Prod.mk.inj hy₁).2 g
          · rw [hstep.2 hgA]
            exact congrFun (Prod.mk.inj hy₂).2 g
        exact Prod.ext hdec htr
    have hbase := sq_correlation_quadForm_mul_le Q_a T_a msg X_cut hT_msg hrect_msg
    rw [hrank] at hbase
    have hrange : ((range msg).ncard : ℝ) ≤ 2 * 2 ^ G_cut.ncard := by
      have hle := ncard_le_card (range msg)
      rw [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
        Nat.card_coe_set_eq] at hle
      exact_mod_cast hle
    have hcorr_sq :
        correlation {y | e.symm (a, y) ∈ S} T_a ^ 2 =
          correlation {y | BitString.quadForm Q_a y} T_a ^ 2 := by
      change correlation {y | BitString.quadForm Q ((sliceEquiv O).symm (a, y))} T_a ^ 2 = _
      rcases hSa with hpos | hneg
      · rw [hpos]
      · rw [hneg, correlation_compl_left, neg_sq]
    change correlation {y | e.symm (a, y) ∈ S} T_a ^ 2 * _ ≤ _
    rw [hcorr_sq]
    exact hbase.trans hrange
  set M_card : ℝ := (Fintype.card (O → Bool) : ℝ)
  have hM_pos : 0 < M_card := by positivity
  have havg := correlation_mul_card_slice S T O e
  have hCS := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (O → Bool)))
    (f := fun a : O → Bool => correlation {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T})
  rw [Finset.card_univ] at hCS
  set ρ := (Q + Qᵀ).blockRank L R'
  have hρ_pos : (0 : ℝ) < 2 ^ ρ := by positivity
  have hsum_le :
      (∑ a : O → Bool,
        correlation {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T} ^ 2 * 2 ^ ρ) ≤
      M_card * (2 * 2 ^ G_cut.ncard) := by
    calc (∑ a : O → Bool,
            correlation {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T} ^ 2 * 2 ^ ρ)
        ≤ ∑ _a : O → Bool, (2 * (2 : ℝ) ^ G_cut.ncard) :=
          Finset.sum_le_sum fun a _ => hslice_bound a
      _ = M_card * (2 * 2 ^ G_cut.ncard) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have htot_le : (correlation S T * M_card) ^ 2 * 2 ^ ρ ≤
      M_card * (M_card * (2 * 2 ^ G_cut.ncard)) := by
    rw [havg]
    calc (∑ a : O → Bool, correlation {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T}) ^ 2 * 2 ^ ρ
        ≤ M_card * (∑ a : O → Bool,
            correlation {y | e.symm (a, y) ∈ S} {y | e.symm (a, y) ∈ T} ^ 2 * 2 ^ ρ) := by
          rw [← Finset.sum_mul, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right hCS hρ_pos.le
      _ ≤ M_card * (M_card * (2 * 2 ^ G_cut.ncard)) :=
          mul_le_mul_of_nonneg_left hsum_le hM_pos.le
  have hMM : 0 < M_card * M_card := mul_pos hM_pos hM_pos
  nlinarith

/-- Unreachable inputs are unread: if `D` contains no reachable input of `c`, then
`correlation² · 2 ^ cutRank D ≤ 2`. -/
theorem sq_correlation_quadForm_mul_le_of_not_reach {σ : Signature.{v}} {n : ℕ}
    (I : Interpretation σ Bool) (Acc : Set Bool) (c : Circuit σ n 1)
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) {D : Set (Fin n)}
    (hD : ∀ i ∈ D, ¬ Compiler.Reach c (.input i)) :
    correlation {x | BitString.quadForm Q x} {x | c.eval I x 0 ∈ Acc} ^ 2 *
        2 ^ (Q + Qᵀ).cutRank D ≤ 2 := by
  classical
  set T : Set (Fin n → Bool) := {x | c.eval I x 0 ∈ Acc}
  have hdep : DependsOn (· ∈ T) Dᶜ := by
    intro x y hxy
    have hzx : EqOn x y (Compiler.nodeReadIn c univ) := by
      rw [Compiler.nodeReadIn_univ]
      exact fun i hi => @hxy i fun hiD => hD i hiD hi
    have heval := (Compiler.eval_splice_signalFrontier I
      (P := (univ : Set (Compiler.Node c))) (x := y) (y := x) (z := x)
      (by simp) hzx (fun _ _ => rfl) 0).1 (mem_univ _)
    simp only [T, mem_ofPred_eq, heval]
  have hdep' : DependsOn (· ∈ Tᶜ) Dᶜ := fun x y hxy => congrArg Not (hdep hxy)
  refine (sq_correlation_quadForm_mul_le Q T (fun x => decide (x ∈ T)) D
    (fun x y h => by simpa using h) fun x => ?_).trans ?_
  · by_cases hx : x ∈ T
    · refine ⟨univ, Dᶜ.domRestrict '' T, ?_⟩
      rw [← eq_rectangle_of_dependsOn hdep]
      exact Set.ext fun y => by by_cases hy : y ∈ T <;> simp [hx, hy]
    · refine ⟨univ, Dᶜ.domRestrict '' Tᶜ, ?_⟩
      rw [← eq_rectangle_of_dependsOn hdep']
      exact Set.ext fun y => by by_cases hy : y ∈ T <;> simp [hx, hy]
  · have hle := ncard_le_card (range fun x => decide (x ∈ T))
    rw [Nat.card_eq_fintype_card, Fintype.card_bool] at hle
    exact_mod_cast hle

/-! ### Asymptotic gate-sweep correlation bounds -/

/-- The gate-sweep coefficient `(k₀ + 1) / (r + 2 ^ k₀ - k₀ - 1)` for quadratic-form correlation at
fan-in `r`. -/
@[expose] noncomputable def quadFormGateSweepCoefficient (r k₀ : ℕ) : ℝ :=
  (k₀ + 1 : ℝ) / ((r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1)

theorem quadFormGateSweep_denom_ge (r k₀ : ℕ) :
    (r : ℝ) ≤ (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1 := by
  have hk : (k₀ + 1 : ℝ) ≤ (2 : ℝ) ^ k₀ := by
    exact_mod_cast Nat.succ_le_of_lt k₀.lt_two_pow_self
  linarith

theorem quadFormGateSweepCoefficient_pos {r : ℕ} (hr : 1 ≤ r) (k₀ : ℕ) :
    0 < quadFormGateSweepCoefficient r k₀ := by
  unfold quadFormGateSweepCoefficient
  have hd : (0 : ℝ) < (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1 := by
    have := quadFormGateSweep_denom_ge r k₀
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact div_pos (by positivity) hd

private theorem le_rpow_of_mul_two_pow_le {y : ℝ} {ρ m : ℕ} {r : ℝ}
    (hy : y * 2 ^ ρ ≤ 2 * 2 ^ m) (hr : r ≤ ρ) :
    y ≤ (2 : ℝ) ^ (1 + (m : ℝ) - r) := by
  have hpos : (0 : ℝ) < 2 ^ ρ := by positivity
  have h₁ : y ≤ 2 * 2 ^ m / 2 ^ ρ := (le_div_iff₀ hpos).mpr hy
  have h₂ : (2 * 2 ^ m / 2 ^ ρ : ℝ) = (2 : ℝ) ^ (1 + (m : ℝ) - (ρ : ℝ)) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one,
      Real.rpow_natCast, Real.rpow_natCast]
  rw [h₂] at h₁
  exact h₁.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

private theorem abs_le_two_rpow_of_sq_le {y γ : ℝ} {n : ℕ}
    (h : y ^ 2 ≤ (2 : ℝ) ^ (-(2 * γ) * n)) : |y| ≤ (2 : ℝ) ^ (-γ * n) := by
  apply abs_le_of_sq_le_sq _ (by positivity)
  have hsq : ((2 : ℝ) ^ (-γ * n)) ^ 2 = (2 : ℝ) ^ (-(2 * γ) * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast
    ring_nf
  rwa [hsq]

/-- **Exponentially small correlation with quadratic forms at fan-in `r`.** For every `r ≥ 2`,
`k₀ ≥ 1`, and `ε > 0`, there is `γ > 0` such that if `(Q n + (Q n)ᵀ)` is disjoint-block-robust with
sublinear deficiency `t n = o(n)`, every circuit of fan-in at most `r` with at most
`(quadFormGateSweepCoefficient r k₀ - ε) n` inner gates has correlation at most `2 ^ (-γ n)` with
`BitString.quadForm (Q n)`. -/
theorem exists_eventually_abs_correlation_quadForm_le_gateSweep {r k₀ : ℕ} (hr : 2 ≤ r)
    (hk₀ : 1 ≤ k₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (Q : ∀ n, Matrix (Fin n) (Fin n) (ZMod 2)) (t : ℕ → ℕ),
      (∀ᶠ n in atTop, (Q n + (Q n)ᵀ).DisjointBlockRobust (t n)) →
      (fun n => (t n : ℝ)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ n 1), c.FanInAtMost r →
          (c.innerSize : ℝ) ≤ (quadFormGateSweepCoefficient r k₀ - ε) * n →
          |correlation {x | BitString.quadForm (Q n) x} {x | c.eval I x 0 ∈ Acc}| ≤
            (2 : ℝ) ^ (-γ * n) := by
  set D_r : ℝ := (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1
  have hDr_ge : (2 : ℝ) ≤ D_r := by
    have h1 := quadFormGateSweep_denom_ge r k₀
    have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hDr_pos : 0 < D_r := by linarith
  set Q_c := quadFormGateSweepCoefficient r k₀
  have hQc_pos : 0 < Q_c := quadFormGateSweepCoefficient_pos (by omega) k₀
  have hDr_Qc : D_r * Q_c = (k₀ + 1 : ℝ) := by
    dsimp only [Q_c, quadFormGateSweepCoefficient, D_r]
    exact mul_div_cancel₀ _ hDr_pos.ne'
  set θ : ℝ := min (1 / 2) (D_r * ε / (2 * (k₀ + 1 : ℝ)))
  have hθ_pos : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ_half : θ ≤ 1 / 2 := min_le_left _ _
  set μ₀ : ℝ := D_r * ε / (2 * (2 : ℝ) ^ k₀)
  have hμ₀_pos : 0 < μ₀ := by positivity
  set μ : ℝ := min θ μ₀
  have hμ_pos : 0 < μ := lt_min hθ_pos hμ₀_pos
  refine ⟨μ / 4, by positivity, fun Q t hQ ht => ?_⟩
  set C_err : ℝ := 2 * (r + 1 : ℝ) * √(3 * (Q_c + 1))
  have hCerr_nn : 0 ≤ C_err := by positivity
  filter_upwards [hQ, ht.bound (show 0 < μ / 8 by positivity), eventually_ge_atTop 2,
    eventually_ge_atTop ⌈16 / μ⌉₊,
    eventually_ge_atTop (⌈(8 * C_err / μ) ^ 2⌉₊ + 1)] with n hQn htn hn2 hn_const hn_sqrt
  intro σ I Acc c hfan hsize
  classical
  have := Fintype.ofFinite {i : Fin n // Compiler.Reach c (.input i)}
  have := Fintype.ofFinite (Compiler.InnerGate c)
  have := Fintype.ofFinite (Compiler.ActiveSignal c)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have htn' : (t n : ℝ) ≤ (μ / 8) * n := by
    simp only [Real.norm_eq_abs, Nat.abs_cast] at htn
    exact htn
  have hconst_n : 2 ≤ (μ / 8) * n := by
    have h1 : 16 / μ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn_const)
    have := (div_le_iff₀ hμ_pos).mp h1
    linarith
  apply abs_le_two_rpow_of_sq_le
  let R_in : Set (Fin n) := {i : Fin n | Compiler.Reach c (.input i)}
  set d_un := R_inᶜ.ncard
  have hcompl_in : (R_in.ncard : ℝ) + d_un = n := by
    rw [← Nat.cast_add, ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  by_cases hd : θ * n ≤ d_un
  · -- Case 1: many unreachable (unread) inputs.
    set m_un := min d_un (n / 2)
    obtain ⟨D, hD_sub, hD_card⟩ := Set.exists_subset_card_eq (min_le_left d_un (n / 2))
    have hD_compl : m_un ≤ Dᶜ.ncard := by
      have htot := ncard_add_ncard_compl D
      rw [Nat.card_eq_fintype_card, Fintype.card_fin, hD_card] at htot
      have hm_half : m_un ≤ n / 2 := min_le_right _ _
      omega
    have hminD : min D.ncard Dᶜ.ncard = m_un := by
      rw [hD_card]
      exact min_eq_left hD_compl
    have hcutD : m_un ≤ (Q n + (Q n)ᵀ).cutRank D + t n := by
      have h := hQn.min_le_cutRank_add D
      rwa [hminD] at h
    have hcorrD := sq_correlation_quadForm_mul_le_of_not_reach I Acc c (Q n)
      fun i hi => hD_sub hi
    have hcorrD' :
        correlation {x | BitString.quadForm (Q n) x} {x | c.eval I x 0 ∈ Acc} ^ 2 *
          2 ^ (Q n + (Q n)ᵀ).cutRank D ≤ 2 * 2 ^ (0 : ℕ) := by
      simpa using hcorrD
    have hstep := le_rpow_of_mul_two_pow_le hcorrD' (r := (m_un : ℝ) - t n) (by
      have : (m_un : ℝ) ≤ (Q n + (Q n)ᵀ).cutRank D + t n := by exact_mod_cast hcutD
      linarith)
    refine hstep.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hhalf_lb : (n : ℝ) / 2 - 1 / 2 ≤ ((n / 2 : ℕ) : ℝ) := by
      have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
      linarith
    have hm_lb : θ * n - 1 / 2 ≤ (m_un : ℝ) := by
      have hθn : θ * n ≤ (n : ℝ) / 2 := by
        have := mul_le_mul_of_nonneg_right hθ_half hn0
        linarith
      dsimp only [m_un]
      rcases min_choice d_un (n / 2) with hmin | hmin <;> rw [hmin] <;> linarith
    have hμ_le_θ : μ ≤ θ := min_le_left _ _
    nlinarith
  · -- Case 2: few unreachable inputs; apply the two-coloring margin on `Node c`.
    push Not at hd
    obtain ⟨A, hLA, hRA, hGA⟩ := Compiler.exists_node_cut_margin c hfan
    let L := {i : Fin n | ∃ hi : Compiler.Reach c (.input i),
      Compiler.support c (.input i hi) ⊆ A}
    let R' := {i : Fin n | ∃ hi : Compiler.Reach c (.input i),
      Compiler.support c (.input i hi) ⊆ Aᶜ}
    let G_cut := {g : Compiler.InnerGate c |
      Compiler.ActiveSignal.gate g ∈ Compiler.signalFrontier c A}
    have hLR_disj : Disjoint L R' := by
      refine Set.disjoint_left.mpr fun i ⟨hi, hsubA⟩ ⟨_, hsubAc⟩ => ?_
      obtain ⟨u, hu⟩ := Compiler.support_nonempty (.input i hi)
      exact hsubAc hu (hsubA hu)
    -- Bound the input sum from below and the gate sum from above via the `k₀`-tangents.
    have hin_lb :
        ∑ i : {i : Fin n // Compiler.Reach c (.input i)},
          (((k₀ + 1 : ℝ) - (Compiler.support c (.input i.1 i.2)).ncard) / (2 : ℝ) ^ k₀) ≤
        ∑ i : {i : Fin n // Compiler.Reach c (.input i)},
          (1 / 2 : ℝ) ^ (Compiler.support c (.input i.1 i.2)).ncard :=
      Finset.sum_le_sum fun i _ => Compiler.two_pow_neg_ge_tangent hk₀
        ((ncard_pos (toFinite _)).mpr (Compiler.support_nonempty (.input i.1 i.2)))
    have hgt_ub :
        ∑ g : Compiler.InnerGate c,
          (1 - (1 / 2 : ℝ) ^ ((Compiler.support c (.gate g)).ncard - 1)) ≤
        ∑ g : Compiler.InnerGate c,
          ((1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) +
            ((Compiler.support c (.gate g)).ncard : ℝ) / (2 : ℝ) ^ k₀) :=
      Finset.sum_le_sum fun g _ => Compiler.one_sub_two_pow_le_tangent k₀
        ((Compiler.two_le_ncard_support_gate g).trans' (by decide))
    -- Combine the support sums into `∑ w : ActiveSignal c, (support c w).ncard`.
    have htot_supp :
        (∑ i : {i : Fin n // Compiler.Reach c (.input i)},
          ((Compiler.support c (.input i.1 i.2)).ncard : ℝ)) +
        (∑ g : Compiler.InnerGate c, ((Compiler.support c (.gate g)).ncard : ℝ)) ≤
        (r + 1 : ℝ) * Nat.card (Compiler.InnerGate c) + 1 := by
      have hnat := Compiler.sum_ncard_support_le_card_innerGate (c := c) hfan
      rw [← (Compiler.ActiveSignal.equiv c).symm.sum_comp (fun w => (Compiler.support c w).ncard),
        Fintype.sum_sum_type] at hnat
      exact_mod_cast hnat
    have hcard_Rin : (Fintype.card {i : Fin n // Compiler.Reach c (.input i)} : ℝ) =
        R_in.ncard := by
      rw [← Nat.card_eq_fintype_card]
      exact_mod_cast (Nat.card_coe_set_eq R_in)
    have hcard_G : (Fintype.card (Compiler.InnerGate c) : ℝ) =
        Nat.card (Compiler.InnerGate c) := by
      rw [Nat.card_eq_fintype_card]
    have hG_le_s : (Nat.card (Compiler.InnerGate c) : ℝ) ≤ c.innerSize := by
      have hnat : Nat.card (Compiler.InnerGate c) ≤ c.innerSize := by
        rw [Circuit.innerSize, ← Nat.card_eq_finsetCard]
        exact Nat.card_le_card_of_injective (fun g => ⟨g.1, Program.mem_innerGates.mpr g.2.2⟩)
          fun _ _ h => Subtype.ext (congrArg Subtype.val h :)
      exact_mod_cast hnat
    have hexp_diff :
        ((k₀ + 1 : ℝ) * R_in.ncard - D_r * Nat.card (Compiler.InnerGate c) - 1) / (2 : ℝ) ^ k₀ ≤
          (∑ i : {i : Fin n // Compiler.Reach c (.input i)},
            (1 / 2 : ℝ) ^ (Compiler.support c (.input i.1 i.2)).ncard) -
          (∑ g : Compiler.InnerGate c,
            (1 - (1 / 2 : ℝ) ^ ((Compiler.support c (.gate g)).ncard - 1))) := by
      have hsum_in :
          ∑ i : {i : Fin n // Compiler.Reach c (.input i)},
            (((k₀ + 1 : ℝ) - (Compiler.support c (.input i.1 i.2)).ncard) / (2 : ℝ) ^ k₀) =
          ((k₀ + 1 : ℝ) * R_in.ncard -
            ∑ i : {i : Fin n // Compiler.Reach c (.input i)},
              ((Compiler.support c (.input i.1 i.2)).ncard : ℝ)) / (2 : ℝ) ^ k₀ := by
        simp_rw [sub_div]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard_Rin,
          ← Finset.sum_div, mul_div_assoc']
        ring
      have hsum_gt :
          ∑ g : Compiler.InnerGate c,
            ((1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) +
              ((Compiler.support c (.gate g)).ncard : ℝ) / (2 : ℝ) ^ k₀) =
          (((2 : ℝ) ^ k₀ - k₀ - 2) * Nat.card (Compiler.InnerGate c) +
            ∑ g : Compiler.InnerGate c,
              ((Compiler.support c (.gate g)).ncard : ℝ)) / (2 : ℝ) ^ k₀ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard_G,
          ← Finset.sum_div]
        have hpos2 : (0 : ℝ) < (2 : ℝ) ^ k₀ := by positivity
        field_simp
        ring
      have hpos2 : (0 : ℝ) < (2 : ℝ) ^ k₀ := by positivity
      have hcomb :
          ((k₀ + 1 : ℝ) * R_in.ncard - D_r * Nat.card (Compiler.InnerGate c) - 1) / (2 : ℝ) ^ k₀ ≤
          ((k₀ + 1 : ℝ) * R_in.ncard -
            ∑ i : {i : Fin n // Compiler.Reach c (.input i)},
              ((Compiler.support c (.input i.1 i.2)).ncard : ℝ)) / (2 : ℝ) ^ k₀ -
          ((((2 : ℝ) ^ k₀ - k₀ - 2) * Nat.card (Compiler.InnerGate c) +
            ∑ g : Compiler.InnerGate c,
              ((Compiler.support c (.gate g)).ncard : ℝ)) / (2 : ℝ) ^ k₀) := by
        rw [← sub_div]
        refine div_le_div_of_nonneg_right ?_ hpos2.le
        dsimp only [D_r]
        linarith [htot_supp]
      linarith [hin_lb, hgt_ub, hsum_in, hsum_gt, hcomb]
    -- Bound the numerator using `d_un < θ * n` and `s ≤ (Q_c - ε) * n`.
    have hnum_lb : μ₀ * n - 1 / (2 : ℝ) ^ k₀ ≤
        ((k₀ + 1 : ℝ) * R_in.ncard - D_r * Nat.card (Compiler.InnerGate c) - 1) / (2 : ℝ) ^ k₀ := by
      have hpos2 : (0 : ℝ) < (2 : ℝ) ^ k₀ := by positivity
      have hd_prod : (k₀ + 1 : ℝ) * d_un ≤ (D_r * ε / 2) * n := by
        have hθ_ub : θ ≤ D_r * ε / (2 * (k₀ + 1 : ℝ)) := min_le_right _ _
        have h1 : (d_un : ℝ) ≤ D_r * ε / (2 * (k₀ + 1 : ℝ)) * n :=
          hd.le.trans (mul_le_mul_of_nonneg_right hθ_ub hn0)
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ k₀ + 1)
        have hcancel : (k₀ + 1 : ℝ) * (D_r * ε / (2 * (k₀ + 1 : ℝ)) * n) = (D_r * ε / 2) * n := by
          field_simp
        linarith
      have hs_prod : D_r * Nat.card (Compiler.InnerGate c) ≤ (k₀ + 1 : ℝ) * n - D_r * ε * n := by
        have h1 : (Nat.card (Compiler.InnerGate c) : ℝ) ≤ (Q_c - ε) * n := hG_le_s.trans hsize
        have h2 := mul_le_mul_of_nonneg_left h1 hDr_pos.le
        have hexp : D_r * ((Q_c - ε) * n) = D_r * Q_c * n - D_r * ε * n := by ring
        rw [hexp, hDr_Qc] at h2
        exact h2
      have hdiv_eq : μ₀ * n - 1 / (2 : ℝ) ^ k₀ = ((D_r * ε / 2) * n - 1) / (2 : ℝ) ^ k₀ := by
        dsimp only [μ₀]
        field_simp
      rw [hdiv_eq]
      refine div_le_div_of_nonneg_right ?_ hpos2.le
      have hRin_eq : (k₀ + 1 : ℝ) * R_in.ncard = (k₀ + 1 : ℝ) * n - (k₀ + 1 : ℝ) * d_un := by
        linarith [congrArg ((k₀ + 1 : ℝ) * ·) hcompl_in]
      linarith
    -- Bound the `O(√n)` deviation term.
    have herr_ub : 2 * ((r + 1 : ℝ) * √(3 * (Nat.card (Compiler.Node c) : ℝ))) ≤ (μ / 8) * n := by
      have hs_qc : (c.innerSize : ℝ) ≤ Q_c * n := by
        have hεn : 0 ≤ ε * n := by positivity
        linarith
      have hnode_le : (Nat.card (Compiler.Node c) : ℝ) ≤ (Q_c + 1) * n := by
        have hnat : (Nat.card (Compiler.Node c) : ℝ) ≤ c.innerSize + 1 := by
          exact_mod_cast (Compiler.card_node_le c)
        linarith
      have hdev1 : 2 * ((r + 1 : ℝ) * √(3 * (Nat.card (Compiler.Node c) : ℝ))) ≤ C_err * √n := by
        have h3 : 3 * (Nat.card (Compiler.Node c) : ℝ) ≤ (3 * (Q_c + 1)) * n := by linarith
        calc 2 * ((r + 1 : ℝ) * √(3 * (Nat.card (Compiler.Node c) : ℝ)))
            ≤ 2 * ((r + 1 : ℝ) * √((3 * (Q_c + 1)) * n)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h3)
                (by positivity)) (by norm_num)
          _ = C_err * √n := by
              rw [Real.sqrt_mul (by positivity)]
              dsimp only [C_err]
              ring
      have hsq_n : (8 * C_err / μ) ^ 2 ≤ n := by
        have : (⌈(8 * C_err / μ) ^ 2⌉₊ : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_succ_le hn_sqrt)
        exact (Nat.le_ceil _).trans this
      have hsqrt_lb : 8 * C_err / μ ≤ √n := Real.le_sqrt_of_sq_le hsq_n
      have hCerr_le : C_err ≤ (μ / 8) * √n := by
        have := (div_le_iff₀ hμ_pos).mp hsqrt_lb
        linarith
      calc 2 * ((r + 1 : ℝ) * √(3 * (Nat.card (Compiler.Node c) : ℝ)))
          ≤ C_err * √n := hdev1
        _ ≤ ((μ / 8) * √n) * √n := mul_le_mul_of_nonneg_right hCerr_le (Real.sqrt_nonneg _)
        _ = (μ / 8) * n := by rw [mul_assoc, Real.mul_self_sqrt hn0]
    -- Combine into `min |L| |R'| - |G_cut|` and apply `sq_correlation_quadForm_mul_le_of_node_cut`.
    have hmin_LR :
        μ₀ * n - 1 / (2 : ℝ) ^ k₀ - (μ / 8) * n ≤
          (min L.ncard R'.ncard : ℝ) - G_cut.ncard := by
      have hmin_real : (min L.ncard R'.ncard : ℝ) = min (L.ncard : ℝ) (R'.ncard : ℝ) := by
        exact_mod_cast rfl
      rw [hmin_real]
      rcases min_choice (L.ncard : ℝ) (R'.ncard : ℝ) with hm | hm <;> rw [hm]
      · linarith [hLA, hGA, hexp_diff, hnum_lb, herr_ub]
      · linarith [hRA, hGA, hexp_diff, hnum_lb, herr_ub]
    have hrank_lb : min L.ncard R'.ncard ≤ (Q n + (Q n)ᵀ).blockRank L R' + t n :=
      hQn.min_le hLR_disj
    have hcorr_cut := sq_correlation_quadForm_mul_le_of_node_cut I Acc c (Q n) A
    have hstep := le_rpow_of_mul_two_pow_le hcorr_cut
      (r := (min L.ncard R'.ncard : ℝ) - t n) (by
        have : (min L.ncard R'.ncard : ℝ) ≤ (Q n + (Q n)ᵀ).blockRank L R' + t n := by
          exact_mod_cast hrank_lb
        linarith)
    refine hstep.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hpow2_le : 1 / (2 : ℝ) ^ k₀ ≤ 1 := div_le_one_of_le₀
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (by positivity)
    have hμ_le_μ₀ : μ ≤ μ₀ := min_le_right _ _
    have hμn_le : μ * n ≤ μ₀ * n := mul_le_mul_of_nonneg_right hμ_le_μ₀ hn0
    dsimp only [L, R', G_cut] at hmin_LR
    linarith

/-- The deficiency `2 ⌊√n⌋ + 1` of `Matrix.symmHardForm` is `o(n)`. -/
theorem isLittleO_sqrt_deficiency :
    (fun n : ℕ => ((2 * Nat.sqrt n + 1 : ℕ) : ℝ)) =o[atTop] fun n => (n : ℝ) := by
  refine IsLittleO.of_bound fun δ hδ => ?_
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈9 / δ ^ 2⌉₊] with n hn1 hnC
  have hs_pos : 1 ≤ Nat.sqrt n := by
    have h := Nat.lt_succ_sqrt' n
    rw [Nat.succ_eq_add_one] at h
    by_contra h0
    have hs0 : Nat.sqrt n = 0 := by omega
    rw [hs0] at h
    omega
  have h2s : ((2 * Nat.sqrt n + 1 : ℕ) : ℝ) ≤ 3 * (Nat.sqrt n : ℝ) := by
    exact_mod_cast (show 2 * Nat.sqrt n + 1 ≤ 3 * Nat.sqrt n by omega)
  have hsq_le : ((Nat.sqrt n : ℝ)) * (Nat.sqrt n : ℝ) ≤ n := by
    exact_mod_cast Nat.sqrt_le n
  have hnC' : 9 / δ ^ 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnC)
  have h9 : 9 ≤ δ ^ 2 * n := by
    have h := (div_le_iff₀ (show (0 : ℝ) < δ ^ 2 by positivity)).mp hnC'
    linarith
  set x : ℝ := ((2 * Nat.sqrt n + 1 : ℕ) : ℝ)
  set y : ℝ := δ * n
  have hy_pos : 0 < y := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    positivity
  have hx_nn : 0 ≤ x := Nat.cast_nonneg _
  have hxy_sq : x ^ 2 ≤ y ^ 2 := by
    calc x ^ 2 ≤ (3 * (Nat.sqrt n : ℝ)) ^ 2 := pow_le_pow_left₀ hx_nn h2s 2
      _ = 9 * ((Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ)) := by ring
      _ ≤ 9 * (n : ℝ) := mul_le_mul_of_nonneg_left hsq_le (by norm_num)
      _ ≤ (δ ^ 2 * n) * n := mul_le_mul_of_nonneg_right h9 (Nat.cast_nonneg _)
      _ = y ^ 2 := by dsimp only [y]; ring
  have hxy : x ≤ y := by
    by_contra hlt
    push Not at hlt
    have : y ^ 2 < x ^ 2 := by nlinarith
    linarith
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  rw [abs_of_nonneg hx_nn]
  exact hxy

/-- **Unconditional correlation bound against `Matrix.symmHardForm`.** For every `r ≥ 2`, `k₀ ≥ 1`,
and `ε > 0`, some `γ > 0` bounds the correlation of `BitString.quadForm (Matrix.symmHardForm n)`
with every circuit of fan-in at most `r` and at most
`(quadFormGateSweepCoefficient r k₀ - ε) n` inner gates by `2 ^ (-γ n)`. -/
theorem exists_eventually_abs_correlation_symmHardForm_le_gateSweep {r k₀ : ℕ} (hr : 2 ≤ r)
    (hk₀ : 1 ≤ k₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ n 1), c.FanInAtMost r →
          (c.innerSize : ℝ) ≤ (quadFormGateSweepCoefficient r k₀ - ε) * n →
          |correlation {x | BitString.quadForm (Matrix.symmHardForm n) x}
            {x | c.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨γ, hγ, H⟩ := exists_eventually_abs_correlation_quadForm_le_gateSweep.{v} hr hk₀ hε
  exact ⟨γ, hγ, H Matrix.symmHardForm (fun n => 2 * Nat.sqrt n + 1)
    (Eventually.of_forall Matrix.disjointBlockRobust_symmHardForm) isLittleO_sqrt_deficiency⟩

/-- Explicit `Ω(log r)` choice of `k₀ ≥ 1` for `quadFormGateSweepCoefficient`: for all `r ≥ 2`,
some `k₀ ≥ 1` satisfies `log₂ r - log₂ log₂ r - 2 ≤ (r - 1) · quadFormGateSweepCoefficient r k₀`. -/
theorem exists_log_sub_log_log_le_mul_quadFormGateSweepCoefficient {r : ℕ} (hr : 2 ≤ r) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧
      Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 2 ≤
        (r - 1 : ℝ) * quadFormGateSweepCoefficient r k₀ := by
  rcases lt_or_ge r 4 with hsmall | hr4
  · refine ⟨1, le_rfl, ?_⟩
    have hr_cases : r = 2 ∨ r = 3 := by omega
    rcases hr_cases with rfl | rfl
    · rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) ^ (1 : ℕ) by norm_num, Real.logb_two_pow, Nat.cast_one,
        Real.logb_one]
      unfold quadFormGateSweepCoefficient
      norm_num
    · have hlog3_ge : 1 ≤ Real.logb 2 (3 : ℝ) := by
        rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
      have hlog3_le : Real.logb 2 (3 : ℝ) ≤ 2 := by
        calc Real.logb 2 (3 : ℝ)
            ≤ Real.logb 2 ((2 : ℝ) ^ (2 : ℕ)) :=
              Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by norm_num)
          _ = 2 := by rw [Real.logb_two_pow]; norm_num
      have hll_nn : 0 ≤ Real.logb 2 (Real.logb 2 (3 : ℝ)) :=
        Real.logb_nonneg (by norm_num) hlog3_ge
      have hrhs : ((3 : ℕ) - 1 : ℝ) * quadFormGateSweepCoefficient 3 1 = 4 / 3 := by
        unfold quadFormGateSweepCoefficient
        norm_num
      push_cast at hrhs ⊢
      linarith
  · set ℓ := Nat.log 2 r
    have hℓ2 : 2 ≤ ℓ := by
      have : Nat.log 2 4 ≤ Nat.log 2 r := Nat.log_mono_right hr4
      have h4 : Nat.log 2 4 = 2 := by decide
      omega
    have hpow_ℓ : 2 ^ ℓ ≤ r := Nat.pow_log_le_self 2 (by omega)
    have hℓ_lt_pow : ℓ < 2 ^ ℓ := ℓ.lt_two_pow_self
    have hdiv_ge2 : 2 ≤ r / ℓ := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      rcases eq_or_lt_of_le hℓ2 with h2 | h3
      · rw [← h2]
        omega
      · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h3) with h3' | h4'
        · have hℓ3 : ℓ = 3 := h3'.symm
          have h8 : 2 ^ 3 ≤ r := by rw [← hℓ3]; exact hpow_ℓ
          omega
        · have h2ℓ : 2 * ℓ ≤ 2 ^ ℓ := by
            clear hpow_ℓ hℓ_lt_pow hr4 hℓ2 h3
            induction ℓ, Nat.succ_le_of_lt h4' using Nat.le_induction with
            | base => decide
            | succ m hm ih =>
              rw [pow_succ']
              omega
          exact h2ℓ.trans hpow_ℓ
    set k₀ := Nat.log 2 (r / ℓ)
    have hk₀1 : 1 ≤ k₀ := by
      have : Nat.log 2 2 ≤ Nat.log 2 (r / ℓ) := Nat.log_mono_right hdiv_ge2
      have h2 : Nat.log 2 2 = 1 := by decide
      omega
    refine ⟨k₀, hk₀1, ?_⟩
    have hk₀_le_r : 2 ^ k₀ * ℓ ≤ r := by
      have h := Nat.pow_log_le_self 2 (show r / ℓ ≠ 0 by omega)
      exact (Nat.mul_le_mul_right ℓ h).trans (Nat.div_mul_le_self r ℓ)
    have hr_lt_succ : r < 2 ^ (k₀ + 1) * ℓ := by
      have h : r / ℓ < 2 ^ (k₀ + 1) := by
        simpa [k₀, Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (b := 2) (by decide) (r / ℓ)
      have hdiv := Nat.div_add_mod r ℓ
      have hmod : r % ℓ < ℓ := Nat.mod_lt r (by omega)
      nlinarith
    have hℓ_le_log : (ℓ : ℝ) ≤ Real.logb 2 r := by
      rw [← Real.logb_two_pow ℓ]
      exact Real.logb_le_logb_of_le (by norm_num) (by positivity) (by exact_mod_cast hpow_ℓ)
    have hlog_r_le : Real.logb 2 r ≤ (k₀ : ℝ) + 1 + Real.logb 2 ℓ := by
      have hr_le_real : (r : ℝ) ≤ (2 : ℝ) ^ (k₀ + 1) * ℓ := by exact_mod_cast hr_lt_succ.le
      calc Real.logb 2 r
          ≤ Real.logb 2 ((2 : ℝ) ^ (k₀ + 1) * ℓ) :=
            Real.logb_le_logb_of_le (by norm_num) (by positivity) hr_le_real
        _ = (k₀ : ℝ) + 1 + Real.logb 2 ℓ := by
            rw [Real.logb_mul (by positivity) (by positivity), Real.logb_two_pow]
            push_cast
            ring
    have hll_mono : Real.logb 2 ℓ ≤ Real.logb 2 (Real.logb 2 r) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) hℓ_le_log
    have hk₀_alg : (k₀ - 1 : ℝ) ≤ (r - 1 : ℝ) * quadFormGateSweepCoefficient r k₀ := by
      unfold quadFormGateSweepCoefficient
      have hd_pos : (0 : ℝ) < (r : ℝ) + (2 : ℝ) ^ k₀ - k₀ - 1 := by
        have h1 := quadFormGateSweep_denom_ge r k₀
        have h2 : (4 : ℝ) ≤ r := by exact_mod_cast hr4
        linarith
      rw [mul_div_assoc', le_div_iff₀ hd_pos]
      have hk₀_le_ℓ : k₀ ≤ ℓ := by
        by_contra hgt
        push Not at hgt
        have : r < 2 ^ k₀ * ℓ := by
          have h : r < 2 ^ (ℓ + 1) := by
            simpa [ℓ, Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (b := 2) (by decide) r
          have h2 : 2 ^ (ℓ + 1) ≤ 2 ^ k₀ := Nat.pow_le_pow_right (by decide) hgt
          have hℓ2' : 2 ≤ ℓ := hℓ2
          nlinarith
        omega
      have hk₀_pow_le_r : (k₀ : ℝ) * (2 : ℝ) ^ k₀ ≤ r := by
        have hnat : k₀ * 2 ^ k₀ ≤ r := by
          calc k₀ * 2 ^ k₀ ≤ ℓ * 2 ^ k₀ := Nat.mul_le_mul_right _ hk₀_le_ℓ
            _ = 2 ^ k₀ * ℓ := mul_comm _ _
            _ ≤ r := hk₀_le_r
        exact_mod_cast hnat
      have hk₀1_r : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀1
      have hr4_r : (4 : ℝ) ≤ r := by exact_mod_cast hr4
      nlinarith [sq_nonneg ((k₀ : ℝ) - 1)]
    linarith

/-- **Unconditional `Ω(log r)` quadratic-form correlation bound.** For every `r ≥ 2` and `ε > 0`,
some `γ > 0` ensures that every circuit of fan-in at most `r` with
`(r - 1) * c.innerSize ≤ (log₂ r - log₂ log₂ r - 2 - ε) * n` has correlation at most `2 ^ (-γ n)`
with `BitString.quadForm (Matrix.symmHardForm n)`. -/
theorem exists_eventually_abs_correlation_symmHardForm_le_log {r : ℕ} (hr : 2 ≤ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop,
      ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
        (c : Circuit σ n 1), c.FanInAtMost r →
          ((r - 1 : ℝ) * c.innerSize) ≤
            (Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 2 - ε) * n →
          |correlation {x | BitString.quadForm (Matrix.symmHardForm n) x}
            {x | c.eval I x 0 ∈ Acc}| ≤ (2 : ℝ) ^ (-γ * n) := by
  obtain ⟨k₀, hk₀1, hk₀_le⟩ := exists_log_sub_log_log_le_mul_quadFormGateSweepCoefficient hr
  have hr1_pos : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  obtain ⟨γ, hγ, H⟩ := exists_eventually_abs_correlation_symmHardForm_le_gateSweep.{v} hr hk₀1
    (ε := ε / (r - 1 : ℝ)) (div_pos hε hr1_pos)
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [H] with n hn σ I Acc c hfan hsize
  refine hn σ I Acc c hfan ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmul : (r - 1 : ℝ) * c.innerSize ≤
      (r - 1 : ℝ) * ((quadFormGateSweepCoefficient r k₀ - ε / (r - 1 : ℝ)) * n) := by
    have hsub :
        Real.logb 2 r - Real.logb 2 (Real.logb 2 r) - 2 - ε ≤
          (r - 1 : ℝ) * (quadFormGateSweepCoefficient r k₀ - ε / (r - 1 : ℝ)) := by
      have hid : (r - 1 : ℝ) * (ε / (r - 1 : ℝ)) = ε := mul_div_cancel₀ ε hr1_pos.ne'
      linarith
    exact hsize.trans ((mul_le_mul_of_nonneg_right hsub hn0).trans_eq (mul_assoc _ _ _))
  exact le_of_mul_le_mul_left hmul hr1_pos

end Cslib.Circuits.Frontier
