/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.CubePoints
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Basic
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.UnitExponent
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Fan
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Price.Random
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# The unit exponent at the centres of the facets of a cube

In the flat case, the centres `±½ e_d` of some facets of the cube `[-½, ½] ^ k` have a spectral
point whose scaled wire exponents are the Euclidean distances up to `ε`, and whose scaled unit
exponent at these centres is at most `√k + ε` (`Flat.exists_spectralPoint_cube`, Proposition
E.9 of [AnthropicVPVNP2026], p. 36).

The proof moves the centres in `k` steps from a main diagonal of the cube, where the unit exponent
is at most the distance `√k` of two opposite vertices, by taking pointwise midpoints. Along a
midpoint the scaled unit exponent is convex up to a small error (Lemma E.8, p. 35): a new party is
placed half at each end by Proposition A.7 (`SpectralPoint.exists_extend_keep`), and the curvature
bound for prices (Theorem C.1, `isPrice_sq_le_of_mid`) bounds its distance from the midpoint.

## Main results

* `Flat.exists_spectralPoint_cube`: Proposition E.9.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Section E.5, Lemma E.8, p. 35, and Proposition E.9, p. 36; module `Paper.Convex`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Flat

open Finset Cslib.PartyTensor Cslib.Circuits.Arithmetic.Separation.TwoCases

variable {K : Type} [Field K]

section Mix

variable {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]

/-- A power of two below the geometric mean of two powers of two. -/
private theorem le_mean_of_two_rpow_le {r s t : ℝ}
    (h : (2 : ℝ) ^ r ≤ ∏ l : Fin 2, ((2 : ℝ) ^ (![s, t] l)) ^ (1 / 2 : ℝ)) : r ≤ (s + t) / 2 := by
  rw [Fin.prod_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    at h
  linarith [(Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).1 h]

/-- A spectral point `F` over `V` extends to `F'` with a new party for every element of `A`,
placed half at `a` and half at `b`. The wire exponents and the unit exponent at `m` stay; the wire
exponents of the new parties and their unit exponent are at most the means for `F`. -/
private theorem exists_mix [Nonempty V] (F : SpectralPoint K V) (a b m : A → V) :
    ∃ F' : SpectralPoint K (V ⊕ A),
      (∀ p p', F'.wireExponent (Sum.inl p) (Sum.inl p') = F.wireExponent p p') ∧
      F'.unitExponent (Sum.inl ∘ m) = F.unitExponent m ∧
      (∀ x y, F'.wireExponent x y ≤ (F.wireExponent (Sum.elim id a x) (Sum.elim id a y) +
        F.wireExponent (Sum.elim id b x) (Sum.elim id b y)) / 2) ∧
      F'.unitExponent Sum.inr ≤ (F.unitExponent a + F.unitExponent b) / 2 := by
  obtain ⟨F', hle, hd, he, hC⟩ := F.exists_extend_keep (fun _ : Fin 2 => (1 / 2 : ℝ))
    (fun _ => by norm_num) (by norm_num) ![a, b] (push m (unit K A 2))
    (lt_of_lt_of_le one_pos (F.toUpperFunctional.one_le_unit m (by norm_num)))
  refine ⟨F', he, ?_, fun x y => (hd x y).trans_eq ?_, ?_⟩
  · simp only [SpectralPoint.unitExponent]
    rw [← F'.congr (antisymmRel_push_push Sum.inl m _), hC]
  · simp [Fin.sum_univ_two]
    ring
  · have h := hle (push Sum.inr (unit K A 2))
    rw [F'.apply_push_unit_two] at h
    refine le_mean_of_two_rpow_le (h.trans_eq (Finset.prod_congr rfl fun l _ => ?_))
    rw [F.congr (antisymmRel_push_push _ _ _), F.apply_push_unit_two]
    fin_cases l <;> rfl

end Mix

section Midpoints

variable {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]

/-- If `v` is a midpoint of `x` and `y` for a price `w` and `z` is at most `w x y / 2 + δ` from
`x` and from `y`, then `w z v ^ 2 ≤ w x y δ + δ ^ 2`, by the curvature bound (Theorem C.1). -/
private theorem sq_dist_midpoint_le {Y : Type} {w : Y → Y → ℝ} (hw : IsPrice K w) {x y v z : Y}
    {δ : ℝ} (hx : w x v ≤ w x y / 2) (hy : w y v ≤ w x y / 2) (hzx : w z x ≤ w x y / 2 + δ)
    (hzy : w z y ≤ w x y / 2 + δ) : w z v ^ 2 ≤ w x y * δ + δ ^ 2 := by
  have h := Curvature.isPrice_sq_le_of_mid hw x y v z hx hy (by ring)
  have h3 : w z x ^ 2 ≤ (w x y / 2 + δ) ^ 2 := pow_le_pow_left₀ (hw.nonneg z x) hzx 2
  have h4 : w z y ^ 2 ≤ (w x y / 2 + δ) ^ 2 := pow_le_pow_left₀ (hw.nonneg z y) hzy 2
  nlinarith

/-- If, for the scaled wire exponents `c d_F`, every `m v` is a midpoint of `a v` and `b v` up to
`δ`, then the scaled unit exponent at `m` is at most the mean of those at `a` and `b`, up to the
sum of the numbers `√(c d_F(a v, b v) δ + δ ^ 2)`. -/
private theorem unitExponent_le_mean_add (F : SpectralPoint K V) {c : ℝ} (hc : 0 ≤ c)
    (a b m : A → V) {δ : ℝ}
    (ha : ∀ v, c * F.wireExponent (m v) (a v) ≤ c * F.wireExponent (a v) (b v) / 2 + δ)
    (hb : ∀ v, c * F.wireExponent (m v) (b v) ≤ c * F.wireExponent (a v) (b v) / 2 + δ) :
    c * F.unitExponent m ≤ (c * F.unitExponent a + c * F.unitExponent b) / 2 +
      ∑ v, √(c * F.wireExponent (a v) (b v) * δ + δ ^ 2) := by
  rcases isEmpty_or_nonempty A with hA | ⟨⟨v₀⟩⟩
  · rw [Subsingleton.elim a m, Subsingleton.elim b m]
    simp
  have : Nonempty V := ⟨m v₀⟩
  obtain ⟨F', he, hm, hd, hg⟩ := exists_mix F a b m
  have hw : IsPrice K fun x y => c * F'.wireExponent x y := (isPrice_wireExponent F').smul hc
  -- the new party `v` is close to `m v`
  have hclose (v : A) : c * F'.wireExponent (Sum.inl (m v)) (Sum.inr v) ≤
      √(c * F.wireExponent (a v) (b v) * δ + δ ^ 2) := by
    refine Real.le_sqrt_of_sq_le ?_
    have h := sq_dist_midpoint_le hw (x := Sum.inl (a v)) (y := Sum.inl (b v)) (v := Sum.inr v)
      (z := Sum.inl (m v)) (δ := δ) ?_ ?_ ?_ ?_
    · simpa only [he] using h
    · have := mul_le_mul_of_nonneg_left (hd (Sum.inl (a v)) (Sum.inr v)) hc
      simp only [Sum.elim_inl, Sum.elim_inr, id, F.wireExponent_self, he] at this ⊢
      linarith
    · have := mul_le_mul_of_nonneg_left (hd (Sum.inl (b v)) (Sum.inr v)) hc
      simp only [Sum.elim_inl, Sum.elim_inr, id, F.wireExponent_self,
        F.wireExponent_comm (b v) (a v), he] at this ⊢
      linarith
    · simpa only [he] using ha v
    · simpa only [he] using hb v
  have h1 := F'.unitExponent_le_move (Sum.inl ∘ m) Sum.inr
  rw [hm] at h1
  calc c * F.unitExponent m
      ≤ c * (F'.unitExponent Sum.inr + ∑ v, F'.wireExponent ((Sum.inl ∘ m) v) (Sum.inr v)) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ = c * F'.unitExponent Sum.inr + ∑ v, c * F'.wireExponent (Sum.inl (m v)) (Sum.inr v) := by
        rw [mul_add, Finset.mul_sum]
        rfl
    _ ≤ c * ((F.unitExponent a + F.unitExponent b) / 2) +
          ∑ v, √(c * F.wireExponent (a v) (b v) * δ + δ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hg hc) (Finset.sum_le_sum fun v _ => hclose v)
    _ = _ := by ring

variable (K) (A) in
/-- Let `w` be a function on the pairs of a finite set `V`. For every `ε > 0` there is `δ > 0`
such that for a spectral point `F` and a scale `c ≥ 0` with `c d_F` within `δ` of `w`, and maps
`a`, `b`, `m` with every `m v` a midpoint of `a v` and `b v` for `w`, the scaled unit exponent at
`m` is at most the mean of those at `a` and `b`, plus `ε`. -/
private theorem unitExponent_convex (w : V → V → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (F : SpectralPoint K V) (c : ℝ), 0 ≤ c →
      (∀ u v, |w u v - c * F.wireExponent u v| < δ) → ∀ a b m : A → V,
        (∀ v, w (m v) (a v) ≤ w (a v) (b v) / 2) → (∀ v, w (m v) (b v) ≤ w (a v) (b v) / 2) →
          c * F.unitExponent m ≤ (c * F.unitExponent a + c * F.unitExponent b) / 2 + ε := by
  set R : ℝ := ∑ u, ∑ v, |w u v|
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => abs_nonneg _
  have hwR (u v : V) : w u v ≤ R :=
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun v => |w u v|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ v)).trans (Finset.single_le_sum (f := fun u => ∑ v, |w u v|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ u)))
  set n : ℝ := (Fintype.card A : ℝ) with hn
  have hden : 0 < (n ^ 2 + 1) * (2 * R + 4) := by positivity
  refine ⟨min 1 (ε ^ 2 / ((n ^ 2 + 1) * (2 * R + 4))), lt_min one_pos (by positivity), ?_⟩
  intro F c hc hF a b m ha hb
  set δ : ℝ := min 1 (ε ^ 2 / ((n ^ 2 + 1) * (2 * R + 4)))
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ * ((n ^ 2 + 1) * (2 * R + 4)) ≤ ε ^ 2 := (le_div_iff₀ hden).1 (min_le_right _ _)
  have key := unitExponent_le_mean_add F hc a b m (δ := 3 / 2 * δ)
    (fun v => by
      linarith [(abs_lt.1 (hF (m v) (a v))).1, (abs_lt.1 (hF (a v) (b v))).2, ha v])
    (fun v => by
      linarith [(abs_lt.1 (hF (m v) (b v))).1, (abs_lt.1 (hF (a v) (b v))).2, hb v])
  refine key.trans (add_le_add le_rfl ?_)
  have hterm (v : A) : √(c * F.wireExponent (a v) (b v) * (3 / 2 * δ) + (3 / 2 * δ) ^ 2) ≤
      √(δ * (2 * R + 4)) := by
    refine Real.sqrt_le_sqrt ?_
    have h3 : c * F.wireExponent (a v) (b v) ≤ R + 1 := by
      linarith [(abs_lt.1 (hF (a v) (b v))).1, hwR (a v) (b v)]
    nlinarith
  refine (Finset.sum_le_sum fun v _ => hterm v).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
  refine (Real.le_sqrt_of_sq_le ?_).trans (Real.sqrt_sq hε.le).le
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith [mul_nonneg hδ0.le (by positivity : 0 ≤ 2 * R + 4)]

variable (K) in
/-- **Lemma E.8.** For a finite `V ⊆ ℝⁿ`, maps `a`, `b`, `m` from `I` to `V` with every
`m i` the midpoint of `a i` and `b i`, and `ε > 0`, there is `δ > 0` such that for every spectral
point `F` on `V` and `c ≥ 0` with `|c d_F(x, y) - ‖x - y‖| < δ` on `V`, the scaled unit exponent
at `m` is at most the mean of those at `a` and at `b`, plus `ε`. -/
private theorem unitExponent_midpoint_le {n : ℕ} (V : Finset (EuclideanSpace ℝ (Fin n)))
    (I : Type) [Fintype I] [DecidableEq I] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (F : SpectralPoint K V) (c : ℝ), 0 ≤ c →
      (∀ x y : V, |c * F.wireExponent x y - dist x y| < δ) → ∀ a b m : I → V,
        (∀ i, (m i : EuclideanSpace ℝ (Fin n)) = midpoint ℝ (a i).1 (b i).1) →
          c * F.unitExponent m ≤ 1 / 2 * (c * F.unitExponent a) + 1 / 2 * (c * F.unitExponent b) +
            ε := by
  classical
  obtain ⟨δ, hδ, h⟩ := unitExponent_convex K I (fun x y : V => dist x y) hε
  refine ⟨δ, hδ, fun F c hc hd a b m hm => ?_⟩
  have := h F c hc (fun x y => by rw [abs_sub_comm]; exact hd x y) a b m
    (fun i => le_of_eq ?_) (fun i => le_of_eq ?_)
  · linarith
  · rw [Subtype.dist_eq, Subtype.dist_eq, hm, dist_midpoint_left, Real.norm_ofNat]
    ring
  · rw [Subtype.dist_eq, Subtype.dist_eq, hm, dist_midpoint_right, Real.norm_ofNat]
    ring

end Midpoints

section Cube

/-- The sign vectors `α_χ` of the proof of Proposition E.9 at level `j`: the centre `±½ e_d`
(the sign `s`) stays where it is if `d < j`, and otherwise goes to `±½ χ_d (0, …, 0, χ)` with `j`
zeros. -/
private def cubeSign {k : ℕ} (j : ℕ) (χ : Fin k → Bool) (d : Fin k) (s : Bool) : Fin k → SignType :=
  fun x => if d.1 < j then (if x = d then boolSign s else 0) else
    (if x.1 < j then 0 else boolSign s * boolSign (χ d) * boolSign (χ x))

/-- At level `0` the image lies on a main diagonal of the cube. -/
private theorem cubeSign_zero {k : ℕ} (χ : Fin k → Bool) (d : Fin k) (s : Bool) :
    cubeSign 0 χ d s = (fun x => boolSign (χ x)) ∨ cubeSign 0 χ d s = fun x => -boolSign (χ x) := by
  unfold cubeSign
  cases s <;> cases χ d
  · left; funext x; cases χ x <;> simp [boolSign]
  · right; funext x; cases χ x <;> simp [boolSign]
  · right; funext x; cases χ x <;> simp [boolSign]
  · left; funext x; cases χ x <;> simp [boolSign]

/-- At level `k` every centre stays where it is. -/
private theorem cubePoint_cubeSign_top {k : ℕ} (χ : Fin k → Bool) (d : Fin k) (s : Bool) :
    cubePoint (cubeSign k χ d s) =
      (if s then (1 / 2 : ℝ) else -(1 / 2)) • EuclideanSpace.single d (1 : ℝ) := by
  ext x
  rw [cubePoint_apply]
  by_cases hx : x = d <;> cases s <;> simp [cubeSign, boolSign, hx, neg_div]

/-- At level `j + 1` the point is the midpoint of the two points of level `j` for the two values
of `χ` at `j`. -/
private theorem cubePoint_cubeSign_succ {k j : ℕ} (hj : j < k) (χ : Fin k → Bool) (d : Fin k)
    (s : Bool) :
    cubePoint (cubeSign (j + 1) χ d s) =
      midpoint ℝ (cubePoint (cubeSign j (Function.update χ ⟨j, hj⟩ true) d s))
        (cubePoint (cubeSign j (Function.update χ ⟨j, hj⟩ false) d s)) := by
  have key (x : Fin k) : ((cubeSign (j + 1) χ d s x : SignType) : ℝ) =
      (((cubeSign j (Function.update χ ⟨j, hj⟩ true) d s x : SignType) : ℝ) +
        ((cubeSign j (Function.update χ ⟨j, hj⟩ false) d s x : SignType) : ℝ)) / 2 := by
    unfold cubeSign
    by_cases h1 : d.1 < j
    · simp [h1, h1.trans (Nat.lt_succ_self j)]
    · by_cases h2 : d = ⟨j, hj⟩
      · subst h2
        by_cases h3 : x.1 < j
        · have : x ≠ ⟨j, hj⟩ := fun h => h3.ne (congrArg Fin.val h)
          simp [h3, this]
        · by_cases h4 : x = ⟨j, hj⟩
          · subst h4
            cases s <;> simp [boolSign]
          · cases s <;> simp [h3, h4, boolSign] <;> cases χ x <;> simp
      · have h2' : ¬ d.1 < j + 1 := fun h => h2 (Fin.ext (show d.1 = j by omega))
        by_cases h3 : x.1 < j
        · simp [h1, h2', h3, h3.trans (Nat.lt_succ_self j)]
        · by_cases h4 : x = ⟨j, hj⟩
          · subst h4
            cases s <;> cases χ d <;> simp [h1, h2, h2', boolSign]
          · have h4' : ¬ x.1 < j + 1 := fun h => h4 (Fin.ext (show x.1 = j by omega))
            simp [h1, h2, h2', h3, h4, h4']
  ext x
  rw [midpoint_eq_smul_add]
  simp only [PiLp.smul_apply, PiLp.add_apply, cubePoint_apply, smul_eq_mul, key, invOf_eq_inv]
  ring

/-- **Proposition E.9.** In the flat case, let `V ⊆ ℝᵏ` be finite and `P ⊆ V` a nonempty set
of centres `±½ e_d` of facets of the cube. For every `ε > 0` there are a spectral point `F` on `V`
and `c ≥ 0` with `|c d_F(x, y) - ‖x - y‖| < ε` on `V` and `c · g(P) ≤ √k + ε`, where `g(P)` is the
unit exponent at `P`. -/
theorem exists_spectralPoint_cube (hK : FlatCase K) {k : ℕ} (V : Finset (EuclideanSpace ℝ (Fin k)))
    (P : Finset (EuclideanSpace ℝ (Fin k))) (hPV : P ⊆ V) (hP : P.Nonempty)
    (hc : ∀ x ∈ P, ∃ (j : Fin k) (b : Bool),
      x = (if b then (1 / 2 : ℝ) else -(1 / 2)) • EuclideanSpace.single j 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : SpectralPoint K V) (c : ℝ), 0 ≤ c ∧
      (∀ x y : V, |c * F.wireExponent x y - dist x y| < ε) ∧
      c * F.unitExponent (fun x : P => (⟨x.1, hPV x.2⟩ : V)) ≤ √k + ε := by
  classical
  have : Nonempty P := hP.coe_sort
  have hk : 0 < k := (hc hP.choose hP.choose_spec).choose.pos
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  choose j b hjb using fun x : P => hc x.1 x.2
  -- add the points `½ u` of the cube
  let V' : Finset (EuclideanSpace ℝ (Fin k)) := V ∪ univ.image cubePoint
  let incl : V → V' := fun x => ⟨x.1, mem_union_left _ x.2⟩
  let pt : (Fin k → SignType) → V' :=
    fun u => ⟨cubePoint u, mem_union_right _ (mem_image_of_mem _ (mem_univ u))⟩
  have : Nonempty V' := ⟨pt fun _ => 0⟩
  obtain ⟨δ, hδ, hconv⟩ := unitExponent_midpoint_le K V' P (show 0 < ε / (2 * k) by positivity)
  obtain ⟨F, c, hc0, hF⟩ := (hK k V' fun x => x.1).exists_spectralPoint id
    (show 0 < min δ (ε / 2) by positivity)
  have hF' (x y : V') : |c * F.wireExponent x y - dist x y| < min δ (ε / 2) := by
    simpa only [abs_sub_comm, Subtype.dist_eq, id_eq] using hF x y
  let α : ℕ → (Fin k → Bool) → P → V' := fun i χ x => pt (cubeSign i χ (j x) (b x))
  have hlevel : ∀ i ≤ k, ∀ χ, c * F.unitExponent (α i χ) ≤ √k + ε / 2 + i * (ε / (2 * k)) := by
    intro i
    induction i with
    | zero =>
      intro _ χ
      have h1 := F.unitExponent_le_of_two (α 0 χ) (pt fun x => boolSign (χ x))
        (pt fun x => -boolSign (χ x)) fun x =>
          (cubeSign_zero χ (j x) (b x)).imp (congrArg pt) (congrArg pt)
      have h2 := (abs_lt.1 (hF' (pt fun x => boolSign (χ x)) (pt fun x => -boolSign (χ x)))).2
      rw [Subtype.dist_eq, dist_cubePoint_neg] at h2
      have h3 := mul_le_mul_of_nonneg_left h1 hc0
      simp only [Nat.cast_zero, zero_mul, add_zero]
      linarith [min_le_right δ (ε / 2)]
    | succ i ih =>
      intro hi χ
      have h1 := hconv F c hc0 (fun x y => (hF' x y).trans_le (min_le_left _ _))
        (α i (Function.update χ ⟨i, hi⟩ true)) (α i (Function.update χ ⟨i, hi⟩ false))
        (α (i + 1) χ) fun x => cubePoint_cubeSign_succ hi χ (j x) (b x)
      have h2 := ih (Nat.le_of_succ_le hi) (Function.update χ ⟨i, hi⟩ true)
      have h3 := ih (Nat.le_of_succ_le hi) (Function.update χ ⟨i, hi⟩ false)
      push_cast
      linarith
  refine ⟨F.pull incl, c, hc0, fun x y => ?_, ?_⟩
  · rw [F.pull_wireExponent, Subtype.dist_eq]
    exact (hF' (incl x) (incl y)).trans_le ((min_le_right _ _).trans (by linarith))
  · have e : incl ∘ (fun x : P => (⟨x.1, hPV x.2⟩ : V)) = α k fun _ => true :=
      funext fun x => Subtype.ext ((hjb x).trans (cubePoint_cubeSign_top _ _ _).symm)
    rw [F.pull_unitExponent, e]
    refine (hlevel k le_rfl _).trans (le_of_eq ?_)
    field_simp
    ring

end Cube

end Cslib.Circuits.Arithmetic.Separation.Flat
