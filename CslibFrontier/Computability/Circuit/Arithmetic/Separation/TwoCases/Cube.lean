/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Basic
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Rank
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Curvature
import CslibFrontier.Foundations.Geometry.CAT0.Toolkit
import Mathlib.Data.Fintype.Order

/-!
# The two cases: Theorem D.2

At least one of the two hypotheses of Definition D.1 holds
(`TwoCases.flatCase_or_contractingCase`). Outside the contracting case some price on
`Mat_μ(F₂)` is the square root of the rank of the difference (`TwoCases.exists_sq_eq_rank`), so
the diagonal matrices with entries `0` and `1` are the vertices of a Euclidean cube `[0, 1]^μ` in a
CAT(0) space whose metric is a price (Proposition C.3). Step 8 of the proof fills the cube one
coordinate at a time, sending each segment in the new direction to the geodesic segment between
the images of its ends; by Lemma C.4(f) the map stays isometric. Every finite subset of `ℝ^k`,
`k ≤ μ`, is up to translation and scale a subset of the cube.

## Main results

* `TwoCases.flatCase_or_contractingCase`: Theorem D.2.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem D.2 and Step 8 of its proof, pp. 30–31; module `Paper.Alternative` (`thm_alt`)
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TwoCases

open Finset Function Cslib.PartyTensor Cslib.CAT0
open Cslib.Circuits.Arithmetic.Separation.Flag

variable {Y : Type} [MetricSpace Y] {μ : ℕ}

/-- The points of `[0, 1]^μ` whose coordinates outside `D` are `0` or `1`. -/
private def cube (D : Finset (Fin μ)) : Set (Fin μ → ℝ) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1 ∧ (i ∉ D → x i = 0 ∨ x i = 1)}

/-- `F` is isometric on `cube D`. -/
private def IsoOn (F : (Fin μ → ℝ) → Y) (D : Finset (Fin μ)) : Prop :=
  ∀ x ∈ cube D, ∀ y ∈ cube D, dist (F x) (F y) ^ 2 = ∑ i, (x i - y i) ^ 2

private theorem update_mem {D : Finset (Fin μ)} {c : Fin μ} {x : Fin μ → ℝ} {t : ℝ}
    (hx : x ∈ cube (insert c D)) (ht : t = 0 ∨ t = 1) : update x c t ∈ cube D := fun i => by
  by_cases hi : i = c
  · subst hi
    rw [update_self]
    rcases ht with rfl | rfl <;> norm_num
  · rw [update_of_ne hi]
    exact ⟨(hx i).1, (hx i).2.1, fun h => (hx i).2.2 (by simp [hi, h])⟩

/-- "We fill it one coordinate at a time … Lemma C.4(f), applied with `h = 1` to two such
segments, shows that the map stays isometric." -/
private theorem exists_isoOn_insert [CompleteCAT0Space Y] {F : (Fin μ → ℝ) → Y}
    {D : Finset (Fin μ)} (hF : IsoOn F D) (c : Fin μ) :
    ∃ F' : (Fin μ → ℝ) → Y, IsoOn F' (insert c D) := by
  have hγ : ∀ z : Fin μ → ℝ, ∃ γ : Y, 0 ≤ z c → z c ≤ 1 →
      IsPointAt (F (update z c 0)) (F (update z c 1)) (z c) γ := fun z => by
    by_cases h : 0 ≤ z c ∧ z c ≤ 1
    · exact (exists_isPointAt _ _ h.1 h.2).imp fun _ h' _ _ => h'
    · exact ⟨F z, fun h0 h1 => absurd ⟨h0, h1⟩ h⟩
  choose F' hF' using hγ
  refine ⟨F', fun x hx y hy => ?_⟩
  -- the squared distances between the ends of the two segments
  have d : ∀ x' ∈ cube (insert c D), ∀ y' ∈ cube (insert c D), ∀ s t : ℝ, (s = 0 ∨ s = 1) →
      (t = 0 ∨ t = 1) → dist (F (update x' c s)) (F (update y' c t)) ^ 2 =
        (s - t) ^ 2 + ∑ i ∈ univ.erase c, (x' i - y' i) ^ 2 := fun x' hx' y' hy' s t hs ht => by
    rw [hF _ (update_mem hx' hs) _ (update_mem hy' ht), ← add_sum_erase _ _ (mem_univ c),
      update_self, update_self]
    exact congrArg _ (sum_congr rfl fun i hi => by
      rw [update_of_ne (ne_of_mem_erase hi), update_of_ne (ne_of_mem_erase hi)])
  have h01 : ∀ x' ∈ cube (insert c D), dist (F (update x' c 0)) (F (update x' c 1)) ^ 2 = 1 :=
    fun x' hx' => by simpa using d x' hx' x' hx' 0 1 (by simp) (by simp)
  have eq_of_sq : ∀ {p q : ℝ}, 0 ≤ p → 0 ≤ q → p ^ 2 = q ^ 2 → p = q := fun hp hq h =>
    (pow_left_inj₀ hp hq two_ne_zero).1 h
  have h := dist_sq_of_flat_of_isPointAt rfl
    (eq_of_sq dist_nonneg dist_nonneg ((h01 y hy).trans (h01 x hx).symm))
    (eq_of_sq dist_nonneg dist_nonneg (by
      rw [d x hx y hy 1 1 (by simp) (by simp), d x hx y hy 0 0 (by simp) (by simp)]; norm_num)) rfl
    (by rw [h01 x hx, d x hx y hy 0 0 (by simp) (by simp), d x hx y hy 0 1 (by simp) (by simp)];
        norm_num)
    (by rw [h01 x hx, d x hx y hy 0 0 (by simp) (by simp), d x hx y hy 1 0 (by simp) (by simp)];
        norm_num)
    (hx c).1 (hx c).2.1 (hy c).1 (hy c).2.1 (hF' x (hx c).1 (hx c).2.1) (hF' y (hy c).1 (hy c).2.1)
  rw [h, h01 x hx, d x hx y hy 0 0 (by simp) (by simp), ← add_sum_erase _ _ (mem_univ c)]
  ring

/-- "We fill it one coordinate at a time": if the points `g S` of a CAT(0) space have the
squared distances `|S Δ T|` of the vertices of the cube, then the cube `[0, 1]^μ` has an
isometric map into the space. -/
private theorem exists_cube [CompleteCAT0Space Y] (g : Finset (Fin μ) → Y)
    (hg : ∀ S T, dist (g S) (g T) ^ 2 = (symmDiff S T).card) :
    ∃ F : (Fin μ → ℝ) → Y, ∀ x y : Fin μ → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) →
      (∀ i, 0 ≤ y i ∧ y i ≤ 1) → dist (F x) (F y) ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  classical
  have key : ∀ D : Finset (Fin μ), ∃ F : (Fin μ → ℝ) → Y, IsoOn F D := fun D => by
    induction D using Finset.induction_on with
    | empty =>
      refine ⟨fun x => g {i | x i = 1}, fun x hx y hy => ?_⟩
      have e : ∀ i, (x i - y i) ^ 2 = if i ∈ symmDiff ({i | x i = 1} : Finset (Fin μ))
          ({i | y i = 1} : Finset (Fin μ)) then 1 else 0 :=
        fun i => by
          rcases (hx i).2.2 (notMem_empty i) with h1 | h1 <;>
            rcases (hy i).2.2 (notMem_empty i) with h2 | h2 <;>
            simp [h1, h2, Finset.mem_symmDiff, Finset.mem_filter]
      rw [hg, sum_congr rfl fun i _ => e i, sum_boole]
      congr 2
      ext
      simp
    | insert c D _ ih =>
      obtain ⟨F, hF⟩ := ih
      exact exists_isoOn_insert hF c
  obtain ⟨F, hF⟩ := key univ
  exact ⟨F, fun x y hx hy => hF x (fun i => ⟨(hx i).1, (hx i).2, fun h => absurd (mem_univ i) h⟩)
    y fun i => ⟨(hy i).1, (hy i).2, fun h => absurd (mem_univ i) h⟩⟩

variable {K : Type} [Field K]

/-- Step 8: "every finite subset of a Euclidean space of dimension at most `μ` is, up to
translation and scale, a subset of this cube, and hence its metric is a price", for
`μ = k + 3`. -/
private theorem isPrice_dist (hK : ¬ ContractingCase K) (k : ℕ) (V : Type) [Finite V]
    (E : V → EuclideanSpace ℝ (Fin k)) : IsPrice K fun a b => dist (E a) (E b) := by
  obtain ⟨w, hw, hrk⟩ := exists_sq_eq_rank hK (μ := k + 3) (by omega)
  obtain ⟨Y, _, _, φ, hY, hφ⟩ := Curvature.exists_completeCAT0Space_of_isPrice hw
  obtain ⟨F, hF⟩ := exists_cube (Y := Y) (fun S => φ (dg S)) fun S T => by
    have e : (dg S - dg T : Mt (k + 3)) = X 1 1 (symmDiff S T) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [X_one, dg, hS, hT, mem_symmDiff]
      · simp [X_one, dg, hij]
    rw [hφ, hrk, e, rank_X]
  -- the points `(E v + c) / (2c)`, padded with zeros, lie in the cube
  obtain ⟨R, hR⟩ := Finite.exists_le fun p : V × Fin k => |E p.1 p.2|
  set c := max R 1
  have hc : 0 < c := lt_max_of_lt_right one_pos
  let g : V → Fin (k + 3) → ℝ := fun v => Fin.append (fun i => (E v i + c) / (2 * c)) 0
  have hg : ∀ v i, 0 ≤ g v i ∧ g v i ≤ 1 := fun v i => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have := abs_le.1 ((hR (v, i)).trans (le_max_left R 1))
      simp only [g, Fin.append_left]
      constructor
      · exact div_nonneg (by linarith) (by positivity)
      · rw [div_le_one (by positivity)]; linarith
    · simp [g, Fin.append_right]
  have hdist : ∀ u v, dist (E u) (E v) = 2 * c * dist (F (g u)) (F (g v)) := fun u v => by
    refine (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, hF _ _ (hg u) (hg v), Fin.sum_univ_add, EuclideanSpace.dist_eq,
      Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _), mul_add, mul_sum, mul_sum]
    simp only [g, Fin.append_left, Fin.append_right, Pi.zero_apply, sub_self, Real.dist_eq, sq_abs]
    norm_num
    refine sum_congr rfl fun i _ => ?_
    field_simp
    ring
  simpa only [← hdist] using (hY.comp fun v => F (g v)).smul (by positivity : 0 ≤ 2 * c)

/-- **Paper: Theorem D.2** (p. 30): at least one of the two hypotheses of Definition D.1 holds,
that is, one of the two cases occurs. -/
theorem flatCase_or_contractingCase (K : Type) [Field K] : FlatCase K ∨ ContractingCase K :=
  or_iff_not_imp_right.2 fun hK k V _ E => isPrice_dist hK k V E

end Cslib.Circuits.Arithmetic.Separation.TwoCases
