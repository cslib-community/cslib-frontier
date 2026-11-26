/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Finset.Expect
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith

/-!
# The Efron–Stein inequality for uniform averages

For a function `f` of a spectator `y` and of a uniformly random tuple `w : Fin n → A`, the second
moment of `f` about its average over `w` is at most the sum, over the coordinates `i`, of the second
moments of `f` about its averages over the single coordinate `w i`
(`Fintype.expect_sq_sub_expect_le_sum_expect_sq_sub_update`):
`𝔼 (f - 𝔼_w f)² ≤ ∑ i, 𝔼 (f - 𝔼_{w i} f)²`. This is the Efron–Stein inequality
[Efron and Stein][EfronStein1981] in the general form for functions that need not be symmetric
[Steele][Steele1986], for the uniform product measure and with the spectator as an extra fixed
coordinate. It reduces the distance of `f`
from the functions of `y` alone to its distances from the functions not depending on one coordinate
at a time.

The proof is by induction on `n`: split `w = Fin.cons a r`, decompose orthogonally over the fibers
of `(y, a)`, apply the induction hypothesis with the spectator `(y, a)` to the part of average zero
on these fibers, and bound the fiber averages by Jensen's inequality.

## Main results

* `Fintype.expect_sq_sub_expect_le_sum_expect_sq_sub_update`: the Efron–Stein inequality.
* `Fintype.expect_sq_sub_expect_update_le`: the average over one coordinate is the best
  approximation by functions not depending on it.
* `Fintype.expect_sub_expect_sq_le`: bounded-difference variance inequality on `κ → A`.
* `Fintype.exists_forall_abs_sub_expect_le`: simultaneous bounded-difference realization for a
  finite family of observables on `κ → A`.

## References

* [B. Efron, C. Stein, *The Jackknife Estimate of Variance*][EfronStein1981]
* [J. M. Steele, *An Efron-Stein Inequality for Nonsymmetric Statistics*][Steele1986]
-/

public section

open Finset Function
open scoped BigOperators

namespace Fintype

/-- The second moment about a constant is the second moment about the average plus the squared
distance of the average from the constant. -/
private theorem expect_sub_sq_eq {R : Type*} [Fintype R] [Nonempty R] (X : R → ℝ) (c : ℝ) :
    𝔼 r, (X r - c) ^ 2 = 𝔼 r, (X r - 𝔼 s, X s) ^ 2 + (𝔼 s, X s - c) ^ 2 := by
  set m := 𝔼 s, X s
  have h : 𝔼 r, (X r - m) = 0 := by rw [expect_sub_distrib, Fintype.expect_const, sub_self]
  calc 𝔼 r, (X r - c) ^ 2 = 𝔼 r, ((X r - m) ^ 2 + 2 * (m - c) * (X r - m) + (m - c) ^ 2) :=
        expect_congr rfl fun r _ ↦ by ring
    _ = _ := by rw [expect_add_distrib, expect_add_distrib, ← mul_expect, h, mul_zero, add_zero,
        Fintype.expect_const]

/-- **The average over one coordinate is the best approximation** by functions not depending on
that coordinate: if `G` does not change when `w i` is resampled, then the second moment of `f` about
its average over `w i` is at most the second moment of `f - G`. -/
theorem expect_sq_sub_expect_update_le {ι Y A : Type*} [Fintype ι] [DecidableEq ι] [Fintype Y]
    [Fintype A] [Nonempty A] (i : ι) (f G : Y × (ι → A) → ℝ)
    (hG : ∀ p c, G (p.1, update p.2 i c) = G p) :
    𝔼 p, (f p - 𝔼 a, f (p.1, update p.2 i a)) ^ 2 ≤ 𝔼 p, (f p - G p) ^ 2 := by
  set R : Y × (ι → A) → ℝ := fun p ↦ 𝔼 a, f (p.1, update p.2 i a) with hR
  -- The part of `f` of average zero over `w i` is orthogonal to the functions not depending on it.
  have horth : 𝔼 p, (f p - R p) * (R p - G p) = 0 := by
    rw [Fintype.expect_prod_type]
    refine expect_eq_zero fun y _ ↦ ?_
    rw [← Fintype.expect_expect_update _ i]
    refine expect_eq_zero fun w _ ↦ ?_
    have h2 (a : A) : G (y, update w i a) = G (y, w) := hG (y, w) a
    simp only [hR, update_idem, h2]
    rw [← expect_mul, expect_sub_distrib, Fintype.expect_const, sub_self, zero_mul]
  calc 𝔼 p, (f p - R p) ^ 2 ≤ 𝔼 p, ((f p - R p) ^ 2 + 2 * ((f p - R p) * (R p - G p)) +
        (R p - G p) ^ 2) := by
        rw [expect_add_distrib, expect_add_distrib, ← mul_expect, horth, mul_zero, add_zero]
        exact le_add_of_nonneg_right (expect_nonneg fun _ _ ↦ sq_nonneg _)
    _ = 𝔼 p, (f p - G p) ^ 2 := expect_congr rfl fun p _ ↦ by ring

universe u

variable {A : Type u} [Fintype A] [Nonempty A]

/-- **The Efron–Stein inequality** for a uniformly random tuple `w : Fin n → A` and a spectator
`y`: the second moment of `f` about its average over `w` is at most the sum over the coordinates
`i` of the second moments of `f` about its averages over `w i`. The spectator lives in the
universe of `A`, so that the induction can absorb coordinates into it. -/
theorem expect_sq_sub_expect_le_sum_expect_sq_sub_update {n : ℕ} {Y : Type u} [Fintype Y]
    (f : Y × (Fin n → A) → ℝ) :
    𝔼 p, (f p - 𝔼 w, f (p.1, w)) ^ 2 ≤ ∑ i, 𝔼 p, (f p - 𝔼 a, f (p.1, update p.2 i a)) ^ 2 := by
  induction n generalizing Y with
  | zero =>
    have h (p : Y × (Fin 0 → A)) : f p - 𝔼 w, f (p.1, w) = 0 := by
      rw [Fintype.expect_unique, sub_eq_zero]
      exact congrArg f (Prod.ext rfl (Subsingleton.elim _ _))
    simp only [h]
    simp
  | succ n ih =>
    -- Split the tuple into its head `a` and tail `r`.
    have hsplit (G : Y × (Fin (n + 1) → A) → ℝ) :
        𝔼 p, G p = 𝔼 y, 𝔼 a, 𝔼 r : Fin n → A, G (y, Fin.cons a r) := by
      rw [Fintype.expect_prod_type]
      exact expect_congr rfl fun y _ ↦ Fin.expect_univ_cons fun w ↦ G (y, w)
    set g : (Y × A) × (Fin n → A) → ℝ := fun q ↦ f (q.1.1, Fin.cons q.1.2 q.2) with hg
    have hIH := ih g
    have hsplit' (G : (Y × A) × (Fin n → A) → ℝ) :
        𝔼 q, G q = 𝔼 y, 𝔼 a, 𝔼 r, G ((y, a), r) := by
      rw [Fintype.expect_prod_type, Fintype.expect_prod_type]
    -- The average over the whole tuple, and over its tail.
    set h : Y × A → ℝ := fun q ↦ 𝔼 r, g (q, r) with hh
    have hM (y : Y) : 𝔼 w, f (y, w) = 𝔼 a, h (y, a) := Fin.expect_univ_cons fun w ↦ f (y, w)
    -- Orthogonal decomposition over the fibers of `(y, a)`.
    have hLHS : 𝔼 p, (f p - 𝔼 w, f (p.1, w)) ^ 2 =
        𝔼 q, (g q - 𝔼 r, g (q.1, r)) ^ 2 + 𝔼 y, 𝔼 a, (h (y, a) - 𝔼 a', h (y, a')) ^ 2 := by
      rw [hsplit, hsplit', ← expect_add_distrib]
      refine expect_congr rfl fun y _ ↦ ?_
      rw [← expect_add_distrib]
      refine expect_congr rfl fun a _ ↦ ?_
      simp only [hM]
      exact expect_sub_sq_eq (fun r ↦ g ((y, a), r)) _
    -- The tail coordinates, by the induction hypothesis.
    have htail (i : Fin n) : 𝔼 q, (g q - 𝔼 b, g (q.1, update q.2 i b)) ^ 2 =
        𝔼 p, (f p - 𝔼 b, f (p.1, update p.2 i.succ b)) ^ 2 := by
      rw [hsplit, hsplit']
      simp only [hg, Fin.cons_update]
    -- The head coordinate, by Jensen's inequality.
    have hhead : 𝔼 y, 𝔼 a, (h (y, a) - 𝔼 a', h (y, a')) ^ 2 ≤
        𝔼 p, (f p - 𝔼 b, f (p.1, update p.2 0 b)) ^ 2 := by
      rw [hsplit]
      refine expect_le_expect fun y _ ↦ expect_le_expect fun a _ ↦ ?_
      have : h (y, a) - 𝔼 a', h (y, a') =
          𝔼 r, (f (y, Fin.cons a r) - 𝔼 b, f (y, update (Fin.cons a r) 0 b)) := by
        simp only [hh, hg, Fin.update_cons_zero, expect_sub_distrib]
        rw [expect_comm]
      rw [this]
      exact sq_expect_le_expect_sq _ _
    rw [hLHS, Fin.sum_univ_succ]
    calc _ ≤ ∑ i : Fin n, 𝔼 q, (g q - 𝔼 b, g (q.1, update q.2 i b)) ^ 2 +
          𝔼 p, (f p - 𝔼 b, f (p.1, update p.2 0 b)) ^ 2 := add_le_add hIH hhead
      _ = _ := by rw [add_comm]; simp only [htail]

private theorem expect_expect_sq_sub_eq {R : Type*} [Fintype R] [Nonempty R] (f : R → ℝ) :
    (𝔼 x, 𝔼 y, (f x - f y) ^ 2) = 2 * (𝔼 x, (f x - 𝔼 y, f y) ^ 2) := by
  have h (y : R) : (𝔼 x, (f x - f y) ^ 2) =
      (𝔼 x, (f x - 𝔼 z, f z) ^ 2) + (f y - 𝔼 z, f z) ^ 2 := by
    rw [expect_sub_sq_eq f]
    ring
  rw [expect_comm]
  simp only [h, expect_add_distrib, Fintype.expect_const]
  ring

/-- The mean square distance between independent uniform tuples is bounded by the sum of
the mean square distances for resampling one coordinate at a time. -/
theorem expect_expect_sq_sub_le_sum_expect_expect_sq_sub_update {n : ℕ}
    (f : (Fin n → A) → ℝ) :
    (𝔼 u, 𝔼 v, (f u - f v) ^ 2) ≤ ∑ i, 𝔼 u, 𝔼 a, (f u - f (update u i a)) ^ 2 := by
  have h := expect_sq_sub_expect_le_sum_expect_sq_sub_update
    (Y := ULift.{u} Unit) (fun p => f p.2)
  simp only [expect_prod_type, expect_unique] at h
  have hlocal (i : Fin n) :
      (𝔼 u, 𝔼 a, (f u - f (update u i a)) ^ 2) =
        2 * (𝔼 u, (f u - 𝔼 a, f (update u i a)) ^ 2) := by
    rw [mul_expect, ← expect_expect_update _ i, ← expect_expect_update
      (fun u => 2 * (f u - 𝔼 a, f (update u i a)) ^ 2) i]
    refine expect_congr rfl fun u _ => ?_
    simpa only [update_idem, ← mul_expect] using expect_expect_sq_sub_eq (fun a => f (update u i a))
  rw [expect_expect_sq_sub_eq]
  simp only [hlocal, ← mul_sum]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- **Bounded-difference variance bound.** On any finite product `κ → A`, a function whose
oscillation in coordinate `i` is at most `c i ≥ 0` has variance at most `∑ i, (c i) ^ 2`. -/
theorem expect_sub_expect_sq_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : (κ → A) → ℝ) (c : κ → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hf : ∀ ω i a b, |f (update ω i a) - f (update ω i b)| ≤ c i) :
    (𝔼 ω, (f ω - 𝔼 ω', f ω') ^ 2) ≤ ∑ i, c i ^ 2 := by
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let g : (Fin (Fintype.card κ) → A) → ℝ := fun u => f (fun i => u (e i))
  have hg_pair : (𝔼 u, 𝔼 v, (g u - g v) ^ 2) = 2 * 𝔼 ω, (f ω - 𝔼 ω', f ω') ^ 2 := by
    rw [← expect_expect_sq_sub_eq f]
    refine Fintype.expect_equiv (e.symm.arrowCongr (Equiv.refl A))
      (fun u => 𝔼 v, (g u - g v) ^ 2) (fun x => 𝔼 y, (f x - f y) ^ 2) fun u => ?_
    exact Fintype.expect_equiv (e.symm.arrowCongr (Equiv.refl A))
      (fun v => (g u - g v) ^ 2) (fun y => (f (fun i => u (e i)) - f y) ^ 2) fun _ => rfl
  have hstep := expect_expect_sq_sub_le_sum_expect_expect_sq_sub_update g
  have hcoord (j : Fin (Fintype.card κ)) :
      (𝔼 u, 𝔼 a, (g u - g (update u j a)) ^ 2) ≤ c (e.symm j) ^ 2 :=
    expect_le univ_nonempty fun u _ => expect_le univ_nonempty fun a _ => sq_le_sq.mpr <| by
      have hu : update (fun i => u (e i)) (e.symm j) (u j) = fun i => u (e i) :=
        update_eq_self_iff.2 (by simp)
      have hupd : (fun i => update u j a (e i)) = update (fun i => u (e i)) (e.symm j) a :=
        update_comp_equiv u e j a
      rw [abs_of_nonneg (hc _)]
      simpa only [g, hu, hupd] using hf (fun i => u (e i)) (e.symm j) (u j) a
  have hsum : (∑ j, 𝔼 u, 𝔼 a, (g u - g (update u j a)) ^ 2) ≤ ∑ i, c i ^ 2 :=
    (sum_le_sum fun j _ => hcoord j).trans_eq (e.symm.sum_comp fun i => c i ^ 2)
  have hvar_nn : 0 ≤ 𝔼 ω, (f ω - 𝔼 ω', f ω') ^ 2 := expect_nonneg fun _ _ => sq_nonneg _
  linarith

/-- **Simultaneous bounded-difference realization.** Averaging the sum of squared deviations over a
finite family `f : ι → (κ → A) → ℝ` yields a single sample `ω` at which every `f j ω` deviates from
its expectation by at most `√(∑ j, ∑ i, (c j i) ^ 2)`. -/
theorem exists_forall_abs_sub_expect_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → (κ → A) → ℝ) (c : ι → κ → ℝ) (hc : ∀ j i, 0 ≤ c j i)
    (hf : ∀ j ω i a b, |f j (update ω i a) - f j (update ω i b)| ≤ c j i) :
    ∃ ω : κ → A, ∀ j : ι,
      |f j ω - 𝔼 ω', f j ω'| ≤ √(∑ r : ι, ∑ i : κ, c r i ^ 2) := by
  let Φ : (κ → A) → ℝ := fun ω => ∑ r : ι, (f r ω - 𝔼 ω', f r ω') ^ 2
  let B : ℝ := ∑ r : ι, ∑ i : κ, c r i ^ 2
  have hexp_sum : (𝔼 ω : κ → A, Φ ω) = ∑ r : ι, 𝔼 ω : κ → A, (f r ω - 𝔼 ω', f r ω') ^ 2 := by
    simp only [Φ, Fintype.expect_eq_sum_div_card]
    rw [Finset.sum_comm, Finset.sum_div]
  have hexp_le : (𝔼 ω : κ → A, Φ ω) ≤ B :=
    hexp_sum ▸ sum_le_sum fun r _ => expect_sub_expect_sq_le (f r) (c r) (hc r) (hf r)
  have hex : ∃ ω : κ → A, Φ ω ≤ B := by
    by_contra! hgt
    have hlt : B < 𝔼 ω : κ → A, Φ ω := by
      calc B = 𝔼 _ω : κ → A, B := (Fintype.expect_const B).symm
        _ < 𝔼 ω : κ → A, Φ ω :=
          expect_lt_expect (fun ω _ => (hgt ω).le)
            ⟨Classical.arbitrary (κ → A), mem_univ _, hgt _⟩
    linarith
  obtain ⟨ω, hω⟩ := hex
  dsimp only [Φ, B] at hω
  refine ⟨ω, fun j => Real.le_sqrt_of_sq_le ?_⟩
  rw [sq_abs]
  exact (single_le_sum (f := fun r => (f r ω - 𝔼 ω', f r ω') ^ 2)
    (fun r _ => sq_nonneg _) (mem_univ j)).trans hω

end Fintype
