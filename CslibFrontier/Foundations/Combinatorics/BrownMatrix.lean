/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.RectangleFreeMatrix
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Brown's explicit `3`-rectangle-free unit-sphere matrix

For an odd prime `p ≡ 3 (mod 4)`, `-1` is a quadratic non-residue modulo `p`. W. G. Brown
([Brown1966], §2, pp. 282–283, equation (2.1) and Lemma (2.3)) constructed an explicit
`K_{3,3}`-free graph on `EG(3, p) = (ℤ/pℤ)^3` by joining points at squared Euclidean distance `α`
for any nonzero quadratic residue `α ∈ (ℤ/pℤ)^×`. Taking the allowed radius parameter `α = 1` and
viewing the adjacency relation as an `m × m` Boolean matrix `brownMatrix p` (`m = p ^ 3`), every
row has exact weight `p ^ 2 - p = p (p - 1)` and the whole matrix has exact weight
`p ^ 5 - p ^ 4 = p ^ 4 (p - 1) = Θ(m ^ {5/3})` (twice Brown's undirected edge count
`(p ^ 5 - p ^ 4) / 2`), matching the Kővári–Sós–Turán `O(m ^ {5/3})` upper bound up to a constant
factor and supplying the dense `3`-free base matrix in Sergeev's OR-complexity separation
([Sergeev2014ORComplement], Theorem 1(ii), p. 3).

## Main definitions

* `Cslib.brownMatrix`: the `(Fin 3 → ZMod p) × (Fin 3 → ZMod p)` Boolean matrix with entry `(x, y)`
  equal to `true` iff `(x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 = 1`.

## Main results

* `Cslib.card_row_brownMatrix`: for prime `p ≡ 3 (mod 4)`, every row of `brownMatrix p` has exact
  weight `p * (p - 1)`.
* `Cslib.boolMatrixWeight_brownMatrix`: for prime `p ≡ 3 (mod 4)`,
  `boolMatrixWeight (brownMatrix p) = p ^ 4 * (p - 1)`.
* `Cslib.isRectangleFreeMatrix_brownMatrix`: for prime `p ≡ 3 (mod 4)`, `brownMatrix p` is
  `3`-rectangle-free (`K_{3,3}`-free).

## References

* [W. G. Brown, *On graphs that do not contain a Thomsen graph*][Brown1966], §2, pp. 282–283
* [I. S. Sergeev, *On relative OR-complexity of Boolean matrices and their
  complements*][Sergeev2014ORComplement], p. 3
-/

public section

namespace Cslib

open Finset

/-- **Brown's unit-sphere matrix** over `(ℤ/pℤ)^3` ([Brown1966], §2, p. 282, equation (2.1) at
`α = 1`; [Sergeev2014ORComplement], p. 3): entry `(x, y)` is `true` iff
`(x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 = 1` in `ZMod p`. -/
@[expose] def brownMatrix (p : ℕ) : Matrix (Fin 3 → ZMod p) (Fin 3 → ZMod p) Bool :=
  Matrix.of fun x y =>
    decide ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 = 1)

/-- Entry characterization of `brownMatrix`. -/
@[simp] theorem brownMatrix_apply (p : ℕ) (x y : Fin 3 → ZMod p) :
    brownMatrix p x y = decide ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 = 1) :=
  rfl

section PrimeThreeModFour

variable {p : ℕ} [Fact p.Prime]

private theorem not_isSquare_neg_one (hp : p % 4 = 3) : ¬ IsSquare (-1 : ZMod p) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]
  omega

private theorem two_ne_zero_zmod (hp : p % 4 = 3) : (2 : ZMod p) ≠ 0 := by
  intro h2
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  omega

private theorem isSquare_neg_one_of_sq_eq_neg_sq {z w : ZMod p} (hw : w ≠ 0)
    (hzw : z ^ 2 = -w ^ 2) : IsSquare (-1 : ZMod p) :=
  ⟨z * w⁻¹, by linear_combination -(w⁻¹ ^ 2) * hzw + (w * w⁻¹ + 1) * mul_inv_cancel₀ hw⟩

private theorem sq_add_sq_eq_zero_iff (hp : p % 4 = 3) (u v : ZMod p) :
    u ^ 2 + v ^ 2 = 0 ↔ u = 0 ∧ v = 0 := by
  refine ⟨fun huv => ?_, ?_⟩
  · by_cases hv : v = 0
    · subst hv
      exact ⟨by simpa using huv, rfl⟩
    · exact False.elim (not_isSquare_neg_one hp
        (isSquare_neg_one_of_sq_eq_neg_sq (z := u) hv (by linear_combination huv)))
  · rintro ⟨rfl, rfl⟩
    ring

private def circleSet (p : ℕ) [NeZero p] (c : ZMod p) : Finset (ZMod p × ZMod p) :=
  univ.filter fun q => q.1 ^ 2 + q.2 ^ 2 = c

private theorem card_circleSet_zero (hp : p % 4 = 3) : #(circleSet p 0) = 1 := by
  have heq : circleSet p 0 = {(0, 0)} := by
    ext ⟨u, v⟩
    simp only [circleSet, mem_filter, mem_univ, true_and, mem_singleton, Prod.mk.injEq,
      sq_add_sq_eq_zero_iff hp]
  rw [heq, card_singleton]

private theorem card_circleSet_eq_of_ne_zero {c : ZMod p} (hc : c ≠ 0) :
    #(circleSet p c) = #(circleSet p 1) := by
  -- Multiplication by the Gaussian integer `(a + b i) / c`, where `a ^ 2 + b ^ 2 = c`.
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p c
  have hcc := mul_inv_cancel₀ hc
  refine card_bij (fun q _ => ((a * q.1 + b * q.2) * c⁻¹, (a * q.2 - b * q.1) * c⁻¹)) ?_ ?_ ?_
  · rintro ⟨x, y⟩ hxy
    simp only [circleSet, mem_filter, mem_univ, true_and] at hxy ⊢
    linear_combination (x ^ 2 + y ^ 2) * c⁻¹ ^ 2 * hab + c * c⁻¹ ^ 2 * hxy + (c * c⁻¹ + 1) * hcc
  · rintro ⟨x₁, y₁⟩ - ⟨x₂, y₂⟩ - h
    simp only [Prod.mk.injEq] at h
    have h₁ := mul_right_cancel₀ (inv_ne_zero hc) h.1
    have h₂ := mul_right_cancel₀ (inv_ne_zero hc) h.2
    exact Prod.ext (mul_left_cancel₀ hc (by linear_combination a * h₁ - b * h₂ - (x₁ - x₂) * hab))
      (mul_left_cancel₀ hc (by linear_combination b * h₁ + a * h₂ - (y₁ - y₂) * hab))
  · rintro ⟨u, v⟩ huv
    simp only [circleSet, mem_filter, mem_univ, true_and] at huv
    refine ⟨(a * u - b * v, b * u + a * v), ?_, Prod.ext ?_ ?_⟩
    · simp only [circleSet, mem_filter, mem_univ, true_and]
      linear_combination (u ^ 2 + v ^ 2) * hab + c * huv
    · linear_combination u * c⁻¹ * hab + u * hcc
    · linear_combination v * c⁻¹ * hab + v * hcc

private theorem card_circleSet_of_ne_zero (hp : p % 4 = 3) {c : ZMod p} (hc : c ≠ 0) :
    #(circleSet p c) = p + 1 := by
  have hpart : ∑ d : ZMod p, #(circleSet p d) = p ^ 2 := by
    have hfib := card_eq_sum_card_fiberwise
      (s := (univ : Finset (ZMod p × ZMod p))) (t := (univ : Finset (ZMod p)))
      (f := fun q => q.1 ^ 2 + q.2 ^ 2) (fun _ _ => mem_univ _)
    rw [card_univ, Fintype.card_prod, ZMod.card, ← sq] at hfib
    exact hfib.symm
  rw [← add_sum_erase _ _ (mem_univ 0), card_circleSet_zero hp,
    sum_congr rfl fun d hd => card_circleSet_eq_of_ne_zero (ne_of_mem_erase hd), sum_const,
    smul_eq_mul, card_erase_of_mem (mem_univ _), card_univ, ZMod.card] at hpart
  have hc1 : #(circleSet p 1) = p + 1 := by
    have hp3 : 3 ≤ p := by omega
    have hident : 1 + (p - 1) * (p + 1) = p ^ 2 := by
      zify [show 1 ≤ p by omega]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < p - 1) (by omega)
  rw [card_circleSet_eq_of_ne_zero hc, hc1]

private theorem card_unitSphere_three (hp : p % 4 = 3) :
    #(univ.filter fun z : Fin 3 → ZMod p => z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 = 1) = p * (p - 1) := by
  have hbij : #(univ.filter fun z : Fin 3 → ZMod p => z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 = 1) =
      ∑ z₂ : ZMod p, #(circleSet p (1 - z₂ ^ 2)) := by
    rw [← card_sigma]
    refine card_bij (fun z _ => ⟨z 2, (z 0, z 1)⟩) ?_ ?_ ?_
    · intro z hz
      simp only [mem_filter, mem_univ, true_and] at hz
      simp only [mem_sigma, mem_univ, circleSet, mem_filter, true_and]
      linear_combination hz
    · intro z₁ _ z₂ _ h
      simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq] at h
      ext i
      fin_cases i
      exacts [h.2.1, h.2.2, h.1]
    · rintro ⟨z₂, ⟨z₀, z₁⟩⟩ hz
      simp only [mem_sigma, mem_univ, circleSet, mem_filter, true_and] at hz
      refine ⟨![z₀, z₁, z₂], ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      linear_combination hz
  -- Split off the two heights `z₂ = ±1`, where the circle degenerates to a point.
  have hmem_neg1 : (-1 : ZMod p) ∈ (univ : Finset (ZMod p)).erase 1 :=
    mem_erase.mpr ⟨fun h => two_ne_zero_zmod hp (by linear_combination -h), mem_univ _⟩
  have hne (z₂ : ZMod p) (hz₂ : z₂ ∈ ((univ : Finset (ZMod p)).erase 1).erase (-1)) :
      1 - z₂ ^ 2 ≠ 0 := fun h => by
    rcases sq_eq_one_iff.mp (by linear_combination -h) with h1 | h1
    exacts [(mem_erase.mp (mem_erase.mp hz₂).2).1 h1, (mem_erase.mp hz₂).1 h1]
  rw [hbij, ← add_sum_erase _ _ (mem_univ 1), ← add_sum_erase _ _ hmem_neg1,
    sum_congr rfl fun z₂ hz₂ => card_circleSet_of_ne_zero hp (hne z₂ hz₂), sum_const, smul_eq_mul,
    card_erase_of_mem hmem_neg1, card_erase_of_mem (mem_univ _), card_univ, ZMod.card,
    show (1 : ZMod p) - 1 ^ 2 = 0 by ring, show (1 : ZMod p) - (-1) ^ 2 = 0 by ring,
    card_circleSet_zero hp]
  zify [show 1 ≤ p - 1 by omega, show 1 ≤ p by omega]
  ring

/-- Every row of `brownMatrix p` (`p` prime, `p ≡ 3 (mod 4)`) has exact weight `p * (p - 1)`
([Brown1966], §2, p. 282). -/
theorem card_row_brownMatrix (hp : p % 4 = 3) (x : Fin 3 → ZMod p) :
    #(univ.filter fun y : Fin 3 → ZMod p => brownMatrix p x y = true) = p * (p - 1) := by
  rw [← card_unitSphere_three hp]
  refine card_bij (fun y _ => x - y) ?_ ?_ ?_
  · intro y hy
    simpa only [mem_filter, mem_univ, true_and, brownMatrix_apply, decide_eq_true_eq,
      Pi.sub_apply] using hy
  · intro y₁ _ y₂ _ h
    exact sub_right_injective h
  · intro z hz
    refine ⟨x - z, ?_, sub_sub_cancel x z⟩
    simpa only [mem_filter, mem_univ, true_and, brownMatrix_apply, decide_eq_true_eq,
      Pi.sub_apply, sub_sub_cancel] using hz

/-- For prime `p ≡ 3 (mod 4)`, `brownMatrix p` has exact weight `p ^ 4 * (p - 1)` (twice the
undirected edge count `(p ^ 5 - p ^ 4) / 2` of [Brown1966], §2, p. 282;
[Sergeev2014ORComplement], p. 3). -/
theorem boolMatrixWeight_brownMatrix (hp : p % 4 = 3) :
    boolMatrixWeight (brownMatrix p) = p ^ 4 * (p - 1) := by
  rw [boolMatrixWeight_eq_sum_row, sum_congr rfl fun x _ => card_row_brownMatrix hp x, sum_const,
    card_univ, smul_eq_mul, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  ring

private abbrev dot3 (u v : Fin 3 → ZMod p) : ZMod p :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

private abbrev normSq3 (u : Fin 3 → ZMod p) : ZMod p :=
  u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2

private def cross3 (u v : Fin 3 → ZMod p) : Fin 3 → ZMod p :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

private theorem dot3_eq_zero_of_four_unit_dists (hp : p % 4 = 3)
    {a₀ a b₀ b : Fin 3 → ZMod p}
    (h00 : normSq3 (a₀ - b₀) = 1) (h01 : normSq3 (a₀ - b) = 1)
    (h10 : normSq3 (a - b₀) = 1) (h11 : normSq3 (a - b) = 1) :
    dot3 (a - a₀) (b - b₀) = 0 := by
  have h2 : 2 * dot3 (a - a₀) (b - b₀) = 0 := by
    simp only [dot3, normSq3, Pi.sub_apply] at h00 h01 h10 h11 ⊢
    linear_combination h01 - h00 - h11 + h10
  exact (mul_eq_zero.mp h2).resolve_left (two_ne_zero_zmod hp)

private theorem cross3_cross3 (u v w : Fin 3 → ZMod p) :
    cross3 (cross3 u v) w = dot3 u w • v - dot3 v w • u := by
  ext i
  fin_cases i <;>
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cross3, dot3, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring

private theorem collinear_of_cross3_eq_zero {v w : Fin 3 → ZMod p} (hv : v ≠ 0)
    (hc : cross3 v w = 0) : ∃ t : ZMod p, w = t • v := by
  have hc0 : v 1 * w 2 - v 2 * w 1 = 0 := congrFun hc 0
  have hc1 : v 2 * w 0 - v 0 * w 2 = 0 := congrFun hc 1
  have hc2 : v 0 * w 1 - v 1 * w 0 = 0 := congrFun hc 2
  have hall (i j : Fin 3) : v i * w j = v j * w i := by
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    exacts [by linear_combination hc2, by linear_combination -hc1, by linear_combination -hc2,
      by linear_combination hc0, by linear_combination hc1, by linear_combination -hc0]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  refine ⟨w i * (v i)⁻¹, funext fun j => mul_right_cancel₀ hi ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination hall i j - w i * v j * mul_inv_cancel₀ hi

private theorem lagrange_coord_sq (u₀ u₁ u₂ w₀ w₁ w₂ : ZMod p)
    (hu : u₀ ^ 2 + u₁ ^ 2 + u₂ ^ 2 = 1) (hw : w₀ ^ 2 + w₁ ^ 2 + w₂ ^ 2 = 0)
    (huw : u₀ * w₀ + u₁ * w₁ + u₂ * w₂ = 0) :
    (u₁ * w₂ - u₂ * w₁) ^ 2 = -w₀ ^ 2 := by
  linear_combination (u₁ ^ 2 + u₂ ^ 2) * hw - w₀ ^ 2 * hu - (u₁ * w₁ + u₂ * w₂ - u₀ * w₀) * huw

private theorem no_three_collinear_on_unit_sphere (hp : p % 4 = 3)
    {u w : Fin 3 → ZMod p} (hw : w ≠ 0) {s₁ s₂ : ZMod p}
    (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0) (hs₁₂ : s₁ ≠ s₂)
    (h0 : normSq3 u = 1) (h1 : normSq3 (u + s₁ • w) = 1) (h2 : normSq3 (u + s₂ • w) = 1) :
    False := by
  have hexpand (s : ZMod p) :
      normSq3 (u + s • w) - normSq3 u = s * (2 * dot3 u w + s * normSq3 w) := by
    simp only [normSq3, dot3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heq {s : ZMod p} (hs : s ≠ 0) (h : normSq3 (u + s • w) = 1) :
      2 * dot3 u w + s * normSq3 w = 0 :=
    (mul_eq_zero.mp (by rw [← hexpand s, h, h0, sub_self])).resolve_left hs
  have eq₁ := heq hs₁ h1
  have eq₂ := heq hs₂ h2
  have hnorm_w : normSq3 w = 0 := by
    have hdiff : (s₁ - s₂) * normSq3 w = 0 := by linear_combination eq₁ - eq₂
    exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hs₁₂)
  have hdot_uw : dot3 u w = 0 := by
    rw [hnorm_w, mul_zero, add_zero] at eq₁
    exact (mul_eq_zero.mp eq₁).resolve_left (two_ne_zero_zmod hp)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine not_isSquare_neg_one hp ?_
  fin_cases i
  · exact isSquare_neg_one_of_sq_eq_neg_sq hi
      (lagrange_coord_sq (u 0) (u 1) (u 2) (w 0) (w 1) (w 2) h0 hnorm_w hdot_uw)
  · exact isSquare_neg_one_of_sq_eq_neg_sq hi (lagrange_coord_sq (u 1) (u 2) (u 0) (w 1) (w 2) (w 0)
      (by linear_combination h0) (by linear_combination hnorm_w) (by linear_combination hdot_uw))
  · exact isSquare_neg_one_of_sq_eq_neg_sq hi (lagrange_coord_sq (u 2) (u 0) (u 1) (w 2) (w 0) (w 1)
      (by linear_combination h0) (by linear_combination hnorm_w) (by linear_combination hdot_uw))

/-- **Brown's theorem** ([Brown1966], §2, pp. 282–283, equation (2.1) and Lemma (2.3);
[Sergeev2014ORComplement], p. 3): for prime `p ≡ 3 (mod 4)`, `brownMatrix p` is `3`-rectangle-free
(`K_{3,3}`-free). -/
theorem isRectangleFreeMatrix_brownMatrix (hp : p % 4 = 3) :
    IsRectangleFreeMatrix (brownMatrix p) 3 := by
  intro I J hI hJ hall
  obtain ⟨a₀, a₁, a₂, ha₀₁, ha₀₂, ha₁₂, rfl⟩ := card_eq_three.mp hI
  obtain ⟨b₀, b₁, b₂, hb₀₁, hb₀₂, hb₁₂, rfl⟩ := card_eq_three.mp hJ
  have hdist {a b : Fin 3 → ZMod p} (ha : a ∈ ({a₀, a₁, a₂} : Finset _))
      (hb : b ∈ ({b₀, b₁, b₂} : Finset _)) : normSq3 (a - b) = 1 := by
    have h := hall a ha b hb
    simpa only [brownMatrix_apply, decide_eq_true_eq, normSq3, Pi.sub_apply] using h
  have hdist_symm {a b : Fin 3 → ZMod p} (ha : a ∈ ({a₀, a₁, a₂} : Finset _))
      (hb : b ∈ ({b₀, b₁, b₂} : Finset _)) : normSq3 (b - a) = 1 := by
    have h := hdist ha hb
    simp only [normSq3, Pi.sub_apply] at h ⊢
    linear_combination h
  have ha₀ : a₀ ∈ ({a₀, a₁, a₂} : Finset _) := by simp
  have ha₁ : a₁ ∈ ({a₀, a₁, a₂} : Finset _) := by simp
  have ha₂ : a₂ ∈ ({a₀, a₁, a₂} : Finset _) := by simp
  have hb₀ : b₀ ∈ ({b₀, b₁, b₂} : Finset _) := by simp
  have hb₁ : b₁ ∈ ({b₀, b₁, b₂} : Finset _) := by simp
  have hb₂ : b₂ ∈ ({b₀, b₁, b₂} : Finset _) := by simp
  set r₁ := a₁ - a₀
  set r₂ := a₂ - a₀
  set c₁ := b₁ - b₀
  set c₂ := b₂ - b₀
  have hr₁ : r₁ ≠ 0 := sub_ne_zero.mpr ha₀₁.symm
  have hr₂ : r₂ ≠ 0 := sub_ne_zero.mpr ha₀₂.symm
  have hr₁₂ : r₁ ≠ r₂ := fun h => ha₁₂ (sub_left_injective h)
  have hc₁ : c₁ ≠ 0 := sub_ne_zero.mpr hb₀₁.symm
  have hc₂ : c₂ ≠ 0 := sub_ne_zero.mpr hb₀₂.symm
  have hc₁₂ : c₁ ≠ c₂ := fun h => hb₁₂ (sub_left_injective h)
  by_cases hcross : cross3 r₁ r₂ = 0
  · obtain ⟨t, ht⟩ := collinear_of_cross3_eq_zero hr₁ hcross
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hr₂ (by simp only [ht, zero_smul])
    have ht1 : (1 : ZMod p) ≠ t := by
      rintro rfl
      exact hr₁₂ (by simp only [ht, one_smul])
    refine no_three_collinear_on_unit_sphere hp hr₁ one_ne_zero ht0 ht1
      (hdist ha₀ hb₀) ?_ ?_
    · rw [show a₀ - b₀ + (1 : ZMod p) • r₁ = a₁ - b₀ by
        simp only [r₁, one_smul]; abel]
      exact hdist ha₁ hb₀
    · rw [show a₀ - b₀ + t • r₁ = a₂ - b₀ by rw [← ht]; simp only [r₂]; abel]
      exact hdist ha₂ hb₀
  · set n := cross3 r₁ r₂
    have hd11 : dot3 r₁ c₁ = 0 :=
      dot3_eq_zero_of_four_unit_dists hp (hdist ha₀ hb₀) (hdist ha₀ hb₁)
        (hdist ha₁ hb₀) (hdist ha₁ hb₁)
    have hd21 : dot3 r₂ c₁ = 0 :=
      dot3_eq_zero_of_four_unit_dists hp (hdist ha₀ hb₀) (hdist ha₀ hb₁)
        (hdist ha₂ hb₀) (hdist ha₂ hb₁)
    have hd12 : dot3 r₁ c₂ = 0 :=
      dot3_eq_zero_of_four_unit_dists hp (hdist ha₀ hb₀) (hdist ha₀ hb₂)
        (hdist ha₁ hb₀) (hdist ha₁ hb₂)
    have hd22 : dot3 r₂ c₂ = 0 :=
      dot3_eq_zero_of_four_unit_dists hp (hdist ha₀ hb₀) (hdist ha₀ hb₂)
        (hdist ha₂ hb₀) (hdist ha₂ hb₂)
    have hnc₁ : cross3 n c₁ = 0 := by
      rw [cross3_cross3, hd11, hd21, zero_smul, zero_smul, sub_zero]
    have hnc₂ : cross3 n c₂ = 0 := by
      rw [cross3_cross3, hd12, hd22, zero_smul, zero_smul, sub_zero]
    obtain ⟨s₁, hs₁⟩ := collinear_of_cross3_eq_zero hcross hnc₁
    obtain ⟨s₂, hs₂⟩ := collinear_of_cross3_eq_zero hcross hnc₂
    have hs₁0 : s₁ ≠ 0 := by
      rintro rfl
      exact hc₁ (by simp only [hs₁, zero_smul])
    have hs₂0 : s₂ ≠ 0 := by
      rintro rfl
      exact hc₂ (by simp only [hs₂, zero_smul])
    have hs₁₂ : s₁ ≠ s₂ := by
      rintro rfl
      exact hc₁₂ (hs₁.trans hs₂.symm)
    refine no_three_collinear_on_unit_sphere hp hcross hs₁0 hs₂0 hs₁₂
      (hdist_symm ha₀ hb₀) ?_ ?_
    · rw [show b₀ - a₀ + s₁ • n = b₁ - a₀ by rw [← hs₁]; simp only [c₁]; abel]
      exact hdist_symm ha₀ hb₁
    · rw [show b₀ - a₀ + s₂ • n = b₂ - a₀ by rw [← hs₂]; simp only [c₂]; abel]
      exact hdist_symm ha₀ hb₂

end PrimeThreeModFour

end Cslib
