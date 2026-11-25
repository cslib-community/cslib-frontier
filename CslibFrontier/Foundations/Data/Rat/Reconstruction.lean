/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib / Cslib, Wang rational reconstruction and height bounds)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Rat.Basic
public import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rational reconstruction, height bounds, and Chinese-remainder recovery

Implements Wang's extended-Euclidean rational reconstruction `Rat.reconstruct` over `ℤ / Mℤ`,
rational height bounds (`Rat.height`), uniqueness modulo `M` below the `2 * N * D < M` threshold,
completeness of Euclidean reconstruction under height/denominator bounds, and multi-modulus
Chinese-remainder rational recovery (`Rat.reconstructPi`) across pairwise coprime moduli (such as
finite-field primes `ZMod pᵢ`).

## Main definitions

* `Rat.height`: multiplicative rational height `max q.num.natAbs q.den`.
* `Rat.reconstruct`: extended-Euclidean rational reconstruction modulo `M` with numerator bound `N`
  and denominator bound `D`.
* `Rat.reconstructPi`: Chinese-remainder rational reconstruction from residues modulo pairwise
  coprime moduli `m : Fin k → ℕ`.

## Main results

* `Rat.eq_of_modEq_of_bounds`, `Rat.eq_of_modEq_of_height_mul_lt`: modular uniqueness of
  rationals with bounded numerator/denominator or bounded height product.
* `Rat.height_add_le`, `Rat.height_mul_le`, `Rat.height_inv`: arithmetic height bounds.
* `Rat.reconstruct_eq_some`: soundness (numerator, denominator, coprimality, and modular
  congruence invariants of every reconstructed rational).
* `Rat.reconstruct_of_eq`: completeness (recovering `some q` whenever `2 * N * D < M` and
  `q.den.Coprime M`).
* `Rat.reconstructPi_of_eq`: exact recovery from residues in `∀ i, ZMod (m i)`.

## References

* [P. S. Wang, *A p-adic Algorithm for Univariate Partial Fractions*][Wang1981]
* [J. von zur Gathen, J. Gerhard, *Modern Computer Algebra*][vonZurGathenGerhard2013], §5.10.
-/

public section

namespace Rat

open Finset

section HeightAndUniqueness

/-- Multiplicative height `max |num| den` of a rational number `q`. -/
@[expose] def height (q : ℚ) : ℕ :=
  max q.num.natAbs q.den

theorem height_def (q : ℚ) : q.height = max q.num.natAbs q.den :=
  rfl

theorem natAbs_num_le_height (q : ℚ) : q.num.natAbs ≤ height q :=
  le_max_left _ _

theorem den_le_height (q : ℚ) : q.den ≤ height q :=
  le_max_right _ _

theorem one_le_height (q : ℚ) : 1 ≤ height q :=
  le_trans q.den_nz.bot_lt (den_le_height q)

@[simp]
theorem height_zero : height 0 = 1 := by
  simp [height]

@[simp]
theorem height_one : height 1 = 1 := by
  simp [height]

@[simp]
theorem height_neg (q : ℚ) : height (-q) = height q := by
  simp [height]

private theorem mul_eq_mul_of_divInt_eq {r t : ℤ} {q : ℚ} (ht : t ≠ 0)
    (h : Rat.divInt r t = q) : q.num * t = r * (q.den : ℤ) := by
  rw [← Rat.num_divInt_den q, Rat.divInt_eq_divInt_iff ht (by exact_mod_cast q.den_nz)] at h
  exact h.symm

theorem height_inv {q : ℚ} (hq : q ≠ 0) : height q⁻¹ = height q := by
  have hnum_nz : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hinv_num : (q⁻¹).num.natAbs = q.den := by
    rw [Rat.num_inv, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hnum_nz, Int.natAbs_natCast,
      one_mul]
  rw [height, height, hinv_num, Rat.den_inv_of_ne_zero hq, max_comm]

theorem height_divInt_le (a b : ℤ) (hb : b ≠ 0) :
    height (Rat.divInt a b) ≤ max a.natAbs b.natAbs :=
  max_le (le_trans (Rat.natAbs_num_divInt_le a b hb) (le_max_left _ _))
    (le_trans (Rat.den_divInt_le a b hb) (le_max_right _ _))

theorem height_mul_le (p q : ℚ) : height (p * q) ≤ height p * height q :=
  max_le
    ((natAbs_num_mul_le p q).trans
      (Nat.mul_le_mul (natAbs_num_le_height p) (natAbs_num_le_height q)))
    ((den_mul_le p q).trans (Nat.mul_le_mul (den_le_height p) (den_le_height q)))

theorem height_add_le (p q : ℚ) : height (p + q) ≤ 2 * height p * height q := by
  have h₁ := Nat.mul_le_mul (natAbs_num_le_height p) (den_le_height q)
  have h₂ := Nat.mul_le_mul (natAbs_num_le_height q) (den_le_height p)
  have h₃ := Nat.mul_le_mul (den_le_height p) (den_le_height q)
  refine max_le ((natAbs_num_add_le p q).trans ?_) ((den_add_le p q).trans ?_) <;>
    linarith [Nat.zero_le (height p * height q)]

/-- Two products that agree modulo `M`, each of absolute value at most `N * D`, are equal once
`2 * N * D < M`. -/
private theorem mul_eq_mul_of_modEq_of_le {M N D : ℕ} {a b c d : ℤ}
    (hmod : a * b ≡ c * d [ZMOD M]) (hM : 2 * N * D < M)
    (h₁ : a.natAbs * b.natAbs ≤ N * D) (h₂ : c.natAbs * d.natAbs ≤ N * D) : a * b = c * d := by
  refine sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hmod.symm.dvd ?_)
  have := Int.natAbs_sub_le (a * b) (c * d)
  rw [Int.natAbs_mul, Int.natAbs_mul] at this
  rw [Int.natAbs_natCast]
  linarith

/-- Uniqueness of modular rational recovery: if `a₁ * b₂ ≡ a₂ * b₁ [ZMOD M]` with
`|aᵢ| ≤ N`, `0 < bᵢ ≤ D`, and `2 * N * D < M`, then `(a₁ : ℚ) / b₁ = (a₂ : ℚ) / b₂`. -/
theorem eq_of_modEq_of_bounds {M N D : ℕ} {a₁ a₂ : ℤ} {b₁ b₂ : ℕ}
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (ha₁ : a₁.natAbs ≤ N) (ha₂ : a₂.natAbs ≤ N)
    (hbd₁ : b₁ ≤ D) (hbd₂ : b₂ ≤ D) (hM : 2 * N * D < M)
    (hmod : a₁ * (b₂ : ℤ) ≡ a₂ * (b₁ : ℤ) [ZMOD M]) :
    (a₁ : ℚ) / (b₁ : ℚ) = (a₂ : ℚ) / (b₂ : ℚ) := by
  rw [div_eq_div_iff (Nat.cast_ne_zero.mpr hb₁.ne') (Nat.cast_ne_zero.mpr hb₂.ne')]
  exact_mod_cast mul_eq_mul_of_modEq_of_le hmod hM (Nat.mul_le_mul ha₁ hbd₂)
    (Nat.mul_le_mul ha₂ hbd₁)

/-- Modular uniqueness stated directly in terms of rational heights: if `p, q : ℚ` satisfy
`(p.num : ZMod M) * (q.den : ZMod M) = (q.num : ZMod M) * (p.den : ZMod M)` and
`2 * height p * height q < M`, then `p = q`. -/
theorem eq_of_modEq_of_height_mul_lt {M : ℕ} {p q : ℚ}
    (hM : 2 * height p * height q < M)
    (hmod : p.num * (q.den : ℤ) ≡ q.num * (p.den : ℤ) [ZMOD M]) : p = q :=
  Rat.eq_iff_mul_eq_mul.mpr <| mul_eq_mul_of_modEq_of_le hmod hM
    (Nat.mul_le_mul (natAbs_num_le_height p) (den_le_height q))
    ((Nat.mul_le_mul (natAbs_num_le_height q) (den_le_height p)).trans_eq (mul_comm _ _))

end HeightAndUniqueness

section WangReconstruction

private structure EuclidState where
  r0 : ℤ
  t0 : ℤ
  r1 : ℤ
  t1 : ℤ

private def reconstructLoop (N : ℕ) (r0 t0 r1 t1 : ℤ) : EuclidState :=
  if h : (N : ℤ) < r1 then
    let q := r0 / r1
    let r2 := r0 % r1
    let t2 := t0 - q * t1
    have _ : r2.toNat < r1.toNat := by
      have hpos : 0 < r1 := lt_of_le_of_lt (Int.natCast_nonneg N) h
      have hlt := Int.emod_lt_of_pos r0 hpos
      have hnneg := Int.emod_nonneg r0 hpos.ne'
      omega
    reconstructLoop N r1 t1 r2 t2
  else
    ⟨r0, t0, r1, t1⟩
termination_by r1.toNat

private structure StepInv (M : ℕ) (u r0 t0 r1 t1 : ℤ) : Prop where
  r0_pos : 0 < r0
  r1_nonneg : 0 ≤ r1
  r1_lt : r1 < r0
  mod0 : r0 ≡ t0 * u [ZMOD M]
  mod1 : r1 ≡ t1 * u [ZMOD M]
  t_sign : t0 * t1 ≤ 0
  t1_ne : t1 ≠ 0
  bezout : ∃ s : ℤ, s * s = 1 ∧ r0 * t1 - r1 * t0 = s * (M : ℤ)

private theorem t_prod_neg_step {r0 t0 r1 t1 : ℤ} (ht_sign : t0 * t1 ≤ 0) (ht1_ne : t1 ≠ 0)
    (hr1_pos : 0 < r1) (hr1_lt : r1 < r0) : t1 * (t0 - (r0 / r1) * t1) ≤ -1 := by
  have hdiv_ge : 1 ≤ r0 / r1 := Int.le_ediv_of_mul_le hr1_pos (by linarith)
  have ht1_sq : 0 < t1 * t1 := mul_self_pos.mpr ht1_ne
  nlinarith

private theorem stepInv_step {M N : ℕ} {u r0 t0 r1 t1 : ℤ}
    (hinv : StepInv M u r0 t0 r1 t1) (hlt : (N : ℤ) < r1) :
    StepInv M u r1 t1 (r0 % r1) (t0 - (r0 / r1) * t1) := by
  have hr1_pos : 0 < r1 := lt_of_le_of_lt (Int.natCast_nonneg N) hlt
  have hprod := t_prod_neg_step hinv.t_sign hinv.t1_ne hr1_pos hinv.r1_lt
  have heq : r0 % r1 = r0 - (r0 / r1) * r1 := by rw [Int.emod_def, mul_comm]
  obtain ⟨s, hs1, hs2⟩ := hinv.bezout
  exact
    { r0_pos := hr1_pos
      r1_nonneg := Int.emod_nonneg r0 hr1_pos.ne'
      r1_lt := Int.emod_lt_of_pos r0 hr1_pos
      mod0 := hinv.mod1
      mod1 := by
        rw [heq]
        simpa only [sub_mul, mul_assoc] using hinv.mod0.sub ((hinv.mod1).mul_left (r0 / r1))
      t_sign := by linarith
      t1_ne := fun ht2 => by rw [ht2, mul_zero] at hprod; omega
      bezout := ⟨-s, by linear_combination hs1, by rw [heq]; linear_combination -hs2⟩ }

private theorem reconstructLoop_spec {M N : ℕ} {u r0 t0 r1 t1 : ℤ}
    (hinv : StepInv M u r0 t0 r1 t1) :
    let st := reconstructLoop N r0 t0 r1 t1
    StepInv M u st.r0 st.t0 st.r1 st.t1 ∧ st.r1 ≤ (N : ℤ) ∧
      ((st.r0 = r0 ∧ st.t0 = t0 ∧ st.r1 = r1 ∧ st.t1 = t1) ∨
        ((N : ℤ) < st.r0 ∧ st.t0 * st.t1 < 0)) := by
  unfold reconstructLoop
  split_ifs with hlt
  · have hr1_pos : 0 < r1 := lt_of_le_of_lt (Int.natCast_nonneg N) hlt
    obtain ⟨hs, hle, hor⟩ := reconstructLoop_spec (M := M) (N := N) (u := u) (stepInv_step hinv hlt)
    refine ⟨hs, hle, Or.inr ?_⟩
    rcases hor with ⟨hr0_eq, ht0_eq, -, ht1_eq⟩ | hrec
    · rw [hr0_eq, ht0_eq, ht1_eq]
      exact ⟨hlt, by linarith [t_prod_neg_step hinv.t_sign hinv.t1_ne hr1_pos hinv.r1_lt]⟩
    · exact hrec
  · exact ⟨hinv, not_lt.mp hlt, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
termination_by r1.toNat
decreasing_by
  have hpos : 0 < r1 := lt_of_le_of_lt (Int.natCast_nonneg N) hlt
  have := Int.emod_lt_of_pos r0 hpos
  have := Int.emod_nonneg r0 hpos.ne'
  omega

/-- Wang's extended-Euclidean rational reconstruction modulo `M`. Returns `some q` when the
Euclidean sequence first reaches remainder `r ≤ N` with cofactor `t` satisfying `|t| ≤ D` and
`Nat.Coprime t.natAbs M`. -/
def reconstruct (M : ℕ) (u : ℤ) (N D : ℕ) : Option ℚ :=
  if M = 0 then none
  else
    let st := reconstructLoop N (M : ℤ) 0 (u % (M : ℤ)) 1
    if decide (st.t1.natAbs ≤ D ∧ Nat.Coprime st.t1.natAbs M) then
      some (Rat.divInt st.r1 st.t1)
    else
      none

private theorem initial_stepInv {M : ℕ} (hM : 0 < M) (u : ℤ) :
    StepInv M u (M : ℤ) 0 (u % (M : ℤ)) 1 := by
  have hMz : (0 : ℤ) < (M : ℤ) := Int.natCast_pos.mpr hM
  refine
    { r0_pos := hMz
      r1_nonneg := Int.emod_nonneg u hMz.ne'
      r1_lt := Int.emod_lt_of_pos u hMz
      mod0 := by simp [Int.ModEq]
      mod1 := by
        show u % (M : ℤ) ≡ 1 * u [ZMOD M]
        rw [one_mul, Int.ModEq, Int.emod_emod]
      t_sign := by simp
      t1_ne := one_ne_zero
      bezout := ⟨1, rfl, by ring⟩ }

private theorem natAbs_add_of_mul_nonneg {a b : ℤ} (h : 0 ≤ a * b) :
    (a + b).natAbs = a.natAbs + b.natAbs := by
  rcases mul_nonneg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega

/-- Soundness of `Rat.reconstruct`: every output `q` satisfies `|q.num| ≤ N`, `q.den ≤ D`,
`Nat.Coprime q.den M`, and `q.num ≡ u * q.den [ZMOD M]`. -/
theorem reconstruct_eq_some {M N D : ℕ} {u : ℤ} {q : ℚ}
    (hq : reconstruct M u N D = some q) :
    0 < M ∧ q.num.natAbs ≤ N ∧ q.den ≤ D ∧ Nat.Coprime q.den M ∧
      q.num ≡ u * (q.den : ℤ) [ZMOD M] := by
  rw [reconstruct] at hq
  by_cases hM : M = 0
  · simp [hM] at hq
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  simp only [hM, ↓reduceIte] at hq
  let st := reconstructLoop N (M : ℤ) 0 (u % (M : ℤ)) 1
  change (if decide (st.t1.natAbs ≤ D ∧ Nat.Coprime st.t1.natAbs M) then
    some (Rat.divInt st.r1 st.t1) else none) = some q at hq
  split_ifs at hq with hcond
  rcases of_decide_eq_true hcond with ⟨htD, htM⟩
  have hqr : Rat.divInt st.r1 st.t1 = q := Option.some.inj hq
  have hspec := reconstructLoop_spec (N := N) (initial_stepInv hMpos u)
  change StepInv M u st.r0 st.t0 st.r1 st.t1 ∧ st.r1 ≤ (N : ℤ) ∧ _ at hspec
  obtain ⟨hinv, hrN, -⟩ := hspec
  have hden : q.den ∣ st.t1.natAbs := Int.natCast_dvd.mp (hqr ▸ Rat.den_dvd st.r1 st.t1)
  -- Cancel the unit `t1` from `q.num * t1 = r1 * q.den ≡ t1 * u * q.den`.
  have hq_mod := Int.ModEq.cancel_right_div_gcd (Int.natCast_pos.mpr hMpos)
    (c := st.t1) (a := q.num) (b := u * q.den) <| by
      rw [mul_eq_mul_of_divInt_eq hinv.t1_ne hqr]
      calc st.r1 * q.den ≡ st.t1 * u * q.den [ZMOD M] := hinv.mod1.mul_right _
        _ = u * q.den * st.t1 := by ring
  rw [show Int.gcd M st.t1 = 1 from htM.symm, Nat.cast_one, Int.ediv_one] at hq_mod
  subst hqr
  exact ⟨hMpos, (natAbs_num_divInt_le _ _ hinv.t1_ne).trans (by have := hinv.r1_nonneg; omega),
    (den_divInt_le _ _ hinv.t1_ne).trans htD, Nat.Coprime.coprime_dvd_left hden htM, hq_mod⟩

/-- Completeness of `Rat.reconstruct`: if `q : ℚ` satisfies `|q.num| ≤ N`, `q.den ≤ D`,
`2 * N * D < M`, `Nat.Coprime q.den M`, and `(u : ZMod M)` represents `q`, then `reconstruct`
returns `some q`. -/
theorem reconstruct_of_eq {M N D : ℕ} {u : ℤ} {q : ℚ}
    (hN : q.num.natAbs ≤ N) (hD : q.den ≤ D) (hM : 2 * N * D < M)
    (hcop : Nat.Coprime q.den M) (hmod : q.num ≡ u * (q.den : ℤ) [ZMOD M]) :
    reconstruct M u N D = some q := by
  have hMpos : 0 < M := Nat.zero_lt_of_lt hM
  have hM0 : (M : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hMpos.ne'
  rw [reconstruct]
  simp only [hMpos.ne', ↓reduceIte]
  let st := reconstructLoop N (M : ℤ) 0 (u % (M : ℤ)) 1
  change (if decide (st.t1.natAbs ≤ D ∧ Nat.Coprime st.t1.natAbs M) then
    some (Rat.divInt st.r1 st.t1) else none) = some q
  have hspec := reconstructLoop_spec (N := N) (initial_stepInv hMpos u)
  change StepInv M u st.r0 st.t0 st.r1 st.t1 ∧ st.r1 ≤ (N : ℤ) ∧
    ((st.r0 = (M : ℤ) ∧ st.t0 = 0 ∧ st.r1 = u % (M : ℤ) ∧ st.t1 = 1) ∨
      ((N : ℤ) < st.r0 ∧ st.t0 * st.t1 < 0)) at hspec
  rcases hspec with ⟨hinv, hrN, hcase⟩
  have hmod_rt : q.num * st.t1 ≡ (q.den : ℤ) * st.r1 [ZMOD M] :=
    calc q.num * st.t1 ≡ u * q.den * st.t1 [ZMOD M] := hmod.mul_right _
      _ = q.den * (st.t1 * u) := by ring
      _ ≡ q.den * st.r1 [ZMOD M] := (hinv.mod1.mul_left _).symm
  -- Once `|t1| ≤ D`, both cross products are below `M / 2`, so they agree.
  have hcross (ht : st.t1.natAbs ≤ D) : q.num * st.t1 = q.den * st.r1 :=
    mul_eq_mul_of_modEq_of_le hmod_rt hM (Nat.mul_le_mul hN ht)
      ((Nat.mul_le_mul hD (by have := hinv.r1_nonneg; omega)).trans_eq (mul_comm _ _))
  have hdiv_rt : q.num * st.t1 = q.den * st.r1 ∧ st.t1.natAbs = q.den := by
    rcases hcase with ⟨-, -, -, ht1⟩ | ⟨hr0, ht01⟩
    · have heq := hcross (by rw [ht1]; exact q.den_pos.trans_le hD)
      rw [ht1, mul_one] at heq
      have hd1 : q.den = 1 := Nat.eq_one_of_dvd_coprimes q.reduced
        ⟨st.r1.natAbs, by rw [heq, Int.natAbs_mul, Int.natAbs_natCast]⟩ dvd_rfl
      exact ⟨by rw [ht1, mul_one, heq], by rw [ht1, hd1, Int.natAbs_one]⟩
    · -- Write `(q.num, q.den) = x • (r0, t0) + y • (r1, t1)` by Cramer's rule.
      obtain ⟨s, hs1, hs2⟩ := hinv.bezout
      have hmod0 : (q.den : ℤ) * st.r0 ≡ q.num * st.t0 [ZMOD M] :=
        calc (q.den : ℤ) * st.r0 ≡ q.den * (st.t0 * u) [ZMOD M] := hinv.mod0.mul_left _
          _ = u * q.den * st.t0 := by ring
          _ ≡ q.num * st.t0 [ZMOD M] := hmod.symm.mul_right _
      obtain ⟨x, hx⟩ := dvd_mul_of_dvd_right hmod_rt.symm.dvd s
      obtain ⟨y, hy⟩ := dvd_mul_of_dvd_right hmod0.symm.dvd s
      have ha : q.num = x * st.r0 + y * st.r1 := mul_left_cancel₀ hM0 (by
        linear_combination st.r0 * hx + st.r1 * hy - s * q.num * hs2 - M * q.num * hs1)
      have hb : (q.den : ℤ) = x * st.t0 + y * st.t1 := mul_left_cancel₀ hM0 (by
        linear_combination st.t0 * hx + st.t1 * hy - s * q.den * hs2 - M * q.den * hs1)
      have hx0 : x = 0 := by
        by_contra hx0
        -- `x` and `y` have opposite signs, since otherwise `|q.num| ≥ r0 > N`.
        have hxy : x * y < 0 := by
          by_contra hxy
          have h := natAbs_add_of_mul_nonneg (a := x * st.r0) (b := y * st.r1) (by
            rw [mul_mul_mul_comm]
            exact mul_nonneg (not_lt.mp hxy) (mul_nonneg hinv.r0_pos.le hinv.r1_nonneg))
          rw [← ha, Int.natAbs_mul, Int.natAbs_mul] at h
          have := Nat.le_mul_of_pos_left st.r0.natAbs (Int.natAbs_pos.mpr hx0)
          omega
        -- Hence `x * t0` and `y * t1` have the same sign, so `|t1| ≤ q.den ≤ D`.
        have h := natAbs_add_of_mul_nonneg (a := x * st.t0) (b := y * st.t1) (by
          rw [mul_mul_mul_comm]
          exact (mul_pos_of_neg_of_neg hxy ht01).le)
        rw [← hb, Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_mul] at h
        have := Nat.le_mul_of_pos_left st.t1.natAbs
          (Int.natAbs_pos.mpr (right_ne_zero_of_mul hxy.ne))
        rw [sub_eq_zero.mpr (hcross (by omega)), mul_zero] at hx
        exact hx0 ((mul_eq_zero.mp hx.symm).resolve_left hM0)
      rw [hx0, zero_mul, zero_add] at ha hb
      have hbn := congrArg Int.natAbs hb
      rw [Int.natAbs_natCast, Int.natAbs_mul] at hbn
      have hy1 : y.natAbs = 1 := Nat.eq_one_of_dvd_coprimes q.reduced
        ⟨st.r1.natAbs, by rw [ha, Int.natAbs_mul]⟩ ⟨st.t1.natAbs, hbn⟩
      exact ⟨by rw [ha, hb]; ring, by rw [hbn, hy1, one_mul]⟩
  simp only [hdiv_rt.2, decide_eq_true (⟨hD, hcop⟩ : q.den ≤ D ∧ q.den.Coprime M), ↓reduceIte,
    Option.some.injEq]
  rw [← Rat.num_divInt_den q, Rat.divInt_eq_divInt_iff hinv.t1_ne (by exact_mod_cast q.den_nz)]
  exact (hdiv_rt.1.trans (mul_comm _ _)).symm

end WangReconstruction

section CRTReconstruction

open scoped Function

/-- Chinese-remainder rational reconstruction from residues in `∀ i, ZMod (m i)` across pairwise
coprime moduli `m : Fin k → ℕ`. -/
noncomputable def reconstructPi {k : ℕ} (m : Fin k → ℕ) (hcop : Pairwise (Nat.Coprime on m))
    (res : ∀ i, ZMod (m i)) (N D : ℕ) : Option ℚ :=
  reconstruct (∏ i, m i) (((ZMod.prodEquivPi m hcop).symm res).val : ℤ) N D

/-- Completeness of `Rat.reconstructPi`: if `∏ i, m i > 2 * N * D`, each `m i` is coprime to
`q.den`, and `res i` equals `(q.num : ZMod (m i)) * (q.den : ZMod (m i))⁻¹` for every `i`, then
`Rat.reconstructPi` recovers `some q`. -/
theorem reconstructPi_of_eq {k : ℕ} {m : Fin k → ℕ} (hcop : Pairwise (Nat.Coprime on m))
    {res : ∀ i, ZMod (m i)} {N D : ℕ} {q : ℚ}
    (hN : q.num.natAbs ≤ N) (hD : q.den ≤ D) (hM : 2 * N * D < ∏ i, m i)
    (hcop_den : ∀ i, Nat.Coprime q.den (m i))
    (hres : ∀ i, (q.num : ZMod (m i)) = res i * (q.den : ZMod (m i))) :
    reconstructPi m hcop res N D = some q := by
  let M := ∏ i, m i
  have : NeZero M := ⟨by have : 0 < M := Nat.zero_lt_of_lt hM; omega⟩
  let uZ : ZMod M := (ZMod.prodEquivPi m hcop).symm res
  have hcopM : Nat.Coprime q.den M := Nat.Coprime.prod_right fun i _ => hcop_den i
  have hcast : (q.num : ZMod M) = uZ * (q.den : ZMod M) := by
    apply (ZMod.prodEquivPi m hcop).injective
    ext i
    rw [map_mul, map_intCast, map_natCast, RingEquiv.apply_symm_apply]
    exact hres i
  have hmod : q.num ≡ (uZ.val : ℤ) * (q.den : ℤ) [ZMOD M] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    rw [← ZMod.natCast_zmod_val uZ] at hcast
    exact_mod_cast hcast
  exact reconstruct_of_eq hN hD hM hcopM hmod

end CRTReconstruction

end Rat
