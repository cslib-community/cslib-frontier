/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Pointwise
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Upper functionals on a commutative monoid with a covering relation

Let `M` be a commutative monoid with a relation "`t` is covered by the finite family `b`"
(`Cslib.Covering`): reflexive, transitive and compatible with multiplication by an element. For
tensors up to equivalence, `t` is covered by `b` when it is a sum of restrictions of the members
of `b` (`Cslib.PartyTensor.tensorCovering`). An *upper functional*
(`Cslib.Covering.IsUpperFunctional`) is a function `p ≥ 0` on `M` with `p 1 = 1`,
`p (s * t) ≤ p s * p t`, and `p t ≤ ∑ k, p (b k)` whenever `b` covers `t`. It *respects* the
triple `(x, y, c)` (`Cslib.Covering.Respects`) when `p (t * x) ≤ c * p (t * y)` for all `t`.

Upper functionals arise as infima: of a directed family of functions that are almost upper
functionals (`Covering.isUpperFunctional_iInf`), and of the weights of certificates that can be
multiplied and put together along covers (`Covering.isUpperFunctional_sInf`). The *radius set* of
`p` at `t` (`Covering.radiusSet`) consists of the `a > 0` with `p (t ^ m) ≤ C * a ^ m` for some
`C` and all `m`; its infimum is the spectral radius of `p` at `t`.

## Main definitions

* `Cslib.Covering`: covering relations on a commutative monoid.
* `Cslib.Covering.IsUpperFunctional`: upper functionals.
* `Cslib.Covering.Respects`: the inequality `p (t * x) ≤ c * p (t * y)` for all `t`.
* `Cslib.Covering.radiusSet`: the growth rates of `p` along the powers of `t`.

## Main results

* `Cslib.Covering.isUpperFunctional_iInf`, `Cslib.Covering.respects_iInf`: directed infima.
* `Cslib.Covering.isUpperFunctional_sInf`, `Cslib.Covering.respects_sInf`: infima of
  certificate weights.
* `Cslib.Covering.IsUpperFunctional.map_prod_pow_le`: a bound for a product of powers.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  §A.4 of the paper; modules `Ov.Duality.Abstract` (`IsPre` is `IsUpperFunctional`, `Keeps` is
  `Respects`) and `Ov.Duality.Cert`
-/

public section

namespace Cslib

open Finset

/-- A covering relation on a commutative monoid: a relation between elements and finite families
of elements, reflexive, transitive, and compatible with multiplication by an element. -/
structure Covering (M : Type*) [CommMonoid M] where
  /-- The element is covered by the family. -/
  CoveredBy : ∀ {κ : Type} [Fintype κ], M → (κ → M) → Prop
  refl : ∀ t, CoveredBy t fun _ : Unit => t
  bind : ∀ {κ : Type} [Fintype κ] {μ : κ → Type} [∀ k, Fintype (μ k)] {t : M} {b : κ → M}
    {c : ∀ k, μ k → M}, CoveredBy t b → (∀ k, CoveredBy (b k) (c k)) →
      CoveredBy t fun x : Σ k, μ k => c x.1 x.2
  mul : ∀ {κ : Type} [Fintype κ] {t : M} {b : κ → M} (s : M), CoveredBy t b →
    CoveredBy (t * s) fun k => b k * s

namespace Covering

variable {M : Type*} [CommMonoid M]

/-- Covers can be multiplied. -/
theorem mul_mul (D : Covering M) {κ κ' : Type} [Fintype κ] [Fintype κ'] {s t : M} {b : κ → M}
    {c : κ' → M} (h : D.CoveredBy s b) (h' : D.CoveredBy t c) :
    D.CoveredBy (s * t) fun x : Σ _ : κ, κ' => b x.1 * c x.2 := by
  refine D.bind (b := fun k => b k * t) (c := fun k j => b k * c j) (D.mul t h) fun k => ?_
  simpa only [mul_comm _ (b k)] using D.mul (b k) h'

/-- `p` is an *upper functional* for the covering relation `D`: `p ≥ 0`, `p 1 = 1`, `p` is
submultiplicative, and subadditive under covers. -/
structure IsUpperFunctional (D : Covering M) (p : M → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ p t
  map_one : p 1 = 1
  map_mul_le : ∀ s t, p (s * t) ≤ p s * p t
  le_sum : ∀ {κ : Type} [Fintype κ] (t : M) (b : κ → M), D.CoveredBy t b → p t ≤ ∑ k, p (b k)

/-- The inequality `p (t * x) ≤ c * p (t * y)` for all `t`. -/
@[expose] def Respects (p : M → ℝ) (x y : M) (c : ℝ) : Prop := ∀ t, p (t * x) ≤ c * p (t * y)

variable {D : Covering M} {p : M → ℝ}

/-! ### Directed infima -/

omit [CommMonoid M] in
/-- For finitely many elements, one member of a directed family is close to its infimum. -/
private theorem exists_le_iInf_add {ι : Type*} [Nonempty ι] {P : ι → M → ℝ}
    (dir : Directed (· ≥ ·) P) {ε : ℝ}
    (hε : 0 < ε) (b : Finset M) : ∃ i, ∀ t ∈ b, P i t ≤ (⨅ i, P i t) + ε := by
  classical
  induction b using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | insert a b _ ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := exists_lt_of_ciInf_lt (lt_add_of_pos_right (⨅ i, P i a) hε)
    obtain ⟨k, hki, hkj⟩ := dir i j
    refine ⟨k, fun t ht => ?_⟩
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact (hkj t).trans hj.le
    · exact (hki t).trans (hi t ht)

/-- A sum over `κ` of terms each within `δ / (#κ + 1)` of another is within `δ`. -/
private theorem card_mul_div_le {κ : Type} [Fintype κ] {δ : ℝ} (hδ : 0 < δ) :
    (Fintype.card κ : ℝ) * (δ / (Fintype.card κ + 1)) ≤ δ := by
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-- A directed infimum of functions `P i` is an upper functional if each of them is, where
instead of `P i (s * t) ≤ P i s * P i t` it is enough that `P j (s * t) ≤ P i s * P i t` for some
`j`. -/
theorem isUpperFunctional_iInf {ι : Type*} [Nonempty ι] {P : ι → M → ℝ}
    (dir : Directed (· ≥ ·) P) (nonneg : ∀ i t, 0 ≤ P i t) (one : ∀ i, P i 1 = 1)
    (mul_le : ∀ i s t, ∃ j, P j (s * t) ≤ P i s * P i t)
    (le_sum : ∀ i, ∀ {κ : Type} [Fintype κ] (t : M) (b : κ → M), D.CoveredBy t b →
      P i t ≤ ∑ k, P i (b k)) :
    IsUpperFunctional D fun t => ⨅ i, P i t := by
  classical
  have bdd : ∀ t, BddBelow (Set.range fun i => P i t) := fun t =>
    ⟨0, by rintro _ ⟨i, rfl⟩; exact nonneg i t⟩
  have hle : ∀ i t, ⨅ j, P j t ≤ P i t := fun i t => ciInf_le (bdd t) i
  have h0 : ∀ t, 0 ≤ ⨅ i, P i t := fun t => le_ciInf fun i => nonneg i t
  refine ⟨h0, by simp [one], fun s t => ?_, @fun κ _ t b hb => ?_⟩
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    set A := ⨅ i, P i s
    set B := ⨅ i, P i t
    have hA0 : 0 ≤ A := h0 s
    have hB0 : 0 ≤ B := h0 t
    obtain ⟨ε, hε, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε * (A + B + 1) ≤ δ := by
      refine ⟨min 1 (δ / (A + B + 1)), by positivity, min_le_left _ _, ?_⟩
      calc min 1 (δ / (A + B + 1)) * (A + B + 1) ≤ δ / (A + B + 1) * (A + B + 1) := by
            gcongr; exact min_le_right _ _
        _ = δ := by field_simp
    obtain ⟨i, hi⟩ := exists_le_iInf_add dir hε {s, t}
    obtain ⟨j, hj⟩ := mul_le i s t
    have h3 : P i s * P i t ≤ (A + ε) * (B + ε) :=
      mul_le_mul (hi s (by simp)) (hi t (by simp)) (nonneg _ _) (by positivity)
    have h4 := hle j (s * t)
    nlinarith
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨i, hi⟩ := exists_le_iInf_add dir (ε := δ / (Fintype.card κ + 1))
      (by positivity) (Finset.univ.image b)
    have h1 : ∑ k, P i (b k) ≤ ∑ k, ((⨅ i, P i (b k)) + δ / (Fintype.card κ + 1)) :=
      Finset.sum_le_sum fun k _ => hi _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    linarith [(hle i t).trans (le_sum i t b hb), card_mul_div_le (κ := κ) hδ]

/-- A directed infimum respects a triple that each member respects. -/
theorem respects_iInf {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (nonneg : ∀ i t, 0 ≤ P i t)
    {x y : M} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, Respects (P i) x y c) :
    Respects (fun t => ⨅ i, P i t) x y c := by
  intro t
  rw [Real.mul_iInf_of_nonneg hc]
  refine le_ciInf fun i => (ciInf_le ⟨0, ?_⟩ i).trans (h i t)
  rintro _ ⟨i, rfl⟩
  exact nonneg i _

/-! ### Infima of certificate weights -/

/-- `x ≤ inf S * inf T` when `x ≤ a * b` for all `a ∈ S` and `b ∈ T`, for nonempty sets of
numbers `≥ 0`. -/
theorem le_sInf_mul_sInf {S T : Set ℝ} (hS : S.Nonempty) (hT : T.Nonempty)
    (hS0 : ∀ a ∈ S, 0 ≤ a) (hT0 : ∀ b ∈ T, 0 ≤ b) {x : ℝ} (h : ∀ a ∈ S, ∀ b ∈ T, x ≤ a * b) :
    x ≤ sInf S * sInf T := by
  have key : ∀ {S : Set ℝ} (_ : S.Nonempty) {b : ℝ} (_ : 0 ≤ b), (∀ a ∈ S, x ≤ a * b) →
      x ≤ sInf S * b := by
    intro S hS b hb h
    rcases hb.eq_or_lt with rfl | hb
    · obtain ⟨a, ha⟩ := hS
      simpa using h a ha
    · rw [← div_le_iff₀ hb]
      exact le_csInf hS fun a ha => (div_le_iff₀ hb).2 (h a ha)
  rw [mul_comm]
  refine key hT (Real.sInf_nonneg hS0) fun b hb => ?_
  rw [mul_comm]
  exact key hS (hT0 b hb) fun a ha => h a ha b hb

/-- Let `S t` be sets of numbers `≥ 0`, the weights of the certificates for `t`. Their infimum is
an upper functional if certificates can be multiplied and put together along covers, `1` has a
certificate of weight `1`, and none of a weight below `1`. -/
theorem isUpperFunctional_sInf {S : M → Set ℝ} (hne : ∀ t, (S t).Nonempty)
    (h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w)
    (h1 : (1 : ℝ) ∈ S 1) (h1' : ∀ w ∈ S 1, 1 ≤ w)
    (hmul : ∀ s t, ∀ a ∈ S s, ∀ b ∈ S t, a * b ∈ S (s * t))
    (hsum : ∀ {κ : Type} [Fintype κ] (t : M) (b : κ → M), D.CoveredBy t b → ∀ w : κ → ℝ,
      (∀ k, w k ∈ S (b k)) → ∃ w' ∈ S t, w' ≤ ∑ k, w k) :
    IsUpperFunctional D fun t => sInf (S t) := by
  have bdd : ∀ t, BddBelow (S t) := fun t => ⟨0, fun _ hw => h0 t _ hw⟩
  refine ⟨fun t => Real.sInf_nonneg (h0 t), ?_, fun s t => ?_, @fun κ _ t b hb => ?_⟩
  · exact le_antisymm (csInf_le (bdd 1) h1) (le_csInf (hne 1) h1')
  · exact le_sInf_mul_sInf (hne s) (hne t) (h0 s) (h0 t) fun a ha b hb =>
      csInf_le (bdd _) (hmul s t a ha b hb)
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hε : 0 < δ / (Fintype.card κ + 1) := by positivity
    choose w hw hw' using fun k => exists_lt_of_csInf_lt (hne (b k)) (lt_add_of_pos_right _ hε)
    obtain ⟨w', hw'S, hle⟩ := hsum t b hb w hw
    have h2 : ∑ k, w k ≤ ∑ k, (sInf (S (b k)) + δ / (Fintype.card κ + 1)) :=
      Finset.sum_le_sum fun k _ => (hw' k).le
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    linarith [csInf_le (bdd t) hw'S, card_mul_div_le (κ := κ) hδ]

/-- The infimum of certificate weights respects a triple if certificates can be transported
with the factor `c`. -/
theorem respects_sInf {S : M → Set ℝ} (hne : ∀ t, (S t).Nonempty) (h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w)
    {x y : M} {c : ℝ} (hc : 0 < c) (h : ∀ t, ∀ w ∈ S (t * y), c * w ∈ S (t * x)) :
    Respects (fun t => sInf (S t)) x y c := by
  intro t
  have h2 : sInf (S (t * x)) / c ≤ sInf (S (t * y)) := by
    refine le_csInf (hne _) fun a ha => ?_
    rw [div_le_iff₀ hc]
    exact (csInf_le ⟨0, fun _ hw => h0 _ _ hw⟩ (h t a ha)).trans (mul_comm _ _).le
  rw [div_le_iff₀ hc] at h2
  exact h2.trans (mul_comm _ _).le

/-! ### Growth along powers -/

/-- The numbers `a > 0` for which there is a `C` with `p (t ^ m) ≤ C * a ^ m` for all `m`. Their
infimum is the spectral radius of `p` at `t`. -/
@[expose] def radiusSet (p : M → ℝ) (t : M) : Set ℝ :=
  {a | 0 < a ∧ ∃ C : ℝ, ∀ m : ℕ, p (t ^ m) ≤ C * a ^ m}

theorem bddBelow_radiusSet (p : M → ℝ) (t : M) : BddBelow (radiusSet p t) :=
  ⟨0, fun _ ha => ha.1.le⟩

namespace IsUpperFunctional

theorem map_pow_le (h : IsUpperFunctional D p) (t : M) (n : ℕ) : p (t ^ n) ≤ p t ^ n := by
  induction n with
  | zero => simp [h.map_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (h.map_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (h.nonneg _))

/-- The constant of a growth bound is at least `1`. -/
theorem one_le_of_map_pow_le (h : IsUpperFunctional D p) {t : M} {a C : ℝ}
    (hC : ∀ m : ℕ, p (t ^ m) ≤ C * a ^ m) : 1 ≤ C := by
  simpa [h.map_one] using hC 0

theorem mem_radiusSet_of_le (h : IsUpperFunctional D p) {t : M} {a b : ℝ} (ha : a ∈ radiusSet p t)
    (hab : a ≤ b) : b ∈ radiusSet p t := by
  obtain ⟨ha0, C, hC⟩ := ha
  have hC1 := h.one_le_of_map_pow_le hC
  refine ⟨ha0.trans_le hab, C, fun m => (hC m).trans ?_⟩
  gcongr

theorem add_mem_radiusSet (h : IsUpperFunctional D p) (t : M) {δ : ℝ} (hδ : 0 < δ) :
    p t + δ ∈ radiusSet p t :=
  ⟨by linarith [h.nonneg t], 1, fun m => by
    rw [one_mul]
    exact (h.map_pow_le t m).trans (pow_le_pow_left₀ (h.nonneg t) (by linarith) m)⟩

theorem mem_radiusSet_of_sInf_lt (h : IsUpperFunctional D p) {t : M} {a : ℝ}
    (ha : sInf (radiusSet p t) < a) : a ∈ radiusSet p t := by
  obtain ⟨b, hb, hba⟩ := exists_lt_of_csInf_lt ⟨_, h.add_mem_radiusSet t one_pos⟩ ha
  exact h.mem_radiusSet_of_le hb hba.le

/-- The bound for a product of powers, by the bounds for the powers. -/
theorem map_prod_pow_le (h : IsUpperFunctional D p) (S : Finset M) (a C : M → ℝ) (ha : ∀ y, 0 < a y)
    (hC : ∀ y, ∀ m : ℕ, p (y ^ m) ≤ C y * a y ^ m) (e : M → ℕ) :
    p (∏ y ∈ S, y ^ e y) ≤ (∏ y ∈ S, C y) * ∏ y ∈ S, a y ^ e y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [h.map_one]
  | insert y S hy ih =>
    rw [Finset.prod_insert hy, Finset.prod_insert hy, Finset.prod_insert hy]
    have hC0 : 0 ≤ C y * a y ^ e y :=
      mul_nonneg (zero_le_one.trans (h.one_le_of_map_pow_le (hC y))) (pow_nonneg (ha y).le _)
    calc p (y ^ e y * ∏ x ∈ S, x ^ e x)
        ≤ C y * a y ^ e y * ((∏ x ∈ S, C x) * ∏ x ∈ S, a x ^ e x) :=
          (h.map_mul_le _ _).trans (mul_le_mul (hC y (e y)) ih (h.nonneg _) hC0)
      _ = _ := by ring

end IsUpperFunctional

end Covering

end Cslib
