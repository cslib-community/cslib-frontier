/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Algebra.Covering.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Certificates for an upper functional built from a family of elements

Fix a commutative monoid `M` with a covering relation `D`, an element `C`, a finite family
`A β` of elements and a number `η > 0`. A *certificate* of level `k` and weight at most `W` for
`t` (`Cslib.Covering.Certificate`) is a cover of `t * C ^ k` by products
`C ^ u * ∏ β, A β ^ v β` with `u + ∑ β, v β = k`, for which the numbers `η ^ (∑ β, v β)` add up to
at most `W`. Certificates multiply (adding levels and multiplying weights), can be raised to a
higher level, put together along covers, and multiplied by a member `A β` at the cost of a factor
`η` and one level. These constructions give the multiplication and cover premises of
`Cslib.Covering.isUpperFunctional_sInf` for the sets of certificate weights. A client that takes
the infimum of these weights as an upper functional must still establish the other premises of
that theorem: every weight set is nonempty (every element has a certificate), and every
certificate of `1` has weight at least `1` (`Certificate.one` gives only the weight `1` itself).

## Main definitions

* `Cslib.Covering.Certificate`: certificates.

## Main results

* `Cslib.Covering.Certificate.mul`, `Cslib.Covering.Certificate.raise`,
  `Cslib.Covering.Certificate.cover`, `Cslib.Covering.Certificate.mulGen`: constructions of
  certificates.
* `Cslib.Covering.Certificate.weight_nonneg`: weights of certificates are `≥ 0`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  the proof of Theorem A.6 (duality) of the paper; module `Nc.Price.Cover`
-/

public section

namespace Cslib.Covering

open Finset

variable {M : Type*} [CommMonoid M] {B : Type} [Fintype B]

/-- A *certificate* of level `k` and weight at most `W` for `t`: `t * C ^ k` is covered by the
products `C ^ u j * ∏ β, A β ^ v j β` with `u j + ∑ β, v j β = k`, and the numbers
`η ^ (∑ β, v j β)` add up to at most `W`. -/
structure Certificate (D : Covering M) (C : M) (A : B → M) (η : ℝ) (t : M) (k : ℕ) (W : ℝ) where
  /-- The index set of the cover. -/
  Index : Type
  [fintype : Fintype Index]
  /-- The exponent of `C` in each member of the cover. -/
  u : Index → ℕ
  /-- The exponents of the `A β` in each member of the cover. -/
  v : Index → B → ℕ
  level_eq : ∀ j, u j + ∑ β, v j β = k
  coveredBy : D.CoveredBy (t * C ^ k) fun j => C ^ u j * ∏ β, A β ^ v j β
  weight_le : ∑ j, η ^ (∑ β, v j β) ≤ W

attribute [instance] Certificate.fintype

namespace Certificate

variable {D : Covering M} {C : M} {A : B → M} {η : ℝ} {s t : M} {k l : ℕ} {W V : ℝ}

/-- Weights of certificates are `≥ 0`. -/
theorem weight_nonneg (hη : 0 < η) (c : Certificate D C A η t k W) : 0 ≤ W :=
  (Finset.sum_nonneg fun j _ => by positivity).trans c.weight_le

/-- `1` has a certificate of weight `1` at every level. -/
def one (k : ℕ) : Certificate D C A η 1 k 1 where
  Index := Unit
  u _ := k
  v _ _ := 0
  level_eq _ := by simp
  coveredBy := by simpa using D.refl (C ^ k)
  weight_le := by simp

/-- Certificates multiply: levels add and weights multiply. -/
def mul (hη : 0 < η) (c : Certificate D C A η s k W) (c' : Certificate D C A η t l V) :
    Certificate D C A η (s * t) (k + l) (W * V) where
  Index := Σ _ : c.Index, c'.Index
  u x := c.u x.1 + c'.u x.2
  v x β := c.v x.1 β + c'.v x.2 β
  level_eq x := by
    have := c.level_eq x.1
    have := c'.level_eq x.2
    rw [Finset.sum_add_distrib]
    omega
  coveredBy := by
    have e1 : s * t * C ^ (k + l) = s * C ^ k * (t * C ^ l) := by
      rw [pow_add]; exact mul_mul_mul_comm _ _ _ _
    rw [e1]
    convert D.mul_mul c.coveredBy c'.coveredBy using 2 with x
    simp only [pow_add, Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _
  weight_le := by
    rw [Fintype.sum_sigma]
    calc ∑ j, ∑ j', η ^ (∑ β, (c.v j β + c'.v j' β))
        = (∑ j, η ^ (∑ β, c.v j β)) * ∑ j', η ^ (∑ β, c'.v j' β) := by
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [← pow_add, Finset.sum_add_distrib]
      _ ≤ W * V := mul_le_mul c.weight_le c'.weight_le
          (Finset.sum_nonneg fun j _ => by positivity) (c.weight_nonneg hη)

/-- A certificate can be raised to a higher level. -/
def raise (hη : 0 < η) (c : Certificate D C A η t k W) (hkl : k ≤ l) :
    Certificate D C A η t l W := by
  have e : k + (l - k) = l := Nat.add_sub_cancel' hkl
  simpa only [mul_one, e] using c.mul hη (one (D := D) (C := C) (A := A) (η := η) (l - k))

/-- Certificates of the members of a cover of `t` give a certificate of `t`, whose weight is the
sum of the weights. -/
def cover {κ : Type} [Fintype κ] {b : κ → M} {W : κ → ℝ} (h : D.CoveredBy t b)
    (c : ∀ j, Certificate D C A η (b j) k (W j)) : Certificate D C A η t k (∑ j, W j) where
  Index := Σ j, (c j).Index
  u x := (c x.1).u x.2
  v x := (c x.1).v x.2
  level_eq x := (c x.1).level_eq x.2
  coveredBy := D.bind (b := fun j => b j * C ^ k) (D.mul _ h) fun j => (c j).coveredBy
  weight_le := by
    rw [Fintype.sum_sigma]
    exact Finset.sum_le_sum fun j _ => (c j).weight_le

/-- A certificate of `t * C` of level `k` gives one of `t * A β` of level `k + 1`, at the cost of
the factor `η`. -/
def mulGen [DecidableEq B] (hη : 0 < η) (β : B) (c : Certificate D C A η (t * C) k W) :
    Certificate D C A η (t * A β) (k + 1) (η * W) where
  Index := c.Index
  u := c.u
  v j γ := c.v j γ + if γ = β then 1 else 0
  level_eq j := by
    have := c.level_eq j
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ β)]
    omega
  coveredBy := by
    have e1 : t * A β * C ^ (k + 1) = t * C * C ^ k * A β := by rw [pow_succ]; ac_rfl
    rw [e1]
    convert D.mul (A β) c.coveredBy using 2 with j
    simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
      Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    ac_rfl
  weight_le := by
    calc ∑ j, η ^ (∑ γ, (c.v j γ + if γ = β then 1 else 0))
        = η * ∑ j, η ^ (∑ γ, c.v j γ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ β),
            pow_succ']
      _ ≤ η * W := mul_le_mul_of_nonneg_left c.weight_le hη.le

end Certificate

end Cslib.Covering
