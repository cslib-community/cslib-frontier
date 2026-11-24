/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.Antisymmetrization
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Equivalent tensors

Two tensors over a set of parties are *equivalent* when each is a restriction of the other,
`AntisymmRel (· ≤ ·) s t` for the restriction preorder; §A.1 of [AnthropicVPVNP2026] identifies
such tensors.
Tensors whose legs correspond to one another with equal entries are equivalent
(`PartyTensor.antisymmRel_of_equiv`). This file has the laws of products, products of families,
powers and push-forwards up to equivalence. The classes of tensors are Mathlib's
`Antisymmetrization (PartyTensor K I) (· ≤ ·)`, a partial order, and the product makes them a
commutative monoid, into which `toAntisymmetrization` is multiplicative; this is where the product
law for families is proved, once.

## Main results

* `Cslib.PartyTensor.antisymmRel_of_equiv`: tensors with matching legs and entries.
* `Cslib.PartyTensor.antisymmRel_mul`: products of equivalent tensors are equivalent.
* `Cslib.PartyTensor.antisymmRel_mul_comm`, `Cslib.PartyTensor.antisymmRel_mul_assoc`,
  `Cslib.PartyTensor.antisymmRel_one_mul`, `Cslib.PartyTensor.antisymmRel_mul_one`: the product
  is a commutative monoid up to equivalence.
* `Cslib.PartyTensor.antisymmRel_prod_reindex`, `Cslib.PartyTensor.antisymmRel_prod_of_isEmpty`,
  `Cslib.PartyTensor.antisymmRel_prod_unique`, `Cslib.PartyTensor.antisymmRel_prod_sum`,
  `Cslib.PartyTensor.antisymmRel_prod_fin_succ`: products of families.
* `Cslib.PartyTensor.antisymmRel_push_id`, `Cslib.PartyTensor.antisymmRel_push_push`,
  `Cslib.PartyTensor.antisymmRel_push_mul`, `Cslib.PartyTensor.antisymmRel_push_one`,
  `Cslib.PartyTensor.antisymmRel_push_prod`: push-forwards.
* `Cslib.PartyTensor.toAntisymmetrization_mul`, `Cslib.PartyTensor.toAntisymmetrization_pow`,
  `Cslib.PartyTensor.toAntisymmetrization_prod`, `Cslib.PartyTensor.toAntisymmetrization_prod_pow`:
  the class map is multiplicative.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  modules `Ov.Core.Equi`, `Ov.Duality.Minimal` (the monoid of classes) and `Nc.Price.Cover`
  (`cls_prod`, `cls_mon`)
-/

public section

namespace Cslib.PartyTensor

variable {K : Type} [CommSemiring K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
  [DecidableEq J]

/-- Tensors whose index sets correspond to one another, leg by leg, with equal entries are
equivalent. -/
theorem antisymmRel_of_equiv {s t : PartyTensor K I} (e : ∀ p, s.Index p ≃ t.Index p)
    (h : ∀ x, s.entry x = t.entry (fun p => e p (x p))) : AntisymmRel (· ≤ ·) s t :=
  ⟨le_of_entry_eq (fun p => e p) h, le_of_entry_eq (fun p => (e p).symm) fun y => by simp [h]⟩

/-- Products of equivalent tensors are equivalent. -/
theorem antisymmRel_mul {s t s' t' : PartyTensor K I} (h : AntisymmRel (· ≤ ·) s s')
    (h' : AntisymmRel (· ≤ ·) t t') : AntisymmRel (· ≤ ·) (s * t) (s' * t') :=
  ⟨mul_le_mul' h.1 h'.1, mul_le_mul' h.2 h'.2⟩

/-! ### Products -/

/-- The product is commutative. -/
theorem antisymmRel_mul_comm (s t : PartyTensor K I) : AntisymmRel (· ≤ ·) (s * t) (t * s) :=
  antisymmRel_of_equiv (fun _ => Equiv.prodComm _ _) fun _ => mul_comm _ _

/-- The product is associative. -/
theorem antisymmRel_mul_assoc (s t u : PartyTensor K I) :
    AntisymmRel (· ≤ ·) (s * t * u) (s * (t * u)) :=
  antisymmRel_of_equiv (fun _ => Equiv.prodAssoc _ _ _) fun _ => mul_assoc _ _ _

/-- `1` is neutral. -/
theorem antisymmRel_one_mul (t : PartyTensor K I) : AntisymmRel (· ≤ ·) (1 * t) t :=
  antisymmRel_of_equiv (fun p => Equiv.punitProd (t.Index p)) fun _ => one_mul _

/-- `1` is neutral. -/
theorem antisymmRel_mul_one (t : PartyTensor K I) : AntisymmRel (· ≤ ·) (t * 1) t :=
  antisymmRel_of_equiv (fun p => Equiv.prodPUnit (t.Index p)) fun _ => mul_one _

section Prod

variable {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

/-- Renaming the factors of a product. -/
theorem antisymmRel_prod_reindex (b : κ → PartyTensor K I) (e : κ' ≃ κ) :
    AntisymmRel (· ≤ ·) (prod b) (prod fun k => b (e k)) :=
  AntisymmRel.symm <|
    antisymmRel_of_equiv (fun p => Equiv.piCongrLeft (fun k => (b k).Index p) e) fun x => by
      rw [prod_entry, prod_entry]
      refine Fintype.prod_equiv e _ _ fun k => congrArg (b (e k)).entry (funext fun p => ?_)
      exact (Equiv.piCongrLeft_apply_apply (fun k => (b k).Index p) e (x p) k).symm

/-- The product of the empty family is `1`. -/
theorem antisymmRel_prod_of_isEmpty [IsEmpty κ] (b : κ → PartyTensor K I) :
    AntisymmRel (· ≤ ·) (prod b) 1 :=
  antisymmRel_of_equiv (fun p => show (∀ k, (b k).Index p) ≃ Unit from Equiv.equivPUnit _)
    fun x => by simp [prod_entry]

/-- The product of a family with one member. -/
theorem antisymmRel_prod_unique [Unique κ] (b : κ → PartyTensor K I) :
    AntisymmRel (· ≤ ·) (prod b) (b default) :=
  antisymmRel_of_equiv (fun _ => Equiv.piUnique _) fun x => by
    rw [prod_entry, Fintype.prod_unique]
    rfl

/-- The product over a disjoint union. -/
theorem antisymmRel_prod_sum (b : κ ⊕ κ' → PartyTensor K I) :
    AntisymmRel (· ≤ ·) (prod b) (prod (fun k => b (.inl k)) * prod (fun k => b (.inr k))) :=
  antisymmRel_of_equiv (fun p => Equiv.sumPiEquivProdPi fun k => (b k).Index p)
    fun x => by rw [prod_entry, Fintype.prod_sum_type]; rfl

end Prod

/-- The product of a family indexed by `0, …, n` is its first member times the product of the
others. -/
theorem antisymmRel_prod_fin_succ {n : ℕ} (b : Fin (n + 1) → PartyTensor K I) :
    AntisymmRel (· ≤ ·) (prod b) (b 0 * prod fun k : Fin n => b k.succ) :=
  antisymmRel_of_equiv (fun p => (Fin.consEquiv fun k => (b k).Index p).symm)
    fun x => by rw [prod_entry, Fin.prod_univ_succ]; rfl

/-- The product of a family of two tensors. -/
theorem antisymmRel_prod_fin_two (b : Fin 2 → PartyTensor K I) :
    AntisymmRel (· ≤ ·) (prod b) (b 0 * b 1) :=
  (antisymmRel_prod_fin_succ b).trans (antisymmRel_mul .rfl (antisymmRel_prod_unique _))

/-! ### Powers -/

/-- The power with exponent `0`. -/
theorem antisymmRel_pow_zero (t : PartyTensor K I) : AntisymmRel (· ≤ ·) (t ^ 0) 1 :=
  antisymmRel_prod_of_isEmpty (fun _ : Fin 0 => t)

/-- The power with exponent `k + 1`. -/
theorem antisymmRel_pow_succ (t : PartyTensor K I) (k : ℕ) :
    AntisymmRel (· ≤ ·) (t ^ (k + 1)) (t * t ^ k) :=
  antisymmRel_prod_fin_succ (fun _ : Fin (k + 1) => t)

/-! ### Push-forwards -/

section Push

variable {L : Type} [Fintype L] [DecidableEq L]

/-- Giving each leg to the party of its own name changes nothing, up to equivalence. -/
theorem antisymmRel_push_id (t : PartyTensor K I) : AntisymmRel (· ≤ ·) (push id t) t :=
  antisymmRel_of_equiv
    (fun q => ⟨fun y => y ⟨q, rfl⟩, fun a j => (show q = j.val from j.property.symm) ▸ a,
      fun y => by funext ⟨j, hj⟩; cases hj; rfl, fun _ => rfl⟩)
    fun _ => rfl

/-- Giving legs away twice. -/
theorem antisymmRel_push_push (π : J → I) (ρ : L → J) (t : PartyTensor K L) :
    AntisymmRel (· ≤ ·) (push π (push ρ t)) (push (π ∘ ρ) t) :=
  antisymmRel_of_equiv
    (fun q => ⟨fun y i => y ⟨ρ i.val, i.property⟩ ⟨i.val, rfl⟩, fun z j i => z ⟨i.val, by
        rw [Function.comp, i.property]; exact j.property⟩, fun y => by
        funext ⟨j, hj⟩ ⟨i, hi⟩
        cases hj
        cases hi
        rfl, fun _ => rfl⟩)
    fun _ => rfl

/-- Giving the legs of a product away. -/
theorem antisymmRel_push_mul (π : J → I) (s t : PartyTensor K J) :
    AntisymmRel (· ≤ ·) (push π (s * t)) (push π s * push π t) :=
  antisymmRel_of_equiv (fun _ => Equiv.arrowProdEquivProdArrow _ _ _) fun _ => rfl

/-- Giving the legs of `1` away. -/
theorem antisymmRel_push_one (π : J → I) : AntisymmRel (· ≤ ·) (push π (1 : PartyTensor K J)) 1 :=
  antisymmRel_of_equiv
    (fun q => show ({j : J // π j = q} → Unit) ≃ Unit from Equiv.equivPUnit _) fun _ => rfl

/-- Giving the legs of the product of a family away. -/
theorem antisymmRel_push_prod {κ : Type} [Fintype κ] [DecidableEq κ] (π : J → I)
    (b : κ → PartyTensor K J) :
    AntisymmRel (· ≤ ·) (push π (prod b)) (prod fun k => push π (b k)) :=
  antisymmRel_of_equiv (fun _ => Equiv.piComm _) fun _ => rfl

/-- Giving the legs of a power away. -/
theorem antisymmRel_push_pow (π : J → I) (t : PartyTensor K J) (k : ℕ) :
    AntisymmRel (· ≤ ·) (push π (t ^ k)) (push π t ^ k) :=
  antisymmRel_push_prod π (fun _ : Fin k => t)

end Push

/-! ### Classes of tensors -/

/-- A representative of the class of `t` is equivalent to `t`. -/
theorem antisymmRel_ofAntisymmetrization_toAntisymmetrization (t : PartyTensor K I) :
    AntisymmRel (· ≤ ·) (ofAntisymmetrization (· ≤ ·) (toAntisymmetrization (· ≤ ·) t)) t :=
  (toAntisymmetrization_eq _ _ _).1 (toAntisymmetrization_ofAntisymmetrization _ _)

/-- The classes of tensors form a commutative monoid under the product. -/
instance : CommMonoid (Antisymmetrization (PartyTensor K I) (· ≤ ·)) where
  one := toAntisymmetrization (· ≤ ·) 1
  mul := Quotient.map₂ (· * ·) fun _ _ h _ _ h' => antisymmRel_mul h h'
  mul_assoc x y z := by
    induction x using Antisymmetrization.ind
    induction y using Antisymmetrization.ind
    induction z using Antisymmetrization.ind
    exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_mul_assoc _ _ _)
  one_mul x := by
    induction x using Antisymmetrization.ind
    exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_one_mul _)
  mul_one x := by
    induction x using Antisymmetrization.ind
    exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_mul_one _)
  mul_comm x y := by
    induction x using Antisymmetrization.ind
    induction y using Antisymmetrization.ind
    exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_mul_comm _ _)

theorem toAntisymmetrization_one : toAntisymmetrization (· ≤ ·) (1 : PartyTensor K I) = 1 := rfl

theorem toAntisymmetrization_mul (s t : PartyTensor K I) :
    toAntisymmetrization (· ≤ ·) (s * t) =
      toAntisymmetrization (· ≤ ·) s * toAntisymmetrization (· ≤ ·) t :=
  rfl

theorem toAntisymmetrization_pow (t : PartyTensor K I) (n : ℕ) :
    toAntisymmetrization (· ≤ ·) (t ^ n) = toAntisymmetrization (· ≤ ·) t ^ n := by
  induction n with
  | zero => exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_pow_zero t)
  | succ n ih =>
    rw [pow_succ', ← ih, ← toAntisymmetrization_mul]
    exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_pow_succ t n)

theorem toAntisymmetrization_prod {κ : Type} [Fintype κ] [DecidableEq κ]
    (b : κ → PartyTensor K I) :
    toAntisymmetrization (· ≤ ·) (prod b) = ∏ k, toAntisymmetrization (· ≤ ·) (b k) := by
  have key : ∀ {n : ℕ} (b : Fin n → PartyTensor K I),
      toAntisymmetrization (· ≤ ·) (prod b) = ∏ k, toAntisymmetrization (· ≤ ·) (b k) := by
    intro n
    induction n with
    | zero => exact fun b => (toAntisymmetrization_eq _ _ _).2 (antisymmRel_prod_of_isEmpty b)
    | succ n ih =>
      intro b
      rw [Fin.prod_univ_succ, ← ih, ← toAntisymmetrization_mul]
      exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_prod_fin_succ b)
  rw [(toAntisymmetrization_eq _ _ _).2 (antisymmRel_prod_reindex b (Fintype.equivFin κ).symm),
    key]
  exact Fintype.prod_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

/-- The class of a product of powers of tensors. -/
theorem toAntisymmetrization_prod_pow {B : Type} [Fintype B] [DecidableEq B]
    (A : B → PartyTensor K I) (v : B → ℕ) :
    toAntisymmetrization (· ≤ ·) (prod fun β => A β ^ v β) =
      ∏ β, toAntisymmetrization (· ≤ ·) (A β) ^ v β := by
  rw [toAntisymmetrization_prod]
  exact Finset.prod_congr rfl fun β _ => toAntisymmetrization_pow _ _

end Cslib.PartyTensor
