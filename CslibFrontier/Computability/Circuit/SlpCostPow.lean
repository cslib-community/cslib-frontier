/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.SlpCost
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Costs of straight-line programs in powers of one number

The costs of `Cslib.Circuits.Cost` and `Cslib.Circuits.CostP` are counted here in powers of one
number `Y`, the base (`Cslib.Circuits.StepBase D Y`): `3 ≤ Y`, and the alphabet `Fin D` holds
all numbers below `Y ^ 4`. Then a binary operation, a relation or a connective raises the
exponent of the cost by one; a sum, a count or a bounded quantifier over at most `Y` elements and
a choice raise it by two. A family of at most `Y ^ e` functions, each computed in `Y ^ a` steps
with `a + e ≤ k`, is added to a straight-line program in one *stage* of `Y ^ k` gates
(`Cslib.Circuits.StepBase.stage`). The functions and indicators that are computed already cost
nothing (`Cslib.Circuits.Cost.of_mem`, `Cslib.Circuits.CostP.of_mem`).

## Main definitions

* `Cslib.Circuits.StepBase`: the base of the costs.

## Main results

* `Cslib.Circuits.Cost.of_mem`, `Cslib.Circuits.CostP.of_mem`: the functions and the indicators
  that are computed already.
* `Cslib.Circuits.StepBase.lt_of_le`, `StepBase.lt_of_le_two_mul_pow_three`, `StepBase.one_lt`:
  the letters of the alphabet.
* `Cslib.Circuits.StepBase.const`, `StepBase.op`, `StepBase.op1`, `StepBase.sum`,
  `StepBase.ite`, `StepBase.card_filter`: the rules of `Cost` in powers of the base;
  `StepBase.constP`, `StepBase.rel`, `StepBase.rel1`, `StepBase.and`, `StepBase.or`,
  `StepBase.not`, `StepBase.exists_mem`, `StepBase.forall_mem`, `StepBase.exists_univ`,
  `StepBase.forall_univ`: those of `CostP`.
* `Cslib.Circuits.StepBase.stage`: a family of functions takes one stage of a program.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(d), p. 46, and its proof ("For (d)", p. 48); module `Nc.Tow.Slp0`
-/

public section

namespace Cslib.Circuits

open Finset

variable {Inp : Type} {D Y a : ℕ} {H : Set (Inp → ℕ)} {f g : Inp → ℕ} {P Q : Inp → Prop}

/-- A function of `H` is computed from `H` in any number of steps. -/
theorem Cost.of_mem {c : ℕ} (hf : f ∈ H) : Cost D H c f :=
  (Cost.base hf).mono (Nat.zero_le c)

/-- A property whose indicator is a function of `H` is decided from `H` in any number of
steps. -/
theorem CostP.of_mem {c : ℕ} (hP : {x | P x}.indicator 1 ∈ H) : CostP D H c P :=
  costP_iff.2 (Cost.of_mem hP)

/-- The base `Y` of the costs of programs over the alphabet `Fin D`: `3 ≤ Y`, and the alphabet
holds all numbers below `Y ^ 4`. -/
structure StepBase (D Y : ℕ) : Prop where
  three_le : 3 ≤ Y
  pow_four_le : Y ^ 4 ≤ D

namespace StepBase

variable (hY : StepBase D Y)
include hY

theorem pos : 0 < Y := by
  have := hY.three_le
  omega

/-- The numbers up to `2 * Y ^ 3` are letters. -/
theorem lt_of_le_two_mul_pow_three {k : ℕ} (hk : k ≤ 2 * Y ^ 3) : k < D := by
  have h3 := hY.three_le
  have h4 : 2 * Y ^ 3 < Y ^ 4 := by
    rw [pow_succ]
    nlinarith [Nat.one_le_pow 3 Y hY.pos]
  exact hk.trans_lt (h4.trans_le hY.pow_four_le)

/-- The numbers up to `Y` are letters. -/
theorem lt_of_le {k : ℕ} (hk : k ≤ Y) : k < D :=
  hY.lt_of_le_two_mul_pow_three (by nlinarith [Nat.le_self_pow (by norm_num : 3 ≠ 0) Y])

theorem one_lt : 1 < D :=
  hY.lt_of_le (by have := hY.three_le; omega)

theorem zero_lt : 0 < D :=
  zero_lt_one.trans hY.one_lt

private theorem pow_succ_bounds (a : ℕ) : 1 ≤ Y ^ a ∧ 3 * Y ^ a ≤ Y ^ (a + 1) :=
  ⟨Nat.one_le_pow a Y hY.pos, by rw [pow_succ, mul_comm 3]; exact Nat.mul_le_mul_left _ hY.three_le⟩

private theorem le_pow_add_two {s : ℕ} (hs : s ≤ Y) (a : ℕ) :
    s * (Y ^ a + 1) + 1 ≤ Y ^ (a + 2) := by
  obtain ⟨h1, h2⟩ := hY.pow_succ_bounds (a + 1)
  have h3 : s * (Y ^ a + 1) ≤ Y ^ (a + 1) + Y := (Nat.mul_le_mul_right _ hs).trans_eq (by ring)
  have h4 : Y ≤ Y ^ (a + 1) := Nat.le_self_pow (Nat.succ_ne_zero a) Y
  change _ ≤ Y ^ (a + 1 + 1)
  omega

/-! ### Functions -/

theorem const (c : ℕ) (hc : c < D) : Cost D H (Y ^ a) fun _ => c :=
  (Cost.const c hc).mono (hY.pow_succ_bounds a).1

theorem op (φ : ℕ → ℕ → ℕ) (hf : Cost D H (Y ^ a) f) (hg : Cost D H (Y ^ a) g)
    (hb : ∀ x, φ (f x) (g x) < D) : Cost D H (Y ^ (a + 1)) fun x => φ (f x) (g x) :=
  (Cost.op φ hf hg hb).mono (by have := hY.pow_succ_bounds a; omega)

theorem op1 (φ : ℕ → ℕ) (hf : Cost D H (Y ^ a) f) (hb : ∀ x, φ (f x) < D) :
    Cost D H (Y ^ (a + 1)) fun x => φ (f x) :=
  hY.op (fun s _ => φ s) hf (hY.const 0 hY.zero_lt) hb

theorem sum {κ : Type*} (s : Finset κ) {f : κ → Inp → ℕ} (hs : s.card ≤ Y)
    (hf : ∀ i ∈ s, Cost D H (Y ^ a) (f i)) (hb : ∀ x, ∑ i ∈ s, f i x < D) :
    Cost D H (Y ^ (a + 2)) fun x => ∑ i ∈ s, f i x :=
  (Cost.sum hY.zero_lt s hf hb).mono (hY.le_pow_add_two hs a)

theorem ite [DecidablePred P] (hP : CostP D H (Y ^ a) P) (hf : Cost D H (Y ^ a) f)
    (hg : Cost D H (Y ^ a) g) (hf' : ∀ x, f x < D) (hg' : ∀ x, g x < D) :
    Cost D H (Y ^ (a + 2)) fun x => if P x then f x else g x :=
  (Cost.ite hP hf hg hf' hg').mono (by
    have := hY.pow_succ_bounds a
    have := hY.pow_succ_bounds (a + 1)
    change _ ≤ Y ^ (a + 1 + 1)
    omega)

/-! ### Properties -/

theorem constP (P : Prop) : CostP D H (Y ^ a) fun _ => P :=
  (CostP.const hY.one_lt P).mono (hY.pow_succ_bounds a).1

theorem rel (r : ℕ → ℕ → Prop) (hf : Cost D H (Y ^ a) f) (hg : Cost D H (Y ^ a) g) :
    CostP D H (Y ^ (a + 1)) fun x => r (f x) (g x) :=
  (CostP.rel hY.one_lt r hf hg).mono (by have := hY.pow_succ_bounds a; omega)

theorem rel1 (r : ℕ → Prop) (hf : Cost D H (Y ^ a) f) :
    CostP D H (Y ^ (a + 1)) fun x => r (f x) :=
  hY.rel (fun s _ => r s) hf (hY.const 0 hY.zero_lt)

theorem and (hP : CostP D H (Y ^ a) P) (hQ : CostP D H (Y ^ a) Q) :
    CostP D H (Y ^ (a + 1)) fun x => P x ∧ Q x :=
  (hP.and hY.one_lt hQ).mono (by have := hY.pow_succ_bounds a; omega)

theorem or (hP : CostP D H (Y ^ a) P) (hQ : CostP D H (Y ^ a) Q) :
    CostP D H (Y ^ (a + 1)) fun x => P x ∨ Q x :=
  (hP.or hY.one_lt hQ).mono (by have := hY.pow_succ_bounds a; omega)

theorem not (hP : CostP D H (Y ^ a) P) : CostP D H (Y ^ (a + 1)) fun x => ¬ P x :=
  (hP.not hY.one_lt).mono (by have := hY.pow_succ_bounds a; omega)

theorem exists_mem {κ : Type*} (s : Finset κ) {P : κ → Inp → Prop} (hs : s.card ≤ Y)
    (hP : ∀ i ∈ s, CostP D H (Y ^ a) (P i)) : CostP D H (Y ^ (a + 2)) fun x => ∃ i ∈ s, P i x :=
  (CostP.exists_mem hY.one_lt s hP).mono (hY.le_pow_add_two hs a)

theorem forall_mem {κ : Type*} (s : Finset κ) {P : κ → Inp → Prop} (hs : s.card ≤ Y)
    (hP : ∀ i ∈ s, CostP D H (Y ^ a) (P i)) : CostP D H (Y ^ (a + 2)) fun x => ∀ i ∈ s, P i x :=
  (CostP.forall_mem hY.one_lt s hP).mono (hY.le_pow_add_two hs a)

theorem exists_univ {κ : Type*} [Fintype κ] {P : κ → Inp → Prop} (hs : Fintype.card κ ≤ Y)
    (hP : ∀ i, CostP D H (Y ^ a) (P i)) : CostP D H (Y ^ (a + 2)) fun x => ∃ i, P i x :=
  (hY.exists_mem univ hs fun i _ => hP i).congr fun x => by simp

theorem forall_univ {κ : Type*} [Fintype κ] {P : κ → Inp → Prop} (hs : Fintype.card κ ≤ Y)
    (hP : ∀ i, CostP D H (Y ^ a) (P i)) : CostP D H (Y ^ (a + 2)) fun x => ∀ i, P i x :=
  (hY.forall_mem univ hs fun i _ => hP i).congr fun x => by simp

/-- Counting: the number of elements of a set of at most `Y` elements with a property. -/
theorem card_filter {κ : Type*} (s : Finset κ) {P : κ → Inp → Prop} [∀ i x, Decidable (P i x)]
    (hs : s.card ≤ Y) (hP : ∀ i ∈ s, CostP D H (Y ^ a) (P i)) :
    Cost D H (Y ^ (a + 2)) fun x => (s.filter fun i => P i x).card := by
  have e x : (s.filter fun i => P i x).card = ∑ i ∈ s, {x | P i x}.indicator 1 x := by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    exact Finset.card_filter _ _
  refine (hY.sum s hs (fun i hi => costP_iff.1 (hP i hi)) fun x => hY.lt_of_le ?_).congr
    fun x => (e x).symm
  exact (e x ▸ card_filter_le s _).trans hs

/-! ### Stages -/

/-- **One stage.** A family of at most `Y ^ e` functions, each computed in `Y ^ a` steps from the
functions of `H` with `a + e ≤ k`, is computed by `Y ^ k` more gates. -/
theorem stage {n : ℕ} {inp : Fin n → Inp → Fin D} {p c k : ℕ} (h : SlpN inp (p + c * Y ^ k) H)
    {κ : Type*} [Fintype κ] (f : κ → Inp → ℕ) {e : ℕ} (hκ : Fintype.card κ ≤ Y ^ e)
    (hf : ∀ i, Cost D H (Y ^ a) (f i)) (hae : a + e ≤ k) :
    ∃ H', SlpN inp (p + (c + 1) * Y ^ k) H' ∧ H ⊆ H' ∧ ∀ i, f i ∈ H' := by
  refine ⟨_, (h.stage hY.zero_lt f _ hf).le hY.zero_lt ?_, Set.subset_union_left,
    fun i => Or.inr ⟨i, rfl⟩⟩
  have : Fintype.card κ * Y ^ a ≤ Y ^ k := (Nat.mul_le_mul_right _ hκ).trans <| by
    rw [← pow_add, add_comm]
    exact Nat.pow_le_pow_right hY.pos hae
  rw [add_one_mul]
  omega

end StepBase

end Cslib.Circuits
