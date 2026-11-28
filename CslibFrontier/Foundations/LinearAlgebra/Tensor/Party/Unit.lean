/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Network
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# Unit tensors and wires

Relations between unit tensors, whose legs may be held by any parties, several by one party, and
between wires: a smaller unit tensor is a restriction of a larger one, sizes multiply under the
product, several legs of a unit tensor at one party are as good as one, and a pushed unit tensor
depends only on the set of parties holding a leg. Wires can be read in both directions, parallel
wires multiply their dimensions, a wire at one party is a restriction of `1`, a wire is a
restriction of a path of two wires (`PartyTensor.wire_le_mul_wire`), and legs can be moved
along wires (`PartyTensor.push_le_mul_push`). An upper functional, in particular a spectral
point, is between `1` and `n` at a unit tensor of size `n ≥ 1`. The *wire exponent*
`log₂ F ⟨2⟩_pq` of a spectral point `F` is the `d_φ(p, q)` of Lemma A.2 of [AnthropicVPVNP2026].

## Main definitions

* `Cslib.PartyTensor.SpectralPoint.wireExponent`: the exponent of a wire.

## Main results

* `Cslib.PartyTensor.unit_le_unit`, `Cslib.PartyTensor.antisymmRel_unit_mul`,
  `Cslib.PartyTensor.antisymmRel_push_unit_congr`: unit tensors.
* `Cslib.PartyTensor.antisymmRel_wire_comm`, `Cslib.PartyTensor.antisymmRel_wire_mul`,
  `Cslib.PartyTensor.wire_self_le_one`, `Cslib.PartyTensor.wire_le_mul_wire`,
  `Cslib.PartyTensor.push_le_mul_push`: wires.
* `Cslib.PartyTensor.UpperFunctional.one_le_unit`, `Cslib.PartyTensor.UpperFunctional.unit_le`:
  upper-functional bounds at unit tensors, `1 ≤ P ⟨n⟩ ≤ n`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma A.2 of the paper and its proof; modules `Ov.Core.Unit` and `Ov.Core.Tensor` (`Spec.e`)
-/

public section

namespace Cslib.PartyTensor

open Finset

variable {K : Type} [CommSemiring K] {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
  [DecidableEq J]

/-! ### Unit tensors -/

omit [DecidableEq J] in
/-- The entry of a unit tensor at equal indices is `1`. -/
theorem unit_entry_of {r : ℕ} {x : J → Fin r} (h : ∀ i j, x i = x j) : (unit K J r).entry x = 1 :=
  ite_eq_left h

omit [DecidableEq J] in
/-- The other entries of a unit tensor are `0`. -/
theorem unit_entry_of_not {r : ℕ} {x : J → Fin r} (h : ¬ ∀ i j, x i = x j) :
    (unit K J r).entry x = 0 :=
  ite_eq_right h

omit [DecidableEq J] in
/-- Entries of unit tensors at index tuples that are constant together are equal. -/
theorem unit_entry_congr {L : Type} [Fintype L] {r r' : ℕ} {x : J → Fin r}
    {y : L → Fin r'} (h : (∀ i j, x i = x j) ↔ ∀ i j, y i = y j) :
    (unit K J r).entry x = (unit K L r').entry y := by
  by_cases hx : ∀ i j, x i = x j
  · rw [unit_entry_of hx, unit_entry_of (h.1 hx)]
  · rw [unit_entry_of_not hx, unit_entry_of_not fun hy => hx (h.2 hy)]

/-- A smaller unit tensor is a restriction of a larger one. -/
theorem unit_le_unit {m n : ℕ} (h : m ≤ n) : unit K J m ≤ unit K J n :=
  le_of_entry_eq (fun _ => Fin.castLE h) fun x =>
    unit_entry_congr (x := x) (y := fun p => Fin.castLE h (x p))
      ⟨fun hx i j => congr_arg _ (hx i j), fun hx i j => Fin.castLE_injective h (hx i j)⟩

/-- The product of the unit tensors of sizes `m` and `n` is the one of size `m * n`. -/
theorem antisymmRel_unit_mul (m n : ℕ) :
    AntisymmRel (· ≤ ·) (unit K J (m * n)) (unit K J m * unit K J n) :=
  AntisymmRel.symm <| antisymmRel_of_equiv (fun _ => finProdFinEquiv) fun x => by
    change J → Fin m × Fin n at x
    change (unit K J m).entry (fun p => (x p).1) * (unit K J n).entry (fun p => (x p).2) =
      (unit K J (m * n)).entry fun p => finProdFinEquiv (x p)
    rw [unit_entry, unit_entry, unit_entry, ite_zero_mul_ite_zero, mul_one]
    exact if_congr (by simp only [finProdFinEquiv.injective.eq_iff, Prod.ext_iff, forall_and])
      rfl rfl

/-- The unit tensor of size `1` is `1`. -/
theorem antisymmRel_unit_one : AntisymmRel (· ≤ ·) (unit K J 1) 1 :=
  antisymmRel_of_equiv (fun _ => show Fin 1 ≃ Unit from Equiv.ofUnique _ _) fun x => by
    exact unit_entry_of fun i j => Subsingleton.elim (α := Fin 1) _ _

/-- Several legs of a unit tensor at one party are as good as one leg. -/
theorem antisymmRel_push_unit {L : Type} [Fintype L] [DecidableEq L] (ρ : L → J)
    (hρ : ρ.Surjective) (n : ℕ) : AntisymmRel (· ≤ ·) (push ρ (unit K L n)) (unit K J n) := by
  classical
  constructor
  · let w : ∀ q, ({l : L // ρ l = q} → Fin n) → K := fun q a =>
      if ∀ l l', a l = a l' then 1 else 0
    refine le_of_map w (fun q a => a ⟨(hρ q).choose, (hρ q).choose_spec⟩) fun x => ?_
    change ∀ q, {l : L // ρ l = q} → Fin n at x
    change (unit K L n).entry (fun l => x (ρ l) ⟨l, rfl⟩) =
      (∏ q, w q (x q)) *
        (unit K J n).entry fun q => x q ⟨(hρ q).choose, (hρ q).choose_spec⟩
    have cast : ∀ l q (h' : ρ l = q), x (ρ l) ⟨l, rfl⟩ = x q ⟨l, h'⟩ := by rintro l _ rfl; rfl
    by_cases h : ∀ l l', x (ρ l) ⟨l, rfl⟩ = x (ρ l') ⟨l', rfl⟩
    · rw [unit_entry_of h, unit_entry_of, Finset.prod_eq_one, _root_.mul_one]
      · rintro q -
        refine ite_eq_left (show ∀ l l', x q l = x q l' from fun l l' => ?_)
        rw [← cast l.val q l.property, ← cast l'.val q l'.property]
        exact h _ _
      · intro q q'
        rw [← cast _ _ (hρ q).choose_spec, ← cast _ _ (hρ q').choose_spec]
        exact h _ _
    · rw [unit_entry_of_not h]
      by_cases h1 : ∀ q l l', x q l = x q l'
      · rw [unit_entry_of_not, mul_zero]
        intro h2
        refine h fun i j => ?_
        rw [h1 (ρ i) ⟨i, rfl⟩ ⟨_, (hρ (ρ i)).choose_spec⟩,
          h1 (ρ j) ⟨j, rfl⟩ ⟨_, (hρ (ρ j)).choose_spec⟩]
        exact h2 _ _
      · push Not at h1
        obtain ⟨q, l, l', hq⟩ := h1
        rw [Finset.prod_eq_zero (Finset.mem_univ q), zero_mul]
        exact ite_eq_right (show ¬ ∀ l l', x q l = x q l' from fun h => hq (h l l'))
  · refine le_of_entry_eq (fun q a _ => a) fun x => ?_
    refine unit_entry_congr (x := x) (y := fun l => x (ρ l)) ⟨fun h i j => h _ _, fun h i j => ?_⟩
    obtain ⟨i, rfl⟩ := hρ i
    obtain ⟨j, rfl⟩ := hρ j
    exact h i j

/-- A pushed unit tensor depends only on the set of parties that hold a leg. -/
theorem antisymmRel_push_unit_congr {L : Type} [Fintype L] [DecidableEq L] (π : J → I) (π' : L → I)
    (h : Set.range π = Set.range π') (n : ℕ) :
    AntisymmRel (· ≤ ·) (push π (unit K J n)) (push π' (unit K L n)) := by
  classical
  have key : ∀ {L : Type} [Fintype L] [DecidableEq L] (π' : L → I) (S : Finset I)
      (_ : Set.range π' = S),
      AntisymmRel (· ≤ ·) (push π' (unit K L n)) (push (fun q : S => (q : I)) (unit K S n)) := by
    intro L _ _ π' S hS
    let ρ : L → S := fun l => ⟨π' l, Finset.mem_coe.1 (hS ▸ Set.mem_range_self l)⟩
    have hρ : ρ.Surjective := fun ⟨q, hq⟩ => by
      obtain ⟨l, hl⟩ : q ∈ Set.range π' := hS ▸ Finset.mem_coe.2 hq
      exact ⟨l, Subtype.ext hl⟩
    exact ((antisymmRel_push_push (fun q : S => (q : I)) ρ (unit K L n)).symm.trans
      ((antisymmRel_push_unit ρ hρ n).image (monotone_push _)))
  exact (key π (Set.toFinset (Set.range π)) (by simp)).trans
    (key π' (Set.toFinset (Set.range π)) (by simp [h])).symm

/-- A tensor with all its legs at one party is a restriction of `1`. -/
theorem push_const_le_one (q : I) (t : PartyTensor K J) : push (fun _ => q) t ≤ 1 := by
  classical
  refine le_of_map (fun p a => if h : q = p then t.entry fun j => a ⟨j, h⟩ else 1)
    (fun _ _ => ()) fun x => ?_
  have key : ∀ f : ∀ p, ∀ j : {j : J // q = p}, t.Index j.val, t.entry (fun j => f q ⟨j, rfl⟩) =
      ∏ p, if h : q = p then t.entry fun j => f p ⟨j, h⟩ else 1 := fun f => by
    rw [Finset.prod_eq_single q (fun p _ hp => dite_eq_right fun h => hp h.symm) (by simp)]
    simp
  exact (key x).trans (_root_.mul_one _).symm

/-! ### Wires -/

/-- A wire may be read in both directions. -/
theorem antisymmRel_wire_comm (n : ℕ) (p q : I) :
    AntisymmRel (· ≤ ·) (wire K n p q) (wire K n q p) :=
  antisymmRel_push_unit_congr _ _ (by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons]
    simp [Set.pair_comm]) n

/-- A wire with both ends at one party is a restriction of `1`. -/
theorem wire_self_le_one (n : ℕ) (p : I) : wire K n p p ≤ 1 := by
  rw [wire, Matrix.vec_single_eq_const, Matrix.vecCons_const]
  exact push_const_le_one p _

/-- Two parallel wires are one wire, whose dimension is the product. -/
theorem antisymmRel_wire_mul (m n : ℕ) (p q : I) :
    AntisymmRel (· ≤ ·) (wire K (m * n) p q) (wire K m p q * wire K n p q) :=
  ((antisymmRel_unit_mul m n).image (monotone_push _)).trans (antisymmRel_push_mul _ _ _)

/-- A wire of dimension `1` is `1`. -/
theorem antisymmRel_wire_one (p q : I) : AntisymmRel (· ≤ ·) (wire K 1 p q) 1 :=
  (antisymmRel_unit_one.image (monotone_push _)).trans (antisymmRel_push_one _)

private def tr {n : ℕ} (v : Fin 3) (x l : Fin 2 → Fin n) : K :=
  if v = 0 then (if x 0 = l 0 then 1 else 0) else
    if v = 1 then (if l 0 = l 1 then 1 else 0) else (if x 1 = l 1 then 1 else 0)

private theorem tr_sum {n : ℕ} (x : Fin 2 → Fin n) :
    (unit K (Fin 2) n).entry x = ∑ l : Fin 2 → Fin n, ∏ v, tr (K := K) v x l := by
  rw [Finset.sum_eq_single (fun _ => x 0)]
  · rcases eq_or_ne (x 0) (x 1) with h | h
    · rw [unit_entry_of (by simp [Fin.forall_fin_two, h])]
      simp [tr, h]
    · rw [unit_entry_of_not (by simp [Fin.forall_fin_two, h])]
      simp [Fin.prod_univ_succ, tr, h.symm]
  · intro l _ hl
    by_cases h0 : x 0 = l 0
    · by_cases h1 : l 0 = l 1
      · exact absurd (funext fun i => by fin_cases i <;> simp [h0, h1]) hl
      · simp [Fin.prod_univ_succ, tr, h1]
    · simp [Fin.prod_univ_succ, tr, h0]
  · simp

/-- The wire from `p` to `q` is a restriction of the product of the wires from `p` to `r` and
from `r` to `q`. -/
theorem wire_le_mul_wire (n : ℕ) (p q r : I) :
    wire K n p q ≤ wire K n p r * wire K n r q := by
  classical
  have h := push_le_of_edges (V := Fin 3) (E := Fin 2) (J := Fin 2) (K := K) ![p, q] ![p, r, q]
    (unit K (Fin 2) n) (fun _ => Fin n) ![0, 1] ![1, 2] tr
    (by
      intro v x x' l l' hx hl
      change Fin 2 → Fin n at x x'
      fin_cases v
      · have h0 : x 0 = x' 0 := hx 0 rfl
        have h1 := hl 0 (Or.inl rfl)
        simp [tr, h0, h1]
      · have h0 := hl 0 (Or.inr rfl)
        have h1 := hl 1 (Or.inl rfl)
        simp [tr, h0, h1]
      · have h0 : x 1 = x' 1 := hx 1 rfl
        have h1 := hl 1 (Or.inr rfl)
        simp [tr, h0, h1]) tr_sum
  refine h.trans ((antisymmRel_prod_fin_two _).1.trans ?_)
  simp only [Fintype.card_fin]
  exact le_rfl

/-- Moving legs: the leg `j` can be moved from `π' j` to `π j` through a wire of its dimension. -/
theorem push_le_mul_push (π π' : J → I) (t : PartyTensor K J) :
    push π t ≤ prod (fun j => wire K (Fintype.card (t.Index j)) (π j) (π' j)) * push π' t := by
  classical
  have h := push_le_of_network (V := J ⊕ J) (E := J) (κ := Unit) (M := fun _ => J) π
    (Sum.elim π π') t t.Index Sum.inl Sum.inr (fun _ => t) (fun _ j => Sum.inr j)
    (fun v x l y => match v with
      | Sum.inl j => if x j = l j then 1 else 0
      | Sum.inr j => if l j = y () j then 1 else 0)
    (by
      intro v x x' l l' y y' hx hl hy
      rcases v with j | j
      · simp only [hx j rfl, hl j (Or.inl rfl)]
      · simp only [hl j (Or.inr rfl), hy () j rfl])
    (by
      intro x
      rw [Finset.sum_eq_single x]
      · rw [Finset.sum_eq_single (fun _ => x)]
        · simp
        · intro y _ hy
          obtain ⟨j, hj⟩ : ∃ j, ¬ x j = y () j :=
            not_forall.1 fun hcon => hy (funext fun _ => funext fun j => (hcon j).symm)
          rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inr j)) (ite_eq_right hj), zero_mul]
        · simp
      · intro l _ hl
        obtain ⟨j, hj⟩ : ∃ j, ¬ x j = l j :=
          not_forall.1 fun hcon => hl (funext fun j => (hcon j).symm)
        refine Finset.sum_eq_zero fun y _ => ?_
        rw [Finset.prod_eq_zero (Finset.mem_univ (Sum.inl j)) (ite_eq_right hj), zero_mul]
      · simp)
  exact h.trans (mul_le_mul' le_rfl (antisymmRel_prod_unique _).le)

namespace UpperFunctional

variable (P : UpperFunctional K I)

/-- An upper functional at a pushed unit tensor of size at least `1` is at least `1`. -/
theorem one_le_unit {K : Type} [Field K] (P : UpperFunctional K I) [Nonempty I] (π : J → I) {n : ℕ}
    (hn : 1 ≤ n) : 1 ≤ P (push π (unit K J n)) :=
  P.one_le (y := fun _ _ => ⟨0, hn⟩) <| by
    change (unit K J n).entry (fun _ => ⟨0, hn⟩) ≠ 0
    rw [unit_entry_of fun _ _ => rfl]
    exact one_ne_zero

/-- An upper functional at a unit tensor that has a leg is at most its size. -/
theorem unit_le [Nonempty J] (π : J → I) (n : ℕ) : P (push π (unit K J n)) ≤ n := by
  have h := (coveredBy_one_of_le_unit (le_refl (unit K J n))).push π
  simpa [P.congr (antisymmRel_push_one π), P.map_one] using P.le_sum _ _ h

end UpperFunctional

/-- The *wire exponent* of a spectral point between the parties `p` and `q`: `log₂` of its value
at the wire of dimension `2` (the `d_φ(p, q)` of Lemma A.2 of [AnthropicVPVNP2026]). -/
@[expose] noncomputable def SpectralPoint.wireExponent (F : SpectralPoint K I) (p q : I) : ℝ :=
  Real.logb 2 (F (wire K 2 p q))

end Cslib.PartyTensor
