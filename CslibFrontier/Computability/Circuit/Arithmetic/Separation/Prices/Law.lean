/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Price.Basic
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Classes
import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Covers of wires as identities between functions of bits

For the proof of Theorem G.2 (thm:laws) of *VP ≠ VNP over every field* [AnthropicVPVNP2026]. A cover
of a product of wires by products of wires is an identity between functions of bits
(`Separation.Prices.WireId`, `Separation.Prices.exists_wireId`). Powers and products of products of
wires are again products of wires (`Separation.Prices.antisymmRel_wires_pow`,
`Separation.Prices.antisymmRel_prod_wires_pow`), and a spectral point at wires of `n e` bits is
`2 ^ ∑ e, n e · d(e)` (`Separation.Prices.apply_wires_two_pow`).

## Main definitions

* `Separation.Prices.WireId`.

## Main results

* `Separation.Prices.exists_wireId`, `Separation.Prices.antisymmRel_wires_pow`,
  `Separation.Prices.antisymmRel_prod_wires_pow`, `Separation.Prices.apply_wires_two_pow`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem G.2 of the paper; module `Nc.Price.Law`
-/

@[expose] public section


namespace Cslib.Circuits.Arithmetic.Separation.Prices

open Cslib.PartyTensor Finset

/-- An identity that rewrites wires. Parties V; old wires e with ends a e, b e and n e bits; new
wires ν with ends c ν, d ν. For all copies X p (of the bits of the old wires at p, for every party
p): [for every old wire the two copies agree] = Σ_i Σ_(bits g of all new wires) ∏_p tab i p (X p) (g
at p); in the term i the new wire ν has len i ν bits. -/
def WireId (R : Type) [CommRing R] {V E N ι : Type} [Fintype V] [Fintype E] [Fintype N]
    [DecidableEq N] [Fintype ι] (a b : E → V) (c d : N → V) (n : E → ℕ) (len : ι → N → ℕ)
    (tab : ∀ (i : ι) (p : V), (∀ e : {e // a e = p ∨ b e = p}, Fin (n e) → Bool) →
      (∀ ν : {ν // c ν = p ∨ d ν = p}, Fin (len i ν) → Bool) → R) : Prop :=
  ∀ X : ∀ p, ∀ e : {e // a e = p ∨ b e = p}, Fin (n e) → Bool,
    (if ∀ e, X (a e) ⟨e, Or.inl rfl⟩ = X (b e) ⟨e, Or.inr rfl⟩ then (1 : R) else 0) =
      ∑ i, ∑ g : ∀ ν, Fin (len i ν) → Bool, ∏ p, tab i p (X p) (fun ν => g ν)

section Bits

open BitString (equivFin)

variable {K : Type} [Field K] {V : Type} [Fintype V] [DecidableEq V]

variable {E N : Type} [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N]

omit [Fintype V] [DecidableEq V] in
private theorem at_of_end {a b p : V} {j : Fin 2} (h : (![a, b] : Fin 2 → V) j = p) : a = p ∨ b =
    p := by
  fin_cases j
  · exact Or.inl h
  · exact Or.inr h

/-- A sum of restrictions of wires is an identity between functions of bits. -/
theorem exists_wireId {ι : Type} [Fintype ι] {a b : E → V} {c d : N → V} {n : E → ℕ}
    {len : ι → N → ℕ}
    (h : (wires K a b fun e => 2 ^ n e).CoveredBy fun i => wires K c d fun ν => 2 ^ len i ν) :
    ∃ tab, WireId K a b c d n len tab := by
  classical
  obtain ⟨L, hL⟩ := h
  refine ⟨fun i p x g => L i p (fun e j => equivFin _ (x ⟨e, at_of_end j.2⟩))
    (fun ν j => equivFin _ (g ⟨ν, at_of_end j.2⟩)), fun X => ?_⟩
  let x : ∀ p, (wires K a b fun e => 2 ^ n e).Index p := fun p e j =>
    equivFin _ (X p ⟨e, at_of_end j.2⟩)
  have h1 : (wires K a b fun e => 2 ^ n e).entry x =
      if ∀ e, X (a e) ⟨e, Or.inl rfl⟩ = X (b e) ⟨e, Or.inr rfl⟩ then (1 : K) else 0 := by
    have key : ∀ e, (wire K (2 ^ n e) (a e) (b e)).entry (fun p => x p e) =
        if X (a e) ⟨e, Or.inl rfl⟩ = X (b e) ⟨e, Or.inr rfl⟩ then 1 else 0 := by
      intro e
      exact (unit_two_entry fun j => equivFin (n e) (X (![a e, b e] j) ⟨e, at_of_end rfl⟩)).trans
        (if_congr (equivFin (n e)).injective.eq_iff rfl rfl)
    change ∏ e, (wire K (2 ^ n e) (a e) (b e)).entry (fun p => x p e) = _
    rw [Finset.prod_congr rfl fun e _ => key e, Finset.prod_ite_zero]
    simp
  rw [← h1, hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  let Φ : (∀ p, (wires K c d fun ν => 2 ^ len i ν).Index p) ≃ (∀ ν, Fin 2 → Fin (2 ^ len i ν)) :=
    ⟨fun y ν j => y (![c ν, d ν] j) ν ⟨j, rfl⟩, fun z p ν j => z ν j.1,
      fun y => by
        funext p ν j
        obtain ⟨j, rfl⟩ := j
        rfl,
      fun z => rfl⟩
  have h2 : localApply (L i) (wires K c d fun ν => 2 ^ len i ν).entry x =
      ∑ z : ∀ ν, Fin 2 → Fin (2 ^ len i ν),
      (∏ p, L i p (x p) (Φ.symm z p)) * ∏ ν, (unit K (Fin 2) (2 ^ len i ν)).entry (z ν) := by
    refine Fintype.sum_equiv Φ _ _ fun y => ?_
    rw [Φ.symm_apply_apply]
    rfl
  rw [h2, sum_mul_prod_unit (fun ν => 2 ^ len i ν) fun z => ∏ p, L i p (x p) (Φ.symm z p)]
  symm
  exact Fintype.sum_equiv (Equiv.piCongrRight fun ν => equivFin (len i ν)) _ _ fun g => rfl

/-- Wires with the ends p, q, as a homomorphism from numbers to classes of tensors. -/
private noncomputable def wcls (K : Type)
    [Field K] (p q : V) : ℕ →* Antisymmetrization (PartyTensor K V) (· ≤ ·) where
  toFun n := toAntisymmetrization (· ≤ ·) (wire K n p q)
  map_one' := (toAntisymmetrization_eq _ _ _).2 (antisymmRel_wire_one p q)
  map_mul' m n := by
    rw [← toAntisymmetrization_mul]
    exact (toAntisymmetrization_eq _ _ _).2 (antisymmRel_wire_mul m n p q)

private theorem toAntisymmetrization_wires (a b : E → V) (n : E → ℕ) :
    toAntisymmetrization (· ≤ ·) (wires K a b n) = ∏ e,
        wcls K (a e) (b e) (n e) := toAntisymmetrization_prod _

theorem antisymmRel_wires_pow (a b : E → V) (n : E → ℕ) (q : ℕ) :
    AntisymmRel (· ≤ ·) ((wires K a b fun e => 2 ^ n e) ^ q)
        (wires K a b fun e => 2 ^ (q * n e)) := by
  refine (toAntisymmetrization_eq _ _ _).1 ?_
  rw [toAntisymmetrization_pow, toAntisymmetrization_wires, toAntisymmetrization_wires,
      ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [← map_pow, ← pow_mul, mul_comm]

theorem antisymmRel_prod_wires_pow {B : Type} [Fintype B] [DecidableEq B] (c d : N → V)
    (ℬ : B → N → ℕ)
    (v : B → ℕ) :
    AntisymmRel (· ≤ ·) (prod fun β => (wires K c d fun ν => 2 ^ ℬ β ν) ^ v β)
      (wires K c d fun ν => 2 ^ ∑ β, v β * ℬ β ν) := by
  refine (toAntisymmetrization_eq _ _ _).1 ?_
  rw [toAntisymmetrization_prod, toAntisymmetrization_wires]
  simp only [toAntisymmetrization_pow, toAntisymmetrization_wires, ← Finset.prod_pow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun ν _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum, map_prod]
  refine Finset.prod_congr rfl fun β _ => ?_
  rw [← map_pow, ← pow_mul, mul_comm]

/-- The price of wires of n e bits. -/
theorem apply_wires_two_pow (F : SpectralPoint K V) (a b : E → V) (n : E → ℕ) :
    F (wires K a b fun e => 2 ^ n e) = 2 ^ ∑ e, (n e : ℝ) * F.wireExponent (a e) (b e) := by
  rw [SpectralPoint.apply_wires F a b fun e => Nat.one_le_two_pow,
      Real.rpow_sum_of_pos (by norm_num)]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [Real.rpow_mul (by norm_num)]
  norm_num

end Bits

end Cslib.Circuits.Arithmetic.Separation.Prices
