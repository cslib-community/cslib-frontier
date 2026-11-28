/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.NetworkPolynomial
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.WireExponent

/-!
# The tensor of the network polynomial, and its hubs

The coefficients of the polynomial `f_{k,ℓ}` of the complete network form a tensor on the ends of
the wires of [AnthropicVPVNP2026] (p. 33): the end `⟨e, false⟩` of the wire `e` is at its node
`e.low`, the end `⟨e, true⟩` at `e.high` (`Flat.Pair.node`), and every end holds the string of `ℓ`
bits that the node at it sees on the wire. This tensor `T_{k,ℓ}` (`Flat.networkTensor`) is the
product of one wire of dimension `2^ℓ` for every wire of the network: its entry is the
coefficient of `f_{k,ℓ}` at the monomial of the views (`Flat.networkTensor_entry`), and a spectral
point `F` at `T_{k,ℓ}`, with the ends given to parties by `π`, is
`2 ^ (ℓ ∑_e d_F(π ⟨e, false⟩, π ⟨e, true⟩))` (`Flat.apply_push_networkTensor`).

In the proof of Proposition E.5 (pp. 33–34) Lemma A.3 (p. 19) routes `T_{k,ℓ}` through two hubs
`o₁, o₂` for a balanced set `S` of nodes: a wire of dimension `2^ℓ` joins every end at a node of
`S` to `o₁` and every other end to `o₂`, and a wire of dimension `L` joins the hubs
(`Flat.hubTensor`). A spectral point at this tensor is `2` to the power `ℓ` times the sum of the
wire exponents from the ends to their hubs, plus `lg L` times the wire exponent between the hubs
(`Flat.apply_hubTensor`).

## Main definitions

* `Flat.Pair.node`: the node at an end of a wire.
* `Flat.networkTensor`: the tensor `T_{k,ℓ}` on the ends of the wires.
* `Flat.hubTensor`: the tensor of Lemma A.3 with two hubs for a set of nodes.

## Main results

* `Flat.networkTensor_entry`: the entries are the coefficients of the network polynomial.
* `Flat.apply_push_networkTensor`, `Flat.apply_hubTensor`: spectral points at these tensors.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Section E.2 (p. 33) and the proof of Proposition E.5 (pp. 33–34); module `Paper.Flat`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Flat

open Finset MvPolynomial Cslib.PartyTensor

variable {k ℓ : ℕ}

/-- The node at an end of a wire: `e.low` at the end `false`, `e.high` at the end `true`. -/
@[expose] def Pair.node (e : Pair k) (d : Bool) : Fin k := bif d then e.high else e.low

/-- **The tensor `T_{k,ℓ}`** of the network polynomial on the ends of the wires (p. 33): the unit
tensor of size `2^ℓ` on the two ends of every wire. -/
@[expose] def networkTensor (K : Type) [CommSemiring K] (k ℓ : ℕ) :
    PartyTensor K (Σ _ : Pair k, Bool) :=
  outer fun _ => unit K Bool (2 ^ ℓ)

/-- The entries of `T_{k,ℓ}` are the coefficients of the network polynomial: with the index at
every end read as a string of `ℓ` bits, the entry is the coefficient of the monomial of what the
nodes see. -/
theorem networkTensor_entry {K : Type} [CommSemiring K] (z : (Σ _ : Pair k, Bool) → Fin (2 ^ ℓ)) :
    (networkTensor K k ℓ).entry z = (networkPolynomial K k ℓ).coeff (blockMonomial Prod.fst univ
      (BlockChoice.ofProd univ (assemble fun e d => (BitString.equivFin ℓ).symm (z ⟨e, d⟩)))) := by
  rw [coeff_networkPolynomial]
  change ∏ e, (unit K Bool (2 ^ ℓ)).entry (fun d => z ⟨e, d⟩) = _
  simp only [unit_entry, Bool.forall_bool, and_true, true_and, Equiv.apply_eq_iff_eq]
  rw [prod_ite_zero]
  simp only [mem_univ, true_imp_iff, prod_const_one]
  exact if_congr ⟨fun h e => (h e).1, fun h e => ⟨h e, (h e).symm⟩⟩ rfl rfl

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (F : SpectralPoint K I)

/-- A spectral point at `T_{k,ℓ}` with the ends at the parties `π`. -/
theorem apply_push_networkTensor (π : (Σ _ : Pair k, Bool) → I) :
    F (push π (networkTensor K k ℓ)) =
      2 ^ (ℓ * ∑ e, F.wireExponent (π ⟨e, false⟩) (π ⟨e, true⟩)) := by
  rw [networkTensor, F.congr (antisymmRel_push_outer π _), F.map_prod, mul_sum,
    Real.rpow_sum_of_pos two_pos]
  refine prod_congr rfl fun e _ => ?_
  have h : Set.range (fun d => π ⟨e, d⟩) = Set.range ![π ⟨e, false⟩, π ⟨e, true⟩] := by
    ext x
    simp [or_comm]
  rw [F.congr (antisymmRel_push_unit_congr _ _ h _)]
  change F (wire K _ _ _) = _
  rw [F.apply_wire _ _ Nat.one_le_two_pow, Real.rpow_mul two_pos.le]
  norm_cast

/-- **The tensor of Lemma A.3 for a set `S` of nodes** (proof of Proposition E.5, p. 34): a wire
of dimension `2^ℓ` from every end, at the party `π` of the end, to the hub `o₁` if its node is in
`S` and to `o₂` otherwise, and a wire of dimension `L` between the hubs. -/
@[expose] def hubTensor (K : Type) [CommSemiring K] (ℓ L : ℕ) (π : (Σ _ : Pair k, Bool) → I)
    (S : Finset (Fin k)) (o₁ o₂ : I) : PartyTensor K I :=
  prod (fun a : Σ _ : Pair k, Bool => wire K (2 ^ ℓ) (π a) (if a.1.node a.2 ∈ S then o₁ else o₂)) *
    wire K L o₁ o₂

/-- A spectral point at the tensor of Lemma A.3 with a wire of dimension `L ≥ 1` between the
hubs. -/
theorem apply_hubTensor {L : ℕ} (hL : 1 ≤ L) (π : (Σ _ : Pair k, Bool) → I) (S : Finset (Fin k))
    (o₁ o₂ : I) :
    F (hubTensor K ℓ L π S o₁ o₂) = 2 ^ (ℓ * ∑ a, F.wireExponent (π a)
      (if a.1.node a.2 ∈ S then o₁ else o₂) + F.wireExponent o₁ o₂ * Real.logb 2 L) := by
  rw [hubTensor, F.map_mul, F.map_prod, F.apply_wire _ _ hL, Real.rpow_add two_pos, mul_sum,
    Real.rpow_sum_of_pos two_pos, mul_comm (F.wireExponent o₁ o₂), Real.rpow_mul two_pos.le,
    Real.rpow_logb two_pos (by norm_num) (by exact_mod_cast hL)]
  refine congrArg (· * _) (prod_congr rfl fun a _ => ?_)
  rw [F.apply_wire _ _ Nat.one_le_two_pow, Real.rpow_mul two_pos.le]
  norm_cast

end Cslib.Circuits.Arithmetic.Separation.Flat
