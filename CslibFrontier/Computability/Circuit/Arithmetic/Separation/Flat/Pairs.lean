/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The wires of the complete network

The complete network on `k` nodes of [AnthropicVPVNP2026] (Appendix E; modules `Nc.CaseI.Fkl` and
`Nc.CaseI.Lower`) has one wire for every pair of nodes `low < high` (`Flat.Pair`). A sum over the
wires of a term for each of the two ends is a sum over the ordered pairs of distinct nodes
(`Flat.sum_pair_add_swap`), and there are `k (k - 1) / 2` wires (`Flat.sum_pair_one`).

## Main definitions

* `Flat.Pair`: a wire, a pair of nodes `low < high`.
* `Flat.pairEquiv`: wires as pairs of nodes in increasing order.

## Main results

* `Flat.sum_pair_add_swap`: sums over wires and over ordered pairs of distinct nodes.
* `Flat.sum_pair_one`: the number of wires.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix E; modules `Nc.CaseI.Fkl` and `Nc.CaseI.Lower`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Flat

open Finset

variable {k : ℕ}

/-- A wire of the complete network on `k` nodes: a pair of nodes `low < high`. -/
@[ext]
structure Pair (k : ℕ) where
  /-- The smaller node of a wire. -/
  low : Fin k
  /-- The larger node of a wire. -/
  high : Fin k
  /-- The smaller node precedes the larger node. -/
  low_lt_high : low < high
  deriving DecidableEq

/-- Wires as pairs of nodes in increasing order. -/
@[expose] def pairEquiv (k : ℕ) : Pair k ≃ {e : Fin k × Fin k // e.1 < e.2} where
  toFun e := ⟨(e.low, e.high), e.low_lt_high⟩
  invFun := fun ⟨(a, b), h⟩ => ⟨a, b, h⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypePair : Fintype (Pair k) := Fintype.ofEquiv _ (pairEquiv k).symm

/-- A sum over the wires of a term for each end is the sum over the ordered pairs of distinct
nodes. -/
theorem sum_pair_add_swap {M : Type*} [AddCommMonoid M] (G : Fin k → Fin k → M) :
    ∑ e : Pair k, (G e.low e.high + G e.high e.low) = ∑ a, ∑ b, if a = b then 0 else G a b := by
  rw [← (pairEquiv k).symm.sum_comp]
  change ∑ e : {e : Fin k × Fin k // e.1 < e.2}, (G e.val.1 e.val.2 + G e.val.2 e.val.1) = _
  rw [← Fintype.sum_prod_type' (f := fun a b => if a = b then (0 : M) else G a b),
    sum_add_distrib,
    ← sum_subtype (univ.filter fun e : Fin k × Fin k => e.1 < e.2) (by simp)
      (fun e : Fin k × Fin k => G e.1 e.2),
    ← sum_subtype (univ.filter fun e : Fin k × Fin k => e.1 < e.2) (by simp)
      (fun e : Fin k × Fin k => G e.2 e.1), sum_filter, sum_filter,
    Fintype.sum_equiv (Equiv.prodComm _ _) (fun e : Fin k × Fin k => if e.1 < e.2 then G e.2 e.1
      else 0) (fun e => if e.2 < e.1 then G e.1 e.2 else 0) fun e => rfl, ← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  rcases lt_trichotomy e.1 e.2 with h | h | h
  · simp [h, h.ne, not_lt.2 h.le]
  · simp [h]
  · simp [h, h.ne', not_lt.2 h.le]

/-- The complete network on `k` nodes has `k (k - 1) / 2` wires. -/
theorem sum_pair_one : ∑ _e : Pair k, (1 : ℝ) = k * (k - 1) / 2 := by
  have h := sum_pair_add_swap (k := k) fun _ _ => (1 / 2 : ℝ)
  have h2 (a : Fin k) : ∑ b : Fin k, (if a = b then (0 : ℝ) else 1 / 2) = (k - 1) / 2 := by
    have h3 (b : Fin k) :
        (if a = b then (0 : ℝ) else 1 / 2) = 1 / 2 - if a = b then 1 / 2 else 0 := by
      split_ifs <;> ring
    simp only [h3, sum_sub_distrib, sum_ite_eq, mem_univ, ite_true, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  simp only [h2, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h ⊢
  linarith

end Cslib.Circuits.Arithmetic.Separation.Flat
