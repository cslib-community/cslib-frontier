/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.Pairs
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.MvPolynomial.SetMultilinearProd
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# The polynomial of the complete network

In the complete network on `k` nodes of [AnthropicVPVNP2026] (Appendix E; module `Nc.CaseI.Fkl`)
every wire carries a string of `ℓ` bits, and a node sees the strings of its `k - 1` wires. The
polynomial `Flat.networkPolynomial` has one variable for every node and every family of strings
that the node may see; it is the sum, over the strings on all wires, of the product of the
variables of what the nodes see.

Writing a string at each of the two ends of every wire, `Flat.assemble` gives what the nodes see.
The coefficient of the polynomial at the monomial of the nodes' views is `1` if the two ends of
every wire have the same string, and `0` otherwise (`Flat.coeff_networkPolynomial`): as a tensor on
the ends of the wires, the polynomial is the product of the identity tensors of the wires.

## Main definitions

* `Flat.assemble`: what the nodes see, from the strings at the ends of the wires.
* `Flat.networkPolynomial`: the polynomial `f_{k,ℓ}` of the complete network.

## Main results

* `Flat.assemble_injective`, `Flat.assemble_congr`: the views determine the strings at the ends,
  and the view of a node depends only on the ends at this node.
* `Flat.coeff_networkPolynomial`: the coefficients of the polynomial of the complete network.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix E; module `Nc.CaseI.Fkl`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Flat

open Finset MvPolynomial

variable {k ℓ : ℕ}

/-- What the nodes see when every wire has a string at each of its two ends (`false` for the
smaller node, `true` for the larger one): the node `a` sees, for the node `b`, the string at its
end of the wire between them, and the zero string for itself. -/
@[expose] def assemble (x : Pair k → Bool → BitString ℓ) (a b : Fin k) : BitString ℓ :=
  if h : a < b then x ⟨a, b, h⟩ false else if h : b < a then x ⟨b, a, h⟩ true else fun _ => false

theorem assemble_low (x : Pair k → Bool → BitString ℓ) (e : Pair k) :
    assemble x e.low e.high = x e false :=
  dite_eq_left e.low_lt_high

theorem assemble_high (x : Pair k → Bool → BitString ℓ) (e : Pair k) :
    assemble x e.high e.low = x e true :=
  (dite_eq_right e.low_lt_high.asymm).trans (dite_eq_left e.low_lt_high)

theorem assemble_self (x : Pair k → Bool → BitString ℓ) (a : Fin k) :
    assemble x a a = fun _ => false :=
  (dite_eq_right (lt_irrefl a)).trans (dite_eq_right (lt_irrefl a))

/-- The views of the nodes determine the strings at the ends of the wires. -/
theorem assemble_injective :
    Function.Injective (assemble : (Pair k → Bool → BitString ℓ) → Fin k → Fin k → BitString ℓ) :=
  fun x y h => funext fun e => funext fun d => by
    cases d
    · rw [← assemble_low x, ← assemble_low y, h]
    · rw [← assemble_high x, ← assemble_high y, h]

/-- The view of a node depends only on the strings at the ends at this node. -/
theorem assemble_congr {x y : Pair k → Bool → BitString ℓ} {a : Fin k}
    (hlow : ∀ e : Pair k, e.low = a → x e false = y e false)
    (hhigh : ∀ e : Pair k, e.high = a → x e true = y e true) : assemble x a = assemble y a := by
  funext b
  unfold assemble
  split_ifs with h1 h2
  · exact hlow ⟨a, b, h1⟩ rfl
  · exact hhigh ⟨b, a, h2⟩ rfl
  · rfl

/-- **The polynomial of the complete network** on `k` nodes with strings of `ℓ` bits: the sum,
over the strings on all wires, of the product of the variables of what the nodes see. -/
@[expose] noncomputable def networkPolynomial (F : Type*) [CommSemiring F] (k ℓ : ℕ) :
    MvPolynomial (Fin k × (Fin k → BitString ℓ)) F :=
  ∑ s : Pair k → BitString ℓ, ∏ a, X (a, assemble (fun e _ => s e) a)

variable {F : Type*} [CommSemiring F]

/-- **The coefficients of the polynomial of the complete network.** At the monomial of the views
that come from strings at the ends of the wires, the coefficient is `1` if the two ends of every
wire have the same string, and `0` otherwise. -/
theorem coeff_networkPolynomial (x : Pair k → Bool → BitString ℓ) :
    (networkPolynomial F k ℓ).coeff
        (blockMonomial Prod.fst univ (BlockChoice.ofProd univ (assemble x))) =
      if ∀ e, x e false = x e true then 1 else 0 := by
  classical
  have key (s : Pair k → BitString ℓ) :
      blockMonomial Prod.fst univ (BlockChoice.ofProd univ (assemble fun e _ => s e)) =
          blockMonomial Prod.fst univ (BlockChoice.ofProd univ (assemble x)) ↔
        s = (fun e => x e false) ∧ ∀ e, x e false = x e true := by
    rw [(blockMonomial_injective _ _).eq_iff, BlockChoice.ofProd_injective.eq_iff,
      assemble_injective.eq_iff]
    refine ⟨fun h => ⟨funext fun e => congrFun (congrFun h e) false, fun e => ?_⟩, ?_⟩
    · rw [← h]
    · rintro ⟨rfl, h⟩
      exact funext fun e => funext fun d => by cases d <;> simp only [h e]
  simp only [networkPolynomial, coeff_sum, prod_X_eq_monomial_blockMonomial_ofProd,
    coeff_monomial, key, ite_and]
  rw [sum_ite_eq' univ (fun e => x e false), ite_eq_left (mem_univ _)]

end Cslib.Circuits.Arithmetic.Separation.Flat
