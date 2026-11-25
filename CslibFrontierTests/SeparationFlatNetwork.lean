/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.LowerNumbers
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.NetworkPolynomial
import Mathlib.Algebra.Ring.Int.Defs

/-! Tests of the polynomial of the complete network, as a client that sees only the public
statements: what the two nodes of one wire see; the coefficient at equal and at different strings
at the two ends of the wire; the same strings at both ends of all wires on three nodes; and the
numbers of the lower bound on four nodes. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationFlatNetwork

open Finset MvPolynomial Cslib Cslib.Circuits.Arithmetic.Separation.Flat

/-- The wire of the complete network on two nodes. -/
def wire : Pair 2 := ⟨0, 1, by decide⟩

/-- The smaller node sees the string at its end of the wire, and the zero string for itself. -/
example (x : Pair 2 → Bool → BitString 1) :
    assemble x 0 1 = x wire false ∧ assemble x 1 0 = x wire true ∧
      assemble x 0 0 = fun _ => false :=
  ⟨assemble_low x wire, assemble_high x wire, assemble_self x 0⟩

/-- One wire with one bit: the coefficient is `1` when both ends have the bit `true`. -/
example :
    (networkPolynomial ℤ 2 1).coeff (blockMonomial Prod.fst univ
      (BlockChoice.ofProd univ (assemble fun _ _ _ => true))) = 1 := by
  rw [coeff_networkPolynomial, ite_eq_left fun _ => rfl]

/-- One wire with one bit: the coefficient is `0` when the ends have different bits. -/
example :
    (networkPolynomial ℤ 2 1).coeff (blockMonomial Prod.fst univ
      (BlockChoice.ofProd univ (assemble fun _ d _ => d))) = 0 := by
  rw [coeff_networkPolynomial, ite_eq_right]
  exact fun h => Bool.false_ne_true (congrFun (h wire) 0)

/-- Three nodes: strings that do not depend on the end give the coefficient `1`, over any
semiring. -/
example {F : Type} [CommSemiring F] (s : Pair 3 → BitString 2) :
    (networkPolynomial F 3 2).coeff (blockMonomial Prod.fst univ
      (BlockChoice.ofProd univ (assemble fun e _ => s e))) = 1 := by
  rw [coeff_networkPolynomial, ite_eq_left fun _ => rfl]

/-- On three nodes, ends of length one with an error `δ` each: the three wires cost `6 (1 + δ)`. -/
example (δ : ℝ) :
    ∑ _e : Pair 3, ((1 + δ) + (1 + δ)) =
      (∑ a : Fin 3, ∑ b : Fin 3, if a = b then 0 else 1) + 6 * δ := by
  rw [sum_pair_add_add_swap (fun _ _ => 1) δ]
  norm_num

/-- On four nodes, with `√4 = 2`: an inequality between the three sums forces `lg ≥ 4 ℓ / 3`. -/
example {ℓ c S1 S2 S3 lg : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 ≤ c) (hlg : 0 ≤ lg) (hℓc : 100 * c ≤ ℓ)
    (hw : 6 * (1 - 1 / 600) ≤ c * S1) (hh : c * S2 ≤ 6 - 4 / 12 + 2 * 6 * (1 / 600))
    (hm : c * S3 ≤ 1 / (3 * √4) + 1 / 600) (h1 : ℓ * S1 ≤ 4 + ℓ * S2 + S3 * lg) :
    ℓ * (4 * √4) / 6 ≤ lg :=
  lower_numbers (by norm_num) hℓ hc (by norm_num) (by norm_num) hlg hℓc hw hh hm h1

end CslibFrontierTests.SeparationFlatNetwork
