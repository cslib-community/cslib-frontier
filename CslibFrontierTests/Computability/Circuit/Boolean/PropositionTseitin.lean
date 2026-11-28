/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Circuit.Boolean.PropositionTseitin

/-!
# The gate list of a proposition

The implication `p → q` over two atoms compiles to a negation gate at wire `2` and a disjunction
gate at wire `3`, the output. The list is well formed, and its output agrees with the truth table
of the implication at all four valuations. At the valuation `p = true, q = false`, which falsifies
the implication, neither Tseitin transformation has a model with the inputs fixed there.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Circuit.Boolean.PropositionTseitin

open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Logic.PL Cslib.Logic.PL.Proposition

private abbrev pq : Proposition (Fin 2) := .imp (.atom 0) (.atom 1)

example : pq.deMorganCode 0 = ⟨[(.not, [0]), (.or, [2, 1])], 3⟩ := rfl

example : Program.IsCodeFrom signature 2 0 (pq.deMorganCode 0).gates := by decide

example : ∀ v : Fin 2 → Bool,
    evalOutput (List.ofFn v) (pq.deMorganCode 0).gates (pq.deMorganCode 0).output =
      (!v 0 || v 1) := by
  decide

-- The valuation `p = true, q = false` falsifies `p → q`; the circuit formula with the inputs fixed
-- there is unsatisfiable, so no model of `pq.tseitinCNF` restricts to it.
example : ¬ ∃ σ, pq.tseitinCNF.eval σ = true ∧ σ ∘ Sum.inl = ![true, false] := by
  rw [exists_eval_tseitinCNF_iff_satisfiable_tseitinSatCNF, satisfiable_tseitinSatCNF_iff
    (isCodeFrom_deMorganCode pq 0) (by simp) (by decide)]
  rintro ⟨y, hy, hpre, hout⟩
  obtain rfl := hpre.eq_of_length (by simp [hy])
  revert hout
  decide

end CslibFrontierTests.Computability.Circuit.Boolean.PropositionTseitin
