/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Logics.Propositional.PseudoBoolean.PigeonholeSeparation

/-! The separation of VeriPB from LRAT on the pigeonhole formulas, with the variables of
`PHP^{n+1}_n` numbered by `finProdFinEquiv`. -/

@[expose] public section

namespace CslibFrontierTests.Logics.Propositional.VeriPBPigeonholeSeparation

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB

/-- The variable of pigeon `i` and hole `j` is `i n + j`. -/
def name (n : ℕ) (p : Fin (n + 1) × Fin n) : ℕ := (finProdFinEquiv p : ℕ)

theorem name_injective (n : ℕ) : (name n).Injective :=
  Fin.val_injective.comp finProdFinEquiv.injective

-- Cubic-size VeriPB proofs of `PHP^{n+1}_n`, and exponential lower bounds for LRAT.
example (n : ℕ) :
    (∃ P : Proof, check (((CNF.pigeonhole (n + 1) n).relabel (name n)).map Clause.toPB) P = true ∧
      P.steps.length ≤ (n + 1) * (n + 2) ^ 2) ∧
    ∀ cert, ((CNF.pigeonhole (n + 1) n).relabel (name n)).checkLRAT cert = true →
      2 ^ (n / 24) ≤ (n + 1) + n * (n + 1) ^ 2 +
        min (CNF.lratHintCount cert.toList) (cert.size * ((n + 1) * n)) :=
  let ⟨⟨P, hP, hlen, _⟩, hlrat⟩ := pigeonhole_separation n (name_injective n)
  ⟨⟨P, hP, hlen⟩, hlrat⟩

end CslibFrontierTests.Logics.Propositional.VeriPBPigeonholeSeparation

end
