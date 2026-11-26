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

open Cslib Cslib.Logic.PL Cslib.Logic.PL.VeriPB

/-- The variable of pigeon `i` and hole `j` is `i n + j`. -/
def name (n : ℕ) (p : Fin (n + 1) × Fin n) : ℕ := (finProdFinEquiv p : ℕ)

theorem name_injective (n : ℕ) : (name n).Injective :=
  Fin.val_injective.comp finProdFinEquiv.injective

-- Cubic-size VeriPB proofs of `PHP^{n+1}_n`.
example (n : ℕ) :
    ∃ P : Proof, check (((CNF.pigeonhole (n + 1) n).relabel (name n)).map Clause.toPB) P = true ∧
      P.steps.length ≤ (n + 1) * (n + 2) ^ 2 :=
  let ⟨P, hP, hlen, _⟩ := exists_check_pigeonhole n.lt_succ_self (name_injective n)
  ⟨P, hP, hlen⟩

-- No polynomially bounded translation of these proofs into LRAT certificates.
example :
    ¬ ∃ g : ℕ → ℕ, PolynomiallyBounded g ∧ ∀ (n s : ℕ) (P : Proof),
      check (((CNF.pigeonhole (n + 1) n).relabel (name n)).map Clause.toPB) P = true →
      P.steps.all Step.IsCP → P.steps.length ≤ s →
      ∃ cert, ((CNF.pigeonhole (n + 1) n).relabel (name n)).checkLRAT cert = true ∧
        min (CNF.lratHintCount cert.toList) cert.size ≤ g s :=
  not_exists_polynomiallyBounded_checkLRAT_pigeonhole name_injective

-- VeriPB polynomially simulates LRAT and is exponentially more succinct on these formulas.
example :
    ¬ ∃ g : ℕ → ℕ, PolynomiallyBounded g ∧ ∀ (n s : ℕ) (P : Proof),
      check (((CNF.pigeonhole (n + 1) n).relabel (name n)).map Clause.toPB) P = true →
      P.steps.all Step.IsCP → P.steps.length + hintCount P.steps ≤ s →
      ∃ cert, ((CNF.pigeonhole (n + 1) n).relabel (name n)).checkLRAT cert = true ∧
        cert.size + CNF.lratHintCount cert.toList ≤ g s :=
  (check_toVeriPB_and_not_exists_polynomiallyBounded name_injective).2.2

end CslibFrontierTests.Logics.Propositional.VeriPBPigeonholeSeparation

end
