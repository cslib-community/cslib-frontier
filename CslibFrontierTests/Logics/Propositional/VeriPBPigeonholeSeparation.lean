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

-- Counting steps and hints, these proofs still have cubic size.
example (n : ℕ) :
    ∃ P : Proof, check (((CNF.pigeonhole (n + 1) n).relabel (name n)).map Clause.toPB) P = true ∧
      P.steps.length + hintCount P.steps ≤ (n + 1) * (n + 2) ^ 2 :=
  let ⟨P, hP, hlen, hcp, _⟩ := exists_check_pigeonhole n.lt_succ_self (name_injective n)
  ⟨P, hP, by rw [hintCount_eq_zero_of_all_isCP hcp]; exact hlen⟩

-- Every accepted LRAT certificate for these formulas gives an accepted VeriPB proof whose size,
-- in steps and hints, is polynomially bounded in that of the certificate.
example : ∃ g : ℕ → ℕ, PolynomiallyBounded g ∧
    ∀ (n : ℕ) (cert : Array Std.Tactic.BVDecide.LRAT.IntAction),
    ((CNF.pigeonhole (n + 1) n).relabel (name n)).checkLRAT cert = true →
    ∃ P : Proof, check (((CNF.pigeonhole (n + 1) n).relabel (name n)).map Clause.toPB) P = true ∧
      P.steps.length + hintCount P.steps ≤ g (cert.size + CNF.lratHintCount cert.toList) :=
  let ⟨g, hg, h⟩ := exists_polynomiallyBounded_check_of_checkLRAT
  ⟨g, hg, fun _ cert hc => h _ _ cert hc le_rfl⟩

-- For every polynomially bounded `g`, some CNF has an accepted VeriPB proof of size `s` and no
-- accepted LRAT certificate of size at most `g s`.
example {g : ℕ → ℕ} (hg : PolynomiallyBounded g) :
    ∃ (φ : CNF ℕ) (s : ℕ) (P : Proof), check (φ.map Clause.toPB) P = true ∧
      P.steps.length + hintCount P.steps ≤ s ∧
      ∀ cert, φ.checkLRAT cert = true → g s < cert.size + CNF.lratHintCount cert.toList := by
  by_contra h
  push Not at h
  exact not_exists_polynomiallyBounded_checkLRAT_of_check ⟨g, hg, h⟩

end CslibFrontierTests.Logics.Propositional.VeriPBPigeonholeSeparation

end
