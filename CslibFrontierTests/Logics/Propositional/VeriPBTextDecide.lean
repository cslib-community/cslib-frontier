/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

import CslibFrontierTests.Logics.Propositional.VeriPBAuxFixtures
import CslibFrontierTests.Logics.Propositional.VeriPBDomFixtures
import CslibFrontierTests.Logics.Propositional.VeriPBOutputFixtures
-- `import all`: the kernel evaluates the parsers and checkers of `Text` and the step `stepTop` of
-- `Redundance`, whose bodies are not exposed, to decide the acceptance of the fixtures.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Text

/-! Decided text clients of the VeriPB output and conclusion theorems: the acceptance of the
`decision_output` and `optimization_output_opposing_lits_objective` fixtures of the VeriPB
repository, of the PHP(3, 2) proof with symmetry breaking by `dom`, and of the optimality proof
by `dom` under the order `notAux` with an auxiliary variable, is checked by `decide +kernel`, and
the soundness theorems are applied to it. -/

set_option linter.privateModule false

namespace CslibFrontierTests.Logics.Propositional.VeriPBText

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Text

/-- The `decision_output` proof is accepted with an `EQUISATISFIABLE` output and no bound. -/
theorem amo3_accepted : ∃ o : Output, checkOPBOutput amo3 amo3Proof amo3Out =
    some (.noClaim, some o) ∧ o.guarantee = .equisatisfiable ∧ o.bound = none := by
  have h : (checkOPBOutput amo3 amo3Proof amo3Out).map
      (fun r => (r.1, r.2.map fun o => (o.guarantee, o.bound))) =
      some (.noClaim, some (.equisatisfiable, none)) := by
    decide +kernel
  rcases hc : checkOPBOutput amo3 amo3Proof amo3Out with _ | ⟨c, _ | o⟩ <;>
    simp only [hc, Option.map_some, Option.map_none, reduceCtorEq, Option.some.injEq,
      Prod.mk.injEq, and_false] at h
  obtain ⟨rfl, hg, hb⟩ := h
  exact ⟨o, rfl, hg, hb⟩

-- So `amo3` is satisfiable exactly when the output formula, read from `amo3Out` with names that
-- separate it from `amo3`, is.
example : ∃ I O, parseOPB amo3 = some I ∧ (I.Satisfiable ↔ O.Satisfiable) ∧
    ∃ N, N.Separates I amo3Out ∧ parseOPB amo3Out N = some O := by
  obtain ⟨o, h, hg, -⟩ := amo3_accepted
  obtain ⟨I, hI, hsem, -, hN⟩ := semOutput_of_checkOPBOutput h
  rw [hg] at hsem
  exact ⟨I, o.formula, hI, hsem, hN amo3Out rfl⟩

/-- The optimization proof, with its output formula as a file, is accepted with
`BOUNDS 2 : 14 2`. -/
theorem amo3Opt_accepted : (checkOPBOutput amo3Opt amo3OptProof amo3OptOut).map (·.1) =
    some (.bounds (some 2) 14 (some 2) none) := by
  decide +kernel

-- So the optimum of `amo3Opt` is `2`.
example : ∃ I f, parseOPB amo3Opt = some I ∧ I.objective = some f ∧
    (∀ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) → 2 ≤ f.eval σ) ∧
    ∃ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) ∧ f.eval σ ≤ 2 := by
  obtain ⟨I, f, hI, hf, hlb, hub⟩ := bounds_of_checkOPB amo3Opt_accepted
  refine ⟨I, f, hI, hf, fun σ hσ => ?_, hub 2 rfl⟩
  obtain ⟨l, hl, hle⟩ := hlb σ hσ
  cases hl
  exact hle

/-- The PHP(3, 2) proof with symmetry breaking by `dom` under the order `lex4` is accepted with
`UNSAT : 16`. -/
theorem domPhp32_accepted : (checkOPBOutput php32 domPhp32).map (·.1) = some (.unsat 16) := by
  decide +kernel

-- So PHP(3, 2) has no solution.
example : ∃ I, parseOPB php32 = some I ∧ ∀ σ : ℕ → Bool, ¬ ∀ c ∈ I.constraints, c.Holds σ :=
  not_satisfiable_of_checkOPB domPhp32_accepted

/-- The optimality proof by `dom` under the order `notAux`, whose negated order is refuted in
`scope geq`, is accepted with `BOUNDS 1 : 9 1`. -/
theorem domAuxObj_accepted : (checkOPBOutput sym2Aux domAuxObjProof).map (·.1) =
    some (.bounds (some 1) 9 (some 1) none) := by
  decide +kernel

-- So the optimum of `x1 + x2` subject to `x1 + x2 >= 1` is `1`.
example : ∃ I f, parseOPB sym2Aux = some I ∧ I.objective = some f ∧
    (∀ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) → 1 ≤ f.eval σ) ∧
    ∃ σ : ℕ → Bool, (∀ c ∈ I.constraints, c.Holds σ) ∧ f.eval σ ≤ 1 := by
  obtain ⟨I, f, hI, hf, hlb, hub⟩ := bounds_of_checkOPB domAuxObj_accepted
  refine ⟨I, f, hI, hf, fun σ hσ => ?_, hub 1 rfl⟩
  obtain ⟨l, hl, hle⟩ := hlb σ hσ
  cases hl
  exact hle

end CslibFrontierTests.Logics.Propositional.VeriPBText
