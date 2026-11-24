/-
Copyright (c) 2026 Clément Trecourt, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clément Trecourt, Samuel Schlesinger
-/

module
-- upstream: local-only (tests of Levin universal search for SAT)

import CslibFrontier.Computability.Complexity.Classes.NP.UniversalSearch

/-!
# Tests for Levin's universal search

Concrete witnesses exercising:
* a small satisfiable CNF formula solved at stage 1 (`SAT.levinStage` produces a verified
  assignment `[]`, whereas stage 0 returns `none`);
* a small satisfiable CNF formula whose satisfying assignment is non-trivial (`[(0, true)]`),
  showing nonvacuity (`SAT.levinStage` returns `none` at stages 0 and 1, while some later stage
  returns a verified assignment);
* an unsatisfiable CNF formula (`x₀ ∧ ¬x₀`), showing that `SAT.levinStage` returns `none` at every
  stage and that the native universal search machine diverges on it.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.UniversalSearch

open Cslib.Complexity Cslib.Logic.PL

/-- A satisfiable unit-clause formula `¬x₀`, satisfied by the default all-false assignment. -/
private def negUnit : CNF ℕ := [[(0, false)]]

/-- A satisfiable unit-clause formula `x₀`, not satisfied by the default all-false assignment. -/
private def posUnit : CNF ℕ := [[(0, true)]]

/-- An unsatisfiable CNF formula `x₀ ∧ ¬x₀`. -/
private def unsatFormula : CNF ℕ := [[(0, true)], [(0, false)]]

/-- Machine 0 decodes to the empty 0-tape description, which halts in 1 step with output `[]`. -/
private lemma sat_levinStage_one (φ : CNF ℕ) :
    SAT.levinStage φ 1 = if SAT.verifier (φ, []) then some [] else none := by
  have hw0 : Ladner.word 0 = [] := by simp [Ladner.word]
  have hdec : Turing.MultiTapeTM.Universal.decodeDesc
      (Turing.MultiTapeTM.unframe (Ladner.word 0)) = ⟨0, 0, []⟩ := by
    simp [hw0, Turing.MultiTapeTM.Universal.decodeDesc, Turing.MultiTapeTM.Universal.descDecoder,
      Turing.MultiTapeTM.Decoder.map, Turing.MultiTapeTM.Decoder.pair,
      Turing.MultiTapeTM.Decoder.unary, Turing.MultiTapeTM.Decoder.list,
      Turing.MultiTapeTM.unframe, Turing.MultiTapeTM.dropFrame]
  have hrun : Turing.MultiTapeTM.Universal.runWord ⟨0, 0, []⟩ (encCNF φ) 1 = some [] := rfl
  simp only [SAT.levinStage, Cslib.Complexity.levinStage, List.range_one, List.find?_cons,
    List.find?_nil, hdec, hrun, Option.elim_some]
  cases hv : SAT.verifier (φ, []) with
  | false => simp
  | true => simp [hdec, hrun, hv]

/-- Stage 0 runs no machines. -/
example : SAT.levinStage negUnit 0 = none := rfl

/-- Stage 1 finds the empty certificate for `¬x₀` (machine index 0 halts in 1 step with output
`[]`) and `SAT.verifier` accepts it. -/
example : SAT.levinStage negUnit 1 = some [] := by
  rw [sat_levinStage_one]
  decide

example : SAT.verifier (negUnit, []) = true := by decide

/-- Nonvacuity: `x₀` is satisfiable, yet stages 0 and 1 both return `none` because machine 0 emits
`[]` which does not satisfy `x₀`. -/
example : SAT.levinStage posUnit 0 = none := rfl

example : SAT.levinStage posUnit 1 = none := by
  rw [sat_levinStage_one]
  decide

example : posUnit ∈ SAT := ⟨fun _ => true, by decide⟩

example : ∃ K w, SAT.levinStage posUnit K = some w ∧ SAT.verifier (posUnit, w) = true := by
  have hsat : posUnit ∈ SAT := ⟨fun _ => true, by decide⟩
  obtain ⟨K, w, hw⟩ := SAT.exists_levinStage_eq_some_iff.mpr hsat
  exact ⟨K, w, hw, verifier_of_levinStage_eq_some hw⟩

/-- Unsatisfiability: `x₀ ∧ ¬x₀` is not in `SAT`, fails concrete early stages, and returns `none`
at every stage `K`. -/
private theorem unsatFormula_notMem_SAT : unsatFormula ∉ SAT := by
  rintro ⟨σ, hσ⟩
  simp only [unsatFormula, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons, Clause.eval_nil,
    Literal.eval, Bool.or_false, Bool.and_true, Bool.and_eq_true] at hσ
  cases h : σ 0 <;> simp [h] at hσ

example : SAT.levinStage unsatFormula 0 = none := rfl

example : SAT.levinStage unsatFormula 1 = none := by
  rw [sat_levinStage_one]
  decide

example (K : ℕ) : SAT.levinStage unsatFormula K = none := by
  cases h : SAT.levinStage unsatFormula K with
  | none => rfl
  | some w =>
    exact (unsatFormula_notMem_SAT
      (SAT.exists_levinStage_eq_some_iff.mp ⟨K, w, h⟩)).elim

/-- The fixed native universal search machine for `SAT` halts on `posUnit` with a verified
assignment and diverges on `unsatFormula`. -/
example : ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
    (∃ w, tm.Computes (encCNF posUnit) w ∧ SAT.verifier (posUnit, w) = true) ∧
    ¬tm.Halts (encCNF unsatFormula) := by
  obtain ⟨k, State, hfin, tm, _, hsound, hhalts, -, -⟩ := SAT.exists_native_levinSearch
  have hpos : tm.Halts (encCNF posUnit) := (hhalts posUnit).mpr ⟨fun _ => true, by decide⟩
  obtain ⟨w, hw⟩ := Turing.MultiTapeTM.halts_iff_exists_computes.mp hpos
  exact ⟨k, State, hfin, tm, ⟨w, hw, hsound posUnit w hw⟩,
    mt (hhalts unsatFormula).mp unsatFormula_notMem_SAT⟩

end CslibFrontierTests.UniversalSearch
