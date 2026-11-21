/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Prefix
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

set_option linter.privateModule false

open Cslib.Complexity Cslib.Logic.PL

-- Both truth values occur at level one; universal validity is a different language.
example : QBF.ex 0 (.var 0) ∈ SigmaSAT 1 := by decide
example : QBF.ex 0 (.bot) ∉ SigmaSAT 1 := by decide
example : QBF.all 0 (.var 0) ∉ PiSAT 1 := by decide
example : QBF.all 0 (.or (.var 0) (.not (.var 0))) ∈ PiSAT 1 := by decide

-- At level two, a later existential choice can copy the universal choice.
example : QBF.all 0 (.ex 1 (QBF.iff (.var 0) (.var 1))) ∈ PiSAT 2 := by decide
example : QBF.ex 0 (.all 1 (QBF.iff (.var 0) (.var 1))) ∉ SigmaSAT 2 := by decide

-- Repeated bound names use the innermost assignment.
example : QBF.ex 0 (.all 0 (.var 0)) ∉ SigmaSAT 2 := by decide
example : (QuantifiedSAT.trueVars [0, 0] [true, false]).contains 0 = false := by
  rw [QuantifiedSAT.contains_trueVars]
  rfl

-- The languages reject free variables, extra alternations and non-prenex quantifiers.
example : QBF.ex 0 (.var 1) ∉ SigmaSAT 1 := by decide
example : QBF.ex 0 (.all 1 (.top)) ∉ SigmaSAT 1 := by decide
example : QBF.and (.ex 0 (.var 0)) .top ∉ SigmaSAT 2 := by decide

-- Zero levels and empty-block padding have explicit behavior.
example : (QBF.top : QBF ℕ) ∈ SigmaSAT 0 := by decide
example : (QBF.bot : QBF ℕ) ∉ PiSAT 0 := by decide
example : (QBF.top : QBF ℕ) ∈ SigmaSAT 3 := by decide
example : QBF.all 0 (.or (.var 0) (.not (.var 0))) ∉ SigmaSAT 2 := by decide

-- Parsing and the record encoding retain the actual syntax and declared field layout.
example : PrenexQBF.parse true 2 (.ex 7 (.all 9 (.or (.var 7) (.var 9)))) =
    ⟨[[7], [9]], .or (.var 7) (.var 9)⟩ := rfl
example (a : PrenexQBF) : encPrenexQBF a =
    Turing.MultiTapeTM.encPair
      (Turing.MultiTapeTM.encList (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat))
      encQBF (a.blocks, a.matrix) := rfl

-- The shared scan accepts input-dependent predicates without domain-specific proof plumbing.
example : Turing.MultiTapeTM.ComputableInPolyTime
    (fun p : List ℕ × ℕ => p.1.takeWhile (fun n => n < p.2))
    (Turing.MultiTapeTM.encPair (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat)
      Turing.MultiTapeTM.encNat) (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat) := by
  fun_prop

-- Extracting the shared matrix preserves the existing TQBF formula syntax exactly.
example {k : ℕ} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w : ℕ) :
    TQBF.baseFormula tab w = QBF.exs (TQBF.baseVars tab w)
      (.and (TQBF.certLinks k State w) (QBF.ofCNF (tab.relabel TQBF.tabVar))) := rfl
