/-
Copyright (c) 2026 Josh Liebow-Feeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Liebow-Feeser
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.ProofSystem.Optimal

/-! Tests for optimal and p-optimal proof systems: concrete witnesses via `ofDecider` and `join`,
binary join laws, polynomial-boundedness transfer, and the forward `NP`-subset theorem. -/

set_option linter.privateModule false

namespace CslibFrontierTests.ProofSystemOptimal

open Cslib.Complexity Turing.MultiTapeTM

/-- The pairs of Booleans whose first component is `true`. -/
abbrev FirstTrue : Set (Bool × Bool) := {q | q.1 = true}

theorem polyTime_firstTrue_decider :
    ComputableInPolyTime (fun q : Bool × Bool => q.1)
      (encPair encBool encBool) encBool := by
  fun_prop

theorem firstTrue_mem_P : FirstTrue ∈ P (encPair encBool encBool) :=
  ⟨fun q => q.1, polyTime_firstTrue_decider, fun _ => Iff.rfl⟩

/-- Concrete p-optimal proof system for `FirstTrue`, using `(true, true)` as fallback. -/
noncomputable abbrev firstTrueSystem : ProofSystem (encPair encBool encBool) FirstTrue :=
  ProofSystem.ofDecider (.pair .bool .bool) polyTime_firstTrue_decider (fun _ => Iff.rfl)
    (a₀ := (true, true)) rfl

/-- Alternative concrete p-optimal proof system for `FirstTrue`, using `(true, false)` as
fallback. -/
noncomputable abbrev firstTrueSystemAlt : ProofSystem (encPair encBool encBool) FirstTrue :=
  ProofSystem.ofDecider (.pair .bool .bool) polyTime_firstTrue_decider (fun _ => Iff.rfl)
    (a₀ := (true, false)) rfl

/-- Both decider-based proof systems for `FirstTrue` are p-optimal and therefore optimal. -/
example : firstTrueSystem.IsPOptimal :=
  ProofSystem.isPOptimal_ofDecider _ _ _ _

example : firstTrueSystem.IsOptimal :=
  (ProofSystem.isPOptimal_ofDecider _ _ _ _).isOptimal

/-- Any two p-optimal systems mutually p-simulate each other. -/
example : firstTrueSystem.PSimulates firstTrueSystemAlt ∧
    firstTrueSystemAlt.PSimulates firstTrueSystem :=
  (ProofSystem.isPOptimal_ofDecider _ _ _ _).mutual_pSimulates
    (ProofSystem.isPOptimal_ofDecider _ _ _ _)

/-- Concrete evaluation of `join` on tagged proofs and the empty proof. -/
example :
    firstTrueSystem.join firstTrueSystemAlt
      (false :: encPair encBool encBool (true, false)) = (true, false) := by
  rw [ProofSystem.join_false_cons]
  exact ProofSystem.ofDecider_enc _ _ _ _ rfl

example :
    firstTrueSystem.join firstTrueSystemAlt
      (true :: encPair encBool encBool (true, true)) = (true, true) := by
  rw [ProofSystem.join_true_cons]
  exact ProofSystem.ofDecider_enc _ _ _ _ rfl

example :
    firstTrueSystem.join firstTrueSystemAlt [] = firstTrueSystem [] :=
  ProofSystem.join_nil _ _

/-- `join` is a binary join for both `PSimulates` and `Simulates`. -/
example {α : Type} {enc : α ↪ List Bool} {L : Set α}
    (R P Q : ProofSystem enc L) :
    R.PSimulates (P.join Q) ↔ R.PSimulates P ∧ R.PSimulates Q :=
  ProofSystem.pSimulates_join_iff

example {α : Type} {enc : α ↪ List Bool} {L : Set α}
    (R P Q : ProofSystem enc L) :
    R.Simulates (P.join Q) ↔ R.Simulates P ∧ R.Simulates Q :=
  ProofSystem.simulates_join_iff

/-- Conditional existence for `P`, `NP`, and `UNSAT` under `NP = coNP`. -/
example : ∃ Q : ProofSystem (encPair encBool encBool) FirstTrue, Q.IsPOptimal :=
  ProofSystem.exists_isPOptimal_of_mem_P (.pair .bool .bool) ⟨(true, true), rfl⟩ firstTrue_mem_P

example (h : ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC) :
    ∃ P : ProofSystem encCNF UNSAT, P.IsOptimal :=
  ProofSystem.exists_isOptimal_UNSAT_of_NP_eq_coNP h

/-- Bridge between optimality of a refutation system for `UNSAT` and `NP = coNP`. -/
example {P : ProofSystem encCNF UNSAT} (hP : P.IsOptimal) :
    P.PolynomiallyBounded ↔ ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC :=
  hP.polynomiallyBounded_UNSAT_iff_NP_eq_coNP

/-- Forward `(2) → (3)` direction of Krajíček–Pudlák Theorem 2.1(i). -/
example {α : Type} {enc : α ↪ List Bool} {L X : Set α}
    {P : ProofSystem enc L} (hP : P.IsOptimal) (D : Decoder enc)
    (hXL : X ⊆ L) (hX : X ∈ NP enc) :
    ∃ p : Polynomial ℕ, ∀ a ∈ X, ∃ π, P π = a ∧ π.length ≤ p.eval (enc a).length :=
  hP.polyBounded_on_NP_subset D hXL hX

end CslibFrontierTests.ProofSystemOptimal
