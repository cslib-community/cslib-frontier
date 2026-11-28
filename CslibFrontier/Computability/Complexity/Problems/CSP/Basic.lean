/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CSP.Boolean
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Complexity.Problems.SAT
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Reduction.Guard
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Native satisfiability for fixed finite Boolean constraint languages

`Cslib.Complexity.CSPSAT arity sem` contains exactly the well-formed satisfiable instances in
the existing CSP representation, with variables numbered by arbitrary natural numbers. Its
encoding is the existing `encCSP encRel encNat`: framed lists/pairs and binary variable indices.
The relation alphabet, its encoding, arities and semantics are fixed independently of the
instance [Chen2006CSP], Definitions 3.1–3.3. Repeated variables and empty scopes are allowed;
incorrect scope lengths are rejected, and empty relations are interpreted as false.

For every finite relation alphabet this problem belongs to native `NP`. The proof compiles
forbidden local assignments to CNF using the existing fixed-width polynomial-time compiler;
malformed inputs produce an empty clause. No uniform bound in the size of the language is
claimed.

## Main definitions

* `Cslib.Complexity.CSPSAT`: well-formed satisfiable instances of a fixed Boolean language.

## Main results

* `Cslib.Complexity.CSPSAT.polyTimeReducible_of_guard`: a compiler that is faithful on
  well-formed instances, guarded by exact arity, is a polynomial-time reduction.
* `Cslib.Complexity.CSPSAT.exists_boundedWidth_reduction_toSAT`: native compilation to bounded-width
  CNF without introducing variables.
* `Cslib.Complexity.CSPSAT.mem_NP`: membership in native NP for a finite relation alphabet.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The well-formed satisfiable instances of a fixed Boolean constraint language. -/
@[expose] def CSPSAT {Rel : Type} (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) :
    Set (CSP Rel ℕ) :=
  {F | F.WellFormed arity ∧ F.Satisfiable sem}

namespace CSPSAT

variable {Rel : Type}

/-- Membership separates exact-arity syntax from satisfiability. -/
theorem mem_iff (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (F : CSP Rel ℕ) :
    F ∈ CSPSAT arity sem ↔ F.WellFormed arity ∧ F.Satisfiable sem := Iff.rfl

/-- **Guarded compilation.** A polynomial-time compiler that is faithful on well-formed
instances, followed by an exact-arity guard sending every malformed instance to a fixed instance
outside the target, reduces `CSPSAT` to the target. -/
theorem polyTimeReducible_of_guard [Finite Rel] {β : Type} {encB : β ↪ List Bool}
    {B : Set β} (encRel : Rel ↪ List Bool) (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    {compile : CSP Rel ℕ → β} (reject : β)
    (hcompile : ComputableInPolyTime compile (encCSP encRel encNat) encB)
    (hcorrect : ∀ F, F.WellFormed arity → (F.Satisfiable sem ↔ compile F ∈ B))
    (hreject : reject ∉ B) :
    PolyTimeReducible (encCSP encRel encNat) encB (CSPSAT arity sem) B :=
  .of_guard reject (CSP.computableInPolyTime_validArity encRel arity) hcompile hreject fun F => by
    rw [mem_iff, CSP.validArity_eq_true_iff]
    exact and_congr_right (hcorrect F)

/-- For a fixed finite Boolean language, the guarded forbidden-assignment compiler reduces
exact-arity CSP satisfiability to CNF SAT without introducing variables. The clause width is
bounded by the maximum relation arity. Malformed inputs map to the variable-free rejecting
formula. -/
theorem exists_boundedWidth_reduction_toSAT [Finite Rel]
    (encRel : Rel ↪ List Bool) (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) :
    ∃ (f : CSP Rel ℕ → CNF ℕ) (k : ℕ),
      ComputableInPolyTime f (encCSP encRel encNat) encCNF ∧
      (∀ F, F ∈ CSPSAT arity sem ↔ f F ∈ SAT) ∧
      (∀ F, (f F).numVars ≤ F.numVars) ∧
      (∀ F, ∀ c ∈ f F, c.length ≤ k) := by
  classical
  let _ := Fintype.ofFinite Rel
  let k := Finset.univ.sup arity
  let reduce (F : CSP Rel ℕ) : CNF ℕ :=
    if CSP.validArity arity F then F.toCNFBounded k sem else [[]]
  refine ⟨reduce, k, (CSP.computableInPolyTime_validArity encRel arity).ite
    (CSP.computableInPolyTime_toCNFBounded_of_finite encRel encNat k sem)
    (ComputableInPolyTime.const [[]]), ?_, ?_, ?_⟩
  · intro F
    dsimp only [reduce]
    split_ifs with h
    · have hf := (CSP.validArity_eq_true_iff arity F).mp h
      have hw : ∀ c ∈ F, c.scope.length ≤ k := fun c hc =>
        (hf c hc).le.trans (Finset.le_sup (Finset.mem_univ c.rel))
      rw [mem_iff, and_iff_right hf, mem_SAT, CSP.toCNFBounded_eq_toCNF hw, CSP.satisfiable_toCNF]
    · have hf := mt (CSP.validArity_eq_true_iff arity F).mpr h
      simp [mem_iff, hf, mem_SAT, CNF.Satisfiable, CNF.eval, Clause.eval]
  · intro F
    dsimp only [reduce]
    split_ifs
    · exact CSP.numVars_toCNFBounded_le k sem F
    · simp [CNF.numVars, CNF.vars]
  · intro F
    dsimp only [reduce]
    split_ifs
    · exact fun _ hc => CSP.length_clause_mem_toCNFBounded hc
    · intro c hc
      rw [List.mem_singleton] at hc
      subst c
      exact Nat.zero_le k

/-- Every fixed finite Boolean constraint language has a native NP satisfiability problem,
under framed list/pair encodings with binary variable indices. -/
theorem mem_NP [Finite Rel] (encRel : Rel ↪ List Bool) (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) : CSPSAT arity sem ∈ NP (encCSP encRel encNat) := by
  obtain ⟨f, _, hpoly, hmem, _, _⟩ := exists_boundedWidth_reduction_toSAT encRel arity sem
  exact (show PolyTimeReducible (encCSP encRel encNat) encCNF (CSPSAT arity sem) SAT from
    ⟨f, hpoly, hmem⟩).mem_NP SAT.mem_NP

end CSPSAT

end Cslib.Complexity
