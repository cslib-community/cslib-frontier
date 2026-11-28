/-
Copyright (c) 2026 Matthew Doty, Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Nick L. Leppelmeier
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF

/-!
# Weighted partial MaxSAT

A weighted partial MaxSAT instance (`Cslib.Logic.PL.MaxSAT`) pairs hard clauses `hard : CNF V`
with weighted soft clauses `soft : List (Clause V × ℕ)` (repeated soft clauses are counted with
their multiplicity). An assignment is feasible (`Cslib.Logic.PL.MaxSAT.feasible`) when it
satisfies `hard`, and its cost (`Cslib.Logic.PL.MaxSAT.cost`) is the total weight of the soft
clauses it falsifies. The problem is to find the least cost of a feasible assignment, as
in [Bacchus, Järvisalo and Martins][BacchusJarvisaloMartins2021].

This module holds only the definition, stated with the existing clause semantics
`Cslib.Logic.PL.CNF.eval` and `Cslib.Logic.PL.Clause.eval`. Its first client is the
pseudo-Boolean encoding `CslibFrontier.Logics.Propositional.PseudoBoolean.MaxSAT`.

## Main definitions

* `Cslib.Logic.PL.MaxSAT`, `Cslib.Logic.PL.MaxSAT.feasible`, `Cslib.Logic.PL.MaxSAT.cost`.

## References

* [F. Bacchus, M. Järvisalo, R. Martins, *Maximum Satisfiability*][BacchusJarvisaloMartins2021]
-/

public section

namespace Cslib.Logic.PL

/-- A weighted partial MaxSAT instance over variable type `V`. Repeated soft clauses are counted
with multiplicity. -/
@[ext]
structure MaxSAT (V : Type*) where
  /-- Clauses that must be satisfied by every feasible assignment. -/
  hard : CNF V
  /-- Soft clauses paired with non-negative integer weights. -/
  soft : List (Clause V × ℕ)

namespace MaxSAT

variable {V : Type*}

/-- An assignment is feasible when it satisfies every hard clause. -/
@[expose] def feasible (φ : MaxSAT V) (σ : V → Bool) : Prop :=
  φ.hard.eval σ = true

/-- Total weight of soft clauses falsified by `σ`. -/
@[expose] def cost (φ : MaxSAT V) (σ : V → Bool) : ℕ :=
  (φ.soft.map fun cw => if cw.1.eval σ then 0 else cw.2).sum

end MaxSAT

end Cslib.Logic.PL

end
