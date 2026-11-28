/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Layout
import Mathlib.Data.List.GetD

/-!
# The clauses of the quasilinear formula

Clause `i` of the quasilinear formula (`Cslib.Complexity.CookLevin.Quasilinear.Layout.clauseAt`)
is slot `i % 4` of gate `i / 4 % G` of constraint `i / 4 / G`, where `G` bounds the number of gates
of a constraint (`Layout.G`); the constraint index is read as the number of a `Family`, `· / MAXI`,
and a constraint of it, `· % MAXI`. The constraints and gates of a family number
(`Layout.countAt`, `Layout.famGatesAt`) are those of the family with that number, and none when
there is no such family. Indices that name no gate give a tautology (`Layout.tautClause`).

## Main definitions

* `Cslib.Complexity.CookLevin.Quasilinear.Layout.G`: a bound on the gates of a constraint.
* `Cslib.Complexity.CookLevin.Quasilinear.Layout.countAt`, `Layout.famGatesAt`: the constraints
  of a family, given by its number.
* `Cslib.Complexity.CookLevin.Quasilinear.Layout.clauseAt`: clause `i` of the formula.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Quasilinear

open Cslib.Logic.PL

namespace Layout

variable (Λ : Layout) (D : MachineData) (x : List Bool)

/-- A bound on the number of gates of a constraint, for `R` allowed pairs. -/
def G (R : ℕ) : ℕ := Λ.A R + 8

/-- The number of bits of a clause index: enough for `36 · MAXI · G` indices. -/
def addressBits (R : ℕ) : ℕ := Nat.clog 2 (36 * Λ.MAXI * Λ.G R)

/-- The number of bits of a variable: enough for every variable below the last fresh one. -/
def variableBits (R : ℕ) : ℕ := Nat.clog 2 (Λ.AUX + 9 * Λ.MAXI * Λ.A R + 1)

/-- The tautology standing for unused clause indices. -/
def tautClause : Clause ℕ := [(0, true), (0, false), (0, false)]

/-- The number of constraints of the family with number `n`; `0` when there is no such family. -/
def countAt (n : ℕ) : ℕ := (Family.all.map Λ.count).getD n 0

/-- The gates defining the fresh variables of constraint `inst` of the family with number `n`;
none when there is no such family. -/
def famDefsAt (n inst : ℕ) : List Gate := (Family.all.map fun f => Λ.famDefs D x f inst).getD n []

/-- The assertion gates of constraint `inst` of the family with number `n`; none when there is no
such family. -/
def famConsAt (n inst : ℕ) : List Gate := (Family.all.map fun f => Λ.famCons D x f inst).getD n []

/-- All gates of constraint `inst` of the family with number `n`. -/
def famGatesAt (n inst : ℕ) : List Gate := Λ.famDefsAt D x n inst ++ Λ.famConsAt D x n inst

/-- Looking up a family by its number gives the family's constraints. -/
theorem countAt_index (fam : Family) : Λ.countAt fam.index = Λ.count fam := by
  cases fam <;> rfl

/-- Looking up a family by its number gives the family's defining gates. -/
private theorem famDefsAt_index (fam : Family) (inst : ℕ) :
    Λ.famDefsAt D x fam.index inst = Λ.famDefs D x fam inst := by
  cases fam <;> rfl

/-- Looking up a family by its number gives the family's assertion gates. -/
private theorem famConsAt_index (fam : Family) (inst : ℕ) :
    Λ.famConsAt D x fam.index inst = Λ.famCons D x fam inst := by
  cases fam <;> rfl

/-- Looking up a family by its number gives the family's gates. -/
theorem famGatesAt_index (fam : Family) (inst : ℕ) :
    Λ.famGatesAt D x fam.index inst = Λ.famGates D x fam inst := by
  rw [famGatesAt, famGates, famDefsAt_index, famConsAt_index]

/-- There is no constraint of a number that is no family's. -/
private theorem countAt_of_ge {n : ℕ} (hn : 9 ≤ n) : Λ.countAt n = 0 :=
  List.getD_eq_default _ _ (by simpa [Family.all] using hn)

/-- The numbers of constraints of the families, as an explicit list indexed by the family number.
-/
theorem countAt_eq_getD (n : ℕ) :
    Λ.countAt n = [1, 1, 1, Λ.N - 1, (Λ.N - 1) * Λ.I * 3, Λ.N * Λ.I, (Λ.N - 1) * Λ.k,
      Λ.k * Λ.L * Λ.N * Λ.P, Λ.k * Λ.N].getD n 0 :=
  rfl

/-- A number with a constraint is a family's number. -/
theorem lt_nine_of_lt_countAt {n inst : ℕ} (h : inst < Λ.countAt n) : n < 9 := by
  by_contra hn
  rw [Λ.countAt_of_ge (by omega)] at h
  omega

/-- Clause `i` of the formula: slot `i % 4` of gate `i / 4 % G` of constraint `i / 4 / G`, read as
family number `· / MAXI` and constraint `· % MAXI`, or a tautology when no such gate exists. -/
def clauseAt (i : ℕ) : Clause ℕ :=
  if i / 4 / Λ.G D.pairs.length % Λ.MAXI < Λ.countAt (i / 4 / Λ.G D.pairs.length / Λ.MAXI) ∧
      i / 4 % Λ.G D.pairs.length < (Λ.famGatesAt D x (i / 4 / Λ.G D.pairs.length / Λ.MAXI)
        (i / 4 / Λ.G D.pairs.length % Λ.MAXI)).length then
    ((Λ.famGatesAt D x (i / 4 / Λ.G D.pairs.length / Λ.MAXI)
      (i / 4 / Λ.G D.pairs.length % Λ.MAXI)).getD (i / 4 % Λ.G D.pairs.length) default).clause
        (i % 4)
  else tautClause

end Layout

end Cslib.Complexity.CookLevin.Quasilinear
