/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Completeness
public import CslibFrontier.Computability.Complexity.Problems.SharpSAT
public import CslibFrontier.Computability.Complexity.Problems.ThreeSATThree.Size
public import CslibFrontier.Computability.Complexity.Problems.ThreeSATThree.Syntax

/-!
# Parsimonious occurrence reduction for 3SAT

The existing occurrence splitter preserves the number of satisfying assignments. Each source
variable has one value on every copy in its implication cycle, and numbering copies is injective.
The counting problems below count only occurring variables and return zero outside their syntax.
They reuse `SharpSAT` and the existing syntax guards rather than introducing new assignment
or satisfiability semantics.

## Main definitions

* `Cslib.Complexity.SharpThreeSAT`: model count for width-at-most-three CNF, zero otherwise.
* `Cslib.Complexity.SharpThreeSATThree`: model count with the additional three-occurrence bound.

## Main results

* `Cslib.Complexity.sharpThreeSATThree_toThreeSATThree`: exact counts for the total compiler.
* `Cslib.Complexity.SharpThreeSAT.mem_ThreeSAT_iff`,
  `Cslib.Complexity.SharpThreeSATThree.mem_ThreeSATThree_iff`: positivity recovers the languages.
* `Cslib.Complexity.parsimoniousReducible_SharpThreeSAT_SharpThreeSATThree`: the existing
  polynomial-time compiler is a parsimonious reduction.

## References

The occurrence construction and its source credit are documented in `ThreeSATThree`. Its count
preservation is an original elementary consequence of `CNF.copies_agree`.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL

/-- Count satisfying assignments of width-at-most-three CNF; reject other syntax with count zero.
Only variables occurring in the formula are counted. -/
def SharpThreeSAT (φ : CNF ℕ) : ℕ :=
  if φ.all (fun c => decide (c.length ≤ 3)) then SharpSAT φ else 0

/-- Count satisfying assignments of width-three, occurrence-three CNF; reject other syntax with
count zero. Repetitions are literal positions, as in `ThreeSATThree.syntaxCheck`. -/
def SharpThreeSATThree (φ : CNF ℕ) : ℕ :=
  if ThreeSATThree.syntaxCheck φ then SharpSAT φ else 0

/-- Membership in `ThreeSAT` is equivalent to a positive guarded model count. -/
theorem SharpThreeSAT.mem_ThreeSAT_iff {φ : CNF ℕ} :
    φ ∈ ThreeSAT ↔ 0 < SharpThreeSAT φ := by
  simp only [ThreeSAT, Set.mem_ofPred_eq, SharpThreeSAT]
  split <;> simp_all [List.all_eq_true, CNF.modelCount_pos_iff, SharpSAT]

/-- Membership in `ThreeSATThree` is equivalent to a positive guarded model count. -/
theorem SharpThreeSATThree.mem_ThreeSATThree_iff {φ : CNF ℕ} :
    φ ∈ ThreeSATThree ↔ 0 < SharpThreeSATThree φ := by
  rw [ThreeSATThree, Set.mem_ofPred_eq, ← and_assoc, ← ThreeSATThree.syntaxCheck_iff,
    SharpThreeSATThree]
  split_ifs with hg <;> simp [hg, SharpSAT, CNF.modelCount_pos_iff]

/-- The total occurrence compiler preserves the count, including rejected inputs. -/
theorem sharpThreeSATThree_toThreeSATThree (φ : CNF ℕ) :
    SharpThreeSATThree (toThreeSATThree φ) = SharpThreeSAT φ := by
  have hout := (ThreeSATThree.syntaxCheck_iff (toThreeSATThree φ)).2
    ⟨width_toThreeSATThree φ, count_vars_toThreeSATThree_le φ⟩
  simp only [SharpThreeSATThree, SharpThreeSAT, hout, ↓reduceIte, SharpSAT]
  split_ifs with hw
  · exact modelCount_toThreeSATThree φ (by simpa [List.all_eq_true] using hw)
  · simp only [toThreeSATThree, hw, Bool.false_eq_true, ↓reduceIte]
    decide

/-- The already-certified polynomial-time 3SAT-to-3SAT-3 compiler is parsimonious. -/
theorem parsimoniousReducible_SharpThreeSAT_SharpThreeSATThree :
    ParsimoniousReducible encCNF encCNF SharpThreeSAT SharpThreeSATThree :=
  ⟨toThreeSATThree, computableInPolyTime_toThreeSATThree,
    fun φ => (sharpThreeSATThree_toThreeSATThree φ).symm⟩

end Cslib.Complexity
