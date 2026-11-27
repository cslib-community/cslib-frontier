/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Rational.Runtime.Determinant
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Complexity.Problems.Permanent.Matching
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks
import CslibFrontier.Foundations.Data.Matrix.Permanent.Determinant
import Mathlib.Data.List.GetD
import Mathlib.Data.ZMod.Basic

/-!
# Parity of the number of bipartite perfect matchings

The parity of the number of perfect matchings of a Boolean biadjacency table is computable in
polynomial time: lift its entries to integers, compute the division-free integer determinant,
and reduce modulo two. The determinant becomes the permanent in characteristic two, and the
permanent counts perfect matchings of `bipartiteGraph`.

This proves the unique-versus-none promise decision step of [Goldreich, Exercise 6.36(b)]
[Goldreich2007Draft] (February 2007 `r3.pdf`, printed p. 263 / PDF p. 61): accept a graph with
exactly one perfect matching and reject a graph with none. Tables with more matchings are outside
the promise; the algorithm accepts exactly those with an odd count. The empty table has one
perfect matching and is accepted. Ragged rows use the same zero-padding convention as
`BipartitePerfectMatchingCount`, and entries past the square are ignored.

This is not the full exercise: no polynomial-time search relation for matchings is constructed
here. Its counting hardness is supplied separately by the existing permanent reduction.

## Main results

* `bipartiteMatchingParity_eq_true_iff`: the algorithm computes the matching count modulo two.
* `uniqueBipartiteMatching_mem_PromiseP`: unique versus no perfect matching is in promise-P.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM
open Cslib.Circuits.Rational

private def integerRows (A : List (List Bool)) : List (List ℤ) :=
  A.map fun row => row.map fun b => if b then 1 else 0

private theorem determinant_integerRows (A : List (List Bool)) :
    detRows (integerRows A) = ((boolTableMatrix A).map (Nat.cast : ℕ → ℤ)).det := by
  refine detRows_eq_det_of_rowEntry _ (by simp [integerRows]) ?_
  intro i j
  simp only [rowEntry, integerRows, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem i.isLt, Option.map_some, Option.getD_some,
    Matrix.map_apply, boolTableMatrix_apply]
  cases A[i][j.val]? with
  | none => simp
  | some b => cases b <;> simp

private theorem determinant_cast_eq_count (A : List (List Bool)) :
    (detRows (integerRows A) : ZMod 2) = (BipartitePerfectMatchingCount A : ZMod 2) := by
  rw [determinant_integerRows, Int.cast_det, Matrix.det_eq_permanent_of_charTwo,
    bipartitePerfectMatchingCount_eq_zeroOnePermanent, ZeroOnePermanent]
  change _ = (Nat.castRingHom (ZMod 2)) (boolTableMatrix A).permanent
  rw [RingHom.map_permanent]
  congr 1

/-- The parity test for a Boolean biadjacency table: compute its integer determinant and accept
when its residue modulo two is one. -/
@[expose] def bipartiteMatchingParity (A : List (List Bool)) : Bool :=
  decide ((detRows (A.map fun row => row.map fun b => if b then 1 else 0) % 2).toNat = 1)

/-- The determinant-parity algorithm is polynomial-time on framed lists of Boolean rows. -/
@[fun_prop] theorem bipartiteMatchingParity_polyTime :
    ComputableInPolyTime bipartiteMatchingParity encBoolTable encBool := by
  have hrows : ComputableInPolyTime integerRows encBoolTable Cslib.encIntTable := by
    unfold integerRows
    fun_prop
  have hdet := detRows_polytime.comp hrows
  change ComputableInPolyTime (fun A => decide ((detRows (integerRows A) % 2).toNat = 1))
    encBoolTable encBool
  fun_prop

/-- The algorithm accepts exactly the tables whose bipartite graph has an odd number of perfect
matchings. This specifies its behavior outside the unique-versus-none promise as well. -/
theorem bipartiteMatchingParity_eq_true_iff (A : List (List Bool)) :
    bipartiteMatchingParity A = true ↔ BipartitePerfectMatchingCount A % 2 = 1 := by
  have h := congrArg ZMod.val (determinant_cast_eq_count A)
  have hv := ZMod.val_intCast (n := 2) (detRows (integerRows A))
  rw [ZMod.val_natCast] at h
  simp only [bipartiteMatchingParity, decide_eq_true_eq]
  change (detRows (integerRows A) % 2).toNat = 1 ↔ _
  omega

/-- The promise problem on Boolean biadjacency tables with exactly one perfect matching
(yes) or no perfect matching (no). -/
@[expose] def uniqueBipartiteMatching : PromiseProblem (List (List Bool)) where
  yes := {A | BipartitePerfectMatchingCount A = 1}
  no := {A | BipartitePerfectMatchingCount A = 0}
  disjoint := Set.disjoint_left.mpr fun _ h₁ h₀ => by simp_all

/-- The unique-versus-none decision step of Goldreich Exercise 6.36(b): the determinant modulo
two separates a unique perfect matching from no perfect matching, in polynomial time. -/
theorem uniqueBipartiteMatching_mem_PromiseP :
    uniqueBipartiteMatching ∈ PromiseP encBoolTable := by
  refine mem_PromiseP_iff.mpr ⟨bipartiteMatchingParity, bipartiteMatchingParity_polyTime,
    (fun A hA => (bipartiteMatchingParity_eq_true_iff A).mpr ?_), fun A hA => ?_⟩
  · change BipartitePerfectMatchingCount A = 1 at hA
    simp [hA]
  · change BipartitePerfectMatchingCount A = 0 at hA
    rw [Bool.eq_false_iff, ne_eq, bipartiteMatchingParity_eq_true_iff, hA]
    decide

end Cslib.Complexity
