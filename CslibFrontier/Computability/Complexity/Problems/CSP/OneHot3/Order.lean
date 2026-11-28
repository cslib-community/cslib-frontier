/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.OneHot3
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateReindex
import Mathlib.Data.List.GetD

/-!
# Executed ternary scope order and dart reindexing

For the symmetric ternary base relation, keep the first argument and exchange the last two
when the supplied table rotates the first constraint end toward the third original argument.
Each row contributes six dart indices. The same involution reindexes both ends of each edge;
conjugating the actual successor table retains its direction, rather than reflecting it.

The list semantics and integer identities below hold on every raw input. Geometry and exact
ternary width are needed separately to establish acceptance of the reordered certificate.
This ternary restriction applies only to the base hardness source, not to target languages.
-/

public section

namespace Cslib.Complexity.CSP.OneHot3

open Cslib.Logic.PL Graph

/-- Exchange the second and third entries; shorter raw scopes are retained verbatim. -/
@[expose] def swapTail3 : List ℕ → List ℕ
  | a :: b :: c :: tail => a :: c :: b :: tail
  | xs => xs

/-- Exchanging two positions preserves every original variable occurrence. -/
theorem swapTail3_perm (xs : List ℕ) : (swapTail3 xs).Perm xs := by
  match xs with
  | a :: b :: c :: tail => exact (List.Perm.swap b c tail).cons a
  | [] | [_] | [_, _] => exact List.Perm.refl _

/-- Test the literal first-to-second constraint-end step, using the exact six-dart row
layout. Supplied indices are binary table data and never determine a loop bound. -/
@[expose] def forward (c : RotationCertificate) (i : ℕ) : Bool :=
  decide (c.successor.getD (6 * i + 1) 0 = 6 * i + 3)

/-- Execute the required permutation of each scope. The relation symbol and constraint
position are retained, even for repeated rows and malformed scope lengths. -/
@[expose] def orderedConstraints (F : CSP Unit ℕ) (c : RotationCertificate) : CSP Unit ℕ :=
  F.mapIdx fun i row =>
    ⟨row.rel, if forward c i then row.scope else swapTail3 row.scope⟩

/-- Scope alignment keeps every constraint position, including empty scopes. -/
@[simp] theorem length_orderedConstraints (F : CSP Unit ℕ) (c : RotationCertificate) :
    (orderedConstraints F c).length = F.length := by
  simp only [orderedConstraints, List.length_mapIdx]

/-- Scope alignment preserves each original scope length on all raw tables. -/
theorem scopeLength_orderedConstraints (F : CSP Unit ℕ) (c : RotationCertificate)
    (i : ℕ) (hi : i < F.length) :
    ((orderedConstraints F c)[i]'(by rw [length_orderedConstraints]; exact hi)).scope.length =
      F[i].scope.length := by
  simp only [orderedConstraints, List.getElem_mapIdx]
  split
  · rfl
  · exact (swapTail3_perm _).length_eq

/-- Exact ternary width survives the actual permutation, independently of table validity. -/
theorem wellFormed_orderedConstraints (F : CSP Unit ℕ) (c : RotationCertificate)
    (hw : F.WellFormed arity) : (orderedConstraints F c).WellFormed arity := by
  intro row hrow
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hrow
  have hi' : i < F.length := by simpa only [length_orderedConstraints] using hi
  exact (scopeLength_orderedConstraints F c i hi').trans (hw F[i] (List.getElem_mem hi'))

/-- Reordering symmetric base scopes preserves evaluation under the very same assignment,
independently of whether the raw table or scopes pass a verifier. -/
theorem eval_orderedConstraints (F : CSP Unit ℕ) (c : RotationCertificate) (σ : ℕ → Bool) :
    (orderedConstraints F c).eval sem σ = F.eval sem σ := by
  have hsem (row : Constraint Unit ℕ) (i : ℕ) :
      (Constraint.mk row.rel (if forward c i then row.scope else swapTail3 row.scope)).eval
        sem σ = row.eval sem σ := by
    change sem row.rel ((if forward c i then row.scope else swapTail3 row.scope).map σ) = _
    split
    · rfl
    · exact sem_eq_of_perm _ _ ((swapTail3_perm row.scope).map σ)
  apply Bool.eq_iff_iff.mpr
  simp only [orderedConstraints, Cslib.Logic.PL.CSP.eval, List.all_eq_true, List.mem_mapIdx,
    forall_exists_index]
  refine ⟨fun h row hrow => ?_, fun h _ i hi hrow =>
    hrow ▸ (hsem F[i] i).trans (h F[i] (List.getElem_mem hi))⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hrow
  simpa only [hsem] using h _ i hi rfl

/-- The actual row reorder preserves satisfiability on every raw input table. -/
theorem satisfiable_orderedConstraints_iff (F : CSP Unit ℕ) (c : RotationCertificate) :
    (orderedConstraints F c).Satisfiable sem ↔ F.Satisfiable sem := by
  simp only [Cslib.Logic.PL.CSP.Satisfiable, eval_orderedConstraints]

/-- Reindex an actual edge/end index when the last two ternary arguments are exchanged.
The quotient, remainder and successor entries remain binary data on arbitrary raw indices. -/
@[expose] def dartReindex (c : RotationCertificate) (a : ℕ) : ℕ :=
  let row := a / 6
  let port := a / 2 % 3
  let newPort :=
    if forward c row then port else if port = 1 then 2 else if port = 2 then 1 else port
  6 * row + 2 * newPort + a % 2

/-- Dart reindexing retains the original constraint row. -/
theorem dartReindex_row (c : RotationCertificate) (a : ℕ) :
    dartReindex c a / 6 = a / 6 := by
  have hp : a / 2 % 3 < 3 := Nat.mod_lt _ (by decide)
  have hs : a % 2 < 2 := Nat.mod_lt _ (by decide)
  dsimp only [dartReindex]
  split_ifs <;> omega

/-- Both ends of an edge retain their original end tag under scope reordering. -/
theorem dartReindex_side (c : RotationCertificate) (a : ℕ) :
    dartReindex c a % 2 = a % 2 := by
  have hp : a / 2 % 3 < 3 := Nat.mod_lt _ (by decide)
  have hs : a % 2 < 2 := Nat.mod_lt _ (by decide)
  dsimp only [dartReindex]
  split_ifs <;> omega

/-- The native port index undergoes exactly the same exchange as the scope. -/
theorem dartReindex_port (c : RotationCertificate) (a : ℕ) :
    dartReindex c a / 2 % 3 =
      if forward c (a / 6) then a / 2 % 3
      else if a / 2 % 3 = 1 then 2 else if a / 2 % 3 = 2 then 1 else a / 2 % 3 := by
  have hp : a / 2 % 3 < 3 := Nat.mod_lt _ (by decide)
  have hs : a % 2 < 2 := Nat.mod_lt _ (by decide)
  dsimp only [dartReindex]
  split_ifs <;> omega

/-- The literal native reindexing is its own inverse, including malformed binary indices. -/
theorem dartReindex_involutive (c : RotationCertificate) :
    Function.Involutive (dartReindex c) := by
  intro a
  rw [dartReindex, dartReindex_row, dartReindex_port, dartReindex_side]
  have hp : a / 2 % 3 < 3 := Nat.mod_lt _ (by decide)
  have hs : a % 2 < 2 := Nat.mod_lt _ (by decide)
  split_ifs <;> omega

/-- Reindexing never leaves the actual six-dart row interval. -/
theorem dartReindex_lt (c : RotationCertificate) {a n : ℕ} (ha : a < 6 * n) :
    dartReindex c a < 6 * n := by
  have hrow := dartReindex_row c a
  omega

/-- Conjugate the actual binary successor table by the executed scope permutation.
Only the original graph's actual edge-list length funds the output scan. -/
@[expose] def orderedCertificate (F : CSP Unit ℕ) (c : RotationCertificate) :
    RotationCertificate :=
  RotationCertificate.reindex c (2 * (incidenceGraph F).edges.length)
    (dartReindex c) (dartReindex c)

/-- The table has one entry per original indexed edge end, even for invalid input data. -/
@[simp] theorem length_orderedCertificate (F : CSP Unit ℕ) (c : RotationCertificate) :
    (orderedCertificate F c).successor.length = 2 * (incidenceGraph F).edges.length := by
  exact RotationCertificate.length_reindex _ _ _ _

/-- Reading an actual output position gives the literal conjugation of the supplied
table. All missing input entries still use the program's fixed zero fallback. -/
theorem getD_orderedCertificate (F : CSP Unit ℕ) (c : RotationCertificate) {a : ℕ}
    (ha : a < 2 * (incidenceGraph F).edges.length) :
    (orderedCertificate F c).successor.getD a 0 =
      dartReindex c (c.successor.getD (dartReindex c a) 0) := by
  exact RotationCertificate.getD_reindex _ _ _ _ ha

end Cslib.Complexity.CSP.OneHot3
