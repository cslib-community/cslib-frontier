/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateReindex
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateCornerSwap
public import CslibFrontier.Foundations.Data.Nat.BlockMove
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# The raw table program for appending ordered probes

Source occurrence blocks are left body, left probe, right body, right probe. The program
concatenates the supplied tables with an explicit right offset, splices the two nonempty
probe centers at their last outgoing darts, then moves the left probe behind the right
body and probe. Empty probes skip the splice and introduce no dart at an isolated center.

This module supplies the actual program and its finite-index invariants. Correctness for
accepted ordered bodies additionally identifies its table with the existing scope-join
rotation; that is separate from these raw input bounds.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Graph

/-- Execute the append splice and positional reindexing. Counts come from actual body
occurrence and boundary lists in the caller; raw source entries are only binary lookup data. -/
@[expose] def appendRawCertificate (leftBody leftPorts rightBody rightPorts : ℕ)
    (left right : RotationCertificate) : RotationCertificate :=
  let offset := 2 * (leftBody + leftPorts)
  let disjoint : RotationCertificate :=
    ⟨left.successor ++ right.successor.map (offset + ·)⟩
  let joined := if leftPorts = 0 ∨ rightPorts = 0 then disjoint else
    disjoint.swapSuccessors (offset - 1) (offset + 2 * (rightBody + rightPorts) - 1)
  RotationCertificate.reindex joined (2 * (leftBody + leftPorts + rightBody + rightPorts))
    (Nat.blockMove (2 * leftBody) (2 * leftPorts) (2 * (rightBody + rightPorts)))
    (Nat.blockMove (2 * leftBody) (2 * (rightBody + rightPorts)) (2 * leftPorts))

/-- The emitted table has exactly the total number of original indexed edge ends. -/
@[simp] theorem length_appendRawCertificate (leftBody leftPorts rightBody rightPorts : ℕ)
    (left right : RotationCertificate) :
    (appendRawCertificate leftBody leftPorts rightBody rightPorts left right).successor.length =
      2 * (leftBody + leftPorts + rightBody + rightPorts) :=
  RotationCertificate.length_reindex _ _ _ _

/-- If each supplied entry names a local dart, every emitted entry names a dart of the
combined table. Missing entries and skipped empty-probe splices retain this invariant. -/
theorem entries_appendRawCertificate_lt (leftBody leftPorts rightBody rightPorts : ℕ)
    (left right : RotationCertificate)
    (hl : ∀ a ∈ left.successor, a < 2 * (leftBody + leftPorts))
    (hr : ∀ a ∈ right.successor, a < 2 * (rightBody + rightPorts)) :
    ∀ a ∈ (appendRawCertificate leftBody leftPorts rightBody rightPorts left right).successor,
      a < 2 * (leftBody + leftPorts + rightBody + rightPorts) := by
  intro value hv
  let total := 2 * (leftBody + leftPorts + rightBody + rightPorts)
  let offset := 2 * (leftBody + leftPorts)
  let disjoint : RotationCertificate :=
    ⟨left.successor ++ right.successor.map (offset + ·)⟩
  let joined := if leftPorts = 0 ∨ rightPorts = 0 then disjoint else
    disjoint.swapSuccessors (offset - 1) (offset + 2 * (rightBody + rightPorts) - 1)
  change value ∈ (RotationCertificate.reindex joined total
    (Nat.blockMove (2 * leftBody) (2 * leftPorts) (2 * (rightBody + rightPorts)))
    (Nat.blockMove (2 * leftBody) (2 * (rightBody + rightPorts)) (2 * leftPorts))).successor at hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
  have hi' : i < total := List.mem_range.mp hi
  have hpos : 0 < total := by omega
  have hdisjoint : ∀ a ∈ disjoint.successor, a < total := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · have h := hl a ha
      dsimp only [total]
      omega
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      have h := hr b hb
      dsimp only [total, offset]
      omega
  have read_lt (table : List ℕ) (ht : ∀ a ∈ table, a < total) (j : ℕ) :
      table.getD j 0 < total := by
    rcases List.getD_mem_or table j 0 with hj | hj
    · exact ht _ hj
    · rw [hj]
      exact hpos
  have hjoined : ∀ a ∈ joined.successor, a < total := by
    dsimp only [joined]
    split
    · exact hdisjoint
    · intro a ha
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
      exact read_lt disjoint.successor hdisjoint _
  have hb := read_lt joined.successor hjoined
    (Nat.blockMove (2 * leftBody) (2 * (rightBody + rightPorts)) (2 * leftPorts) i)
  have hb' : joined.successor.getD
      (Nat.blockMove (2 * leftBody) (2 * (rightBody + rightPorts)) (2 * leftPorts) i) 0 <
      2 * leftBody + 2 * leftPorts + 2 * (rightBody + rightPorts) := by
    dsimp only [total] at hb
    omega
  have hbound := Nat.blockMove_lt (before := 2 * leftBody) (moved := 2 * leftPorts)
    (after := 2 * (rightBody + rightPorts)) hb'
  omega

end Cslib.Complexity.CSP.OrderedBoundary
