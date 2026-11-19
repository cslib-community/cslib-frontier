/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateReindex
public import CslibFrontier.Foundations.Data.Nat.BlockMove

import Mathlib.Data.Nat.Size

/-!
# Directed boundary rotation on raw successor tables

The body-prefix occurrence count and boundary length determine the probe window.
Only that window is shifted; binary indices outside it stay fixed. Counts zero and one
return the entire supplied certificate, including malformed or surplus entries.

## Main definitions

* `OrderedBoundary.rotateBoundaryCertificateRight`: one RIGHT step with exact short identity.
* `OrderedBoundary.boundaryIndexMap`: transport a probe-window index with its side bit.
* `OrderedBoundary.rotateBoundaryCertificate`: one forward probe-index shift, with its
  separate inverse lookup map and the existing transformed-zero fallback.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

/-- Map a dart index inside the boundary probe window using `shift`, preserving its side bit.
Body-prefix and out-of-window indices remain fixed. -/
@[expose] def boundaryIndexMap (M N : ℕ) (shift : ℕ → ℕ) (i : ℕ) : ℕ :=
  if 2 * M ≤ i ∧ i < 2 * (M + N) then
    2 * (M + shift (i / 2 - M)) + i % 2 else i

/-- A probe-window map changes only bounded indices; arbitrary out-of-window binary data
keeps its original width. -/
theorem size_boundaryIndexMap_le (M N : ℕ) (shift : ℕ → ℕ) (h : ∀ j, shift j < N)
    (v : ℕ) : (boundaryIndexMap M N shift v).size ≤
      max v.size (2 * (M + N)).size := by
  unfold boundaryIndexMap
  split_ifs
  · have hs := h (v / 2 - M)
    have hb := Nat.mod_lt v (by decide : 0 < 2)
    exact (Nat.size_le_size (by omega)).trans (le_max_right _ _)
  · exact le_max_left _ _

/-- Execute one left boundary-word rotation's numeric table transport. The reversed probe
moves old argument slots forward by one; lookup uses the inverse shift. No validity check
or entry-bound premise is used. Short boundaries retain the exact original certificate. -/
@[expose] def rotateBoundaryCertificate (M N : ℕ) (c : Graph.RotationCertificate) :
    Graph.RotationCertificate :=
  if N ≤ 1 then c else
    Graph.RotationCertificate.reindex c (2 * (M + N))
      (boundaryIndexMap M N (fun j => (j + 1) % N))
      (boundaryIndexMap M N (fun j => (j + N - 1) % N))

private theorem blockMove_up_slot (M N : ℕ) (hN : 1 < N) (j : Fin N)
    (bit : ℕ) (hbit : bit < 2) :
    Nat.blockMove (2 * M) (2 * (N - 1)) 2 (2 * (M + j.val) + bit) =
      2 * (M + ((j.val + 1) % N)) + bit := by
  let k : Fin (2 * (N - 1) + 2) := ⟨2 * j.val + bit, by have := j.isLt; omega⟩
  have hindex : 2 * M + k.val = 2 * (M + j.val) + bit := by dsimp [k]; omega
  rw [← hindex, Nat.blockMove_eq_finAddFlip]
  by_cases hj : j.val + 1 = N
  · have hcut : 2 * (N - 1) ≤ k.val := by dsimp [k]; omega
    rw [finAddFlip_apply_mk_right hcut k.isLt]
    change 2 * M + (k.val - 2 * (N - 1)) =
      2 * (M + ((j.val + 1) % N)) + bit
    rw [hj, Nat.mod_self]
    dsimp [k]
    omega
  · have hcut : k.val < 2 * (N - 1) := by
      have := j.isLt
      dsimp [k]
      omega
    rw [finAddFlip_apply_mk_left hcut]
    change 2 * M + (2 + k.val) = 2 * (M + ((j.val + 1) % N)) + bit
    rw [Nat.mod_eq_of_lt (by have := j.isLt; omega)]
    dsimp [k]
    omega

private theorem blockMove_down_slot (M N : ℕ) (hN : 1 < N) (j : Fin N)
    (bit : ℕ) (hbit : bit < 2) :
    Nat.blockMove (2 * M) 2 (2 * (N - 1)) (2 * (M + j.val) + bit) =
      2 * (M + ((j.val + N - 1) % N)) + bit := by
  let k : Fin (2 + 2 * (N - 1)) := ⟨2 * j.val + bit, by have := j.isLt; omega⟩
  have hindex : 2 * M + k.val = 2 * (M + j.val) + bit := by dsimp [k]; omega
  rw [← hindex, Nat.blockMove_eq_finAddFlip]
  by_cases hj : j.val = 0
  · have hcut : k.val < 2 := by dsimp [k]; omega
    rw [finAddFlip_apply_mk_left hcut]
    change 2 * M + (2 * (N - 1) + k.val) =
      2 * (M + ((j.val + N - 1) % N)) + bit
    rw [hj, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    dsimp [k]
    omega
  · have hcut : 2 ≤ k.val := by dsimp [k]; omega
    rw [finAddFlip_apply_mk_right hcut k.isLt]
    change 2 * M + (k.val - 2) = 2 * (M + ((j.val + N - 1) % N)) + bit
    have he : j.val + N - 1 = N + (j.val - 1) := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (by have := j.isLt; omega)]
    dsimp [k]
    omega

private theorem blockMove_window (M N : ℕ) (hN : 1 < N) (i : ℕ) :
    Nat.blockMove (2 * M) (2 * (N - 1)) 2 i =
      boundaryIndexMap M N (fun j => (j + 1) % N) i ∧
    Nat.blockMove (2 * M) 2 (2 * (N - 1)) i =
      boundaryIndexMap M N (fun j => (j + N - 1) % N) i := by
  by_cases hw : 2 * M ≤ i ∧ i < 2 * (M + N)
  · let j : Fin N := ⟨i / 2 - M, by omega⟩
    let bit := i % 2
    have hb : bit < 2 := Nat.mod_lt _ (by decide)
    have he : 2 * (M + j.val) + bit = i := by
      have hd := Nat.mod_add_div i 2
      dsimp [j, bit]
      omega
    simp only [boundaryIndexMap, ite_eq_left hw]
    constructor
    · calc
        _ = Nat.blockMove (2 * M) (2 * (N - 1)) 2
            (2 * (M + j.val) + bit) := congrArg _ he.symm
        _ = _ := blockMove_up_slot M N hN j bit hb
    · calc
        _ = Nat.blockMove (2 * M) 2 (2 * (N - 1))
            (2 * (M + j.val) + bit) := congrArg _ he.symm
        _ = _ := blockMove_down_slot M N hN j bit hb
  · simp only [boundaryIndexMap, ite_eq_right hw]
    constructor <;> unfold Nat.blockMove <;> split_ifs <;> omega

/-- Execute one RIGHT boundary-word rotation by exchanging the first two-dart probe
block with the rest. The reciprocal block move supplies lookup. Short boundaries retain
all original data; missing lookups use the forward image of zero, not an assumed zero. -/
@[expose] def rotateBoundaryCertificateRight (M N : ℕ) (c : Graph.RotationCertificate) :
    Graph.RotationCertificate :=
  if N ≤ 1 then c else
    Graph.RotationCertificate.reindex c (2 * (M + N))
      (Nat.blockMove (2 * M) 2 (2 * (N - 1)))
      (Nat.blockMove (2 * M) (2 * (N - 1)) 2)

/-- The complete RIGHT program uses the same probe-window function as LEFT, with the
predecessor and successor interchanged. This equality holds for arbitrary raw tables. -/
theorem rotateBoundaryCertificateRight_eq_reindex_mod (M N : ℕ)
    (c : Graph.RotationCertificate) :
    rotateBoundaryCertificateRight M N c =
      if N ≤ 1 then c else
        Graph.RotationCertificate.reindex c (2 * (M + N))
          (boundaryIndexMap M N (fun j => (j + N - 1) % N))
          (boundaryIndexMap M N (fun j => (j + 1) % N)) := by
  unfold rotateBoundaryCertificateRight
  split_ifs with hshort
  · rfl
  · have hN : 1 < N := by omega
    have hu := funext fun i => (blockMove_window M N hN i).1
    have hd := funext fun i => (blockMove_window M N hN i).2
    rw [hu, hd]

end Cslib.Complexity.CSP.OrderedBoundary
