/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.ExactTriangle.Splitting

/-!
# Numeric coordinates of ExactTriangle pieces

These bounds connect the existing finite pieces with the truncated original-vertex intervals
used by both native matrix preparation and witness recovery. They expose the same coordinate
facts previously private to the prepared-adjacency consumer, without changing the finite pieces.
-/

public section

namespace Cslib.Algorithms.ExactTriangle

/-- Every enumerated piece begins at an original vertex, before the truncation endpoint. -/
theorem piece_start_lt {n D g k : ℕ} (hD : 16 ≤ D) (hg : 1 ≤ g)
    (hk : k < numPieces n D g) : k * pieceSize D g < n := by
  by_contra hh
  have hc : numPieces n D g ≤ k := (Nat.ceilDiv_le_iff (pieceSize_pos hD hg)).mpr (by omega)
  omega

/-- The active piece/label rectangle fits in the source middle dimension. -/
theorem pieceLength_mul_le_of_mem_sqrtPrimeWindow {D g p n k : ℕ} (hg : 1 ≤ g)
    (hp : p ∈ Nat.sqrtPrimeWindow D) :
    min (pieceSize D g) (n - k * pieceSize D g) * p ≤ D :=
  (Nat.mul_le_mul ((min_le_left _ _).trans (pieceSize_le_sOf hg))
    (Nat.le_sqrt'.mpr (Nat.mem_sqrtPrimeWindow_iff_sq.mp hp).2.2.le)).trans (Nat.sqrt_le D)

/-- An original piece vertex has its computed local coordinate in the actual truncated interval. -/
theorem piece_coordinate {n D g k : ℕ} (hD : 16 ≤ D) (hg : 1 ≤ g)
    (c : Fin n) (hc : c ∈ piece n D g k) :
    k * pieceSize D g + c.val % pieceSize D g = c.val ∧
      c.val % pieceSize D g < min (pieceSize D g) (n - k * pieceSize D g) := by
  have hsplit := (mem_piece c).mp hc ▸ Nat.mul_comm (pieceSize D g) (c.val / pieceSize D g) ▸
    Nat.div_add_mod c.val (pieceSize D g)
  exact ⟨hsplit, lt_min (Nat.mod_lt _ (pieceSize_pos hD hg)) (by omega)⟩

/-- The finite piece is precisely its original-coordinate truncated interval. -/
theorem mem_piece_iff_interval {n D g k : ℕ} (hD : 16 ≤ D) (hg : 1 ≤ g) (c : Fin n) :
    c ∈ piece n D g k ↔ k * pieceSize D g ≤ c.val ∧
      c.val < k * pieceSize D g + min (pieceSize D g) (n - k * pieceSize D g) := by
  refine ⟨fun hc => ?_, fun ⟨hlo, hhi⟩ => ?_⟩
  · obtain ⟨_, _⟩ := piece_coordinate hD hg c hc
    omega
  · have he : c.val = pieceSize D g * k + (c.val - k * pieceSize D g) := by
      rw [Nat.mul_comm]
      omega
    rw [mem_piece, he, Nat.mul_add_div (pieceSize_pos hD hg), Nat.div_eq_of_lt (by omega),
      Nat.add_zero]

end Cslib.Algorithms.ExactTriangle
