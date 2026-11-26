/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.WitnessScan.Exec
public import CslibFrontier.Algorithms.ExactTriangle.PieceBounds
public import CslibFrontier.Algorithms.ExactTriangle.Witnesses

/-!
# Native interval failure and existing finite witness scans

The actual verifier reports the last zero it reads, whereas `scanPiece` returns the first.
Their failure conditions agree: both exhaust precisely the original vertices in the existing
finite piece. This value lemma connects native failure accounting to the existing finite
false-positive theory without identifying the two witness-order conventions.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan

open Cslib.Algorithms.ExactTriangle

/-- Native interval exhaustion is exactly failure of the existing finite piece scan. The
array equations describe the same original integer weights; no witness routine is assumed. -/
theorem fails_iff_scanPiece_eq_none {n D g k : ℕ}
    (AB BC AC : ℕ → ℕ → ℤ) (wAB wBC wAC : Fin n → Fin n → ℤ)
    (hD : 16 ≤ D) (hg : 1 ≤ g)
    (hAB : ∀ u v : Fin n, AB u.val v.val = wAB u v)
    (hBC : ∀ u v : Fin n, BC u.val v.val = wBC u v)
    (hAC : ∀ u v : Fin n, AC u.val v.val = wAC u v)
    (a b : Fin n) :
    let first := k * pieceSize D g
    let length := min (pieceSize D g) (n - first)
    (∀ c : Fin length, AB a.val b.val + BC b.val (first + c.val) +
      AC a.val (first + c.val) ≠ 0) ↔ scanPiece wAB wBC wAC D g k a b = none := by
  let first := k * pieceSize D g
  let length := min (pieceSize D g) (n - first)
  have heq (c : Fin n) : AB a.val b.val + BC b.val c.val + AC a.val c.val =
      weightSum wAB wBC wAC a b c := by rw [hAB, hBC, hAC]; rfl
  rw [scanPiece_eq_none_iff]
  constructor
  · intro hfail c hc
    have hinterval : first ≤ c.val ∧ c.val < first + length :=
      (mem_piece_iff_interval hD hg c).mp hc
    simpa only [show k * pieceSize D g + (c.val - first) = c.val by omega, heq] using
      hfail ⟨c.val - first, by omega⟩
  · intro hfail j
    have hj : j.val < length := j.isLt
    have hl := min_le_right (pieceSize D g) (n - first)
    let c : Fin n := ⟨first + j.val, by omega⟩
    simpa only [← heq c] using hfail c ((mem_piece_iff_interval hD hg c).mpr
      ⟨Nat.le_add_right _ _, Nat.add_lt_add_left j.isLt _⟩)

end Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan
