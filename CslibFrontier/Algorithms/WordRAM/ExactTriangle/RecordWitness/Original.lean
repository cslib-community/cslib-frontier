/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.Program
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.PreparationInput
import CslibFrontier.Foundations.Data.List.GetD

/-!
# Original signed arrays after real preparation

The producer's existing prefix frame retains every original signed input word. These internal
readback rules relate the recovery bank to those same words and to their original magnitude
bound; they do not assume intermediate signed fits or add a second input encoding.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM

/-- A preserved original payload supplies the three signed row-major weight arrays. -/
theorem original_matrices {n D g p : ℕ} (values : List ℤ) {mem : ℕ → ℕ}
    (hprefix : ∀ j < 5 + 3 * (n * n), mem j =
      (Data.init (PreparationInput.input n D g p values) : Data 64).mem j) :
    ∀ a < n, ∀ b < n,
      mem (5 + (a * n + b)) = Signed.encode (values.getD (a * n + b) 0) ∧
      mem (5 + n * n + (a * n + b)) = Signed.encode (values.getD (n * n + (a * n + b)) 0) ∧
      mem (5 + n * n + n * n + (a * n + b)) =
        Signed.encode (values.getD (2 * (n * n) + (a * n + b)) 0) := by
  intro a ha b hb
  have hcell : a * n + b < n * n := by
    simpa only [Nat.mul_comm] using Nat.mul_add_lt_mul_of_lt_of_lt ha hb
  have word (j : ℕ) (hj : j < 3 * (n * n)) :
      mem (5 + j) = Signed.encode (values.getD j 0) :=
    (hprefix _ (Nat.add_lt_add_left hj _)).trans (PreparationInput.input_word n D g p values j)
  exact ⟨word _ (by lia),
    by simpa only [Nat.add_assoc] using word (n * n + (a * n + b)) (by lia),
    by simpa only [Nat.add_assoc, two_mul] using word (2 * (n * n) + (a * n + b)) (by lia)⟩

/-- Original magnitude bounds supply every original array entry, not merely a fitting
intermediate machine state. The implicit index equation is the producer's existing layout. -/
theorem original_magnitude {n A q : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hq : q < 3 * (n * n)) : (values.getD q 0).natAbs ≤ A :=
  hv (values.getD q 0) (List.getD_mem 0 (by omega))

/-- One input magnitude bound applies to the entries of all three weight arrays. -/
theorem original_magnitudes {n A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A) :
    ∀ a < n, ∀ b < n,
      (values.getD (a * n + b) 0).natAbs ≤ A ∧
      (values.getD (n * n + (a * n + b)) 0).natAbs ≤ A ∧
      (values.getD (2 * (n * n) + (a * n + b)) 0).natAbs ≤ A := by
  intro a ha b hb
  have hcell : a * n + b < n * n := by
    simpa only [Nat.mul_comm] using Nat.mul_add_lt_mul_of_lt_of_lt ha hb
  exact ⟨original_magnitude values hlen hv (by lia), original_magnitude values hlen hv (by lia),
    original_magnitude values hlen hv (by lia)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
