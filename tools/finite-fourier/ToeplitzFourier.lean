/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import PinnedFourier
import Mathlib.Order.Lattice.Nat
import CslibFrontier.Computability.Circuit.Linear.ToeplitzLowerBound

/-!
# Comparison with the published finite Fourier statement

The two program types have the same instructions but are defined in independent namespaces.
Translating all programs and readouts preserves their gate count and matrix, so both models
assign the same complexity to every matrix. The positive- and negative-character conventions
and the batching coordinates agree definitionally.
-/

namespace ToeplitzFourierCheck

open OAI.LinearAlgebra.FiniteFourier renaming Program → PublishedProgram,
  Readout → PublishedReadout, Circuit → PublishedCircuit, FourierBlock → PublishedBlock,
  complexity → publishedComplexity, batchMatrix → publishedBatch,
  RealizableAtMost → PublishedAtMost,
  BatchedFourierComplexityTheorem → PublishedBatchedFourierTheorem
open Cslib.Circuit.Linear
open Cslib.Circuit.ToeplitzLowerBound

variable {K I O W : Type*} {s : ℕ}

private def readouts : PublishedReadout K W ≃ Readout K W where
  toFun
    | .zero => .zero
    | .scaled c w => .scaled c w
  invFun
    | .zero => .zero
    | .scaled c w => .scaled c w
  left_inv z := by cases z <;> rfl
  right_inv z := by cases z <;> rfl

private def program : {s : ℕ} → PublishedProgram K I s → Program K I s
  | _, .nil => .nil
  | _, .step p g => .step (program p) ⟨g.left, g.right, g.leftCoeff, g.rightCoeff⟩

private theorem program_surjective : Function.Surjective (program (K := K) (I := I) (s := s)) := by
  intro p
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | step _ g ih =>
    obtain ⟨q, rfl⟩ := ih
    exact ⟨.step q ⟨g.left, g.right, g.leftCoeff, g.rightCoeff⟩, rfl⟩

private def circuit (c : PublishedCircuit K I O s) : LinearCircuit K I O s :=
  ⟨program c.program, fun o => readouts (c.output o)⟩

private theorem circuit_surjective : Function.Surjective (circuit (K := K) (I := I) (O := O)
    (s := s)) := by
  rintro ⟨p, out⟩
  obtain ⟨q, rfl⟩ := program_surjective p
  refine ⟨⟨q, fun o => readouts.symm (out o)⟩, ?_⟩
  simp only [circuit, Equiv.apply_symm_apply]

private theorem program_value [Semiring K] (p : PublishedProgram K I s) (x : I → K) :
    (program p).value x = p.value x := by
  induction p with
  | nil => rfl
  | step _ g ih =>
    simp only [program, Program.value, OAI.LinearAlgebra.FiniteFourier.Program.value, ih]
    rfl

private theorem circuit_matrix [Semiring K] (c : PublishedCircuit K I O s) :
    (circuit c).matrix = c.matrix := by
  classical
  have readout_eval (z : PublishedReadout K (I ⊕ Fin s)) (v : I ⊕ Fin s → K) :
      (readouts z).eval v = z.eval v := by cases z <;> rfl
  funext o i
  change (readouts (c.output o)).eval (Sum.elim _ ((program c.program).value _)) = _
  rw [program_value, readout_eval]
  rfl

private theorem complexity_eq [Semiring K] [Fintype I] [Fintype O] (M : Matrix O I K) :
    publishedComplexity M = complexity M := by
  classical
  rw [complexity, ← Nat.sInf_def (s := {s | RealizableAtMost M s})
    ⟨_, realizableAtMost_card_mul_card M⟩]
  apply congrArg sInf
  ext size
  change PublishedAtMost M size ↔ RealizableAtMost M size
  constructor
  · rintro ⟨s, hs, c, hc⟩
    exact ⟨s, hs, circuit c, (circuit_matrix c).trans hc⟩
  · rintro ⟨s, hs, c, hc⟩
    obtain ⟨p, rfl⟩ := circuit_surjective c
    exact ⟨s, hs, p, (circuit_matrix p).symm.trans hc⟩

private def publishedBlock [Field K] {n : ℕ} (B : FourierBlock K n) : PublishedBlock K n where
  G := B.G
  group := B.group
  finiteGroup := B.finiteGroup
  admissible := B.admissible
  points := B.points
  frequencies := B.frequencies
  inverse := B.inverse

private theorem batch_eq [Field K] {J n : ℕ} (B : Fin J → FourierBlock K n) :
    publishedBatch (fun j => publishedBlock (B j)) = batchMatrix B := rfl

/-- The published batched Fourier theorem implies the all-dimensions lower bound for
the frontier binary Toeplitz family. -/
theorem toeplitz_of_published (h : PublishedBatchedFourierTheorem.{0, 0}) :
    ∃ c > (0 : ℝ), ∀ᶠ m : ℕ in Filter.atTop,
      c * m * Real.sqrt (Real.logb 2 m) ≤ (complexity (binaryToeplitz m) : ℝ) := by
  obtain ⟨c, _, _, hc, _, _, hε⟩ := h
  obtain ⟨C, hC, hbatch⟩ := hε (1 / 2) (by norm_num)
  refine ⟨c / 36, by positivity, binaryToeplitz_size_of_fourierSizeBounds hc hC ?_⟩
  intro K _ J n B hJ hn
  have estimates := (hbatch K (fun j => publishedBlock (B j)) hJ hn).1
  rw [complexity_eq, batch_eq] at estimates
  norm_num at estimates ⊢
  exact estimates

/-- info: 'ToeplitzFourierCheck.toeplitz_of_published' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms toeplitz_of_published

end ToeplitzFourierCheck
