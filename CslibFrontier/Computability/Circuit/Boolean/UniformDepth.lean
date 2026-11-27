/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.DepthClasses
public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace

/-!
# Logspace-uniform Boolean circuit families

A logspace-uniform family has one deterministic transducer that, given the input length in unary,
writes the circuit for that length. We use the native serialization in program order, with binary
wire numbers. This is the generator convention for logspace uniformity
[Arora and Barak][AroraBarak09], Definition 6.14. The transducer's logarithmic workspace already
implies that every circuit it writes has polynomial size.

`LogspaceUniformAC` and `LogspaceUniformNC` use the same bases and depth bounds as `AC` and `NC`.
-/

public section

namespace Cslib.Circuits

open Turing.MultiTapeTM

variable {σ : Signature} {encOp : σ.Op ↪ List Bool}

/-- A single logarithmic-space machine writes the native circuit, with binary wire numbers, on
input the length in unary. The number of outputs is fixed throughout the family. -/
def Circuit.IsLogspaceUniform {m : ℕ} (encOp : σ.Op ↪ List Bool)
    (C : (n : ℕ) → Circuit σ n m) : Prop :=
  ComputableInLogSpace (fun n => (⟨n, C n⟩ : Σ n, Circuit σ n m)) encUnary
    (Circuit.encCircuit encOp m)

/-- A logspace-uniform family has polynomially many gates, since the generator's output is
polynomially long and each gate contributes to the encoded length. -/
theorem Circuit.IsLogspaceUniform.polynomiallyBounded_size {m : ℕ} {C : (n : ℕ) → Circuit σ n m}
    (h : Circuit.IsLogspaceUniform encOp C) : PolynomiallyBounded fun n => (C n).size := by
  obtain ⟨c, d, hlen⟩ := h.polyBounded_length.exists_le
  apply PolynomiallyBounded.of_forall_le c d
  intro n
  exact (Circuit.size_le_length_encCircuit encOp ⟨n, C n⟩).trans (by simpa using hlen n)

namespace Boolean

/-- Languages decided by logspace-uniform circuits over the given encoded basis and of depth at
most a constant multiple of `D n`. The transducer bound supplies polynomial size. -/
def LogspaceUniformDepthClass (I : Interpretation σ Bool) (encOp : σ.Op ↪ List Bool)
    (D : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (C : (n : ℕ) → Circuit σ n 1), Circuit.IsLogspaceUniform encOp C ∧ ∃ c, ∀ n,
    (C n).Computes I (single (L.slice n)) ∧ (C n).depth ≤ c * D n}

/-- Forgetting the generator gives a family with the same depth bound and polynomial size. -/
theorem LogspaceUniformDepthClass.subset_depthClass {I : Interpretation σ Bool} {D : ℕ → ℕ} :
    LogspaceUniformDepthClass I encOp D ⊆ DepthClass I D := by
  rintro L ⟨C, hC, c, h⟩
  exact ⟨c, _, hC.polynomiallyBounded_size, fun n => ⟨C n, (h n).1, (h n).2, le_rfl⟩⟩

/-- Logspace-uniform ACⁱ, with unbounded fan-in and depth `O((log n) ^ i)`. -/
def LogspaceUniformAC (i : ℕ) : Set (Language Bool) :=
  LogspaceUniformDepthClass Unbounded.interpretation Unbounded.encOp fun n =>
    (Nat.log 2 n + 1) ^ i

/-- Logspace-uniform NCⁱ, with the De Morgan basis of fan-in two and depth `O((log n) ^ i)`. -/
def LogspaceUniformNC (i : ℕ) : Set (Language Bool) :=
  LogspaceUniformDepthClass interpretation Boolean.encOp fun n => (Nat.log 2 n + 1) ^ i

end Boolean

end Cslib.Circuits
