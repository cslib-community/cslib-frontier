/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Complexity.Classes.Oracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.RunsWords
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Tidy
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.SuccPow

public import CslibFrontier.Computability.Complexity.Classes.Oracle.Exponential.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.Oracle.Normalization

/-! # Internal halting-clock enlargement for exponential oracle time

These machine proofs preserve the explicit exponential preparation charge and the complete
joint stateful-oracle law. The numerical exponential-time contract is defined separately.
-/

public section

namespace Cslib.Probability

open _root_.Turing.MultiTapePTM.Internal.Oracle

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

namespace IsOracleExpTimeOn

variable {Operation α β : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {output : β ↪ List Bool}

/-- A machine computing the encoded program as a clean phase within time `c * 2 ^ (d * n)` is a
certificate. -/
private theorem of_computesTidily [Finite Operation] {k : ℕ} {Control : Type} [Finite Control]
    {program : α → WordOracleComp Operation β}
    (machine : Turing.MultiTapePTM k Bool Control Operation) (c d : ℕ) {time : α → ℕ}
    (htime : ∀ a, time a ≤ c * 2 ^ (d * (input a).length))
    (h : ∀ a, machine.ComputesTidily (input a) (time a) (output <$> program a)) :
    IsOracleExpTimeOn input output program :=
  ⟨inferInstance, k, Control, inferInstance, machine, c, d, fun a _ oracle s =>
    (((h a).mono (htime a)).runOracle oracle s).symm⟩

end IsOracleExpTimeOn

variable {Operation α β γ : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}

/-- **A polynomial clock is an exponential clock.** The clean realization of a strict oracle PPT
certificate keeps its result once it halts, so its polynomial clock can be raised to
`c * 2 ^ (d * n)`. -/
theorem IsOraclePPTOn.isOracleExpTimeOn {program : α → WordOracleComp Operation γ}
    (h : IsOraclePPTOn input output program) : IsOracleExpTimeOn input output program := by
  obtain ⟨hops, k, Control, hfinite, machine, c, d, hmachine⟩ := h.oraclePhase
  exact IsOracleExpTimeOn.of_computesTidily machine c d
    (fun a => Nat.mul_le_mul_left c (Nat.succ_pow_le_two_pow_mul _ d)) hmachine

/-- Arithmetic for `preprocess_exp`: the two phases and the charged intermediate word fit in one
exponential clock. -/
private theorem preprocess_exp_bound (C c₂ d₂ X : ℕ) (hX : 1 ≤ X) :
    5 * (C * (X + 1)) + c₂ * (C * (X + 1) + 1) ^ d₂ + 9 ≤
      (5 * (2 * C) + c₂ * (2 * C + 1) ^ d₂ + 9) * X ^ (d₂ + 1) := by
  have hX1 : X ≤ X ^ (d₂ + 1) := Nat.le_self_pow (by omega) X
  have hXd : X ^ d₂ ≤ X ^ (d₂ + 1) := Nat.pow_le_pow_right hX (by omega)
  have h1 : 1 ≤ X ^ (d₂ + 1) := Nat.one_le_pow _ _ hX
  have hpow : (C * (X + 1) + 1) ^ d₂ ≤ (2 * C + 1) ^ d₂ * X ^ (d₂ + 1) := by
    calc (C * (X + 1) + 1) ^ d₂ ≤ ((2 * C + 1) * X) ^ d₂ :=
          Nat.pow_le_pow_left (by nlinarith) d₂
      _ = (2 * C + 1) ^ d₂ * X ^ d₂ := Nat.mul_pow _ _ _
      _ ≤ (2 * C + 1) ^ d₂ * X ^ (d₂ + 1) := Nat.mul_le_mul_left _ hXd
  have hlin : 5 * (C * (X + 1)) ≤ 5 * (2 * C) * X ^ (d₂ + 1) := by
    nlinarith [Nat.mul_le_mul_left (2 * C) hX1]
  have hc : c₂ * (C * (X + 1) + 1) ^ d₂ ≤ c₂ * (2 * C + 1) ^ d₂ * X ^ (d₂ + 1) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hpow
  nlinarith

/-- **Exponential-time preparation, then a strict oracle PPT program.** If `prepare` is
computable within time `O(2 ^ (d * n))` and `program` is strict oracle PPT on the prepared
instances, the composite is realized within time `2 ^ O(n)`. The prepared word may be
exponentially long; the polynomial clock of `program` is then exponential in `n`. -/
theorem IsOraclePPTOn.preprocess_exp {program : β → WordOracleComp Operation γ}
    {prepare : α → β} {S : α → ℕ} {d : ℕ}
    (hprogram : IsOraclePPTOn middle output program)
    (hprepare : ComputableInO prepare input middle (fun a => 2 ^ (d * (input a).length)) S) :
    IsOracleExpTimeOn input output (fun a => program (prepare a)) := by
  classical
  obtain ⟨hops, k₂, Control₂, hfinite₂, target, c₂, d₂, htarget⟩ := hprogram.oraclePhase
  obtain ⟨C, ⟨k₁, State₁, hfinite₁, tm, htm⟩, -⟩ := Internal.NormalForm.inO hprepare
  let source : MultiTapePTM k₁ Bool State₁ Operation := ofDeterministic tm
  let firstTime : α → ℕ := fun a => C * (2 ^ (d * (input a).length) + 1)
  have hsource (a : α) : source.ComputesTidily (input a) (firstTime a)
      (pure (middle (prepare a))) :=
    ComputesTidily.of_deterministic (htm a)
  let continuation : List Bool → WordOracleComp Operation (List Bool) :=
    Function.extend middle (fun b => output <$> program b) (fun _ => pure [])
  have hcontinuation (b : β) : continuation (middle b) = output <$> program b :=
    middle.injective.extend_apply _ _ b
  refine IsOracleExpTimeOn.of_computesTidily (target.tidyComp source true)
    (5 * (2 * C) + c₂ * (2 * C + 1) ^ d₂ + 9) (d * (d₂ + 1))
    (time := fun a => 5 * firstTime a + c₂ * (firstTime a + 1) ^ d₂ + 9)
    (fun a => ?_) (fun a => ?_)
  · refine (preprocess_exp_bound C c₂ d₂ _
      (Nat.one_le_two_pow (n := d * (input a).length))).trans (le_of_eq ?_)
    rw [← Nat.pow_mul]
    congr 2
    ring
  · have hcomp := (hsource a).comp true (prog₂ := continuation)
      (t₂ := c₂ * (firstTime a + 1) ^ d₂)
      (fun word State oracle s s' hword => by
        have hlen := (hsource a).length_output_le oracle s hword
        simp only [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hword
        obtain ⟨rfl, -⟩ := hword
        rw [hcontinuation]
        exact (htarget (prepare a)).mono (Nat.mul_le_mul_left c₂
          (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) d₂)))
    simpa only [pure_bind, hcontinuation] using hcomp

end Cslib.Probability
