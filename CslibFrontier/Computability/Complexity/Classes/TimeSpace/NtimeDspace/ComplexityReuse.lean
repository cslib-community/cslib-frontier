/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine

/-!
Pointwise interfaces for reusing the pinned query-machine compiler and its
configuration-counting argument. The budget may depend on the actual encoded
input, rather than only its length. The query bridge requires explicit
callback-space certificates and bounds on every reachable encoded state;
it supplies none of those obligations for the counting algorithm.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.ComplexityReuse

open _root_.Turing _root_.Turing.MultiTapeTM

/-- A coefficient absorbing both configuration-count constants and the
original multiplicative workspace coefficient. -/
def exponentialCoefficient (configuration space : ℕ) : ℕ :=
  configuration * space + configuration + space + 2

theorem coefficient_pos (configuration space : ℕ) :
    0 < exponentialCoefficient configuration space := by
  unfold exponentialCoefficient
  omega

theorem space_coefficient_le (configuration space budget : ℕ) :
    space * budget ≤ exponentialCoefficient configuration space * budget := by
  apply Nat.mul_le_mul_right
  unfold exponentialCoefficient
  omega

/-- Absorb the input-head factor and finite machine constants into an
exponential in an arbitrary pointwise workspace budget. -/
theorem configuration_time_le_exp (inputLength budget configuration space : ℕ)
    (logarithmic : inputLength.log2 + 1 ≤ budget) :
    (inputLength + 2) * configuration * 2 ^ (configuration * (space * budget)) ≤
      2 ^ (exponentialCoefficient configuration space * budget) := by
  have budget_positive : 1 ≤ budget := by omega
  have input_bound : inputLength < 2 ^ budget :=
    Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by decide) logarithmic)
  have input_factor : inputLength + 2 ≤ 2 ^ (2 * budget) := by
    have next : inputLength + 2 ≤ 2 ^ (budget + 1) := by
      rw [pow_succ]
      have positive := Nat.two_pow_pos budget
      omega
    exact next.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have constant_factor : configuration ≤ 2 ^ (configuration * budget) :=
    (Nat.lt_two_pow_self (n := configuration)).le.trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ budget_positive))
  calc
    _ ≤ 2 ^ (2 * budget) * 2 ^ (configuration * budget) *
        2 ^ (configuration * (space * budget)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul input_factor constant_factor)
    _ = 2 ^ (2 * budget + configuration * budget + configuration * (space * budget)) := by
      rw [← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      unfold exponentialCoefficient
      nlinarith)

/-- The readable-configuration argument applies pointwise to any input-indexed
space function. No factorization through encoded input length is required. -/
theorem exists_configuration_time {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {time space : α → ℕ}
    (computes : ComputableInTimeAndSpace f encIn encOut time space) :
    ∃ c, ComputableInTimeAndSpace f encIn encOut
      (fun a => ((encIn a).length + 2) * c * 2 ^ (c * space a)) space := by
  obtain ⟨k, State, finiteState, tm, correct⟩ := computes
  let := Fintype.ofFinite State
  let c := storageBoundBase Bool State k + storageBoundExp Bool k
  have counted : tm.ComputesFunInTimeAndSpace encIn encOut f
      (fun a => ((encIn a).length + 2) * storageBound Bool State k (space a)) space :=
    fun a => (correct a).of_card
  refine ⟨c, k, State, finiteState, tm, counted.mono (fun a => ?_) (fun _ => le_rfl)⟩
  rw [mul_assoc]
  refine Nat.mul_le_mul_left _ ((storageBound_le_base_mul_pow _).trans
    (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))))

/-- Simultaneous time and space with one constant, allowing the budget to vary
with each actual input. The originally supplied time function is discarded by
configuration counting, while the same halting machine and output are kept. -/
theorem exists_exponential_time_of_linear_space {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {time budget : α → ℕ}
    (coefficient : ℕ)
    (computes : ComputableInTimeAndSpace f encIn encOut time (fun a => coefficient * budget a))
    (logarithmic : ∀ a, (encIn a).length.log2 + 1 ≤ budget a) :
    ∃ C, ComputableInTimeAndSpace f encIn encOut
      (fun a => 2 ^ (C * budget a)) (fun a => C * budget a) := by
  obtain ⟨c, counted⟩ := exists_configuration_time computes
  refine ⟨exponentialCoefficient c coefficient, counted.mono (fun a => ?_) (fun a => ?_)⟩
  · exact configuration_time_le_exp _ _ c coefficient (logarithmic a)
  · exact space_coefficient_le c coefficient (budget a)

/-- A reusable compiler bridge: all five callback certificates, first-halting
and output identities, and the run-wide state-encoding bound remain explicit.
This theorem does not certify any particular counting-machine callbacks. -/
theorem query_simultaneous_bounds {α β : Type} {enc : α ↪ List Bool}
    {encOut : β ↪ List Bool} {σ : Type} {encState : σ ↪ List Bool}
    (M : QueryMachine σ)
    (querySpace : ComputableInSpace M.query encState encNat (fun state => (encState state).length))
    (nextSpace : ComputableInSpace M.next (encPair encState (encOption encBool)) encState
      (fun state => (encPair encState (encOption encBool) state).length))
    (emitSpace : ComputableInSpace M.emit (encPair encState (encOption encBool)) encBits
      (fun state => (encPair encState (encOption encBool) state).length))
    (haltSpace : ComputableInSpace M.halted encState encBool (fun state => (encState state).length))
    (finishSpace : ComputableInSpace M.finish encState encBits
        (fun state => (encState state).length))
    {f : α → β} (time : α → ℕ)
    (halts : ∀ a, M.halted (M.run (enc a) (time a)) = true)
    (firstHalt : ∀ a, ∀ t < time a, M.halted (M.run (enc a) t) = false)
    (output : ∀ a, encOut (f a) = M.output (enc a) (time a))
    (budget : α → ℕ) (logarithmic : ∀ a, (enc a).length.log2 + 1 ≤ budget a)
    (stateBound : ∃ c, ∀ a, ∀ t ≤ time a, (encState (M.run (enc a) t)).length ≤ c * budget a) :
    ∃ C, ComputableInTimeAndSpace f enc encOut
      (fun a => 2 ^ (C * budget a)) (fun a => C * budget a) := by
  obtain ⟨compiledTime, coefficient, compiled⟩ :=
    M.computableInSpace querySpace nextSpace emitSpace haltSpace finishSpace time
      halts firstHalt output budget logarithmic stateBound
  exact exists_exponential_time_of_linear_space coefficient compiled logarithmic

/-- The imported hierarchy theorem makes the eventual separation consequence
short, but the essential nondeterministic simulation and strictly sublinear
space gap are hypotheses here, not conclusions of the counting development. -/
theorem conditional_linear_separation {space : ℕ → ℕ}
    (simulation : Cslib.Complexity.NTIME encBits (fun n => n) ⊆
      Cslib.Complexity.DSPACE encBits space)
    (strictGap : ∀ c, ∀ᶠ n in Filter.atTop, c * space n + c ≤ n) :
    Cslib.Complexity.NTIME encBits (fun n => n) ⊂
      Cslib.Complexity.DSPACE encBits (fun n => n) := by
  exact lt_of_le_of_lt simulation
    (Cslib.Complexity.DSPACE_ssubset_DSPACE Cslib.Complexity.spaceConstructible_id
      (fun n => Nat.log2_le_self n) strictGap)

end Cslib.Complexity.NtimeDspace.ComplexityReuse
