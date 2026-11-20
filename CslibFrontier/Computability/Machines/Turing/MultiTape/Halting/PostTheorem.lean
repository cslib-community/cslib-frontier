/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.OraclePartrec
public import CslibFrontier.Foundations.Computability.PostTheorem

/-!
# Oracle machine bounds in the arithmetic hierarchy

A finite oracle machine has natural inputs represented in unary and asks membership
questions of a fixed set. Its halting set is relatively enumerable. If it computes a total
characteristic function, the set it decides is relatively computable. At the `k`th jump
these facts give the three upper bounds of Post's theorem. The machine-to-code simulation
preserves the exact convergence and output needed to apply the code characterization.

## Main definitions

* `Cslib.Computability.EnumerableByOracleTM`: relative enumerability by a finite oracle machine.
* `Cslib.Computability.DecidableByOracleTM`: relative decision by a finite oracle machine.

## Main results

* `Cslib.Computability.EnumerableByOracleTM.mem_arithmeticSigma` and
  `Cslib.Computability.EnumerableByOracleTM.mem_arithmeticPi_compl`: the bounds for
  machine halting and divergence sets.
* `Cslib.Computability.DecidableByOracleTM.mem_arithmeticDelta`: the bound for sets
  decided by a total machine.
-/

public section

namespace Cslib.Computability

open Turing.MultiTapeTM.Universal

/-- Set membership in the Boolean interface of a finite oracle machine. -/
@[expose] noncomputable def membershipOracleBool (B : Set ℕ) (n : ℕ) : Bool :=
  membershipOracle B n != 0

private theorem part_membershipOracleBool (B : Set ℕ) :
    (fun n => Part.some (membershipOracleBool B n).toNat) = (membershipOracle B : ℕ →. ℕ) := by
  funext n
  classical
  by_cases hn : n ∈ B <;> simp [membershipOracleBool, membershipOracle, hn]

/-- A set is enumerable by a finite membership-oracle machine if it is the halting set
on unary inputs. The output is unrestricted. -/
@[expose] def EnumerableByOracleTM (A B : Set ℕ) : Prop :=
  ∃ M : OracleDesc, ∀ n, n ∈ A ↔
    ∃ t, (M.runFor (membershipOracleBool B) (List.replicate n 1) t).ordinary.state = none

/-- A set is decidable by a finite membership-oracle machine if it halts on every unary
input and returns the characteristic value as the length of its output. -/
@[expose] def DecidableByOracleTM (A B : Set ℕ) : Prop :=
  ∃ M : OracleDesc, M.evalUnary (membershipOracleBool B) = (membershipOracle A : ℕ →. ℕ)

variable {A B : Set ℕ}

private theorem recursiveIn_oracleTM (M : OracleDesc) (B : Set ℕ) :
    Nat.RecursiveIn {(membershipOracle B : ℕ →. ℕ)} (M.evalUnary (membershipOracleBool B)) := by
  rw [← part_membershipOracleBool]
  exact M.recursiveIn_evalUnary (membershipOracleBool B)

/-- Finite-machine halting yields a relative enumeration in the oracle-code model. -/
theorem EnumerableByOracleTM.enumerableIn (h : EnumerableByOracleTM A B) : EnumerableIn A B := by
  obtain ⟨M, hM⟩ := h
  obtain ⟨c, hc⟩ := Nat.RecursiveIn.Code.exists_code.mp (recursiveIn_oracleTM M B)
  refine ⟨c, fun n => ?_⟩
  rw [hc]
  change _ ↔ (M.eval (membershipOracleBool B) (List.replicate n 1)).Dom
  rw [hM, Part.dom_iff_mem]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨_, (M.mem_eval_iff _ _ _).mpr ⟨t, ht, rfl⟩⟩
  · rintro ⟨out, hout⟩
    obtain ⟨t, ht, _⟩ := (M.mem_eval_iff _ _ out).mp hout
    exact ⟨t, ht⟩

/-- A total characteristic output gives a relative decision in the oracle-code model. -/
theorem DecidableByOracleTM.decidableIn (h : DecidableByOracleTM A B) : DecidableIn A B := by
  obtain ⟨M, hM⟩ := h
  rw [DecidableIn, ← hM]
  exact recursiveIn_oracleTM M B

/-- Halting relative to the kth jump gives an existential formula at level k + 1. -/
theorem EnumerableByOracleTM.mem_arithmeticSigma {k : ℕ}
    (h : EnumerableByOracleTM A (iteratedJump k)) : A ∈ ArithmeticSigma (k + 1) :=
  mem_arithmeticSigma_succ_iff.mpr h.enumerableIn

/-- Divergence relative to the kth jump gives a universal formula at level k + 1. -/
theorem EnumerableByOracleTM.mem_arithmeticPi_compl {k : ℕ}
    (h : EnumerableByOracleTM A (iteratedJump k)) : Aᶜ ∈ ArithmeticPi (k + 1) :=
  mem_arithmeticPi_succ_iff.mpr (by simpa using h.enumerableIn)

/-- A decision relative to the kth jump gives both formulas at level k + 1. -/
theorem DecidableByOracleTM.mem_arithmeticDelta {k : ℕ}
    (h : DecidableByOracleTM A (iteratedJump k)) : A ∈ ArithmeticDelta (k + 1) :=
  mem_arithmeticDelta_succ_iff.mpr h.decidableIn

end Cslib.Computability
