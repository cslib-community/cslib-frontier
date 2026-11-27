/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.OraclePartrec

/-!
# Basic finite oracle programs

An ordinary finite transition table embeds into the oracle model by keeping its
actions and leaving the query tape untouched. The membership program scans a
tally input, copies its length onto the query tape, and returns the oracle answer
as a unary natural number.

## Main results

* `Turing.MultiTapeTM.Universal.Desc.runFor_toOracle`: lifting an ordinary table preserves each
  configuration and its output.
* `Turing.MultiTapeTM.Universal.Desc.mem_eval_toOracle_iff`: the lift preserves halting with
  the exact output word.
* `Turing.MultiTapeTM.Universal.OracleDesc.evalUnary_unaryQuery`: the native membership
  instruction computes the same partial function as the oracle code.
-/

public section

namespace Turing.MultiTapeTM.Universal

/-- Regard an ordinary finite transition table as an oracle table that never queries. -/
@[expose] def Desc.toOracle (d : Desc) : OracleDesc where
  tapes := d.tapes
  initial := d.q₀
  table := d.table.map fun (key, a) => (key, .step a false)

private theorem Desc.step_toOracle (d : Desc) (oracle : ℕ → Bool) (x : List ℕ)
    (c : SCfg × List ℕ) :
    d.toOracle.step oracle x ⟨c.1, 0, c.2⟩ =
      ⟨(stepOut d x c).1, 0, (stepOut d x c).2⟩ := by
  rcases c with ⟨c, out⟩
  cases h : c.state with
  | none => simp [OracleDesc.step, OracleDesc.stepWith, stepOut, step, h]
  | some q =>
    simp only [OracleDesc.step, OracleDesc.stepWith, Desc.toOracle, h, List.find?_map,
      Function.comp_def, stepOut, step]
    cases d.table.find? (·.1 = c.key x q) with
    | none => simp
    | some a => simp [OracleDesc.Config.applyInstruction]

/-- Lifting a finite table preserves its configuration and output at every time. -/
theorem Desc.runFor_toOracle (d : Desc) (oracle : ℕ → Bool) (x : List ℕ) (t : ℕ) :
    d.toOracle.runFor oracle x t =
      let c := (stepOut d x)^[t] (init d, [])
      ⟨c.1, 0, c.2⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [OracleDesc.runFor, Function.iterate_succ_apply', ← OracleDesc.runFor, ih,
      Function.iterate_succ_apply']
    exact d.step_toOracle oracle x _

/-- The lifted table returns exactly a word produced by a halted ordinary run. -/
theorem Desc.mem_eval_toOracle_iff (d : Desc) (oracle : ℕ → Bool) (x out : List ℕ) :
    out ∈ d.toOracle.eval oracle x ↔ ∃ t, simulate d x t = (out, true) := by
  rw [OracleDesc.mem_eval_iff]
  apply exists_congr
  intro t
  simp only [d.runFor_toOracle, simulate, Prod.mk.injEq, Option.isNone_iff_eq_none, and_comm]

namespace OracleDesc

/-- Copy a unary natural-number input to the query tape, ask membership, and emit one tally
on a yes answer. The no answer emits the empty word. -/
@[expose] def unaryQuery : OracleDesc where
  tapes := 0
  initial := 0
  table :=
    [(⟨0, some 1, []⟩, .step ⟨.pos, [], none, some 0⟩ true),
     (⟨0, none, []⟩, .query 1 2),
     (⟨1, none, []⟩, .step ⟨.zero, [], some 1, none⟩ false),
     (⟨2, none, []⟩, .step ⟨.zero, [], none, none⟩ false)]

private theorem runFor_unaryQuery_scan (oracle : ℕ → Bool) {n t : ℕ} (ht : t ≤ n) :
    unaryQuery.runFor oracle (List.replicate n 1) t =
      ⟨⟨some 0, t + 1, []⟩, t, []⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hin : inputSymbol (List.replicate n 1) (t + 1) = some 1 := by
      simp [inputSymbol, List.drop_replicate, List.head?_replicate, show n - t ≠ 0 by omega]
    rw [runFor, Function.iterate_succ_apply', ← runFor, ih (by omega)]
    simp [unaryQuery, step, stepWith, SCfg.key, Config.applyInstruction, Act.apply, moveInput,
      applyTapes, hin]

/-- The membership program returns the whole unary output, including the empty no word. -/
theorem eval_unaryQuery (oracle : ℕ → Bool) (n : ℕ) :
    unaryQuery.eval oracle (List.replicate n 1) =
      Part.some (if oracle n then [1] else []) := by
  apply Part.eq_some_iff.mpr
  apply (unaryQuery.mem_eval_iff _ _ _).mpr
  refine ⟨n + 2, ?_⟩
  have hin : inputSymbol (List.replicate n 1) (n + 1) = none := by
    simp [inputSymbol, List.drop_replicate]
  rw [runFor, show n + 2 = 2 + n by omega, Function.iterate_add_apply, ← runFor,
    runFor_unaryQuery_scan oracle (Nat.le_refl n)]
  cases ha : oracle n <;>
    simp [unaryQuery, step, stepWith, SCfg.key, Config.applyInstruction, Act.apply, moveInput,
      hin, ha, Function.iterate_succ_apply']

/-- Compiling the oracle opcode to the native model agrees with evaluation of the recursive
code on all total membership oracles and all tally inputs. -/
theorem evalUnary_unaryQuery (oracle : ℕ → Bool) (n : ℕ) :
    unaryQuery.evalUnary oracle n =
      Nat.RecursiveIn.Code.oracle.eval (fun k => Part.some (oracle k).toNat) n := by
  simp only [evalUnary, eval_unaryQuery, Part.map_some, Nat.RecursiveIn.Code.eval]
  cases oracle n <;> rfl

end OracleDesc

end Turing.MultiTapeTM.Universal
