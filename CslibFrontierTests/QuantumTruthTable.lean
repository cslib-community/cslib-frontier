/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Classes.BQP.TruthTable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Checked quantum truth-table computations -/

set_option linter.privateModule false

namespace CslibFrontierTests.QuantumTruthTable

open Cslib.Quantum Cslib.Complexity Turing.MultiTapeTM

private def singletonOracle : Set (List Bool) := {w | w = [true]}

private instance : DecidablePred (· ∈ singletonOracle) :=
  fun w => inferInstanceAs (Decidable (w = [true]))

private abbrev twoQueries : TruthTableCircuitDescription :=
  ⟨6, 2, 3, 7, [], []⟩

/-- The same layer queries the empty word and the one-bit word from two disjoint blocks. -/
example :
    let z := inputState 6 [false, false, false, true, true, false]
    (twoQueries.queryLayer (by decide) singletonOracle).eval (ket (Fin.append z (fun _ => false))) =
      ket (Fin.append z (fun i : Fin 2 => i == 1)) := by
  dsimp only
  rw [TruthTableCircuitDescription.queryLayer_eval_ket]
  congr 2
  funext i
  fin_cases i <;> decide

private abbrev emptyQuery (n k : ℕ) : TruthTableCircuitDescription :=
  let width := 2 * n + 1 + k
  ⟨width, 1, 0, width, [], []⟩

private abbrev uniformEmptyQuery : UniformTruthTableCircuitFamily where
  description := emptyQuery
  computableInPolyTime_description := by
    unfold emptyQuery
    fun_prop
  wellFormed n k := by
    refine ⟨le_rfl, Nat.zero_le _, Nat.lt_succ_self _, ?_, ?_⟩ <;> simp

private def emptyOracle : Set (List Bool) := {w | w = []}

private instance : DecidablePred (· ∈ emptyOracle) :=
  fun w => inferInstanceAs (Decidable (w = []))

private theorem uniformEmptyQuery_accepts (x a : List Bool) :
    uniformEmptyQuery.acceptProb emptyOracle x a = 1 := by
  rw [UniformTruthTableCircuitFamily.acceptProb, TruthTableCircuitDescription.acceptProb,
    TruthTableCircuitDescription.run]
  dsimp only [emptyQuery, uniformEmptyQuery]
  simp only [Circuit.ofPhaseCodes, List.filterMap_nil, Circuit.eval_nil, Circuit.run,
    embedState_ket]
  let n := 2 * x.length + 1 + a.length
  let z := inputState n (encPair encBits encBits (x, a))
  have hglue :
      glue (Fin.castLEEmb (Nat.le_add_right n 1)) z (fun _ => false) =
        Fin.append z (fun _ : Fin 1 => false) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      exact glue_apply_emb (Fin.castLEEmb (Nat.le_add_right n 1)) z (fun _ => false) j
    · rw [glue_of_not, Fin.append_right]
      intro q hq
      have h := congrArg Fin.val hq
      change q.val = n + j.val at h
      exact (Nat.not_le_of_lt q.isLt) (h ▸ Nat.le_add_right n j.val)
  rw [hglue, TruthTableCircuitDescription.queryLayer_eval_ket, measureProb_ket]
  have hout :
      (Fin.append z ((fun _ : Fin 1 => false) +
        fun i => decide ((emptyQuery x.length a.length).queryWord (by simp) z i ∈ emptyOracle)))
        (Fin.natAdd n (0 : Fin 1)) = true := by
    rw [Fin.append_right]
    change false + decide (([] : List Bool) ∈ emptyOracle) = true
    decide
  apply ite_eq_left
  simp only [onesAt, Finset.mem_filter, Finset.mem_univ, List.mem_singleton, true_and,
    forall_eq]
  exact ⟨by omega, hout⟩

example : (Set.univ : Set (List Bool)) ∈ BQPTruthTablePoly encBits emptyOracle := by
  refine ⟨uniformEmptyQuery, fun _ => [], Cslib.polynomiallyBounded_iff_le.mpr ?_, ?_⟩
  · exact ⟨0, 0, fun _ => Nat.le_refl 0⟩
  · intro x
    norm_num [uniformEmptyQuery_accepts]

end CslibFrontierTests.QuantumTruthTable
