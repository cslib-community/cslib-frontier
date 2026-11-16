/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Complexity.Classes.Alternation.Game

public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT
import CslibFrontier.Computability.Complexity.Classes.PH.Projection
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.List.OfFnGetD
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.List.FinRange

/-!
# Polynomial-hierarchy membership of grouped quantified SAT

Each quantifier block is padded to a common polynomial bound on the number of variables.
The verifier cuts the padding, computes the word assignment with shadowing, and runs the
existing quantifier-free Boolean-formula scan. Malformed prefixes and matrices are rejected.
-/

public section

namespace Cslib.Complexity.PrenexQBF

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime QuantifiedSAT

private theorem wellFormed_iff (i : ℕ) (a : PrenexQBF) :
    a.WellFormed i ↔ a.blocks.length = i ∧ a.matrix.QuantifierFree ∧
      (QBF.exs a.blocks.flatten a.matrix).Closed := by
  rw [QBF.Closed, QBF.freeVars_exs, Finset.sdiff_eq_empty_iff_subset]
  rfl

/-- Well-formedness of a grouped prenex instance is decidable in polynomial time. -/
theorem wellFormed_polyTime (i : ℕ) :
    ComputableInPolyTime (fun a : PrenexQBF => decide (a.WellFormed i)) encPrenexQBF encBool := by
  have hq := computableInPolyTime_decide_quantifierFree.comp (encPrenexQBF_matrix_polyTime .id')
  have hvars : ComputableInPolyTime (fun a : PrenexQBF => a.blocks.flatten)
      encPrenexQBF (encList encNat) := by fun_prop
  have hc : ComputableInPolyTime
      (fun a : PrenexQBF => decide (QBF.exs a.blocks.flatten a.matrix).Closed)
      encPrenexQBF encBool := TQBF.computableInPolyTime_decide_closed.comp
    (TQBF.computableInPolyTime_exs hvars (encPrenexQBF_matrix_polyTime .id'))
  simp only [wellFormed_iff]
  fun_prop

/-- The lengths of the first `i` variable blocks, paired with a common certificate length. -/
private def lengths (i : ℕ) (a : PrenexQBF) (n : ℕ) : List (ℕ × ℕ) :=
  (List.range i).map fun j => ((a.blocks.getD j []).length, n)

private theorem lengths_fst (i : ℕ) (a : PrenexQBF) (n : ℕ) (hi : a.blocks.length = i) :
    (lengths i a n).map Prod.fst = a.blocks.map List.length := by
  calc
    _ = ((List.range i).map (fun j => a.blocks.getD j [])).map List.length := by
      simp only [lengths, List.map_map, Function.comp_def]
    _ = _ := congrArg (List.map List.length) (by
      simpa only [List.ofFn_eq_pmap, List.pmap_eq_map] using
        List.ofFn_getD_eq_of_length [] hi)

private theorem block_length_le (a : PrenexQBF) (j : ℕ) :
    (a.blocks.getD j []).length ≤ a.blocks.flatten.length := by
  by_cases hj : j < a.blocks.length
  · rw [List.getD_eq_getElem _ _ hj]
    rw [List.length_flatten]
    exact List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) (List.getElem_mem hj))
  · simp [hj]

private def verifier (i : ℕ) (p : Polynomial ℕ) (x : PrenexQBF × List Bool) : Bool :=
  decide (x.1.WellFormed i) &&
    (x.1.matrix.tokens.reverse.foldl
      (QBF.evalStep fun v => (trueVars x.1.blocks.flatten
        (takeBlocks (lengths i x.1 (p.eval (encPrenexQBF x.1).length)) x.2)).contains v)
      []).headD false

private theorem verifier_polyTime (i : ℕ) (p : Polynomial ℕ) :
    ComputableInPolyTime (verifier i p) (encPair encPrenexQBF encBits) encBool := by
  have htake : ComputableInPolyTime
      (fun x : PrenexQBF × List Bool =>
        takeBlocks (lengths i x.1 (p.eval (encPrenexQBF x.1).length)) x.2)
      (encPair encPrenexQBF encBits) encBits := by
    have hp : ComputableInPolyTime
        (fun x : PrenexQBF × List Bool => p.eval (encPrenexQBF x.1).length)
        (encPair encPrenexQBF encBits) encUnary :=
      (unary_eval p).comp ((encoding_length encPrenexQBF).comp (fst _ _))
    unfold lengths
    simpa only [List.map_map, Function.comp_def] using computableInPolyTime_takeBlocks
      ((List.range i).map fun j =>
        (fun x : PrenexQBF × List Bool => (x.1.blocks.getD j []).length,
          fun x => p.eval (encPrenexQBF x.1).length))
      (by simp only [List.forall_mem_map]; intro j _; exact ⟨by fun_prop, hp⟩) (snd _ _)
  have hvars : ComputableInPolyTime (fun x : PrenexQBF × List Bool => x.1.blocks.flatten)
      (encPair encPrenexQBF encBits) (encList encNat) := by fun_prop
  have htrue := trueVars_polyTime.comp (hvars.prod htake)
  have heval := computableInPolyTime_evalTokens.comp
    ((encPrenexQBF_matrix_polyTime (fst _ _)).prod htrue)
  have hvalid := (wellFormed_polyTime i).comp (fst encPrenexQBF encBits)
  exact bool_and.comp (hvalid.prod heval)

private theorem verifier_spec (i : ℕ) (p : Polynomial ℕ)
    (hp : ∀ a : PrenexQBF, a.blocks.flatten.length ≤ p.eval (encPrenexQBF a).length)
    (q : Bool) (a : PrenexQBF) :
    Alternation q (List.replicate i (p.eval (encPrenexQBF a).length))
      (fun w => verifier i p (a, w) = true) ↔
        a.WellFormed i ∧ (a.formula q).eval (fun _ => false) = true := by
  by_cases ha : a.WellFormed i
  · have hl : (lengths i a (p.eval (encPrenexQBF a).length)).map Prod.snd =
        List.replicate i (p.eval (encPrenexQBF a).length) := by
      simp only [lengths, List.map_map, Function.comp_def, List.map_const', List.length_range]
    rw [← hl]
    have heval (w : List Bool) : verifier i p (a, w) = true ↔
        a.matrix.eval (QBF.updates (fun _ => false) a.blocks.flatten
          (takeBlocks (lengths i a (p.eval (encPrenexQBF a).length)) w)) = true := by
      simp only [verifier, ha, decide_true, Bool.true_and,
        QBF.foldl_evalStep ha.2.1, List.headD_cons, contains_trueVars]
    have hle : ∀ l ∈ lengths i a (p.eval (encPrenexQBF a).length), l.1 ≤ l.2 := by
      rintro l hl
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hl
      exact (block_length_le a j).trans (hp a)
    rw [alternation_congr heval,
      alternation_takeBlocks (P := fun w =>
        a.matrix.eval (QBF.updates (fun _ => false) a.blocks.flatten w) = true) hle,
      lengths_fst i a _ ha.1, ← eval_formula, and_iff_right ha]
  · simp only [verifier, ha, decide_false, Bool.false_and, Bool.false_eq_true,
      alternation_const, false_and]

/-- Grouped existential-first quantified SAT is in its level of the polynomial hierarchy,
including level zero. The verifier has native polynomial-time computation evidence. -/
theorem mem_SigmaP (i : ℕ) : SigmaSAT i ∈ SigmaP i encPrenexQBF := by
  have hlen : ComputableInPolyTime (fun a : PrenexQBF => a.blocks.flatten.length)
      encPrenexQBF encUnary := by fun_prop
  obtain ⟨p, hp⟩ := hlen.polyBounded.exists_polynomial
  refine ⟨List.replicate i p, verifier i p, List.length_replicate,
    verifier_polyTime i p, fun a => ?_⟩
  simp only [List.map_replicate]
  exact (verifier_spec i p hp true a).symm

/-- Grouped universal-first quantified SAT is in its level of the polynomial hierarchy,
including level zero. -/
theorem mem_PiP (i : ℕ) : PiSAT i ∈ PiP i encPrenexQBF := by
  have hlen : ComputableInPolyTime (fun a : PrenexQBF => a.blocks.flatten.length)
      encPrenexQBF encUnary := by fun_prop
  obtain ⟨p, hp⟩ := hlen.polyBounded.exists_polynomial
  refine ⟨List.replicate i p, verifier i p, List.length_replicate,
    verifier_polyTime i p, fun a => ?_⟩
  simp only [List.map_replicate]
  exact (verifier_spec i p hp false a).symm

end Cslib.Complexity.PrenexQBF
