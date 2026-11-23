/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module

import CslibFrontier.Crypto.Computational.CBCMAC
import CslibFrontier.Crypto.Primitives.UHF.PrefixFreePRF

/-!
# Tests for the prefix-free collision wrapper

Use a proper-prefix pair in the CBC word domain with a two-block cap. Its queries use the
three-block domain. A repeated valid guess makes no external query.
-/

set_option linter.privateModule false

open Cslib Cslib.Crypto Cslib.Crypto.UHF Cslib.Probability Turing.MultiTapeTM

private def properPrefixGuess : CollisionGuess (List Bool) :=
  ⟨[true, false], [true, false, false, false]⟩

example : IsPrefixFreeOraclePPT (cbcBlockValid (fun _ => 3)) id
    (prefixFreeCollisionReduction id id (cbcBlockValid (fun _ => 2))
      (fun _ => pure properPrefixGuess)) := by
  apply isPrefixFreeOraclePPT_prefixFreeCollisionReduction ComputableInPolyTime.id'
    ComputableInPolyTime.id' (computableInPolyTime_cbcBlockValid (ComputableInPolyTime.const 2))
    _ (ComputableInPolyTime.const properPrefixGuess).isPPTOn
  intro n w hv
  simp only [cbcBlockValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
  obtain ⟨⟨hNonempty, hMod⟩, hCap⟩ := hv
  refine ⟨?_, Nat.dvd_of_mod_eq_zero hMod⟩
  cases n with
  | zero => exact False.elim (Nat.not_le_of_gt hNonempty (by simpa using hCap))
  | succ n => exact Nat.zero_lt_succ n

example :
    wordQueryRunDist id
      (prefixFreeCollisionReduction id id (cbcBlockValid (fun _ => 2))
        (fun _ => pure properPrefixGuess) 2 []) =
    PMF.pure (true, [[true, false, true, true], [true, false, false, false, true, true]]) := by
  have hvalid : (cbcBlockValid (fun _ => 2) 2 properPrefixGuess.first &&
      cbcBlockValid (fun _ => 2) 2 properPrefixGuess.second &&
      decide (properPrefixGuess.first ≠ properPrefixGuess.second)) = true := by decide
  simp only [prefixFreeCollisionReduction, wordQueryRunDist_sample_bind, ProbComp.eval_pure,
    PMF.pure_bind, ite_eq_left hvalid, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def, wordQueryRunDist_query_bind, wordQueryRunDist_pure, PMF.pure_map]
  rfl

example :
    wordQueryRunDist id
      (prefixFreeCollisionReduction id id (cbcBlockValid (fun _ => 2))
        (fun _ => pure ⟨[true, false], [true, false]⟩) 2 []) = PMF.pure (false, []) := by
  simp [prefixFreeCollisionReduction]
