/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.Promise.CoinSplit
import CslibFrontier.Tactic.PolyTime

/-! Checked clients of Goldreich's Exercise 6.11: the error bound `SmallOfflineError` is met by an
algorithm that never errs, for a set that is neither empty nor everything, and both parts of the
exercise then apply to its promise problem `Π′`, whose yes-instances are exactly the pairs with a
member of `S` and a coin string of the right length. -/

set_option linter.privateModule false

namespace CslibFrontierTests.CoinSplit

open Cslib Cslib.Complexity Cslib.Complexity.PromiseProblem Turing.MultiTapeTM

/-- The words starting with `true`. -/
abbrev S : Set (List Bool) := {w | w.headD false = true}

/-- An off-line algorithm deciding `S` without error, ignoring its coins. -/
abbrev A' : List Bool × List Bool → Bool := fun q => q.1.headD false

theorem A'_polyTime : ComputableInPolyTime A' (encPair encBits encBits) encBool := by
  polytime

/-- `A'` never errs, so it meets the error bound for any number of coins, here `2 |x|`. -/
theorem smallOfflineError : SmallOfflineError encBits S Polynomial.X A' := fun x => by
  simp only [S, A', Set.mem_ofPred_eq, iff_self, not_true_eq_false]
  rw [Finset.filter_false_of_mem fun _ _ h => h, Finset.card_empty, mul_zero]
  positivity

/-- Exercise 6.11(1) for this algorithm. -/
example : RPReducibleWithError encBits (encPair encBits encBits) (fun _ => 1 / 2) (ofSet S)ᶜ
    (coinSplit smallOfflineError)ᶜ :=
  rpReducibleWithError_coinSplit smallOfflineError

/-- Goldreich's sampler, applied to the member `[true]`, hits `Π′_yes` with probability more
than `1 / 2`. -/
example : 1 / 2 < ((ProbComp.eval ((fun w => ([true], w)) <$>
    BitString.sampleList (Polynomial.X.eval (encBits [true]).length))).toOuterMeasure
      (coinSplit smallOfflineError).yes).toReal :=
  half_lt_toOuterMeasure_coinSplit_yes smallOfflineError (by simp [S])

/-- Exercise 6.11(2) for this algorithm. -/
example : coinSplit smallOfflineError ∈ PromiseCoRP (encPair encBits encBits) :=
  coinSplit_mem_PromiseCoRP A'_polyTime smallOfflineError

/-- A yes-instance of `Π′`: a member of `S` with a coin string of length `|x|`. -/
example : ([true], [false]) ∈ (coinSplit smallOfflineError).yes := by
  simp [S, A']

/-- A no-instance of `Π′`. -/
example : ([false], [false]) ∈ (coinSplit smallOfflineError).no := by
  simp [S]

/-- A pair with a coin string of the wrong length is outside the promise. -/
example : ([true], []) ∉ (coinSplit smallOfflineError).yes ∪ (coinSplit smallOfflineError).no := by
  simp [S]

end CslibFrontierTests.CoinSplit
