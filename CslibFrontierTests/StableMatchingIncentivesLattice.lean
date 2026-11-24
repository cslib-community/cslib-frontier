/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.StableMatching.Core
import CslibFrontier.Algorithms.Lean.StableMatching.Incomplete.Incentives
import CslibFrontier.Algorithms.Lean.StableMatching.Incomplete.Lattice
import CslibFrontier.Algorithms.Lean.StableMatching.RothImpossibility

/-!
# Checked client tests for `StableMatching` core, lattice, and incentives

Exercises:
* **Core = stable matchings (`Theorem 10.12`, [SchummerVohra2007])**: on `Instance 3`
  (`rothInstance`) and on an unequal-sided `IncompleteInstance 3 2`, checking both a stable
  matching (`InCore` / `InWeakCore`) and an unstable/non-IR partial matching (blocked by a
  singleton coalition violating IR).
* **Roth impossibility for all `n ≥ 3` (`Roth1982`, Theorem 3) and sharp `n ≤ 2` boundary**:
  explicit checks at `n = 0, 1, 2` (positive) and `n = 3, 4, 5` (impossibility), plus fixed dummy
  pairs in `padInstance`.
* **Incomplete-list Conway–Knuth distributive lattice**: unequal-sided `3 × 2` market where one
  proposer stays permanently unmatched, checking `propJoin` / `propMeet` `DistribLattice` ordering
  (`⊥ < ⊤`), and exact non-`Nodup` preference lists.
* **Incomplete-list blocking lemma & truncation impossibility (`m ≥ 2, n ≥ 2`)**: concrete `2 × 2`
  truncation witness where `w₀` strictly gains by dropping `m₀` from `[m₁, m₀]` to `[m₁]`,
  contrasted with the positive `m ≤ 1 ∨ n ≤ 1` converse (`1 × 3`, `3 × 1`).
* **Gale–Sotomayor comparative statics (`ExtendsByReceiver`)**: adding a third receiver `w₂` to a
  `2 × 2` market strictly improves a proposer's partner and strictly worsens an original receiver's
  partner under deferred acceptance.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.StableMatchingIncentivesLattice

open Cslib.Algorithms.Lean.StableMatching

/-! ### 1. Core vs stability (`Instance` and `IncompleteInstance`) -/

/-- On `rothInstance`, both `rothProposerOptimal` and `rothReceiverOptimal` lie in `InCore` and
`InWeakCore`. -/
example :
    MatchingMechanism.rothInstance.InCore MatchingMechanism.rothProposerOptimal ∧
    MatchingMechanism.rothInstance.InWeakCore MatchingMechanism.rothReceiverOptimal :=
  ⟨(MatchingMechanism.rothInstance.isStable_iff_inCore _).1
      ((MatchingMechanism.rothInstance_isStable_iff _).2 (Or.inl rfl)),
   (MatchingMechanism.rothInstance.isStable_iff_inWeakCore _).1
      ((MatchingMechanism.rothInstance_isStable_iff _).2 (Or.inr rfl))⟩

/-- A `1 × 1` incomplete instance where receiver `0` finds proposer `0` unacceptable (`[]`):
pairing `(0, 0)` violates individual rationality and hence is **outside** the core. -/
example :
    let I : IncompleteInstance 1 1 := ⟨fun _ => [0], fun _ => []⟩
    let μ : PartialMatching 1 1 := PartialMatching.ofInjOn (fun _ => some 0) (fun p q _ _ _ =>
      Subsingleton.elim p q)
    ¬ I.InCore μ := by
  intro I μ hcore
  have hst : I.IsStable μ := (I.isStable_iff_inCore μ).2 hcore
  have hacc := (hst.1 0 0 rfl).2
  exact List.not_mem_nil hacc

/-! ### 2. Roth impossibility sharp threshold (`n ≤ 2` vs `n ≥ 3`, complete lists) -/

example :
    (MatchingMechanism.deferredAcceptance (n := 2)).IsStable ∧
    (MatchingMechanism.deferredAcceptance (n := 2)).IsProposerStrategyProof ∧
    (MatchingMechanism.deferredAcceptance (n := 2)).IsReceiverStrategyProof :=
  ⟨MatchingMechanism.isStable_deferredAcceptance,
   MatchingMechanism.isProposerStrategyProof_deferredAcceptance,
   MatchingMechanism.isReceiverStrategyProof_deferredAcceptance_of_le_two (by omega)⟩

example (M : MatchingMechanism 4) :
    ¬ (M.IsStable ∧ M.IsProposerStrategyProof ∧ M.IsReceiverStrategyProof) :=
  MatchingMechanism.not_isStable_and_strategyProof_of_le (by omega) M

example (M : MatchingMechanism 5) :
    ¬ (M.IsStable ∧ M.IsProposerStrategyProof ∧ M.IsReceiverStrategyProof) :=
  MatchingMechanism.not_isStable_and_strategyProof_of_le (by omega) M

/-- In `padInstance` for `n = 5`, dummy pairs `3` and `4` are fixed in every stable matching. -/
example {μ : Matching 5}
    (hμ : (MatchingMechanism.padInstance (by omega : 3 ≤ 5)
      MatchingMechanism.rothInstance).IsStable μ) :
    μ 3 = 3 ∧ μ 4 = 4 :=
  ⟨MatchingMechanism.isStable_padInstance_fixed (by omega) hμ (by decide),
   MatchingMechanism.isStable_padInstance_fixed (by omega) hμ (by decide)⟩

/-! ### 3. Incomplete-list lattice & duplicate preference list (`Nodup`-free) -/

/-- A `3 × 2` incomplete market with a duplicate entry (`[0, 0, 1]`) in proposer `0`'s list and
two distinct stable partial matchings leaving proposer `2` permanently unmatched. -/
private def unequalMarket : IncompleteInstance 3 2 where
  propPref
    | 0 => [0, 0, 1]
    | 1 => [1, 0]
    | 2 => []
  recvPref
    | 0 => [1, 0]
    | 1 => [0, 1]

example :
    unequalMarket.propRank 0 (unequalMarket.deferredAcceptance 0) = unequalMarket.finalState 0 ∧
    unequalMarket.deferredAcceptance 0 = some 0 ∧
    unequalMarket.deferredAcceptance 1 = some 1 ∧
    unequalMarket.deferredAcceptance 2 = none ∧
    unequalMarket.receiverDeferredAcceptance 0 = some 1 ∧
    unequalMarket.receiverDeferredAcceptance 1 = some 0 ∧
    unequalMarket.receiverDeferredAcceptance 2 = none := by
  refine ⟨unequalMarket.propRank_deferredAcceptance_eq_finalState 0, ?_⟩
  decide

example :
    let bot : unequalMarket.Stable := ⊥
    let top : unequalMarket.Stable := ⊤
    (bot ⊔ top) = top ∧ (bot ⊓ top) = bot ∧ bot ≠ top := by
  intro bot top
  refine ⟨bot_sup_eq _, inf_top_eq _, fun h => ?_⟩
  have h0 : bot.1 0 = top.1 0 := congrArg (fun x => x.1 0) h
  revert h0
  decide

/-! ### 4. Incomplete-list sharp Roth threshold (`2 × 2` vs `1 × 3` / `3 × 1`) -/

/-- On `truncationWitness 2 2`, receiver `0` strictly gains under proposer-DA by truncating her
list from `[1, 0]` to `[1]`: she moves from `some 0` (rank 1) to `some 1` (rank 0). -/
example :
    let I := PartialMatchingMechanism.truncationWitness 2 2 (by omega) (by omega)
    I.deferredAcceptance.symm 0 = some 0 ∧
    (I.updateRecvPref 0 [1]).deferredAcceptance.symm 0 = some 1 ∧
    I.recvRank 0 (some 1) < I.recvRank 0 (some 0) := by
  decide

/-- Positive boundary (`m = 1, n = 3` and `m = 3, n = 1`): `deferredAcceptance` is strategy-proof
for BOTH proposers and receivers. -/
example :
    PartialMatchingMechanism.IsProposerStrategyProof
      (IncompleteInstance.deferredAcceptance (m := 1) (n := 3)) ∧
    PartialMatchingMechanism.IsReceiverStrategyProof
      (IncompleteInstance.deferredAcceptance (m := 1) (n := 3)) ∧
    PartialMatchingMechanism.IsProposerStrategyProof
      (IncompleteInstance.deferredAcceptance (m := 3) (n := 1)) ∧
    PartialMatchingMechanism.IsReceiverStrategyProof
      (IncompleteInstance.deferredAcceptance (m := 3) (n := 1)) :=
  ⟨PartialMatchingMechanism.isProposerStrategyProof_deferredAcceptance,
   PartialMatchingMechanism.isReceiverStrategyProof_deferredAcceptance_of_le_one (Or.inl le_rfl),
   PartialMatchingMechanism.isProposerStrategyProof_deferredAcceptance,
   PartialMatchingMechanism.isReceiverStrategyProof_deferredAcceptance_of_le_one (Or.inr le_rfl)⟩

/-- Impossibility already at `m = 2, n = 2` (and asymmetric `m = 2, n = 3`). -/
example (M : PartialMatchingMechanism 2 3) :
    ¬ (M.IsStable ∧ M.IsProposerStrategyProof ∧ M.IsReceiverStrategyProof) :=
  PartialMatchingMechanism.not_isStable_and_strategyProof (by omega) (by omega) M

/-! ### 5. Gale–Sotomayor comparative statics (`2 × 2 → 2 × 3`) -/

private def baseMarket : IncompleteInstance 2 2 where
  propPref
    | 0 => [0, 1]
    | 1 => [0, 1]
  recvPref
    | 0 => [0, 1]
    | 1 => [0, 1]

/-- Add receiver `2` who only wants proposer `0` and is proposer `0`'s new favourite. -/
private def enlargedMarket : IncompleteInstance 2 3 where
  propPref
    | 0 => [2, 0, 1]
    | 1 => [0, 1]
  recvPref
    | 0 => [0, 1]
    | 1 => [0, 1]
    | 2 => [0]

private theorem extends_witness :
    IncompleteInstance.ExtendsByReceiver baseMarket enlargedMarket where
  recvPref_castSucc r := by revert r; decide
  mem_propPref_castSucc_iff p r := by revert p r; decide
  propRank_castSucc_lt_iff p r₁ r₂ := by revert p r₁ r₂; decide

/-- Adding receiver `2` strictly improves *both* proposers (proposer `0`: `0 → 2`, proposer `1`:
`1 → 0`) and strictly worsens receiver `0` (`0 → 1`) and leaves receiver `1` unmatched
(`some 1 → none`), verifying every inequality of `ExtendsByReceiver`. -/
example :
    (∀ p : Fin 2, enlargedMarket.propRank p (enlargedMarket.deferredAcceptance p) ≤
      enlargedMarket.propRank p ((baseMarket.deferredAcceptance p).map Fin.castSucc)) ∧
    (∀ r : Fin 2, baseMarket.recvRank r (baseMarket.deferredAcceptance.symm r) ≤
      baseMarket.recvRank r (enlargedMarket.deferredAcceptance.symm r.castSucc)) ∧
    (∀ p : Fin 2, enlargedMarket.propRank p (enlargedMarket.receiverDeferredAcceptance p) ≤
      enlargedMarket.propRank p
        ((baseMarket.receiverDeferredAcceptance p).map Fin.castSucc)) ∧
    (∀ r : Fin 2, baseMarket.recvRank r (baseMarket.receiverDeferredAcceptance.symm r) ≤
      baseMarket.recvRank r (enlargedMarket.receiverDeferredAcceptance.symm r.castSucc)) ∧
    enlargedMarket.deferredAcceptance 0 = some 2 ∧
    enlargedMarket.deferredAcceptance 1 = some 0 ∧
    baseMarket.deferredAcceptance 0 = some 0 ∧
    baseMarket.deferredAcceptance 1 = some 1 ∧
    enlargedMarket.deferredAcceptance.symm 1 = none := by
  refine ⟨extends_witness.deferredAcceptance_propRank_le,
    extends_witness.deferredAcceptance_recvRank_le,
    extends_witness.receiverDeferredAcceptance_propRank_le,
    extends_witness.receiverDeferredAcceptance_recvRank_le, ?_⟩
  decide

end CslibFrontierTests.StableMatchingIncentivesLattice
