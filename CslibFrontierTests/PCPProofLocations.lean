/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Classes.PCP.ProofLocations
import CslibFrontier.Computability.DecisionTree.Leaves

/-! Checked instances of the effective-length bounds of Goldreich, Exercise 9.15: an adaptive
verifier with `r = 1` coin and `q = 2` queries, whose second query depends on its coin and on the
first answer, examines six distinct locations: it attains `2 ^ r * (2 ^ q - 1) = 6`, within the
bound `2 ^ (q + r) = 8`. The non-adaptive bound applies to every `IsPCPVerifier`. -/

set_option linter.privateModule false

namespace CslibFrontierTests.PCPProofLocations

open Cslib Cslib.Complexity Cslib.DecisionTree

/-- On coin `ρ`, query location `ρ`; then query location `2 + 2 ρ + b` after the answer `b`. -/
def adaptive (ρ : BitString 1) : DecisionTree ℕ Bool :=
  let c := (ρ 0).toNat
  node c (node (2 + 2 * c) (leaf false) (leaf true)) (node (3 + 2 * c) (leaf false) (leaf true))

example (ρ : BitString 1) : (adaptive ρ).depth ≤ 2 := by
  cases h : ρ 0 <;> simp [adaptive, h]

/-- The two trees examine six distinct locations `0, …, 5`, three each (`2 ^ 2 - 1`), which
attains `2 ^ r * (2 ^ q - 1) = 6`; the bound `2 ^ (q + r)` is `8`. -/
example : (Finset.univ.biUnion fun ρ => (adaptive ρ).allQueries).card = 6 := by
  decide

example : (Finset.univ.biUnion fun ρ => (adaptive ρ).allQueries).card ≤ 2 ^ (2 + 1) :=
  card_biUnion_allQueries_le adaptive fun ρ => by cases h : ρ 0 <;> simp [adaptive, h]

/-- The locations queried on a proof are among those at the internal nodes. -/
example (ρ : BitString 1) (π : ℕ → Bool) : (adaptive ρ).queries π ⊆ (adaptive ρ).allQueries :=
  queries_subset_allQueries _ _

/-- The non-adaptive bound for an arbitrary verifier with its own bounds `r` and `q`. -/
example {α : Type} {enc : α ↪ List Bool} {r q : ℕ → ℕ} {V : PCPVerifier α} {A : Set α}
    (h : IsPCPVerifier enc r q V A) (a : α) :
    (V.queryTable a).toFinset.card ≤ 2 ^ r (enc a).length * q (enc a).length :=
  h.card_toFinset_queryTable_le a

end CslibFrontierTests.PCPProofLocations
