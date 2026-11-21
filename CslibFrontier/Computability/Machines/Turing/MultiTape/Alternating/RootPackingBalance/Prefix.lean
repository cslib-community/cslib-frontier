/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance
public import CslibFrontier.Computability.PolyTime.SeededRankChallenge

/-!
# The quantified root balance game

The physical prefix quantifies over binary moves. On the resulting three fields, the native
challenge decoder determines a terminal answer or the edge, bit and claim of a rank query.
The order of the quantifiers forces an edge's rank guess to serve every bit challenge.
-/

public section

namespace Turing.MultiTapeATM.RootPackingBalance

open Cslib MultiTapeTM QuantifiedWord

/-- The value of a concrete choice word when the native decoder has either stopped or
produced a request for the rank machine. -/
@[expose] def challengeValue (n a : ℕ) (check : SeededRankChallenge.Request → Prop)
    (word : List Bool) : Prop :=
  (SeededRankChallenge.run ⟨n, a, word⟩).elim (fun b => b = true) check

/-- The exact value of the three-field game with the actual native challenge decoder. -/
theorem plays_iff_rank_checks (n a : ℕ) (check : SeededRankChallenge.Request → Prop) :
    let w := Nat.clog 2 n
    plays (challengeValue n a check) [] (rankFlags w) ↔ ∀ e : Fin n, ∃ g : Fin (2 ^ w),
      SeededRankCapacity.fits ⟨n, a, g.val⟩ = true ∧
      ∀ j : Fin w, check ⟨e.val, j.val, g.val.testBit j.val⟩ := by
  apply plays_rankFlags_iff_local n (Nat.clog 2 n) (Nat.le_pow_clog (by decide) n)
  intro e g j
  unfold challengeValue
  rw [List.append_assoc, SeededRankChallenge.run_lowBits _ _ _ _ _ e.isLt g.isLt j.isLt]
  by_cases he : e.val < n <;> by_cases hg : (g.val + 1) * 64 ^ (2 * a) ≤ 2 * n <;>
    by_cases hj : j.val < Nat.clog 2 n <;>
    simp [he, hg, hj, SeededRankCapacity.fits_eq_true_iff]

/-- The finite native prefix and a continuation that implements the decoded terminal semantics
check all legitimate edge challenges. The prefix pays exactly twice the flag length plus one. -/
theorem prefix_spec {k : ℕ} {S : Type} {input : List Bool} (leaf : MultiTapeATM k Bool S)
    (tape : Fin k) (storage : Cfg k Bool Unit input) (t n a : ℕ)
    (check : SeededRankChallenge.Request → Prop)
    (h : ∀ word : List Bool, word.length = (rankFlags (Nat.clog 2 n)).length →
      let cfg := WordGameLeaf.config tape (some leaf.toPTM.initial) word word.length storage
      leaf.HaltsWithin t cfg ∧ (leaf.AcceptsWithin t cfg ↔ challengeValue n a check word)) :
    let w := Nat.clog 2 n
    let cfg := WordGameLeaf.config tape (some .dispatch) (rankFlags w) 0 storage
    let time := t + 2 * (rankFlags w).length + 1
    (machine leaf tape).HaltsWithin time cfg ∧ ((machine leaf tape).AcceptsWithin time cfg ↔
      ∀ e : Fin n, ∃ g : Fin (2 ^ w), SeededRankCapacity.fits ⟨n, a, g.val⟩ = true ∧
        ∀ j : Fin w, check ⟨e.val, j.val, g.val.testBit j.val⟩) := by
  obtain ⟨hh, ha⟩ := spec leaf tape t storage (challengeValue n a check) []
    (rankFlags (Nat.clog 2 n)) (by simpa using h)
  exact ⟨hh, ha.trans (plays_iff_rank_checks n a check)⟩

end Turing.MultiTapeATM.RootPackingBalance
