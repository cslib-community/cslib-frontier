/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Controller
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Native scalar operations for double counting

The comparison used by `Cslib.DoubleCounting.Passes` takes two binary tally records and uses
workspace linear in their encoded length. In a scan on `N` vertices with walk lengths bounded
by `k`, the count is at most `N` and the sum is at most `N * k`. The comparison can therefore
operate on short registers, independently of the walks that contributed to them.
The outer scan can update its tally
and tie flag in linear space in the binary registers, using `addVertex_inSpace`.
-/

public section

namespace Turing.DoubleCounting

open Cslib.DoubleCounting MultiTapeTM ComputableInSpace

/-- Binary count (framed), followed by binary length sum. -/
enc_structure encTally : Tally where count : encNat, lengthSum : encNat

/-- The actual tally (framed), followed by the expected tally. -/
abbrev encTallies := encPair encTally encTally

/-- The terminal test uses linear work space in the size of the two binary tallies. -/
theorem matches_inSpace :
    ComputableInSpace (fun p : Tally × Tally => p.1.matches p.2)
      encTallies encBool (fun p => (encTallies p).length) := by
  have actual := fst encTally encTally
  have expected := snd encTally encTally
  have countCheck := budget_natEq (encTally_count_budget actual) (encTally_count_budget expected)
  have lengthCheck := budget_natEq
    (encTally_lengthSum_budget actual) (encTally_lengthSum_budget expected)
  exact (budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod countCheck lengthCheck)).of_enc_eq fun _ => rfl

/-- Binary tally followed by the tie bit, using the record framing convention. -/
enc_structure encRoundUpdate : RoundUpdate where tally : encTally, bad : encBool

/-- The outer scan's vertex update uses linear space in its encoded scalar arguments. -/
theorem addVertex_inSpace :
    ComputableInSpace
      (fun (⟨a, k, predecessors⟩ : RoundUpdate × (ℕ × ℕ)) => a.addVertex k predecessors)
      (encPair encRoundUpdate (encPair encNat encNat)) encRoundUpdate
      (fun p => (encPair encRoundUpdate (encPair encNat encNat) p).length) := by
  let encIn := encPair encRoundUpdate (encPair encNat encNat)
  have ha := fst encRoundUpdate (encPair encNat encNat)
  have hargs := snd encRoundUpdate (encPair encNat encNat)
  have hk := hargs.fst'
  have hp := hargs.snd'
  have hOne := budget_const (encIn := encIn) (encB := encNat) 1 (.refl _)
  have ht := encRoundUpdate_tally_budget ha
  have hnew := encTally_mk_budget
    (budget_natAdd (encTally_count_budget ht) hOne)
    (budget_natAdd (encTally_lengthSum_budget ht) (budget_natAdd hk hOne))
  have hflag := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 || p.2)
    (budget_prod (encRoundUpdate_bad_budget ha) (budget_natLt hOne hp))
  exact (encRoundUpdate_mk_budget (budget_ite (budget_natIsZero hp) ht hnew) hflag).of_enc_eq
    fun p => by simp [RoundUpdate.addVertex]

/-- Space occupied by the outer tally and flag when their numeric registers are bounded. -/
theorem length_encRoundUpdate_le {a : RoundUpdate} {n : ℕ}
    (hc : a.tally.count ≤ n) (hs : a.tally.lengthSum ≤ n * n) :
    (encRoundUpdate a).length ≤ 6 * (Nat.log2 (n * n) + 1) + 4 := by
  have hn : n ≤ n * n := by cases n <;> simp
  have hcount := length_encNat_le_log2 (hc.trans hn)
  have hsum := length_encNat_le_log2 hs
  simp only [encRoundUpdate_apply, encRoundUpdateFields, encTally_apply, encTallyFields,
    length_encPair, encBool_apply, List.length_singleton]
  omega

/-- An exact current-round tally and its tie bit fit in logarithmic space in the
number of vertices throughout the bounded controller's round schedule. -/
theorem length_encRoundUpdate_of_expected {n k : ℕ} {r : Fin n → Fin n → Prop}
    {s : Fin n} (hk : k ≤ n) (bad : Bool) :
    (encRoundUpdate ⟨expected r s k, bad⟩).length ≤ 6 * (Nat.log2 (n * n) + 1) + 4 := by
  obtain ⟨hc, hs⟩ := expected_bounds (r := r) (s := s) (k := k)
  apply length_encRoundUpdate_le (by simpa using hc)
  exact (by simpa using hs : (expected r s k).lengthSum ≤ n * k).trans
    (Nat.mul_le_mul_left n hk)

end Turing.DoubleCounting
