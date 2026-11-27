/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Basic
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Slowdown
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Speedup
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.NondeterministicPolynomial

/-!
# Certificates for a native speedup and slowdown

The profiles describe integer polynomial exponents. A proposed slowdown is checked with the
exact inequality `a * p ≤ b * q` for a rational simulation exponent `p / q`. The grammar includes
clock weakening, the native degree-twelve time/degree-two space speedup to degree eight,
and the native two-block slowdown. The padding step and linear-NTIME simulation budget are
explicit assumptions. Search over this grammar checks each returned certificate; it does not
validate the rules of other alternation-trading proof systems.

## Main definitions

* `TradingProfile`, `checkTradingChain`, `searchTradingChain`.

## Main results

* `tradingEdge_sound`, `checkTradingChain_sound`, `searchTradingChain_contradiction`.

## References

* Frontier's [alternation-trading roadmap](https://github.com/cslib-community/cslib-frontier/issues/2896).
* The [automated alternation-trading generator](https://github.com/abhijit-mudigonda/automated-alternating-lbs)
  inspired the search over rule sequences. It is independent of this certificate checker.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Integer bounds for the native classes. The assumed linear-NTIME simulation
uses a rational exponent via an exact inequality on powers of its clock. -/
inductive TradingProfile where
  | nt (degree : ℕ)
  | two (degree : ℕ)
  | spaceTwelve
  deriving DecidableEq

/-- Interpret a resource profile in Frontier’s native bit-string classes. -/
def TradingProfile.languages : TradingProfile → Set (Set (List Bool))
  | .nt a => NTIME encBits fun n => (n + 1) ^ a
  | .two a => SigmaTwoTIME encBits fun n => (n + 1) ^ a
  | .spaceTwelve => TISP encBits (fun n => (n + 1) ^ 12) (fun n => (n + 1) ^ 2)

/-- The padding edge is a premise. The other rules are instantiations of native
weakening, speedup and slowdown. No solver arithmetic is trusted. -/
@[expose] def tradingEdge (p q : ℕ) : TradingProfile → TradingProfile → Bool
  | .nt a, .nt b => decide (a ≤ b)
  | .nt a, .spaceTwelve => decide (a = 12)
  | .spaceTwelve, .two b => decide (b = 8)
  | .two a, .nt b => decide (0 < q ∧ 1 ≤ a ∧ a ≤ b ∧ a * p ≤ b * q)
  | _, _ => false

/-- Each checked edge gives the named inclusion under explicit padding and simulation premises. -/
theorem tradingEdge_sound {p q C : ℕ} {t : ℕ → ℕ}
    (padding : (TradingProfile.nt 12).languages ⊆ TradingProfile.spaceTwelve.languages)
    (linear : NTIME encBits id ⊆ DTIME encBits t)
    (cost : ∀ n, t n ^ q ≤ C * (n + 1) ^ p)
    {a b : TradingProfile} (h : tradingEdge p q a b = true) : a.languages ⊆ b.languages := by
  cases a <;> cases b <;> simp only [tradingEdge, decide_eq_true_eq, Bool.false_eq_true] at h
  · exact NTIME_mono fun n => Nat.pow_le_pow_right (Nat.succ_pos n) h
  · subst_vars
    exact padding
  · exact SigmaTwoTIME_succ_pow_subset_NTIME_succ_pow linear cost h.1 h.2.1 h.2.2.1 h.2.2.2
  · subst_vars
    exact TISP_pow_twelve_subset_SigmaTwoTIME

/-- Check every edge and require the final profile to equal the requested goal. -/
@[expose] def checkTradingChain (p q : ℕ) (goal : TradingProfile) :
    TradingProfile → List TradingProfile → Bool
  | a, [] => decide (a = goal)
  | a, b :: bs => tradingEdge p q a b && checkTradingChain p q goal b bs

/-- A checked sequence composes the native inclusions. -/
theorem checkTradingChain_sound {p q C : ℕ} {t : ℕ → ℕ}
    (padding : (TradingProfile.nt 12).languages ⊆ TradingProfile.spaceTwelve.languages)
    (linear : NTIME encBits id ⊆ DTIME encBits t)
    (cost : ∀ n, t n ^ q ≤ C * (n + 1) ^ p)
    (goal a : TradingProfile) (chain : List TradingProfile)
    (h : checkTradingChain p q goal a chain = true) : a.languages ⊆ goal.languages := by
  induction chain generalizing a with
  | nil =>
    have eq : a = goal := of_decide_eq_true h
    exact eq ▸ Set.Subset.rfl
  | cons b rest ih =>
    have pair := Bool.and_eq_true_iff.mp h
    exact (tradingEdge_sound padding linear cost pair.1).trans (ih b pair.2)

/-- Enumerate certificate sequences up to the requested depth over a finite
profile list. The public search validates each proposed certificate. -/
@[expose] def tradingCandidates (profiles : List TradingProfile) :
    ℕ → List (List TradingProfile)
  | 0 => [[]]
  | depth + 1 => [] :: profiles.flatMap fun a => (tradingCandidates profiles depth).map (a :: ·)

/-- Search the finite profile list for a checked chain of at most the given depth. -/
@[expose] def searchTradingChain (p q depth : ℕ) (profiles : List TradingProfile)
    (start goal : TradingProfile) : Option (List TradingProfile) :=
  (tradingCandidates profiles depth).find? (checkTradingChain p q goal start)

/-- A checked chain from degree twelve to a smaller positive degree contradicts the native
hierarchy under the stated inclusion and resource premises. -/
theorem searchTradingChain_contradiction {p q C depth b : ℕ} {t : ℕ → ℕ}
    {profiles : List TradingProfile} {chain : List TradingProfile} (hb : 1 ≤ b) (hlt : b < 12)
    (found : searchTradingChain p q depth profiles (.nt 12) (.nt b) = some chain)
    (padding : (TradingProfile.nt 12).languages ⊆ TradingProfile.spaceTwelve.languages)
    (linear : NTIME encBits id ⊆ DTIME encBits t)
    (cost : ∀ n, t n ^ q ≤ C * (n + 1) ^ p) : False := by
  have cert : checkTradingChain p q (.nt b) (.nt 12) chain = true := List.find?_some found
  exact (NTIME_succ_pow_ssubset_NTIME_succ_pow (a := b) (b := 12) hb hlt).not_superset
    (checkTradingChain_sound padding linear cost _ _ _ cert)

end Cslib.Complexity
