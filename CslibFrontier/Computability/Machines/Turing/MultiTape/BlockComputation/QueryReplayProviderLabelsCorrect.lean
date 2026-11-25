/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayProvidersCorrect

/-!
# Invariants and rejection of checked provider labels

A successful checked combination has canonical explicit replay buffers. Rejection occurs
exactly when the previous label or at least one provider label fails canonical decoding. The
criterion checks every provider, including labels for windows absent from the current schedule.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Providers.Labels

variable {k s : ℕ} {Q : Type}

/-- Every successful checked combination supplies the canonical buffers needed by native replay. -/
theorem canonical_of_combine_some (e : Q ≃ Fin s) (b : ℕ) (ports : PortMap k)
    (previousWord : List Bool) (providerWords : ProviderWords k) (raw : RawResult k Q)
    (hcombined : combine e (b, ports, previousWord, providerWords) = some raw) :
    Load.CanonicalWindows b raw := by
  classical
  let previous := Encoding.NativeChecked.parse (k := k) e (b, previousWord)
  let providers := fun h δ => Encoding.NativeChecked.parse (k := k) e (b, providerWords h δ)
  let empty : RawResult k Q := (none, fun _ => 0, .empty, fun _ => [])
  change (if previous.isSome && decide (∀ h δ, (providers h δ).isSome = true) then
    some (Providers.combine (b, ports, previous.getD empty,
      fun h δ => (providers h δ).getD empty)) else none) = some raw at hcombined
  split at hcombined
  next hguard =>
    obtain ⟨hprevSome, hprovSome⟩ :
        previous.isSome = true ∧ ∀ h δ, (providers h δ).isSome = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hguard
    obtain ⟨prev, hprev⟩ := Option.isSome_iff_exists.mp hprevSome
    choose prov hprov using fun h δ => Option.isSome_iff_exists.mp (hprovSome h δ)
    rw [← Option.some.inj hcombined]
    exact Providers.canonical_combine b ports _ _
      (by
        simpa only [hprev, Option.getD_some] using
          Load.canonical_of_checked_some e b previousWord prev hprev)
      fun h δ => by
        simpa only [hprov h δ, Option.getD_some] using
          Load.canonical_of_checked_some e b (providerWords h δ) (prov h δ) (hprov h δ)
  next => contradiction

/-- Checked combination rejects precisely the failed previous/provider labels, even when the
port map ignores that provider's window. No default value turns failure into success. -/
theorem combine_eq_none_iff (e : Q ≃ Fin s) (b : ℕ) (ports : PortMap k)
    (previousWord : List Bool) (providerWords : ProviderWords k) :
    combine e (b, ports, previousWord, providerWords) = none ↔
      Encoding.NativeChecked.parse (k := k) e (b, previousWord) = none ∨
        ∃ h δ, Encoding.NativeChecked.parse (k := k) e (b, providerWords h δ) = none := by
  classical
  cases hprevious : Encoding.NativeChecked.parse (k := k) e (b, previousWord) with
  | none => simp [combine, hprevious]
  | some previous => simp [combine, hprevious, Option.isSome_eq_false_iff]

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Providers.Labels
