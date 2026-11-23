/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Words

/-!
# Encoded-output transport for normalized machine witnesses

`ComputableTidilyInTimeAndSpace.of_enc_eq` reuses a normalized machine when its encoded output
is unchanged. Numerical linear certificates use `ComputableInDegree` with cost degree one;
`ComputableInDegree.one_one_iff` gives the equivalent common linear time/workspace bound.
-/

namespace Turing.MultiTapeTM

-- upstream: candidate
-- vendored: local output-word transport rule; not part of the copied revision.
/-- Reuse the same machine when the new function emits the same encoded output word.
The time and space bounds are unchanged; no encoding conversion is performed. -/
public theorem ComputableTidilyInTimeAndSpace.of_enc_eq
    {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : α → β} {g : α → γ} {t s : α → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encIn encMid t s)
    (h : ∀ a, encOut (g a) = encMid (f a)) :
    ComputableTidilyInTimeAndSpace g encIn encOut t s :=
  let ⟨k, State, hfinite, tm, htm⟩ := hf
  ⟨k, State, hfinite, tm, fun a => h a ▸ htm a⟩

end Turing.MultiTapeTM
