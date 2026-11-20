/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.FewP.Machine

/-!
# Accepting branch counts in exponential time

Both classes use the same all-branches exponential clock, with transition occurrences
distinguished as in the machine characterization of `FewP`.

## Main definitions

* `HasExponentialTimeAcceptCount`: functions realized as native exponential-time counts.
* `FewEXP`: existential acceptance with an independent exponential bound on ambiguity.
* `ParityEXP`: acceptance by the parity of the accepting branch count.
-/

public section

namespace Cslib.Complexity

open _root_.Turing

variable {α : Type}

/-- A single nonblocking counting machine realizes the given accepting count within
exponential time on every branch. -/
@[expose] def HasExponentialTimeAcceptCount (enc : α ↪ List Bool) (f : α → ℕ) : Prop :=
  ∃ (c d e k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeCTM k Bool State),
    machine.Nonblocking ∧ ∀ a,
      let clock := d * 2 ^ (enc a).length ^ c + e
      let cfg := Cfg.init machine.initial (enc a)
      machine.HaltsWithin clock cfg ∧ machine.acceptCount clock cfg = f a

/-- FewEXP is nondeterministic exponential time with at most exponentially many accepting paths
on every input. The ambiguity exponent is independent of the clock exponent [Ronneburger2004]. -/
@[expose] def FewEXP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (f : α → ℕ) (c d e : ℕ), HasExponentialTimeAcceptCount enc f ∧ ∀ a,
    f a ≤ d * 2 ^ (enc a).length ^ c + e ∧ (a ∈ A ↔ 0 < f a)}

/-- Parity EXP is the exponential-time analogue of `ParityP`: accept exactly when the count
of accepting branches is odd. -/
@[expose] def ParityEXP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f : α → ℕ, HasExponentialTimeAcceptCount enc f ∧ ∀ a, a ∈ A ↔ Odd (f a)}

end Cslib.Complexity
