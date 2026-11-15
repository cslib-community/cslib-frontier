/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Basic
public import CslibFrontier.Probability.Uniform

/-!
# Translation-Invariant Key Sources for Secret Sharing

Defines `Cslib.Crypto.Protocols.SecretSharing.SourceClass.translationInvariant`, the shared class
of translation-invariant key distributions on an additive group `Key`, together with uniform
membership `SourceClass.uniformOfFintype_mem_translationInvariant`.

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.SourceClass.translationInvariant`: distributions `P`
  invariant under right translation `P.map (· + δ) = P`.

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.SourceClass.uniformOfFintype_mem_translationInvariant`:
  `uniformOfFintype Key ∈ SourceClass.translationInvariant Key` when `Key` is finite.
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing

open Cslib.Probability.PMF

namespace SourceClass

/-- The class of translation-invariant distributions on an additive key type `Key`:
distributions `P` unchanged under right translation `P.map (· + δ) = P` for every `δ : Key`.

When `Key` is finite and nonempty, `uniformOfFintype Key` belongs to this class; when `Key` is
infinite and nontrivial, no translation-invariant `PMF` exists (`translationInvariant Key = ∅`),
making privacy over it vacuous. -/
@[expose] def translationInvariant (Key : Type*) [Add Key] : SourceClass Key :=
  { P | ∀ δ : Key, P.map (· + δ) = P }

/-- Uniform key sampling belongs to `SourceClass.translationInvariant` for every finite additive
group. -/
theorem uniformOfFintype_mem_translationInvariant (Key : Type*)
    [AddGroup Key] [Fintype Key] :
    uniformOfFintype Key ∈ translationInvariant Key := fun δ =>
  uniformOfFintype_map_add_right δ

end SourceClass

end Cslib.Crypto.Protocols.SecretSharing
