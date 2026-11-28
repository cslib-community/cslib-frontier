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
* `Cslib.Crypto.Protocols.SecretSharing.AccessStructure.viewDistOf_eq_of_map_add_eq`: a coalition
  has the same view distribution on two secrets when a translation of the key that fixes the source
  carries its view on the first to its view on the second.
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing

open Cslib.Probability.PMF

namespace SourceClass

/-- The class of translation-invariant distributions on an additive key type `Key`:
distributions `P` unchanged under right translation `P.map (· + δ) = P` for every `δ : Key`.

When `Key` is a finite additive group, `uniformOfFintype Key` belongs to this class; when `Key`
is an infinite additive group, no translation-invariant `PMF` exists
(`translationInvariant Key = ∅`), making privacy over it vacuous. -/
@[expose] def translationInvariant (Key : Type*) [Add Key] : SourceClass Key :=
  { P | ∀ δ : Key, P.map (· + δ) = P }

/-- Uniform key sampling belongs to `SourceClass.translationInvariant` for every finite additive
group. -/
theorem uniformOfFintype_mem_translationInvariant (Key : Type*)
    [AddGroup Key] [Fintype Key] :
    uniformOfFintype Key ∈ translationInvariant Key := fun δ =>
  uniformOfFintype_map_add_right δ

end SourceClass

namespace AccessStructure

/-- If translating the key by `δ` carries the view of the coalition `s` on the secret `m₀` to its
view on `m₁`, and the key source `Q` is invariant under that translation, then `s` has the same
view distribution on `m₀` and `m₁`. -/
theorem viewDistOf_eq_of_map_add_eq {Secret Key Party : Type*} {Share : Party → Type*} [Add Key]
    {Q : PMF Key} {δ : Key} (hQ : Q.map (· + δ) = Q)
    {share : Key → Secret → (i : Party) → Share i} {s : Finset Party} {m₀ m₁ : Secret}
    (hshift : ∀ k, (fun i : s => share k m₀ i.val) = fun i : s => share (k + δ) m₁ i.val) :
    viewDistOf Q share s m₀ = viewDistOf Q share s m₁ := by
  conv_rhs => rw [← hQ]
  simp only [viewDistOf, PMF.map_comp]
  congr 1
  funext k
  exact hshift k

end AccessStructure

end Cslib.Crypto.Protocols.SecretSharing
