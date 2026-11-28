/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Prices.Law

/-!
# Identities with slots of one bit

The identities `Separation.Prices.WireId` in the form in which the proof of Theorem G.2 (thm:laws)
of *VP ≠ VNP over every field* [AnthropicVPVNP2026] uses them: slots of one bit, and all roles see
all copies (`Separation.Prices.BitId`, `Separation.Prices.WireId.bitId`).

## Main definitions

* `Separation.Prices.BitId`.

## Main results

* `Separation.Prices.WireId.bitId`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem G.2 of the paper; module `Nc.Price.LawF`
-/

@[expose] public section


namespace Cslib.Circuits.Arithmetic.Separation.Prices

open Cslib.PartyTensor Finset

/-- An identity that rewrites wires of one bit (slots): the form of `Nc.G.Law.law`. -/
def BitId (R : Type) [CommRing R] {V S N ι : Type} [Fintype V] [Fintype S] [Fintype N]
    [DecidableEq N] [Fintype ι] (a b : S → V) (c d : N → V) (len : ι → N → ℕ)
    (tab : ∀ (p : V) (i : ι), ({e // a e = p ∨ b e = p} → Bool) →
      ((ν : {ν // c ν = p ∨ d ν = p}) → Fin (len i ν) → Bool) → R) : Prop :=
  ∀ X : V → S → Bool, (if ∀ e, X (a e) e = X (b e) e then (1 : R) else 0) =
    ∑ i, ∑ g : ∀ ν, Fin (len i ν) → Bool, ∏ p, tab p i (fun e => X p e) (fun ν => g ν)

/-- Wires of several bits are several wires of one bit. -/
theorem WireId.bitId {R : Type} [CommRing R] {V E N ι : Type} [Fintype V] [Fintype E] [Fintype N]
    [DecidableEq N] [Fintype ι] {a b : E → V} {c d : N → V} {n : E → ℕ} {len : ι → N → ℕ}
    {tab : ∀ (i : ι) (p : V), (∀ e : {e // a e = p ∨ b e = p}, Fin (n e) → Bool) →
      (∀ ν : {ν // c ν = p ∨ d ν = p}, Fin (len i ν) → Bool) → R}
    (h : WireId R a b c d n len tab) :
    BitId R (fun s : Σ e, Fin (n e) => a s.1) (fun s : Σ e, Fin (n e) => b s.1) c d len
      (fun p i x g => tab i p (fun e k => x ⟨⟨e.1, k⟩, e.2⟩) g) := by
  intro X
  have h1 := h fun p e k => X p ⟨e.1, k⟩
  rw [← h1]
  congr 1
  refine propext ⟨fun h e => ?_, fun h s => ?_⟩
  · funext k
    exact h ⟨e, k⟩
  · exact congr_fun (h s.1) s.2

end Cslib.Circuits.Arithmetic.Separation.Prices
