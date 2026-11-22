/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.InformationTheory.Coding.PrefixFree

/-!
# Deterministic Prefix-Free Encodings

Prefix-free encodings ([BonehShoup2023], Sections 6.6–6.6.1, pp. 235–236): functions into
nonempty lists of blocks whose range is a prefix-free set (`InformationTheory.IsPrefixFree`).

## Main definitions

* `Cslib.Crypto.PRF.IsPrefixFreeEncoding`: predicate for an injective encoding into nonempty lists
  whose range is prefix-free.
* `Cslib.Crypto.PRF.stopBitEncode`: Method 2 stop-bit encoding (§6.6.1, p. 236), appending `false`
  to every block except the last and `true` to the last block.

## Main results

* `Cslib.Crypto.PRF.IsPrefixFreeEncoding.iff_forall_prefix`: characterization in terms of
  nonemptiness and prefix-implication `pf m₁ <+: pf m₂ → m₁ = m₂`.
* `Cslib.Crypto.PRF.IsPrefixFreeEncoding.comp_injective`: precomposing with an injective map
  preserves `IsPrefixFreeEncoding`.
* `Cslib.Crypto.PRF.length_stopBitEncode`: `stopBitEncode` preserves the number of blocks.
* `Cslib.Crypto.PRF.isPrefixFreeEncoding_stopBitEncode`: `stopBitEncode` is a prefix-free encoding
  on nonempty lists of `n`-bit blocks.

## Differences from the book

* The codomain is `List X` with nonemptiness bundled and length bounds `≤ ℓ` proved separately
  (`length_stopBitEncode`) rather than encoded in a bounded-list type `X^{≤ℓ}`.
* `stopBitEncode` maps `n`-bit payload blocks to `(n + 1)`-bit output blocks (`n : ℕ`), which
  corresponds to the book's `(n - 1)`-bit payload blocks and `n`-bit output blocks with `n ≥ 1`.
* Empty messages are explicitly excluded by the subtype `{m : List (BitString n) // m ≠ []}`,
  matching `X_{>0}^{≤ℓ}`.
* Method 1 (`isPrefixFreeEncoding_prependLength`, §6.6.1, p. 235) lives in
  `CslibFrontier.Crypto.Primitives.BlockCipher.LengthPrependedCBCMAC`. Theorem 6.8 and randomized
  prefix-free encodings (§6.7, §6.10) are not included here.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Version 0.6,
  Sections 6.6–6.6.1, pp. 235–236.
-/

public section

namespace Cslib.Crypto.PRF

/-- A function `pf : M → List X` is a **prefix-free encoding** ([BonehShoup2023], Section 6.6,
p. 235) if every output is nonempty, `pf` is injective, and `Set.range pf` is a prefix-free set. -/
structure IsPrefixFreeEncoding {M X : Type*} (pf : M → List X) : Prop where
  ne_nil : ∀ m, pf m ≠ []
  injective : Function.Injective pf
  isPrefixFree_range : InformationTheory.IsPrefixFree (Set.range pf)

namespace IsPrefixFreeEncoding

variable {M M' X : Type*} {pf : M → List X}

/-- A function is a prefix-free encoding iff every output is nonempty and `pf m₁ <+: pf m₂`
implies `m₁ = m₂`. -/
theorem iff_forall_prefix :
    IsPrefixFreeEncoding pf ↔ (∀ m, pf m ≠ []) ∧ (∀ m₁ m₂, pf m₁ <+: pf m₂ → m₁ = m₂) := by
  constructor
  · intro h
    refine ⟨h.ne_nil, ?_⟩
    exact fun m₁ m₂ hpre => h.injective (h.isPrefixFree_range _ ⟨m₁, rfl⟩ _ ⟨m₂, rfl⟩ hpre)
  · rintro ⟨hne, hall⟩
    refine ⟨hne, fun m₁ m₂ heq => hall m₁ m₂ (heq ▸ List.prefix_refl _), ?_⟩
    rintro _ ⟨m₁, rfl⟩ _ ⟨m₂, rfl⟩ hpre
    rw [hall m₁ m₂ hpre]

/-- Precomposing a prefix-free encoding with an injective map yields a prefix-free encoding. -/
theorem comp_injective (h : IsPrefixFreeEncoding pf) {e : M' → M} (he : Function.Injective e) :
    IsPrefixFreeEncoding (pf ∘ e) where
  ne_nil m := h.ne_nil (e m)
  injective := h.injective.comp he
  isPrefixFree_range := h.isPrefixFree_range.anti (Set.range_comp_subset_range _ _)

end IsPrefixFreeEncoding

/-- Method 2 stop-bit encoding ([BonehShoup2023], Section 6.6.1, p. 236): appends `false` to every
block except the last and `true` to the last block, mapping `n`-bit blocks to `(n + 1)`-bit blocks.
Empty input maps to `[]`. -/
@[expose]
def stopBitEncode {n : ℕ} : List (BitString n) → List (BitString (n + 1))
  | [] => []
  | [a] => [Fin.snoc (α := fun _ => Bool) a true]
  | a :: b :: rest => Fin.snoc (α := fun _ => Bool) a false :: stopBitEncode (b :: rest)

/-- `stopBitEncode` preserves the number of blocks. -/
@[simp]
theorem length_stopBitEncode {n : ℕ} :
    ∀ (m : List (BitString n)), (stopBitEncode m).length = m.length
  | [] => rfl
  | [_] => rfl
  | _ :: b :: rest => by simp [stopBitEncode, length_stopBitEncode (b :: rest)]

private theorem stopBitEncode_ne_nil {n : ℕ} :
    ∀ {m : List (BitString n)}, m ≠ [] → stopBitEncode m ≠ []
  | [], h => absurd rfl h
  | [_], _ => by simp [stopBitEncode]
  | _ :: _ :: _, _ => by simp [stopBitEncode]

private theorem eq_of_stopBitEncode_prefix {n : ℕ} :
    ∀ {m₁ m₂ : List (BitString n)}, m₁ ≠ [] → stopBitEncode m₁ <+: stopBitEncode m₂ → m₁ = m₂
  | [], _, h, _ => absurd rfl h
  | [_], [], _, hp => by simp [stopBitEncode] at hp
  | _ :: _ :: _, [], _, hp => by simp [stopBitEncode] at hp
  | [_], [_], _, hp => by
    simp only [stopBitEncode, List.cons_prefix_cons] at hp
    rw [(Fin.snoc_injective2 hp.1).1]
  | [_], _ :: _ :: _, _, hp => by
    simp only [stopBitEncode, List.cons_prefix_cons] at hp
    exact absurd (Fin.snoc_injective2 hp.1).2 (by decide)
  | _ :: _ :: _, [_], _, hp => by
    simp only [stopBitEncode, List.cons_prefix_cons] at hp
    exact absurd (Fin.snoc_injective2 hp.1).2 (by decide)
  | _ :: _ :: _, _ :: _ :: _, _, hp => by
    simp only [stopBitEncode, List.cons_prefix_cons] at hp
    rw [(Fin.snoc_injective2 hp.1).1, eq_of_stopBitEncode_prefix (by simp) hp.2]

/-- **Method 2 (stop bits)** ([BonehShoup2023], Section 6.6.1, p. 236): `stopBitEncode` is a
prefix-free encoding on nonempty lists of `n`-bit blocks. -/
theorem isPrefixFreeEncoding_stopBitEncode (n : ℕ) :
    IsPrefixFreeEncoding (fun m : {m : List (BitString n) // m ≠ []} => stopBitEncode m.1) :=
  IsPrefixFreeEncoding.iff_forall_prefix.mpr
    ⟨fun m => stopBitEncode_ne_nil m.2,
      fun m₁ _ hp => Subtype.ext (eq_of_stopBitEncode_prefix m₁.2 hp)⟩

end Cslib.Crypto.PRF
