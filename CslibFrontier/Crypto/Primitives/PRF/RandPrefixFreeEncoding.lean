/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.BitString.Pad10Star
import CslibFrontier.Foundations.Data.List.ModifyLast
public import Cslib.Probability.PMF
import CslibFrontier.Probability.PMF.Uniform

/-!
# Randomized prefix-free encodings

Boneh and Shoup turn a PRF that is secure only on prefix-free query sets into a fully secure one
by encoding its inputs with a keyed encoding that is prefix-free with high probability
([BonehShoup2023], §6.7, pp. 236–237, and §6.10, p. 242). This file defines the notion and proves
the collision bounds of the book's two examples. Theorem 6.9, the PRF built from such an encoding,
is not proved here.

## Main definitions

* `PrefixCompatible x y` is Definition 6.5, `x ∼ y`: one of the lists is a prefix of the other.
* `IsRandPrefixFreeEncoding seed rpf ε` is Definition 6.6: `rpf k m` is never empty, and for
  distinct messages `m₀ ≠ m₁` the probability over `k ← seed` that `rpf k m₀ ∼ rpf k m₁` is at
  most `ε`. The encodings need not be injective for a fixed key, as the book remarks.
* `cmacRpf n (k₁, k₂)` is CMAC's encoding of a bit string (§6.10): a message whose length is a
  positive multiple of `n` is cut into `n`-bit blocks and `k₁` is added to the last; any other
  message is padded with `1 ‖ 0^*` (`Cslib.BitString.pad10star`) and `k₂` is added to the last
  block.

## Main results

* `isRandPrefixFreeEncoding_modifyLast_add`: adding a uniform key to the last block of a
  non-empty message, `rpf(k, (a₁, …, aᵥ)) = (a₁, …, aᵥ₋₁, aᵥ ⊕ k)`, is a randomized
  `1/|X|`-prefix-free encoding (§6.7, "A simple rpf").
* `isRandPrefixFreeEncoding_cmacRpf`: for `0 < n` and two independent uniform keys, CMAC's
  encoding is randomized `2⁻ⁿ`-prefix-free.
* `length_cmacRpf_le`: for `0 < n` and `1 ≤ ℓ`, CMAC's encoding of a message of at most `nℓ` bits
  has at most `ℓ` blocks, the book's codomain.

## Differences from the book

Encodings take values in `List X` and Definition 6.6's bound `≤ ℓ` on the number of blocks is a
separate length lemma; non-emptiness is part of the definition. Definition 6.6 is stated for any
key law `seed : PMF K` and any `ε : ℝ≥0∞`; the book draws `k` uniformly and takes `0 ≤ ε ≤ 1`.
The simple encoding is proved for every finite additive group `X` (for `Cslib.BitString n`, `+` is
XOR) on the non-empty lists; on all lists it fails, since `[]` is a prefix of everything. The CMAC
encoding needs `0 < n`, is defined on every bit string, and its length bound needs `1 ≤ ℓ`; with a
single key `k₁ = k₂` the empty message and `1 ‖ 0^(n-1)` collide for every key. Counterexamples
for these hypotheses are in `CslibFrontierTests.Crypto.RandPrefixFreeEncoding`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], version 0.6,
  Definitions 6.5 and 6.6 and §6.7 (pp. 236–237), and §6.10 (p. 242).
-/

public section

open scoped ENNReal

namespace Cslib.Crypto.PRF

open Cslib.Probability

/-! ### Definitions 6.5 and 6.6 -/

/-- Prefix compatibility `x ∼ y` ([BonehShoup2023], Definition 6.5): `x` is a prefix of `y` or `y`
is a prefix of `x`. -/
@[expose]
def PrefixCompatible {X : Type*} (x y : List X) : Prop :=
  x <+: y ∨ y <+: x

instance {X : Type*} [DecidableEq X] (x y : List X) : Decidable (PrefixCompatible x y) :=
  inferInstanceAs (Decidable (x <+: y ∨ y <+: x))

theorem prefixCompatible_comm {X : Type*} (x y : List X) :
    PrefixCompatible x y ↔ PrefixCompatible y x :=
  or_comm

/-- A randomized `ε`-prefix-free encoding ([BonehShoup2023], Definition 6.6): every encoding is
non-empty, and for distinct messages the probability over `k ← seed` that their encodings are
prefix-compatible is at most `ε`. The bound on the number of blocks is not part of the definition;
the book also draws `k` uniformly and takes `ε ≤ 1`. -/
structure IsRandPrefixFreeEncoding {K M X : Type*} (seed : PMF K) (rpf : K → M → List X)
    (ε : ℝ≥0∞) : Prop where
  ne_nil : ∀ k m, rpf k m ≠ []
  prob_le : ∀ ⦃m₀ m₁⦄, m₀ ≠ m₁ →
    seed.toOuterMeasure {k | PrefixCompatible (rpf k m₀) (rpf k m₁)} ≤ ε

namespace IsRandPrefixFreeEncoding

variable {K M M' X : Type*} {seed : PMF K} {rpf : K → M → List X} {ε : ℝ≥0∞}

/-- Restricting a randomized prefix-free encoding along an injection of messages, for instance to
the messages of bounded length, keeps its bound. -/
theorem comp_injective (h : IsRandPrefixFreeEncoding seed rpf ε) {e : M' → M}
    (he : Function.Injective e) : IsRandPrefixFreeEncoding seed (fun k m => rpf k (e m)) ε :=
  ⟨fun k m => h.ne_nil k (e m), fun _ _ hm => h.prob_le (he.ne hm)⟩

/-- For a uniform key on a finite type, it suffices to count: if at most `c` keys make the
encodings of any two distinct messages prefix-compatible, the encoding is `c / |K|`-prefix-free. -/
theorem of_card_le [Fintype K] [Nonempty K] [DecidableEq X] (hne : ∀ k m, rpf k m ≠ []) {c : ℕ}
    (hc : ∀ m₀ m₁, m₀ ≠ m₁ →
      (Finset.univ.filter fun k => PrefixCompatible (rpf k m₀) (rpf k m₁)).card ≤ c) :
    IsRandPrefixFreeEncoding (PMF.uniformOfFintype K) rpf (c / Fintype.card K) := by
  refine ⟨hne, fun m₀ m₁ hm => ?_⟩
  rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype, div_eq_mul_inv]
  gcongr
  exact_mod_cast hc m₀ m₁ hm

end IsRandPrefixFreeEncoding

/-! ### Adding a key to the last block -/

section ModifyLast

variable {X : Type*} [AddGroup X]

/-- If the encoding of a shorter non-empty list is a prefix of that of a longer one, the key added
to the shorter list is determined by the two lists. -/
private theorem exists_key_eq_of_length_lt {l₀ l₁ : List X} (hl₀ : l₀ ≠ [])
    (hlt : l₀.length < l₁.length) : ∃ c : X, ∀ c₀ c₁ : X,
      PrefixCompatible (l₀.modifyLast (· + c₀)) (l₁.modifyLast (· + c₁)) → c₀ = c := by
  obtain ⟨init, a, rfl⟩ := (List.eq_nil_or_concat l₀).resolve_left hl₀
  simp only [List.concat_eq_append, List.length_append, List.length_singleton] at hlt
  refine ⟨-a + l₁[init.length]'(by omega), fun c₀ c₁ hc => ?_⟩
  rcases hc with hpre | hpre
  · rw [List.concat_eq_append, List.modifyLast_concat] at hpre
    have hget := hpre.getElem (i := init.length) (by simp)
    rw [List.getElem_concat_length rfl, List.getElem_modifyLast,
      ite_eq_right (by omega)] at hget
    exact eq_neg_add_of_add_eq hget
  · have := hpre.length_le
    simp only [List.concat_eq_append, List.length_modifyLast, List.length_append,
      List.length_singleton] at this
    omega

/-- If two lists of equal length are prefix-compatible after adding keys to their last blocks, the
two keys differ by an amount fixed by the lists, and they are equal only when the lists are. -/
private theorem exists_key_eq_add_of_length_eq {l₀ l₁ : List X} (hl₀ : l₀ ≠ [])
    (hlen : l₀.length = l₁.length) : ∃ d : X, ∀ c₀ c₁ : X,
      PrefixCompatible (l₀.modifyLast (· + c₀)) (l₁.modifyLast (· + c₁)) →
        c₀ = d + c₁ ∧ (c₀ = c₁ → l₀ = l₁) := by
  obtain ⟨i₀, a₀, rfl⟩ := (List.eq_nil_or_concat l₀).resolve_left hl₀
  obtain ⟨i₁, a₁, rfl⟩ := (List.eq_nil_or_concat l₁).resolve_left fun h => by simp [h] at hlen
  simp only [List.concat_eq_append, List.length_append, List.length_singleton,
    Nat.add_right_cancel_iff] at hlen
  refine ⟨-a₀ + a₁, fun c₀ c₁ hc => ?_⟩
  simp only [List.concat_eq_append, List.modifyLast_concat] at hc
  have heq : i₀ ++ [a₀ + c₀] = i₁ ++ [a₁ + c₁] :=
    hc.elim (fun h => h.eq_of_length (by simp [hlen]))
      fun h => (h.eq_of_length (by simp [hlen])).symm
  obtain ⟨rfl, hlast⟩ := List.append_inj heq hlen
  have hlast' := List.head_eq_of_cons_eq hlast
  refine ⟨by rw [add_assoc, ← eq_neg_add_of_add_eq hlast'], ?_⟩
  rintro rfl
  rw [add_right_cancel hlast']

end ModifyLast

/-- Adding a uniform key to the last block is a randomized `1/|X|`-prefix-free encoding of the
non-empty lists ([BonehShoup2023], §6.7, "A simple rpf", pp. 236–237), for every finite additive
group `X`; the book's is `X = {0,1}ⁿ` under XOR. -/
theorem isRandPrefixFreeEncoding_modifyLast_add (X : Type*) [Fintype X] [Nonempty X]
    [AddGroup X] :
    IsRandPrefixFreeEncoding (PMF.uniformOfFintype X)
      (fun k (m : {m : List X // m ≠ []}) => m.1.modifyLast (· + k))
      (Fintype.card X : ℝ≥0∞)⁻¹ := by
  classical
  have key : ∀ m₀ m₁ : {m : List X // m ≠ []}, m₀.1.length < m₁.1.length →
      (Finset.univ.filter fun k : X =>
        PrefixCompatible (m₀.1.modifyLast (· + k)) (m₁.1.modifyLast (· + k))).card ≤ 1 := by
    intro m₀ m₁ hlt
    obtain ⟨c, hc⟩ := exists_key_eq_of_length_lt m₀.2 hlt
    exact Finset.card_le_one.mpr fun k₀ hk₀ k₁ hk₁ =>
      (hc _ _ (Finset.mem_filter.mp hk₀).2).trans (hc _ _ (Finset.mem_filter.mp hk₁).2).symm
  simpa using IsRandPrefixFreeEncoding.of_card_le (c := 1)
    (rpf := fun k (m : {m : List X // m ≠ []}) => m.1.modifyLast (· + k))
    (fun k m => by simpa [← List.length_pos_iff] using m.2) fun m₀ m₁ hm => by
      rcases lt_trichotomy m₀.1.length m₁.1.length with hlt | heq | hgt
      · exact key m₀ m₁ hlt
      · obtain ⟨d, hd⟩ := exists_key_eq_add_of_length_eq m₀.2 heq
        refine (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun k _ hk =>
          hm (Subtype.ext ((hd k k hk).2 rfl)))).trans_le zero_le_one
      · simpa only [prefixCompatible_comm] using key m₁ m₀ hgt

/-! ### CMAC's encoding -/

/-- The unkeyed part of CMAC's encoding ([BonehShoup2023], §6.10, p. 242): `(true, blocks)` when
`|m|` is a positive multiple of `n`, with `m` cut into `n`-bit blocks, and otherwise
`(false, blocks of m ‖ 1 ‖ 0^*)`. The flag selects the key added to the last block. -/
@[expose]
def cmacCore (n : ℕ) (m : List Bool) : Bool × List (BitString n) :=
  if 0 < m.length ∧ n ∣ m.length then (true, BitString.toBlocks n m)
  else (false, BitString.toBlocks n (BitString.pad10star n m))

/-- CMAC's randomized prefix-free encoding ([BonehShoup2023], §6.10, p. 242). Cut `m` into `n`-bit
blocks; if `|m|` is a positive multiple of `n`, add `k₁` to the last block, and otherwise pad `m`
with `1 ‖ 0^*` to a positive multiple of `n` and add `k₂` to the last block. -/
@[expose]
def cmacRpf (n : ℕ) (k : BitString n × BitString n) (m : List Bool) : List (BitString n) :=
  (cmacCore n m).2.modifyLast (· + if (cmacCore n m).1 then k.1 else k.2)

private theorem cmacCore_snd_ne_nil {n : ℕ} (hn : 0 < n) (m : List Bool) :
    (cmacCore n m).2 ≠ [] := by
  unfold cmacCore
  split_ifs with h
  · rw [← List.length_pos_iff, BitString.length_toBlocks]
    exact Nat.div_pos (Nat.le_of_dvd h.1 h.2) hn
  · exact BitString.toBlocks_pad10star_ne_nil hn m

private theorem cmacCore_injective {n : ℕ} (hn : 0 < n) : Function.Injective (cmacCore n) := by
  intro m₀ m₁ h
  unfold cmacCore at h
  split_ifs at h with h₀ h₁ h₁
  · exact BitString.toBlocks_injOn h₀.2 h₁.2 (congrArg Prod.snd h)
  · simp at h
  · simp at h
  · exact BitString.toBlocks_pad10star_injective hn (congrArg Prod.snd h)

/-- CMAC's encoding has the book's codomain: a message of at most `nℓ` bits has at most `ℓ`
blocks, for `0 < n` and `1 ≤ ℓ`. -/
theorem length_cmacRpf_le {n ℓ : ℕ} (hn : 0 < n) (hℓ : 1 ≤ ℓ) (k : BitString n × BitString n)
    {m : List Bool} (hm : m.length ≤ n * ℓ) : (cmacRpf n k m).length ≤ ℓ := by
  rw [cmacRpf, List.length_modifyLast, cmacCore]
  split_ifs with h
  · simpa using Nat.div_le_of_le_mul hm
  · have hlt : m.length < n * ℓ :=
      (Nat.eq_zero_or_pos m.length).elim (fun h0 => h0.symm ▸ Nat.mul_pos hn hℓ)
        fun hpos => lt_of_le_of_ne hm fun heq => h ⟨hpos, ℓ, heq⟩
    have := BitString.length_pad10star_le hn m
    simpa [Nat.lt_succ_iff] using Nat.div_lt_of_lt_mul (k := ℓ + 1) (by
      rw [Nat.mul_succ]
      omega)

/-- Selecting a key by a flag. -/
private abbrev selectKey {X : Type*} (b : Bool) (k : X × X) : X := if b then k.1 else k.2

/-- At most `|X|` key pairs have their `b`-selected key a fixed function of the other one. -/
private theorem card_filter_selectKey_le {X : Type*} [Fintype X] (b : Bool)
    (φ : X → X) (s : Finset (X × X)) (hs : ∀ k ∈ s, selectKey b k = φ (selectKey (!b) k)) :
    s.card ≤ Fintype.card X := by
  classical
  refine (Finset.card_le_card (t := Finset.univ.image fun x : X =>
      if b then (φ x, x) else (x, φ x)) fun k hk => ?_).trans (Finset.card_image_le.trans (by simp))
  have h := hs k hk
  refine Finset.mem_image.mpr ⟨selectKey (!b) k, Finset.mem_univ _, ?_⟩
  cases b <;> simp only [selectKey, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte] at h ⊢ <;> rw [← h]

/-- CMAC's encoding with two independent uniform keys is a randomized `2⁻ⁿ`-prefix-free encoding
of all bit strings, for `0 < n` ([BonehShoup2023], §6.10, p. 242). -/
theorem isRandPrefixFreeEncoding_cmacRpf {n : ℕ} (hn : 0 < n) :
    IsRandPrefixFreeEncoding (PMF.uniformOfFintype (BitString n × BitString n)) (cmacRpf n)
      ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  have hratio : ((2 : ℝ≥0∞) ^ n)⁻¹ =
      Fintype.card (BitString n) / Fintype.card (BitString n × BitString n) := by
    rw [Fintype.card_prod, Cslib.BitString.card, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)),
      mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by simp), mul_one]
  rw [hratio]
  refine IsRandPrefixFreeEncoding.of_card_le (c := Fintype.card (BitString n)) (rpf := cmacRpf n)
    (fun _ m => by simpa [cmacRpf, ← List.length_pos_iff] using cmacCore_snd_ne_nil hn m)
    fun m₀ m₁ hm => ?_
  have hne := (cmacCore_injective hn).ne hm
  have hL₀ := cmacCore_snd_ne_nil hn m₀
  have hL₁ := cmacCore_snd_ne_nil hn m₁
  unfold cmacRpf
  generalize cmacCore n m₀ = c₀ at hne hL₀
  generalize cmacCore n m₁ = c₁ at hne hL₁
  obtain ⟨b₀, L₀⟩ := c₀
  obtain ⟨b₁, L₁⟩ := c₁
  dsimp only at hL₀ hL₁ ⊢
  rcases lt_trichotomy L₀.length L₁.length with hlt | heq | hgt
  · obtain ⟨c, hc⟩ := exists_key_eq_of_length_lt hL₀ hlt
    exact card_filter_selectKey_le b₀ (fun _ => c) _ fun k hk =>
      hc _ _ (Finset.mem_filter.mp hk).2
  · obtain ⟨d, hd⟩ := exists_key_eq_add_of_length_eq hL₀ heq
    rcases eq_or_ne b₀ b₁ with rfl | hb
    · exact (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun k _ hk =>
        hne (congrArg (b₀, ·) ((hd _ _ hk).2 rfl)))).trans_le (Nat.zero_le _)
    · obtain rfl : b₁ = !b₀ := by cases b₀ <;> cases b₁ <;> first | rfl | contradiction
      exact card_filter_selectKey_le b₀ (d + ·) _ fun k hk =>
        (hd _ _ (Finset.mem_filter.mp hk).2).1
  · obtain ⟨c, hc⟩ := exists_key_eq_of_length_lt hL₁ hgt
    exact card_filter_selectKey_le b₁ (fun _ => c) _ fun k hk =>
      hc _ _ ((prefixCompatible_comm _ _).mp (Finset.mem_filter.mp hk).2)

end Cslib.Crypto.PRF
