/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.InformationTheory.Coding.PrefixFree
import CslibFrontier.Foundations.Data.List.Append

/-!
# Deterministic Prefix-Free Encodings

Prefix-free encodings ([BonehShoup2023], Sections 6.6–6.6.1, pp. 235–236): functions into
nonempty lists of blocks whose range is a prefix-free set (`InformationTheory.IsPrefixFree`).

## Main definitions

* `Cslib.Crypto.PRF.IsPrefixFreeEncoding`: predicate for an injective encoding into nonempty lists
  whose range is prefix-free.
* `Cslib.Crypto.PRF.stopBitEncode`: Method 2 stop-bit encoding (§6.6.1, p. 236), appending `false`
  to every block except the last and `true` to the last block.
* `Cslib.Crypto.PRF.separatingBlock`: a common extension block for two queries.
* `Cslib.Crypto.PRF.findFreshBlock`: bounded search in an indexed block alphabet.
* `Cslib.Crypto.PRF.freshBatchBlock`: a block absent from a batch of queries.

## Main results

* `Cslib.Crypto.PRF.IsPrefixFreeEncoding.iff_forall_prefix`: characterization in terms of
  nonemptiness and prefix-implication `pf m₁ <+: pf m₂ → m₁ = m₂`.
* `Cslib.Crypto.PRF.IsPrefixFreeEncoding.comp_injective`: precomposing with an injective map
  preserves `IsPrefixFreeEncoding`.
* `Cslib.Crypto.PRF.length_stopBitEncode`: `stopBitEncode` preserves the number of blocks.
* `Cslib.Crypto.PRF.isPrefixFreeEncoding_stopBitEncode`: `stopBitEncode` is a prefix-free encoding
  on nonempty lists of `n`-bit blocks.
* `Cslib.Crypto.PRF.separatingBlock_prefix_incomparable`: the common extension makes two distinct
  queries prefix-incomparable.
* `Cslib.Crypto.PRF.isPrefixFree_append_of_notMem_flatten`: appending an absent block makes
  a batch of block lists prefix-free.
* `Cslib.Crypto.PRF.isPrefixFree_append_of_freshBatchBlock_eq_some`: every block returned by
  the search makes the extended batch prefix-free.
* `Cslib.Crypto.PRF.isPrefixFree_append_freshBatchBlock`: the bounded search succeeds when
  there are more possible blocks than block occurrences, and its extension is prefix-free.

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
  Sections 6.6–6.6.1, pp. 235–236, and 7.2.2, pp. 258–260.
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

/-- Choose a common block to append to two queries. At the end of the shorter query, the
chosen block differs from the block at that position in the longer query. The two candidate
blocks are supplied by the caller. This is a preparation step for [BonehShoup2023], v0.6,
Theorem 7.3 (printed pp. 258–259), using one extra block even for incomparable queries. -/
@[expose] def separatingBlock {X : Type*} [BEq X] (a b : X) (u v : List X) : X :=
  let next := if u.length ≤ v.length then v.getD u.length a else u.getD v.length a
  if next == a then b else a

private theorem not_prefix_append_separatingBlock_of_length_le {X : Type*} [BEq X]
    [LawfulBEq X] {a b : X} (hab : a ≠ b) {u v : List X} (hne : u ≠ v)
    (hlen : u.length ≤ v.length) :
    ¬ u ++ [separatingBlock a b u v] <+: v ++ [separatingBlock a b u v] := by
  intro hp
  rcases hlen.eq_or_lt with heq | hlt
  · have hs := hp.eq_of_length (by simp only [List.length_append, heq])
    exact hne (List.append_cancel_right hs)
  · have hmem := List.prefix_iff_getElem?.mp hp u.length (by simp)
    have hnext : v[u.length] = separatingBlock a b u v := by
      apply Option.some.inj
      simpa only [List.getElem?_append_left hlt, List.getElem_append_right (le_refl u.length),
        Nat.sub_self, List.getElem_cons_zero, List.getElem?_eq_getElem hlt] using hmem
    have hget : v.getD u.length a = v[u.length] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    rw [separatingBlock, ite_eq_left hlen, hget] at hnext
    split_ifs at hnext with h
    · exact hab ((beq_iff_eq.mp h).symm.trans hnext)
    · exact h (beq_iff_eq.mpr hnext)

/-- Appending the chosen common block makes two distinct queries prefix-incomparable. -/
theorem separatingBlock_prefix_incomparable {X : Type*} [BEq X] [LawfulBEq X]
    {a b : X} (hab : a ≠ b) {u v : List X} (hne : u ≠ v) :
    let c := separatingBlock a b u v
    (¬ u ++ [c] <+: v ++ [c]) ∧ (¬ v ++ [c] <+: u ++ [c]) := by
  dsimp only
  rcases lt_trichotomy u.length v.length with h | h | h
  · refine ⟨not_prefix_append_separatingBlock_of_length_le hab hne h.le, ?_⟩
    intro hp
    have hle := hp.length_le
    simp only [List.length_append, List.length_singleton] at hle
    omega
  · refine ⟨not_prefix_append_separatingBlock_of_length_le hab hne h.le, ?_⟩
    intro hp
    have hs := hp.eq_of_length (by simp only [List.length_append, h])
    exact hne (List.append_cancel_right hs).symm
  · have hc : separatingBlock a b u v = separatingBlock a b v u := by
      simp only [separatingBlock, ite_eq_right (Nat.not_le_of_gt h), ite_eq_left h.le]
    refine ⟨?_, hc ▸ not_prefix_append_separatingBlock_of_length_le hab hne.symm h.le⟩
    intro hp
    have hle := hp.length_le
    simp only [List.length_append, List.length_singleton] at hle
    omega

/-- Find the first unused block among at most `used.length + 1` entries in an indexed alphabet. -/
@[expose] def findFreshBlock {α : Type*} [BEq α] {size : ℕ} (blockAt : Fin size → α)
    (used : List α) : Option α :=
  let candidates := (List.finRange (min size (used.length + 1))).map fun i =>
    blockAt (Fin.castLE (min_le_left _ _) i)
  candidates.find? fun block => !used.contains block

/-- Search the first `min (2 ^ n) (b + 1)` bit strings for a block absent from `messages`, where
`b` counts all block occurrences. This is the block-selection step of [BonehShoup2023], v0.6,
Theorem 7.4 (printed pp. 259–260). It returns `none` when the batch uses the whole alphabet. -/
@[expose] def freshBatchBlock {n : ℕ} (messages : List (List (BitString n))) :
    Option (BitString n) :=
  findFreshBlock (BitString.equivFin n).symm messages.flatten

/-- An absent block delimits each message, so appending it to the batch makes a prefix-free set. -/
theorem isPrefixFree_append_of_notMem_flatten {α : Type*}
    {messages : List (List α)} {block : α} (hfresh : block ∉ messages.flatten) :
    InformationTheory.IsPrefixFree ((fun msg => msg ++ [block]) '' {msg | msg ∈ messages}) := by
  have hnotMem {msg} (hm : msg ∈ messages) : block ∉ msg :=
    fun hb => hfresh (List.mem_flatten.mpr ⟨msg, hm, hb⟩)
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ ⟨tail, htail⟩
  have hsplit : u ++ block :: tail = v ++ block :: [] := by
    simpa only [List.append_assoc, List.singleton_append] using htail
  rw [((List.append_cons_inj_of_notMem_prefix (hnotMem hu) (hnotMem hv)).mp hsplit).1]

/-- Appending a block returned by the batch search makes the extended messages prefix-free. -/
theorem isPrefixFree_append_of_freshBatchBlock_eq_some {n : ℕ}
    {messages : List (List (BitString n))} {block : BitString n}
    (hblock : freshBatchBlock messages = some block) :
    InformationTheory.IsPrefixFree ((fun msg => msg ++ [block]) '' {msg | msg ∈ messages}) := by
  unfold freshBatchBlock findFreshBlock at hblock
  exact isPrefixFree_append_of_notMem_flatten (by simpa using List.find?_some hblock)

/-- The batch search supplies a fresh delimiter whenever the total block count is below the
alphabet size. Appending it to every message gives a prefix-free set, including when an original
message is empty or is a prefix of another. This is the query preparation step for (7.9). -/
theorem isPrefixFree_append_freshBatchBlock {n : ℕ} {messages : List (List (BitString n))}
    (hsize : messages.flatten.length < 2 ^ n) :
    ∃ block, freshBatchBlock messages = some block ∧
      InformationTheory.IsPrefixFree ((fun msg => msg ++ [block]) '' {msg | msg ∈ messages}) := by
  let used := messages.flatten
  let candidate := (BitString.equivFin n).symm ∘ Fin.castLE (min_le_left (2 ^ n) (used.length + 1))
  let candidates := (List.finRange (min (2 ^ n) (used.length + 1))).map candidate
  have hfind : (freshBatchBlock messages).isSome := by
    change (candidates.find? fun block => !used.contains block).isSome
    rw [List.find?_isSome]
    by_contra! hnone
    have hsubset : candidates.toFinset ⊆ used.toFinset := by
      intro block hb
      simpa using hnone block (List.mem_toFinset.mp hb)
    have hinj : Function.Injective candidate :=
      (BitString.equivFin n).symm.injective.comp (Fin.castLE_injective _)
    have hnodup : candidates.Nodup := (List.nodup_finRange _).map hinj
    have hle := (Finset.card_le_card hsubset).trans (List.toFinset_card_le used)
    rw [List.toFinset_card_of_nodup hnodup] at hle
    simp only [candidates, List.length_map, List.length_finRange,
      min_eq_right (Nat.succ_le_of_lt (show used.length < 2 ^ n from hsize))] at hle
    omega
  obtain ⟨block, hblock⟩ := Option.isSome_iff_exists.mp hfind
  exact ⟨block, hblock, isPrefixFree_append_of_freshBatchBlock_eq_some hblock⟩

end Cslib.Crypto.PRF
