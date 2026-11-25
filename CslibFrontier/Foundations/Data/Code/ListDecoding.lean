/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Density
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Set.Card
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Data.ENat.Basic
import Mathlib.Data.List.GetD

/-!
# List decoding

A *list code* encodes messages of a type `α` as words `ι → β` over an alphabet `β`, and its list
decoder turns every received word `w` into `L` candidate messages. The code *list decodes up to
radius `ρ`* if the candidates for `w` include every message whose codeword differs from `w` on at
most a `ρ` fraction of the coordinates [Arora and Barak, Chapter 19][AroraBarak09]; binary codes
are those with `β = Bool`. A word that agrees with the codeword of `x` on a `1 / 2 + δ` fraction of
the coordinates thus determines `x` up to `L` possibilities when the code list decodes up to radius
`1 / 2 - δ` (`Cslib.ListCode.ListDecodes.mem_candidates_of_half_add_le`): `x` is one of the at
most `L` candidates (`Cslib.ListCode.card_candidates_le`), and it is named by an index of
`⌈log₂ L⌉` bits (`Cslib.ListCode.ListDecodes.exists_decodeBits_eq_some`). This is how the
Nisan–Wigderson reconstruction recovers a message from a predictor of its codeword.

The combinatorial counterpart `Cslib.Code.IsListDecodable C ρ L` states that every Hamming ball of
relative radius `ρ` contains at most `L` codewords of `C : Set (ι → α)`. For an injective encoder
of a finite nonempty message type, this is equivalent to the existence of a `Cslib.ListCode` that
list decodes up to radius `ρ` (`Cslib.Code.isListDecodable_range_iff_exists_listCode`).

## Main definitions

* `Cslib.ListCode`: an encoder of messages as words over an alphabet with a list decoder.
* `Cslib.ListCode.ListDecodes`: list decoding up to a relative radius.
* `Cslib.ListCode.candidates`: the candidates for a received word.
* `Cslib.ListCode.decodeBits`: the candidate named by a binary index.
* `Cslib.Code.IsListDecodable`: combinatorial `(ρ, L)`-list-decodability of a code
  `C : Set (ι → α)`.

## Main results

* `Cslib.ListCode.card_candidates_le`: there are at most `L` candidates.
* `Cslib.ListCode.listDecodes_of_surjective`: a decoder listing every message list decodes at
  every radius.
* `Cslib.ListCode.ListDecodes.exists_decode_eq`,
  `Cslib.ListCode.ListDecodes.exists_decode_eq_of_half_add_le`: a message whose codeword
  agrees with the received word on enough coordinates is a candidate.
* `Cslib.ListCode.ListDecodes.exists_decodeBits_eq_some`: it is named by an index of
  `Nat.clog 2 L` bits.
* `Cslib.Code.isListDecodable_finset_iff`, `Cslib.Code.isListDecodable_iff_forall_finset`:
  finite-code and finite-subset characterizations of `IsListDecodable`.
* `Cslib.Code.IsListDecodable.mono`: monotonicity in code, radius, and list size.
* `Cslib.Code.isListDecodable_range_iff_exists_listCode`: equivalence between combinatorial
  `(ρ, L)`-list-decodability and `Cslib.ListCode.ListDecodes`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
-/

@[expose] public section

namespace Cslib

open Finset

/-- A *list code*: an encoder of messages of type `α` as words on the coordinates `ι` over the
alphabet `β`, with a list decoder returning `L` candidate messages for every received word. -/
structure ListCode (α ι β : Type*) (L : ℕ) where
  /-- The codeword of a message. -/
  encode : α → ι → β
  /-- The `k`-th candidate message for a received word. -/
  decode : (ι → β) → Fin L → α

namespace ListCode

variable {α ι β : Type*} {L : ℕ} (C : ListCode α ι β L)

/-- The code *list decodes up to radius `ρ`*: the candidates for a received word `w` include every
message whose codeword differs from `w` on at most a `ρ` fraction of the coordinates. -/
def ListDecodes [Fintype ι] [DecidableEq β] (ρ : ℝ) : Prop :=
  ∀ x w, (hammingDist (C.encode x) w : ℝ) ≤ ρ * Fintype.card ι → ∃ k, C.decode w k = x

/-- The candidates for the received word `w`, without repetitions. -/
def candidates [DecidableEq α] (w : ι → β) : Finset α :=
  univ.image (C.decode w)

/-- A message is a candidate for `w` exactly when the decoder returns it at some index. -/
@[simp]
theorem mem_candidates [DecidableEq α] {w : ι → β} {x : α} :
    x ∈ C.candidates w ↔ ∃ k, C.decode w k = x := by
  simp [candidates]

/-- **List size.** A received word has at most `L` candidates. -/
theorem card_candidates_le [DecidableEq α] (w : ι → β) : #(C.candidates w) ≤ L :=
  card_image_le.trans_eq (card_fin L)

/-- The candidate named by the binary index `b` of `Nat.clog 2 L` bits, read least significant bit
first: the `k`-th candidate for `w` if `b` spells a number `k < L`, and nothing otherwise. -/
def decodeBits (w : ι → β) (b : BitString (Nat.clog 2 L)) : Option α :=
  let k : Fin (2 ^ Nat.clog 2 L) := BitString.equivFin (Nat.clog 2 L) b
  if h : (k : ℕ) < L then some (C.decode w ⟨k, h⟩) else none

/-- **Short index.** Every candidate is named by an index of `Nat.clog 2 L` bits. -/
theorem exists_decodeBits_eq_some {w : ι → β} {x : α} (h : ∃ k, C.decode w k = x) :
    ∃ b : BitString (Nat.clog 2 L), C.decodeBits w b = some x := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨BitString.indexBits k, ?_⟩
  simp only [decodeBits, BitString.indexBits, Equiv.apply_symm_apply, Fin.val_castLE, k.isLt,
    ↓reduceDIte]

variable [Fintype ι] [DecidableEq β] {C}

/-- A decoder whose candidates enumerate all messages, whatever the received word, list decodes at
every radius: the list then has `L ≥ |α|` entries, so this only shows that list decoding is
satisfiable. -/
theorem listDecodes_of_surjective (h : ∀ w, Function.Surjective (C.decode w)) (ρ : ℝ) :
    C.ListDecodes ρ :=
  fun x w _ => h w x

/-- A list decoder up to radius `ρ` lists every message whose codeword agrees with the received
word on at least a `1 - ρ` fraction of the coordinates. -/
theorem ListDecodes.exists_decode_eq {ρ : ℝ} (hC : C.ListDecodes ρ) {x : α} {w : ι → β}
    (h : 1 - ρ ≤ (dens {i | C.encode x i = w i} : ℝ)) : ∃ k, C.decode w k = x := by
  refine hC x w ?_
  rw [hammingDist_eq_card_mul_one_sub_dens (𝕜 := ℝ), mul_comm]
  gcongr
  linarith

/-- A list decoder up to radius `1 / 2 - δ` lists every message whose codeword agrees with the
received word on at least a `1 / 2 + δ` fraction of the coordinates. -/
theorem ListDecodes.exists_decode_eq_of_half_add_le {δ : ℝ} (hC : C.ListDecodes (1 / 2 - δ))
    {x : α} {w : ι → β} (h : 1 / 2 + δ ≤ (dens {i | C.encode x i = w i} : ℝ)) :
    ∃ k, C.decode w k = x :=
  hC.exists_decode_eq (by linarith)

/-- A message whose codeword agrees with the received word on at least a `1 / 2 + δ` fraction of
the coordinates is among the candidates of a list decoder up to radius `1 / 2 - δ`. -/
theorem ListDecodes.mem_candidates_of_half_add_le [DecidableEq α] {δ : ℝ}
    (hC : C.ListDecodes (1 / 2 - δ)) {x : α} {w : ι → β}
    (h : 1 / 2 + δ ≤ (dens {i | C.encode x i = w i} : ℝ)) : x ∈ C.candidates w :=
  C.mem_candidates.mpr (hC.exists_decode_eq_of_half_add_le h)

/-- **Short index.** If a code list decodes up to radius `1 / 2 - δ`, a received word that agrees
with the codeword of `x` on at least a `1 / 2 + δ` fraction of the coordinates, together with an
index of `Nat.clog 2 L` bits, determines `x`. -/
theorem ListDecodes.exists_decodeBits_eq_some {δ : ℝ} (hC : C.ListDecodes (1 / 2 - δ)) {x : α}
    {w : ι → β} (h : 1 / 2 + δ ≤ (dens {i | C.encode x i = w i} : ℝ)) :
    ∃ b : BitString (Nat.clog 2 L), C.decodeBits w b = some x :=
  C.exists_decodeBits_eq_some (hC.exists_decode_eq_of_half_add_le h)

end ListCode

namespace Code

variable {ι α : Type*} [Fintype ι] [DecidableEq α]

/-- A code `C : Set (ι → α)` is *(ρ, L)-list-decodable* if every Hamming ball of relative radius
`ρ` contains at most `L` codewords. -/
def IsListDecodable (C : Set (ι → α)) (ρ : ℝ) (L : ℕ) : Prop :=
  ∀ w : ι → α, {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι}.encard ≤ L

private theorem encard_le_coe_of_finset_card_le {γ : Type*} {S : Set γ} {L : ℕ}
    (h : ∀ B : Finset γ, (B : Set γ) ⊆ S → #B ≤ L) :
    S.encard ≤ L := by
  classical
  by_contra! hlt
  have hle : ((L + 1 : ℕ) : ℕ∞) ≤ S.encard := by
    rw [Nat.cast_add, Nat.cast_one]
    exact Order.add_one_le_of_lt hlt
  obtain ⟨t, hts, ht⟩ := Set.exists_subset_encard_eq hle
  have htFin : t.Finite := Set.finite_of_encard_eq_coe ht
  have hcard : #(htFin.toFinset) = L + 1 := by
    rw [← Nat.cast_inj (R := ℕ∞), ← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset, ht]
  have hB := h htFin.toFinset (by simpa using hts)
  omega

/-- A finite code `C : Finset (ι → α)` is `(ρ, L)`-list-decodable iff every Hamming ball of
relative radius `ρ` meets `C` in at most `L` codewords. -/
theorem isListDecodable_finset_iff {C : Finset (ι → α)} {ρ : ℝ} {L : ℕ} :
    IsListDecodable (C : Set (ι → α)) ρ L ↔
      ∀ w : ι → α, #{c ∈ C | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} ≤ L := by
  refine forall_congr' fun w => ?_
  have hset : ({c ∈ (C : Set (ι → α)) | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} : Set _) =
      ((C.filter fun c => (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι : Finset (ι → α)) :
        Set (ι → α)) := by
    ext c
    simp
  rw [hset, Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]

/-- A (possibly infinite) code `C : Set (ι → α)` is `(ρ, L)`-list-decodable iff every finite subset
contained in a Hamming ball of relative radius `ρ` has cardinality at most `L`. -/
theorem isListDecodable_iff_forall_finset {C : Set (ι → α)} {ρ : ℝ} {L : ℕ} :
    IsListDecodable C ρ L ↔
      ∀ w : ι → α, ∀ B : Finset (ι → α),
        (B : Set (ι → α)) ⊆ {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} →
        #B ≤ L := by
  refine ⟨fun h w B hB => ?_, fun h w => encard_le_coe_of_finset_card_le (h w)⟩
  have henc : (B : Set (ι → α)).encard ≤ L := (Set.encard_le_encard hB).trans (h w)
  rwa [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le] at henc

/-- List decodability is downward closed in the code and radius and upward closed in the list
size. -/
theorem IsListDecodable.mono {C C' : Set (ι → α)} {ρ ρ' : ℝ} {L L' : ℕ}
    (h : IsListDecodable C ρ L) (hC : C' ⊆ C) (hρ : ρ' ≤ ρ) (hL : L ≤ L') :
    IsListDecodable C' ρ' L' := fun w => by
  have hsub : {c ∈ C' | (hammingDist c w : ℝ) ≤ ρ' * Fintype.card ι} ⊆
      {c ∈ C | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} := by
    rintro c ⟨hc, hdist⟩
    refine ⟨hC hc, hdist.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _)
  exact (Set.encard_le_encard hsub).trans ((h w).trans (Nat.cast_le.2 hL))

/-- For an injective encoder of a finite nonempty message type, combinatorial `(ρ, L)`-list
decodability of `Set.range enc` is equivalent to the existence of a `ListCode` with encoder `enc`
that list decodes up to radius `ρ`. -/
theorem isListDecodable_range_iff_exists_listCode {M : Type*} [Finite M] [Nonempty M]
    {enc : M → ι → α} (henc : Function.Injective enc) {ρ : ℝ} {L : ℕ} :
    IsListDecodable (Set.range enc) ρ L ↔
      ∃ D : ListCode M ι α L, D.encode = enc ∧ D.ListDecodes ρ := by
  classical
  constructor
  · intro h
    have := Fintype.ofFinite M
    let S : (ι → α) → Finset M := fun w =>
      {x | (hammingDist (enc x) w : ℝ) ≤ ρ * Fintype.card ι}
    have hS (w : ι → α) : #(S w) ≤ L := by
      have himg : ((S w).image enc : Set (ι → α)) ⊆
          {c ∈ Set.range enc | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} := by
        rintro c hc
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_univ, true_and, S] at hc
        obtain ⟨x, hdist, rfl⟩ := hc
        exact ⟨⟨x, rfl⟩, hdist⟩
      have hencard : (((S w).image enc : Finset (ι → α)) : Set (ι → α)).encard ≤ L :=
        (Set.encard_le_encard himg).trans (h w)
      rw [Set.encard_coe_eq_coe_finsetCard, card_image_of_injective _ henc, Nat.cast_le]
        at hencard
      exact hencard
    refine ⟨⟨enc, fun w k => (S w).toList.getD k (Classical.arbitrary M)⟩, rfl, fun x w hx => ?_⟩
    have hxS : x ∈ (S w).toList := by
      rw [Finset.mem_toList, Finset.mem_filter]
      exact ⟨Finset.mem_univ x, hx⟩
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 hxS
    refine ⟨⟨i, hi.trans_le ((Finset.length_toList _).trans_le (hS w))⟩, ?_⟩
    change (S w).toList.getD i _ = x
    rw [List.getD_eq_getElem _ _ hi, hix]
  · rintro ⟨D, rfl, hD⟩ w
    have hsub : {c ∈ Set.range D.encode | (hammingDist c w : ℝ) ≤ ρ * Fintype.card ι} ⊆
        (((Finset.univ : Finset (Fin L)).image fun k => D.encode (D.decode w k) :
          Finset (ι → α)) : Set (ι → α)) := by
      rintro c ⟨⟨x, rfl⟩, hdist⟩
      obtain ⟨k, hk⟩ := hD x w hdist
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact ⟨k, congrArg D.encode hk⟩
    refine (Set.encard_le_encard hsub).trans ?_
    rw [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]
    exact card_image_le.trans_eq (card_fin L)

end Code

end Cslib
