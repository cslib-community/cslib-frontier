/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MAC.CarterWegman
import CslibFrontier.Crypto.Protocols.MAC.GHASH
import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
import CslibFrontier.Probability.HashFamily.Polynomial

/-!
# Tests for GHASH

Checks (9.18) of [BonehShoup2023] for three blocks, that the difference on bit strings is XOR
(the "XOR" of "XOR-DUF"), the relation of GHASH to `H_xpoly` and to the hash of Katz–Lindell's
Theorem 4.17, and Remark 7.4 as an instance. The hypotheses of the positive results have failing
cases: a constant encoding (`hinj`), a leading zero block (`hlast`), one-block inputs (the bound,
and `hlen`), a two-element field (the bound at two blocks), `2 ^ 64` bits of associated data (`hd`;
`hc` is the same with the fields exchanged), and padding that merges bit strings of different
lengths (lengths in bits). The XOR-DUF theorems are applied at the book's
`ℓ = 2 ^ 32 - 1`, at bit bounds on the two fields, at the field `BinaryField w` with its bit
encoding, and through `nonceStrongGame_le`, the Carter–Wegman bound that takes them as hypothesis.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GHASH

open Cslib Cslib.Crypto Cslib.Probability Cslib.Crypto.PolynomialEvaluation
open scoped ENNReal

variable {F : Type*} [Field F]

/-! ### (9.18) and XOR -/

-- (9.18) for three blocks, through the public equations `ghash_cons` and `ghash_nil`.
example (k z₀ z₁ z₂ : F) : ghash k [z₀, z₁, z₂] = z₀ * k ^ 3 + z₁ * k ^ 2 + z₂ * k := by
  simp only [ghash_cons, ghash_nil, List.length_cons, List.length_nil]
  ring

-- On `BitString n` the difference of `IsDeltaUniversalHash` is XOR (Remark 7.3).
example {n : ℕ} (x y : BitString n) : x - y = fun i => xor (x i) (y i) := by
  funext i
  rw [Pi.sub_apply]
  cases x i <;> cases y i <;> decide

-- "Almost the same as `H_xpoly`": GHASH is `H_xpoly` of (7.23) without its leading term
-- `k ^ (v + 1)`, the term that separates inputs of different lengths in `H_xpoly`.
example (k : F) (z : List F) : xpolyHash k z = k ^ (z.length + 1) + ghash k z := by
  induction z using List.reverseRecOn with
  | nil => simp [xpolyHash, polyHash]
  | append_singleton z a ih =>
    have h : polyHash k (z ++ [a]) = polyHash k z * k + a := by
      simp [polyHash, List.foldl_append]
    rw [xpolyHash] at ih
    rw [xpolyHash, h, ghash_concat, List.length_append, List.length_singleton]
    linear_combination k * ih

-- The GHASH criterion contains Katz–Lindell's Theorem 4.17: their hash is GHASH of the message
-- followed by its length code (`hash_eq_ghash`), whose last block is that code.
example [Fintype F] {ℓ : ℕ} {encodeLength : Fin ℓ → F} (hencode : Function.Injective encodeLength) :
    IsDeltaUniversalHash (PMF.uniformOfFintype F) (hash encodeLength) (ℓ / Fintype.card F) := by
  have h := isDeltaUniversalHash_ghash (ℓ := ℓ) (coefficients encodeLength)
    (fun m m' h => Subtype.ext (List.append_inj_left' h rfl))
    (fun m m' h => by
      simp only [coefficients, List.getLastD_concat] at h
      have h2 : m.1.length = m'.1.length := congrArg Fin.val (hencode h)
      simp [coefficients, h2])
    (fun m => by simp only [coefficients, List.length_append, List.length_singleton]; exact m.2)
  have heq : hash encodeLength = fun k m => ghash k (coefficients encodeLength m) := by
    funext k m; exact hash_eq_ghash encodeLength k m
  rwa [heq]

-- Remark 7.4: `H_xpoly` over the `2 ^ n`-element field is an `(ℓ + 1) / 2 ^ n`-XOR-DUF.
example {n : ℕ} (hn : n ≠ 0) (ℓ : ℕ) :
    IsDeltaUniversalHash (PMF.uniformOfFintype (BinaryField n))
      (fun k (m : {m : List (BinaryField n) // m.length ≤ ℓ}) => xpolyHash k m)
      ((ℓ + 1) / 2 ^ n) := by
  have h := isDeltaUniversalHash_xpolyHash (F := BinaryField n) ℓ
  have hcard : (Fintype.card (BinaryField n) : ℝ≥0∞) = 2 ^ n := by
    rw [BinaryField.card hn]; norm_cast
  rwa [hcard] at h

/-! ### The XOR-DUF theorems on fixed-length inputs and on `BinaryField w` -/

-- Inputs of one length `v` over any finite field: `v / |F|`.
example [Fintype F] (v : ℕ) :
    IsDeltaUniversalHash (PMF.uniformOfFintype F)
      (fun k (z : {z : List F // z.length = v}) => ghash k z) (v / Fintype.card F) :=
  isDeltaUniversalHash_ghash Subtype.val Subtype.val_injective
    (fun x x' _ => x.2.trans x'.2.symm) (fun x => x.2.le)

-- Inputs of one length `v` on 128-bit strings: `v / 2 ^ 128`.
example (e : F ≃+ BitString 128) (v : ℕ) :
    IsDeltaUniversalHash (PMF.uniformOfFintype (BitString 128))
      (fun k (z : {z : List (BitString 128) // z.length = v}) => ghashBits e k z)
      (v / 2 ^ 128) :=
  isDeltaUniversalHash_ghashBits e Subtype.val Subtype.val_injective
    (fun x x' _ => x.2.trans x'.2.symm) (fun x => x.2.le)

-- The bit-string theorem at `BinaryField w` with its bit encoding, any `w ≠ 0`.
example {w ℓ : ℕ} (hw : w ≠ 0) {X : Type*} (enc : X → List (BitString w))
    (hinj : Function.Injective enc)
    (hlast : ∀ x x', (enc x).getLastD 0 = (enc x').getLastD 0 →
      (enc x).length = (enc x').length)
    (hlen : ∀ x, (enc x).length ≤ ℓ) :
    IsDeltaUniversalHash (PMF.uniformOfFintype (BitString w))
      (fun k x => ghashBits (BinaryField.equivBits hw) k (enc x)) (ℓ / 2 ^ w) :=
  isDeltaUniversalHash_ghashBits (BinaryField.equivBits hw) enc hinj hlast hlen

-- The headline at `BinaryField 128` with its bit encoding.
example {X : Type*} {ℓ : ℕ} (d c : X → List Bool)
    (hinj : ∀ x x', d x = d x' → c x = c x' → x = x')
    (hd : ∀ x, (d x).length < 2 ^ 64) (hc : ∀ x, (c x).length < 2 ^ 64)
    (hlen : ∀ x, (gcmHashInput (d x) (c x)).length ≤ ℓ) :
    IsDeltaUniversalHash (PMF.uniformOfFintype (BitString 128))
      (fun k x => ghashBits (BinaryField.equivBits (by norm_num)) k (gcmHashInput (d x) (c x)))
      (ℓ / 2 ^ 128) :=
  isDeltaUniversalHash_ghashBits_gcmHashInput _ d c hinj hd hc hlen

/-! ### Failing cases of the hypotheses -/

-- `hinj`: a constant encoding of two inputs is not Δ-universal for any `ε < 1`.
example [Fintype F] {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ IsDeltaUniversalHash (PMF.uniformOfFintype F)
      (fun k (_ : Bool) => ghash k ([] : List F)) ε :=
  not_isDeltaUniversalHash_of_sub_const (x := true) (x' := false) (by decide) 0
    (fun k => sub_self _) hε

-- `hlast`: the injective encoding `true ↦ [0]`, `false ↦ []` collides under every key.
example [Fintype F] {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ IsDeltaUniversalHash (PMF.uniformOfFintype F)
      (fun k (b : Bool) => ghash k (if b then [0] else ([] : List F))) ε :=
  not_isDeltaUniversalHash_of_sub_const (x := true) (x' := false) (by decide) 0
    (fun k => by simp [ghash_cons_zero]) hε

-- The bound and `hlen`: on one-block inputs no `ε < 1 / |F|` works, in every finite field, so
-- `ℓ / |F|` is attained at `ℓ = 1` and `hlen` cannot be dropped.
example [Fintype F] {ε : ℝ≥0∞} (hε : ε < (Fintype.card F : ℝ≥0∞)⁻¹) :
    ¬ IsDeltaUniversalHash (PMF.uniformOfFintype F)
      (fun k (z : {z : List F // z.length = 1}) => ghash k z) ε := fun hh => by
  have h : (PMF.uniformOfFintype F).toOuterMeasure {k : F | ghash k [1] - ghash k [0] = 1} ≤ ε :=
    hh ⟨[1], rfl⟩ ⟨[0], rfl⟩ (by simp) 1
  have hset : {k : F | ghash k [1] - ghash k [0] = 1} = {1} := by
    ext k; simp [ghash_cons]
  rw [hset, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply] at h
  exact absurd (h.trans_lt hε) (lt_irrefl _)

-- The bound at two blocks: in a two-element field `[1, 1]` and `[0, 0]` collide under both keys,
-- so `v / |F|` cannot be lowered to `(v - 1) / |F|` at `v = 2`.
example [Fintype F] (h2 : Fintype.card F = 2) (k : F) : ghash k [1, 1] = ghash k [0, 0] := by
  have hk : k ^ 2 = k := by simpa [h2] using FiniteField.pow_card k
  have h2' : (2 : F) = 0 := by simpa [h2] using Nat.cast_card_eq_zero F
  have h : ghash k [1, 1] - ghash k [0, 0] = k ^ 2 + k := by
    simp only [ghash_cons, ghash_nil, List.length_cons, List.length_nil]
    ring
  rw [← sub_eq_zero, h, hk, ← two_mul, h2', zero_mul]

/-- Every block of `gcmBlocks` of a string of zeros is zero. -/
private theorem gcmBlocks_replicate_false (n : ℕ) :
    ∀ x ∈ gcmBlocks (List.replicate n false), x = 0 := by
  intro x hx
  rw [gcmBlocks] at hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  funext j
  rw [BitString.padBlocks_getElem_apply _ _ _ i (by simpa using hi), List.getD_eq_getElem?_getD,
    List.getElem?_replicate]
  split_ifs <;> rfl

/-- The length block of two zero lengths is zero. -/
private theorem gcmLengthBlock_zero_zero : gcmLengthBlock 0 0 = 0 := by
  funext j
  have hj : gcmLengthBlock 0 0 j = false := by simp [gcmLengthBlock]
  rw [hj]; rfl

/-- A list of zero blocks hashes to zero. -/
private theorem ghashBits_eq_zero {w : ℕ} (e : F ≃+ BitString w) (k : BitString w)
    (z : List (BitString w)) (hz : ∀ x ∈ z, x = 0) : ghashBits e k z = 0 := by
  have h : ghash (e.symm k) (z.map e.symm) = 0 := by
    induction z with
    | nil => exact ghash_nil _
    | cons a z ih =>
      rw [List.map_cons, hz a (by simp), map_zero, ghash_cons_zero]
      exact ih fun x hx => hz x (List.mem_cons_of_mem _ hx)
  rw [ghashBits_def, h, map_zero]

-- `hd` (and symmetrically `hc`): the length block wraps at `2 ^ 64`, so `2 ^ 64` zero bits of
-- associated data and no associated data, each with an empty ciphertext, are different inputs
-- with the same hash under every key.
example (e : F ≃+ BitString 128) (k : BitString 128) :
    ghashBits e k (gcmHashInput (List.replicate (2 ^ 64) false) []) =
      ghashBits e k (gcmHashInput [] []) := by
  have h64 : gcmLengthBlock (2 ^ 64) 0 = gcmLengthBlock 0 0 := by
    funext j
    simp only [gcmLengthBlock]
    split_ifs with h
    · rw [Nat.testBit_two_pow, Nat.zero_testBit]
      simp only [decide_eq_false_iff_not]
      omega
    · rfl
  have key : ∀ n, gcmLengthBlock n 0 = 0 →
      ghashBits e k (gcmHashInput (List.replicate n false) []) = 0 := by
    intro n hn
    refine ghashBits_eq_zero e k _ fun x hx => ?_
    simp only [gcmHashInput, List.mem_append, List.mem_singleton, List.length_replicate,
      List.length_nil] at hx
    rcases hx with (hx | hx) | hx
    · exact gcmBlocks_replicate_false n x hx
    · exact gcmBlocks_replicate_false 0 x hx
    · rw [hx, hn]
  exact (key (2 ^ 64) (h64.trans gcmLengthBlock_zero_zero)).trans
    (key 0 gcmLengthBlock_zero_zero).symm

-- The length block of the empty input is zero, and so is its hash under every key.
example (e : F ≃+ BitString 128) (k : BitString 128) : ghashBits e k (gcmHashInput [] []) = 0 :=
  ghashBits_eq_zero e k _ fun x hx => by
    simp only [gcmHashInput, List.length_nil, List.mem_append, List.mem_singleton] at hx
    rcases hx with (hx | hx) | hx
    · exact gcmBlocks_replicate_false 0 x hx
    · exact gcmBlocks_replicate_false 0 x hx
    · rw [hx, gcmLengthBlock_zero_zero]

-- Lengths in bits: zero padding identifies `[false]` with `[false, false]`, so a length field that
-- does not separate them (a count of whole bytes, say) gives both the same hash input.
example : gcmBlocks [false] = gcmBlocks [false, false] := by
  have h1 : ∀ n, [false].getD n false = false := fun n => by rcases n with _ | n <;> simp
  have h2 : ∀ n, [false, false].getD n false = false := fun n => by
    rcases n with _ | _ | n <;> simp
  rw [gcmBlocks, gcmBlocks]
  refine List.ext_getElem (by simp) fun i hi hi' => funext fun j => ?_
  rw [BitString.padBlocks_getElem_apply _ _ _ i (by simpa using hi),
    BitString.padBlocks_getElem_apply _ _ _ i (by simpa using hi'), h1, h2]

/-! ### The headline at the book's parameters and in its caller -/

-- The book's `ℓ = 2 ^ 32 - 1`: at most that many blocks hashed, the length block included. Both
-- fields are then shorter than `2 ^ 64` bits.
example (e : F ≃+ BitString 128) {X : Type*} (d c : X → List Bool)
    (hinj : ∀ x x', d x = d x' → c x = c x' → x = x')
    (hlen : ∀ x, (gcmHashInput (d x) (c x)).length ≤ 2 ^ 32 - 1) :
    IsDeltaUniversalHash (PMF.uniformOfFintype (BitString 128))
      (fun k x => ghashBits e k (gcmHashInput (d x) (c x)))
      (((2 ^ 32 - 1 : ℕ) : ℝ≥0∞) / 2 ^ 128) :=
  isDeltaUniversalHash_ghashBits_gcmHashInput e d c hinj
    (fun x => by have := hlen x; rw [length_gcmHashInput] at this; omega)
    (fun x => by have := hlen x; rw [length_gcmHashInput] at this; omega) hlen

/-- Associated data of at most `a` bits with a ciphertext of at most `b` bits. -/
abbrev Input (a b : ℕ) : Type := {d : List Bool // d.length ≤ a} × {c : List Bool // c.length ≤ b}

-- Bit bounds `a, b < 2 ^ 64` on the two fields: `ε = (⌈a / 128⌉ + ⌈b / 128⌉ + 1) / 2 ^ 128`.
example (e : F ≃+ BitString 128) {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    IsDeltaUniversalHash (PMF.uniformOfFintype (BitString 128))
      (fun k (x : Input a b) => ghashBits e k (gcmHashInput x.1 x.2))
      (((a + 127) / 128 + (b + 127) / 128 + 1 : ℕ) / 2 ^ 128) :=
  isDeltaUniversalHash_ghashBits_gcmHashInput e (fun x : Input a b => (x.1 : List Bool))
    (fun x => (x.2 : List Bool)) (fun x x' h1 h2 => Prod.ext (Subtype.ext h1) (Subtype.ext h2))
    (fun x => x.1.property.trans_lt ha) (fun x => x.2.property.trans_lt hb)
    (fun x => by
      rw [length_gcmHashInput]
      have := x.1.property
      have := x.2.property
      omega)

open Cslib.Crypto.Protocols.CarterWegman in
-- The caller: the random-function step of the proof of Theorem 7.10 for the tag layer of GCM, with
-- a truly random pad function. A forger choosing its nonces, never repeating one, wins with
-- probability at most `ε + 2 ^ (-128)`.
example (e : F ≃+ BitString 128) {X N : Type} [DecidableEq X] [Fintype N] [DecidableEq N]
    {ℓ : ℕ} (d c : X → List Bool) (hinj : ∀ x x', d x = d x' → c x = c x' → x = x')
    (hd : ∀ x, (d x).length < 2 ^ 64) (hc : ∀ x, (c x).length < 2 ^ 64)
    (hlen : ∀ x, (gcmHashInput (d x) (c x)).length ≤ ℓ)
    (forger : NonceForger X N (BitString 128)) :
    nonceStrongGame (PMF.uniformOfFintype (BitString 128))
        (fun k x => ghashBits e k (gcmHashInput (d x) (c x))) forger true ≤
      (ℓ : ℝ≥0∞) / 2 ^ 128 + (Fintype.card (BitString 128) : ℝ≥0∞)⁻¹ :=
  nonceStrongGame_le (isDeltaUniversalHash_ghashBits_gcmHashInput e d c hinj hd hc hlen) forger

end CslibFrontierTests.Crypto.GHASH
