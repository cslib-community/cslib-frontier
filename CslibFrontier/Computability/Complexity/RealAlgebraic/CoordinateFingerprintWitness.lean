/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup

/-!
# Fixed-width coordinate fingerprint witnesses

For each coordinate, a framed list of binary naturals records the modulus offset,
modular-power parameter, and target in that order. The low bit of the target encodes its sign.
The frame permits padding to one width. Binary addressing and bounded decoding work
on every word. Every tuple of admissible choices has a word of that width.

Adapted from the fingerprint part of `ChoiceTupleEncoding`, `ChoiceTupleNative` and
`ChoiceTupleCompleteness` in lean-canny at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
The deformation coefficient index is selected by the coordinate evaluator, so the
witness here carries fingerprint entries only.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM ComputableInPolyTime

/-- One coordinate's modular-power fingerprint and signed target. -/
structure CoordinateFingerprint where
  /-- Modulus for the modular powers. -/
  modulus : ℕ
  /-- Base of the modular powers. -/
  parameter : ℕ
  /-- Signed value of the fingerprint to select. -/
  target : ℤ

/-- The common decoded-modulus bound for coordinate polynomials of degree at most `D`. -/
@[expose] def CoordinateFingerprint.modulusBound (D : ℕ) : ℕ := 2 * (D ^ 3 + 2)

open CoordinateFingerprint (modulusBound)

/-- The admissible ranges for a fingerprint of a polynomial of degree at most `D`. -/
@[expose] def CoordinateFingerprint.Bounded (D : ℕ) (f : CoordinateFingerprint) : Prop :=
  2 < f.modulus ∧ f.modulus ≤ modulusBound D ∧ f.parameter < f.modulus ∧
    f.target.natAbs ≤ D * f.modulus

/-- The framed binary list, followed by an arbitrary padding suffix. -/
abbrev encCoordinateFingerprintWord : (List ℕ × List Bool) ↪ List Bool :=
  encPair (encList encNat) encBits

private def entries (word : List Bool) : List ℕ :=
  ((Decoder.pair (Decoder.list Decoder.nat) Decoder.bits).decode word).1

private def entry (word : List Bool) (i offset : ℕ) : ℕ :=
  (entries word).getD (3 * i + offset) 0

private def normalizeModulus (D r : ℕ) : ℕ := 3 + r % (modulusBound D - 2)

private def normalize (D r g t : ℕ) : CoordinateFingerprint :=
  let μ := normalizeModulus D r
  let mag := (t / 2) % (D * μ + 1)
  ⟨μ, g % μ, if t % 2 = 0 then (mag : ℤ) else -(mag : ℤ)⟩

/-- Decode the fingerprint for coordinate `i`, using zero for absent entries. The modulus
lies in the admissible range even when the word or the coordinate address is out of range. -/
def decodeCoordinateFingerprint (D : ℕ) (word : List Bool) (i : ℕ) : CoordinateFingerprint :=
  normalize D (entry word i 0) (entry word i 1) (entry word i 2)

/-- The decoded fingerprint is bounded for every word and binary coordinate address. -/
theorem decodeCoordinateFingerprint_bounded (D : ℕ) (word : List Bool) (i : ℕ) :
    (decodeCoordinateFingerprint D word i).Bounded D := by
  let r := entry word i 0
  let g := entry word i 1
  let t := entry word i 2
  let μ := normalizeModulus D r
  let mag := (t / 2) % (D * μ + 1)
  have hU : 4 ≤ modulusBound D := by unfold modulusBound; omega
  have hr := Nat.mod_lt r (by omega : 0 < modulusBound D - 2)
  have hmin : 2 < μ := by unfold μ normalizeModulus; omega
  have hmax : μ ≤ modulusBound D := by unfold μ normalizeModulus; omega
  have hmag : mag ≤ D * μ := Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))
  change 2 < μ ∧ μ ≤ modulusBound D ∧ g % μ < μ ∧
    (if t % 2 = 0 then (mag : ℤ) else -(mag : ℤ)).natAbs ≤ D * μ
  refine ⟨hmin, hmax, Nat.mod_lt _ (by omega), ?_⟩
  split_ifs <;> simpa only [Int.natAbs_neg, Int.natAbs_natCast]

/-- Compute the common modulus bound in binary polynomial time. -/
theorem CoordinateFingerprint.modulusBound_polyTime {α : Type}
    {enc : α ↪ List Bool} {D : α → ℕ}
    (hD : ComputableInPolyTime D enc encNat) :
    ComputableInPolyTime (fun w => modulusBound (D w)) enc encNat :=
  binary_mul' (.const 2) (binary_add' (binary_pow' hD (.const 3)) (.const 2))

private theorem entry_polyTime {α : Type} {enc : α ↪ List Bool}
    {word : α → List Bool} {i : α → ℕ}
    (hw : ComputableInPolyTime word enc encBits) (hi : ComputableInPolyTime i enc encNat)
    (offset : ℕ) : ComputableInPolyTime (fun w => entry (word w) (i w) offset) enc encNat :=
  let hdata := (fst (encList encNat) encBits).comp
    ((Decoder.pair (Decoder.list Decoder.nat) Decoder.bits).computableInPolyTime.comp hw)
  listGetD_binary 0 hdata (binary_add' (binary_mul' (.const 3) hi) (.const offset))

/-- Reading the bounded modulus costs polynomial time in the word and binary coordinate index. -/
theorem decodeCoordinateFingerprint_modulus_polyTime {α : Type} {enc : α ↪ List Bool}
    {D i : α → ℕ} {word : α → List Bool}
    (hD : ComputableInPolyTime D enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun w => (decodeCoordinateFingerprint (D w) (word w) (i w)).modulus)
      enc encNat :=
  binary_add' (.const 3)
    (binary_mod' (entry_polyTime hw hi 0)
      (binary_sub' (CoordinateFingerprint.modulusBound_polyTime hD) (.const 2)))

/-- Reading the bounded modular-power parameter takes polynomial time. -/
theorem decodeCoordinateFingerprint_parameter_polyTime {α : Type} {enc : α ↪ List Bool}
    {D i : α → ℕ} {word : α → List Bool}
    (hD : ComputableInPolyTime D enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun w => (decodeCoordinateFingerprint (D w) (word w) (i w)).parameter)
      enc encNat :=
  binary_mod' (entry_polyTime hw hi 1) (decodeCoordinateFingerprint_modulus_polyTime hD hi hw)

/-- Reading the bounded target in signed binary takes polynomial time. -/
theorem decodeCoordinateFingerprint_target_polyTime {α : Type} {enc : α ↪ List Bool}
    {D i : α → ℕ} {word : α → List Bool}
    (hD : ComputableInPolyTime D enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun w => (decodeCoordinateFingerprint (D w) (word w) (i w)).target)
      enc encIntBin := by
  have hraw := entry_polyTime hw hi 2
  have hμ := decodeCoordinateFingerprint_modulus_polyTime hD hi hw
  have hbound := binary_add' (binary_mul' hD hμ) (.const 1)
  have hmag := intBin_natCast.comp (binary_mod' (binary_div' hraw (.const 2)) hbound)
  have hparity := decide_eq' (binary_mod' hraw (.const 2)) (.const 0)
  have h := ite' hparity hmag (intBin_neg.comp hmag)
  simpa only [decodeCoordinateFingerprint, normalize, Function.comp_apply, decide_eq_true_eq]
    using h

private def entryBound (D : ℕ) : ℕ := max (modulusBound D) (2 * (D * modulusBound D) + 1)

/-- Bit width of a padded fingerprint tuple for `n` coordinates of degree bound `D`. -/
def coordinateFingerprintWitnessWidth (D n : ℕ) : ℕ :=
  2 * ((3 * n) * (2 * (entryBound D).size + 1)) + 1

/-- The width is computable in unary from a binary degree bound and unary arity. -/
theorem coordinateFingerprintWitnessWidth_polyTime {α : Type} {enc : α ↪ List Bool}
    {D n : α → ℕ} (hD : ComputableInPolyTime D enc encNat)
    (hn : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (fun w => coordinateFingerprintWitnessWidth (D w) (n w)) enc encUnary := by
  have hU := CoordinateFingerprint.modulusBound_polyTime hD
  have htarget := binary_add' (binary_mul' (.const 2) (binary_mul' hD hU)) (.const 1)
  have hsize := binary_size.comp (binary_max' hU htarget)
  have hentry := unary_add' (unary_mul' (.const 2) hsize) (.const 1)
  exact unary_add' (unary_mul' (.const 2) (unary_mul' (unary_mul' (.const 3) hn) hentry))
    (.const 1)

private theorem normalize_complete (D : ℕ) (f : CoordinateFingerprint) (hf : f.Bounded D) :
    ∃ r g t : ℕ, r ≤ entryBound D ∧ g ≤ entryBound D ∧ t ≤ entryBound D ∧
      normalize D r g t = f := by
  rcases f with ⟨μ, g, target⟩
  change 2 < μ ∧ μ ≤ modulusBound D ∧ g < μ ∧ target.natAbs ≤ D * μ at hf
  obtain ⟨hmin, hmax, hg, ht⟩ := hf
  have hm : normalizeModulus D (μ - 3) = μ := by
    unfold normalizeModulus
    rw [Nat.mod_eq_of_lt (by omega : μ - 3 < modulusBound D - 2)]
    omega
  have hr' : μ - 3 ≤ entryBound D :=
    (Nat.sub_le _ _).trans (hmax.trans (le_max_left _ _))
  have hg' : g ≤ entryBound D := hg.le.trans (hmax.trans (le_max_left _ _))
  have hγ : g % μ = g := Nat.mod_eq_of_lt hg
  cases target with
  | ofNat v =>
    change v ≤ D * μ at ht
    have hv := ht.trans (Nat.mul_le_mul_left D hmax)
    refine ⟨μ - 3, g, 2 * v, hr', hg', (le_max_of_le_right (by omega)), ?_⟩
    simp only [normalize, hm, hγ, show 2 * v / 2 = v by omega, show 2 * v % 2 = 0 by omega,
      ite_true, Nat.mod_eq_of_lt (Nat.lt_succ_of_le ht)]
    rfl
  | negSucc v =>
    change v + 1 ≤ D * μ at ht
    have hv := ht.trans (Nat.mul_le_mul_left D hmax)
    refine ⟨μ - 3, g, 2 * (v + 1) + 1, hr', hg', (le_max_of_le_right (by omega)), ?_⟩
    simp only [normalize, hm, hγ, show (2 * (v + 1) + 1) / 2 = v + 1 by omega,
      show (2 * (v + 1) + 1) % 2 = 1 by omega, Nat.one_ne_zero, ite_false,
      Nat.mod_eq_of_lt (Nat.lt_succ_of_le ht)]
    rfl

open Classical in
/-- Every admissible coordinate fingerprint tuple has a witness at the prescribed width. -/
theorem exists_coordinateFingerprintWitness {D n : ℕ} (f : Fin n → CoordinateFingerprint)
    (hf : ∀ i, (f i).Bounded D) :
    ∃ word : List Bool, word.length = coordinateFingerprintWitnessWidth D n ∧
      ∀ i : Fin n, decodeCoordinateFingerprint D word i.val = f i := by
  choose r g t hr hg ht hnorm using fun i => normalize_complete D (f i) (hf i)
  let atSlot (j : Fin (3 * n)) : ℕ :=
    let i : Fin n := ⟨j.val / 3, by have := j.isLt; omega⟩
    if j.val % 3 = 0 then r i else if j.val % 3 = 1 then g i else t i
  let data := List.ofFn atSlot
  let width := coordinateFingerprintWitnessWidth D n
  let padding := List.replicate (width - (2 * (encList encNat data).length + 1)) false
  let word := encCoordinateFingerprintWord (data, padding)
  have hentry (j : ℕ) (hj : j ∈ data) : (encNat j).length ≤ (entryBound D).size := by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hj
    rw [encNat_apply, Nat.size_eq_bits_len]
    apply Nat.size_le_size
    unfold atSlot
    split_ifs <;> first | exact hr _ | exact hg _ | exact ht _
  have hlength := length_encList_le encNat data hentry
  have hlen : data.length = 3 * n := List.length_ofFn
  rw [hlen] at hlength
  have hword : entries word = data := by
    rw [entries, show word = encPair (encList encNat) encBits (data, padding) from rfl,
      Decoder.decode_enc]
  refine ⟨word, ?_, ?_⟩
  · change (encPair (encList encNat) encBits (data, padding)).length = width
    rw [length_encPair]
    change 2 * (encList encNat data).length + 1 + padding.length = width
    simp only [padding, List.length_replicate, width, coordinateFingerprintWitnessWidth]
    omega
  · intro i
    have hslot (k : ℕ) (hk : k < 3) : entry word i.val k =
        if k = 0 then r i else if k = 1 then g i else t i := by
      have hi := i.isLt
      have hindex : 3 * i.val + k < 3 * n := by omega
      rw [entry, hword, List.getD_eq_getElem?_getD]
      simp only [data, List.getElem?_ofFn, hindex, dite_true, Option.getD_some, atSlot]
      have hdiv : (⟨(3 * i.val + k) / 3, by omega⟩ : Fin n) = i := by
        apply Fin.ext
        change (3 * i.val + k) / 3 = i.val
        omega
      rw [hdiv, show (3 * i.val + k) % 3 = k by omega]
    rw [decodeCoordinateFingerprint, hslot 0 (by decide), hslot 1 (by decide),
      hslot 2 (by decide)]
    exact hnorm i

end Cslib.Complexity.RealAlgebraic
