/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Schedule
public import CslibFrontier.Foundations.Combinatorics.SparseModeValidate

/-!
# Compressed words for the contraction mode budget

At a node of valuation `i`, a colour is a packet and one of `2^(i+1)` tiles. A mode additionally
specifies its positive weight minus one. The sparse exponent word has one canonical encoding
at width `32 * branchExponent C s d`, and a coordinate query reads the original exponent.
-/

public section

namespace Cslib.Circuits.Frontier.ContractionSchedule

open SparseModeTuple Finset

/-- Represent a tuple of mode exponents using the packet/tile pair as a single colour. -/
@[expose] def modeRows {packets tiles pt : ℕ} (β : Fin packets × Fin tiles × Fin pt → ℕ) :
    List SparseModeTuple.Row :=
  SparseModeTuple.ofFn fun c b =>
    let z := (finProdFinEquiv (m := packets) (n := tiles)).symm c
    β (z.1, z.2, b)

/-- Each coordinate of the sparse representation is its original packet, tile and weight entry. -/
theorem coord_modeRows {packets tiles pt : ℕ} (β : Fin packets × Fin tiles × Fin pt → ℕ)
    (k : Fin packets) (t : Fin tiles) (b : Fin pt) :
    coord (modeRows β) (finProdFinEquiv (k, t)).val b.val = β (k, t, b) := by
  rw [modeRows, coord_ofFn]
  simp only [Equiv.symm_apply_apply]

/-- Two distinct exponent tuples never contribute through the same fixed-width word. -/
theorem padded_modeRows_injective (packets tiles pt width : ℕ) :
    Function.Injective (fun β : Fin packets × Fin tiles × Fin pt → ℕ =>
      padded width (modeRows β)) := by
  intro β γ h
  funext z
  rcases z with ⟨k, t, b⟩
  have eq := congrArg (fun w => query w (finProdFinEquiv (k, t)).val b.val) h
  simpa only [query_padded, coord_modeRows, Option.some.injEq] using eq

/-- Positive weight of a mode indexed by its packet, tile, and weight minus one. -/
abbrev modeWeight {packets tiles pt : ℕ} : Fin packets × Fin tiles × Fin pt → ℕ
  | (_, _, b) => b.val + 1

/-- The sparse word charges exactly the sum defining the mode budget. -/
theorem mass_modeRows {packets tiles pt : ℕ} (β : Fin packets × Fin tiles × Fin pt → ℕ) :
    mass (modeRows β) = ∑ z, modeWeight z * β z := by
  rw [modeRows, mass_ofFn]
  calc
    _ = ∑ z : Fin packets × Fin tiles, ∑ i : Fin pt, (i.val + 1) * β (z.1, z.2, i) :=
      Fintype.sum_equiv finProdFinEquiv.symm _ _ fun _ => rfl
    _ = _ := by simp only [Fintype.sum_prod_type]

/-- The exponent function addressed by a sparse word's colour and weight coordinates. -/
@[expose] def modeValues (packets tiles pt : ℕ) (rows : List Row) :
    Fin packets × Fin tiles × Fin pt → ℕ := fun ⟨packet, tile, weight⟩ =>
  coord rows (finProdFinEquiv (packet, tile)).val weight.val

/-- Reading every coordinate of an encoded tuple recovers the original function. -/
theorem modeValues_modeRows {packets tiles pt : ℕ}
    (β : Fin packets × Fin tiles × Fin pt → ℕ) :
    modeValues packets tiles pt (modeRows β) = β := by
  funext z
  exact coord_modeRows _ _ _ _

/-- An in-domain descriptor is reconstructed by its finitely many exponents. -/
theorem modeRows_modeValues (packets tiles pt : ℕ) (rows : List Row)
    (hc : colours rows ≤ packets * tiles) (hm : mass rows ≤ pt) :
    modeRows (modeValues packets tiles pt rows) = rows := by
  simpa only [modeRows, modeValues, Prod.mk.eta, Equiv.apply_symm_apply] using
    ofFn_coord (m := packets * tiles) (n := pt) rows hc hm

/-- Validate the sparse word and expose its exponents through coordinate lookups. -/
def readModes (packets tiles pt width : ℕ) (word : List Bool) :
    Option (Fin packets × Fin tiles × Fin pt → ℕ) :=
  (validate width (packets * tiles) pt word).map (modeValues packets tiles pt)

/-- The accepted words are exactly the canonical encodings of the original strict mode budget.
This converse excludes extra colours, out-of-range weights and duplicate contributions. -/
theorem readModes_eq_some_iff {packets tiles pt width : ℕ} {word : List Bool}
    {β : Fin packets × Fin tiles × Fin pt → ℕ} :
    readModes packets tiles pt width word = some β ↔
      β ∈ TensorNetwork.modeBudget modeWeight pt ∧
        (encode (modeRows β)).length ≤ width ∧ word = padded width (modeRows β) := by
  rw [readModes, Option.map_eq_some_iff]
  constructor
  · rintro ⟨rows, hr, rfl⟩
    obtain ⟨hd, hc, hm⟩ := validate_eq_some_iff.mp hr
    have hs := modeRows_modeValues packets tiles pt rows hc hm.le
    refine ⟨(TensorNetwork.mem_modeBudget (fun _ => Nat.succ_pos _)).mpr ?_, ?_⟩
    · rw [← mass_modeRows, hs]
      exact hm
    · rw [hs]
      exact decode_eq_some_iff.mp hd
  · rintro ⟨hβ, hl, rfl⟩
    refine ⟨modeRows β, validate_eq_some_iff.mpr
      ⟨decode_padded hl, colours_ofFn_le _, ?_⟩, modeValues_modeRows β⟩
    rw [mass_modeRows]
    exact (TensorNetwork.mem_modeBudget (fun _ => Nat.succ_pos _)).mp hβ

private theorem sqrt_two_mul_le (x : ℕ) : Nat.sqrt (2 * x) ≤ 2 * Nat.sqrt x + 1 := by
  have hx := Nat.lt_succ_sqrt x
  have hs := Nat.sqrt_le' (2 * x)
  nlinarith

/-- At an active node every budgeted exponent tuple fits the same `32 * e_d` bits.
The constant factor preserves the geometric branch sum across recursive calls. -/
theorem ActiveBounds.length_modeRows_le {C s d M p : ℕ} (hb : ActiveBounds C s d M p)
    (ha : Active C s d M p) {i h packets : ℕ} (hi : i < taper s d)
    (hh : h * taper s d ≤ 3 * M + taper s d) (hk : packets * 2 ^ slotBits s d ≤ 3 * M)
    (β : Fin packets × Fin (2 ^ (i + 1)) × Fin (nodePrecision p h (slotBits s d) M i) → ℕ)
    (hβ : β ∈ TensorNetwork.modeBudget modeWeight
      (nodePrecision p h (slotBits s d) M i)) :
    (encode (modeRows β)).length ≤ 32 * branchExponent C s d := by
  let m := packets * 2 ^ (i + 1)
  let pt := nodePrecision p h (slotBits s d) M i
  have hc : colours (modeRows β) ≤ m := colours_ofFn_le _
  have hp : mass (modeRows β) ≤ pt := (mass_modeRows β).le.trans
    ((TensorNetwork.mem_modeBudget (fun _ => Nat.succ_pos _)).mp hβ).le
  have he := length_encode_le (modeRows β) hc hp
  have hx : Nat.sqrt (m * pt) ≤ 15360 * C * s / (Nat.sqrt (Nat.log 2 s) * 8 ^ d) :=
    sqrt_modeBudget_le ha hb.two_le hb.one_le_taper (by have := slotBits_eq s d; omega)
      (hb.nodePrecision_mul_taper_le i h hi hh) hk
  have hs := sqrt_two_mul_le (m * pt)
  rw [← mul_assoc] at hs
  unfold branchExponent
  omega

end Cslib.Circuits.Frontier.ContractionSchedule
