/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.OuterRootTemplate
public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RawScheduleVerifier
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.OuterRootLeafRequest
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits

/-!
# Raw carry-save leaf requests for the actual root contraction

The request guard checks both the path's movement encoding and its number of rows.
Every enabled request names a numbered schedule and a bit below the padded precision.
A disabled request contributes zero, including the second carry-save word.
-/

public section

namespace Cslib.Complexity.CountingSimulation.OuterRootLeaf

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeATM
open Cslib.BitString Circuits.Boolean.CarrySaveQuery Circuits.Frontier.ContractionSchedule
open OuterRootLeafRequest RootSeedChoice

/-- The six serializer fields at the scheduled source time. -/
@[expose] def source (k states t : ℕ) (path : List Bool) (carry : Bool) (bits : List Bool) :
    Input :=
  ⟨outerRootTemplate k states t, encNat (2 ^ (2 * (k + 1) * numBlocks t)),
    encNat (paddedTime t + 1), path, carry, bits⟩

/-- Removing only high zero padding preserves the requested bit index. -/
theorem ofBits_take_of_lt (bits : List Bool) (w : ℕ) (h : lsbValue bits < w) :
    ofBits (bits.take (encNat w).length) = lsbValue bits := by
  rw [ofBits_eq_lsbValue, length_encNat_eq_size]
  by_cases hl : bits.length ≤ w.size
  · rw [List.take_of_length_le hl]
  have ha := lsbValue_append (bits.take w.size) (bits.drop w.size)
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left (by omega)] at ha
  by_cases hz : lsbValue (bits.drop w.size) = 0
  · simpa only [hz, Nat.mul_zero, Nat.add_zero] using ha.symm
  have hp := Nat.le_mul_of_pos_right (2 ^ w.size) (Nat.pos_of_ne_zero hz)
  have hw := Nat.lt_size_self w
  omega

private theorem valid_path_iff {k q : ℕ} (path : List Bool) :
    ScheduleBits.validate k path = true ∧ path.length = 2 * (k + 1) * q ↔
      ∃ n : ℕ, ScheduleBits.rows (List.ofFn (scheduleOfNat k q n)) = path := by
  constructor
  · rintro ⟨hv, hl⟩
    obtain ⟨rs, rfl⟩ := (ScheduleBits.validate_eq_true_iff_exists_rows _ _).1 hv
    rw [ScheduleBits.length_rows] at hl
    have hr : rs.length = q := Nat.eq_of_mul_eq_mul_left (by positivity) hl
    subst q
    let n := scheduleEquiv k rs.length rs.get
    refine ⟨n.val, ?_⟩
    rw [scheduleOfNat_eq_symm n.isLt]
    simp [n]
  · rintro ⟨n, rfl⟩
    exact ⟨ScheduleBits.validate_rows _, by simp only [ScheduleBits.length_rows, List.length_ofFn]⟩

/-- The enabled physical branch calls exactly one numbered schedule at a bounded bit. -/
theorem active_iff (k states t : ℕ) (path bits : List Bool) (carry : Bool) :
    let x := source k states t path carry bits
    active (data k x) = true ↔ carry = false ∧
      (∃ n : ℕ, ScheduleBits.rows (List.ofFn (scheduleOfNat k (numBlocks t) n)) = path) ∧
      ofBits (bits.take x.width.length) < paddedTime t + 1 := by
  dsimp only
  rw [← valid_path_iff]
  simp only [active, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  simp only [data, source,
    ofBits_eq_lsbValue, encNat_apply, lsbValue_bits]
  rw [Nat.size_eq_bits_len, Nat.size_pow, Nat.add_left_inj]
  tauto

/-- Replacing the protected path and public query fields constructs the verifier's exact input. -/
theorem request_eq (k states t n : ℕ) (path bits : List Bool) (carry claim : Bool)
    (hp : ScheduleBits.rows (List.ofFn (scheduleOfNat k (numBlocks t) n)) = path) :
    let x := source k states t path carry bits
    publicRequest k claim x = queryPublic k (numBlocks t) (rootCopies k states t) n
      (slotBits (rootEdges k states t) 0) (zeroSeed (rootVertices k states t) _)
      (ofBits (bits.take x.width.length)) claim := by
  subst path
  rfl

variable {k s : ℕ} {State : Type} (M : MultiTapePTM k Bool State) (st : State ≃ Fin s)
  (input : List Bool) (t : ℕ)

/-- On a valid movement word the carry-save bit is the bit of the actual scheduled contraction. -/
theorem value_schedule (n : ℕ) (path bits : List Bool)
    (hp : ScheduleBits.rows (List.ofFn (scheduleOfNat k (numBlocks t) n)) = path)
    (hb : lsbValue bits < paddedTime t + 1) :
    value (RawScheduleSum.contractionLeaf M st input t) ⟨path, 0, false, lsbValue bits⟩ =
      (blockNetworkOf M st (input, t, n)).2.contraction.testBit (lsbValue bits) := by
  rw [value, dite_eq_left hb, tree, RawScheduleSum.contractionLeaf,
    RawScheduleSum.component_operand,
    RawScheduleSum.weight, (ScheduleBits.decodeSchedule_eq_some_iff _ _).2 hp]
  rfl

/-- The disabled branch correctly handles both the carry word and malformed schedule paths. -/
theorem value_inactive (path bits : List Bool) (carry : Bool)
    (hb : lsbValue bits < paddedTime t + 1)
    (h : active (data k (source k s t path carry bits)) = false) :
    value (RawScheduleSum.contractionLeaf M st input t) ⟨path, 0, carry, lsbValue bits⟩ =
      false := by
  rw [value, dite_eq_left hb, tree, RawScheduleSum.contractionLeaf,
    RawScheduleSum.component_operand]
  cases carry with
  | true => rfl
  | false =>
    have hn : ScheduleBits.decodeSchedule k (numBlocks t) path = none := by
      cases he : ScheduleBits.decodeSchedule k (numBlocks t) path with
      | none => rfl
      | some σ =>
        exfalso
        let n := scheduleEquiv k (numBlocks t) σ
        have hp := (ScheduleBits.decodeSchedule_eq_some_iff _ _).1 he
        have hr : scheduleOfNat k (numBlocks t) n.val = σ := by
          rw [scheduleOfNat_eq_symm n.isLt]
          exact (scheduleEquiv _ _).symm_apply_apply _
        rw [← hr] at hp
        have hi := ofBits_take_of_lt bits _ hb
        have hv := (active_iff k s t path bits false).2 ⟨rfl, ⟨n.val, hp⟩, hi ▸ hb⟩
        rw [h] at hv
        contradiction
    simp only [Bool.false_eq_true, ↓reduceIte, RawScheduleSum.weight, hn, Option.elim_none,
      Nat.zero_testBit]

end Cslib.Complexity.CountingSimulation.OuterRootLeaf
