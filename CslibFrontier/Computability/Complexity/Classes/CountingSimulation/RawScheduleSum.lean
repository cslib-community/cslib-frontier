/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.BlockNetworks
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleDecode
public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.CountingQuery

/-!
# Summing block contractions over raw movement words

The path in the outer binary sum is the row-major two-bit schedule used by root endpoint queries.
Every schedule occurs once. Words containing invalid movement pairs contribute zero.
-/

public section

namespace Turing.MultiTapeTM.ScheduleBits

open MultiTapePTM

/-- Read one head from a single row, using zero for a missing or invalid cell. -/
@[expose] def readRow (k : ℕ) (word : List Bool) (h : Option (Fin k)) : SignType :=
  let signs := (decodePairs word).getD []
  signs[h.elim 0 (fun j => j.val + 1)]?.getD 0

private theorem readRow_row {k : ℕ} (r : Option (Fin k) → SignType) :
    readRow k (row r) = r := by
  funext h
  cases h with
  | none => simp [readRow, row]
  | some j =>
    have hj : j.val + 1 < k + 1 := Nat.succ_lt_succ j.isLt
    simp only [readRow, row, decodePairs_encode, Option.getD_some, Option.elim_some,
      List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
    rfl

/-- Read a fixed number of rows in input-head-first order. -/
@[expose] def readRows (k : ℕ) : (q : ℕ) → List Bool → Schedule k q
  | 0, _ => Fin.elim0
  | q + 1, word => Fin.cases (readRow k (word.take (2 * (k + 1))))
      (readRows k q (word.drop (2 * (k + 1))))

private theorem readRows_rows {k q : ℕ} (σ : Schedule k q) :
    readRows k q (rows (List.ofFn σ)) = σ := by
  induction q with
  | zero => funext i; exact Fin.elim0 i
  | succ q ih =>
    rw [List.ofFn_succ, rows, readRows, ← length_row (σ 0), List.take_left, List.drop_left,
      readRow_row, ih]
    funext i
    exact Fin.cases (by rfl) (fun _ => by rfl) i

/-- Decode a raw word at a fixed height. The length and all movement pairs are checked by
round-tripping the proposed schedule through the canonical row encoding. -/
@[expose] def decodeSchedule (k q : ℕ) (word : List Bool) : Option (Schedule k q) :=
  let σ := readRows k q word
  if rows (List.ofFn σ) = word then some σ else none

/-- Successful decoding is equivalent to equality with the exact canonical movement table. -/
theorem decodeSchedule_eq_some_iff {k q : ℕ} (word : List Bool) (σ : Schedule k q) :
    decodeSchedule k q word = some σ ↔ rows (List.ofFn σ) = word := by
  constructor
  · intro h
    dsimp only [decodeSchedule] at h
    split at h
    · rwa [← Option.some.inj h]
    · contradiction
  · rintro rfl
    simp [decodeSchedule, readRows_rows]

end Turing.MultiTapeTM.ScheduleBits

namespace Cslib.Complexity.CountingSimulation.RawScheduleSum

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM
open Cslib.BitString Cslib.Circuits.Boolean Cslib.Circuits.Boolean.CarrySaveQuery

/-- Weight of a raw leaf, with zero weight assigned to every rejected word. -/
@[expose] def weight {k q : ℕ} (f : Schedule k q → ℕ) (word : List Bool) : ℕ :=
  (ScheduleBits.decodeSchedule k q word).elim 0 f

private def index {k q : ℕ} (σ : Schedule k q) : ℕ :=
  binaryValue (ScheduleBits.rows (List.ofFn σ))

private theorem word_index {k q : ℕ} (σ : Schedule k q) :
    binaryWord (2 * (k + 1) * q) (index σ) = ScheduleBits.rows (List.ofFn σ) := by
  have bound : index σ < 2 ^ (2 * (k + 1) * q) := by
    simpa [index] using binaryValue_lt_two_pow (ScheduleBits.rows (List.ofFn σ))
  apply binaryValue_injective_of_length_eq
  · rw [length_binaryWord bound, ScheduleBits.length_rows, List.length_ofFn]
  · exact binaryValue_binaryWord _ _

private theorem index_injective (k q : ℕ) : Function.Injective (@index k q) := by
  intro a b h
  have hw := congrArg (binaryWord (2 * (k + 1) * q)) h
  rw [word_index, word_index] at hw
  exact Option.some.inj (((ScheduleBits.decodeSchedule_eq_some_iff _ a).2 hw).symm.trans
    ((ScheduleBits.decodeSchedule_eq_some_iff _ b).2 rfl))

/-- Summing over binary addresses counts each schedule exactly once, including the empty table. -/
theorem sum_weight {k q : ℕ} (f : Schedule k q → ℕ) :
    ∑ j ∈ Finset.range (2 ^ (2 * (k + 1) * q)), weight f (binaryWord (2 * (k + 1) * q) j) =
      ∑ σ, f σ := by
  classical
  let L := 2 * (k + 1) * q
  let codes := Finset.univ.image (@index k q)
  have sub : codes ⊆ Finset.range (2 ^ L) := by
    intro j hj
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.mp hj
    simpa [index, L] using binaryValue_lt_two_pow (ScheduleBits.rows (List.ofFn σ))
  rw [← Finset.sum_subset sub]
  · unfold codes
    rw [Finset.sum_image (fun a _ b _ h => index_injective k q h)]
    apply Finset.sum_congr rfl
    intro σ _
    rw [word_index, weight, (ScheduleBits.decodeSchedule_eq_some_iff _ σ).2 rfl]
    rfl
  · intro j _ hj
    unfold weight
    cases he : ScheduleBits.decodeSchedule k q (binaryWord L j) with
    | none => rfl
    | some σ =>
      have hw := (ScheduleBits.decodeSchedule_eq_some_iff _ σ).1 he
      have hj' : index σ = j := (congrArg binaryValue hw).trans (binaryValue_binaryWord ..)
      exact (hj (Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hj'⟩)).elim

/-- Carry-save leaf for a natural-valued contraction. Its second word is zero. -/
@[expose] def operand (w a : ℕ) : BitString (w + w) :=
  Fin.append ((equivFin w).symm ⟨a % 2 ^ w, Nat.mod_lt _ (by positivity)⟩) (fun _ => false)

/-- A leaf query needs at most one bit of the schedule's contraction. -/
theorem component_operand (w a : ℕ) (carry : Bool) (i : Fin w) :
    component (operand w a) carry i = if carry then false else a.testBit i.val := by
  cases carry <;> simp only [operand, component, Bool.false_eq_true, ↓reduceIte, fstBits_append,
    sndBits_append, equivFin_symm_apply, Nat.testBit_mod_two_pow, i.isLt, decide_true,
    Bool.true_and]

private theorem leafSum_ext {w : ℕ} {f g : List Bool → BitString (w + w)}
    (n : ℕ) (p : List Bool) (h : ∀ a, a.length = p.length + n → f a = g a) :
    leafSum f n p = leafSum g n p := by
  induction n generalizing p with
  | zero => rw [leafSum, leafSum, h p (by simp)]
  | succ n ih =>
    simp only [leafSum]
    congr 1 <;> apply ih <;> intro a ha <;> apply h <;>
      simp only [List.length_append, List.length_singleton] at ha <;> omega

/-- The outer tree uses its raw path directly as the movement table of the contraction leaf. -/
@[expose] def total {k q : ℕ} (w : ℕ) (f : Schedule k q → ℕ) : BitString w :=
  (carryLookaheadAdd w).eval interpretation
    (tree (fun p => operand w (weight f p)) (2 * (k + 1) * q) [])

/-- The outer carry-save tree returns each low bit of the full sum, including on overflow. -/
theorem total_apply {k q : ℕ} (w : ℕ) (f : Schedule k q → ℕ) (i : Fin w) :
    total w f i = (∑ σ, f σ).testBit i.val := by
  let L := 2 * (k + 1) * q
  have hw : ∀ p : List Bool, p.length = L → p = binaryWord L (binaryValue p) := by
    intro p hp
    have bound : binaryValue p < 2 ^ L := hp ▸ binaryValue_lt_two_pow p
    exact binaryValue_injective_of_length_eq (hp.trans (length_binaryWord bound).symm)
      (binaryValue_binaryWord L (binaryValue p)).symm
  have hs := leafSum_ext (w := w) (f := fun p => operand w (weight f p))
    (g := fun p => operand w (weight f (binaryWord L (binaryValue p)))) L []
    (by
      intro p hp
      exact congrArg (fun word => operand w (weight f word)) (hw p (by simpa using hp)))
  rw [← testBit_equivFin (total w f) i, total, val_eval_carryLookaheadAdd_pair,
    pairVal_tree_mod, hs,
    leafSum_binaryValue (fun j => operand w (weight f (binaryWord L j))) L []]
  simp only [binaryValue, List.foldl_nil, Nat.zero_mul, Nat.zero_add, operand, pairVal_append,
    Equiv.apply_symm_apply, val_equivFin_false, Nat.add_zero]
  rw [← Finset.sum_nat_mod, sum_weight, Nat.testBit_mod_two_pow]
  simp [i.isLt]

/-- A bit of the actual padded accepting-path count is a bit of a raw-path tree of block-network
contractions. This is a circuit semantics identity for the outer sum. -/
theorem total_contraction_apply {k s : ℕ} {State : Type} [Finite State]
    (machine : MultiTapePTM k Bool State) (e : State ≃ Fin s) (x : List Bool)
    {t : ℕ} (ht : 2 ≤ t) (w : ℕ) (i : Fin w) :
    total w (fun σ : Schedule k (numBlocks t) =>
      (machine.explicitBlockNetwork x (blockLength t) σ e).contraction) i =
        (machine.acceptCount x (paddedTime t)).testBit i.val := by
  rw [total_apply, machine.sum_contraction_explicitBlockNetwork _ _ _ (numBlocks_pos ht)]
  rfl

end Cslib.Complexity.CountingSimulation.RawScheduleSum
