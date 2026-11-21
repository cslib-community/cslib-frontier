/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord
public import CslibFrontier.Foundations.Data.BitString.Binary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Quantifying fixed-width binary fields

A consecutive group of flags for one player quantifies over a complete fixed-width word. Each
number below the corresponding power of two has exactly one such least-significant-first field.
-/

public section

namespace Turing.MultiTapeATM.QuantifiedWord

open Cslib.BitString

/-- A previously stored prefix may be read by the terminal value after all players have moved. -/
theorem plays_append_prefix (value : List Bool → Prop) (base pre players : List Bool) :
    plays value (base ++ pre) players ↔ plays (fun word => value (base ++ word)) pre players := by
  induction players generalizing pre with
  | nil => rfl
  | cons player tail ih =>
    cases player <;> simp only [plays, Bool.false_eq_true, ↓reduceIte, List.append_assoc, ih]

private theorem plays_forall_words (value : List Bool → Prop) (pre rest : List Bool) (w : ℕ) :
    plays value pre (List.replicate w true ++ rest) ↔
      ∀ xs : List Bool, xs.length = w → plays value (pre ++ xs) rest := by
  induction w generalizing pre with
  | zero => simp
  | succ w ih =>
    simp only [List.replicate_succ, List.cons_append, plays, ↓reduceIte]
    constructor
    · intro h xs hx
      cases xs with
      | nil => simp at hx
      | cons bit tail =>
        simpa only [List.append_assoc, List.singleton_append] using
          (ih (pre ++ [bit])).1 (h bit) tail (by simpa using hx)
    · intro h bit
      apply (ih (pre ++ [bit])).2
      intro xs hx
      simpa only [List.append_assoc, List.singleton_append] using h (bit :: xs) (by simp [hx])

private theorem plays_exists_word (value : List Bool → Prop) (pre rest : List Bool) (w : ℕ) :
    plays value pre (List.replicate w false ++ rest) ↔
      ∃ xs : List Bool, xs.length = w ∧ plays value (pre ++ xs) rest := by
  induction w generalizing pre with
  | zero => simp
  | succ w ih =>
    simp only [List.replicate_succ, List.cons_append, plays, Bool.false_eq_true, ↓reduceIte]
    constructor
    · rintro ⟨bit, h⟩
      obtain ⟨xs, hx, hp⟩ := (ih (pre ++ [bit])).1 h
      refine ⟨bit :: xs, by simp [hx], ?_⟩
      simpa only [List.append_assoc, List.singleton_append] using hp
    · rintro ⟨ys, h, hp⟩
      cases ys with
      | nil => simp at h
      | cons bit xs =>
        refine ⟨bit, (ih (pre ++ [bit])).2 ⟨xs, by simpa using h, ?_⟩⟩
        simpa only [List.append_assoc, List.singleton_append] using hp

/-- A complete group of universal moves checks exactly every number in its binary field. -/
theorem plays_forall_field (value : List Bool → Prop) (pre rest : List Bool) (w : ℕ) :
    plays value pre (List.replicate w true ++ rest) ↔
      ∀ i : Fin (2 ^ w), plays value (pre ++ lowBits w i.val) rest := by
  rw [plays_forall_words]
  constructor
  · exact fun h i => h _ (length_lowBits w i.val)
  · intro h xs hx
    subst w
    simpa only [lowBits_lsbValue] using h ⟨lsbValue xs, lsbValue_lt xs⟩

/-- A complete group of existential moves chooses a single bounded number for the suffix. -/
theorem plays_exists_field (value : List Bool → Prop) (pre rest : List Bool) (w : ℕ) :
    plays value pre (List.replicate w false ++ rest) ↔
      ∃ i : Fin (2 ^ w), plays value (pre ++ lowBits w i.val) rest := by
  rw [plays_exists_word]
  constructor
  · rintro ⟨xs, hx, hp⟩
    subst w
    exact ⟨⟨lsbValue xs, lsbValue_lt xs⟩, by simpa only [lowBits_lsbValue] using hp⟩
  · rintro ⟨i, hi⟩
    exact ⟨_, length_lowBits w i.val, hi⟩

/-- Flags for a universal edge, one common existential rank, and a universal bit challenge. -/
@[expose] def rankFlags (w : ℕ) : List Bool :=
  List.replicate w true ++ (List.replicate w false ++ List.replicate (Nat.clog 2 w) true)

/-- The flags for an edge count given in binary occupy two rank fields and one bit-index field. -/
theorem length_rankFlags (w : ℕ) : (rankFlags w).length = 2 * w + Nat.clog 2 w := by
  simp [rankFlags, two_mul, Nat.add_assoc]

/-- A native deterministic machine prepares all the quantifier flags from the binary edge count.
Both ceiling logarithms are computed before their unary counters are used to repeat flags. -/
theorem computableInPolyTime_rankFlags :
    MultiTapeTM.ComputableInPolyTime (fun n => rankFlags (Nat.clog 2 n))
      MultiTapeTM.encNat MultiTapeTM.encBits := by
  open MultiTapeTM.ComputableInPolyTime in
    exact ((bitsReplicate true).comp binary_clog_two).bitsAppend
      (((bitsReplicate false).comp binary_clog_two).bitsAppend
        ((bitsReplicate true).comp (binary_clog_two.comp binary_clog_two_nat)))

/-- The physical three-field prefix has exactly the local verifier's quantifier order.
Zero-width fields have a single encoding (the empty word). -/
theorem plays_rankFlags (value : List Bool → Prop) (w : ℕ) :
    plays value [] (rankFlags w) ↔ ∀ e : Fin (2 ^ w), ∃ g : Fin (2 ^ w),
      ∀ j : Fin (2 ^ Nat.clog 2 w), value (lowBits w e.val ++ lowBits w g.val ++
        lowBits (Nat.clog 2 w) j.val) := by
  rw [rankFlags, plays_forall_field]
  apply forall_congr'
  intro e
  rw [plays_exists_field]
  apply exists_congr
  intro g
  simpa only [List.nil_append, List.append_nil, plays] using
    plays_forall_field value (lowBits w e.val ++ lowBits w g.val) [] (Nat.clog 2 w)

/-- Padded edges are accepted without a guess condition. A genuine edge requires a fitting
rank even when its bit-width is zero, and only genuine bit challenges invoke the leaf. -/
theorem plays_rankFlags_iff_local (n w : ℕ) (hn : n ≤ 2 ^ w) (value : List Bool → Prop)
    (fits : Fin (2 ^ w) → Prop) (check : Fin n → Fin (2 ^ w) → Fin w → Prop)
    (h : ∀ (e g : Fin (2 ^ w)) (j : Fin (2 ^ Nat.clog 2 w)),
      value (lowBits w e.val ++ lowBits w g.val ++ lowBits (Nat.clog 2 w) j.val) ↔
        ∀ he : e.val < n, fits g ∧ ∀ hj : j.val < w, check ⟨e.val, he⟩ g ⟨j.val, hj⟩) :
    plays value [] (rankFlags w) ↔ ∀ e, ∃ g, fits g ∧ ∀ j, check e g j := by
  rw [plays_rankFlags]
  constructor
  · intro hall e
    let wide : Fin (2 ^ w) := ⟨e.val, e.isLt.trans_le hn⟩
    obtain ⟨g, hg⟩ := hall wide
    refine ⟨g, ((h wide g 0).1 (hg 0) e.isLt).1, ?_⟩
    intro j
    let jj : Fin (2 ^ Nat.clog 2 w) := ⟨j.val, j.isLt.trans_le (Nat.le_pow_clog (by decide) w)⟩
    exact ((h wide g jj).1 (hg jj) e.isLt).2 j.isLt
  · intro hall e
    by_cases he : e.val < n
    · obtain ⟨g, hg, hj⟩ := hall ⟨e.val, he⟩
      exact ⟨g, fun j => (h e g j).2 fun _ => ⟨hg, fun hbit => hj ⟨j.val, hbit⟩⟩⟩
    · exact ⟨0, fun j => (h e 0 j).2 fun hlt => False.elim (he hlt)⟩

end Turing.MultiTapeATM.QuantifiedWord
