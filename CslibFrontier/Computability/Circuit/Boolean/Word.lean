/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.Synthesis
public import CslibFrontier.Computability.Circuit.Iteration
public import CslibFrontier.Foundations.Data.BitString.BitVec
public import Init.Data.BitVec.Bitblast

/-!
# Word arithmetic over the De Morgan basis

Words are Lean's `BitVec`s, stored least significant bit first (`Cslib.BitString.equivBitVec`). A
word-valued function of the inputs is available when each of its coordinate functions is
(`Boolean.wordWires`). This module bounds the gates needed to make words available from available
words: addition, subtraction, unsigned comparison, comparison with a constant, complementation,
constants, multiplexing, and selection of one of several words by a binary index. Equality of
available bit strings is `Formula.equalBits` inserted by `Synthesis.circuit`. Their semantics are
the `BitVec` operations, through the bit-blasting identities of the core library; no decision
procedure or native evaluation is used.

Addition is a ripple-carry adder: every carry is computed once and shared by the sum bits, for
`12 * w + 1` gates on `w`-bit words including the initial carry constant. All bounds charge every
gate, including constants and negations.

## Main definitions

* `Cslib.Circuits.Boolean.wordWires`: the coordinate functions of a word-valued function.
* `Cslib.Circuits.Boolean.selectBits`: select one of several bit strings by a binary index.

## Main results

* `Cslib.Circuits.Synthesis.mux`: a multiplexer in four gates.
* `Cslib.Circuits.Synthesis.word_add`, `word_addCarry`, `word_sub`: ripple-carry arithmetic.
* `Cslib.Circuits.Synthesis.word_ult`, `word_eq_const`: comparisons.
* `Cslib.Circuits.Synthesis.word_not`, `word_const`, `word_mux`: bitwise operations.
* `Cslib.Circuits.Synthesis.selectBits`: selection charging one comparison per record and bit.

## References

* Adapted from lean/Proofs/{Synthesis,Arithmetic,Words}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions],
  where each sum bit recomputes its carry chain.
-/

public section

namespace Cslib.Circuits

namespace Boolean

variable {n k w R : ℕ}

/-- The coordinate functions of a word-valued function. -/
@[expose] def wordWires (a : BitString n → BitVec w) : Set (BooleanFunction n) :=
  Set.range fun i : Fin w => fun x => (a x).getLsbD i.val

/-- Zero extension and truncation only rewire available bits and the false constant. -/
theorem wordWires_setWidth_subset {v : ℕ} {s : Set (BooleanFunction n)}
    {value : BitString n → BitVec w} (hv : wordWires value ⊆ s) (hz : (fun _ => false) ∈ s) :
    wordWires (fun x => (value x).setWidth v) ⊆ s := by
  rintro _ ⟨bit, rfl⟩
  simp only [BitVec.getLsbD_setWidth, bit.isLt, decide_true, Bool.true_and]
  by_cases hi : bit.val < w
  · exact hv ⟨⟨bit.val, hi⟩, rfl⟩
  · simpa only [BitVec.getLsbD_of_ge _ _ (by omega : w ≤ bit.val)] using hz

/-- The bit string at the position given by the value of a binary index, or all-false if the
value is not a position. Positions beyond `2 ^ k` are never selected. -/
@[expose] def selectBits (index : BitVec k) (values : Fin R → BitString w) : BitString w :=
  fun bit => decide (∃ j : Fin R, index.toNat = j.val ∧ values j bit = true)

/-- An index whose value is a position selects exactly that bit string. -/
theorem selectBits_of_toNat_lt (index : BitVec k) (values : Fin R → BitString w)
    (hi : index.toNat < R) : selectBits index values = values ⟨index.toNat, hi⟩ := by
  funext bit
  apply Bool.eq_iff_iff.mpr
  simp only [selectBits, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, hv⟩
    rwa [show (⟨index.toNat, hi⟩ : Fin R) = j from Fin.ext hj]
  · exact fun hv => ⟨_, rfl, hv⟩

/-- An index whose value is not a position selects all-false. -/
theorem selectBits_of_le_toNat (index : BitVec k) (values : Fin R → BitString w)
    (hi : R ≤ index.toNat) : selectBits index values = fun _ => false := by
  funext bit
  simp only [selectBits, decide_eq_false_iff_not, not_exists, not_and]
  intro j hj
  omega

/-- An in-range position written as an index selects exactly its bit string. -/
theorem selectBits_ofNat (hR : R ≤ 2 ^ k) (values : Fin R → BitString w) (j : Fin R) :
    selectBits (BitVec.ofNat k j.val) values = values j := by
  have hj : (BitVec.ofNat k j.val).toNat = j.val := by
    simp [Nat.mod_eq_of_lt (j.isLt.trans_le hR)]
  exact (selectBits_of_toNat_lt _ _ (hj.symm ▸ j.isLt)).trans (congrArg values (Fin.ext hj))

end Boolean

namespace Synthesis

open Boolean

variable {n k w R : ℕ} {s : Set (BooleanFunction n)}

/-- One available control bit selects between two available functions in four gates. -/
theorem mux {f a b : BooleanFunction n} (hf : f ∈ s) (ha : a ∈ s) (hb : b ∈ s) :
    Synthesis interpretation s {fun x => if f x then a x else b x} 4 := by
  convert ((of_mem hf).and (of_mem ha)).or ((of_mem hf).not.and (of_mem hb)) using 2
  funext x
  cases f x <;> simp

section Arithmetic

variable (a b : BitString n → BitVec w)

private lemma carry_step {s' : Set (BooleanFunction n)} (c : Bool) (t : ℕ) {m : ℕ}
    (hat : Synthesis interpretation s' {fun x => (a x).getLsbD t} 0)
    (hbt : Synthesis interpretation s' {fun x => (b x).getLsbD t} 0)
    (hct : Synthesis interpretation s' {fun x => BitVec.carry t (a x) (b x) c} m) :
    Synthesis interpretation s' {fun x => BitVec.carry (t + 1) (a x) (b x) c} (m + 4) := by
  convert ((hat.and hbt).or ((hat.or hbt).and hct)).mono Set.Subset.rfl Set.Subset.rfl
    (by omega : _ ≤ m + 4) using 2
  funext x
  rw [BitVec.carry_succ]
  cases (a x).getLsbD t <;> cases (b x).getLsbD t <;> cases BitVec.carry t (a x) (b x) c <;> rfl

/-- One carry chain uses four gates per bit and its initial constant. -/
private theorem word_carry (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) (c : Bool) {t : ℕ} (ht : t ≤ w) :
    Synthesis interpretation s {fun x => BitVec.carry t (a x) (b x) c} (4 * t + 1) := by
  induction t with
  | zero => simpa using Synthesis.const c
  | succ t ih =>
    exact (carry_step a b c t (of_mem (ha ⟨t, by omega⟩)) (of_mem (hb ⟨t, by omega⟩))
      (ih (by omega))).mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-- All carries of a sum, each computed once from the previous one. -/
private theorem word_carries (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) (c : Bool) :
    Synthesis interpretation s
      (stages (fun t => {fun x => BitVec.carry t (a x) (b x) c}) w) (4 * w + 1) := by
  let q := fun t => ({fun x => BitVec.carry t (a x) (b x) c} : Set (BooleanFunction n))
  have h0 : Synthesis interpretation s (q 0) 1 := by simpa [q] using Synthesis.const c
  have hs := steps (I := interpretation) (s := s ∪ q 0) q 4 w Set.subset_union_right fun t ht =>
    carry_step a b c t (of_mem (Or.inl (Or.inl (ha ⟨t, ht⟩))))
      (of_mem (Or.inl (Or.inl (hb ⟨t, ht⟩)))) (of_mem (Or.inr (subset_stages q le_rfl rfl)))
  simpa [Nat.add_comm, Nat.mul_comm] using h0.trans hs

/-- Ripple-carry addition with an initial carry: four gates per carry, eight per sum bit and
the initial constant. -/
theorem word_addCarry (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) (c : Bool) :
    Synthesis interpretation s
      (wordWires fun x => a x + b x + BitVec.setWidth w (BitVec.ofBool c)) (12 * w + 1) := by
  let C := stages (fun t => {fun x => BitVec.carry t (a x) (b x) c}) w
  have h := (word_carries a b ha hb c).trans <| family (I := interpretation) (s := s ∪ C)
    (fun i : Fin w => fun x => (a x + b x + BitVec.setWidth w (BitVec.ofBool c)).getLsbD i.val)
    (fun _ => 8) fun i => by
      simpa only [BitVec.getLsbD_add_add_bool i.isLt] using
        (of_mem (Or.inl (ha i))).xor ((of_mem (Or.inl (hb i))).xor
          (of_mem (Or.inr (subset_stages _ i.isLt.le rfl))))
  exact h.mono Set.Subset.rfl Set.Subset.rfl
    (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; omega)

/-- Ripple-carry addition modulo the word width. -/
theorem word_add (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s (wordWires fun x => a x + b x) (12 * w + 1) := by
  simpa using word_addCarry a b ha hb false

/-- A hardwired word uses one constant gate per bit. -/
theorem word_const (v : BitVec w) : Synthesis interpretation s (wordWires fun _ => v) w := by
  simpa [wordWires] using family (I := interpretation) (s := s)
    (fun i : Fin w => fun _ => v.getLsbD i.val) (fun _ => 1) fun _ => Synthesis.const _

/-- Bitwise complementation uses one gate per bit. -/
theorem word_not (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s (wordWires fun x => ~~~b x) w := by
  have h := family (I := interpretation) (s := s)
    (fun i : Fin w => fun x => !(b x).getLsbD i.val) (fun _ => 1)
    fun i => (of_mem (hb i)).not
  simpa only [wordWires, BitVec.getLsbD_not, Fin.is_lt, decide_true, Bool.true_and,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one] using h

/-- Unsigned comparison, by the carry of `a + ~~~b + 1`. -/
theorem word_ult (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s {fun x => (a x).ult (b x)} (5 * w + 2) := by
  have hc := word_carry (s := s ∪ wordWires fun x => ~~~b x) a (fun x => ~~~b x)
    (fun i => Or.inl (ha i)) (fun i => Or.inr ⟨i, rfl⟩) true le_rfl
  have h := (word_not b hb).trans hc.not
  simpa only [BitVec.ult_eq_not_carry, Nat.mul_succ, Nat.add_assoc,
    show w + (4 * w + 1 + 1) = 5 * w + 2 by omega] using h

/-- Subtraction modulo the word width, as `a + ~~~b + 1`. -/
theorem word_sub (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s (wordWires fun x => a x - b x) (13 * w + 1) := by
  have h := (word_not b hb).trans <| word_addCarry (s := s ∪ wordWires fun x => ~~~b x)
    a (fun x => ~~~b x) (fun i => Or.inl (ha i)) (fun i => Or.inr ⟨i, rfl⟩) true
  have heq (x : BitString n) :
      a x - b x = a x + ~~~b x + BitVec.setWidth w (BitVec.ofBool true) := by
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
    exact congrArg _ (BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_setWidth]))
  simpa only [← heq] using h.mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-- A word multiplexer shares one available control bit, four gates per bit. -/
theorem word_mux (flag : BooleanFunction n) (hf : flag ∈ s)
    (ha : ∀ i : Fin w, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin w, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s (wordWires fun x => if flag x then a x else b x) (4 * w) := by
  simpa [wordWires, Nat.mul_comm] using family (I := interpretation) (s := s)
    (fun i : Fin w => fun x => (if flag x then a x else b x).getLsbD i.val) (fun _ => 4) fun i => by
      simpa only [apply_ite (BitVec.getLsbD · i.val)] using mux hf (ha i) (hb i)

end Arithmetic

/-- Testing a word against a constant needs one literal per bit and a conjunction. -/
theorem word_eq_const (a : BitString n → BitVec k)
    (ha : ∀ i : Fin k, (fun x => (a x).getLsbD i.val) ∈ s) (v : BitVec k) :
    Synthesis interpretation s {fun x => decide (a x = v)} (2 * k + 1) := by
  have h := forall_mem (s := s) Finset.univ
    (fun i : Fin k => fun x => decide ((a x).getLsbD i.val = v.getLsbD i.val))
    (fun _ => 1) fun i _ => by
      cases hv : v.getLsbD i.val
      · simpa only [hv, Bool.decide_eq_false] using (of_mem (ha i)).not
      · simpa only [hv, Bool.decide_eq_true] using
          (of_mem (ha i)).mono Set.Subset.rfl Set.Subset.rfl (Nat.zero_le 1)
  have heq (x : BitString n) : (∀ i : Fin k, (a x).getLsbD i.val = v.getLsbD i.val) ↔ a x = v :=
    ⟨fun h => BitVec.eq_of_getLsbD_eq fun i hi => h ⟨i, hi⟩,
      fun h i => congrArg (·.getLsbD i.val) h⟩
  simpa only [Finset.mem_univ, forall_true_left, decide_eq_true_eq, heq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, Nat.mul_comm] using h

/-- Selecting among available bit strings by an available index charges one comparison with
each position for every output bit. -/
theorem selectBits (index : BitString n → BitVec k) (values : Fin R → BitString n → BitString w)
    (hi : ∀ i : Fin k, (fun x => (index x).getLsbD i.val) ∈ s)
    (hv : ∀ j bit, (fun x => values j x bit) ∈ s) :
    Synthesis interpretation s
      (Set.range fun bit x => Boolean.selectBits (index x) (fun j => values j x) bit)
      (w * (R * (2 * k + 3) + 1)) := by
  simpa using family (I := interpretation) (s := s)
    (fun bit x => Boolean.selectBits (index x) (fun j => values j x) bit)
    (fun _ => R * (2 * k + 3) + 1) fun bit => by
      simpa [Boolean.selectBits, Nat.add_assoc] using exists_mem (s := s) Finset.univ
        (fun j : Fin R => fun x => decide ((index x).toNat = j.val) && values j x bit)
        (fun _ => 2 * k + 2) fun j _ => by
          by_cases hj : j.val < 2 ^ k
          · simpa only [BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj] using
              (word_eq_const index hi (BitVec.ofNat k j.val)).and (of_mem (hv j bit))
          · convert (Synthesis.const false).mono Set.Subset.rfl Set.Subset.rfl
              (Nat.le_add_left 1 _) using 2
            funext x
            have := (index x).isLt
            simp only [Bool.and_eq_false_imp, decide_eq_true_eq]
            omega

end Synthesis

end Cslib.Circuits
