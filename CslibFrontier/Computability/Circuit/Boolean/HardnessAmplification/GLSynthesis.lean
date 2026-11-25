/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AtLeast
public import CslibFrontier.Computability.Circuit.Synthesis
public import CslibFrontier.Crypto.Computational.GoldreichLevin.Decoding

/-!
# De Morgan circuits for Goldreich–Levin candidates

Let `C` be a predictor on `a + w` bits with a De Morgan circuit of at most `s` gates, and suppose
its first `a` input bits are available as functions `xb k`. Fix `K` masks and a guess. One bit of
the corrected-majority candidate for `r ↦ C (xb, r)` takes `2 ^ K - 1` copies of `C`, each with at
most one negation, and a strict majority: `glBitCost K s` further gates once the two constants
are available (`Cslib.Circuits.Boolean.synthesis_candidate_apply`). All `w` bits together, with
the constants, take `glCost w K s` gates (`Cslib.Circuits.Boolean.synthesis_candidate`), and one
bit as a circuit on the inputs takes `2 + glBitCost K s` gates
(`Cslib.Circuits.Boolean.complexity_candidate_apply_le`).

The statements fix no layout of the `a` bits. The Goldreich–Levin stage of worst-case
reconstruction reads them as the bits of a point of a field
(`Cslib.Circuits.Boolean.bitSynthesis_glPredictor`). The amplification reconstruction of
Carmosino, Impagliazzo, Kabanets and Kolokolova reads them as `k` blocks of `n` bits
(`Cslib.Circuits.Boolean.complexity_glAmpCandidate_apply_le`).

## Main definitions

* `Cslib.Circuits.Boolean.glBitCost`, `Cslib.Circuits.Boolean.glCost`: the gate budgets for one
  bit and for all bits of a candidate.

## Main results

* `Cslib.Circuits.Boolean.synthesis_candidate_apply`: one bit of a candidate.
* `Cslib.Circuits.Boolean.synthesis_candidate`: all bits of a candidate.
* `Cslib.Circuits.Boolean.complexity_candidate_apply_le`: the circuit complexity of one bit.

## References

* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
-/

public section

namespace Cslib.Circuits.Boolean

open Finset

/-- The gate budget of one bit of a Goldreich–Levin candidate with `K` masks and a predictor of
size `s`, given the two constants: `2 ^ K - 1` copies of the predictor, each with at most one
negation, and a strict majority. -/
@[expose] def glBitCost (K s : ℕ) : ℕ :=
  (2 ^ K - 1) * (s + 1) + (2 + (2 ^ K - 1) * (2 * (2 ^ K - 1 + 2)))

/-- The gate budget of a Goldreich–Levin candidate with `w` output bits, `K` masks and a predictor
of size `s`: two constants, and `glBitCost K s` gates for each output bit. -/
@[expose] def glCost (w K s : ℕ) : ℕ :=
  2 + w * ((2 ^ K - 1) * (s + 1) + (2 + (2 ^ K - 1) * (2 * (2 ^ K - 1 + 2))))

theorem glCost_eq (w K s : ℕ) : glCost w K s = 2 + w * glBitCost K s :=
  rfl

private theorem append_apply {n p q : ℕ} (A : Fin p → BooleanFunction n)
    (B : Fin q → BooleanFunction n) (k : Fin (p + q)) (v : Fin n → Bool) :
    Fin.append A B k v = Fin.append (fun i => A i v) (fun i => B i v) k := by
  exact Fin.addCases (fun _ => by simp only [Fin.append_left])
    (fun _ => by simp only [Fin.append_right]) k

/-- A strict majority of the `N` votes of a finset, enumerated, is a threshold of `N` functions. -/
private theorem strictMajorityOn_eq_atLeast {n : ℕ} {ι : Type*} (T : Finset ι)
    (vote : ι → BooleanFunction n) (v : Fin n → Bool) :
    BitString.strictMajorityOn T (fun i => vote i v) =
      atLeast (fun l => if h : l < #T then vote (T.equivFin.symm ⟨l, h⟩) else fun _ => false)
        #T (#T / 2 + 1) v := by
  classical
  simp only [BitString.strictMajorityOn, atLeast]
  congr 1
  rw [Nat.lt_iff_add_one_le]
  congr 1
  refine card_bij (fun i hi => (T.equivFin ⟨i, (mem_filter.1 hi).1⟩ : ℕ))
    (fun i hi => ?_) (fun _ _ _ _ h => congrArg Subtype.val (T.equivFin.injective (Fin.ext h)))
    fun l hl => ?_
  · exact mem_filter.2 ⟨mem_range.2 (T.equivFin _).2, by
      rw [dite_eq_left (T.equivFin _).2]; simpa using (mem_filter.1 hi).2⟩
  · obtain ⟨hl, hv⟩ := mem_filter.1 hl
    exact ⟨T.equivFin.symm ⟨l, mem_range.1 hl⟩, mem_filter.2
      ⟨(T.equivFin.symm ⟨l, mem_range.1 hl⟩).2, by rwa [dite_eq_left (mem_range.1 hl)] at hv⟩,
      by simp⟩

variable {a w n : ℕ}

/-- **One bit of a Goldreich–Levin candidate.** If the predictor `C` has a De Morgan circuit with
at most `sC` gates, and its first `a` input bits `xb` and the two constants are available, then
bit `j` of the candidate with masks `masks` and guess `guess` can be made available with
`glBitCost K sC` further gates. -/
theorem synthesis_candidate_apply {C : BooleanFunction (a + w)} {sC : ℕ}
    (hC : complexity interpretation (single C) ≤ sC) {K : ℕ} (masks : Fin K → BitString w)
    (guess : BitString K) {S : Set (BooleanFunction n)} (xb : Fin a → BooleanFunction n)
    (hxb : ∀ k, xb k ∈ S) (htrue : (fun _ => true) ∈ S) (hfalse : (fun _ => false) ∈ S)
    (j : Fin w) :
    Synthesis interpretation S
      {fun v => Crypto.GoldreichLevin.candidate (fun r => C (Fin.append (fun k => xb k v) r))
        masks guess j}
      (glBitCost K sC) := by
  classical
  obtain ⟨c, hc, hsize⟩ := complexity_le_iff.1 hC
  have hvote (r : BitString w) (bit : Bool) : Synthesis interpretation S
      {fun v => C (Fin.append (fun k => xb k v) r) ^^ bit} (sC + 1) := by
    let g : Fin (a + w) → BooleanFunction n := Fin.append xb fun k _ => r k
    have hg (k : Fin (a + w)) : g k ∈ S := Fin.addCases
      (fun i => by simp only [g, Fin.append_left]; exact hxb i)
      (fun i => by simp only [g, Fin.append_right]; cases r i <;> assumption) k
    have heval : (fun v => c.eval interpretation (fun k => g k v) 0) =
        fun v => C (Fin.append (fun k => xb k v) r) := funext fun v => by
      rw [hc]
      simp only [single_apply]
      exact congrArg C (funext fun k => append_apply _ _ k v)
    have h1 := (Synthesis.circuit (I := interpretation) c g hg).mono Set.Subset.rfl
      (Set.singleton_subset_iff.2 ⟨0, heval⟩) hsize
    cases bit
    · simpa using h1.mono Set.Subset.rfl Set.Subset.rfl (Nat.le_succ _)
    · simpa using h1.not
  set T := Crypto.GoldreichLevin.nonemptySubsets K
  let V (t : Finset (Fin K)) (v : Fin n → Bool) : Bool :=
    C (Fin.append (fun k => xb k v) (Pi.single j 1 + ∑ l ∈ t, masks l)) ^^ ∑ l ∈ t, guess l
  have hvotes := Synthesis.biUnion (I := interpretation) (s := S) T (fun t => {V t})
    (fun _ => sC + 1) fun t _ => hvote _ _
  have hmaj := synthesis_atLeast (s := S ∪ ⋃ t ∈ T, {V t}) (k := #T) (j := #T / 2 + 1)
    (fun l => if h : l < #T then V (T.equivFin.symm ⟨l, h⟩) else fun _ => false)
    (fun l hl => by
      rw [dite_eq_left hl]
      exact Set.mem_union_right _ (Set.mem_biUnion (T.equivFin.symm ⟨l, hl⟩).2 rfl)) (by omega)
  refine (hvotes.trans hmaj).mono Set.Subset.rfl
    (Set.singleton_subset_iff.2 (funext fun v => strictMajorityOn_eq_atLeast T V v)) ?_
  simp only [sum_const, smul_eq_mul, glBitCost, T, Crypto.GoldreichLevin.card_nonemptySubsets,
    le_refl]

/-- **All bits of a Goldreich–Levin candidate.** If the predictor `C` has a De Morgan circuit
with at most `sC` gates and its first `a` input bits `xb` are available, then the bits of the
candidate with masks `masks` and guess `guess` can be made available with `glCost w K sC`
further gates. -/
theorem synthesis_candidate {C : BooleanFunction (a + w)} {sC : ℕ}
    (hC : complexity interpretation (single C) ≤ sC) {K : ℕ} (masks : Fin K → BitString w)
    (guess : BitString K) {S : Set (BooleanFunction n)} (xb : Fin a → BooleanFunction n)
    (hxb : ∀ k, xb k ∈ S) :
    Synthesis interpretation S
      (Set.range fun j v =>
        Crypto.GoldreichLevin.candidate (fun r => C (Fin.append (fun k => xb k v) r)) masks
          guess j)
      (glCost w K sC) := by
  have hconst : Synthesis interpretation S ({fun _ => true} ∪ {fun _ => false}) 2 :=
    (Synthesis.const (s := S) true).union (Synthesis.const (s := S) false)
  let bit : Fin w → BooleanFunction n := fun j v =>
    Crypto.GoldreichLevin.candidate (fun r => C (Fin.append (fun k => xb k v) r)) masks guess j
  have hall := Synthesis.iUnion (I := interpretation)
    (s := S ∪ ({fun _ => true} ∪ {fun _ => false})) (fun j => {bit j})
    (fun _ => glBitCost K sC) fun j =>
      synthesis_candidate_apply hC masks guess xb (fun k => Set.mem_union_left _ (hxb k))
        (Set.mem_union_right _ (Set.mem_union_left _ rfl))
        (Set.mem_union_right _ (Set.mem_union_right _ rfl)) j
  exact (hconst.trans hall).mono Set.Subset.rfl
    (by rintro _ ⟨j, rfl⟩; exact Set.mem_iUnion.2 ⟨j, rfl⟩) (by simp [glCost_eq])

/-- **The circuit complexity of one bit of a Goldreich–Levin candidate**, as a function of the
first `a` input bits of the predictor: at most `2 + glBitCost K sC` gates, the two constants and
one bit. -/
theorem complexity_candidate_apply_le {C : BooleanFunction (a + w)} {sC : ℕ}
    (hC : complexity interpretation (single C) ≤ sC) {K : ℕ} (masks : Fin K → BitString w)
    (guess : BitString K) (j : Fin w) :
    complexity interpretation
        (single fun x : BitString a => Crypto.GoldreichLevin.candidate
          (fun r => C (Fin.append x r)) masks guess j) ≤
      2 + glBitCost K sC := by
  refine Synthesis.complexity_le ?_
  have hconst : Synthesis interpretation (inputs a) ({fun _ => true} ∪ {fun _ => false}) 2 :=
    (Synthesis.const true).union (Synthesis.const false)
  exact hconst.trans (synthesis_candidate_apply (S := inputs a ∪ _) hC masks guess (fun k x => x k)
    (fun k => Set.mem_union_left _ ⟨k, rfl⟩) (Set.mem_union_right _ (Set.mem_union_left _ rfl))
    (Set.mem_union_right _ (Set.mem_union_right _ rfl)) j)

end Cslib.Circuits.Boolean
