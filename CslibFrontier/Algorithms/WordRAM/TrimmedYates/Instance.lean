/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Basic
public import CslibFrontier.Computability.WordRAM.InputArray
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Regs

/-!
# Sparse set-function entries and problem instances for trimmed Yates

Word-level encoding, weight envelopes, and input admissibility for sparse weighted set-function
instances over `Fin d` ([ChanItakuraMaYu2026], Problem 2.1 / Theorem 2.2).

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.evalEntries`, `entryAbsSum`, `encodeEntries`: mathematical
  semantics, absolute-weight sum, and flat word encoding of sparse `(set, weight)` entry lists.
* `Cslib.Algorithms.WordRAM.TrimmedYates.Instance`: sparse weighted set-function instance over
  `Fin d`, with `leftFn`, `rightFn`, `numEntries`, `weightSum`, `encode`, `spaceBound`, `timeBound`,
  and `FitsWidth`.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.evalEntries_eq_sum_filter`, `evalEntries_ranked`,
  `natAbs_evalEntries_le`: filter-sum characterization, rank preservation, and weight bound for
  `evalEntries`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.length_encodeEntries`,
  `Instance.length_encode`, `Instance.FitsWidth.inputFits`: word-layout characterizations and
  `InputFits` admissibility.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.WordRAM.TrimmedYates

open Finset Cslib.WordRAM

/-- Set function represented by a list of sparse `(set, weight)` entries, summing duplicate keys. -/
@[expose] def evalEntries {d : ℕ} (es : List (Finset (Fin d) × ℤ)) (S : Finset (Fin d)) : ℤ :=
  es.foldl (fun fn p X => if X = p.1 then fn X + p.2 else fn X) (fun _ => 0) S

private theorem evalEntries_append_singleton {d : ℕ} (es : List (Finset (Fin d) × ℤ))
    (p : Finset (Fin d) × ℤ) (S : Finset (Fin d)) :
    evalEntries (es ++ [p]) S = if S = p.1 then evalEntries es S + p.2 else evalEntries es S := by
  simp only [evalEntries, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem evalEntries_eq_sum_filter {d : ℕ} (es : List (Finset (Fin d) × ℤ)) (S : Finset (Fin d)) :
    evalEntries es S = ((es.filter fun p => decide (p.1 = S)).map Prod.snd).sum := by
  induction es using List.reverseRecOn with
  | nil => rfl
  | append_singleton es p ih =>
    rw [evalEntries_append_singleton, ih, List.filter_append, List.map_append, List.sum_append]
    by_cases hSA : S = p.1 <;> simp [hSA, eq_comm]

theorem evalEntries_ranked {d t : ℕ} {es : List (Finset (Fin d) × ℤ)}
    (hes : ∀ p ∈ es, p.2 ≠ 0 → #p.1 = t) (S : Finset (Fin d)) (hS : evalEntries es S ≠ 0) :
    #S = t := by
  contrapose! hS
  rw [evalEntries_eq_sum_filter]
  refine List.sum_eq_zero fun v hv => ?_
  obtain ⟨p, hp_flt, rfl⟩ := List.mem_map.mp hv
  obtain ⟨hp_es, hp_eq⟩ := List.mem_filter.mp hp_flt
  by_contra hv0
  exact hS ((of_decide_eq_true hp_eq) ▸ hes p hp_es hv0)

/-- Sum of `|v|` across sparse `(set, v)` entries. -/
@[expose] def entryAbsSum {d : ℕ} (es : List (Finset (Fin d) × ℤ)) : ℕ :=
  (es.map fun p => p.2.natAbs).sum

theorem natAbs_evalEntries_le {d : ℕ} (es : List (Finset (Fin d) × ℤ))
    (S : Finset (Fin d)) : (evalEntries es S).natAbs ≤ entryAbsSum es := by
  induction es using List.reverseRecOn with
  | nil => simp [evalEntries, entryAbsSum]
  | append_singleton es p ih =>
    rw [evalEntries_append_singleton, entryAbsSum, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [← entryAbsSum]
    split_ifs
    · exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add_right ih _)
    · exact ih.trans (Nat.le_add_right _ _)

/-- Word encoding of a sparse `(set, weight)` list: `[setMask S₀, Signed.encode v₀, ...]`. -/
@[expose] def encodeEntries {d : ℕ} (es : List (Finset (Fin d) × ℤ)) : List ℕ :=
  es.flatMap fun p => [setMask p.1, Signed.encode p.2]

@[simp] theorem length_encodeEntries {d : ℕ} (es : List (Finset (Fin d) × ℤ)) :
    (encodeEntries es).length = 2 * es.length := by
  simp [encodeEntries, List.length_flatMap, Nat.mul_comm]

/-- Sparse weighted set-function instance over `Fin d` with threshold `s` and query sets `queries`.
In the ranked setting of [ChanItakuraMaYu2026], Problem 2.1 / Theorem 2.2, `leftEntries` are
supported on sets of size `t₁`, `rightEntries` on sets of size `t₂`, and `queries` have size
`t₁ + t₂` (`t₁ = t₂ = t` in Theorem 2.2). -/
structure Instance where
  /-- Universe dimension `d` (ground set `Fin d`). -/
  d : ℕ
  /-- Trimming threshold `s`. -/
  s : ℕ
  /-- Sparse `(set, weight)` pairs summing to the left input function `f`. -/
  leftEntries : List (Finset (Fin d) × ℤ)
  /-- Sparse `(set, weight)` pairs summing to the right input function `g`. -/
  rightEntries : List (Finset (Fin d) × ℤ)
  /-- Query subsets `Cs` at which to evaluate the covering product / subset convolution. -/
  queries : List (Finset (Fin d))

/-- Left input set function `f : Finset (Fin inst.d) → ℤ`. -/
@[expose] def Instance.leftFn (inst : Instance) : Finset (Fin inst.d) → ℤ :=
  evalEntries inst.leftEntries

/-- Right input set function `g : Finset (Fin inst.d) → ℤ`. -/
@[expose] def Instance.rightFn (inst : Instance) : Finset (Fin inst.d) → ℤ :=
  evalEntries inst.rightEntries

/-- Total number of sparse input entries `n = |leftEntries| + |rightEntries|`. -/
@[expose] def Instance.numEntries (inst : Instance) : ℕ :=
  inst.leftEntries.length + inst.rightEntries.length

/-- Sum of `|v|` over all sparse input entries. -/
@[expose] def Instance.weightSum (inst : Instance) : ℕ :=
  entryAbsSum inst.leftEntries + entryAbsSum inst.rightEntries

/-- Flat word encoding `[d, s, |leftEntries|, |rightEntries|, |queries|, leftEntries...,
rightEntries..., queryMasks...]`. -/
@[expose] def Instance.encode (inst : Instance) : List ℕ :=
  [inst.d, inst.s, inst.leftEntries.length, inst.rightEntries.length, inst.queries.length] ++
    encodeEntries inst.leftEntries ++
    encodeEntries inst.rightEntries ++
    inst.queries.map setMask

@[simp] theorem Instance.length_encode (inst : Instance) :
    inst.encode.length = 5 + 2 * inst.numEntries + inst.queries.length := by
  simp only [Instance.encode, Instance.numEntries, List.length_append, List.length_cons,
    List.length_nil, length_encodeEntries, List.length_map]
  omega

/-- Peak address bound for executing `program` on `inst`. -/
@[expose] def Instance.spaceBound (inst : Instance) : ℕ :=
  solveSpace (10 + 2 * (inst.d + 1) * inst.numEntries + inst.queries.length)
    inst.d inst.s inst.queries.length (highPeak inst.s inst.queries)

/-- Running-time bound for executing `program` on `inst` (including the final `halt`). -/
@[expose] def Instance.timeBound (inst : Instance) : ℕ :=
  250 * (inst.d + 1) ^ 2 *
    (inst.numEntries + lowCount inst.d inst.s +
      inst.queries.length * max 1 (highPeak inst.s inst.queries))

/-- Word-width admissibility predicate for `inst`. -/
@[expose] def Instance.FitsWidth (inst : Instance) (w : ℕ) : Prop :=
  Fits w inst.spaceBound ∧ Fits w (valueEnvelope inst.d inst.weightSum)

private theorem signedEncode_le_valueEnvelope {d W : ℕ} {z : ℤ} (hz : z.natAbs ≤ W) :
    Signed.encode z ≤ valueEnvelope d W := by
  dsimp only [valueEnvelope, Signed.encode]
  have h1 : 1 ≤ 8 ^ d := Nat.one_le_pow _ _ (by decide)
  have hW : W + 1 ≤ (W + 1) ^ 2 := by rw [sq]; exact Nat.le_mul_self _
  have hmul : W + 1 ≤ 8 ^ d * (W + 1) ^ 2 := hW.trans (Nat.le_mul_of_pos_left _ h1)
  split_ifs <;> omega

/-- Any word width satisfying `inst.FitsWidth w` also fits every word of `inst.encode`. -/
theorem Instance.FitsWidth.inputFits {inst : Instance} {w : ℕ} (h : inst.FitsWidth w) :
    InputFits w inst.encode := by
  obtain ⟨hsp, hval⟩ := h
  have hmask : Fits w (2 ^ inst.d) := mask_fits_of_valueEnvelope hval
  have hnum_le : 2 * inst.numEntries ≤ 2 * (inst.d + 1) * inst.numEntries :=
    Nat.mul_le_mul_right _ (by omega)
  have hsp_le {k : ℕ} (hk : k ≤ 5 + 2 * inst.numEntries + inst.queries.length + inst.s) :
      Fits w k :=
    hsp.of_le (by dsimp only [Instance.spaceBound, solveSpace]; omega)
  have hentry {es : List (Finset (Fin inst.d) × ℤ)} (hes : entryAbsSum es ≤ inst.weightSum)
      {p : Finset (Fin inst.d) × ℤ} (hp : p ∈ es) {v : ℕ}
      (hv : v = setMask p.1 ∨ v = Signed.encode p.2) : Fits w v := by
    rcases hv with rfl | rfl
    · exact hmask.of_le (setMask_lt p.1).le
    · exact hval.of_le (signedEncode_le_valueEnvelope
        ((List.le_sum_of_mem (List.mem_map_of_mem (f := fun x => x.2.natAbs) hp)).trans hes))
  refine ⟨by rw [inst.length_encode]; exact hsp_le (by omega), fun v hv => ?_⟩
  simp only [Instance.encode, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    encodeEntries, List.mem_flatMap, List.mem_map] at hv
  rcases hv with (((rfl | rfl | rfl | rfl | rfl) | ⟨p, hp, hv⟩) | ⟨p, hp, hv⟩) | ⟨C, _, rfl⟩
  · exact hmask.of_le Nat.lt_two_pow_self.le
  · exact hsp_le (by omega)
  · exact hsp_le (by dsimp only [Instance.numEntries]; omega)
  · exact hsp_le (by dsimp only [Instance.numEntries]; omega)
  · exact hsp_le (by omega)
  · exact hentry (Nat.le_add_right _ _) hp hv
  · exact hentry (Nat.le_add_left _ _) hp hv
  · exact hmask.of_le (setMask_lt C).le

end Cslib.Algorithms.WordRAM.TrimmedYates
