/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter
import all CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter

/-!
# Correctness of the refuter's affine-representation oracle

`evaluateAux S a val` asks the dense XOR-SAT decider whether the affine system of `S`, the
parameter values `val` and `a = 0` are simultaneously satisfiable. On a well-formed state this
returns the value of the auxiliary variable `a` in the unique solution extending `val`, so
`findAffineRep S a` recovers the affine representation of `a` in the parameters.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.evaluateAux_eq`: `evaluateAux` evaluates an
  auxiliary variable.
* `Cslib.Circuits.Boolean.AffineDisperser4n.findAffineRep_spec`: `findAffineRep` is the affine
  representation of an auxiliary variable.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Complexity.XORSAT.Dense Cslib.Circuits Cslib.BitString

variable {n : ℕ}

private theorem dot_map_decide (T : Finset ℕ) (w : ℕ → Bool) :
    ∀ l : List ℕ, dot (l.map fun i => decide (i ∈ T)) (l.map w) =
      (l.map fun i => if i ∈ T then w i else 0).sum
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, dot, dot_map_decide T w l, List.sum_cons]
    by_cases ha : a ∈ T <;>
      simp only [ha, decide_true, decide_false, ite_true, ite_false] <;> cases w a <;> rfl

private theorem dot_toDenseRow (N : ℕ) (T : Finset ℕ) (w : ℕ → Bool) (hT : ∀ i ∈ T, i < N) :
    dot ((List.range N).map fun i => decide (i ∈ T)) ((List.range N).map w) = ∑ i ∈ T, w i := by
  rw [dot_map_decide, show ((List.range N).map fun i => if i ∈ T then w i else 0).sum =
    ∑ i ∈ Finset.range N, if i ∈ T then w i else 0 from rfl, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 fun i hi => Finset.mem_range.2 (hT i hi)]

/-- The dense system queried by `evaluateAux S a val`. -/
private abbrev auxSystem (S : State n) (a : ℕ) (val : ℕ → Bool) : System :=
  ((S.eqns.sort (· ≤ ·)).map fun e => toDenseRow (varBound S) (S.eqn e).terms (S.eqn e).rhs) ++
    ((S.params.sort (· ≤ ·)).map fun p => toDenseRow (varBound S) {p} (val p)) ++
    [toDenseRow (varBound S) {a} false]

private theorem width_auxSystem (S : State n) (a : ℕ) (val : ℕ → Bool) :
    Width (varBound S) (auxSystem S a val) := by
  simp only [Width, auxSystem, List.mem_append, List.mem_map, List.mem_singleton]
  rintro _ ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | rfl) <;> simp [toDenseRow]

private theorem dot_toDenseRow_varBound {S : State n} {T : Finset ℕ} (hT : T ⊆ S.params ∪ S.aux)
    (c : Bool) (v : ℕ → Bool) :
    dot (toDenseRow (varBound S) T c).coeffs ((List.range (varBound S)).map v) =
      ∑ i ∈ T, v i :=
  dot_toDenseRow _ _ _ fun _ hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) (hT hi))

private theorem holds_auxSystem_iff {S : State n} (hwf : S.WellFormed) {a : ℕ}
    (ha : a ∈ S.params ∪ S.aux) (val v : ℕ → Bool) :
    Holds (auxSystem S a val) ((List.range (varBound S)).map v) ↔
      S.EqnsHold v ∧ (∀ p ∈ S.params, v p = val p) ∧ v a = false := by
  simp only [Holds, List.forall_mem_append, List.forall_mem_map, Finset.mem_sort,
    List.forall_mem_singleton, and_assoc]
  refine and_congr (forall₂_congr fun e he => ?_) (and_congr (forall₂_congr fun p hp => ?_) ?_)
  · rw [dot_toDenseRow_varBound (hwf.terms_subset e he)]; rfl
  · rw [dot_toDenseRow_varBound (Finset.singleton_subset_iff.2 (Finset.mem_union_left _ hp)),
      Finset.sum_singleton]; rfl
  · rw [dot_toDenseRow_varBound (Finset.singleton_subset_iff.2 ha), Finset.sum_singleton]; rfl

private theorem satisfiable_auxSystem_iff {S : State n} (hwf : S.WellFormed) {a : ℕ}
    (ha : a ∈ S.params ∪ S.aux) (val : ℕ → Bool) :
    Satisfiable (varBound S) (auxSystem S a val) ↔
      ∃ v, S.EqnsHold v ∧ (∀ p ∈ S.params, v p = val p) ∧ v a = false := by
  refine ⟨fun ⟨l, hl, hH⟩ => ⟨fun i => l.getD i false, ?_⟩,
    fun ⟨v, hv⟩ => ⟨_, by simp, (holds_auxSystem_iff hwf ha val v).2 hv⟩⟩
  rw [← holds_auxSystem_iff hwf ha,
    show ((List.range (varBound S)).map fun i => l.getD i false) = l from
      List.ext_getElem (by simp [hl]) fun i _ h₂ => by simp [h₂]]
  exact hH

/-- `evaluateAux S a val` is the value of the auxiliary variable `a` in the solution of the affine
system extending the parameter assignment `val`. -/
theorem evaluateAux_eq {S : State n} (hwf : S.WellFormed) {a : ℕ} (ha : a ∈ S.aux)
    {val w : ℕ → Bool} (hw : ∀ j ∈ S.params, w j = val j) (hweq : S.EqnsHold w) :
    evaluateAux S a val = w a := by
  have key : Cslib.Complexity.XORSAT.Dense.decide ⟨varBound S, auxSystem S a val⟩ = true ↔
      w a = false := by
    rw [decide_eq_true_iff, and_iff_right (width_auxSystem S a val),
      satisfiable_auxSystem_iff hwf (Finset.mem_union_right _ ha)]
    exact ⟨fun ⟨v, hv, hvp, hva⟩ =>
      hva ▸ hwf.unique w v (fun j hj => (hw j hj).trans (hvp j hj).symm) hweq hv a ha,
      fun hwa => ⟨w, hweq, hw, hwa⟩⟩
  change (if Cslib.Complexity.XORSAT.Dense.decide ⟨varBound S, auxSystem S a val⟩ then false
    else true) = w a
  cases hwa : w a
  · exact ite_eq_left (key.2 hwa)
  · exact ite_eq_right fun h => Bool.noConfusion (hwa.symm.trans (key.1 h))

/-- On an auxiliary variable `a = c + ∑ j ∈ T, u j`, `evaluateAux S a val` evaluates the affine
expression at `val`. -/
theorem evaluateAux_eq_of_affineIn {S : State n} (hwf : S.WellFormed) {a : ℕ} (ha : a ∈ S.aux)
    {c : Bool} {T : Finset ℕ} (h : S.AffineIn a c T) (val : ℕ → Bool) :
    evaluateAux S a val = c + ∑ j ∈ T, val j := by
  obtain ⟨w, hw, hweq⟩ := hwf.solvable val
  rw [evaluateAux_eq hwf ha hw hweq, h.2 w hweq]
  exact congrArg (c + ·) (Finset.sum_congr rfl fun j hj => hw j (h.1 hj))

/-- `findAffineRep S Q` is the affine representation of the auxiliary variable `Q` in the
parameters. -/
theorem findAffineRep_spec {S : State n} (hwf : S.WellFormed) {Q : ℕ} (hQ : Q ∈ S.aux) :
    S.AffineIn Q (findAffineRep S Q).1 (findAffineRep S Q).2 := by
  obtain ⟨c, T, h⟩ := hwf.exists_affineIn hQ
  have h0 : evaluateAux S Q (fun _ => false) = c :=
    (evaluateAux_eq_of_affineIn hwf hQ h _).trans
      ((congrArg (c + ·) Finset.sum_const_zero).trans (add_zero c))
  have hT : (findAffineRep S Q).2 = T := by
    ext y
    simp only [findAffineRep, Finset.mem_filter, h0, evaluateAux_eq_of_affineIn hwf hQ h]
    have hsum : ∑ j ∈ T, (j == y) = if y ∈ T then 1 else 0 := by
      rw [← Finset.sum_ite_eq' T y fun _ => (1 : Bool)]
      exact Finset.sum_congr rfl fun j _ => by
        by_cases hj : j = y <;> simp [hj, beq_false_of_ne] <;> rfl
    rw [hsum]
    by_cases hy : y ∈ T
    · simp only [hy, ite_true, iff_true]; exact ⟨h.1 hy, by cases c <;> rfl⟩
    · simp only [hy, ite_false, iff_false, not_and]; exact fun _ => by cases c <;> decide
  change S.AffineIn Q (evaluateAux S Q fun _ => false) (findAffineRep S Q).2
  rwa [h0, hT]

end Cslib.Circuits.Boolean.AffineDisperser4n
