/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Metric
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Relation
public import CslibFrontier.Computability.Complexity.Problems.SharpSAT
public import CslibFrontier.Computability.Complexity.Reduction.Levin
import CslibFrontier.Computability.Complexity.CookLevin.Counting
import CslibFrontier.Computability.Complexity.CookLevin.Levin
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# The padded witness relation of SAT

`SAT.paddedRelation` is the artificial witness relation of `SAT` suggested in
[Goldreich, Exercise 6.35][Goldreich2007Draft] (February 2007 `r3.pdf`, printed p. 263 /
PDF p. 61): `(φ, τσ)` is a solution when `τ` describes a satisfying assignment of `φ` and `σ` is
one arbitrary bit. Every solution set has even size, so no formula has a unique solution and
the source's promise problem `(US_R, complement of S_R)`, exactly one solution (yes) versus no
solution (no), is decided by always rejecting. Yet the relation is
PC-complete under Levin reductions, and its count `2 · #SAT` is #P-complete under metric
reductions. `SAT.exercise_6_36a` packages these facts as [Goldreich, Exercise 6.36(a)]
[Goldreich2007Draft]; the first and last clauses are Exercise 6.35.

Formulas are encoded by `encCNF`. The assignment part `τ` is a canonical certificate of the
`#SAT` counting verifier `SharpSAT.verifier`: `|encCNF φ|` bits whose positions at the first
occurrence of each variable in `φ.vars` carry its value and whose other positions are `false`.
Canonical certificates correspond one-to-one to the assignments of the occurring variables, so
`|R(φ)| = 2 · #SAT(φ)` exactly as in the source (`searchCount_paddedRelation`). The padding bit
`σ` is the last bit of the solution.

The source's PC is the library's `NPRelation` (equivalently `FNP`, `NPRelation.isWitness_mem_FNP`)
and PC-completeness is `LevinHard`, reduction with both witness maps. The source defines
#P-completeness by Cook reductions; metric (one-query) completeness is stronger. `#R` is not
#P-complete under parsimonious reductions, since every count of `R` is even.

## Main definitions

* `Cslib.Complexity.SAT.paddedRelation`: the padded witness relation of `SAT`.

## Main results

* `Cslib.Complexity.SAT.paddedRelation_levinHard`: every NP relation Levin-reduces to it.
* `Cslib.Complexity.SAT.searchCount_paddedRelation`: it has `2 · #SAT(φ)` solutions.
* `Cslib.Complexity.SAT.exercise_6_36a`: Goldreich Exercise 6.36(a).
-/

public section

namespace Cslib.Complexity.SAT

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- The **padded witness relation of SAT** [Goldreich, Exercise 6.35][Goldreich2007Draft], on
formulas encoded by `encCNF`: a solution for `φ` is a word `τσ` of `|encCNF φ| + 1` bits whose
first `|encCNF φ|` bits `τ` are a certificate accepted by the `#SAT` counting verifier (a
satisfying assignment written canonically) and whose last bit `σ` is arbitrary. -/
@[expose]
noncomputable def paddedRelation : NPRelation encCNF :=
  ⟨Polynomial.X + 1, fun x => SharpSAT.verifier (x.1, x.2.take (encCNF x.1).length),
    by fun_prop⟩

/-- The solutions of the padded relation are a counting certificate followed by any bit. -/
theorem isWitness_paddedRelation_iff {φ : CNF ℕ} {w : List Bool} :
    paddedRelation.IsWitness φ w ↔ w.length = (encCNF φ).length + 1 ∧
      SharpSAT.verifier (φ, w.take (encCNF φ).length) = true := by
  simp [NPRelation.IsWitness, paddedRelation]

/-- Zero every bit of a `SAT` certificate except at the first occurrences of variables. -/
private def canonicalize (φ : CNF ℕ) (w : List Bool) : List Bool :=
  (List.range w.length).map fun i => w.getD i false && SharpSAT.isFirst φ i

private theorem getD_canonicalize (φ : CNF ℕ) (w : List Bool) (i : ℕ) :
    (canonicalize φ w).getD i false = (w.getD i false && SharpSAT.isFirst φ i) :=
  if hi : i < w.length then List.getD_map_range _ false hi
  else by simp [canonicalize, List.getD_eq_getElem?_getD, Nat.le_of_not_lt hi]

/-- Canonicalizing a certificate keeps the assignment it describes. -/
private theorem verifier_canonicalize (φ : CNF ℕ) (w : List Bool) :
    verifier (φ, canonicalize φ w) = verifier (φ, w) := by
  refine CNF.eval_congr fun v (hv : v ∈ φ.vars) => ?_
  change (canonicalize φ w).getD _ false = w.getD _ false
  rw [getD_canonicalize, SharpSAT.isFirst_idxOf hv, Bool.and_true]

private theorem canonical_canonicalize (φ : CNF ℕ) (w : List Bool) :
    SharpSAT.canonical φ (canonicalize φ w) = true :=
  SharpSAT.canonical_eq_true_iff.2 fun i _ h =>
    ((Bool.and_eq_true _ _).mp (getD_canonicalize φ w i ▸ h)).2

private theorem computableInPolyTime_canonicalize :
    ComputableInPolyTime (fun x : CNF ℕ × List Bool => canonicalize x.1 x.2 ++ [false])
      (encPair encCNF encBits) encBits := by
  fun_prop [canonicalize]

/-- The Levin reduction of the standard witness relation of `SAT` to the padded relation: keep
the formula, canonicalize the certificate and append a `false` bit; drop the last bit back. -/
private noncomputable def toPaddedRelation : LevinReduction npRelation paddedRelation where
  toFun := id
  forwardWitness x := canonicalize x.1 x.2 ++ [false]
  backwardWitness x := x.2.take (encCNF x.1).length
  computableInPolyTime_toFun := .id'
  computableInPolyTime_forwardWitness := computableInPolyTime_canonicalize
  computableInPolyTime_backwardWitness := by fun_prop
  isWitness_forwardWitness φ w h := by
    rw [isWitness_npRelation_iff] at h
    have hlen : (canonicalize φ w).length = (encCNF φ).length := by
      simpa only [canonicalize, List.length_map, List.length_range] using h.1
    refine isWitness_paddedRelation_iff.2 ⟨by simp [hlen], ?_⟩
    rw [id, List.take_append_of_le_length hlen.ge, List.take_of_length_le hlen.le]
    simp [SharpSAT.verifier, verifier_canonicalize, h.2, canonical_canonicalize]
  isWitness_backwardWitness φ w h := by
    obtain ⟨hlen, hV⟩ := isWitness_paddedRelation_iff.1 h
    refine isWitness_npRelation_iff.2 ⟨by simp [hlen], ?_⟩
    simp only [SharpSAT.verifier, Bool.and_eq_true] at hV
    exact hV.1

/-- **The padded relation is PC-complete**: every NP relation, over any encoded instance type,
Levin-reduces to it, by the Cook–Levin reduction followed by padding. -/
theorem paddedRelation_levinHard : LevinHard paddedRelation :=
  CookLevin.SAT_levinHard.trans toPaddedRelation

/-- **The padded relation has `2 · #SAT(φ)` solutions**: one for each satisfying assignment and
each value of the padding bit. -/
theorem searchCount_paddedRelation (φ : CNF ℕ) :
    searchCount paddedRelation.IsWitness φ = 2 * SharpSAT φ := by
  classical
  rw [paddedRelation.searchCount_eq, show paddedRelation.certLength = Polynomial.X + 1 from rfl,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, acceptCount_add,
    ← SharpSAT.acceptCount_verifier, acceptCount, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [acceptCount_congr (W := fun _ => SharpSAT.verifier (φ, List.ofFn u)) fun v => by
    simp [paddedRelation, List.take_left' (List.length_ofFn (f := u))]]
  cases SharpSAT.verifier (φ, List.ofFn u) <;> simp [acceptCount_true, acceptCount_false]

/-- The count of the padded relation is #P-complete under metric reductions: it is in #P, and
`#SAT` is recovered from it by halving. -/
theorem searchCount_paddedRelation_sharpPMetricComplete :
    SharpPMetricComplete encCNF (searchCount paddedRelation.IsWitness) := by
  refine ⟨searchCount_mem_SharpP paddedRelation.isWitness_mem_FNP,
    CookLevin.SharpSAT_sharpPComplete.sharpPMetricComplete.2.trans ?_⟩
  exact ⟨id, fun q : CNF ℕ × ℕ => q.2 / 2, id', binary_div' (snd _ _) (const 2),
    fun φ => by simp [searchCount_paddedRelation]⟩

/-- **[Goldreich, Exercise 6.36(a)][Goldreich2007Draft]** (February 2007 `r3.pdf`, printed
p. 263 / PDF p. 61), for the padded relation `R` of Exercise 6.35: `R` is in PC (`FNP`) and
PC-complete under Levin reductions, `#R` is #P-complete under metric (one-query Cook)
reductions, and the promise problem `(US_R, complement of S_R)` is in promise-P: its yes
instances have exactly one solution and its no instances have none. Its first, second and last
clauses are Exercise 6.35. -/
theorem exercise_6_36a :
    paddedRelation.IsWitness ∈ FNP encCNF ∧ LevinHard paddedRelation ∧
      SharpPMetricComplete encCNF (searchCount paddedRelation.IsWitness) ∧
      (⟨{φ | searchCount paddedRelation.IsWitness φ = 1},
        {φ | searchCount paddedRelation.IsWitness φ = 0},
        Set.disjoint_left.mpr (fun _ h₁ h₀ => by simp_all)⟩ :
          PromiseProblem (CNF ℕ)) ∈ PromiseP encCNF := by
  refine ⟨paddedRelation.isWitness_mem_FNP, paddedRelation_levinHard,
    searchCount_paddedRelation_sharpPMetricComplete,
    mem_PromiseP_iff.2 ⟨fun _ => false, const false, fun φ hφ => ?_, fun _ _ => rfl⟩⟩
  rw [Set.mem_ofPred_eq, searchCount_paddedRelation] at hφ
  omega

end Cslib.Complexity.SAT
