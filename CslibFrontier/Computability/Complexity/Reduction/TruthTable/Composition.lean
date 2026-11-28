/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.TruthTable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# Composing polynomial-time truth-table reductions

Polynomial-time efficiency certificates for the resource-free truth-table composition operators
`Cslib.Complexity.truthTableCompQuery` and `Cslib.Complexity.truthTableCompCombiner` from
`CslibFrontier.Computability.Reduction.TruthTable`, together with transitivity of
`Cslib.Complexity.PolyTimeTruthTableReducible`.

Given `(r, q, d)` from `L` to `B` and `(r', q', d')` from `B` to `C`, summing `r' (q (a, i))` over
`i < r a` gives a polynomial-time unary block stride `M a` bounding every inner query count, and
unary division and remainder evaluate `truthTableCompQuery q q' M` directly without materializing
a flattened query list.

## Main results

* `Cslib.Complexity.computableInPolyTime_truthTableCompQuery`,
  `Cslib.Complexity.computableInPolyTime_truthTableCompCombiner`,
  `Cslib.Complexity.exists_polyTime_truthTableComp_bound`: polynomial-time certificates for the
  block-indexed composite query map, composite combiner, and uniform inner-count bound.
* `Cslib.Complexity.PolyTimeTruthTableReducible.trans`: polynomial-time truth-table reductions
  compose.

## References

* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {L : Set α} {B : Set β} {C : Set γ}

/-- Quotient/remainder block-indexed composite queries are computable in polynomial time when the
outer and inner query generators and the unary block stride `M` are. -/
theorem computableInPolyTime_truthTableCompQuery {q : α × ℕ → β} {q' : β × ℕ → γ} {M : α → ℕ}
    (hq : ComputableInPolyTime q (encPair encA encUnary) encB)
    (hq' : ComputableInPolyTime q' (encPair encB encUnary) encC)
    (hM : ComputableInPolyTime M encA encUnary) :
    ComputableInPolyTime (truthTableCompQuery q q' M) (encPair encA encUnary) encC := by
  unfold truthTableCompQuery
  fun_prop

/-- The composite combiner is computable in polynomial time when the component counts, outer query
generator, component combiners, and unary block stride `M` are. -/
theorem computableInPolyTime_truthTableCompCombiner {r : α → ℕ} {q : α × ℕ → β}
    {d : α × List Bool → Bool} {r' : β → ℕ} {d' : β × List Bool → Bool} {M : α → ℕ}
    (hr : ComputableInPolyTime r encA encUnary)
    (hq : ComputableInPolyTime q (encPair encA encUnary) encB)
    (hd : ComputableInPolyTime d (encPair encA encBits) encBool)
    (hr' : ComputableInPolyTime r' encB encUnary)
    (hd' : ComputableInPolyTime d' (encPair encB encBits) encBool)
    (hM : ComputableInPolyTime M encA encUnary) :
    ComputableInPolyTime (truthTableCompCombiner r q d r' d' M) (encPair encA encBits)
      encBool := by
  unfold truthTableCompCombiner
  fun_prop

/-- Summing the inner query counts across `i < r a` supplies a polynomial-time unary block stride
`M` bounding every active second-stage query count. -/
theorem exists_polyTime_truthTableComp_bound {r : α → ℕ} {q : α × ℕ → β} {r' : β → ℕ}
    (hr : ComputableInPolyTime r encA encUnary)
    (hq : ComputableInPolyTime q (encPair encA encUnary) encB)
    (hr' : ComputableInPolyTime r' encB encUnary) :
    ∃ M : α → ℕ, (∀ a, ∀ i < r a, r' (q (a, i)) ≤ M a) ∧
      ComputableInPolyTime M encA encUnary :=
  ⟨fun a => ((List.range (r a)).flatMap fun i => List.range (r' (q (a, i)))).length,
    fun a i hi => by
      simp only [List.length_flatMap, List.length_range]
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩),
    by fun_prop⟩

/-- **Polynomial-time truth-table reductions compose.** -/
@[trans]
theorem PolyTimeTruthTableReducible.trans (hLB : PolyTimeTruthTableReducible encA encB L B)
    (hBC : PolyTimeTruthTableReducible encB encC B C) :
    PolyTimeTruthTableReducible encA encC L C :=
  TruthTableReducibleBy.trans (fun _ _ _ _ _ _ ⟨hr, hq, hd⟩ ⟨hr', hq', hd'⟩ =>
    let ⟨M, hcM, hM⟩ := exists_polyTime_truthTableComp_bound hr hq hr'
    ⟨M, hcM, by fun_prop, computableInPolyTime_truthTableCompQuery hq hq' hM,
      computableInPolyTime_truthTableCompCombiner hr hq hd hr' hd' hM⟩) hLB hBC

end Cslib.Complexity
