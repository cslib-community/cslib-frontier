/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Relation
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Metric
import CslibFrontier.Computability.Complexity.Classes.SharpP.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# An easy search problem with a hard counting problem

Adjoining one distinguished solution to a counting verifier makes its search problem trivial,
while the count becomes `f + 1`. Subtracting one is a metric reduction back to `f`.
This proves [Goldreich2007Draft], Theorem 6.19 (printed p. 225, February 2007 draft), by the
artificial-problem route explicitly permitted immediately after its statement. It does not
claim that the distinguished solutions themselves are perfect matchings.

`SharpPMetricComplete.exists_mem_FPSearch` applies to any metric-complete count, in particular
Valiant's bipartite perfect-matching count. Completeness is explicitly **metric**, hence Cook,
not parsimonious: every input has the distinguished solution, even when the original count is
zero. The relation is in the existing `FPSearch` class, which also requires membership in `FNP`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

/-- Adjoining a unique all-false solution makes the search problem easy and increases the count
by exactly one. Other solutions are tagged `true`; their remaining bits are accepted by the
original #P verifier. Both the solver and membership test have native polynomial-time witnesses. -/
private theorem exists_mem_FPSearch_searchCount_add_one {f : α → ℕ} (hf : f ∈ SharpP enc) :
    ∃ R : α → List Bool → Prop, R ∈ FPSearch enc ∧ ∀ a, searchCount R a = f a + 1 := by
  obtain ⟨p, V, hV, hf⟩ := hf
  let S : NPRelation enc := ⟨p + 1, selectVerifier allFalseVerifier V,
    computableInPolyTime_selectVerifier computableInPolyTime_allFalseVerifier hV⟩
  refine ⟨S.IsWitness, ⟨S.isWitness_mem_FNP, ?_⟩, fun a => ?_⟩
  · refine ⟨fun a => some (List.replicate (p.eval (enc a).length + 1) false), ?_, ?_⟩
    · exact (optionSome encBits).comp ((bitsReplicate false).comp
        (unary_add' ((unary_eval p).comp (encoding_length enc)) (const 1)))
    · intro a
      constructor
      · intro w hw
        cases Option.some.inj hw
        constructor
        · simp [S]
        · simp [S, selectVerifier, allFalseVerifier, List.replicate_succ]
      · simp
  · rw [S.searchCount_eq]
    simp only [S, Polynomial.eval_add, Polynomial.eval_one, acceptCount_selectVerifier,
      acceptCount_allFalseVerifier, ← hf a]
    omega

/-- [Goldreich2007Draft], Theorem 6.19, by its artificial-problem route: any metric-complete #P
count gives a relation in `FPSearch` whose count is #P-complete **under metric reductions**.
A metric reduction is a one-query Cook reduction; parsimonious completeness is not asserted. -/
theorem SharpPMetricComplete.exists_mem_FPSearch {f : α → ℕ}
    (hf : SharpPMetricComplete enc f) :
    ∃ R : α → List Bool → Prop, R ∈ FPSearch enc ∧
      SharpPMetricComplete enc (searchCount R) := by
  obtain ⟨R, hR, hcount⟩ := exists_mem_FPSearch_searchCount_add_one hf.1
  refine ⟨R, hR, searchCount_mem_SharpP hR.1, hf.2.trans ?_⟩
  exact ⟨id, fun q : α × ℕ => q.2 - 1, id', binary_sub' (snd _ _) (const 1),
    fun a => by simp [hcount a]⟩

end Cslib.Complexity
