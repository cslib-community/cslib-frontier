/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PCP
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic

/-!
# PCP(r, q) for promise problems

A PCP system for a promise problem `Q` asks for completeness only on the yes-instances and for
soundness only on the no-instances. Instances outside the promise are unconstrained. This is
Definition 9.14 of [Goldreich, *Computational Complexity: A Conceptual Perspective*, draft
r5][Goldreich2007DraftR5] (printed pp. 419–420), read in the promise-problem framework of its
Section 2.4.1. Exercise 9.25 uses it for `gapCSP`. Randomness, query bounds and the polynomial-time
requirement are those of `Cslib.Complexity.IsPCPVerifier` and `Cslib.Complexity.PCP`.

Unlike `Cslib.Complexity.PromiseP`, `PromisePCP` is defined directly, not through total
completions. A particular promise verifier need not verify any completion: for example, one that
accepts every proof on some instance outside the promise with probability 3/4. This is a fact
about that verifier only; whether the class has a characterization by completions is not
addressed here. The resource bounds apply on every instance, including those outside the promise.

## Main definitions

* `Cslib.Complexity.IsPromisePCPVerifier`: bounds, completeness on yes-instances and soundness on
  no-instances.
* `Cslib.Complexity.PromisePCP`: the promise class `PCP(r, q)`, with constant factors.

## Main results

* `Cslib.Complexity.isPromisePCPVerifier_ofSet_iff`, `Cslib.Complexity.ofSet_mem_PromisePCP`: on
  decision problems the notions are `Cslib.Complexity.IsPCPVerifier` and `Cslib.Complexity.PCP`.
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool}

/-- `V` is a verifier for the promise problem `Q` using at most `r n` random bits and at most `q n`
queries on instances whose encoding has length `n`. Every yes-instance has a proof that is
accepted for every random string. On every no-instance, every proof is accepted for at most half
of the random strings. Nothing is required on instances outside the promise. -/
structure IsPromisePCPVerifier (enc : α ↪ List Bool) (r q : ℕ → ℕ) (V : PCPVerifier α)
    (Q : PromiseProblem α) : Prop where
  /-- At most `r n` random bits on an instance whose encoding has length `n`. -/
  coins_le : ∀ a, V.coins a ≤ r (enc a).length
  /-- At most `q n` queries on an instance whose encoding has length `n`. -/
  length_queries_le :
    ∀ a (ρ : List Bool), ρ.length = V.coins a → (V.queries (a, ρ)).length ≤ q (enc a).length
  /-- Completeness: every yes-instance has a proof accepted for every random string. -/
  complete :
    ∀ a ∈ Q.yes, ∃ π : List Bool, ∀ ρ : List Bool, ρ.length = V.coins a → V.accepts a π ρ = true
  /-- Soundness: on a no-instance, every proof is accepted for at most half of the random
  strings. -/
  sound : ∀ a ∈ Q.no, ∀ π : List Bool,
    2 * acceptCount (fun x => V.accepts x.1 π x.2) a (V.coins a) ≤ 2 ^ V.coins a

/-- The class `PCP(r, q)` of promise problems with respect to the encoding `enc` of instances:
the promise problems with a polynomial-time verifier using `O(r n)` random bits and `O(q n)`
queries on instances whose encoding has length `n`. -/
def PromisePCP (r q : ℕ → ℕ) (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ (V : PCPVerifier α) (c d : ℕ), V.PolyTime enc ∧
    IsPromisePCPVerifier enc (fun n => c * r n) (fun n => d * q n) V Q}

/-- On a decision problem, a promise verifier is a PCP verifier. -/
theorem isPromisePCPVerifier_ofSet_iff {r q : ℕ → ℕ} {V : PCPVerifier α} {A : Set α} :
    IsPromisePCPVerifier enc r q V (.ofSet A) ↔ IsPCPVerifier enc r q V A :=
  ⟨fun h => ⟨h.coins_le, h.length_queries_le, h.complete, h.sound⟩,
    fun h => ⟨h.coins_le, h.length_queries_le, h.complete, h.sound⟩⟩

/-- A decision problem is in the promise class `PCP(r, q)` exactly when it is in `PCP(r, q)`. -/
@[simp]
theorem ofSet_mem_PromisePCP {r q : ℕ → ℕ} {A : Set α} :
    PromiseProblem.ofSet A ∈ PromisePCP r q enc ↔ A ∈ PCP r q enc := by
  simp only [PromisePCP, PCP, Set.mem_ofPred_eq, isPromisePCPVerifier_ofSet_iff]

end Cslib.Complexity
