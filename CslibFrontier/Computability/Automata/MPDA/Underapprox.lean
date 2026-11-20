/-
Copyright (c) 2026 Sparsa Roychowdhury. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sparsa Roychowdhury
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Automata.MPDA.Holes
public import CslibFrontier.Foundations.Data.List.Splits
import CslibFrontier.Foundations.Data.List.Extract

/-! # Context-, round- and scope-bounded sequences of multistack pushdown automata

Reachability for multistack pushdown automata is undecidable, so verification focuses on
restricted classes of runs. Section 2 of [AkshayGastinKrishnaRoychowdhury2020] recalls the
classes that hole-bounded sequences generalize:

- `MPDA.ContextBounded`: at most `K` contexts, where a context uses at most one stack.
- `MPDA.RoundBounded`: at most `K` rounds, where a round is one possibly empty context for each
  stack `0, …, n - 1`, in this order.
- `MPDA.ScopeBounded`: at most `K` context switches between a push and its matching pop.

## Main definitions

- `MPDA.IsContext`, `MPDA.IsRound`: contexts and rounds.
- `MPDA.ContextBounded`, `MPDA.RoundBounded`, `MPDA.ScopeBounded`.

## Main results

- `MPDA.RoundBounded.contextBounded`: `K` rounds give at most `K * n` contexts.
- `MPDA.ContextBounded.scopeBounded`: a sequence with at most `K` contexts is `K`-scope-bounded.

## Implementation notes

Positions are `0`-indexed. The scope of a matched push and pop is measured by the number of
contexts of the factor from the push to the pop: `K` context switches means `K + 1` contexts.

## References

* [S. Akshay, P. Gastin, S. Krishna, S. Roychowdhury,
  *Revisiting Underapproximate Reachability for Multipushdown Systems*]
  [AkshayGastinKrishnaRoychowdhury2020]
-/

public section

namespace Cslib.Automata.MPDA

variable {n : ℕ} {Γ α β : Type*}

/-! ## Contexts and rounds -/

/-- The stack touched by an operation, if any. -/
@[expose] def Op.stack : Op n Γ → Option (Fin n)
  | .nop => none
  | .push i _ => some i
  | .pop i _ => some i

/-- Every operation of `w` touches stack `i` or no stack. -/
@[expose] def IsContextOf (i : Fin n) (w : List (α × Op n Γ)) : Prop :=
  ∀ μ ∈ w, μ.2.stack = none ∨ μ.2.stack = some i

/-- A context is a sequence of transitions that uses at most one stack. -/
@[expose] def IsContext (w : List (α × Op n Γ)) : Prop :=
  ∃ o : Option (Fin n), ∀ μ ∈ w, μ.2.stack = none ∨ μ.2.stack = o

/-- A round is a sequence of contexts for stacks `0, …, n - 1`, in this order. Each context may be
empty. -/
@[expose] def IsRound (w : List (α × Op n Γ)) : Prop :=
  ∃ vs : Fin n → List (α × Op n Γ), (List.ofFn vs).flatten = w ∧ ∀ i, IsContextOf i (vs i)

/-- At most `K` contexts. -/
@[expose] def ContextBounded (K : ℕ) (w : List (α × Op n Γ)) : Prop := List.Splits IsContext K w

/-- At most `K` rounds. -/
@[expose] def RoundBounded (K : ℕ) (w : List (α × Op n Γ)) : Prop := List.Splits IsRound K w

theorem IsContext.of_isInfix {u w : List (α × Op n Γ)} (hu : u <:+: w) (h : IsContext w) :
    IsContext u :=
  let ⟨o, ho⟩ := h
  ⟨o, fun μ hμ => ho μ (hu.subset hμ)⟩

private theorem IsRound.contextBounded {w : List (α × Op n Γ)} (h : IsRound w) :
    ContextBounded n w := by
  obtain ⟨vs, rfl, hvs⟩ := h
  refine ⟨List.ofFn vs, by simp, rfl, ?_⟩
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact ⟨some i, hvs i⟩

/-- `K` rounds give at most `K * n` contexts. -/
theorem RoundBounded.contextBounded {K : ℕ} {w : List (α × Op n Γ)} (h : RoundBounded K w) :
    ContextBounded (K * n) w :=
  (h.mono fun _ hv => hv.contextBounded).trans

private theorem ContextBounded.of_isInfix {K : ℕ} {u w : List (α × Op n Γ)}
    (h : ContextBounded K w) (hu : u <:+: w) : ContextBounded K u :=
  List.Splits.of_isInfix (fun _ _ huv hv => hv.of_isInfix huv) h hu

/-! ## Scope-bounded sequences -/

/-- A sequence is `K`-scope-bounded if every push and its matching pop are separated by at most `K`
context switches, that is, the factor from the push to the pop splits into at most `K + 1`
contexts. -/
@[expose] def ScopeBounded (K : ℕ) (w : List (α × Op n Γ)) : Prop :=
  ∀ p m, Matches w p m → ContextBounded (K + 1) (w.extract p (m + 1))

/-- A sequence with at most `K` contexts is `K`-scope-bounded. -/
theorem ContextBounded.scopeBounded {K : ℕ} {w : List (α × Op n Γ)} (h : ContextBounded K w) :
    ScopeBounded K w :=
  fun p m _ => (h.of_isInfix (w.extract_isInfix p (m + 1))).mono_bound (Nat.le_succ K)

end Cslib.Automata.MPDA
