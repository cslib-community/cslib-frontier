/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Problems.CountingSAT
public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT
import CslibFrontier.Computability.Complexity.Classes.Toda.Hierarchy
import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Membership

/-!
# A randomized formula reduction from the polynomial hierarchy to `⊕SAT`

Every problem in the polynomial hierarchy is decided with bounded error by a polynomial-time map
`A` from an instance and a random string to a formula in conjunctive normal form, followed by
membership in `⊕SAT` (`Cslib.Complexity.Toda.exists_boundedError_ParitySAT_of_mem_PH`). It
composes Toda's `PH ⊆ BP·⊕P` (`Cslib.Complexity.PH_subset_BPOp_ParityP`) with the
`⊕P`-completeness of `⊕SAT` under polynomial-time reductions
(`Cslib.Complexity.ParitySAT_parityPComplete`).

## Arora–Barak, draft Lemma 9.18

[Arora and Barak, draft Lemma 9.18, printed p. 181 / PDF p. 197][AroraBarak07] asks, for each
constant `c`, for a probabilistic polynomial-time algorithm `A` such that every quantified Boolean
formula `ψ` with `c` levels of alternation satisfies:
`ψ` true implies `Pr[A(ψ) ∈ ⊕SAT] ≥ 2 / 3`, and `ψ` false implies `Pr[A(ψ) ∈ ⊕SAT] = 0`.
`Cslib.Complexity.Toda.exists_boundedError_ParitySAT_alternation` is **not** that lemma: it is
the two-sided form, in which a false `ψ` gives `Pr[A(ψ) ∈ ⊕SAT] ≤ 1 / 3`.

The draft's proof does not give one-sided error. Each step should take a formula `ψ` with an
initial `⊕` quantifier to `ψ'` with "if `ψ` is false then so is `ψ'`". But `ψ = ⊕_z ∃x ∀w φ` is
true when the number of `z` with a nonempty set `S_z` is odd, while `ψ'` counts the `z` whose
trials isolate an element of `S_z`. If exactly two `z` have nonempty `S_z`, `ψ` is false; when
isolation fails for one of them, which happens with positive probability, `ψ'` is true. The
rewriting `∀ x P ⇔ ¬∃ x ¬P` with identity (4) also turns errors of one direction into the other.
This is a gap in the printed proof. No counterexample to the printed statement is known here, so
it is not recorded as a source error; the one-sided endpoint stays open.

## Statement-to-source mapping

* A quantified Boolean formula with `c` levels of alternation is a well-formed `PrenexQBF` with
  `c` blocks (`PrenexQBF.WellFormed c`; empty blocks allow fewer levels) and an initial polarity
  `q` (existential for `q = true`); its matrix is any quantifier-free formula. The algorithm may
  depend on `q`, which is visible in the syntax.
* `A(ψ)` with random coins is the polynomial-time map `A (a, r)` on random strings `r` of
  polynomial length `ρ`, and `⊕SAT` is `Cslib.Complexity.ParitySAT`, CNF formulas with an odd
  number of satisfying assignments. Probabilities are fractions of the random strings
  (`Cslib.Complexity.BoundedErrorAt`).

## Main results

* `Cslib.Complexity.Toda.exists_boundedError_ParitySAT_of_mem_PH`: `PH` reduces to `⊕SAT` by a
  bounded-error randomized formula map.
* `Cslib.Complexity.Toda.exists_boundedError_ParitySAT_alternation`: the two-sided form of
  Lemma 9.18.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft][AroraBarak07]
* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
-/

public section

namespace Cslib.Complexity.Toda

open Cslib.Logic.PL Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

open Classical in
/-- **The polynomial hierarchy reduces to `⊕SAT` with bounded error**: for every problem `L` in
`PH` there are a polynomial `ρ` and a polynomial-time map `A` from an instance and a random string
to a CNF formula such that membership of `A (a, r)` in `⊕SAT` decides `a ∈ L` with bounded error
over the random strings `r` of length `ρ (enc a).length`. -/
theorem exists_boundedError_ParitySAT_of_mem_PH {L : Set α} (hL : L ∈ PH enc) :
    ∃ (ρ : Polynomial ℕ) (A : α × List Bool → CNF ℕ),
      ComputableInPolyTime A (encPair enc encBits) encCNF ∧
        DecidesWithBoundedError enc ρ (fun x => decide (A x ∈ ParitySAT)) L := by
  obtain ⟨ρ, L', hL', hdec⟩ := PH_subset_BPOp_ParityP hL
  obtain ⟨A, hA, hiff⟩ := ParitySAT_parityPComplete.2 (encPair enc encBits) L' hL'
  have hV : (fun x => decide (A x ∈ ParitySAT)) = fun x => decide (x ∈ L') :=
    funext fun x => decide_eq_decide.2 (hiff x).symm
  exact ⟨ρ, A, hA, hV ▸ hdec⟩

open Classical in
/-- **Two-sided form of Arora–Barak, draft Lemma 9.18; not the cited lemma.** The draft asks for
no false positives (`Pr[A(ψ) ∈ ⊕SAT] = 0` on false `ψ`); here false formulas are mapped into
`⊕SAT` for at most a third of the random strings.

For `c` blocks and initial polarity `q` there are a polynomial `ρ` and a polynomial-time map `A`
to CNF formulas such that for every well-formed prenex formula `a` with `c` blocks, `A (a, r)`
lies in `⊕SAT` for at least two thirds of the random strings `r` of length
`ρ (encPrenexQBF a).length` when `a.formula q` is true, and for at most a third when it is
false. -/
theorem exists_boundedError_ParitySAT_alternation (c : ℕ) (q : Bool) :
    ∃ (ρ : Polynomial ℕ) (A : PrenexQBF × List Bool → CNF ℕ),
      ComputableInPolyTime A (encPair encPrenexQBF encBits) encCNF ∧
        ∀ a : PrenexQBF, a.WellFormed c →
          BoundedErrorAt encPrenexQBF ρ (fun x => decide (A x ∈ ParitySAT)) a
            (decide ((a.formula q).eval (fun _ => false) = true)) := by
  -- the true formulas of the given shape form a problem in the hierarchy
  have hL : {a : PrenexQBF | a.WellFormed c ∧ (a.formula q).eval (fun _ => false) = true} ∈
      PH encPrenexQBF :=
    q.rec (PiP_subset_PH c (PrenexQBF.mem_PiP c)) (SigmaP_subset_PH c (PrenexQBF.mem_SigmaP c))
  obtain ⟨ρ, A, hA, hdec⟩ := exists_boundedError_ParitySAT_of_mem_PH hL
  refine ⟨ρ, A, hA, fun a ha => ?_⟩
  by_cases ht : (a.formula q).eval (fun _ => false) = true
  · simpa [ht] using (hdec a).1 ⟨ha, ht⟩
  · simpa [ht] using (hdec a).2 fun h => ht h.2

end Cslib.Complexity.Toda
