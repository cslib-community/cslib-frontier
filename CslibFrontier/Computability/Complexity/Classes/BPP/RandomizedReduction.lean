/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Probabilistic.PPT
import CslibFrontier.Computability.Probabilistic.CoinTape
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Probability.BitString

/-!
# Randomized polynomial-time many-one reductions with two-sided error

[Arora and Barak, Definition 7.19][AroraBarak07] (printed p. 129 / PDF p. 145): a language `A`
reduces to `B` under a randomized polynomial-time reduction, `A ≤_r B`, if there is a probabilistic
Turing machine `M` such that `Pr[B(M(x)) = A(x)] ≥ 2/3` for every `x`. Here (`BPReducible`) the
machine is a uniform strict probabilistic polynomial-time program `R : α → ProbComp β`
(`Cslib.Probability.IsPPTOn`) between explicit instance encodings, and the condition says that
`R a` lands in `B` exactly when `a ∈ A` with probability at least `2/3`. The one-sided variant used
in metacomplexity is `Cslib.Complexity.PromiseProblem.RPReducible`.

`bpReducible_iff` turns such a program into a deterministic polynomial-time map `f` of an instance
and a random string of polynomial length, such that the test `f (a, r) ∈ B` decides `A` with bounded
error (`DecidesWithBoundedError`). This is the form that the bounded-error operator `BPOp` uses.

## Main definitions

* `Cslib.Complexity.BPReducible`: `A ≤_r B` of Definition 7.19.

## Main results

* `Cslib.Complexity.bpReducible_iff`: the seeded characterization.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07],
  Definition 7.19.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Probability

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}

/-- **Randomized polynomial-time many-one reduction**
[Arora and Barak, Definition 7.19][AroraBarak07]: `A ≤_r B` when a uniform strict PPT program
`R : α → ProbComp β` maps every instance `a` to an instance whose membership in `B` agrees with
the membership of `a` in `A` with probability at least `2 / 3`. -/
@[expose] def BPReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α) (B : Set β) :
    Prop :=
  ∃ R : α → ProbComp β, IsPPTOn encA encB R ∧
    ∀ a, 2 / 3 ≤ ((ProbComp.eval (R a)).toOuterMeasure {b | b ∈ B ↔ a ∈ A}).toReal

open Classical in
private theorem decidesWithBoundedError_iff_card {p : Polynomial ℕ} {f : α × List Bool → β} :
    DecidesWithBoundedError encA p (fun x => decide (f x ∈ B)) A ↔
      ∀ a, 2 * 2 ^ p.eval (encA a).length ≤
        3 * (Finset.univ.filter fun r : Fin (p.eval (encA a).length) → Bool =>
          (f (a, List.ofFn r) ∈ B ↔ a ∈ A)).card := by
  refine forall_congr' fun a => ?_
  by_cases ha : a ∈ A <;> simp [ha, BoundedErrorAt]

open Classical in
/-- **Seeded characterization of `A ≤_r B`**: `A` reduces to `B` under a randomized polynomial-time
reduction exactly when some polynomial-time map `f` of an instance `a` and a random string of
length `p(|a|)` satisfies: the test `f (a, r) ∈ B` decides `A` with bounded error. -/
theorem bpReducible_iff :
    BPReducible encA encB A B ↔
      ∃ (p : Polynomial ℕ) (f : α × List Bool → β),
        ComputableInPolyTime f (encPair encA encBits) encB ∧
        DecidesWithBoundedError encA p (fun x => decide (f x ∈ B)) A := by
  simp only [decidesWithBoundedError_iff_card]
  constructor
  · rintro ⟨R, hR, hprob⟩
    obtain ⟨c, d, evalR, hevalR, -, hlaw⟩ := hR.exists_total_seeded_evaluator
    refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun x => evalR x.1 x.2, hevalR, fun a => ?_⟩
    have hp : (Polynomial.C c * (Polynomial.X + 1) ^ d).eval (encA a).length =
        c * ((encA a).length + 1) ^ d := by simp
    rw [hp, ← @Nat.cast_le ℝ]
    push_cast
    have h := hprob a
    rw [hlaw a _ le_rfl, BitString.toOuterMeasure_map_uniformList_toReal,
      le_div_iff₀ (by positivity)] at h
    simp only [Set.mem_ofPred_eq] at h
    linarith
  · rintro ⟨p, f, hf, hcard⟩
    refine ⟨fun a => (fun w => f (a, w)) <$> BitString.sampleList (p.eval (encA a).length),
      IsPPTOn.of_seeded
        ((ComputableInPolyTime.unary_eval p).comp (ComputableInPolyTime.encoding_length encA)) hf,
      fun a => ?_⟩
    simp only [ProbComp.eval_map, BitString.eval_sampleList,
      BitString.toOuterMeasure_map_uniformList_toReal, Set.mem_ofPred_eq]
    rw [le_div_iff₀ (by positivity)]
    have h3 := (Nat.cast_le (α := ℝ)).mpr (hcard a)
    push_cast at h3
    linarith

end Cslib.Complexity
