/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Crypto.Primitives.PRG.Defs
public import CslibFrontier.Probability.Product
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Primitives.PRG.Game
import CslibFrontier.Probability.Product.Resample

/-!
# Parallel composition of finite pseudorandom generators

Given a PRG `G : Generator Seed Output` and `n : ℕ`, the `n`-wise parallel composition
`G.parallel n` evaluates `G` independently on `n` seeds:
`G'(s_1, ..., s_n) := (G(s_1), ..., G(s_n))` ([BonehShoup2023], §3.4.1).

In the finite-type PRG game (`Attack Game 3.1`), adversaries are unrestricted `PMF` kernels, so
no efficiency claim is made here. For every `[NeZero n]` and every adversary `A` attacking
`G.parallel n`, `G.parallelReduction n A` samples a uniform hybrid index `ω : Fin n` and achieves
the exact relation `PRGadv[A, G'] = n · PRGadv[B, G]` of [BonehShoup2023], Theorem 3.2 (p. 55):
`(G.parallel n).advantage A = n * G.advantage (G.parallelReduction n A)`.

For the uniform strict-PPT asymptotic statement on bit-list ensembles (which delegates to the
library's certified `sequenceTest` reduction and incurs loss `dyadicSize (count n)`), see
`CslibFrontier.Crypto.Computational.PseudorandomGenerator.Parallel`.

## Main definitions

* `Cslib.Crypto.PRG.Generator.parallel`: `n`-wise parallel composition of a finite generator.
* `Cslib.Crypto.PRG.Generator.parallelReduction`: single-coordinate hybrid reduction adversary
  `B` against `G`.

## Main results

* `Cslib.Crypto.PRG.Generator.outputDist_parallel`: the output law of `G.parallel n` is the
  `n`-fold independent product of `G.outputDist`.
* `Cslib.Crypto.PRG.Generator.advantage_parallel_eq`: for `[NeZero n]`,
  `(G.parallel n).advantage A = n * G.advantage (G.parallelReduction n A)`.

## References

* [BonehShoup2023] Dan Boneh and Victor Shoup, *A Graduate Course in Applied Cryptography*,
  v0.6, §3.4.1, Theorem 3.2 (pp. 54–59).
-/

public section

namespace Cslib.Crypto.PRG.Generator

open Cslib.Crypto
open Cslib.Probability
open scoped NNReal

section GeneratorParallel

variable {Seed Output : Type*}

/-- Apply `G` independently to each coordinate of an `n`-tuple of seeds:
`G'(s_1, ..., s_n) := (G(s_1), ..., G(s_n))` ([BonehShoup2023], §3.4.1). -/
@[expose] def parallel (G : Generator Seed Output) (n : ℕ) :
    Generator (Fin n → Seed) (Fin n → Output) :=
  ⟨fun s i => G (s i)⟩

variable [Fintype Seed] [Nonempty Seed]

/-- The output distribution of `G.parallel n` is the `n`-fold independent product of
`G.outputDist`. -/
theorem outputDist_parallel [Finite Output] (G : Generator Seed Output) (n : ℕ) :
    (G.parallel n).outputDist = PMF.pi (fun _ : Fin n => G.outputDist) := by
  classical
  rw [Generator.outputDist, parallel, Generator.coe_mk, ← PMF.pi_uniformOfFintype, ← PMF.pi_map]
  rfl

variable [Fintype Output] [Nonempty Output]

/-- Hybrid distribution for `G.parallel n` at step `j`: the first `j` coordinates are uniform
in `Output`, and the remaining coordinates are independent draws from `G.outputDist`. -/
private noncomputable def parallelHybrid (G : Generator Seed Output) (n j : ℕ) :
    PMF (Fin n → Output) :=
  PMF.pi (fun i : Fin n => if i.val < j then PMF.uniformOfFintype Output else G.outputDist)

@[simp]
private theorem parallelHybrid_zero (G : Generator Seed Output) (n : ℕ) :
    parallelHybrid G n 0 = (G.parallel n).outputDist := by
  simp [parallelHybrid, outputDist_parallel]

@[simp]
private theorem parallelHybrid_self (G : Generator Seed Output) (n : ℕ) :
    parallelHybrid G n n = PMF.uniformOfFintype (Fin n → Output) := by
  classical
  have h : (fun i : Fin n => if i.val < n then PMF.uniformOfFintype Output else G.outputDist) =
      fun _ => PMF.uniformOfFintype Output := by
    funext i
    simp [i.isLt]
  rw [parallelHybrid, h, PMF.pi_uniformOfFintype]

/-- Hybrid reduction adversary `B` against `G` ([BonehShoup2023], Theorem 3.2, pp. 57–58):
samples `ω : Fin n` uniformly, fills coordinates `< ω` uniformly from `Output`, inserts its
challenge `r` at coordinate `ω`, draws coordinates `> ω` from `G.outputDist`, and runs `A`. -/
noncomputable def parallelReduction (G : Generator Seed Output) (n : ℕ) [NeZero n]
    (A : Adversary (Fin n → Output)) : Adversary Output :=
  fun r =>
    (PMF.uniformOfFintype (Fin n)).bind fun ω =>
      (PMF.pi (fun i : Fin n =>
        if i.val < ω.val then PMF.uniformOfFintype Output
        else G.outputDist)).bind fun rest =>
          A (Function.update rest ω r)

private theorem parallelHybrid_bind_of_lt (G : Generator Seed Output) (n : ℕ)
    (A : Adversary (Fin n → Output)) (ω : Fin n) :
    G.outputDist.bind (fun r =>
      (PMF.pi (fun i : Fin n =>
        if i.val < ω.val then PMF.uniformOfFintype Output else G.outputDist)).bind fun rest =>
          A (Function.update rest ω r)) =
      (parallelHybrid G n ω.val).bind A := by
  classical
  rw [PMF.bind_pi_function_update (α := fun _ => Output)]
  simp only [parallelHybrid]
  congr 1
  congr 1 with i
  by_cases hi : i = ω
  · subst hi
    simp
  · simp [Function.update_of_ne hi]

private theorem parallelHybrid_succ_bind (G : Generator Seed Output) (n : ℕ)
    (A : Adversary (Fin n → Output)) (ω : Fin n) :
    (PMF.uniformOfFintype Output).bind (fun r =>
      (PMF.pi (fun i : Fin n =>
        if i.val < ω.val then PMF.uniformOfFintype Output else G.outputDist)).bind fun rest =>
          A (Function.update rest ω r)) =
      (parallelHybrid G n (ω.val + 1)).bind A := by
  classical
  rw [PMF.bind_pi_function_update (α := fun _ => Output)]
  simp only [parallelHybrid]
  congr 1
  congr 1 with i
  by_cases hi : i = ω
  · subst hi
    simp
  · have hlt : i.val < ω.val + 1 ↔ i.val < ω.val := by
      have hne : i.val ≠ ω.val := fun h => hi (Fin.ext h)
      omega
    simp [Function.update_of_ne hi, hlt]

/-- **Boneh–Shoup Theorem 3.2 (finite typed relation, p. 55):** For `[NeZero n]` and every
unrestricted `PMF`-kernel adversary `A` against `G.parallel n`, `G.parallelReduction n A`
satisfies `PRGadv[A, G'] = n · PRGadv[B, G]`. -/
theorem advantage_parallel_eq (G : Generator Seed Output) (n : ℕ) [NeZero n]
    (A : Adversary (Fin n → Output)) :
    (G.parallel n).advantage A = n * G.advantage (G.parallelReduction n A) := by
  let games : ℕ → Game := fun j => (parallelHybrid G n j).bind A
  have havg := Game.advantage_hybrid_average games n n le_rfl
  have h0 : games 0 = (G.parallel n).realExperiment A := by
    simp [games, Generator.realExperiment]
  have hn_eq : games n = Generator.idealExperiment A := by
    simp [games, Generator.idealExperiment]
  have hreal_red : G.realExperiment (G.parallelReduction n A) =
      (PMF.uniformOfFintype (Fin n)).bind fun ω =>
        if ω.val < n then games ω.val else PMF.pure false := by
    unfold parallelReduction
    rw [Generator.realExperiment, PMF.bind_comm]
    congr 1 with ω : 1
    simp only [ω.isLt, ↓reduceIte, games]
    exact parallelHybrid_bind_of_lt G n A ω
  have hideal_red : Generator.idealExperiment (G.parallelReduction n A) =
      (PMF.uniformOfFintype (Fin n)).bind fun ω =>
        if ω.val < n then games (ω.val + 1) else PMF.pure false := by
    unfold parallelReduction
    rw [Generator.idealExperiment, PMF.bind_comm]
    congr 1 with ω : 1
    simp only [ω.isLt, ↓reduceIte, games]
    exact parallelHybrid_succ_bind G n A ω
  rw [h0, hn_eq, ← hreal_red, ← hideal_red] at havg
  rw [Generator.advantage_eq_game, Generator.advantage_eq_game]
  have hcoe := congrArg ((↑) : ℝ≥0 → ℝ) havg
  simpa [NNReal.coe_mul, NNReal.coe_natCast] using hcoe

end GeneratorParallel

end Cslib.Crypto.PRG.Generator
