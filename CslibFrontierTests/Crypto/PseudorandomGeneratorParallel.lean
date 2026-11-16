/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.PseudorandomGenerator.Parallel
public import CslibFrontier.Crypto.Primitives.PRG.Parallel
import CslibFrontier.Foundations.Data.BitString.List.Rows
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for parallel PRG composition

Exercises the finite-type and word-level parallel PRG API in
`CslibFrontier.Crypto.Primitives.PRG.Parallel`,
`CslibFrontier.Crypto.Computational.PseudorandomGenerator.Parallel`, and the helper lemma
`Cslib.BitString.flatten_listRows_of_length`:
* concrete `decide` evaluations of `parallelGenerator`, including `count = 0` and short-seed zero
  padding;
* concrete evaluation of `BitString.flatten_listRows_of_length` and `length_parallelGenerator`;
* `computableInPolyTime_parallelGenerator` on concrete unary schedules and an arbitrary
  polynomial-time generator;
* `computationallyIndistinguishable_parallelGenerator` applied to an arbitrary
  `PseudorandomGenerator` with `count n = n`;
* concrete `decide` evaluation of `PRG.Generator.parallel`, exact application of
  `PRG.Generator.advantage_parallel_eq`, and the `Secure.prod`-shaped finite corollary as a checked
  example.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.PseudorandomGeneratorParallel

open Cslib Cslib.Crypto Turing.MultiTapeTM
open scoped NNReal

-- Concrete `decide` evaluations of `parallelGenerator`: `count = 2`, `count = 0`, and short seed.
example :
    parallelGenerator (fun s => s ++ [true]) 2 2 [true, false, false, true] =
      [true, false, true, false, true, true] := by
  decide

example : parallelGenerator (fun s => s ++ [true]) 0 2 [true, false] = [] := by decide

example :
    parallelGenerator (fun s => s ++ [true]) 2 2 [true] =
      [true, false, true, false, false, true] := by
  decide

-- Flattening `listRows` of matching total length recovers the input word.
example :
    (BitString.listRows 2 3 [true, false, true, false, true, false]).flatten =
      [true, false, true, false, true, false] :=
  BitString.flatten_listRows_of_length rfl

-- Output length when `generator` maps `width`-bit strings to `width + 1`-bit strings.
example (count width : ℕ) (seed : List Bool) :
    (parallelGenerator (fun s => s ++ [true]) count width seed).length = count * (width + 1) :=
  length_parallelGenerator (length := fun w => w + 1) (fun {s} => by simp) count width seed

-- Polynomial-time certificate on a concrete `count = id` schedule.
example {generator : List Bool → List Bool}
    (hgen : ComputableInPolyTime generator encBits encBits) :
    ComputableInPolyTime (fun n => parallelGenerator generator n n []) encUnary encBits :=
  computableInPolyTime_parallelGenerator hgen .id' .id' (.const [])

-- Boneh–Shoup Theorem 3.2 applied to an arbitrary `PseudorandomGenerator` with `count n = n`.
example {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length) :
    ComputationallyIndistinguishable
      (fun n => (BitString.uniformList (n * n)).map (parallelGenerator generator n n))
      (fun n => BitString.uniformList (n * length n)) :=
  computationallyIndistinguishable_parallelGenerator hG ComputableInPolyTime.id'

-- Concrete evaluation of `PRG.Generator.parallel` (unfolds `Generator.parallel`).
private def dupGenerator : PRG.Generator Bool (Bool × Bool) := ⟨fun b => (b, b)⟩

example : (dupGenerator.parallel 2) ![true, false] = ![(true, true), (false, false)] := by
  decide

-- Exact finite advantage identity (`advantage_parallel_eq`) for `dupGenerator.parallel 2`.
example (A : PRG.Adversary (Fin 2 → Bool × Bool)) :
    (dupGenerator.parallel 2).advantage A =
      2 * dupGenerator.advantage (dupGenerator.parallelReduction 2 A) :=
  dupGenerator.advantage_parallel_eq 2 A

-- One `Secure.prod`-shaped finite corollary as a checked example (no closure theorem in library).
example {Seed Output : Type*} [Fintype Seed] [Nonempty Seed] [Fintype Output] [Nonempty Output]
    {G : PRG.Generator Seed Output} (n : ℕ) [NeZero n]
    {Admissible₁ : PRG.Adversary Output → Prop}
    {Admissible₂ : PRG.Adversary (Fin n → Output) → Prop} {ε : ℝ≥0}
    (hG : G.Secure Admissible₁ ε)
    (hred : ∀ A, Admissible₂ A → Admissible₁ (G.parallelReduction n A)) :
    (G.parallel n).Secure Admissible₂ (n * ε) := by
  intro A hA
  rw [G.advantage_parallel_eq n A]
  have hle := hG (G.parallelReduction n A) (hred A hA)
  push_cast
  gcongr

end CslibFrontierTests.Crypto.PseudorandomGeneratorParallel
