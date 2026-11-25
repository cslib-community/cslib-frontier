/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
public import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Crypto.Computational.Hybrid.Sequence
import CslibFrontier.Foundations.Data.BitString.List.Rows
import CslibFrontier.Languages.Probabilistic.Repeat
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Tactic.PPT

/-!
# Parallel composition of uniform strict-PPT pseudorandom generators

Given a bitstring generator `generator : List Bool → List Bool`, a repetition count `count`, and a
block width `width`, `parallelGenerator generator count width seed` splits `seed` into `count`
blocks of length `width`, evaluates `generator` on each block, and concatenates the outputs
([BonehShoup2023], §3.4.1).

Differences from [BonehShoup2023], Theorem 3.2 (pp. 54–59):
* Security (`computationallyIndistinguishable_parallelGenerator`) is stated on the output ensemble
  over `count n` independent `n`-bit seeds `(BitString.uniformList (count n * n)).map
  (parallelGenerator generator (count n) n)` rather than bundled as a `PseudorandomGenerator`:
  `PseudorandomGenerator` indexes security by the total seed length, and a flat seed of length
  `count n * n` does not uniquely determine `n`.
* All `count n` seeds share the security parameter length `n`.
* The repetition parameter `count` is required to be computable in deterministic polynomial time
  in unary (`ComputableInPolyTime count encUnary encUnary`), matching the book's poly-bounded
  requirement and inherited from `ComputationallyIndistinguishable.replicate_bind`.
* Rather than instantiating a fresh `B` that draws `ω` uniformly from `{1, ..., count n}`,
  `computationallyIndistinguishable_parallelGenerator` delegates directly to
  `ComputationallyIndistinguishable.replicate_bind`, whose certified `sequenceTest` reduction
  samples from a padded dyadic range and incurs loss `dyadicSize (count n)` (with
  `count n + 1 ≤ dyadicSize (count n) ≤ 2 * (count n + 1)` by `lt_dyadicSize` and `dyadicSize_le`;
  `Sequence.sequenceTest_advantage`).
* The expansion hypothesis `hG.stretch` (`∀ n, n < length n`) of `PseudorandomGenerator` is not
  needed by the computational indistinguishability proof.

## Main definitions

* `Cslib.Crypto.parallelGenerator`: `count`-wise parallel composition on bit-list seeds of width
  `width`.

## Main results

* `Cslib.Crypto.computableInPolyTime_parallelGenerator`: deterministic polynomial-time
  efficiency certificate for `parallelGenerator`.
* `Cslib.Crypto.length_parallelGenerator`: output length `count * length width` when `generator`
  maps every word to length `length word.length`.
* `Cslib.Crypto.computationallyIndistinguishable_parallelGenerator`: [BonehShoup2023],
  Theorem 3.2 for uniform strict-PPT generators.

## References

* [BonehShoup2023] Dan Boneh and Victor Shoup, *A Graduate Course in Applied Cryptography*,
  v0.6, §3.4.1, Theorem 3.2 (pp. 54–59).
-/

public section

namespace Cslib.Crypto

open Cslib.Probability
open Turing.MultiTapeTM

/-- `count`-wise parallel composition of a bitstring generator `generator` on blocks of width
`width`: split `seed` into `count` rows of length `width`, apply `generator` to each row, and
concatenate the outputs ([BonehShoup2023], §3.4.1). -/
@[expose] def parallelGenerator (generator : List Bool → List Bool) (count width : ℕ)
    (seed : List Bool) : List Bool :=
  ((BitString.listRows count width seed).map generator).flatten

/-- Polynomial-time efficiency certificate for `parallelGenerator`: if `generator` is deterministic
polynomial-time on bitstrings and `count`, `width`, `seed` are polynomial-time in `input`, then
`parallelGenerator generator (count a) (width a) (seed a)` is deterministic polynomial-time. -/
theorem computableInPolyTime_parallelGenerator {Param : Type} {input : Param ↪ List Bool}
    {generator : List Bool → List Bool} {count width : Param → ℕ} {seed : Param → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    (hcount : ComputableInPolyTime count input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hseed : ComputableInPolyTime seed input encBits) :
    ComputableInPolyTime
      (fun a => parallelGenerator generator (count a) (width a) (seed a)) input encBits := by
  fun_prop [parallelGenerator]

/-- Exact output length of `parallelGenerator` when each row output has length `length width`. -/
theorem length_parallelGenerator {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hlen : ∀ {seed : List Bool}, (generator seed).length = length seed.length)
    (count width : ℕ) (seed : List Bool) :
    (parallelGenerator generator count width seed).length = count * length width := by
  unfold parallelGenerator
  rw [List.length_flatten, List.map_map, Function.comp_def]
  have hmap : List.map (fun x => (generator x).length) (BitString.listRows count width seed) =
      List.replicate count (length width) := by
    apply List.ext_getElem (by simp)
    intro i hi _
    have hi' : i < count := by simpa using hi
    simp only [List.getElem_map, List.getElem_replicate, BitString.listRows,
      List.getElem_range, BitString.length_listRow, hlen]
  rw [hmap, List.sum_replicate, smul_eq_mul]

private theorem eval_replicate_sampleList_bind_flatten (f : List Bool → List Bool)
    (count width : ℕ) :
    ProbComp.eval (do
        let outs ← OracleComp.replicate count (BitString.sampleList width >>= fun s => pure (f s))
        pure outs.flatten) =
      (BitString.uniformList (count * width)).map (parallelGenerator f count width) := by
  rw [ProbComp.eval_bind, ProbComp.eval_replicate_of_uniformList count width _ f (by
    simp only [ProbComp.eval_bind, BitString.eval_sampleList, ProbComp.eval_pure,
      show (fun s => PMF.pure (f s)) = PMF.pure ∘ f from rfl, PMF.bind_pure_comp])]
  simp only [ProbComp.eval_pure,
    show (fun a : List (List Bool) => PMF.pure a.flatten) = PMF.pure ∘ List.flatten from rfl,
    PMF.bind_pure_comp, PMF.map_comp]
  rfl

private theorem eval_replicate_sampleList_uniform_flatten (count width : ℕ) :
    ProbComp.eval (do
        let outs ← OracleComp.replicate count (BitString.sampleList width)
        pure outs.flatten) =
      BitString.uniformList (count * width) := by
  rw [ProbComp.eval_bind, ProbComp.eval_replicate_of_uniformList count width _ id
    (by rw [BitString.eval_sampleList, PMF.map_id])]
  simp only [ProbComp.eval_pure,
    show (fun a : List (List Bool) => PMF.pure a.flatten) = PMF.pure ∘ List.flatten from rfl,
    PMF.bind_pure_comp, PMF.map_comp]
  conv_rhs => rw [← PMF.map_id (BitString.uniformList (count * width))]
  exact PMF.map_congr_on_support _ _ _ fun w hw => by
    simpa only [Function.comp_def, List.map_id, id_eq] using
      BitString.flatten_listRows_of_length (BitString.length_of_mem_support_uniformList hw)

/-- **Boneh–Shoup Theorem 3.2 (uniform strict-PPT word layer, pp. 54–59):** if `generator` is a
`PseudorandomGenerator` with output length `length` and `count` is a unary polynomial-time copy
count, then applying `generator` to `count n` independent uniform `n`-bit seeds and concatenating
the outputs is computationally indistinguishable from `BitString.uniformList (count n * length n)`.
Delegates the PPT hybrid reduction (`sequenceTest`, loss `dyadicSize (count n)`) and its
`isPPTOn_sequenceTest` certificate to `ComputationallyIndistinguishable.replicate_bind`. -/
theorem computationallyIndistinguishable_parallelGenerator
    {generator : List Bool → List Bool} {length count : ℕ → ℕ}
    (hG : PseudorandomGenerator generator length)
    (hcount : ComputableInPolyTime count encUnary encUnary) :
    ComputationallyIndistinguishable
      (fun n => (BitString.uniformList (count n * n)).map
        (parallelGenerator generator (count n) n))
      (fun n => BitString.uniformList (count n * length n)) := by
  let orig (n : ℕ) : ProbComp (List Bool) :=
    BitString.sampleList n >>= fun s => pure (generator s)
  let repl (n : ℕ) : ProbComp (List Bool) := BitString.sampleList (length n)
  have horig : IsPPTOn encUnary encBits orig := by
    dsimp only [orig]
    have _ : IsPPTOn encUnary encBits BitString.sampleList :=
      Cslib.Probability.isPPTOn_sampleList
    have _ := hG.polyTime
    ppt
  have hrepl : IsPPTOn encUnary encBits repl := by
    dsimp only [repl]
    have _ := hG.polyTime_length
    ppt
  have hprocess : IsPPTOn (encPair encUnary (encList encBits)) encBits
      (fun p => pure p.2.flatten) :=
    (ComputableInPolyTime.bitsFlatten (.snd encUnary (encList encBits))).isPPTOn
  have hind : ComputationallyIndistinguishable
      (fun n => ProbComp.eval (orig n)) (fun n => ProbComp.eval (repl n)) := by
    convert hG.indistinguishable using 2 with n
    · simp only [orig, generatorEnsemble, ProbComp.eval_bind, BitString.eval_sampleList,
        ProbComp.eval_pure, show (fun s => PMF.pure (generator s)) = PMF.pure ∘ generator from rfl,
        PMF.bind_pure_comp]
    · simp [repl, BitString.eval_sampleList]
  have hrep := ComputationallyIndistinguishable.replicate_bind
    (process := fun _ xs => pure xs.flatten) horig hrepl hind hcount hprocess
  dsimp only [orig, repl] at hrep
  simpa only [eval_replicate_sampleList_bind_flatten,
    eval_replicate_sampleList_uniform_flatten] using hrep

end Cslib.Crypto
