/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Basic
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Instance
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.InputTrie
public import CslibFrontier.Algorithms.WordRAM.TrimmedYates.Program

/-!
# Selected entries of ranked subset convolution on the word RAM

Word-RAM implementation and running-time bound for [ChanItakuraMaYu2026], Theorem 2.2
(Section 2.1): given sparse integer-weighted set functions `f` and `g` on `Fin d` supported on
sets of sizes `t₁` and `t₂` (with `t₁ = t₂ = t` in Theorem 2.2) and query sets `Cs` of size
`t₁ + t₂`, compute `[subsetConvolution f g C | C ∈ Cs]` using trimmed fast zeta and Möbius passes
at threshold `s ≤ t₁ + t₂`.

Every operation left uncharged in a unit-cost cell model is implemented and charged as concrete
`Basis.standard` instructions across focused sub-modules:

* `CslibFrontier.Algorithms.WordRAM.TrimmedYates.Basic`: `d`-bit subset masks (`setMask`), depth-`d`
  binary trie view (`HoldsTrie`), caller register ABI (`numRegs`, `Reg.*`), and
  combinatorial domain/workspace/width envelopes (`lowCount`, `highCount`, `highPeak`,
  `valueEnvelope`, `solveSpace`).
* `CslibFrontier.Algorithms.WordRAM.TrimmedYates.Instance`: sparse `(set, weight)` entry lists
  (`evalEntries`, `entryAbsSum`, `encodeEntries`) and problem `Instance` encoding and width
  admissibility (`Instance.FitsWidth`).
* `CslibFrontier.Algorithms.WordRAM.TrimmedYates.Trie`,
  `CslibFrontier.Algorithms.WordRAM.TrimmedYates.InputTrie`, and
  `CslibFrontier.Algorithms.WordRAM.TrimmedYates.InputSetup`: deterministic `O(d + 1)` binary tries
  in flat word memory without assuming zeroed scratch space, sparse input-trie accumulation
  (`buildInputTrie`, `exec_buildInputTrie`), and `Data.init` decoding.
* `CslibFrontier.Algorithms.WordRAM.TrimmedYates.Enumeration`,
  `CslibFrontier.Algorithms.WordRAM.TrimmedYates.Tabulate`,
  `CslibFrontier.Algorithms.WordRAM.TrimmedYates.Stages`,
  `CslibFrontier.Algorithms.WordRAM.TrimmedYates.Triple`,
  `CslibFrontier.Algorithms.WordRAM.TrimmedYates.Preprocess`, and
  `CslibFrontier.Algorithms.WordRAM.TrimmedYates.Query`: coordinate-by-coordinate bounded subset
  enumeration, domain tabulation and pointwise product, trimmed zeta/Möbius stages, the 3-transform
  convolution kernel, low-cardinality preprocessing, and per-query dispatch.
* `CslibFrontier.Algorithms.WordRAM.TrimmedYates.Program`: pre-built trie solver (`solveFromTries`)
  and complete initialized flat `Program .standard 56` (`program`).

## Main definitions

* `Cslib.Algorithms.WordRAM.TrimmedYates.setMask`: `d`-bit unsigned mask of `S : Finset (Fin d)`.
* `Cslib.Algorithms.WordRAM.TrimmedYates.HoldsTrie`: read-only depth-`d` binary trie representation.
* `Cslib.Algorithms.WordRAM.TrimmedYates.lowCount`, `highCount`, `highPeak`, `solveSpace`,
  `valueEnvelope`: combinatorial table sizes and explicit word-width envelopes.
* `Cslib.Algorithms.WordRAM.TrimmedYates.Instance`, `evalEntries`: sparse weighted set-function
  problem instances over `Fin d` and their mathematical semantics.
* `Cslib.Algorithms.WordRAM.TrimmedYates.buildInputTrie`, `solveFromTries`, `program`: sparse
  input-trie builder, subroutine from pre-built input tries, and complete initialized flat
  `Program .standard 56`.

## Main results

* `Cslib.Algorithms.WordRAM.TrimmedYates.exec_buildInputTrie`, `exec_solveFromTries`,
  `exec_solveFromTries_subsetConvolution`: builds sparse input tries in `O(d · |es|)` instructions
  and, from pre-built input tries, answers all queries within
  `O((d + 1)² · (∑_{j ≤ s} C(d, j) + |Cs| · ∑_{s ≤ j ≤ 2t} C(2t, j)))` instructions.
* `Cslib.Algorithms.WordRAM.TrimmedYates.computesListInTime_program`, `executesList_program`:
  complete flat-program Theorem 2.2 bound
  `O((d + 1)² · (n + ∑_{j ≤ s} C(d, j) + |Cs| · ∑_{s ≤ j ≤ 2t} C(2t, j)))` from
  `State.init inst.encode`, charging sparse input insertion, domain enumeration, trie indexing,
  signed arithmetic, and the final `halt`.

## References

* [A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto, *Fourier meets Möbius: fast subset
  convolution*][BjorklundHusfeldtKaskiKoivisto2007]
* [A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto, *Trimmed Moebius inversion and graphs of
  bounded degree*][BjorklundHusfeldtKaskiKoivisto2010]
* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/
