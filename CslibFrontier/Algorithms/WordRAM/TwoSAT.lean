/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TwoSAT
public import CslibFrontier.Algorithms.WordRAM.ClauseCode
public import CslibFrontier.Algorithms.WordRAM.DFS
public import CslibFrontier.Algorithms.WordRAM.TwoSAT.Defs
public import CslibFrontier.Algorithms.WordRAM.TwoSAT.Programs
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Notation

/-!
# Linear-time 2-SAT on the word RAM

The [Aspvall–Plass–Tarjan][AspvallPlassTarjan1979] linear-time 2-SAT decision and
satisfying-assignment algorithm on the standard-basis word RAM (`Cslib.WordRAM.Basis.standard`),
running in `O(n + |φ|)` instructions on formulas `φ : CNF (Fin n)`.

## Representation

An instance (`Cslib.Algorithms.WordRAM.TwoSAT.Instance`) consists of a variable count `n : ℕ` and
a formula `φ : CNF (Fin n)`. Its input word list (`Instance.encode`) stores `n`, the clause count
`|φ|`, and each clause via `Cslib.Algorithms.WordRAM.ClauseCode.encodeClauseBy Fin.val` (its
length followed by literal codes `2 * v.val + b.toNat`).

Under `Cslib.WordRAM.ExecutesList`, the output word list (`answerWords G`) is:
* `[]` when `φ` violates the width-`2` bound or is unsatisfiable (`TwoSAT.solveFin G.n G.φ = none`);
* `1 :: [(σ 0).toNat, …, (σ (n - 1)).toNat]` when `TwoSAT.solveFin G.n G.φ = some σ`.
Prefixing `1` distinguishes a satisfying empty assignment on `n = 0` (`[1]`) from rejection (`[]`),
so `decodeAnswer G (answerWords G) = TwoSAT.solveFin G.n G.φ` holds unconditionally for all `n` and
`φ`.

The implication graph is built in compressed sparse row form in the scratch layout of
`CslibFrontier.Algorithms.WordRAM.DFS`, whose `sccIndexCode` computes the topological component
index of every literal (forward iterative DFS, CSR transposition, and Kosaraju peeling).

## Main definitions

* `Cslib.Algorithms.WordRAM.TwoSAT.Instance`: 2-SAT problem instance `(n, φ)`.
* `Cslib.Algorithms.WordRAM.TwoSAT.Instance.totalLits`,
  `Cslib.Algorithms.WordRAM.TwoSAT.Instance.encode`,
  `Cslib.Algorithms.WordRAM.TwoSAT.Instance.outAddrBase`,
  `Cslib.Algorithms.WordRAM.TwoSAT.Instance.wordBound`: literal-occurrence count, input word list,
  output-list base address, and linear word-width bound.
* `Cslib.Algorithms.WordRAM.TwoSAT.encodeAssignment`,
  `Cslib.Algorithms.WordRAM.TwoSAT.answerWords`,
  `Cslib.Algorithms.WordRAM.TwoSAT.decodeAnswer`: output word list and lossless decoder to
  `Option (Fin G.n → Bool)`.
* `Cslib.Algorithms.WordRAM.TwoSAT.Reg.outBase`: output-list header register.
* `Cslib.Algorithms.WordRAM.TwoSAT.solver`,
  `Cslib.Algorithms.WordRAM.TwoSAT.program`: structured and flat word-RAM programs.

## Main results

* `Cslib.Algorithms.WordRAM.TwoSAT.Instance.encode_length`,
  `Cslib.Algorithms.WordRAM.TwoSAT.Instance.inputFits_encode`: encoded word count and input-fit
  certificate from `Fits w G.wordBound`.
* `Cslib.Algorithms.WordRAM.TwoSAT.decodeAnswer_answerWords`: lossless output decoding.
* `Cslib.Algorithms.WordRAM.TwoSAT.answerWords_eq_nil_iff`,
  `Cslib.Algorithms.WordRAM.TwoSAT.eval_of_decodeAnswer_eq_some`: decision characterization and
  witness soundness.
* `Cslib.Algorithms.WordRAM.TwoSAT.solver_spec`,
  `Cslib.Algorithms.WordRAM.TwoSAT.program_spec`,
  `Cslib.Algorithms.WordRAM.TwoSAT.computesListInTime_program`: execution within
  `512 * (G.n + G.φ.length + 1)` instructions at every word width `w` with `Fits w G.wordBound`.
* `Cslib.Algorithms.WordRAM.TwoSAT.not_readsWidth_program`,
  `Cslib.Algorithms.WordRAM.TwoSAT.isRandFree_program`: width-independence and determinism
  certificates for `program`.

## References

* [B. Aspvall, M. F. Plass, R. E. Tarjan, *A linear-time algorithm for testing the truth of
  certain quantified boolean formulas*][AspvallPlassTarjan1979]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/
