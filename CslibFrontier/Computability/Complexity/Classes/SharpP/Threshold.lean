/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.MetricOracle
public import CslibFrontier.Computability.Complexity.Classes.Oracle.BinarySearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Counting functions and their threshold languages

For any `f a ≤ 2 ^ p(|enc a|)`, computing `f` in binary and deciding `N ≤ f a` are
polynomial-time oracle equivalent [Goldreich2007Draft], Proposition 6.15 (printed p. 223,
February 2007 draft). The forward direction reads the bits of `f` using the existing metric
reduction interpreter; the reverse direction uses the shared binary-search program.

Both statements use native strict oracle computation, including query construction and reply
access. The counting oracle is the existing bit graph, rather than a unit-cost unbounded
integer reply. There are at most `p(|enc a|) + 1` relevant count bits, including when the
upper bound is attained. The threshold query uses `encPair enc encNat`: framed instance,
then a binary natural. No #P assumption is needed beyond the stated bound; every #P function
has such a bound by `SharpP.exists_le_two_pow`.

## Main results

* `threshold_polyTimeOracleProgram`: threshold decision from a counting oracle.
* `computableInPolyTimeWithOracle_threshold`: recover the count from its threshold language.
-/

public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {f : α → ℕ} {p : Polynomial ℕ}

/-- Threshold decision from the bits of `f`, uniformly over all oracles answering those bits.
This is the forward direction of [Goldreich2007Draft], Proposition 6.15. The postprocessing
compares binary naturals; the oracle interpreter reads at most `p(|enc a|) + 1` count bits. -/
theorem threshold_polyTimeOracleProgram
    (hp : ∀ a, f a ≤ 2 ^ p.eval (enc a).length) :
    PolyTimeOracleProgram (encPair enc encNat) encBool (AnswersBits enc f)
      (· = fun q : α × ℕ => decide (q.2 ≤ f q.1)) := by
  have hred : MetricReducible (encPair enc encNat) enc encBool encNat
      (fun q : α × ℕ => decide (q.2 ≤ f q.1)) f :=
    ⟨Prod.fst, fun q => decide (q.1.2 ≤ q.2), ComputableInPolyTime.fst _ _,
      ComputableInPolyTime.binary_le'
        ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
        (ComputableInPolyTime.snd _ _), fun _ => rfl⟩
  exact hred.polyTimeOracleProgram (p := p + 1) fun a =>
    (hp a).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by simp))

/-- Recover an exponentially bounded count in binary from its threshold language, with
`p(|enc a|) + 1` binary-search rounds. This is the reverse direction of [Goldreich2007Draft],
Proposition 6.15. The strict oracle certificate bounds computation for arbitrary replies,
not just correct threshold answers. -/
theorem computableInPolyTimeWithOracle_threshold
    (hp : ∀ a, f a ≤ 2 ^ p.eval (enc a).length) :
    ComputableInPolyTimeWithOracle
      ((encPair enc encNat) '' {q : α × ℕ | q.2 ≤ f q.1}) f enc encNat := by
  classical
  let A := (encPair enc encNat) '' {q : α × ℕ | q.2 ≤ f q.1}
  refine ⟨fun a => BinarySearch.search (enc a) (p.eval (enc a).length + 1),
    BinarySearch.isOraclePPTOn_search ComputableInPolyTime.id'.encoding_comp
      (ComputableInPolyTime.unary_add'
        ((ComputableInPolyTime.unary_eval p).comp (ComputableInPolyTime.encoding_length enc))
        (ComputableInPolyTime.const 1)), fun a => ?_⟩
  apply BinarySearch.interpret_id_search
  · intro k
    change encPair enc encNat (a, k) ∈ A ↔ k ≤ f a
    exact (encPair enc encNat).injective.mem_set_image
  · exact (hp a).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))

end Cslib.Complexity
