/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin
public import CslibFrontier.Computability.Complexity.Classes.BPP.Derandomization
import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic
import CslibFrontier.Foundations.Data.BitString.WordCount

/-!
# Derandomizing Merlin–Arthur

Average-case hardness in `E` collapses `MA` to `NP` (Arora and Barak's Exercise 16.4). The
argument derandomizes Arthur's check of a fixed proof
(`MA_subset_NP_of_PromiseBPP_subset_PromiseP`). Pairs of an instance `a` and a candidate proof `w`
form a promise problem: yes when Arthur accepts `(a, w)` on at least two thirds of his random
strings, no when he accepts on at most one third. It is in `PromiseBPP` on pairs, by running
Arthur on `a`, `w` and a prefix of the random string. Promise derandomization
(`PromiseBPP_subset_PromiseP_of_isAverageCaseHard`) gives a deterministic polynomial-time test of
pairs that accepts the yes-pairs and rejects the no-pairs, and that test is an `NP` verifier for
the problem: Merlin's good proof is a yes-pair, and when `a` is not in the problem, every proof is
a no-pair.

## Main results

* `Cslib.Complexity.MA_subset_NP_of_PromiseBPP_subset_PromiseP`: promise derandomization on pairs
  gives `MA ⊆ NP`.
* `Cslib.Complexity.MA_eq_NP_of_isAverageCaseHard`: Arora and Barak, Exercise 16.4.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft
  2007-01-08][AroraBarak07], Definition 16.7, Theorem 16.10 and Exercise 16.4
* [N. Nisan, A. Wigderson, *Hardness vs randomness*][NisanWigderson1994]
-/

public section

namespace Cslib.Complexity

open Cslib.Circuits.Boolean Turing.MultiTapeTM Finset Filter PromiseProblem

variable {α : Type} {enc : α ↪ List Bool}

/-- **Promise derandomization collapses `MA` to `NP`.** If every promise problem on pairs of an
instance and a word that is solved with bounded error in polynomial time is also solved
deterministically in polynomial time, then `MA enc ⊆ NP enc`. The pairs are an instance and a
candidate proof. The yes-pairs are those that Arthur accepts with probability at least two thirds,
and the no-pairs those that he accepts with probability at most one third. -/
theorem MA_subset_NP_of_PromiseBPP_subset_PromiseP
    (h : PromiseBPP (encPair enc encBits) ⊆ PromiseP (encPair enc encBits)) :
    MA enc ⊆ NP enc := by
  rintro A ⟨q, p, V, hV, hMA⟩
  -- Arthur's check of a fixed proof `w` on instance `a`
  let arthur (w : List Bool) : α × List Bool → Bool := fun y => V (y.1, w ++ y.2)
  have hdisj (z : α × List Bool) (htrue : BoundedErrorAt enc p (arthur z.2) z.1 true)
      (hfalse : BoundedErrorAt enc p (arthur z.2) z.1 false) : False := by
    rw [boundedErrorAt_true_iff] at htrue
    rw [boundedErrorAt_false_iff] at hfalse
    have := Nat.one_le_two_pow (n := p.eval (enc z.1).length)
    omega
  let Q : PromiseProblem (α × List Bool) :=
    { yes := {z | BoundedErrorAt enc p (arthur z.2) z.1 true}
      no := {z | BoundedErrorAt enc p (arthur z.2) z.1 false}
      disjoint := Set.disjoint_left.2 fun z hyes hno => hdisj z hyes hno }
  -- on pairs, Arthur reads the first `p (|a|)` bits of a random string of length `p (|(a, w)|)`
  let V' : (α × List Bool) × List Bool → Bool := fun x =>
    V (x.1.1, x.1.2 ++ x.2.take (p.eval (enc x.1.1).length))
  have hV' : ComputableInPolyTime V' (encPair (encPair enc encBits) encBits) encBool :=
    hV.comp (ComputableInPolyTime.prod (by fun_prop)
      (ComputableInPolyTime.bitsAppend (by fun_prop)
        (ComputableInPolyTime.bitsTakeWithInput (by fun_prop) (by fun_prop))))
  -- bounded error transfers from the instance to the pair
  have htransfer (z : α × List Bool) (b : Bool) :
      BoundedErrorAt (encPair enc encBits) p V' z b ↔ BoundedErrorAt enc p (arthur z.2) z.1 b := by
    set K := p.eval (encPair enc encBits z).length
    set k := p.eval (enc z.1).length
    have hkK : k ≤ K := Polynomial.monotone_eval p (by
      simp only [encPair_apply, List.length_append, length_frame]
      omega)
    have hcount := BitString.card_filter_take hkK fun u => V (z.1, z.2 ++ u) = b
    simp only [BoundedErrorAt]
    change 2 * 2 ^ K ≤ 3 * #{r : Fin K → Bool |
        V (z.1, z.2 ++ (List.ofFn r).take k) = b} ↔
      2 * 2 ^ k ≤ 3 * #{r : Fin k → Bool | V (z.1, z.2 ++ List.ofFn r) = b}
    rw [hcount, ← Nat.sub_add_cancel hkK, pow_add, Nat.add_sub_cancel,
      mul_left_comm 2, mul_left_comm 3, mul_le_mul_iff_right₀ (Nat.two_pow_pos _)]
  have hQ : Q ∈ PromiseBPP (encPair enc encBits) :=
    ⟨p, V', hV', fun z => ⟨fun hz => (htransfer z true).2 hz, fun hz => (htransfer z false).2 hz⟩⟩
  obtain ⟨f, hf, hyes, hno⟩ := mem_PromiseP_iff.1 (h hQ)
  refine ⟨q, f, hf, fun a => ⟨fun ha => ?_, fun ⟨w, hw, hfw⟩ => ?_⟩⟩
  · obtain ⟨y, hy⟩ := (hMA a).1 ha
    exact ⟨List.ofFn y, List.length_ofFn, hyes (a, List.ofFn y) hy⟩
  · by_contra ha
    have h' := (hMA a).2 ha (BitString.ofList _ w)
    rw [BitString.ofFn_ofList hw] at h'
    exact Bool.false_ne_true (hno (a, w) h' ▸ hfw)

/-- **Average-case hardness in `E` collapses `MA` to `NP`** [Arora and Barak,
Exercise 16.4][AroraBarak07] (web draft 2007-01-08, printed p. 318, PDF p. 334). Let `L` be a
problem on words in `E`, decidable in time `O(2 ^ (k n))` for some `k`, and let `c > 0`. If for all
large `n` the slice of `L` at `n` is average-case hard for size `2 ^ (n / c)`, then
`MA enc = NP enc` for every encoding `enc` of instances.

The draft assumes `f ∈ E` and `ε > 0` with `H_avg(f)(n) ≥ 2 ^ (ε n)` for every `n`
(Definition 16.7: for some natural `S ≥ 2 ^ (ε n)`, every circuit of size at most `S` agrees with
`f` on less than a `1 / 2 + 1 / S` fraction of the inputs). That hypothesis implies the one here
for every natural `c > 1 / ε` (for instance `c > 2 / ε`). The two circuit conventions differ:
the draft's Definition 6.1 counts all nodes (inputs, AND, OR and NOT gates of fan-in at most two,
and output nodes, without constants), while `Cslib.Circuits.Boolean.IsAverageCaseHard` counts the
De Morgan gates (AND, OR, NOT and constants) of a circuit, not its inputs. Translate a De Morgan
circuit with `s` gates on `n ≥ 1` inputs into a source circuit whose only node without outgoing
edges is the output (Definition 6.1 counts every such node as an output): drop the gates the
output does not depend on, replace each constant gate by `x₁ ∧ ¬x₁` or `¬(x₁ ∧ ¬x₁)`, fold every
unused input into one dummy zero (an AND of inputs with a negation) and OR that zero into the
output. The result has `O(n + s + 1)` nodes. With `s = 2 ^ ⌊n / c⌋ ≤ 2 ^ (n / c)` and
`1 / c < ε`, this linear overhead is eventually at most `2 ^ (ε n) ≤ S`. So
every Boolean function `g` of complexity at most `s` agrees with `f` on less than a
`1 / 2 + 1 / S ≤ 1 / 2 + 1 / s` fraction of the inputs, since `s ≤ S`. That is
`IsAverageCaseHard (f.slice n) s` for all large `n`, the hypothesis here. So the theorem holds
under the draft's hypothesis, and also under the weaker one stated: eventual, non-strict
hardness. `MA` has two-sided error `1 / 3` (`Cslib.Complexity.MA`). -/
theorem MA_eq_NP_of_isAverageCaseHard {L : Language Bool} {c : ℕ}
    (hL : (L : Set (List Bool)) ∈ E encBits) (hc : 0 < c)
    (hard : ∀ᶠ n in atTop, IsAverageCaseHard (L.slice n) (2 ^ (n / c)))
    (enc : α ↪ List Bool) : MA enc = NP enc :=
  (MA_subset_NP_of_PromiseBPP_subset_PromiseP
    (PromiseBPP_subset_PromiseP_of_isAverageCaseHard hL hc hard _)).antisymm NP_subset_MA

end Cslib.Complexity
