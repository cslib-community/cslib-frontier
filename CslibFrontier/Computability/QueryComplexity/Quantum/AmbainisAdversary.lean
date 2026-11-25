/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Progress
public import CslibFrontier.Computability.QueryComplexity.Quantum.Search
public import Cslib.Foundations.Data.BitString
import CslibFrontier.Computability.QueryComplexity.Quantum.ValueAdversary
import CslibFrontier.Foundations.Data.BitString.Flip
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Foundations.Quantum.Measurement.Overlap

/-!
# Ambainis's quantum adversary method

Let a `T`-query algorithm (`Cslib.Quantum.run`) with a unit initial state be run on related pairs
`(x, y) ∈ R` of inputs, and suppose that at the end the states on every related pair have overlap
`|⟨ψ_x, ψ_y⟩| ≤ δ`. Suppose also that every first input of `R` is related to at least `m` inputs
and every second input to at least `m'`, and that `l_{x,i} l_{y,i} ≤ L` for every related pair
`(x, y)` and every coordinate `i` with `x_i ≠ y_i`. Here `l_{x,i}` is the number of pairs of `R`
with first input `x` that differ at `i`, and `l_{y,i}` is the number with second input `y`. Then
`(1 - δ) √(m m') ≤ 2T √L` (`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_sqrt`), which is
[Ambainis2002], Theorem 6, for bit queries. If a measurement accepts every first input with
probability at least `1 - ε` and every second input with probability at most `ε ≤ 1/2`, then
`δ = 2√(ε(1-ε))` (`Cslib.Quantum.norm_inner_le_two_mul_sqrt_of_measureProb`, [Ambainis2002],
Lemma 1). Bounding `l_{x,i} ≤ l` and `l_{y,i} ≤ l'` gives [Ambainis2002], Theorem 2:
`(1 - 2√(ε(1-ε))) √(m m') ≤ 2T √(l l')`
(`Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt`).

Only the inputs that occur in `R` are constrained, so the bounds apply to promise problems and
partial functions: correctness is required only on those inputs. When the related pairs are the
neighbors `(x, x ⊕ eᵢ)` with `x ∈ A` and `x ⊕ eᵢ ∈ B`, `l = l' = 1`, and the bound reads
`(1 - δ) √(m m') ≤ 2T` with `m` and `m'` lower bounds on the numbers of neighbors across
(`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_neighbors`). The applications to parity,
threshold functions and majority are in the module
`CslibFrontier.Computability.QueryComplexity.Quantum.AmbainisAdversary.Symmetric`, and those to
Tribes and to the `AND` of `OR`s in
`CslibFrontier.Computability.QueryComplexity.Quantum.AmbainisAdversary.Tribes`.

**The argument.** Viewing `Cslib.Quantum.phaseOracle` as the value-query oracle
`Cslib.Quantum.valueOracle Cslib.Quantum.phaseStep` on `State N W = ValueState (Fin N) Bool W`
(`Cslib.Quantum.runValue_phaseStep`) specializes the general value-query Theorem 6 bound
`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_sqrt_value` in
`CslibFrontier.Computability.QueryComplexity.Quantum.ValueAdversary` directly to Boolean bit
queries:
* Before any query all states are equal, so the unweighted progress sum starts at `|R|` and ends at
  most `δ |R|`.
* One query lowers `|⟨ψ_x, ψ_y⟩|` only at indices `i` with `x_i ≠ y_i`, where Cauchy–Schwarz and
  Parseval across query slices bound each step's drop by `2 √L √(|X| |Y|)` for first- and
  second-input sets `X` and `Y`.
* Finally `|R| ≥ m |X|` and `|R| ≥ m' |Y|`, so `|R| ≥ √(m m') √(|X| |Y|)`.

**Source mapping** (numbering of arXiv:quant-ph/0002066v1).
* `one_sub_mul_sqrt_le_two_mul_mul_sqrt` is Theorem 6 (§6.1) for `{0, 1}`-valued variables. The
  conclusion is stated through the final overlap `δ` on the related pairs rather than through a
  function `f`, so it holds for any output alphabet: Lemma 1 may be applied to each pair with the
  measurement of the answer `f(x)`.
* `norm_inner_le_two_mul_sqrt_of_measureProb` is Lemma 1 (§3), for one measurement.
* `one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt` is Theorem 2 (§5.1), for Boolean outputs
  read off one set `S` of measurement outcomes.
* `one_sub_mul_sqrt_le_two_mul_of_neighbors` is the case `l = l' = 1` of Theorem 2 that §5.3 uses
  for the `AND` of `OR`s (Theorem 4) and for majority and parity.

The source states `Ω(·)` bounds. The constants are those of this proof. As in the polynomial
method (`CslibFrontier.Computability.QueryComplexity.Quantum.Polynomial`), the bounds hold for each
algorithm. There is no separate definition of quantum query complexity.

## Main results

* `Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_sqrt`: `(1 - δ) √(m m') ≤ 2T √L`.
* `Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt`:
  `(1 - 2√(ε(1-ε))) √(m m') ≤ 2T √(l l')`.
* `Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_of_neighbors` and
  `Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_of_neighbors`: the bounds across single
  bit flips.

## References

* [A. Ambainis, *Quantum lower bounds by quantum arguments*][Ambainis2002]
-/

public section

namespace Cslib.Quantum

open Finset Function

variable {N : ℕ} {W : Type*} [Fintype W]

variable (U : ℕ → State N W →ₗᵢ[ℂ] State N W)

/-- **Ambainis's adversary bound** [Ambainis2002], Theorem 6, for bit queries: let `R` be a
nonempty set of pairs of inputs on which a `T`-query algorithm with a unit initial state ends in
states with overlap at most `δ`. If every first input of `R` lies in at least `m` pairs of `R` and
every second input in at least `m'`, and `l_{x,i} l_{y,i} ≤ L` for every `(x, y) ∈ R` and every
`i` with `x_i ≠ y_i`, where `l_{x,i}` counts the pairs of `R` with first input `x` that differ at
`i` and `l_{y,i}` those with second input `y`, then `(1 - δ) √(m m') ≤ 2T √L`. The constant is
that of this proof. The source states `Ω(√(m m' / l_max))`. -/
theorem one_sub_mul_sqrt_le_two_mul_mul_sqrt {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    {R : Finset (BitString N × BitString N)} (hR : R.Nonempty) {δ : ℝ}
    (hδ : ∀ p ∈ R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ δ) {m m' L : ℕ}
    (hm : ∀ p ∈ R, m ≤ #{q ∈ R | q.1 = p.1}) (hm' : ∀ p ∈ R, m' ≤ #{q ∈ R | q.2 = p.2})
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L) :
    (1 - δ) * √(m * m') ≤ 2 * T * √L :=
  one_sub_mul_sqrt_le_two_mul_mul_sqrt_value phaseStep U hψ₀ T hR
    (by simpa only [runValue_phaseStep] using hδ) hm hm' hL

/-- **Ambainis's adversary bound** [Ambainis2002], Theorem 2, for Boolean outputs: let a
`T`-query algorithm with a unit initial state accept, by an outcome in `S`, the first input of
every pair of a nonempty set `R` with probability at least `1 - ε` and the second with probability
at most `ε ≤ 1/2`. If every first input lies in at least `m` pairs and every second input in at
least `m'`, and for every coordinate `i` every first input lies in at most `l` pairs differing at
`i` and every second input in at most `l'`, then `(1 - 2√(ε(1-ε))) √(m m') ≤ 2T √(l l')`. The
constant is that of this proof. The source states `Ω(√(m m' / (l l')))`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) (S : Finset (Fin N × Bool × W)) {R : Finset (BitString N × BitString N)}
    (hR : R.Nonempty) {ε : ℝ} (h₁ : ∀ p ∈ R, 1 - ε ≤ measureProb (run U ψ₀ p.1 T) S)
    (h₂ : ∀ p ∈ R, measureProb (run U ψ₀ p.2 T) S ≤ ε) (hε : 2 * ε ≤ 1) {m m' l l' : ℕ}
    (hm : ∀ p ∈ R, m ≤ #{q ∈ R | q.1 = p.1}) (hm' : ∀ p ∈ R, m' ≤ #{q ∈ R | q.2 = p.2})
    (hl : ∀ p ∈ R, ∀ i, #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} ≤ l)
    (hl' : ∀ p ∈ R, ∀ i, #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ l') :
    (1 - 2 * √(ε * (1 - ε))) * √(m * m') ≤ 2 * T * √(l * l') := by
  have hδ : ∀ p ∈ R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ 2 * √(ε * (1 - ε)) :=
    fun p hp => norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, hψ₀])
      (by rw [norm_run, hψ₀]) (h₁ p hp) (h₂ p hp) hε
  simpa only [Nat.cast_mul] using one_sub_mul_sqrt_le_two_mul_mul_sqrt U hψ₀ T hR hδ hm hm'
    (L := l * l') fun p hp i _ => Nat.mul_le_mul (hl p hp i) (hl' p hp i)

/-- **The adversary bound across single bit flips**, the case `l = l' = 1` of [Ambainis2002],
Theorem 2, in which the related pairs are the neighbors `(x, x ⊕ eᵢ)` with `x ∈ A` and
`x ⊕ eᵢ ∈ B`: let a `T`-query algorithm with a unit initial state end, on every such pair, in
states with overlap at most `δ`. If `A` is nonempty, every input in `A` has at least `m` neighbors
in `B` and every input in `B` has at least `m'` neighbors in `A`, then `(1 - δ) √(m m') ≤ 2T`. -/
theorem one_sub_mul_sqrt_le_two_mul_of_neighbors {ψ₀ : State N W} (hψ₀ : ‖ψ₀‖ = 1)
    (T : ℕ) {A B : Finset (BitString N)} (hA : A.Nonempty) {δ : ℝ}
    (hδ : ∀ x ∈ A, ∀ i, update x i (!x i) ∈ B →
      ‖inner ℂ (run U ψ₀ x T) (run U ψ₀ (update x i (!x i)) T)‖ ≤ δ) {m m' : ℕ}
    (hm : ∀ x ∈ A, m ≤ #{i | update x i (!x i) ∈ B})
    (hm' : ∀ y ∈ B, m' ≤ #{i | update y i (!y i) ∈ A}) :
    (1 - δ) * √(m * m') ≤ 2 * T := by
  classical
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · simp [h0]
  set R := hammingEdges A B
  have hflip (x : BitString N) (i : Fin N) : hammingDist x (update x i (!x i)) = 1 :=
    hammingDist_update_of_ne (by cases x i <;> simp)
  -- `R` is nonempty: some input of `A` has a neighbor in `B`
  have hR : R.Nonempty := by
    obtain ⟨x, hx⟩ := hA
    obtain ⟨i, hi⟩ := card_pos.1 (lt_of_lt_of_le hpos (hm x hx))
    exact ⟨(x, update x i (!x i)), mem_hammingEdges.2 ⟨hx, (mem_filter.1 hi).2, hflip x i⟩⟩
  -- the overlap on every related pair is at most `δ`
  have hδR : ∀ p ∈ R, ‖inner ℂ (run U ψ₀ p.1 T) (run U ψ₀ p.2 T)‖ ≤ δ := by
    intro p hp
    obtain ⟨hpA, hpB, hd⟩ := mem_hammingEdges.1 hp
    obtain ⟨i, hi, -⟩ := hammingDist_eq_one_iff.1 hd
    have hp2 := (update_not_eq_of_hammingDist_le_one hd.le hi).symm
    rw [hp2] at hpB ⊢
    exact hδ p.1 hpA i hpB
  -- at most one pair from each end differs at a given coordinate
  have hl : ∀ p ∈ R, ∀ i, #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} ≤ 1 := by
    refine fun p _ i => card_le_one.2 fun q hq r hr => ?_
    obtain ⟨hqR, hqi, hq1⟩ := mem_filter.1 hq
    obtain ⟨hrR, hri, hr1⟩ := mem_filter.1 hr
    have hq2 := (update_not_eq_of_hammingDist_le_one (mem_hammingEdges.1 hqR).2.2.le hqi).symm
    have hr2 := (update_not_eq_of_hammingDist_le_one (mem_hammingEdges.1 hrR).2.2.le hri).symm
    exact Prod.ext (hq1.trans hr1.symm) (by rw [hq2, hr2, hq1, hr1])
  have hl' : ∀ p ∈ R, ∀ i, #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ 1 := by
    refine fun p _ i => card_le_one.2 fun q hq r hr => ?_
    obtain ⟨hqR, hqi, hq2⟩ := mem_filter.1 hq
    obtain ⟨hrR, hri, hr2⟩ := mem_filter.1 hr
    have hq1 := (update_not_eq_of_hammingDist_le_one
      ((hammingDist_comm _ _).trans (mem_hammingEdges.1 hqR).2.2).le (Ne.symm hqi)).symm
    have hr1 := (update_not_eq_of_hammingDist_le_one
      ((hammingDist_comm _ _).trans (mem_hammingEdges.1 hrR).2.2).le (Ne.symm hri)).symm
    exact Prod.ext (by rw [hq1, hr1, hq2, hr2]) (hq2.trans hr2.symm)
  -- every input has its neighbors as partners
  have hdeg : ∀ p ∈ R, m ≤ #{q ∈ R | q.1 = p.1} := by
    intro p hp
    refine (hm p.1 (mem_hammingEdges.1 hp).1).trans (card_le_card_of_injOn
      (fun i => (p.1, update p.1 i (!p.1 i))) (fun i hi => ?_) ?_)
    · exact mem_filter.2
        ⟨mem_hammingEdges.2 ⟨(mem_hammingEdges.1 hp).1, (mem_filter.1 hi).2, hflip _ i⟩, rfl⟩
    · intro i _ j _ hij
      exact BitString.update_not_injective p.1 (congrArg Prod.snd hij)
  have hdeg' : ∀ p ∈ R, m' ≤ #{q ∈ R | q.2 = p.2} := by
    intro p hp
    refine (hm' p.2 (mem_hammingEdges.1 hp).2.1).trans (card_le_card_of_injOn
      (fun i => (update p.2 i (!p.2 i), p.2)) (fun i hi => ?_) ?_)
    · refine mem_filter.2
        ⟨mem_hammingEdges.2 ⟨(mem_filter.1 hi).2, (mem_hammingEdges.1 hp).2.1, ?_⟩, rfl⟩
      exact (hammingDist_comm _ _).trans (hflip _ i)
    · intro i _ j _ hij
      exact BitString.update_not_injective p.2 (congrArg Prod.fst hij)
  simpa using one_sub_mul_sqrt_le_two_mul_mul_sqrt U hψ₀ T hR hδR hdeg hdeg' (L := 1)
    fun p hp i _ => (Nat.mul_le_mul (hl p hp i) (hl' p hp i)).trans_eq (mul_one 1)

/-- **The adversary bound across single bit flips**, for Boolean outputs: let a `T`-query
algorithm with a unit initial state accept every input in a nonempty set `A`, by an outcome in
`S`, with probability at least `1 - ε` and every input in `B` with probability at most `ε ≤ 1/2`.
If every input in `A` has at least `m` neighbors in `B` and every input in `B` has at least `m'`
neighbors in `A`, then `(1 - 2√(ε(1-ε))) √(m m') ≤ 2T`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_of_neighbors {ψ₀ : State N W}
    (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ) (S : Finset (Fin N × Bool × W)) {A B : Finset (BitString N)}
    (hA : A.Nonempty) {ε : ℝ} (h₁ : ∀ x ∈ A, 1 - ε ≤ measureProb (run U ψ₀ x T) S)
    (h₂ : ∀ y ∈ B, measureProb (run U ψ₀ y T) S ≤ ε) (hε : 2 * ε ≤ 1) {m m' : ℕ}
    (hm : ∀ x ∈ A, m ≤ #{i | update x i (!x i) ∈ B})
    (hm' : ∀ y ∈ B, m' ≤ #{i | update y i (!y i) ∈ A}) :
    (1 - 2 * √(ε * (1 - ε))) * √(m * m') ≤ 2 * T :=
  one_sub_mul_sqrt_le_two_mul_of_neighbors U hψ₀ T hA
    (fun x hx _ hi => norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, hψ₀])
      (by rw [norm_run, hψ₀]) (h₁ x hx) (h₂ _ hi) hε) hm hm'

end Cslib.Quantum
