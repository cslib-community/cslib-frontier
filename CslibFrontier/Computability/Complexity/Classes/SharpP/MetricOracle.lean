/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.Counting
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Metric
public import CslibFrontier.Computability.Complexity.Classes.Oracle.QueryBit
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
import CslibFrontier.Computability.Complexity.Classes.SharpP.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Oracle.Composition

/-!
# Metric reductions as oracle computations

Arora and Barak define `FP^f` for `f : {0,1}* → ℕ` as the functions computable in polynomial time
by an oracle machine that may ask for bit `i` of `f x` [Arora and Barak, Section 9.2][AroraBarak07];
here the oracle language answers the bits of `f` (`Cslib.Complexity.AnswersBits`, for instance
`Cslib.Complexity.bitGraph`). A function is #P-complete in their sense (Definition 9.5) when it is
in #P and every function in #P lies in `FP^f`.

A metric reduction `f a = post (a, g (r a))` is such an oracle computation when the values of `g`
have polynomially many bits: the program `Cslib.Complexity.readBitsProgram` asks, one after the
other, for bits `0, 1, …, c a - 1` of `g (r a)`, where `c a` is a polynomial in the length of the
encoded query, reassembles the number, and applies `post`
(`Cslib.Complexity.MetricReducible.polyTimeOracleProgram`). The program is fixed before the
oracle and is correct against every oracle language answering the bits of `g`. Hence
#P-completeness under metric reductions gives #P-completeness in the sense of Arora and Barak
(`Cslib.Complexity.SharpPMetricComplete.computableInPolyTimeWithOracle`).

## Main results

* `Cslib.Complexity.MetricReducible.polyTimeOracleProgram`,
  `Cslib.Complexity.MetricReducible.computableInPolyTimeWithOracle`: a metric reduction to a
  function with polynomially many bits is a polynomial-time oracle computation.
* `Cslib.Complexity.SharpPMetricComplete.computableInPolyTimeWithOracle`: every #P function is
  in `FP^f` for a #P-complete `f` under metric reductions (Arora–Barak Definition 9.5).
* `Cslib.Complexity.mem_SharpP_iff_computableInPolyTime_of_bitGraph`: if every #P function under
  an encoding is in `FP^g` and `g ∈ FP`, then `#P = FP` under that encoding (Arora–Barak
  Proposition 9.6).

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 draft][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α β Y : Type}

variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encY : Y ↪ List Bool}

/-- **A metric reduction is a polynomial-time oracle program.** If `f` reduces by a metric
reduction to `g`, whose values have fewer than `p (|encB b|)` bits for a polynomial `p`, then one
polynomial-time oracle program computes `f` against every oracle language answering the bits of
`g`: it reads the bits of `g (r a)` and applies the recovery map. -/
theorem MetricReducible.polyTimeOracleProgram {f : α → Y} {g : β → ℕ}
    (h : MetricReducible encA encB encY encNat f g) {p : Polynomial ℕ}
    (hp : ∀ b, g b < 2 ^ p.eval (encB b).length) :
    PolyTimeOracleProgram encA encY (AnswersBits encB g) (· = f) := by
  classical
  obtain ⟨r, post, hr, hpost, hfg⟩ := h
  let req : α → ℕ → List Bool := fun a i => encPair encB encNat (r a, i)
  let count : α → ℕ := fun a => p.eval (encB (r a)).length
  have hreq : ComputableInPolyTime (fun q : α × ℕ => req q.1 q.2) (encPair encA encUnary)
      encBits :=
    .encoding_comp (f := fun q : α × ℕ => (r q.1, q.2))
      ((hr.comp (.fst _ _)).prod (ComputableInPolyTime.unary_to_binary.comp (.snd _ _)))
  have hcount : ComputableInPolyTime count encA encUnary :=
    (by fun_prop : ComputableInPolyTime (fun b => p.eval (encB b).length) encB encUnary).comp hr
  have hpost' : ComputableInPolyTime (fun q : α × List Bool => post (q.1, ofBits q.2))
      (encPair encA encBits) encY :=
    hpost.comp ((ComputableInPolyTime.fst _ _).prod
      (ComputableInPolyTime.bitsToNat.comp (.snd _ _)))
  refine ⟨fun a => (fun bits => post (a, ofBits bits)) <$> readBitsProgram req count a,
    by simpa only [OracleComp.interpret_map] using
      (isOraclePPTOn_readBitsProgram hreq hcount).map_with hpost',
    fun A hA => funext fun a => ?_⟩
  rw [OracleComp.interpret_map, interpret_readBitsProgram, hfg a]
  change post (a, ofBits (List.ofFn _)) = _
  rw [hA.ofFn_eq_lowBits (r a) (count a), ofBits_lowBits (hp (r a))]

/-- A metric reduction to a function `g` with polynomially many bits makes `f` computable in
polynomial time relative to the bit graph of `g`: `f ∈ FP^g` in the sense of Arora and Barak. -/
theorem MetricReducible.computableInPolyTimeWithOracle {f : α → Y} {g : β → ℕ}
    (h : MetricReducible encA encB encY encNat f g) {p : Polynomial ℕ}
    (hp : ∀ b, g b < 2 ^ p.eval (encB b).length) :
    ComputableInPolyTimeWithOracle (bitGraph encB g) f encA encY := by
  obtain ⟨_, hg, rfl⟩ := (h.polyTimeOracleProgram hp).exists_computableInPolyTimeWithOracle
    (answersBits_bitGraph encB g)
  exact hg

/-- **#P-completeness under metric reductions gives #P-completeness in the sense of Arora and
Barak** (Definition 9.5): every function in #P is computable in polynomial time relative to the
bit graph of a #P-complete function. -/
theorem SharpPMetricComplete.computableInPolyTimeWithOracle {g : β → ℕ}
    (hg : SharpPMetricComplete encB g) {f : α → ℕ} (hf : f ∈ SharpP encA) :
    ComputableInPolyTimeWithOracle (bitGraph encB g) f encA encNat := by
  obtain ⟨p, hp⟩ := SharpP.exists_le_two_pow hg.1
  refine (hg.2 _ _ hf).computableInPolyTimeWithOracle (p := p + 1) fun b => ?_
  calc g b ≤ 2 ^ p.eval (encB b).length := hp b
    _ < 2 ^ (p + 1).eval (encB b).length := Nat.pow_lt_pow_right (by norm_num) (by simp)

/-- **A #P-complete function in FP collapses #P to FP** [AroraBarak07, Proposition 9.6]. Fix an
instance encoding `encA`. Suppose every function in #P under `encA` is computable in polynomial
time relative to the bit graph of `g`, as in Definition 9.5, and `g` itself is computable in
polynomial time. Then the functions in #P under `encA` are exactly the polynomial-time functions
with binary output (`FP` here): `f ∈ FP^g = FP`, and `FP ⊆ #P` by `mem_SharpP_of_polyTime`.

The draft's functions are on `{0,1}*`: at `encA = encBits` the completeness premise is
Definition 9.5's, and `Decoder.bits` decodes the instances of `g`. Here `g` may have any instance
encoding with a polynomial-time decoder, which lets the bit-graph oracle reject words that are not
codes (`bitGraph_mem_P`). The draft's hypothesis `g ∈ #P` is not needed. For #SAT and the 0/1
permanent, the completeness premise holds at every encoding, by
`SharpPMetricComplete.computableInPolyTimeWithOracle`. -/
theorem mem_SharpP_iff_computableInPolyTime_of_bitGraph {g : β → ℕ} (D : Decoder encB)
    (hcomplete : ∀ f : α → ℕ, f ∈ SharpP encA →
      ComputableInPolyTimeWithOracle (bitGraph encB g) f encA encNat)
    (hg : ComputableInPolyTime g encB encNat) {f : α → ℕ} :
    f ∈ SharpP encA ↔ ComputableInPolyTime f encA encNat :=
  ⟨fun hf => (hcomplete f hf).computableInPolyTime (bitGraph_mem_P D hg),
    mem_SharpP_of_polyTime⟩

end Cslib.Complexity
