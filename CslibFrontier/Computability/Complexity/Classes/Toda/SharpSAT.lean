/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Toda
public import CslibFrontier.Computability.Complexity.CookLevin.Counting
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Toda's theorem with a `#SAT` oracle

[Arora and Barak, Theorem 9.11][AroraBarak07] (2007-01-08 draft, printed p. 179 / PDF p. 195)
states `PH ⊆ P^{#SAT}`: one fixed counting oracle suffices. As in Definition 9.5 and the
library's `FP^{#SAT}` (`Cslib.Complexity.intPermanent_computableInPolyTimeWithOracle_SharpSAT`),
access to the function `#SAT` is access to its bit graph `bitGraph encCNF SharpSAT`, and
formulas are CNF formulas under `encCNF`.

The class `P^#P` of `Cslib.Complexity.PWithSharpPOracle` lets each problem choose its own
function in `#P`, and a program in it may send arbitrary words as queries. Translating such
queries to `#SAT` would need to recognize and decode instance codes at the word level. The proof
here avoids that: Toda's proof decides a problem in `PH` by one bit of a function `f` in `#P` on
its own instances (`Cslib.Complexity.exists_SharpP_testBit_of_mem_BPOp_ParityP`), and a
parsimonious reduction `r` with `f a = g (r a)` turns that bit into one query to the bit graph
of `g`, about the instance `r a` that the program computes itself.

## Main results

* `Cslib.Complexity.SharpPHard.mem_PWithOracle_bitGraph_of_testBit`: a bit at a polynomial
  position of a function in `#P` is decided with one query to the bit graph of any function that
  is `#P`-hard under parsimonious reductions.
* `Cslib.Complexity.PH_subset_PWithOracle_bitGraph_SharpSAT`: **Toda's theorem,
  `PH ⊆ P^{#SAT}`**.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach* (2007 draft)][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {encβ : β ↪ List Bool} {g : β → ℕ} {L : Set α}

/-- **One bit of a `#P` value, with a fixed hard counting oracle**: if `g` is `#P`-hard under
parsimonious reductions, a problem decided by the bit at a polynomial position of a function in
`#P` on its own instances is in polynomial time relative to the bit graph of `g`. The program
computes the parsimonious image of its instance and asks for one bit of its `g` value. -/
theorem SharpPHard.mem_PWithOracle_bitGraph_of_testBit (hg : SharpPHard encβ g) {f : α → ℕ}
    (hf : f ∈ SharpP enc) {p : Polynomial ℕ}
    (h : ∀ a, a ∈ L ↔ (f a).testBit (p.eval (enc a).length)) :
    L ∈ PWithOracle (bitGraph encβ g) enc := by
  classical
  obtain ⟨r, hr, hfr⟩ := hg enc f hf
  have hq : ComputableInPolyTime (fun a => encPair encβ encNat (r a, p.eval (enc a).length))
      enc encBits :=
    ComputableInPolyTime.encoding_comp (f := fun a => (r a, p.eval (enc a).length))
      (hr.prod (ComputableInPolyTime.unary_to_binary.comp (f := fun n : ℕ => n)
        (g := fun a => p.eval (enc a).length) (by fun_prop)))
  exact (PolyTimeOracleProgram.of_query (Admissible := (· = bitGraph encβ g))
    (Spec := fun d => ∀ a, a ∈ L ↔ d a = true) hq fun A hA a => by
      subst hA
      rw [h a, hfr a, decide_eq_true_iff]
      exact (answersBits_bitGraph encβ g _ _).symm).exists_computableInPolyTimeWithOracle rfl

/-- **Toda's theorem, `PH ⊆ P^{#SAT}`** [Toda][Toda1991], [Arora and Barak, Theorem
9.11][AroraBarak07]: every problem in the polynomial hierarchy, under any encoding of its
instances, is decided in polynomial time relative to the fixed oracle language
`bitGraph encCNF SharpSAT`, the bit graph of the number of satisfying assignments of CNF
formulas. The program of the proof makes one query. -/
theorem PH_subset_PWithOracle_bitGraph_SharpSAT :
    PH enc ⊆ PWithOracle (bitGraph encCNF SharpSAT) enc := fun _ hL =>
  let ⟨_, hf, _, h⟩ := exists_SharpP_testBit_of_mem_BPOp_ParityP (PH_subset_BPOp_ParityP hL)
  CookLevin.SharpSAT_sharpPHard.mem_PWithOracle_bitGraph_of_testBit hf h

end Cslib.Complexity
