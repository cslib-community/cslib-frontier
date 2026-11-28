/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Mathlib.Data.Nat.Bitwise

/-!
# Polynomial time with a `#P` oracle

The oracle classes of `Cslib.Complexity.PWithOracle` query languages. The values of a function
`f : β → ℕ` are queried bit by bit: the *code* `encPair encβ encNat (b, i)` asks for bit `i` of
`f b`, under an encoding `encβ` of the arguments of `f`. An oracle language *answers the bits*
of `f` (`Cslib.Complexity.AnswersBits`) when it contains every code exactly when the requested
bit is `1`; it may answer other words arbitrarily. The bit graph of `f`
(`Cslib.Complexity.bitGraph`), which contains the codes of the bits `1` and nothing else,
answers the bits of `f`.

`P^#P` relative to the encoding `enc` of instances (`Cslib.Complexity.PWithSharpPOracle`)
consists of the problems `L` decided by one deterministic oracle program, strict oracle PPT as
in `Cslib.Complexity.ComputableInPolyTimeWithOracle`, that is correct against every oracle
language answering the bits of some function `f ∈ #P`, for some encoded type of arguments of
`f`. As for `Cslib.Complexity.RPWithPromiseOracle`, the program is fixed before the oracle, and
the answers on words that are not codes are arbitrary, so the program only learns bits of `f`;
in particular the oracle does not reveal which words are codes, however hard that is to decide.
Taking the bit graph as the oracle language, such a problem is in polynomial time relative to
the bit graph of a function in `#P` (`Cslib.Complexity.mem_PWithOracle_bitGraph`). The class
does not count queries; it contains `P` (`Cslib.Complexity.P_subset_PWithSharpPOracle`), and a
problem decided by one bit, at a polynomial position, of a function in `#P` on its own instances
is in it, by a program making one query
(`Cslib.Complexity.mem_PWithSharpPOracle_of_testBit`).

## Main definitions

* `Cslib.Complexity.AnswersBits`: an oracle language answering the bits of a function.
* `Cslib.Complexity.bitGraph`: the bits of a function, as an oracle language.
* `Cslib.Complexity.PWithSharpPOracle`: polynomial time with a `#P` oracle.

## Main results

* `Cslib.Complexity.answersBits_bitGraph`: the bit graph answers the bits.
* `Cslib.Complexity.bitGraph_mem_P`: the bit graph of a polynomial-time function is in `P`, when
  its instance encoding has a decoder.
* `Cslib.Complexity.mem_PWithOracle_bitGraph`: `P^#P` lies in polynomial time relative to the
  bit graph of a function in `#P`.
* `Cslib.Complexity.P_subset_PWithSharpPOracle`: `P ⊆ P^#P`.
* `Cslib.Complexity.mem_PWithSharpPOracle_of_testBit`: one bit of a `#P` value is in `P^#P`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α β : Type}

/-- The oracle language `A` **answers the bits** of `f : β → ℕ` under the encoding `encβ`: the
code `encPair encβ encNat (b, i)` is in `A` exactly when bit `i` of `f b` is `1`. Words that are
not codes may be in `A` or not. -/
def AnswersBits (encβ : β ↪ List Bool) (f : β → ℕ) (A : Set (List Bool)) : Prop :=
  ∀ b i, encPair encβ encNat (b, i) ∈ A ↔ (f b).testBit i

/-- Reading the first `w` bit answers in order reconstructs exactly the low bits of the value. -/
theorem AnswersBits.ofFn_eq_lowBits {enc : β ↪ List Bool} {g : β → ℕ} {A : Set (List Bool)}
    [DecidablePred (· ∈ A)] (hA : AnswersBits enc g A) (b : β) (w : ℕ) :
    (List.ofFn fun i : Fin w => decide (encPair enc encNat (b, i.val) ∈ A)) =
      BitString.lowBits w (g b) := by
  rw [BitString.lowBits_eq_ofFn]
  refine congrArg List.ofFn (funext fun i => Bool.eq_iff_iff.mpr ?_)
  exact decide_eq_true_iff.trans (hA b i)

/-- The bit graph of `f : β → ℕ`: the codes `encPair encβ encNat (b, i)` such that bit `i` of
`f b` is `1`, and no other word. -/
def bitGraph (encβ : β ↪ List Bool) (f : β → ℕ) : Set (List Bool) :=
  encPair encβ encNat '' {x | (f x.1).testBit x.2}

/-- The bit graph answers the bits. -/
theorem answersBits_bitGraph (encβ : β ↪ List Bool) (f : β → ℕ) :
    AnswersBits encβ f (bitGraph encβ f) := fun _ _ =>
  (encPair encβ encNat).injective.mem_set_image

/-- **The bit graph of a polynomial-time function is in `P`.** If `g` is computable in polynomial
time with binary output and `encβ` has a polynomial-time decoder, a word is decided by decoding it
as a pair `(b, i)`, checking that it re-encodes to itself, and reading bit `i` of `g b`. The
position `i` is binary, so it is first capped at the bit length of `g b`. -/
theorem bitGraph_mem_P {encβ : β ↪ List Bool} {g : β → ℕ} (D : Decoder encβ)
    (hg : ComputableInPolyTime g encβ encNat) : bitGraph encβ g ∈ P encBits := by
  classical
  let D' := D.pair Decoder.nat
  have hdec : ComputableInPolyTime D'.decode encBits (encPair encβ encNat) :=
    D'.computableInPolyTime
  have hval : ComputableInPolyTime (fun w => g (D'.decode w).1) encBits encNat :=
    hg.comp hdec.fst'
  have hidx : ComputableInPolyTime (fun w => min (g (D'.decode w).1).size (D'.decode w).2)
      encBits encUnary :=
    ComputableInPolyTime.binary_min_unary' (ComputableInPolyTime.binary_size.comp hval) hdec.snd'
  have hbit := ComputableInPolyTime.binary_testBit hval hidx
  refine ⟨fun w => decide (encPair encβ encNat (D'.decode w) = w) &&
    (g (D'.decode w).1).testBit (min (g (D'.decode w).1).size (D'.decode w).2),
    (hdec.encoding_comp.decide_eq' .id').bool_and' hbit, fun w => ?_⟩
  have hmin (n i : ℕ) : n.testBit (min n.size i) = n.testBit i := by
    rcases le_total i n.size with h | h
    · rw [min_eq_right h]
    · rw [min_eq_left h, Nat.testBit_eq_false_of_lt (Nat.lt_size_self n),
        Nat.testBit_eq_false_of_lt ((Nat.lt_size_self n).trans_le
          (Nat.pow_le_pow_right two_pos h))]
  simp only [hmin, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [D'.decode_enc]
    exact ⟨rfl, hx⟩
  · rintro ⟨hw, hbit⟩
    exact ⟨D'.decode w, hbit, hw⟩

open Classical in
/-- **`P^#P`** [Arora and Barak, Chapter 17][AroraBarak09]: the problems `L` such that, for some
type `β` with encoding `encβ` and some `f ∈ SharpP encβ`, one deterministic oracle program, strict
oracle PPT on the encoding `enc` of instances, decides `L` against every oracle language answering
the bits of `f`. Answers on words that are not codes are arbitrary. -/
def PWithSharpPOracle (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ (β : Type) (encβ : β ↪ List Bool) (f : β → ℕ), f ∈ SharpP encβ ∧
    PolyTimeOracleProgram enc encBool (AnswersBits encβ f) (fun g => ∀ a, a ∈ L ↔ g a = true)}

variable {enc : α ↪ List Bool} {L : Set α}

/-- **`P^#P` lies in polynomial time relative to a `#P` bit graph**: against the bit graph of its
function, the program of a problem in `P^#P` decides it. -/
theorem mem_PWithOracle_bitGraph (hL : L ∈ PWithSharpPOracle enc) :
    ∃ (β : Type) (encβ : β ↪ List Bool) (f : β → ℕ), f ∈ SharpP encβ ∧
      L ∈ PWithOracle (bitGraph encβ f) enc := by
  classical
  obtain ⟨β, encβ, f, hf, hL⟩ := hL
  exact ⟨β, encβ, f, hf, hL.exists_computableInPolyTimeWithOracle (answersBits_bitGraph encβ f)⟩

/-- **`P ⊆ P^#P`**: a polynomial-time decider makes no query. -/
theorem P_subset_PWithSharpPOracle : P enc ⊆ PWithSharpPOracle enc := by
  rintro L ⟨g, hg, hL⟩
  exact ⟨α, enc, 0, SharpP.zero_mem, .of_polyTime hg fun _ _ => hL⟩

/-- **One bit of a `#P` value is in `P^#P`**: a problem decided by the bit at a polynomial
position of a function in `#P` on its own instances is in `P^#P`. The program asks for that bit,
with one query. -/
theorem mem_PWithSharpPOracle_of_testBit {f : α → ℕ} (hf : f ∈ SharpP enc)
    {p : Polynomial ℕ} (h : ∀ a, a ∈ L ↔ (f a).testBit (p.eval (enc a).length)) :
    L ∈ PWithSharpPOracle enc := by
  classical
  have hq : ComputableInPolyTime (fun a => encPair enc encNat (a, p.eval (enc a).length))
      enc encBits :=
    ComputableInPolyTime.encoding_comp (f := fun a => (a, p.eval (enc a).length))
      (ComputableInPolyTime.id'.prod
        (ComputableInPolyTime.unary_to_binary.comp (f := fun n : ℕ => n)
          (g := fun a => p.eval (enc a).length) (by fun_prop)))
  exact ⟨α, enc, f, hf, .of_query hq fun A hA a =>
    (h a).trans ((hA a (p.eval (enc a).length)).symm.trans decide_eq_true_iff.symm)⟩

end Cslib.Complexity
