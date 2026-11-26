/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SharpFormula
public import CslibFrontier.Computability.Complexity.Problems.SharpSAT
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Combinators
public import CslibFrontier.Computability.Complexity.Classes.Toda.Counting
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Complexity.CookLevin.Counting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# From parity to counts modulo `2 ^ (m + 1)` by a formula transformation

[Arora and Barak, draft Lemma 9.19, printed p. 183 / PDF p. 199][AroraBarak07]: a deterministic
polynomial-time transformation `T` takes an input `ψ` of `⊕SAT` and `1 ^ m` to an unquantified
Boolean formula `T (ψ, 1 ^ m)` whose number of satisfying assignments is `-1` modulo `2 ^ (m + 1)`
when `ψ ∈ ⊕SAT` and `0` modulo `2 ^ (m + 1)` otherwise
(`Cslib.Complexity.Toda.exists_formulaAmplification`).

## Statement-to-source mapping

* The draft's inputs of `⊕SAT` (Definition 9.14) are unquantified Boolean formulas, not
  necessarily in CNF. Here they are the quantifier-free formulas `QBF ℕ`, encoded by `encQBF`, and
  `ψ ∈ ⊕SAT` is `Odd ψ.modelCount`: an odd number of assignments of the free variables of `ψ`
  satisfy it (`Cslib.Logic.PL.QBF.modelCount`).
* `1 ^ m` is `m` in unary (`encUnary`), paired with `ψ` by `encPair`.
* The output is a formula in conjunctive normal form, a special case of an unquantified Boolean
  formula, and `#(T (ψ, 1 ^ m))` is `Cslib.Complexity.SharpSAT`, the number of assignments of its
  occurring variables that satisfy it. The congruences are equations in `ZMod (2 ^ (m + 1))`.
* The draft's display writes `#(ϕ)` for the output; it is read as `#(T (ψ, 1 ^ m))`.

## Proof

The proof does not iterate the draft's `ψ ↦ 4 ψ ^ 3 + 3 ψ ^ 4`. It uses the binomial amplifier of
`CslibFrontier.Computability.Complexity.Classes.Toda.Counting`, which already makes a count that
is `1` or `0` modulo `2 ^ K` for an odd or even count `#ψ`
(`Cslib.Complexity.Toda.cast_card_filter_countingTest`, with no random string and `K = m + 1`).
Multiplying by the `2 ^ K - 1` nonzero words of `K` bits gives `-1` or `0`. The counting verifier
of Boolean formulas (`Cslib.Complexity.SharpFormula.verifier`) supplies the witnesses of `ψ`, so
the product is a function in `#P` of `(ψ, m)`. The parsimonious Cook–Levin reduction
(`Cslib.Complexity.CookLevin.SharpSAT_sharpPHard`) turns it into a polynomial-time map to CNF
formulas with exactly that many satisfying assignments.

The draft's auxiliary sum `ϕ + ψ` on `max {n, m} + 1` variables is not used. As printed it counts
`2 ^ (max {n, m} - n) #ϕ + 2 ^ (max {n, m} - m) #ψ`, not `#ϕ + #ψ`, when `n ≠ m`, and
`4 τ ^ 3 + 3 τ ^ 4` adds formulas with different numbers of variables. It is not a numbered result.

## Main definitions

* `Cslib.Complexity.Toda.amplifyVerifier`: the verifier of the amplified count.

## Main results

* `Cslib.Complexity.Toda.cast_acceptCount_amplifyVerifier`: the amplified count is `-1` or `0`.
* `Cslib.Complexity.Toda.exists_formulaAmplification`: **Lemma 9.19**.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft][AroraBarak07]
* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
-/

public section

namespace Cslib.Complexity.Toda

open Finset Cslib.Logic.PL Turing.MultiTapeTM

/-- **The verifier of the amplified count** on `(ψ, m)`, with `K = m + 1`: a word of `K` bits not
all `false`, followed by a word of the counting test with sizes up to `K`, no random string, and
rows of `|distinctFreeVars ψ|` bits holding assignments of `ψ`. -/
@[expose] def amplifyVerifier : (QBF ℕ × ℕ) × List Bool → Bool :=
  andVerifier (fun a => a.2 + 1) (fun y => !allFalseVerifier y) <| Function.uncurry fun a w =>
    countingTest (fun _ z => SharpFormula.verifier (a.1, z)) (a.2 + 1) 0
      a.1.distinctFreeVars.length w

/-- The length of the words of `amplifyVerifier`. -/
@[expose] def amplifyLength (a : QBF ℕ × ℕ) : ℕ :=
  (a.2 + 1) + ((a.2 + 1) + ((a.2 + 1) + (0 + (a.2 + 1) * a.1.distinctFreeVars.length)))

/-- **The amplified count is `-1` or `0`** modulo `2 ^ (m + 1)`, as `#ψ` is odd or even. -/
theorem cast_acceptCount_amplifyVerifier {ψ : QBF ℕ} (hψ : ψ.QuantifierFree) (m : ℕ) :
    (acceptCount amplifyVerifier (ψ, m) (amplifyLength (ψ, m)) : ZMod (2 ^ (m + 1))) =
      if Odd ψ.modelCount then -1 else 0 := by
  classical
  -- the nonzero words
  have hnz : acceptCount (fun y => !allFalseVerifier y) (ψ, m) (m + 1) = 2 ^ (m + 1) - 1 := by
    have := acceptCount_add_acceptCount_not allFalseVerifier (ψ, m) (m + 1)
    rw [acceptCount_allFalseVerifier] at this
    omega
  -- the counting test
  have hcount : (acceptCount (Function.uncurry fun (a : QBF ℕ × ℕ) w =>
      countingTest (fun _ z => SharpFormula.verifier (a.1, z)) (a.2 + 1) 0
        a.1.distinctFreeVars.length w) (ψ, m)
        ((m + 1) + ((m + 1) + (0 + (m + 1) * ψ.distinctFreeVars.length))) :
          ZMod (2 ^ (m + 1))) = if Odd ψ.modelCount then 1 else 0 := by
    have h := cast_card_filter_countingTest (fun _ z => SharpFormula.verifier (ψ, z)) (m + 1) 0
      ψ.distinctFreeVars.length
    have hZ : (univ.filter fun z : Fin ψ.distinctFreeVars.length → Bool =>
        SharpFormula.verifier (ψ, List.ofFn z) = true).card = ψ.modelCount :=
      SharpFormula.acceptCount_verifier hψ
    simp only [hZ] at h
    change ((univ.filter fun w : Fin ((m + 1) + ((m + 1) + (0 + (m + 1) *
      ψ.distinctFreeVars.length))) → Bool => countingTest (fun _ z => SharpFormula.verifier (ψ, z))
        (m + 1) 0 ψ.distinctFreeVars.length (List.ofFn w) = true).card : ZMod (2 ^ (m + 1))) = _
    rw [h]
    by_cases ho : Odd ψ.modelCount <;> simp [ho]
  have hpos : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  rw [amplifyLength, amplifyVerifier, acceptCount_andVerifier, Nat.cast_mul, hnz, hcount,
    Nat.cast_sub hpos, ZMod.natCast_self, Nat.cast_one]
  split <;> simp

/-- The amplified count is a function in `#P` of `(ψ, m)`, after padding the words to a polynomial
of the length of the encoded pair. -/
private theorem amplifyCount_mem_SharpP :
    (fun a => acceptCount amplifyVerifier a (amplifyLength a)) ∈
      SharpP (encPair encQBF encUnary) := by
  set p : Polynomial ℕ := 4 * (Polynomial.X + 1) * (Polynomial.X + 1)
  refine ⟨p, padVerifier amplifyLength amplifyVerifier, ?_, fun a => ?_⟩
  · have hF : ComputableInPolyTime (fun x : (QBF ℕ × List Bool) × List Bool =>
        SharpFormula.verifier (x.1.1, x.2)) (encPair (encPair encQBF encBits) encBits) encBool := by
      fun_prop
    have hC : ComputableInPolyTime (fun y : (QBF ℕ × ℕ) × List Bool =>
        countingTest (fun r z => (fun x : (QBF ℕ × List Bool) × List Bool =>
          SharpFormula.verifier (x.1.1, x.2)) ((y.1.1, r), z)) (y.1.2 + 1) 0
          y.1.1.distinctFreeVars.length y.2)
        (encPair (encPair encQBF encUnary) encBits) encBool :=
      computableInPolyTime_countingTest hF (by fun_prop) (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop)
    have hV : ComputableInPolyTime amplifyVerifier
        (encPair (encPair encQBF encUnary) encBits) encBool :=
      computableInPolyTime_andVerifier (by fun_prop) (by fun_prop) hC
    have hL : ComputableInPolyTime amplifyLength (encPair encQBF encUnary) encUnary := by
      unfold amplifyLength
      fun_prop
    fun_prop
  · refine (acceptCount_padVerifier_of_le _ _ ?_).symm
    have hm := length_le_encPair_right encQBF encUnary a
    have hZ := QBF.three_mul_length_distinctFreeVars_le a.1
    have hQ := length_le_encPair_left encQBF encUnary a
    simp only [encUnary_apply, List.length_replicate] at hm
    simp only [amplifyLength, p, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_ofNat]
    nlinarith

/-- **Arora–Barak, draft Lemma 9.19.** There is a deterministic polynomial-time transformation
`T` from a Boolean formula `ψ` and `1 ^ m` to an unquantified (CNF) formula such that for every
quantifier-free `ψ`, the number of satisfying assignments of `T (ψ, 1 ^ m)` is `-1` modulo
`2 ^ (m + 1)` when `ψ ∈ ⊕SAT` (an odd number of satisfying assignments) and `0` modulo
`2 ^ (m + 1)` when `ψ ∉ ⊕SAT`. -/
theorem exists_formulaAmplification :
    ∃ T : QBF ℕ × ℕ → CNF ℕ, ComputableInPolyTime T (encPair encQBF encUnary) encCNF ∧
      ∀ ψ : QBF ℕ, ψ.QuantifierFree → ∀ m : ℕ,
        (Odd ψ.modelCount → (SharpSAT (T (ψ, m)) : ZMod (2 ^ (m + 1))) = -1) ∧
        (¬Odd ψ.modelCount → (SharpSAT (T (ψ, m)) : ZMod (2 ^ (m + 1))) = 0) := by
  obtain ⟨T, hT, hcount⟩ := CookLevin.SharpSAT_sharpPHard _ _ amplifyCount_mem_SharpP
  refine ⟨T, hT, fun ψ hψ m => ?_⟩
  have h := cast_acceptCount_amplifyVerifier hψ m
  rw [show acceptCount amplifyVerifier (ψ, m) (amplifyLength (ψ, m)) = _ from hcount (ψ, m)] at h
  exact ⟨fun ho => by simpa [ho] using h, fun he => by simpa [he] using h⟩

end Cslib.Complexity.Toda
