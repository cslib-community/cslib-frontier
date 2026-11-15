/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Parity
public import CslibFrontier.Languages.Probabilistic.Plurality
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.Event

/-!
# Linear cryptanalysis by majority vote

A block cipher `E : BitString h → BitString n → BitString n` satisfies a linear relation for masks
`(S₀, S₁, S₂)` and bias `ε` ([BonehShoup2023], Section 4.3.1, eq. (4.14)) when for every key
`k : BitString h`, the parity relation `parityOn S₀ m ^^ parityOn S₁ (E k m) = parityOn S₂ k` holds
with probability at least `1 / 2 + ε` over uniform plaintexts `m : BitString n`. Evaluating
`linearKeyBitEstimate` on `t` independent uniform plaintext/ciphertext pairs recovers
`parityOn S₂ k` with probability at least `1 - Real.exp (-2 * t * ε ^ 2)`
(`HasLinearRelation.prob_linearKeyBitEstimate_ge`), strengthening the printed bound
`1 - Real.exp (-(t * ε ^ 2 / 2))` of Lemma 4.3 / eq. (4.15).

Boneh–Shoup defines `Majority` only when `t` is odd. Here `linearKeyBitEstimate` uses
`Cslib.ProbComp.plurality false`, which coincides with `Majority` on all odd `t` (and whenever one
bit has strictly more than `t / 2` votes), and resolves ties in favor of the earliest vote achieving
the maximum count (returning `false` when `t = 0`). The non-negativity hypothesis `0 ≤ ε` is a
premise of `HasLinearRelation.prob_linearKeyBitEstimate_ge` rather than part of `HasLinearRelation`.
This module models only the estimator function and its recovery probability, making no running-time
or query-cost claim and recovering only the single key parity bit `parityOn S₂ k`.

## Main definitions

* `Cslib.Crypto.LinearCryptanalysis.HasLinearRelation`: linear approximation condition (4.14).
* `Cslib.Crypto.LinearCryptanalysis.linearKeyBitEstimate`: majority-vote estimator for
  `parityOn S₂ k`.

## Main results

* `Cslib.Crypto.LinearCryptanalysis.HasLinearRelation.prob_linearKeyBitEstimate_ge`: recovery lower
  bound `1 - Real.exp (-2 * t * ε ^ 2)` (strengthening Boneh–Shoup Lemma 4.3 / eq. (4.15)).

## References

* [BonehShoup2023] D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6,
  Section 4.3.1, eqs. (4.14)–(4.15) and Lemma 4.3, pp. 123–124.
-/

public section

namespace Cslib.Crypto.LinearCryptanalysis

open Cslib.Probability

/-- A block cipher `E : BitString h → BitString n → BitString n` satisfies a linear relation with
masks `(S₀, S₁, S₂)` and bias `ε` ([BonehShoup2023], Section 4.3.1, eq. (4.14)) if for every key
`k : BitString h`, `parityOn S₀ m ^^ parityOn S₁ (E k m) = parityOn S₂ k` holds for at least
`1 / 2 + ε` of plaintexts `m : BitString n`. -/
@[expose]
def HasLinearRelation {h n : ℕ} (E : BitString h → BitString n → BitString n)
    (S₀ S₁ : Finset (Fin n)) (S₂ : Finset (Fin h)) (ε : ℝ) : Prop :=
  ∀ k : BitString h,
    1 / 2 + ε ≤ ((Probability.PMF.uniformOfFintype (BitString n)).toOuterMeasure
      {m : BitString n | (parityOn S₀ m ^^ parityOn S₁ (E k m)) = parityOn S₂ k}).toReal

/-- Majority-vote estimator for the key parity bit `parityOn S₂ k` from `t` plaintext/ciphertext
pairs, implemented with `Cslib.ProbComp.plurality false`. It agrees with Boneh–Shoup's
`Majority` for odd `t` and breaks ties in favor of the earliest maximally frequent vote (`false`
for `t = 0`). -/
@[expose]
def linearKeyBitEstimate {n t : ℕ} (S₀ S₁ : Finset (Fin n))
    (pairs : Fin t → BitString n × BitString n) : Bool :=
  ProbComp.plurality false
    (List.ofFn fun i => parityOn S₀ (pairs i).1 ^^ parityOn S₁ (pairs i).2)

/-- **Linear cryptanalysis key-bit recovery** ([BonehShoup2023], Section 4.3.1, Lemma 4.3 /
eq. (4.15), sharpened with Hoeffding exponent `-2 * t * ε ^ 2`). When `0 ≤ ε`,
`linearKeyBitEstimate` on `t` independent uniform plaintext/ciphertext pairs recovers
`parityOn S₂ k` with probability at least `1 - Real.exp (-2 * t * ε ^ 2)`, implying the printed
bound `1 - Real.exp (-(t * ε ^ 2 / 2))`. -/
theorem HasLinearRelation.prob_linearKeyBitEstimate_ge {h n : ℕ}
    {E : BitString h → BitString n → BitString n} {S₀ S₁ : Finset (Fin n)}
    {S₂ : Finset (Fin h)} {ε : ℝ} (hrel : HasLinearRelation E S₀ S₁ S₂ ε) (hε : 0 ≤ ε)
    (k : BitString h) (t : ℕ) :
    1 - Real.exp (-2 * t * ε ^ 2) ≤
      ((Probability.PMF.uniformOfFintype (Fin t → BitString n)).toOuterMeasure
        {m : Fin t → BitString n |
          linearKeyBitEstimate S₀ S₁ (fun i => (m i, E k (m i))) = parityOn S₂ k}).toReal := by
  let vote : BitString n → Bool := fun m => parityOn S₀ m ^^ parityOn S₁ (E k m)
  let program : ProbComp Bool := vote <$> ProbComp.uniform (BitString n)
  have hlaw :
      ProbComp.eval program = (Probability.PMF.uniformOfFintype (BitString n)).map vote := by
    simp only [program, ProbComp.eval_map, ProbComp.eval_uniform]
  have hp : 1 / 2 + ε ≤ (ProbComp.eval program (parityOn S₂ k)).toReal := by
    rw [hlaw, ← _root_.PMF.toOuterMeasure_apply_singleton, _root_.PMF.toOuterMeasure_map_apply]
    exact hrel k
  have hmain := ProbComp.one_sub_exp_le_eval_plurality_replicate_toReal false (parityOn S₂ k) t
    program hε hp
  rw [ProbComp.eval_map, ProbComp.eval_replicate_of_uniform t program vote hlaw,
    _root_.PMF.map_comp, ← _root_.PMF.toOuterMeasure_apply_singleton,
    _root_.PMF.toOuterMeasure_map_apply] at hmain
  exact hmain

end Cslib.Crypto.LinearCryptanalysis
