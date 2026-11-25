/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.SecondPreimageResistant
public import CslibFrontier.Crypto.Computational.TargetCollisionResistant
public import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Target collision resistance from second-preimage resistance (`H(k ⊕ m)`)

Given a hash function `H : List Bool → List Bool`, the XOR-masked keyed family
$$H_{\mathrm{tcr}}(k, m) := H(k \oplus m)$$
([BonehShoup2023], Section 8.11.3, equation (8.18) and Theorem 8.12, pp. 338–339) is target
collision-resistant on `n`-bit messages under uniform `n`-bit keys whenever `H` is second-preimage
resistant on any validity domain `valid` that eventually admits all `n`-bit strings (in particular
Definition 8.6's `{0, 1}ⁿ` domain `validFixedLengthInput` or unrestricted
`SecondPreimageResistant`):

* `validFixedLengthInput n m` checks `decide (m.length = n)`, with plain polynomial-time
  certificate `computableInPolyTime_validFixedLengthInput`.
* `xorTargetHash H n k m = H (BitString.listXor n [k, m])`, with plain polynomial-time certificate
  `computableInPolyTime_xorTargetHash`.
* `xorTargetToSecondPreimage adversary` turns a two-stage `TargetCollisionFinder` into a
  `SecondPreimageFinder` by running `adversary.choose n` to obtain `(m₀, state)`, planting the key
  `k := m ⊕ m₀` on the uniform `n`-bit challenge `m`, running `adversary.find n state k` to obtain
  `m₁`, and returning `m₁ ⊕ k` (`isPPT_xorTargetToSecondPreimage`).
* `succProbability_targetCollisionGame_xorTargetHash_le` proves the concrete reduction bound
  `TCRadv[A, H_tcr] ≤ SPRadvOn[B, H, valid]` at parameter `n` with factor `1` and additive loss
  `0` whenever `valid n` accepts all `n`-bit strings.
* `SecondPreimageResistantOn.targetCollisionResistantOn_xorTargetHash` derives asymptotic
  `TargetCollisionResistantOn id (xorTargetHash H) validFixedLengthInput` from
  `SecondPreimageResistantOn H valid` whenever `valid n` eventually admits all `n`-bit strings.

The restriction to `validFixedLengthInput` (messages of length `n`, matching the book's fixed
domain `M = {0, 1}^n` in equation (8.18)) is essential because `BitString.listXor n` pads or
truncates its inputs to `n` bits: without `validFixedLengthInput`, `m₀ = []` and `m₁ = [false]`
collide under `xorTargetHash H n k` for every `H`, `n`, and `k`. Likewise, `valid n` must admit
`n`-bit words because `xorTargetToSecondPreimage` produces an `n`-bit candidate `m₁ ⊕ k`.

## Main definitions

* `Cslib.Crypto.validFixedLengthInput`: `decide (m.length = n)`.
* `Cslib.Crypto.xorTargetHash`: `H (BitString.listXor n [k, m])`.
* `Cslib.Crypto.xorTargetToSecondPreimage`: reduction from `targetCollisionGame` for
  `xorTargetHash H` to `secondPreimageGameOn H valid`.

## Main results

* `Cslib.Crypto.computableInPolyTime_validFixedLengthInput`,
  `Cslib.Crypto.computableInPolyTime_xorTargetHash`.
* `Cslib.Crypto.isPPT_xorTargetToSecondPreimage`.
* `Cslib.Crypto.succProbability_targetCollisionGame_xorTargetHash_le`.
* `Cslib.Crypto.SecondPreimageResistantOn.targetCollisionResistantOn_xorTargetHash`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 8.11.3 (equation (8.18) and Theorem 8.12, pp. 338–339).
-/

public section

namespace Cslib.Crypto

open ProbComp Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- Validity predicate for `n`-bit messages at security parameter `n`. -/
@[expose]
def validFixedLengthInput (n : ℕ) (m : List Bool) : Bool :=
  decide (m.length = n)

@[simp]
theorem validFixedLengthInput_eq_true_iff {n : ℕ} {m : List Bool} :
    validFixedLengthInput n m = true ↔ m.length = n :=
  decide_eq_true_iff

/-- Testing whether an input has length `n` is computable in plain polynomial time. -/
@[program_certificate]
theorem computableInPolyTime_validFixedLengthInput :
    ComputableInPolyTime
      (fun p : ℕ × List Bool => validFixedLengthInput p.1 p.2)
      (encPair encUnary encBits) encBool :=
  ComputableInPolyTime.id'.snd'.length_bits_comp.decide_eq' ComputableInPolyTime.id'.fst'

/-- The XOR-masked keyed hash family `H_tcr(k, m) = H(k ⊕ m)` of [BonehShoup2023], Section 8.11.3,
equation (8.18), p. 338, at security parameter `n` (where keys and messages have length `n`). -/
@[expose]
def xorTargetHash (H : List Bool → List Bool) (n : ℕ) (k m : List Bool) : List Bool :=
  H (BitString.listXor n [k, m])

@[simp]
theorem xorTargetHash_apply (H : List Bool → List Bool) (n : ℕ) (k m : List Bool) :
    xorTargetHash H n k m = H (BitString.listXor n [k, m]) := rfl

/-- Evaluating `xorTargetHash H` is polynomial-time when `H` is polynomial-time. -/
@[program_certificate]
theorem computableInPolyTime_xorTargetHash {H : List Bool → List Bool}
    (hH : ComputableInPolyTime H encBits encBits) :
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => xorTargetHash H p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits := by
  fun_prop [xorTargetHash]

/-- The second-preimage finder `B` of [BonehShoup2023], Theorem 8.12 (pp. 338–339): given unary
`n` and a uniform `n`-bit input `m`, run `adversary.choose n` to obtain `(m₀, state)`, plant the
key `k := m ⊕ m₀`, run `adversary.find n state k` to obtain `m₁`, and output `m₁ ⊕ k`. -/
@[expose]
noncomputable def xorTargetToSecondPreimage (adversary : TargetCollisionFinder) :
    SecondPreimageFinder := fun n m => do
  let choice ← adversary.choose n
  let k := BitString.listXor n [m, choice.1]
  let m₁ ← adversary.find n choice.2 k
  return BitString.listXor n [m₁, k]

/-- Running both stages of a strict PPT `TargetCollisionFinder` with two `n`-bit XOR operations is
uniformly strict PPT. -/
@[program_certificate]
theorem isPPT_xorTargetToSecondPreimage {adversary : TargetCollisionFinder}
    (ha : adversary.IsPPT) :
    IsPPT encBits (xorTargetToSecondPreimage adversary) := by
  refine IsPPTOn.bind_with (by apply ha.choose.preprocess (prepare := Prod.fst); fun_prop) ?_
  refine IsPPTOn.bind_with
    (by
      apply ha.find.preprocess
        (prepare := fun p : (ℕ × List Bool) × (List Bool × List Bool) =>
          (p.1.1, p.2.2, BitString.listXor p.1.1 [p.1.2, p.2.1]))
      fun_prop) ?_
  apply ComputableInPolyTime.isPPTOn
  fun_prop

/-- **Theorem 8.12, concrete bound** ([BonehShoup2023], Section 8.11.3, pp. 338–339): for every
target-collision adversary `adversary` attacking `xorTargetHash H` on `n`-bit messages and any
second-preimage domain predicate `valid` that accepts all `n`-bit words, the second-preimage finder
`xorTargetToSecondPreimage adversary` wins `secondPreimageGameOn H valid` at least as often as
`adversary` wins `targetCollisionGame`. -/
theorem succProbability_targetCollisionGame_xorTargetHash_le
    (H : List Bool → List Bool) {valid : ℕ → List Bool → Bool} {n : ℕ}
    (hvalid : ∀ w : List Bool, w.length = n → valid n w = true)
    (adversary : TargetCollisionFinder) :
    Game.succProbability
      (ProbComp.eval
        (targetCollisionGame id (xorTargetHash H) validFixedLengthInput adversary n)) ≤
      Game.succProbability
        (ProbComp.eval
          (secondPreimageGameOn H valid (xorTargetToSecondPreimage adversary) n)) := by
  apply Game.succProbability_mono
  have hgame :
      ProbComp.eval (secondPreimageGameOn H valid (xorTargetToSecondPreimage adversary) n) =
        (ProbComp.eval (adversary.choose n)).bind fun choice =>
          (BitString.uniformList n).bind fun k =>
            (ProbComp.eval (adversary.find n choice.2 k)).bind fun m₁ =>
              let m := BitString.listXor n [choice.1, k]
              let m' := BitString.listXor n [m₁, k]
              PMF.pure (valid n m' && ((m' != m) && (H m' == H m))) := by
    simp only [secondPreimageGameOn, xorTargetToSecondPreimage, ProbComp.eval_bind,
      ProbComp.eval_pure, BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind]
    rw [PMF.bind_comm]
    refine PMF.bind_congr_on_support _ _ _ fun choice _ => ?_
    have hmask :
        (BitString.uniformList n).map (fun m => BitString.listXor n [m, choice.1]) =
          BitString.uniformList n :=
      BitString.uniformList_map_listXor n choice.1
    conv_rhs => rw [← hmask, PMF.bind_map]
    refine PMF.bind_congr_on_support _ _ _ fun m hm => ?_
    have hm_len : m.length = n := BitString.mem_support_uniformList_iff.mp hm
    have hrec : BitString.listXor n [choice.1, BitString.listXor n [m, choice.1]] = m := by
      rw [BitString.listXor_pair_comm n m choice.1,
        BitString.listXor_pair_self_left_of_length choice.1 hm_len]
    dsimp only [Function.comp_def]
    simp only [hrec]
  rw [hgame]
  simp only [targetCollisionGame, id_eq, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList]
  refine PMF.bind_apply_mono_on_support _ _ fun choice _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun k _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun m₁ _ => ?_
  cases hcol : isCollision (xorTargetHash H n) validFixedLengthInput n k choice.1 m₁
  · simp
  · rw [isCollision_eq_true_iff] at hcol
    obtain ⟨hm₀_len, hm₁_len, hne, hH⟩ := hcol
    rw [validFixedLengthInput_eq_true_iff] at hm₀_len hm₁_len
    simp only [xorTargetHash, BitString.listXor_pair_comm n k] at hH
    have hne' : BitString.listXor n [m₁, k] ≠ BitString.listXor n [choice.1, k] :=
      fun heq => hne ((BitString.listXor_pair_left_inj hm₁_len hm₀_len k).mp heq).symm
    have hv' : valid n (BitString.listXor n [m₁, k]) = true :=
      hvalid _ (BitString.length_listXor n [m₁, k])
    simp [hv', hne', hH.symm]

/-- **Theorem 8.12** ([BonehShoup2023], Section 8.11.3, p. 338): if `H` is second-preimage
resistant on a domain `valid` that eventually admits all `n`-bit words (in particular
Definition 8.6's `{0, 1}ⁿ` domain `validFixedLengthInput` or unrestricted
`SecondPreimageResistant`), then `H_tcr(k, m) = H(k ⊕ m)` is target collision-resistant on `n`-bit
messages under uniform `n`-bit keys. -/
theorem SecondPreimageResistantOn.targetCollisionResistantOn_xorTargetHash
    {H : List Bool → List Bool} {valid : ℕ → List Bool → Bool}
    (hH : SecondPreimageResistantOn H valid)
    (hvalid : ∀ᶠ n in Filter.atTop, ∀ w : List Bool, w.length = n → valid n w = true) :
    TargetCollisionResistantOn id (xorTargetHash H) validFixedLengthInput := by
  refine TargetCollisionResistantOn.of_negligible fun adversary hadversary => ?_
  refine negligible_of_eventually_le
    (hH.negligible (xorTargetToSecondPreimage adversary)
      (isPPT_xorTargetToSecondPreimage hadversary)) ?_
  filter_upwards [hvalid] with n hvn
  exact succProbability_targetCollisionGame_xorTargetHash_le H hvn adversary

end Cslib.Crypto
