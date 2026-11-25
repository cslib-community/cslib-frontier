/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.Amplify
public import CslibFrontier.Crypto.Computational.ShoupComposition
public import CslibFrontier.Crypto.Computational.TargetCollisionResistant
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PadicVal
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool

/-!
# Target collision-resistant hashing from inaccessible entropy and one-way functions

Completing the construction of universal one-way hash families (target collision-resistant hash
families) from arbitrary one-way functions (`[Rompel1990]`; `[Shoup2000]`; `[HHRVW2020]`,
Section 5.1, Theorem 5.1, STEPS 4–5, Lemmas 5.6 and 5.7, pp. 29–32):

1. **Target shift (`rompelShiftedStep`; `[HHRVW2020]`, Section 5.1.4, Lemma 5.6, pp. 29–30, and
   Section 5.1.5, STEP 4, p. 31)**:
   given a `ShrinkingCollisionGrid` `G` whose `gridCount n` candidates compress `G.inLen n =
   G.outLen n + G.shrinkLen n` bits to `G.outLen n` bits (with `G.shrinkLen n = Nat.log 2 n + 1`
   on the canonical grid `AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid_log`),
   shifting the input of candidate `q` by a `G.inLen n`-bit key mask `y` via
   `w ↦ G.evalGrid n q (listXor (G.inLen n) [w, y])` converts random-input collision resistance at
   `q = goodIdx n` into keyed target collision resistance on `G.inLen n`-bit inputs.
2. **Shoup `O(|y| log t)` XOR-masking cascade and candidate concatenation (`rompelCandidateEval`,
   `rompelCompressionEval`, `rompelCompression`, `rompelKeyLen_le`; `[Shoup2000]`;
   `[HHRVW2020]`, Section 5.1.4, Lemma 5.7, p. 30, and Section 5.1.5, STEP 5(ii–iii), p. 32)**:
   instantiating `ShoupComposition.shoupComposeEval` with `rompelShiftedStep` over
   `rompelCascadeSteps G n = ⌈(2 * G.gridCount n - 1) * G.outLen n / G.shrinkLen n⌉` steps
   compresses `2 * rompelBlockLen G n` bits to `G.outLen n` bits for each `q < G.gridCount n`, and
   concatenating all `G.gridCount n` candidate outputs produces a halving `KeyedCompressionFamily`
   (`rompelCompression G`) with block width `rompelBlockLen G n = G.gridCount n * G.outLen n`.
   - **Key length (`rompelKeyLen_le`)**: the shared key `K = y ++ masks` has bit-length
     `rompelKeyLen G n = G.inLen n + (Nat.log 2 (rompelCascadeSteps G n) + 1) * G.outLen n ≤
     (Nat.log 2 (rompelCascadeSteps G n) + 2) * G.inLen n`, matching `[HHRVW2020]` Lemma 5.7's
     `O(|y| log t)` bound directly on `rompelCompression G`.
   - **Shared key across candidates vs. `[HHRVW2020]` STEP 5(iii)**: sharing one Shoup key
     `K = (y, M₀, …, M_d)` across all `G.gridCount n` candidate rows suffices for every security,
     PPT, key-length, and domain-extension claim in the library because for each strict PPT
     adversary `adv`, `G.exists_good_candidate` supplies one index `goodIdx n`, so
     `rompelCompressionInverter G adv` only needs faithful key simulation at `goodIdx n`. Sharing
     `K` achieves the same multiplicative reduction loss `dyadicSize (G.gridCount n) *
     dyadicSize (rompelCascadeSteps G n)` with `G.gridCount n`-times shorter keys than
     per-candidate keys.
3. **Modular reduction via `ShoupComposition` (`rompelCompressionInverter`,
   `succProbability_targetCollisionGame_rompelCompression_le`,
   `ShrinkingCollisionGrid.targetCollisionResistant_rompelCompression`)**:
   projecting `rompelCompressionEval` onto row `qStar` (`listRow_rompelCompressionEval`) reduces
   collisions on `rompelCompression G` to `rompelCandidateEval G · qStar`, where
   `succProbability_targetCollisionGame_shoupCompose_le` reduces `rompelCascadeSteps G n` steps to
   a single call to `rompelShiftedStep G · qStar` with loss `dyadicSize (rompelCascadeSteps G n)`.
   Guessing `qGuess` via `sampleDyadicIndex (G.gridCount n)` and XOR-shifting the uniform challenge
   `zWord` against `shoupComposeChoose`'s target `w₀` (`yStar := zWord ⊕ w₀`) completes Lemma 5.6's
   1-step reduction to `randomCollisionGame` with total loss
   `dyadicSize (G.gridCount n) * dyadicSize (rompelCascadeSteps G n)` and zero additive error.
4. **Domain extension to `List Bool` (`rompelHash`,
   `ShrinkingCollisionGrid.targetCollisionResistant_rompelHash`,
   `AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantHash`,
   `OneWay.exists_targetCollisionResistant_keyedHashFamily`)**:
   composing `rompelCompression G` with `KeyedCompressionFamily.treeHash` (`uowhfTreeHash`) yields
   an unrestricted computational target collision-resistant `KeyedHashFamily` on `List Bool` from
   any uniform `OneWay` function, establishing the qualitative polynomial-time target
   collision-resistance part of `[HHRVW2020]` Theorem 5.1 (with dense two-universal matrices in
   `EntropyReduction` and `(n + 1)`-level `treeHash` in `rompelHash`).

## Main definitions

* `Cslib.Crypto.rompelShiftedStep`: XOR-masked `G.shrinkLen n`-bit shrinking candidate step
  (Lemma 5.6, STEP 4).
* `Cslib.Crypto.rompelCascadeSteps`, `Cslib.Crypto.rompelBlockLen`, `Cslib.Crypto.rompelKeyLen`:
  step, block, and shared `O(|y| log t)` key-length schedules for `rompelCompression`.
* `Cslib.Crypto.rompelCandidateEval`, `Cslib.Crypto.rompelCascadeInput`: Shoup XOR-masked
  `G.shrinkLen n`-bit shrinking cascade and step-`i` compression-input extractor (`[Shoup2000]`;
  `[HHRVW2020]`, Lemma 5.7, STEP 5(ii)).
* `Cslib.Crypto.rompelCompressionEval`, `Cslib.Crypto.rompelCompression`: `gridCount n`-way
  concatenated `2 * rompelBlockLen G n → rompelBlockLen G n` `KeyedCompressionFamily` (adapting
  STEP 5(iii) with shared Shoup key).
* `Cslib.Crypto.rompelCompressionInverter`: uniform strict-PPT reduction from target collisions of
  `rompelCompression G` to `randomCollisionGame` on `G`, built from `shoupComposeChoose` and
  `shoupComposeFindWith`.
* `Cslib.Crypto.rompelHash`: unrestricted `KeyedHashFamily` `(rompelCompression G).treeHash`.

## Main results

* `Cslib.Crypto.rompelKeyLen_le`, `Cslib.Crypto.ShrinkingCollisionGrid.rompelCompression_keyLen_le`:
  explicit `O(|y| log t)` key-length bound `(Nat.log 2 (rompelCascadeSteps G n) + 2) * G.inLen n`
  for `rompelCompression G`.
* `Cslib.Crypto.exists_rompelCascadeInput_collision`: deterministic extraction of a step collision
  `1 ≤ i ≤ rompelCascadeSteps G n` from any `2 * rompelBlockLen G n`-bit collision of candidate `q`.
* `Cslib.Crypto.isPPT_rompelCompressionInverter`: uniform strict-PPT certificate for
  `rompelCompressionInverter`.
* `Cslib.Crypto.succProbability_targetCollisionGame_rompelCompression_le`: concrete security bound
  against `randomCollisionGame` at any candidate `qStar < G.gridCount n`.
* `Cslib.Crypto.ShrinkingCollisionGrid.targetCollisionResistant_rompelCompression`,
  `Cslib.Crypto.ShrinkingCollisionGrid.targetCollisionResistant_rompelHash`: target collision
  resistance of `rompelCompression G` and `rompelHash G`.
* `Cslib.Crypto.AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid_rompelCompression`,
  `Cslib.Crypto.OneWay.exists_shrinkingCollisionGrid_rompelCompression`: end-to-end compression
  theorems preserving `G.shrinkLen n = Nat.log 2 n + 1` and `rompelCompression_keyLen_le`.
* `Cslib.Crypto.AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantCompression`,
  `Cslib.Crypto.AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantHash`,
  `Cslib.Crypto.OneWay.exists_targetCollisionResistant_keyedCompressionFamily`,
  `Cslib.Crypto.OneWay.exists_targetCollisionResistant_keyedHashFamily`: qualitative Theorem 5.1
  existence endpoints from Definition 3.9 and from `OneWay`.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Sections 5.1.4–5.1.5, Theorem 5.1, Lemmas 5.6–5.7,
  pp. 29–32][HHRVW2020]
* [V. Shoup, *A Composition Theorem for Universal One-Way Hash Functions*, EUROCRYPT 2000,
  LNCS 1807, pp. 445–452][Shoup2000]
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990]
-/

public section

namespace Cslib.Crypto

open ProbComp Cslib.Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Schedules and XOR-shifted `G.shrinkLen n`-bit shrinking step (Lemma 5.6, STEP 4) -/

/-- Number of `G.shrinkLen n`-bit cascade steps `((2 * G.gridCount n - 1) * G.outLen n +
G.shrinkLen n - 1) / G.shrinkLen n` used by each candidate in `rompelCompression G`
(`[HHRVW2020]`, Section 5.1.5, STEP 5(ii), p. 32). -/
def rompelCascadeSteps (G : ShrinkingCollisionGrid) (n : ℕ) : ℕ :=
  ((2 * G.gridCount n - 1) * G.outLen n + G.shrinkLen n - 1) / G.shrinkLen n

/-- Output (and half-input) block width `G.gridCount n * G.outLen n` of `rompelCompression G`
(`[HHRVW2020]`, Section 5.1.5, STEP 5(iii), p. 32). -/
@[expose]
def rompelBlockLen (G : ShrinkingCollisionGrid) (n : ℕ) : ℕ :=
  G.gridCount n * G.outLen n

/-- Shared Shoup `O(|y| log t)` key bit-length
`G.inLen n + (Nat.log 2 (rompelCascadeSteps G n) + 1) * G.outLen n` of `rompelCompression G`
(`[Shoup2000]`; `[HHRVW2020]`, Section 5.1.4, Lemma 5.7, p. 30). -/
@[expose]
def rompelKeyLen (G : ShrinkingCollisionGrid) (n : ℕ) : ℕ :=
  shoupComposeKeyLen G.inLen G.outLen (rompelCascadeSteps G) n

theorem rompelKeyLen_eq (G : ShrinkingCollisionGrid) (n : ℕ) :
    rompelKeyLen G n = G.inLen n + (Nat.log 2 (rompelCascadeSteps G n) + 1) * G.outLen n :=
  rfl

/-- **`[HHRVW2020]` Lemma 5.7 `O(|y| log t)` key-length bound**:
`rompelKeyLen G n ≤ (Nat.log 2 (rompelCascadeSteps G n) + 2) * G.inLen n`. -/
theorem rompelKeyLen_le (G : ShrinkingCollisionGrid) (n : ℕ) :
    rompelKeyLen G n ≤ (Nat.log 2 (rompelCascadeSteps G n) + 2) * G.inLen n :=
  shoupComposeKeyLen_le (by have := G.outLen_add_shrink n; omega)

theorem rompelCascadeSteps_pos (G : ShrinkingCollisionGrid) (n : ℕ) :
    1 ≤ rompelCascadeSteps G n := by
  have hk := G.gridCount_pos n
  have hout := G.le_outLen n
  have hs := G.shrinkLen_pos n
  have := Nat.mul_pos (by omega : 0 < 2 * G.gridCount n - 1) (by omega : 0 < G.outLen n)
  unfold rompelCascadeSteps
  exact Nat.div_pos (by omega) hs

private theorem outLen_le_rompelBlockLen (G : ShrinkingCollisionGrid) (n : ℕ) :
    G.outLen n ≤ rompelBlockLen G n :=
  Nat.le_mul_of_pos_left _ (G.gridCount_pos n)

private theorem outLen_le_two_mul_rompelBlockLen (G : ShrinkingCollisionGrid) (n : ℕ) :
    G.outLen n ≤ 2 * rompelBlockLen G n :=
  (outLen_le_rompelBlockLen G n).trans (Nat.le_mul_of_pos_left _ zero_lt_two)

theorem two_mul_rompelBlockLen_le (G : ShrinkingCollisionGrid) (n : ℕ) :
    2 * rompelBlockLen G n ≤ G.outLen n + rompelCascadeSteps G n * G.shrinkLen n := by
  have hk := G.gridCount_pos n
  have hs := G.shrinkLen_pos n
  have hprod := Nat.mul_pos (by omega : 0 < 2 * G.gridCount n - 1)
    (by have := G.le_outLen n; omega : 0 < G.outLen n)
  have hdiv := Nat.div_add_mod ((2 * G.gridCount n - 1) * G.outLen n + G.shrinkLen n - 1)
    (G.shrinkLen n)
  have hmod := Nat.mod_lt ((2 * G.gridCount n - 1) * G.outLen n + G.shrinkLen n - 1) hs
  have hceil : (2 * G.gridCount n - 1) * G.outLen n ≤ rompelCascadeSteps G n * G.shrinkLen n := by
    unfold rompelCascadeSteps; rw [mul_comm] at hdiv; omega
  rw [rompelBlockLen, ← mul_assoc, show 2 * G.gridCount n = 1 + (2 * G.gridCount n - 1) by omega,
    add_mul, one_mul]
  exact Nat.add_le_add_left hceil _

theorem le_rompelBlockLen (G : ShrinkingCollisionGrid) (n : ℕ) :
    n ≤ rompelBlockLen G n :=
  (Nat.le_succ n).trans ((G.le_outLen n).trans (outLen_le_rompelBlockLen G n))

attribute [local fun_prop] ShrinkingCollisionGrid.polyTime_inLen
  ShrinkingCollisionGrid.polyTime_outLen
  ShrinkingCollisionGrid.polyTime_shrinkLen
  ShrinkingCollisionGrid.polyTime_gridCount

@[fun_prop]
theorem computableInPolyTime_rompelCascadeSteps (G : ShrinkingCollisionGrid) :
    ComputableInPolyTime (rompelCascadeSteps G) encUnary encUnary := by
  unfold rompelCascadeSteps; fun_prop

@[fun_prop]
theorem computableInPolyTime_rompelBlockLen (G : ShrinkingCollisionGrid) :
    ComputableInPolyTime (rompelBlockLen G) encUnary encUnary := by
  unfold rompelBlockLen; fun_prop

@[fun_prop]
theorem computableInPolyTime_rompelKeyLen (G : ShrinkingCollisionGrid) :
    ComputableInPolyTime (rompelKeyLen G) encUnary encUnary :=
  computableInPolyTime_shoupComposeKeyLen G.polyTime_inLen G.polyTime_outLen
    (computableInPolyTime_rompelCascadeSteps G) (ComputableInPolyTime.id' (encIn := encUnary))

/-- **XOR-shifted `G.shrinkLen n`-bit shrinking step** (`[HHRVW2020]`, Section 5.1.4, Lemma 5.6,
pp. 29–30; Section 5.1.5, STEP 4, p. 31): masks `w` by `y` at width `G.inLen n` and evaluates
candidate `q` of `G` (`G.outLen n + G.shrinkLen n = G.inLen n`). -/
@[expose]
def rompelShiftedStep (G : ShrinkingCollisionGrid) (n q : ℕ) (y w : List Bool) : List Bool :=
  G.evalGrid n q (BitString.listXor (G.inLen n) [w, y])

@[simp]
theorem length_rompelShiftedStep (G : ShrinkingCollisionGrid) (n q : ℕ) (y w : List Bool) :
    (rompelShiftedStep G n q y w).length = G.outLen n :=
  G.length_evalGrid n q _

@[fun_prop]
theorem computableInPolyTime_rompelShiftedStep (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n q : γ → ℕ} {y w : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary)
    (hy : ComputableInPolyTime y encIn encBits)
    (hw : ComputableInPolyTime w encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelShiftedStep G (n a) (q a) (y a) (w a))
      encIn encBits :=
  G.polyTime_evalGrid.comp (hn.prod (hq.prod
    (ComputableInPolyTime.bitsXorWithInput (G.polyTime_inLen.comp hn)
      (ComputableInPolyTime.cons' hw
        (ComputableInPolyTime.cons' hy (ComputableInPolyTime.const []))))))

/-! ### Shoup `O(|y| log t)` XOR-masking cascade and step-collision extraction (Lemma 5.7) -/

/-- Candidate-`q` `2 * rompelBlockLen G n → G.outLen n` Shoup XOR-masking cascade evaluator under
compact key `K` (`y := BitString.listRow (G.inLen n) 0 K`, `masks := K.drop (G.inLen n)`). -/
@[expose]
def rompelCandidateEval (G : ShrinkingCollisionGrid) (n q : ℕ) (K x : List Bool) : List Bool :=
  shoupComposeEval G.inLen G.outLen G.shrinkLen (rompelCascadeSteps G)
    (fun m y w => rompelShiftedStep G m q y w) n K x

@[simp]
theorem length_rompelCandidateEval (G : ShrinkingCollisionGrid) (n q : ℕ) (K x : List Bool) :
    (rompelCandidateEval G n q K x).length = G.outLen n :=
  length_shoupComposeEval fun _ _ _ _ => length_rompelShiftedStep G n q _ _

@[fun_prop]
theorem computableInPolyTime_rompelCandidateEval (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n q : γ → ℕ} {K x : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary)
    (hK : ComputableInPolyTime K encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelCandidateEval G (n a) (q a) (K a) (x a))
      encIn encBits := by
  have hin := G.polyTime_inLen.comp hn
  have hy := ComputableInPolyTime.bitsRowWithInput hin (.const 0) hK
  have hp1 := ComputableInPolyTime.fst encIn encBits
  exact computableInPolyTime_shoupCascade (G.polyTime_outLen.comp hn)
    (G.polyTime_shrinkLen.comp hn) ((computableInPolyTime_rompelCascadeSteps G).comp hn)
    (computableInPolyTime_rompelShiftedStep G (hn.comp hp1) (hq.comp hp1) (hy.comp hp1)
      (.snd encIn encBits))
    (fun _ w _ => length_rompelShiftedStep G _ _ _ w)
    (ComputableInPolyTime.bitsDropWithInput hK hin) hx

/-- Step-`i` (`1 ≤ i ≤ rompelCascadeSteps G n`) `G.inLen n`-bit input fed to
`rompelShiftedStep G n q (BitString.listRow (G.inLen n) 0 K)` during
`rompelCandidateEval G n q K x`. -/
@[expose]
def rompelCascadeInput (G : ShrinkingCollisionGrid) (n q i : ℕ) (K x : List Bool) : List Bool :=
  let y := BitString.listRow (G.inLen n) 0 K
  let masks := K.drop (G.inLen n)
  shoupStepInput (G.outLen n) (G.shrinkLen n) masks x i
    (shoupState (G.outLen n) (G.shrinkLen n) (rompelShiftedStep G n q y) masks x (i - 1))

@[simp]
theorem length_rompelCascadeInput (G : ShrinkingCollisionGrid) (n q i : ℕ)
    (K x : List Bool) :
    (rompelCascadeInput G n q i K x).length = G.inLen n := by
  unfold rompelCascadeInput
  rw [length_shoupStepInput, G.outLen_add_shrink n]

@[fun_prop]
theorem computableInPolyTime_rompelCascadeInput (G : ShrinkingCollisionGrid)
    {γ : Type} {encIn : γ ↪ List Bool}
    {n q i : γ → ℕ} {K x : γ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hK : ComputableInPolyTime K encIn encBits)
    (hx : ComputableInPolyTime x encIn encBits) :
    ComputableInPolyTime
      (fun a => rompelCascadeInput G (n a) (q a) (i a) (K a) (x a))
      encIn encBits := by
  have hout := G.polyTime_outLen.comp hn
  have hshrink := G.polyTime_shrinkLen.comp hn
  have hy := ComputableInPolyTime.bitsRowWithInput (G.polyTime_inLen.comp hn) (.const 0) hK
  have hmasks := ComputableInPolyTime.bitsDropWithInput hK (G.polyTime_inLen.comp hn)
  have hp1 := ComputableInPolyTime.fst encIn encBits
  have hstate := computableInPolyTime_shoupState
    (step := fun a w => rompelShiftedStep G (n a) (q a)
      (BitString.listRow (G.inLen (n a)) 0 (K a)) w)
    hout hshrink (hi.unary_sub' (.const 1))
    (computableInPolyTime_rompelShiftedStep G (hn.comp hp1) (hq.comp hp1) (hy.comp hp1)
      (.snd encIn encBits))
    (fun _ w _ => length_rompelShiftedStep G _ _ _ w) hmasks hx
  exact computableInPolyTime_shoupStepInput hout hshrink hmasks hx hi hstate

/-- **Deterministic step-collision extraction (`[Shoup2000]`, `[HHRVW2020]`, Section 5.1.4,
Lemma 5.7, p. 30)**: if two distinct `2 * rompelBlockLen G n`-bit inputs `x₀ ≠ x₁` collide under
`rompelCandidateEval G n q K`, there exists a step `1 ≤ i ≤ rompelCascadeSteps G n` where their
`G.inLen n`-bit step inputs `rompelCascadeInput G n q i K` are distinct yet collide under
`rompelShiftedStep G n q (BitString.listRow (G.inLen n) 0 K)`. -/
theorem exists_rompelCascadeInput_collision (G : ShrinkingCollisionGrid)
    {n q : ℕ} {K x₀ x₁ : List Bool}
    (hx₀ : x₀.length = 2 * rompelBlockLen G n)
    (hx₁ : x₁.length = 2 * rompelBlockLen G n)
    (hne : x₀ ≠ x₁)
    (hcol : rompelCandidateEval G n q K x₀ = rompelCandidateEval G n q K x₁) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ rompelCascadeSteps G n ∧
      rompelCascadeInput G n q i K x₀ ≠ rompelCascadeInput G n q i K x₁ ∧
      rompelShiftedStep G n q (BitString.listRow (G.inLen n) 0 K)
          (rompelCascadeInput G n q i K x₀) =
        rompelShiftedStep G n q (BitString.listRow (G.inLen n) 0 K)
          (rompelCascadeInput G n q i K x₁) :=
  exists_shoupCascade_step_collision (G.shrinkLen_pos n) (outLen_le_two_mul_rompelBlockLen G n)
    (two_mul_rompelBlockLen_le G n)
    (rompelShiftedStep G n q (BitString.listRow (G.inLen n) 0 K))
    (fun w _ => length_rompelShiftedStep G n q _ w)
    (K.drop (G.inLen n)) x₀ x₁ hx₀ hx₁ hne hcol

/-! ### `gridCount n`-way candidate concatenation (adapting `[HHRVW2020]`, STEP 5(iii), p. 32) -/

/-- **`gridCount n`-way concatenated compression evaluator** (adapting `[HHRVW2020]`, Section 5.1.5,
STEP 5(iii), p. 32): evaluates `rompelCandidateEval G n q K x` for every `0 ≤ q < G.gridCount n`
under the shared key sequence `K` and concatenates the `G.outLen n`-bit digests into a
`rompelBlockLen G n`-bit block. -/
def rompelCompressionEval (G : ShrinkingCollisionGrid) (n : ℕ) (K x : List Bool) : List Bool :=
  (List.range (G.gridCount n)).flatMap fun q => rompelCandidateEval G n q K x

@[simp]
theorem length_rompelCompressionEval (G : ShrinkingCollisionGrid) (n : ℕ) (K x : List Bool) :
    (rompelCompressionEval G n K x).length = rompelBlockLen G n := by
  simp [rompelCompressionEval, rompelBlockLen]

theorem listRow_rompelCompressionEval (G : ShrinkingCollisionGrid) (n : ℕ) (K x : List Bool)
    {q : ℕ} (hq : q < G.gridCount n) :
    BitString.listRow (G.outLen n) q (rompelCompressionEval G n K x) =
      rompelCandidateEval G n q K x := by
  have h := BitString.listRow_flatMap_append (width := G.outLen n)
    (fun idx => rompelCandidateEval G n idx K x) (List.range (G.gridCount n))
    (fun idx _ => length_rompelCandidateEval G n idx K x) [] q (by simpa using hq)
  simpa only [rompelCompressionEval, List.append_nil, List.getElem_range] using h

@[fun_prop]
theorem computableInPolyTime_rompelCompressionEval (G : ShrinkingCollisionGrid) :
    ComputableInPolyTime
      (fun ⟨n, K, x⟩ => rompelCompressionEval G n K x)
      (encPair encUnary (encPair encBits encBits)) encBits := by
  unfold rompelCompressionEval
  apply ComputableInPolyTime.flatMapToBitsWithInput
    (ComputableInPolyTime.unary_range' (by fun_prop))
  have hp := ComputableInPolyTime.id'
    (encIn := encPair (encPair encUnary (encPair encBits encBits)) encUnary)
  exact computableInPolyTime_rompelCandidateEval G hp.fst'.fst' hp.snd'
    hp.fst'.snd'.fst' hp.fst'.snd'.snd'

/-- **Rompel / HHRVW halving `KeyedCompressionFamily`** (adapting `[Shoup2000]`;
`[HHRVW2020]`, Section 5.1.5, STEP 4 and STEP 5(ii–iii), pp. 31–32): compresses
`2 * rompelBlockLen G n`-bit blocks to `rompelBlockLen G n`-bit blocks under shared
`O(|y| log t)` Shoup XOR-masking keys (`rompelKeyLen G n`). -/
@[expose]
def rompelCompression (G : ShrinkingCollisionGrid) : KeyedCompressionFamily where
  keyLen := rompelKeyLen G
  blockLen := rompelBlockLen G
  eval := rompelCompressionEval G
  keyLen_polyTime := computableInPolyTime_rompelKeyLen G
  blockLen_polyTime := computableInPolyTime_rompelBlockLen G
  polyTime := computableInPolyTime_rompelCompressionEval G
  le_blockLen := le_rompelBlockLen G
  length_eq n K x _ _ := length_rompelCompressionEval G n K x

/-- **`[HHRVW2020]` Lemma 5.7 `O(|y| log t)` key-length bound** directly on
`(rompelCompression G).keyLen`. -/
theorem ShrinkingCollisionGrid.rompelCompression_keyLen_le
    (G : ShrinkingCollisionGrid) (n : ℕ) :
    (rompelCompression G).keyLen n ≤ (Nat.log 2 (rompelCascadeSteps G n) + 2) * G.inLen n :=
  rompelKeyLen_le G n

/-! ### Modular reduction via `ShoupComposition` to `randomCollisionGame` -/

private def clampIdx (bound guess : ℕ) : ℕ :=
  (bound - 1) - ((bound - 1) - guess)

private theorem clampIdx_eq_of_lt {bound guess : ℕ} (h : guess < bound) :
    clampIdx bound guess = guess := by
  unfold clampIdx; omega

@[local fun_prop]
private theorem computableInPolyTime_clampIdx {γ : Type} {encIn : γ ↪ List Bool}
    {bound guess : γ → ℕ}
    (hb : ComputableInPolyTime bound encIn encUnary)
    (hg : ComputableInPolyTime guess encIn encUnary) :
    ComputableInPolyTime (fun a => clampIdx (bound a) (guess a)) encIn encUnary := by
  unfold clampIdx; fun_prop

/-- **Planted-subkey reduction to `randomCollisionGame`** (`[Shoup2000]`; `[HHRVW2020]`,
Section 5.1.4, Lemmas 5.6–5.7, pp. 29–30; Section 5.1.5, STEPS 4–5, pp. 31–32): samples a dyadic
candidate guess `qGuess`, runs `shoupComposeChoose` to obtain the planted `G.inLen n`-bit step
target `choice.1` and encoded Shoup state `choice.2`, shifts the challenge `zWord` to form
`yStar = listXor (G.inLen n) [zWord, choice.1]`, runs `shoupComposeFindWith` on
`rompelShiftedStep G n q` at key `yStar`, and unmasks the returned step input via `w₁ ⊕ yStar`. -/
noncomputable def rompelCompressionInverter (G : ShrinkingCollisionGrid)
    (adversary : TargetCollisionFinder) (n : ℕ) (zWord : List Bool) : ProbComp (List Bool) := do
  let qGuess ← sampleDyadicIndex (G.gridCount n)
  let choice ← shoupComposeChoose G.outLen G.shrinkLen (rompelCascadeSteps G) adversary n
  let q := clampIdx (G.gridCount n) qGuess
  let yStar := BitString.listXor (G.inLen n) [zWord, choice.1]
  let w₁ ← shoupComposeFindWith (G.inLen n) (G.outLen n) (G.shrinkLen n)
    (rompelCascadeSteps G n) (rompelShiftedStep G n q) adversary n choice.2 yStar
  return BitString.listXor (G.inLen n) [w₁, yStar]

/-- `rompelCompressionInverter G adversary` is uniformly strict PPT whenever `adversary` is
strict PPT. -/
theorem isPPT_rompelCompressionInverter (G : ShrinkingCollisionGrid)
    {adversary : TargetCollisionFinder} (ha : adversary.IsPPT) :
    IsPPT encBits (rompelCompressionInverter G adversary) := by
  apply IsPPTOn.isPPT
  refine (isPPTOn_sampleDyadicIndex (by fun_prop)).bind_with ?_
  refine ((isPPTOn_shoupComposeChoose G.polyTime_outLen G.polyTime_shrinkLen
    (computableInPolyTime_rompelCascadeSteps G) ha.choose).preprocess (by fun_prop)).bind_with ?_
  let enc2 := encPair (encPair (encPair encUnary encBits) encUnary) (encPair encBits encBits)
  have h2 := ComputableInPolyTime.id' (encIn := enc2)
  have h2_n := h2.fst'.fst'.fst'
  have h2_in := G.polyTime_inLen.comp h2_n
  have h2_yStar := ComputableInPolyTime.bitsXorWithInput h2_in
    (.cons' h2.fst'.fst'.snd' (.cons' h2.snd'.fst' (.const [])))
  have sid := ComputableInPolyTime.id' (encIn := encPair enc2 (encPair encBits encBits))
  have hstep_key := computableInPolyTime_rompelShiftedStep G (h2_n.comp sid.fst')
    (computableInPolyTime_clampIdx (G.polyTime_gridCount.comp (h2_n.comp sid.fst'))
      (h2.fst'.snd'.comp sid.fst'))
    sid.snd'.fst' sid.snd'.snd'
  refine (isPPTOn_shoupComposeFindWith
    (stepOfKey := fun r : ((ℕ × List Bool) × ℕ) × (List Bool × List Bool) =>
      rompelShiftedStep G r.1.1.1 (clampIdx (G.gridCount r.1.1.1) r.1.2))
    h2_in (G.polyTime_outLen.comp h2_n) (G.polyTime_shrinkLen.comp h2_n)
    ((computableInPolyTime_rompelCascadeSteps G).comp h2_n)
    h2_n hstep_key (fun _ _ w _ _ => length_rompelShiftedStep G _ _ _ w)
    h2.snd'.snd' h2_yStar ha.find).bind_with ?_
  have h3 := ComputableInPolyTime.id' (encIn := encPair enc2 encBits)
  exact (ComputableInPolyTime.bitsXorWithInput (h2_in.comp h3.fst')
    (.cons' h3.snd' (.cons' (h2_yStar.comp h3.fst') (.const [])))).isPPTOn

/-- **Concrete security bound for `rompelCompression G`**: at every candidate index
`qStar < G.gridCount n`, the target-collision success probability of `adversary` against
`rompelCompression G` is at most `dyadicSize (G.gridCount n) * dyadicSize (rompelCascadeSteps G n)`
times the random-collision success probability of `rompelCompressionInverter G adversary` against
candidate `qStar`. -/
theorem succProbability_targetCollisionGame_rompelCompression_le
    (G : ShrinkingCollisionGrid) (adversary : TargetCollisionFinder)
    {n qStar : ℕ} (hqStar : qStar < G.gridCount n) :
    Game.succProbability
      (ProbComp.eval
        (targetCollisionGame (rompelCompression G).keyLen (rompelCompression G).eval
          (rompelCompression G).validInput adversary n)) ≤
      (dyadicSize (G.gridCount n) * dyadicSize (rompelCascadeSteps G n) : ℝ≥0) *
        Game.succProbability
          (ProbComp.eval
            (randomCollisionGame (fun k => G.evalGrid k qStar) G.inLen
              (rompelCompressionInverter G adversary) n)) := by
  let hShift (m : ℕ) (y w : List Bool) : List Bool := rompelShiftedStep G m qStar y w
  let validLong (m : ℕ) (x : List Bool) : Bool := x.length == 2 * rompelBlockLen G m
  let validBase (m : ℕ) (w : List Bool) : Bool := w.length == G.outLen m + G.shrinkLen m
  let shoupAdv :=
    shoupComposeAdversary G.inLen G.outLen G.shrinkLen (rompelCascadeSteps G) hShift adversary
  -- Step 1: Projecting a `rompelCompressionEval` collision onto row `qStar` yields a collision
  -- on `rompelCandidateEval G n qStar` (= `shoupComposeEval` for `hShift`).
  have hproj :
      Game.succProbability
        (ProbComp.eval
          (targetCollisionGame (rompelCompression G).keyLen (rompelCompression G).eval
            (rompelCompression G).validInput adversary n)) ≤
      Game.succProbability
        (ProbComp.eval
          (targetCollisionGame (shoupComposeKeyLen G.inLen G.outLen (rompelCascadeSteps G))
            (shoupComposeEval G.inLen G.outLen G.shrinkLen (rompelCascadeSteps G) hShift)
            validLong adversary n)) := by
    refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) ?_
    dsimp only [targetCollisionGame]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList,
      show (rompelCompression G).keyLen n =
          shoupComposeKeyLen G.inLen G.outLen (rompelCascadeSteps G) n
        by simp only [rompelCompression, rompelKeyLen]]
    refine PMF.bind_apply_mono_on_support _ true fun choice _ =>
      PMF.bind_apply_mono_on_support _ true fun K _ =>
        PMF.bind_apply_mono_on_support _ true fun x₁ _ => ?_
    cases hW : isCollision ((rompelCompression G).eval n) (rompelCompression G).validInput n K
        choice.1 x₁
    · simp only [PMF.pure_apply, reduceCtorEq, ↓reduceIte]; exact zero_le
    · obtain ⟨hx₀, hx₁, hne, hcol⟩ := isCollision_eq_true_iff.mp hW
      simp only [KeyedCompressionFamily.validInput, rompelCompression] at hx₀ hx₁
      rw [isCollision_eq_true_iff.mpr ⟨hx₀, hx₁, hne, by
            change rompelCandidateEval G n qStar K choice.1 = rompelCandidateEval G n qStar K x₁
            rw [← listRow_rompelCompressionEval G n K choice.1 hqStar,
              ← listRow_rompelCompressionEval G n K x₁ hqStar]
            exact congrArg _ hcol⟩]
  -- Step 2: Apply `succProbability_targetCollisionGame_shoupCompose_le` (`dyadicSize t` factor).
  have hshoup :
      Game.succProbability
        (ProbComp.eval
          (targetCollisionGame (shoupComposeKeyLen G.inLen G.outLen (rompelCascadeSteps G))
            (shoupComposeEval G.inLen G.outLen G.shrinkLen (rompelCascadeSteps G) hShift)
            validLong adversary n)) ≤
      (dyadicSize (rompelCascadeSteps G n) : ℝ≥0) *
        Game.succProbability
          (ProbComp.eval (targetCollisionGame G.inLen hShift validBase shoupAdv n)) :=
    succProbability_targetCollisionGame_shoupCompose_le adversary n
      (G.shrinkLen_pos n) (outLen_le_two_mul_rompelBlockLen G n) (two_mul_rompelBlockLen_le G n)
      (fun _ w _ _ => length_rompelShiftedStep G n qStar _ w)
  -- Step 3: Lemma 5.6 1-step XOR-shift + `qGuess = qStar` point bound (`dyadicSize gridCount`).
  have hshift :
      Game.succProbability
        (ProbComp.eval (targetCollisionGame G.inLen hShift validBase shoupAdv n)) ≤
      (dyadicSize (G.gridCount n) : ℝ≥0) *
        Game.succProbability
          (ProbComp.eval
            (randomCollisionGame (fun k => G.evalGrid k qStar) G.inLen
              (rompelCompressionInverter G adversary) n)) := by
    let Dq := dyadicSize (G.gridCount n)
    let W := G.inLen n
    let candTrial (qGuess : ℕ) : Game :=
      (ProbComp.eval
        (shoupComposeChoose G.outLen G.shrinkLen (rompelCascadeSteps G) adversary n)).bind
        fun choice =>
          (BitString.uniformList W).bind fun zWord =>
            let q := clampIdx (G.gridCount n) qGuess
            let yStar := BitString.listXor W [zWord, choice.1]
            (ProbComp.eval
              (shoupComposeFindWith W (G.outLen n) (G.shrinkLen n) (rompelCascadeSteps G n)
                (rompelShiftedStep G n q) adversary n choice.2 yStar)).bind fun w₁ =>
              let z' := BitString.listXor W [w₁, yStar]
              PMF.pure (decide (z'.length = W ∧ z' ≠ zWord ∧
                G.evalGrid n qStar z' = G.evalGrid n qStar zWord))
    have hrand_eq :
        ProbComp.eval
          (randomCollisionGame (fun k => G.evalGrid k qStar) G.inLen
            (rompelCompressionInverter G adversary) n) =
          (PMF.uniformOfFintype (Fin Dq)).bind fun a => candTrial a.val := by
      dsimp only [randomCollisionGame, rompelCompressionInverter, candTrial, Dq, W]
      simp only [ProbComp.eval_bind, ProbComp.eval_pure, eval_sampleDyadicIndex,
        BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind, PMF.bind_map, Function.comp_def]
      rw [PMF.bind_comm (BitString.uniformList W) (PMF.uniformOfFintype (Fin Dq))]
      exact PMF.bind_congr_on_support _ _ _ fun _ _ => PMF.bind_comm (BitString.uniformList W) _ _
    have hqStar_eq :
        candTrial qStar =
          ProbComp.eval (targetCollisionGame G.inLen hShift validBase shoupAdv n) := by
      dsimp only [candTrial, targetCollisionGame, shoupAdv, shoupComposeAdversary]
      simp only [clampIdx_eq_of_lt hqStar, ProbComp.eval_bind, ProbComp.eval_pure,
        BitString.eval_sampleList]
      refine PMF.bind_congr_on_support _ _ _ fun choice hch => ?_
      have hw₀_len : choice.1.length = W :=
        (length_fst_of_mem_support_shoupComposeChoose hch).trans (G.outLen_add_shrink n)
      conv_rhs => rw [← BitString.uniformList_map_listXor W choice.1, PMF.bind_map]
      refine PMF.bind_congr_on_support _ _ _ fun zWord hz => ?_
      have hz_len := BitString.length_of_mem_support_uniformList hz
      dsimp only [Function.comp_def]
      refine PMF.bind_congr_on_support _ _ _ fun w₁ hw₁ => ?_
      have hw₁_len : w₁.length = W :=
        (length_of_mem_support_shoupComposeFindWith hw₁).trans (G.outLen_add_shrink n)
      set yStar := BitString.listXor W [zWord, choice.1]
      have hx₀ : BitString.listXor W [choice.1, yStar] = zWord := by
        dsimp only [yStar]
        rw [BitString.listXor_pair_comm W zWord choice.1,
          BitString.listXor_pair_self_left_of_length choice.1 hz_len]
      have hne_iff : BitString.listXor W [w₁, yStar] ≠ zWord ↔ choice.1 ≠ w₁ := by
        rw [← hx₀, ne_eq, BitString.listXor_pair_left_inj hw₁_len hw₀_len yStar, ne_comm]
      have hv {w : List Bool} (hw : w.length = W) : validBase n w = true := by
        simp [validBase, hw, W, G.outLen_add_shrink n]
      dsimp only [W] at hx₀ hne_iff ⊢
      congr 1
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, isCollision_eq_true_iff]
      simp only [BitString.length_listXor, true_and, hne_iff, hv hw₀_len, hv hw₁_len, hShift,
        rompelShiftedStep, hx₀, eq_comm]
    obtain ⟨val, hval⟩ : ∃ val : ℕ → ℝ≥0, ∀ q, Game.succProbability (candTrial q) = val q :=
      ⟨_, fun _ => rfl⟩
    let aStar : Fin Dq := ⟨qStar, hqStar.trans (lt_dyadicSize _)⟩
    have : Nonempty (Fin Dq) := ⟨aStar⟩
    conv_lhs => rw [← hqStar_eq, hval]
    rw [hrand_eq, Game.succProbability_uniform, Fintype.card_fin,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (dyadicSize_pos _).ne')]
    simp_rw [hval]
    exact Finset.single_le_sum (f := fun a : Fin Dq => val a.val)
      (fun _ _ => zero_le) (Finset.mem_univ aStar)
  exact ((hproj.trans hshoup).trans (mul_le_mul_of_nonneg_left hshift zero_le)).trans_eq (by ring)

/-- **Adapting `[HHRVW2020]`, Section 5.1.5, STEP 4 and STEP 5(ii–iii) (pp. 31–32)**: for any
`ShrinkingCollisionGrid` `G`, `rompelCompression G` is a target collision-resistant
`KeyedCompressionFamily`. -/
theorem ShrinkingCollisionGrid.targetCollisionResistant_rompelCompression
    (G : ShrinkingCollisionGrid) :
    (rompelCompression G).TargetCollisionResistant := by
  apply TargetCollisionResistantOn.of_negligible
  intro adversary hadversary
  obtain ⟨goodIdx, hgood_lt, hneg_rand⟩ := G.exists_good_candidate _
    (isPPT_rompelCompressionInverter G hadversary)
  have hloss_pb :=
    (dyadicSize_polynomiallyBounded.comp G.polyTime_gridCount.polynomiallyBounded).mul
      (dyadicSize_polynomiallyBounded.comp
        (computableInPolyTime_rompelCascadeSteps G).polynomiallyBounded)
  refine negligible_of_le (hneg_rand.polynomiallyBounded_mul hloss_pb) fun n => ?_
  simpa only [randomCollisionGame, Nat.cast_mul] using
    succProbability_targetCollisionGame_rompelCompression_le G adversary (hgood_lt n)

/-! ### Unrestricted `KeyedHashFamily` and `OneWay` UOWHF endpoints -/

/-- **Rompel / HHRVW unrestricted `KeyedHashFamily`** (`[Rompel1990]`; `[HHRVW2020]`,
Section 5.1, Theorem 5.1, p. 26): hashes arbitrary-length bit strings `List Bool` to
`rompelBlockLen G n`-bit digests via `(rompelCompression G).treeHash` (inheriting `uowhfTreeHash`'s
`(n + 1)`-level binary tree and `< 2 ^ n` finite-parameter tree capacity). -/
@[expose]
def rompelHash (G : ShrinkingCollisionGrid) : KeyedHashFamily :=
  (rompelCompression G).treeHash

/-- `rompelHash G` is unrestrictedly target collision-resistant on all `List Bool`. -/
theorem ShrinkingCollisionGrid.targetCollisionResistant_rompelHash
    (G : ShrinkingCollisionGrid) :
    (rompelHash G).TargetCollisionResistant :=
  KeyedCompressionFamily.targetCollisionResistant_treeHash
    G.targetCollisionResistant_rompelCompression

/-- End-to-end target collision-resistant compression from Definition 3.9
(`AdversaryInaccessibleEntropyFamily`) preserving both the `(Nat.log 2 n + 1)`-bit candidate
shrinkage of `exists_shrinkingCollisionGrid_log` and Lemma 5.7's `O(|y| log t)` shared-key bound
`rompelCompression_keyLen_le`. -/
theorem AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid_rompelCompression
    (F : AdversaryInaccessibleEntropyFamily) :
    ∃ G : ShrinkingCollisionGrid,
      (∀ n, G.shrinkLen n = Nat.log 2 n + 1) ∧
      (rompelCompression G).TargetCollisionResistant ∧
      ∀ n, (rompelCompression G).keyLen n ≤
        (Nat.log 2 (rompelCascadeSteps G n) + 2) * G.inLen n :=
  let ⟨G, hlog⟩ := F.exists_shrinkingCollisionGrid_log
  ⟨G, hlog, G.targetCollisionResistant_rompelCompression, G.rompelCompression_keyLen_le⟩

/-- End-to-end target collision-resistant compression from any uniform `OneWay` function,
preserving both `(Nat.log 2 n + 1)`-bit candidate shrinkage and Lemma 5.7's `O(|y| log t)`
shared-key bound `rompelCompression_keyLen_le`. -/
theorem OneWay.exists_shrinkingCollisionGrid_rompelCompression
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ G : ShrinkingCollisionGrid,
      (∀ n, G.shrinkLen n = Nat.log 2 n + 1) ∧
      (rompelCompression G).TargetCollisionResistant ∧
      ∀ n, (rompelCompression G).keyLen n ≤
        (Nat.log 2 (rompelCascadeSteps G n) + 2) * G.inLen n :=
  let ⟨G, hlog⟩ := hf.exists_shrinkingCollisionGrid_log
  ⟨G, hlog, G.targetCollisionResistant_rompelCompression, G.rompelCompression_keyLen_le⟩

/-- **Qualitative polynomial-time target collision-resistant compression from Definition 3.9**
(`[HHRVW2020]`, Section 5.1, Theorem 5.1, p. 26): every `AdversaryInaccessibleEntropyFamily` yields
a target collision-resistant `KeyedCompressionFamily`. `EntropyReduction` uses dense two-universal
matrices rather than Toeplitz hashing; see `exists_shrinkingCollisionGrid_rompelCompression` and
`rompelCompression_keyLen_le` for the Lemma 5.7 `O(|y| log t)` key-length bound. -/
theorem AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantCompression
    (F : AdversaryInaccessibleEntropyFamily) :
    ∃ C : KeyedCompressionFamily, C.TargetCollisionResistant := by
  obtain ⟨G, _, hTCR, _⟩ := F.exists_shrinkingCollisionGrid_rompelCompression
  exact ⟨rompelCompression G, hTCR⟩

/-- **Qualitative polynomial-time target collision-resistant hashing from Definition 3.9**
(`[HHRVW2020]`, Section 5.1, Theorem 5.1, p. 26): every `AdversaryInaccessibleEntropyFamily` yields
an unrestricted target collision-resistant `KeyedHashFamily` on `List Bool` via the `(n + 1)`-level
`KeyedCompressionFamily.treeHash` wrapper (`EntropyReduction` uses dense two-universal matrices;
see `rompelCompression_keyLen_le` for the Lemma 5.7 compression key bound). -/
theorem AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantHash
    (F : AdversaryInaccessibleEntropyFamily) :
    ∃ H : KeyedHashFamily, H.TargetCollisionResistant := by
  obtain ⟨G⟩ := F.exists_shrinkingCollisionGrid
  exact ⟨rompelHash G, G.targetCollisionResistant_rompelHash⟩

/-- **Qualitative polynomial-time target collision-resistant compression from `OneWay`**
(`[HHRVW2020]`, Section 5.1, Theorem 5.1, p. 26): every uniform `OneWay` function yields a target
collision-resistant `KeyedCompressionFamily` (`EntropyReduction` uses dense two-universal matrices;
see `OneWay.exists_shrinkingCollisionGrid_rompelCompression` and `rompelCompression_keyLen_le` for
the Lemma 5.7 `O(|y| log t)` key-length bound). -/
theorem OneWay.exists_targetCollisionResistant_keyedCompressionFamily
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ C : KeyedCompressionFamily, C.TargetCollisionResistant := by
  obtain ⟨G, _, hTCR, _⟩ := hf.exists_shrinkingCollisionGrid_rompelCompression
  exact ⟨rompelCompression G, hTCR⟩

/-- **Rompel–HHRVW universal one-way hash theorem** (`[Rompel1990]`; `[HHRVW2020]`,
Section 5.1, Theorem 5.1, p. 26, qualitative polynomial-time scope): every uniform `OneWay`
function implies the existence of an unrestricted target collision-resistant `KeyedHashFamily` on
`List Bool` (`EntropyReduction` uses dense two-universal matrices and `rompelHash` uses the
`(n + 1)`-level `KeyedCompressionFamily.treeHash`; see `rompelCompression_keyLen_le` for the
Lemma 5.7 `O(|y| log t)` compression key bound). -/
theorem OneWay.exists_targetCollisionResistant_keyedHashFamily
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ H : KeyedHashFamily, H.TargetCollisionResistant := by
  obtain ⟨F⟩ := hf.exists_inaccessibleEntropyFamily
  exact F.toAdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantHash

end Cslib.Crypto
