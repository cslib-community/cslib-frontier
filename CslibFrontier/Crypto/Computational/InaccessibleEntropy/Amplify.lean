/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.EntropyReduction
public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.OneWay
public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.Repetition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Probability.PMF.Uniform

/-!
# Gap amplification and candidate grid for logarithmic-bit shrinking collision resistance

Combining parallel repetition (`Repetition.lean`, Lemma 5.3), two-universal input hashing, and
$(\lfloor \log_2 n \rfloor + 1)$-bit shrinking output hashing (`EntropyReduction.lean`, Lemmas 5.4
and 5.5), this module formalizes STEPS 1–3 of `[HHRVW2020]`, Section 5.1.5, Proof of Theorem 5.1
(pp. 30–31):

1. **Concrete parameter schedule** (`ampSlack`, `ampReps`, `ampGridCount`, `ampShrinkLen`): from any
   `AdversaryInaccessibleEntropyFamily` $F$ (`[HHRVW2020]`, Definition 3.9, p. 15) with input width
   $n_0(n)$ and gap denominator $D(n) \ge 1$, set
   $$\Delta(n) = 3 (n + 2) D(n) (n_0(n) + 1)^2, \qquad
     t(n) = 6 D(n) \Delta(n), \qquad
     \kappa(n) = 6 D(n) (n_0(n) + 1) + 3,$$
   and logarithmic output shrinkage $s(n) = \lfloor \log_2 n \rfloor + 1$ (`ampShrinkLen n`).
   None of these schedules or evaluators mention any accessible-set family. At security parameters
   $n \ge N_0$ where $H(Z \mid F_0(Z)) - \mathbb{E}[\log_2 |L_A(Z)|] \ge 1 / D(n)$, repeating
   $t(n)$ times amplifies the expected entropy gap to at least $6 \Delta(n)$, while the Hoeffding
   exponent $2 \Delta(n)^2 / (t(n) \cdot n_0(n)^2)$ exceeds $n + 2$, and the output-hash factor
   $2^{s(n)} \le 2(n + 1)$ leaves total error $(4 n + 6) \cdot 2^{-n}$ negligible.
2. **Uniform polynomial-time candidate grid** (`ShrinkingCollisionGrid`): because the real entropy
   $k_0(n) = H(Z \mid F_0(Z))$ need not be efficiently computable and the accessible-set family
   $L_A$ may depend on the collision-finder, the grid exposes $\kappa(n)$ uniformly polynomial-time
   candidates $F_3^{(q \cdot \Delta(n))}$ ($0 \le q < \kappa(n)$), all sharing the same input width
   `inLen n`, output width `outLen n`, and shrinkage `shrinkLen n ≥ 1` with
   `outLen n + shrinkLen n = inLen n` and `n + 1 ≤ outLen n`.
3. **Adversary-dependent collision-resistant candidate on random inputs**
   (`AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid_log`,
   `AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid`,
   `InaccessibleEntropyFamily.exists_shrinkingCollisionGrid`,
   `OneWay.exists_shrinkingCollisionGrid`): because neither `shrunkHashEscapeInverter` nor
   `repEscapeInverter` reads the candidate index, each uniform strict-PPT adversary `B` against the
   grid induces a single uniform strict-PPT adversary $A_0(B)$ against $F_0$; applying Definition
   3.9 to $A_0(B)$ yields a witnessing family $L_{A_0(B)}$ whose mean $a_0(n)$ places
   $q^*_B(n) = \lfloor t(n) a_0(n) / \Delta(n) \rfloor_+ + 3 < \kappa(n)$ inside
   $[t a_0 + 2 \Delta, t k_0 - 3 \Delta]$, making candidate $q^*_B(n)$ collision-resistant on random
   inputs against `B`. Target shifts, Shoup-masked cascades, and $\kappa(n)$-way concatenation for
   target collision resistance and Rompel's signature theorem build on `ShrinkingCollisionGrid` in
   `CslibFrontier.Crypto.Computational.InaccessibleEntropy.TargetCollision` and
   `CslibFrontier.Crypto.Computational.Rompel`.

## Main definitions

* `Cslib.Crypto.ampSlack`, `Cslib.Crypto.ampReps`, `Cslib.Crypto.ampGridCount`,
  `Cslib.Crypto.ampShrinkLen`: pure-`ℕ` amplification, shrinkage, and grid-size schedule for an
  `AdversaryInaccessibleEntropyFamily`.
* `Cslib.Crypto.ShrinkingCollisionGrid`: uniform polynomial-time grid of shrinking candidates
  (`shrinkLen n ≥ 1`) admitting an adversary-dependent collision-resistant candidate sequence on
  random inputs.
* `Cslib.Crypto.AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid_log`:
  `log n`-bit shrinking grid witness (`shrinkLen n = Nat.log 2 n + 1`).

## Main results

* `Cslib.Crypto.AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid_log`,
  `Cslib.Crypto.InaccessibleEntropyFamily.exists_shrinkingCollisionGrid_log`,
  `Cslib.Crypto.OneWay.exists_shrinkingCollisionGrid_log`: STEPS 1–3 of Theorem 5.1 from Definition
  3.9, fixed `InaccessibleEntropyFamily`, and `OneWay` with `shrinkLen n = Nat.log 2 n + 1`.
* `Cslib.Crypto.AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid`,
  `Cslib.Crypto.InaccessibleEntropyFamily.exists_shrinkingCollisionGrid`,
  `Cslib.Crypto.OneWay.exists_shrinkingCollisionGrid`: `Nonempty ShrinkingCollisionGrid` (`1 ≤
  shrinkLen n`) corollaries.

## References

* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Sections 5.1.1–5.1.3 and 5.1.5, Theorem 5.1 STEPS 1–3,
  pp. 26–31][HHRVW2020]
-/

public section

namespace Cslib.Crypto

open Cslib.Probability Finset Turing.MultiTapeTM
open scoped BigOperators ENNReal NNReal

/-! ### Amplification parameter schedule and candidate-grid interface -/

/-- Concentration and hash-truncation slack
$\Delta(n) = 3 (n + 2) D(n) (n_0(n) + 1)^2$ (`[HHRVW2020]`, Section 5.1.5, STEP 1, p. 30). -/
@[expose] def ampSlack (F : AdversaryInaccessibleEntropyFamily) (n : ℕ) : ℕ :=
  3 * (n + 2) * F.denom n * ((F.inLen n + 1) * (F.inLen n + 1))

/-- Parallel repetition count $t(n) = 6 D(n) \Delta(n)$ (`[HHRVW2020]`, Section 5.1.5, STEP 1,
p. 30). -/
@[expose] def ampReps (F : AdversaryInaccessibleEntropyFamily) (n : ℕ) : ℕ :=
  6 * F.denom n * ampSlack F n

/-- Number of candidate truncation indices $\kappa(n) = 6 D(n) (n_0(n) + 1) + 3$ (`[HHRVW2020]`,
Section 5.1.5, STEP 5, p. 31). -/
@[expose] def ampGridCount (F : AdversaryInaccessibleEntropyFamily) (n : ℕ) : ℕ :=
  6 * F.denom n * (F.inLen n + 1) + 3

/-- Logarithmic output shrinkage $\lfloor \log_2 n \rfloor + 1$ bits (`[HHRVW2020]`, Section 5.1.3,
Lemma 5.5, p. 29, and Section 5.1.5, STEP 3, p. 31). Reuses `rompelTruncWidth`. -/
@[expose] def ampShrinkLen (n : ℕ) : ℕ := rompelTruncWidth n

/-- Effective repeated input bit width: equals `ampReps F n * F.inLen n` whenever `1 ≤ F.inLen n`
(in particular for all `n ≥ N₀`), with a fallback `n + 2` when `F.inLen n = 0` so nontrivial
shrinkage holds unconditionally at every `n : ℕ`. -/
@[expose] def ampRepInLen (F : AdversaryInaccessibleEntropyFamily) (n : ℕ) : ℕ :=
  if F.inLen n = 0 then n + 2 else ampReps F n * F.inLen n

/-- Effective repeated output bit width matching `ampRepInLen`. -/
@[expose] def ampRepOutLen (F : AdversaryInaccessibleEntropyFamily) (n : ℕ) : ℕ :=
  if F.inLen n = 0 then n + 2 else ampReps F n * F.outLen n

/-- Effective repeated word evaluator matching `ampRepInLen` and `ampRepOutLen`. -/
@[expose] def ampRepEvalWord (F : AdversaryInaccessibleEntropyFamily) (n : ℕ) (u : List Bool) :
    List Bool :=
  if F.inLen n = 0 then List.replicate (n + 2) false
  else repEvalWord (ampReps F n) (F.inLen n) (F.evalWord n) u

/-- A uniform polynomial-time candidate grid of shrinking hash functions
$F_3^{(n, q)} : \{0, 1\}^{\mathrm{inLen}(n)} \to \{0, 1\}^{\mathrm{outLen}(n)}$ ($0 \le q <
\mathrm{gridCount}(n)$) with shrinkage `shrinkLen n ≥ 1` such that every uniform strict-PPT
adversary `B` has an in-range candidate sequence `goodIdx` (which may depend on `B`) that is
collision-resistant on random inputs against `B` (`[HHRVW2020]`, Section 5.1.5, STEPS 1–3 and
STEP 5, pp. 30–31). -/
structure ShrinkingCollisionGrid where
  /-- Input bit width $N_3(n)$ shared by all candidates at security parameter $n$. -/
  inLen : ℕ → ℕ
  /-- Output bit width $M_3(n) = N_3(n) - \mathrm{shrinkLen}(n)$ shared by all candidates. -/
  outLen : ℕ → ℕ
  /-- Per-evaluation bit shrinkage $s(n) \ge 1$ shared by all candidates. -/
  shrinkLen : ℕ → ℕ
  /-- Polynomially bounded number of candidate indices $\kappa(n) \ge 1$. -/
  gridCount : ℕ → ℕ
  /-- Uniform word-level evaluator `(n, q, raw) ↦ evalGrid n q raw`. -/
  evalGrid : ℕ → ℕ → List Bool → List Bool
  /-- Plain polynomial-time unary input-length certificate. -/
  polyTime_inLen : ComputableInPolyTime inLen encUnary encUnary
  /-- Plain polynomial-time unary output-length certificate. -/
  polyTime_outLen : ComputableInPolyTime outLen encUnary encUnary
  /-- Plain polynomial-time unary shrinkage-width certificate. -/
  polyTime_shrinkLen : ComputableInPolyTime shrinkLen encUnary encUnary
  /-- Plain polynomial-time unary grid-count certificate. -/
  polyTime_gridCount : ComputableInPolyTime gridCount encUnary encUnary
  /-- Plain polynomial-time uniform grid-evaluation certificate. -/
  polyTime_evalGrid : ComputableInPolyTime
    (fun ⟨n, q, raw⟩ => evalGrid n q raw)
    (encPair encUnary (encPair encUnary encBits)) encBits
  /-- Nonempty candidate range at every security parameter. -/
  gridCount_pos : ∀ n, 1 ≤ gridCount n
  /-- Strict positive shrinkage (`≥ 1` bit) at every security parameter. -/
  shrinkLen_pos : ∀ n, 1 ≤ shrinkLen n
  /-- Nontrivial output length growing with the security parameter. -/
  le_outLen : ∀ n, n + 1 ≤ outLen n
  /-- Exact `shrinkLen n`-bit shrinkage at every security parameter. -/
  outLen_add_shrink : ∀ n, outLen n + shrinkLen n = inLen n
  /-- Exact output length `outLen n` for every candidate and raw word. -/
  length_evalGrid : ∀ n q raw, (evalGrid n q raw).length = outLen n
  /-- Every uniform strict-PPT adversary `B` admits an in-range candidate sequence `goodIdx` that is
  collision-resistant on random inputs against `B`. -/
  exists_good_candidate :
    ∀ B : ℕ → List Bool → ProbComp (List Bool), IsPPT encBits B →
      ∃ goodIdx : ℕ → ℕ, (∀ n, goodIdx n < gridCount n) ∧
        Negligible (fun n =>
          Game.succProbability (ProbComp.eval
            (randomCollisionGame (fun k => evalGrid k (goodIdx k)) inLen B n)))

/-! ### Polynomial-time certificates and dimension bounds -/

attribute [local fun_prop] AdversaryInaccessibleEntropyFamily.polyTime_inLen
  AdversaryInaccessibleEntropyFamily.polyTime_outLen
  AdversaryInaccessibleEntropyFamily.polyTime_denom
  AdversaryInaccessibleEntropyFamily.polyTime_evalWord

@[fun_prop]
theorem computableInPolyTime_ampSlack (F : AdversaryInaccessibleEntropyFamily) :
    ComputableInPolyTime (ampSlack F) encUnary encUnary := by
      unfold ampSlack
      fun_prop

@[fun_prop]
theorem computableInPolyTime_ampReps (F : AdversaryInaccessibleEntropyFamily) :
    ComputableInPolyTime (ampReps F) encUnary encUnary := by
      unfold ampReps
      fun_prop

@[fun_prop]
theorem computableInPolyTime_ampGridCount (F : AdversaryInaccessibleEntropyFamily) :
    ComputableInPolyTime (ampGridCount F) encUnary encUnary := by
      unfold ampGridCount
      fun_prop

@[fun_prop]
theorem computableInPolyTime_ampShrinkLen :
    ComputableInPolyTime ampShrinkLen encUnary encUnary :=
  computableInPolyTime_rompelTruncWidth

theorem ampShrinkLen_pos (n : ℕ) : 1 ≤ ampShrinkLen n :=
  Nat.succ_pos _

theorem ampShrinkLen_le (n : ℕ) : ampShrinkLen n ≤ n + 1 :=
  Nat.add_le_add_right (Nat.log_le_self 2 n) 1

theorem two_pow_ampShrinkLen_le (n : ℕ) : 2 ^ ampShrinkLen n ≤ 2 * (n + 1) :=
  two_pow_rompelTruncWidth_le n

@[fun_prop]
theorem computableInPolyTime_ampRepInLen (F : AdversaryInaccessibleEntropyFamily) :
    ComputableInPolyTime (ampRepInLen F) encUnary encUnary := by
  unfold ampRepInLen
  exact .ite_decide (by fun_prop) (by fun_prop) (by fun_prop)

@[fun_prop]
theorem computableInPolyTime_ampRepOutLen (F : AdversaryInaccessibleEntropyFamily) :
    ComputableInPolyTime (ampRepOutLen F) encUnary encUnary := by
  unfold ampRepOutLen
  exact .ite_decide (by fun_prop) (by fun_prop) (by fun_prop)

@[fun_prop]
theorem computableInPolyTime_ampRepEvalWord (F : AdversaryInaccessibleEntropyFamily) :
    ComputableInPolyTime (fun p : ℕ × List Bool => ampRepEvalWord F p.1 p.2)
      (encPair encUnary encBits) encBits := by
  unfold ampRepEvalWord
  exact .ite_decide (by fun_prop) (by fun_prop) (by fun_prop)

private theorem le_ampSlack (F : AdversaryInaccessibleEntropyFamily) (n : ℕ) :
    3 * (n + 2) ≤ ampSlack F n := by
  have := F.denom_pos n
  exact (Nat.le_mul_of_pos_right _ (by positivity)).trans
    (Nat.le_mul_of_pos_right _ (by positivity))

private theorem le_ampRepInLen (F : AdversaryInaccessibleEntropyFamily) (n : ℕ) :
    n + 2 ≤ ampRepInLen F n := by
  unfold ampRepInLen ampReps
  split_ifs with h0
  · exact le_rfl
  · have := Nat.pos_of_ne_zero h0
    have := F.denom_pos n
    exact (by have := le_ampSlack F n; omega : n + 2 ≤ ampSlack F n).trans
      ((Nat.le_mul_of_pos_left _ (by positivity)).trans (Nat.le_mul_of_pos_right _ (by positivity)))

private theorem add_ampShrinkLen_le_inputHashInLen (F : AdversaryInaccessibleEntropyFamily)
    (n : ℕ) : n + 1 + ampShrinkLen n ≤ inputHashInLen (ampRepInLen F n) := by
  unfold inputHashInLen
  nlinarith [le_ampRepInLen F n, ampShrinkLen_le n]

/-! ### Main grid theorem: STEPS 1–3 of Theorem 5.1 -/

private noncomputable def ampGoodIdx (F : AdversaryInaccessibleEntropyFamily)
    (accSet : (n : ℕ) → BitString (F.inLen n) → Finset (BitString (F.inLen n)))
    (N₀ n : ℕ) : ℕ :=
  if n < N₀ then 0
  else Nat.floor
    (((ampReps F n : ℝ) * accessibleSetExpectation (accSet n)) / (ampSlack F n : ℝ)) + 3

private theorem ampGoodIdx_lt_ampGridCount (F : AdversaryInaccessibleEntropyFamily)
    (accSet : (n : ℕ) → BitString (F.inLen n) → Finset (BitString (F.inLen n))) {N₀ : ℕ}
    (hN₀ : ∀ n ≥ N₀, accessibleSetExpectation (accSet n) ≤
      PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString (F.inLen n))).map fun z =>
        (wordToFinMap (F.inLen n) (F.outLen n) (F.evalWord n) z, z)) - 1 / (F.denom n : ℝ))
    (n : ℕ) : ampGoodIdx F accSet N₀ n < ampGridCount F n := by
  dsimp only [ampGoodIdx]
  split_ifs with hlt
  · unfold ampGridCount; omega
  · have hgap := hN₀ n (not_lt.mp hlt)
    have hk_le : PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString (F.inLen n))).map
        fun z => (wordToFinMap (F.inLen n) (F.outLen n) (F.evalWord n) z, z)) ≤ F.inLen n :=
      (PMF.conditionalEntropy_le_log_card _).trans_eq (by simp [Real.logb_pow])
    have hD_pos : (0 : ℝ) < F.denom n := Nat.cast_pos.2 (F.denom_pos n)
    have hΔ_pos : (0 : ℝ) < ampSlack F n :=
      Nat.cast_pos.2 (lt_of_lt_of_le (by omega) (le_ampSlack F n))
    have hfl : Nat.floor (((ampReps F n : ℝ) * accessibleSetExpectation (accSet n)) /
        (ampSlack F n : ℝ)) ≤ 6 * F.denom n * F.inLen n := by
      refine Nat.floor_le_of_le ?_
      simp only [ampReps, Nat.cast_mul, Nat.cast_ofNat]
      rw [mul_assoc, mul_comm (ampSlack F n : ℝ), ← mul_assoc, mul_div_cancel_right₀ _ hΔ_pos.ne']
      have ha_le : accessibleSetExpectation (accSet n) ≤ F.inLen n := by
        linarith [div_pos zero_lt_one hD_pos]
      gcongr
    unfold ampGridCount
    nlinarith [F.denom_pos n]

private theorem amp_hoeffding_exponent_le (F : AdversaryInaccessibleEntropyFamily) {n : ℕ}
    (hw₀_pos : 1 ≤ F.inLen n) :
    -2 * (ampSlack F n : ℝ) ^ 2 / ((ampReps F n : ℝ) * (F.inLen n : ℝ) ^ 2) ≤ -(n : ℝ) := by
  have hD : (1 : ℝ) ≤ F.denom n := by exact_mod_cast F.denom_pos n
  have hw : (1 : ℝ) ≤ F.inLen n := by exact_mod_cast hw₀_pos
  have hΔ : (0 : ℝ) < ampSlack F n := Nat.cast_pos.2 (lt_of_lt_of_le (by omega) (le_ampSlack F n))
  have ht : (ampReps F n : ℝ) = 6 * (F.denom n : ℝ) * (ampSlack F n : ℝ) := by
    simp only [ampReps, Nat.cast_mul, Nat.cast_ofNat]
  rw [div_le_iff₀ (by rw [ht]; positivity)]
  have hkey :=
    calc (n : ℝ) * ((ampReps F n : ℝ) * (F.inLen n : ℝ) ^ 2)
      _ ≤ ((n : ℝ) + 2) * ((6 * (F.denom n : ℝ) * (ampSlack F n : ℝ)) *
          ((F.inLen n : ℝ) + 1) ^ 2) := by
            rw [← ht]
            gcongr <;> nlinarith
      _ = 2 * (ampSlack F n : ℝ) ^ 2 := by
            unfold ampSlack
            push_cast; ring
  linarith

private theorem amp_randomCollisionGame_succProbability_le
    (F : AdversaryInaccessibleEntropyFamily)
    (accSet : (n : ℕ) → BitString (F.inLen n) → Finset (BitString (F.inLen n)))
    (hself : ∀ n z, z ∈ accSet n z) {N₀ : ℕ}
    (hN₀ : ∀ n ≥ N₀, accessibleSetExpectation (accSet n) ≤
      PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString (F.inLen n))).map fun z =>
        (wordToFinMap (F.inLen n) (F.outLen n) (F.evalWord n) z, z)) - 1 / (F.denom n : ℝ))
    (B : ℕ → List Bool → ProbComp (List Bool)) {n : ℕ} (hn : N₀ ≤ n) :
    Game.succProbability (ProbComp.eval
      (randomCollisionGame
        (fun k => shrunkHashEvalWord (ampRepInLen F k) (ampRepOutLen F k)
          (ampRepEvalWord F k) (ampGoodIdx F accSet N₀ k * ampSlack F k) (ampShrinkLen k))
        (fun k => shrunkHashInLen (ampRepInLen F k) (ampRepOutLen F k) (ampShrinkLen k)) B n)) ≤
      (dyadicSize (ampReps F n) : ℝ≥0) *
        Game.succProbability (ProbComp.eval
          (accessibleEscapeGame F.evalWord F.inLen accSet
            (repEscapeInverter (ampReps F) F.inLen
              (shrunkHashEscapeInverter
                (fun k => ampReps F k * F.inLen k)
                (fun k => ampReps F k * F.outLen k) ampShrinkLen B)) n)) +
      ((4 * n + 6 : ℕ) : ℝ≥0) * (1 / 2 : ℝ≥0) ^ n := by
  let n₁True (k : ℕ) : ℕ := ampReps F k * F.inLen k
  let m₁True (k : ℕ) : ℕ := ampReps F k * F.outLen k
  let B₁ := shrunkHashEscapeInverter n₁True m₁True ampShrinkLen B
  let w₀ := F.inLen n
  let m₀ := F.outLen n
  let D := F.denom n
  let t := ampReps F n
  let Δ := ampSlack F n
  let f₀ := wordToFinMap w₀ m₀ (F.evalWord n)
  let a₀ := accessibleSetExpectation (accSet n)
  let k₀ := PMF.conditionalEntropy ((PMF.uniformOfFintype (BitString w₀)).map fun z => (f₀ z, z))
  have ha₀_nonneg : 0 ≤ a₀ := accessibleSetExpectation_nonneg _
  have hgap₀ : a₀ ≤ k₀ - 1 / (D : ℝ) := hN₀ n hn
  have hk₀_le : k₀ ≤ (w₀ : ℝ) :=
    (PMF.conditionalEntropy_le_log_card _).trans_eq (by simp [Real.logb_pow])
  have hD_pos : (0 : ℝ) < D := by exact_mod_cast F.denom_pos n
  have hw₀_ne_zero : w₀ ≠ 0 := fun h0 => by
    linarith [div_pos zero_lt_one hD_pos, (Nat.cast_eq_zero (R := ℝ)).mpr h0]
  have hn₁_eq : ampRepInLen F n = n₁True n := by
    simp only [ampRepInLen, n₁True, hw₀_ne_zero, ↓reduceIte, w₀]
  have hm₁_eq : ampRepOutLen F n = m₁True n := by
    simp only [ampRepOutLen, m₁True, hw₀_ne_zero, ↓reduceIte, w₀]
  have heval₁_eq : ampRepEvalWord F n = repEvalWord t w₀ (F.evalWord n) := by
    funext u; simp only [ampRepEvalWord, hw₀_ne_zero, ↓reduceIte, t, w₀]
  have hs_le : ampShrinkLen n ≤ inputHashInLen (n₁True n) :=
    hn₁_eq ▸ Nat.le_of_add_left_le (add_ampShrinkLen_le_inputHashInLen F n)
  let A_max : ℝ := (t : ℝ) * a₀ + (Δ : ℝ)
  let K_min : ℝ := (t : ℝ) * k₀ - (Δ : ℝ)
  have hcoll := shrunkHash_randomCollision_le n₁True m₁True
    (fun k => ampGoodIdx F accSet N₀ k * ampSlack F k) ampShrinkLen
    (fun k => repEvalWord (ampReps F k) (F.inLen k) (F.evalWord k))
    (fun k => repBitAccessibleSet (ampReps F k) (F.inLen k) (accSet k))
    B n hs_le (fun u _ => length_repEvalWord (F.length_evalWord n) u) A_max K_min
  have hrep_esc := repEscape_le_dyadicSize_mul_escape (ampReps F) F.inLen F.outLen F.evalWord
    accSet B₁ n (F.length_evalWord n)
  have hΔ_ge : (3 * (n + 2) : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast le_ampSlack F n
  have hΔ_pos : (0 : ℝ) < Δ := by linarith
  have ht_real : (t : ℝ) = 6 * (D : ℝ) * (Δ : ℝ) := by dsimp only [t, ampReps]; push_cast; ring
  have hgap_scaled : 6 * (Δ : ℝ) ≤ (t : ℝ) * k₀ - (t : ℝ) * a₀ := by
    rw [← mul_sub]
    calc 6 * (Δ : ℝ) = (t : ℝ) * (1 / (D : ℝ)) := by rw [ht_real]; field_simp [hD_pos.ne']
      _ ≤ (t : ℝ) * (k₀ - a₀) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  let qFloor := Nat.floor (((t : ℝ) * a₀) / (Δ : ℝ))
  have hfloor_le : (qFloor : ℝ) * (Δ : ℝ) ≤ (t : ℝ) * a₀ :=
    (le_div_iff₀ hΔ_pos).mp (Nat.floor_le (by positivity))
  have hlt_floor_succ : (t : ℝ) * a₀ < ((qFloor : ℝ) + 1) * (Δ : ℝ) :=
    (div_lt_iff₀ hΔ_pos).mp (Nat.lt_floor_add_one _)
  let j₀ : ℕ := ampGoodIdx F accSet N₀ n * Δ
  have hj₀_real : (j₀ : ℝ) = ((qFloor : ℝ) + 3) * (Δ : ℝ) := by
    simp only [j₀, ampGoodIdx, not_lt.mpr hn, ↓reduceIte, t, a₀, Δ, qFloor]; push_cast; ring
  have hmin_eq : (min j₀ (n₁True n) : ℝ) = (j₀ : ℝ) := by
    have htw : (t : ℝ) * k₀ ≤ (n₁True n : ℝ) := by
      dsimp only [n₁True]; rw [Nat.cast_mul]; gcongr
    rw [← Nat.cast_min, Nat.min_eq_left (by exact_mod_cast (show (j₀ : ℝ) ≤ n₁True n by linarith))]
  have hhoeff_exp := amp_hoeffding_exponent_le F (Nat.pos_of_ne_zero hw₀_ne_zero)
  have htail_acc := (repBitAccessibleSet_logb_card_ge_prob t w₀ (accSet n) (hself n)
    hΔ_pos.le).trans (Real.exp_le_half_pow n hhoeff_exp)
  have htail_ent := (repEvalWord_realSampleEntropy_le_prob (F.length_evalWord n) hΔ_pos.le).trans
    (Real.exp_le_half_pow n hhoeff_exp)
  have hpow_in : (2 : ℝ) ^ (A_max - (min j₀ (n₁True n) : ℝ)) ≤ (1 / 2 : ℝ) ^ n :=
    Real.two_rpow_le_half_pow n (by rw [hmin_eq]; dsimp only [A_max]; linarith)
  have hpow_out : (2 : ℝ) ^ ((min j₀ (n₁True n) : ℝ) - K_min) ≤ (1 / 2 : ℝ) ^ n :=
    Real.two_rpow_le_half_pow n (by rw [hmin_eq]; dsimp only [K_min]; linarith)
  have hout_term :=
    (mul_le_mul (by exact_mod_cast two_pow_ampShrinkLen_le n :
        (2 : ℝ) ^ ampShrinkLen n ≤ 2 * ((n : ℝ) + 1))
      (add_le_add htail_ent hpow_out) (by positivity) (by positivity)).trans_eq
      (show (2 * ((n : ℝ) + 1)) * ((1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ n) =
        4 * ((n : ℝ) + 1) * (1 / 2 : ℝ) ^ n by ring)
  simp only [randomCollisionGame, hn₁_eq, hm₁_eq, heval₁_eq, t, w₀]
  rw [← NNReal.coe_le_coe]
  dsimp only [randomCollisionGame, n₁True, m₁True, B₁, t, w₀, m₀, j₀, Δ]
    at hcoll hrep_esc htail_acc hpow_in hout_term ⊢
  push_cast at hcoll hrep_esc hpow_in hout_term ⊢
  linarith [hcoll, hrep_esc, htail_acc, hpow_in, hout_term]

/-- **`[HHRVW2020]`, Section 5.1.5, Proof of Theorem 5.1, STEPS 1–3 (pp. 30–31) from Definition
3.9**: every `AdversaryInaccessibleEntropyFamily` yields a uniform polynomial-time
`ShrinkingCollisionGrid` of strictly `(Nat.log 2 n + 1)`-bit shrinking hash candidates. -/
theorem AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid_log
    (F : AdversaryInaccessibleEntropyFamily) :
    ∃ G : ShrinkingCollisionGrid, ∀ n, G.shrinkLen n = Nat.log 2 n + 1 := by
  refine ⟨{
    inLen := fun n => shrunkHashInLen (ampRepInLen F n) (ampRepOutLen F n) (ampShrinkLen n)
    outLen := fun n => shrunkHashOutLen (ampRepInLen F n) (ampRepOutLen F n) (ampShrinkLen n)
    shrinkLen := ampShrinkLen
    gridCount := ampGridCount F
    evalGrid := fun n q raw =>
      shrunkHashEvalWord (ampRepInLen F n) (ampRepOutLen F n)
        (ampRepEvalWord F n) (q * ampSlack F n) (ampShrinkLen n) raw
    polyTime_inLen := by unfold shrunkHashInLen outHashLen inputHashInLen inputHashOutLen; fun_prop
    polyTime_outLen := by
      unfold shrunkHashOutLen outHashLen inputHashInLen inputHashOutLen; fun_prop
    polyTime_shrinkLen := computableInPolyTime_ampShrinkLen
    polyTime_gridCount := computableInPolyTime_ampGridCount F
    polyTime_evalGrid := by fun_prop
    gridCount_pos := fun n => by unfold ampGridCount; omega
    shrinkLen_pos := ampShrinkLen_pos
    le_outLen := fun n => by
      have := add_ampShrinkLen_le_inputHashInLen F n
      unfold shrunkHashOutLen outHashLen; omega
    outLen_add_shrink := fun n => shrunkHashOutLen_add_shrink
      (Nat.le_of_add_left_le (add_ampShrinkLen_le_inputHashInLen F n)) _
    length_evalGrid := fun _ _ _ => length_shrunkHashEvalWord _ _ _ _ _ _
    exists_good_candidate := fun B hB => by
      have hB₀_ppt := isPPT_repEscapeInverter (t := ampReps F) (inLen₀ := F.inLen)
        (by fun_prop) (by fun_prop)
        (isPPT_shrunkHashEscapeInverter (n₁ := fun k => ampReps F k * F.inLen k)
          (m₁ := fun k => ampReps F k * F.outLen k) (s := ampShrinkLen)
          (by fun_prop) (by fun_prop) (by fun_prop) hB)
      obtain ⟨accSet, hself, _, ⟨N₀, hN₀⟩, hesc_neg⟩ := F.exists_accessibleSet _ hB₀_ppt
      refine ⟨ampGoodIdx F accSet N₀, ampGoodIdx_lt_ampGridCount F accSet hN₀, ?_⟩
      have hdyad_pb := dyadicSize_polynomiallyBounded.comp
        (computableInPolyTime_ampReps F).polynomiallyBounded
      have hgeom_neg := (negligible_geometric (ratio := (1 / 2 : ℝ≥0))
        (by norm_num)).polynomiallyBounded_mul (p := fun n => 4 * n + 6) (by fun_prop)
      refine negligible_of_eventually_le
        ((hesc_neg.polynomiallyBounded_mul hdyad_pb).add hgeom_neg) ?_
      filter_upwards [Filter.eventually_ge_atTop N₀] with n hn
      exact amp_randomCollisionGame_succProbability_le F accSet hself hN₀ B hn
  }, fun _ => rfl⟩

/-- Specialization of `AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid_log` to a
fixed `InaccessibleEntropyFamily`, preserving `G.shrinkLen n = Nat.log 2 n + 1`. -/
theorem InaccessibleEntropyFamily.exists_shrinkingCollisionGrid_log
    (F : InaccessibleEntropyFamily) :
    ∃ G : ShrinkingCollisionGrid, ∀ n, G.shrinkLen n = Nat.log 2 n + 1 :=
  F.toAdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid_log

/-- **`[HHRVW2020]`, Section 4.2, Theorem 4.5 (p. 21) composed with Section 5.1.5, Theorem 5.1,
STEPS 1–3 (pp. 30–31)**: every uniform `OneWay` function yields a uniform polynomial-time
`ShrinkingCollisionGrid` with `G.shrinkLen n = Nat.log 2 n + 1`. -/
theorem OneWay.exists_shrinkingCollisionGrid_log {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ G : ShrinkingCollisionGrid, ∀ n, G.shrinkLen n = Nat.log 2 n + 1 :=
  let ⟨F⟩ := hf.exists_inaccessibleEntropyFamily
  F.exists_shrinkingCollisionGrid_log

/-- `Nonempty ShrinkingCollisionGrid` (`1 ≤ shrinkLen n`) corollary of
`AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid_log`, forgetting the explicit
`Nat.log 2 n + 1` shrinkage equation. -/
theorem AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid
    (F : AdversaryInaccessibleEntropyFamily) :
    Nonempty ShrinkingCollisionGrid :=
  let ⟨G, _⟩ := F.exists_shrinkingCollisionGrid_log
  ⟨G⟩

/-- `Nonempty ShrinkingCollisionGrid` (`1 ≤ shrinkLen n`) specialization of
`AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid` to a fixed
`InaccessibleEntropyFamily`. -/
theorem InaccessibleEntropyFamily.exists_shrinkingCollisionGrid (F : InaccessibleEntropyFamily) :
    Nonempty ShrinkingCollisionGrid :=
  F.toAdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid

/-- `Nonempty ShrinkingCollisionGrid` (`1 ≤ shrinkLen n`) corollary of
`OneWay.exists_shrinkingCollisionGrid_log`, forgetting the explicit `Nat.log 2 n + 1` shrinkage
equation. -/
theorem OneWay.exists_shrinkingCollisionGrid {f : List Bool → List Bool} (hf : OneWay f) :
    Nonempty ShrinkingCollisionGrid :=
  let ⟨G, _⟩ := hf.exists_shrinkingCollisionGrid_log
  ⟨G⟩

end Cslib.Crypto
