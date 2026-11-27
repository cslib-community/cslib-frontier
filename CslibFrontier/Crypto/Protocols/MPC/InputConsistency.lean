/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Protocols.MPC.SPDZ
public import CslibFrontier.Languages.Probabilistic.Notation
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

/-!
# Input Consistency in Two-Party Arithmetic MPC: Additive-Shift Attack and MAC Repair

This module formalizes two complementary building blocks illustrating active input-consistency
vulnerabilities in unauthenticated two-party additive secret sharing over a prime field `ZMod q`
(`[Fact (Nat.Prime q)]`) and their information-theoretic repair via random MAC authentication:

1. **Corrupt-Party Additive-Shift Attack on `f(x) = x * (x - 1)` (`bitCheckPoly`,
   `AdditiveShare2`, `evalShiftedBitCheck`, `naiveBitCheckRealExp`, `naiveBitCheckIdealExp`):**
   Suppose `P₀` holds a secret bit `x ∈ {0, 1} ⊆ ZMod q` and shares it additively as `(x₀, x₁)`
   with `x₀ + x₁ = x`. In an unauthenticated arithmetic circuit evaluating the bit-check
   polynomial `f(x) = x * (x - 1)`, a malicious `P₁` can replace its share `x₁` by `x₁ + δ` for
   an arbitrary offset `δ : ZMod q`. We prove the exact algebraic evaluation identity
   $$f(x + \delta) = f(x) + \delta \cdot (2x + \delta - 1).$$
   For `x ∈ {0, 1}` and `δ = 1`, this simplifies to `f(x + 1) = 2 * x`, so `f(0 + 1) = 0` while
   `f(1 + 1) = 2`. Whenever `q > 2` is prime, `2 ≠ 0` in `ZMod q`, so the circuit output
   deterministically reveals `x` (`f(x + 1) = 0 ↔ x = 0` and `f(x + 1) = 2 ↔ x = 1`), whereas the
   ideal functionality outputs `f(x) = 0` identically for both `x = 0` and `x = 1`. In the
   explicit `ProbComp` distinguishing experiments, the `δ = 1` adversary achieves left-right
   distinguishing advantage `1` (versus `0` for any ideal-world observer) and hidden-bit recovery
   probability `1` (versus `1 / 2` in the ideal world).

2. **Random-MAC and Random-Linear-Combination Input-Authentication Repair
   (`SPDZ.AuthShare.tamperParty`, `mkAuthShare2`, `macSingleCheckGame`, `LinearCombAuthVec2`,
   `vecLinearCombCheckGame`, `vecBatchMacCheckGame`):**
   - *Single authenticated share:* authenticated inputs are two-party SPDZ shares
     `SPDZ.AuthShare q 2` with public modifier `δ = 0` (`mkAuthShare2`). Given a uniform MAC key
     `α ← $ᵗ ZMod q` unknown to `P₁` and a valid sharing of `(x, t)` with `t = α * x`, if a corrupt
     `P₁` adds `(δ_x, δ_t)` to its value and MAC shares (`SPDZ.AuthShare.tamperParty`), the
     reconstructed check `SPDZ.AuthShare.Valid α` passes if and only if `α * δ_x = δ_t`. For any
     nonzero input shift `δ_x ≠ 0`, this holds with exact probability `1 / q`
     (via `SPDZ.eval_macKey_guess_eq`).
   - *Vector of `k` input shares:* we package both (i) a batched vector-MAC / linear-code validity
     check (`LinearCombAuthVec2`) under a fresh uniform linear-combination key
     `r ← $ᵗ (Fin k → ZMod q)`, where honest shares pass with probability `1` and any nonzero
     tampering vector `δ ≠ 0` passes with exact probability `1 / q` (via
     `Cslib.Probability.toOuterMeasure_uniform_linearComb_eq`), and (ii) a batched check
     (`vecBatchMacCheckGame`) of `k` SPDZ-authenticated shares under independent random weights
     `r ← $ᵗ (Fin k → ZMod q)` and scalar MAC key `α ← $ᵗ ZMod q`, passing with probability `1`
     when honest and at most `2 / q` when `δ_x ≠ 0`; the tampered check has the distribution of
     `SPDZ.macCheckSoundnessGame`, so the bound is `SPDZ.probability_macCheckSoundnessGame_le`.

## Source mapping

* Sections 1–2 formalize the attack in [BonehShoup2023], Section 23.4.1, paragraph "Processing
  inputs: a first idea" (printed p. 1035): `Q_j` shares `x = x₁ + x₂`, a corrupt `P₁` adds one to
  its share, and the published output of `f(x) = x(x - 1)` then reveals a binary `x`. The source's
  input owner `Q_j` and parties `P₁, P₂` become `P₀`'s secret and the corrupt share holder here.
  The `q > 2` hypothesis (needed for `2 ≠ 0`) and the `ProbComp` real/ideal distinguishing and
  bit-guessing games are original framing.
* The source's repair, "Processing inputs: a second idea" (printed pp. 1035–1036, with its
  analysis continuing to p. 1037), authenticates each input by `E = A * x` but checks it inside
  the circuit through validity codes `D` and `F` built from shared triples. That in-circuit check,
  and a PPT-adversary treatment of the attack, are not formalized here; they remain open under
  #5829.
* Section 3's single-share relation `α * δ_x = δ_t` is the authentication-code check
  `K^{(i)} δ = δ^{(i)}` of [BonehShoup2023], Section 23.2.4.1, equation (23.2) (printed p. 1012),
  phrased on the SPDZ representation of [DamgardPastroSmartZakarias2012]. The batched scalar-MAC
  check of Section 4 is the `MACCheck` cheating equation of
  [DamgardKellerLarraiaPastroSchollSmart2013] (see `CslibFrontier.Crypto.Protocols.MPC.SPDZ`).
  The standalone tampering games (`macSingleCheckGame`, `vecLinearCombCheckGame`,
  `vecBatchMacCheckGame`) and the linear-combination code `LinearCombAuthVec2` are original.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.InputConsistency.bitCheckPoly`: the bit-check polynomial
  `f(x) = x * (x - 1)`.
* `Cslib.Crypto.Protocols.MPC.InputConsistency.AdditiveShare2`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.AdditiveShare2.reconstruct`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.AdditiveShare2.IsValidFor`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.AdditiveShare2.shiftShare1`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.evalShiftedBitCheck`: two-party additive shares,
  corrupt share-`1` additive shift, and shifted bit-check evaluation.
* `Cslib.Crypto.Protocols.MPC.InputConsistency.sampleAdditiveShare2`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.naiveBitCheckRealExp`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.naiveBitCheckIdealExp`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.shiftOneDistinguisher`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.naiveBitCheckRealLRGame`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.naiveBitCheckIdealLRGame`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.naiveBitCheckRealGuessGame`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.naiveBitCheckIdealGuessGame`: `ProbComp` real and
  ideal experiments and distinguishing games for the `δ = 1` attack.
* `Cslib.Crypto.Protocols.MPC.InputConsistency.mkAuthShare2`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.macSingleCheckGame`: two-party authenticated
  sharings with `δ = 0` and the single-input tampering check game (tampering is
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.tamperParty`).
* `Cslib.Crypto.Protocols.MPC.InputConsistency.LinearCombAuthVec2`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.LinearCombAuthVec2.IsValidFor`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.LinearCombAuthVec2.tamper1`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.vecLinearCombCheckGame`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.batchMacCheckPasses`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.vecBatchMacCheckGame`: vector input-sharing
  validity checks under fresh random linear-combination and MAC keys.

## Main results

* `Cslib.Crypto.Protocols.MPC.InputConsistency.bitCheckPoly_eq_zero_of_mem`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.bitCheckPoly_add`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.evalShiftedBitCheck_eq`: exact algebraic evaluation
  identity `f(x + δ) = f(x) + δ * (2 * x + δ - 1)`.
* `Cslib.Crypto.Protocols.MPC.InputConsistency.bitCheckPoly_add_one_eq_zero_iff`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.bitCheckPoly_add_one_eq_two_iff`: specialization to
  `δ = 1` and exact input recovery when `q > 2` is prime.
* `Cslib.Crypto.Protocols.MPC.InputConsistency.advantage_naiveBitCheckIdealLRGame`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.advantage_naiveBitCheckRealLRGame_shiftOne`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.probability_naiveBitCheckRealGuessGame`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.probability_naiveBitCheckIdealGuessGame`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.advantage_naiveBitCheckGuessGame`: exact
  distinguishing advantages (`1` vs `0`) and bit-recovery probabilities (`1` vs `1 / 2`).
* `Cslib.Crypto.Protocols.MPC.InputConsistency.probability_macSingleCheckGame_honest`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.probability_macSingleCheckGame_eq`: single-share
  completeness and exact `1 / q` soundness (through
  `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare.valid_tamperParty_iff`).
* `Cslib.Crypto.Protocols.MPC.InputConsistency.LinearCombAuthVec2.tamper1_isValidFor_iff`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.probability_vecLinearCombCheckGame_honest`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.probability_vecLinearCombCheckGame_eq`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.batchMacCheckPasses_tamperParty_iff`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.probability_vecBatchMacCheckGame_honest`,
  `Cslib.Crypto.Protocols.MPC.InputConsistency.probability_vecBatchMacCheckGame_le`: completeness
  (`1`) and soundness (`1 / q` and `2 / q`) for `k`-element input vectors.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Version 0.6,
  Section 23.2.4.1 (equation (23.2), p. 1012) and Section 23.4.1 (pp. 1035–1037).
* [I. Damgård, V. Pastro, N. P. Smart, S. Zakarias, *Multiparty Computation from Somewhat
  Homomorphic Encryption*][DamgardPastroSmartZakarias2012].
* [I. Damgård, M. Keller, E. Larraia, V. Pastro, P. Scholl, N. P. Smart, *Practical Covertly
  Secure MPC for Dishonest Majority — Or: Breaking the SPDZ
  Limits*][DamgardKellerLarraiaPastroSchollSmart2013].
-/

public section

namespace Cslib.Crypto.Protocols.MPC.InputConsistency

open Cslib.Probability Cslib.ProbComp Cslib.Crypto
open scoped ENNReal NNReal

/-! ### 1. Corrupt-party additive-shift attack on `f(x) = x * (x - 1)` -/

/-- The bit-check polynomial `f(x) = x * (x - 1)` over a ring `R`. -/
@[expose] def bitCheckPoly {R : Type} [Ring R] (x : R) : R :=
  x * (x - 1)

/-- Two-party additive sharing `(x₀, x₁)` of a value over `R`. -/
@[ext] structure AdditiveShare2 (R : Type) where
  /-- Party `0`'s additive share `x₀`. -/
  share0 : R
  /-- Party `1`'s additive share `x₁`. -/
  share1 : R
  deriving DecidableEq, Fintype, Inhabited, Repr

namespace AdditiveShare2

/-- Reconstructed value `x₀ + x₁` of a two-party additive sharing. -/
@[expose] def reconstruct {R : Type} [Add R] (s : AdditiveShare2 R) : R :=
  s.share0 + s.share1

/-- Predicate asserting that `s` is a valid additive sharing of `x` (`x₀ + x₁ = x`). -/
@[expose] def IsValidFor {R : Type} [Add R] (s : AdditiveShare2 R) (x : R) : Prop :=
  s.reconstruct = x

/-- Corrupt party `P₁` adds a known offset `δ` to its own share: `(x₀, x₁) ↦ (x₀, x₁ + δ)`. -/
@[expose] def shiftShare1 {R : Type} [Add R] (s : AdditiveShare2 R) (δ : R) : AdditiveShare2 R :=
  ⟨s.share0, s.share1 + δ⟩

@[simp] theorem reconstruct_shiftShare1 {R : Type} [AddSemigroup R]
    (s : AdditiveShare2 R) (δ : R) :
    (s.shiftShare1 δ).reconstruct = s.reconstruct + δ := by
  simp [reconstruct, shiftShare1, add_assoc]

theorem reconstruct_shiftShare1_of_isValidFor {R : Type} [AddSemigroup R]
    {s : AdditiveShare2 R} {x : R} (hs : s.IsValidFor x) (δ : R) :
    (s.shiftShare1 δ).reconstruct = x + δ := by
  rw [reconstruct_shiftShare1, hs]

end AdditiveShare2

/-- Output of the naive two-party bit-check circuit when corrupt `P₁` adds offset `δ` to its
share before evaluation. -/
@[expose] def evalShiftedBitCheck {R : Type} [Ring R] (s : AdditiveShare2 R) (δ : R) : R :=
  bitCheckPoly (s.shiftShare1 δ).reconstruct

/-- Any binary input `x ∈ {0, 1}` is a root of `f(x) = x * (x - 1)`. -/
theorem bitCheckPoly_eq_zero_of_mem {R : Type} [Ring R] {x : R} (hx : x ∈ ({0, 1} : Set R)) :
    bitCheckPoly x = 0 := by
  rcases hx with rfl | rfl <;> simp [bitCheckPoly]

/-- **Exact algebraic shift identity:** adding `δ` to `x` shifts `f(x) = x * (x - 1)` by
`δ * (2 * x + δ - 1)`. -/
theorem bitCheckPoly_add {R : Type} [CommRing R] (x δ : R) :
    bitCheckPoly (x + δ) = bitCheckPoly x + δ * (2 * x + δ - 1) := by
  dsimp only [bitCheckPoly]
  ring

/-- When `s` is a valid additive sharing of `x`, shifting `P₁`'s share by `δ` causes the naive
bit-check circuit to evaluate to `f(x) + δ * (2 * x + δ - 1)`. -/
theorem evalShiftedBitCheck_eq {R : Type} [CommRing R]
    {s : AdditiveShare2 R} {x : R} (hs : s.IsValidFor x) (δ : R) :
    evalShiftedBitCheck s δ = bitCheckPoly x + δ * (2 * x + δ - 1) := by
  dsimp only [evalShiftedBitCheck]
  rw [s.reconstruct_shiftShare1_of_isValidFor hs, bitCheckPoly_add]

private theorem bitCheckPoly_one {R : Type} [Ring R] :
    bitCheckPoly (1 : R) = 0 := by
  simp [bitCheckPoly]

private theorem bitCheckPoly_one_add_one {R : Type} [Ring R] :
    bitCheckPoly ((1 : R) + 1) = 2 := by
  dsimp only [bitCheckPoly]
  norm_num

private theorem two_ne_zero_zmod {q : ℕ} [Fact (Nat.Prime q)] (hq : 2 < q) :
    (2 : ZMod q) ≠ 0 := by
  intro h2
  have h2' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h2
  have hdvd : q ∣ 2 := (CharP.cast_eq_zero_iff (ZMod q) q 2).mp h2'
  have hle : q ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  omega

/-- **Converse / recovery lemma (`x = 0`):** for binary `x ∈ {0, 1} ⊆ ZMod q` with `q > 2` prime,
under the additive shift `δ = 1`, `f(x + 1) = 0 ↔ x = 0`. -/
theorem bitCheckPoly_add_one_eq_zero_iff {q : ℕ} [Fact (Nat.Prime q)] (hq : 2 < q)
    {x : ZMod q} (hx : x ∈ ({0, 1} : Set (ZMod q))) :
    bitCheckPoly (x + 1) = 0 ↔ x = 0 := by
  rcases hx with rfl | rfl
  · simp [bitCheckPoly_one]
  · simp [bitCheckPoly_one_add_one, two_ne_zero_zmod hq]

/-- **Converse / recovery lemma (`x = 1`):** for binary `x ∈ {0, 1} ⊆ ZMod q` with `q > 2` prime,
under the additive shift `δ = 1`, `f(x + 1) = 2 ↔ x = 1`. -/
theorem bitCheckPoly_add_one_eq_two_iff {q : ℕ} [Fact (Nat.Prime q)] (hq : 2 < q)
    {x : ZMod q} (hx : x ∈ ({0, 1} : Set (ZMod q))) :
    bitCheckPoly (x + 1) = 2 ↔ x = 1 := by
  have h2 : (2 : ZMod q) ≠ 0 := two_ne_zero_zmod hq
  rcases hx with rfl | rfl
  · simp [bitCheckPoly_one, Ne.symm h2]
  · simp [bitCheckPoly_one_add_one]

/-! ### 2. Explicit two-world distinguishing games for the `δ = 1` shift attack -/

/-- Sample a uniform two-party additive sharing `(x₀, x - x₀)` of `x : ZMod q`. -/
noncomputable def sampleAdditiveShare2 (q : ℕ) [NeZero q] (x : ZMod q) :
    ProbComp (AdditiveShare2 (ZMod q)) := do
  let x0 ← $ᵗ ZMod q
  return ⟨x0, x - x0⟩

/-- Every sharing in the support of `sampleAdditiveShare2 q x` reconstructs to `x`. -/
theorem isValidFor_of_mem_support_sampleAdditiveShare2 {q : ℕ} [NeZero q] {x : ZMod q}
    {s : AdditiveShare2 (ZMod q)}
    (hs : s ∈ (ProbComp.eval (sampleAdditiveShare2 q x)).support) :
    s.IsValidFor x := by
  simp only [sampleAdditiveShare2, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_uniform,
    PMF.mem_support_map_iff] at hs
  rcases hs with ⟨x0, _, rfl⟩
  simp [AdditiveShare2.IsValidFor, AdditiveShare2.reconstruct]

/-- Real-world experiment for secret bit `b : Bool` (`x = if b then 1 else 0`): `P₀` samples a
uniform additive sharing of `x`, corrupt `P₁` adds `δ` to its share, and the circuit outputs
`evalShiftedBitCheck s δ`. -/
noncomputable def naiveBitCheckRealExp (q : ℕ) [NeZero q] (δ : ZMod q) (b : Bool) :
    ProbComp (ZMod q) := do
  let x : ZMod q := if b then 1 else 0
  let s ← sampleAdditiveShare2 q x
  return evalShiftedBitCheck s δ

/-- Ideal-world experiment for secret bit `b : Bool` (`x = if b then 1 else 0`): outputs the ideal
evaluation `f(x) = x * (x - 1)` directly. -/
noncomputable def naiveBitCheckIdealExp (q : ℕ) (b : Bool) : ProbComp (ZMod q) := do
  let x : ZMod q := if b then 1 else 0
  return bitCheckPoly x

/-- In `naiveBitCheckRealExp q δ b`, the circuit deterministically outputs `f(x + δ)` regardless
of the random share `x₀`. -/
@[simp] theorem eval_naiveBitCheckRealExp (q : ℕ) [NeZero q] (δ : ZMod q) (b : Bool) :
    ProbComp.eval (naiveBitCheckRealExp q δ b) =
      PMF.pure (bitCheckPoly ((if b then (1 : ZMod q) else 0) + δ)) := by
  simp only [naiveBitCheckRealExp, bind_pure_comp, ProbComp.eval_map]
  calc (ProbComp.eval (sampleAdditiveShare2 q (if b then (1 : ZMod q) else 0))).map
        (fun s => evalShiftedBitCheck s δ)
      = (ProbComp.eval (sampleAdditiveShare2 q (if b then (1 : ZMod q) else 0))).map
          (fun _ => bitCheckPoly ((if b then (1 : ZMod q) else 0) + δ)) := by
          refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun s hs => ?_
          have hval := isValidFor_of_mem_support_sampleAdditiveShare2 hs
          dsimp only [evalShiftedBitCheck]
          rw [s.reconstruct_shiftShare1_of_isValidFor hval]
    _ = PMF.pure (bitCheckPoly ((if b then (1 : ZMod q) else 0) + δ)) := PMF.map_const _ _

/-- In the ideal world, `naiveBitCheckIdealExp q b` outputs `0` identically for both `b = false`
and `b = true`. -/
@[simp] theorem eval_naiveBitCheckIdealExp (q : ℕ) (b : Bool) :
    ProbComp.eval (naiveBitCheckIdealExp q b) = PMF.pure 0 := by
  cases b <;> simp [naiveBitCheckIdealExp, bitCheckPoly]

/-- Distinguisher / bit-extractor for the `δ = 1` attack: outputs `true` iff the circuit output
equals `2`. -/
@[expose] def shiftOneDistinguisher {R : Type} [DecidableEq R] [OfNat R 2] (z : R) : Bool :=
  decide (z = 2)

/-- Left-right distinguishing game in the real world on secret bit `b : Bool` for distinguisher
`D : ZMod q → ProbComp Bool`. -/
noncomputable def naiveBitCheckRealLRGame (q : ℕ) [NeZero q] (δ : ZMod q)
    (D : ZMod q → ProbComp Bool) (b : Bool) : ProbComp Bool := do
  let z ← naiveBitCheckRealExp q δ b
  D z

/-- Left-right distinguishing game in the ideal world on secret bit `b : Bool` for distinguisher
`D : ZMod q → ProbComp Bool`. -/
noncomputable def naiveBitCheckIdealLRGame (q : ℕ)
    (D : ZMod q → ProbComp Bool) (b : Bool) : ProbComp Bool := do
  let z ← naiveBitCheckIdealExp q b
  D z

/-- **Ideal-world indistinguishability:** every randomized distinguisher
`D : ZMod q → ProbComp Bool` has distinguishing advantage `0` between `b = false` (`x = 0`) and
`b = true` (`x = 1`) in the ideal world. -/
theorem advantage_naiveBitCheckIdealLRGame (q : ℕ) (D : ZMod q → ProbComp Bool) :
    Game.advantage
      (ProbComp.eval (naiveBitCheckIdealLRGame q D false))
      (ProbComp.eval (naiveBitCheckIdealLRGame q D true)) = 0 := by
  have heq :
      ProbComp.eval (naiveBitCheckIdealLRGame q D false) =
      ProbComp.eval (naiveBitCheckIdealLRGame q D true) := by
    simp [naiveBitCheckIdealLRGame]
  rw [heq]
  exact Game.advantage_self _

/-- **Real-world advantage `1`:** when `q > 2` is prime, the `δ = 1` shift adversary together with
`shiftOneDistinguisher` distinguishes `b = false` (`x = 0`) from `b = true` (`x = 1`) with
distinguishing advantage `1`. -/
theorem advantage_naiveBitCheckRealLRGame_shiftOne {q : ℕ} [Fact (Nat.Prime q)] (hq : 2 < q) :
    let D : ZMod q → ProbComp Bool := fun z => return shiftOneDistinguisher z
    Game.advantage
      (ProbComp.eval (naiveBitCheckRealLRGame q 1 D false))
      (ProbComp.eval (naiveBitCheckRealLRGame q 1 D true)) = 1 := by
  dsimp only
  have h2 : (2 : ZMod q) ≠ 0 := two_ne_zero_zmod hq
  have hfalse :
      let D : ZMod q → ProbComp Bool := fun z => return shiftOneDistinguisher z
      ProbComp.eval (naiveBitCheckRealLRGame q 1 D false) = PMF.pure false := by
    simp [naiveBitCheckRealLRGame, shiftOneDistinguisher, bitCheckPoly_one, Ne.symm h2]
  have htrue :
      let D : ZMod q → ProbComp Bool := fun z => return shiftOneDistinguisher z
      ProbComp.eval (naiveBitCheckRealLRGame q 1 D true) = PMF.pure true := by
    simp [naiveBitCheckRealLRGame, shiftOneDistinguisher, bitCheckPoly_one_add_one]
  rw [hfalse, htrue, Game.advantage_pure_false_left]
  simp [Game.succProbability]

/-- Hidden-bit recovery game in the real world (`δ = 1`): samples a uniform secret bit
`b ← $ᵗ Bool`, runs the shifted circuit, and checks whether `shiftOneDistinguisher z = b`. -/
noncomputable def naiveBitCheckRealGuessGame (q : ℕ) [NeZero q] : ProbComp Bool := do
  let b ← $ᵗ Bool
  let z ← naiveBitCheckRealExp q 1 b
  return decide (shiftOneDistinguisher z = b)

/-- Hidden-bit recovery game in the ideal world: samples a uniform secret bit `b ← $ᵗ Bool`,
runs the ideal bit-check circuit, and checks whether an arbitrary randomized observer
`A : ZMod q → ProbComp Bool` outputs `b`. -/
noncomputable def naiveBitCheckIdealGuessGame (q : ℕ)
    (A : ZMod q → ProbComp Bool) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let z ← naiveBitCheckIdealExp q b
  let b' ← A z
  return decide (b' = b)

/-- When `q > 2` is prime, the `δ = 1` adversary recovers the uniform secret bit `b` with
probability `1`. -/
theorem probability_naiveBitCheckRealGuessGame {q : ℕ} [Fact (Nat.Prime q)] (hq : 2 < q) :
    Pr[naiveBitCheckRealGuessGame q] = 1 := by
  have h2 : (2 : ZMod q) ≠ 0 := two_ne_zero_zmod hq
  have heval : ProbComp.eval (naiveBitCheckRealGuessGame q) = PMF.pure true := by
    simp only [naiveBitCheckRealGuessGame, ProbComp.eval_bind, ProbComp.eval_uniform,
      eval_naiveBitCheckRealExp, ProbComp.eval_pure, PMF.pure_bind]
    have hfun :
        (fun b : Bool =>
          PMF.pure (decide (shiftOneDistinguisher
            (bitCheckPoly ((if b then (1 : ZMod q) else 0) + 1)) = b))) =
        fun _ : Bool => PMF.pure true := by
      ext b
      cases b <;>
        simp [shiftOneDistinguisher, bitCheckPoly_one, bitCheckPoly_one_add_one, Ne.symm h2]
    rw [hfun]
    exact PMF.bind_const _ (PMF.pure true)
  rw [heval]
  simp

/-- In the ideal world, every randomized observer `A : ZMod q → ProbComp Bool` guesses the
uniform secret bit `b` with probability exactly `1 / 2`. -/
theorem probability_naiveBitCheckIdealGuessGame (q : ℕ) (A : ZMod q → ProbComp Bool) :
    Pr[naiveBitCheckIdealGuessGame q A] = 1 / 2 := by
  have heval :
      (ProbComp.eval (naiveBitCheckIdealGuessGame q A)) true = (2 : ℝ≥0∞)⁻¹ := by
    simp only [naiveBitCheckIdealGuessGame, ProbComp.eval_bind, ProbComp.eval_uniform,
      eval_naiveBitCheckIdealExp, ProbComp.eval_pure, PMF.pure_bind]
    rw [PMF.bind_comm, PMF.bind_apply, tsum_bool]
    have hsum :
        ((ProbComp.eval (A 0)) true + (ProbComp.eval (A 0)) false) = 1 := by
      rw [add_comm, ← tsum_bool]
      exact (ProbComp.eval (A 0)).tsum_coe
    have hguess : ∀ c : Bool,
        ((PMF.uniformOfFintype Bool).bind fun a => PMF.pure (decide (c = a))) true =
          (2 : ℝ≥0∞)⁻¹ := by
      intro c
      rw [PMF.bind_apply, tsum_bool]
      cases c <;> simp [PMF.uniformOfFintype_apply]
    rw [hguess false, hguess true, ← add_mul, add_comm ((ProbComp.eval (A 0)) false),
      hsum, one_mul]
  rw [heval, ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_div]

/-- In the uniform-bit guessing game, the `δ = 1` attack outperforms every ideal-world observer
`A` by distinguishing advantage exactly `1 / 2`. -/
theorem advantage_naiveBitCheckGuessGame {q : ℕ} [Fact (Nat.Prime q)] (hq : 2 < q)
    (A : ZMod q → ProbComp Bool) :
    Game.advantage
      (ProbComp.eval (naiveBitCheckRealGuessGame q))
      (ProbComp.eval (naiveBitCheckIdealGuessGame q A)) = 1 / 2 := by
  apply NNReal.eq
  rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability,
    probability_naiveBitCheckRealGuessGame hq, probability_naiveBitCheckIdealGuessGame q A]
  norm_num

/-! ### 3. Random-MAC input-authentication repair on `SPDZ.AuthShare` -/

/-- The two-party SPDZ authenticated sharing of `x` under MAC key `alpha` with public modifier
`δ = 0`, determined by party `0`'s value share `x₀` and MAC share `t₀`: party `0` holds
`(x₀, t₀)` and party `1` holds `(x - x₀, alpha * x - t₀)`. -/
@[expose] def mkAuthShare2 {q : ℕ} (alpha x x0 t0 : ZMod q) : SPDZ.AuthShare q 2 where
  delta := 0
  valShares := ![x0, x - x0]
  macShares := ![t0, alpha * x - t0]

theorem valid_mkAuthShare2 {q : ℕ} (alpha x x0 t0 : ZMod q) :
    (mkAuthShare2 alpha x x0 t0).Valid alpha := by
  simp [mkAuthShare2, SPDZ.AuthShare.Valid, SPDZ.AuthShare.macSum, SPDZ.AuthShare.secret,
    Fin.sum_univ_two]

/-- Full single-input MAC verification game: samples a uniform MAC key `α ← $ᵗ ZMod q` and a
uniform two-party authenticated sharing of `x` (`mkAuthShare2` with uniform `x₀`, `t₀`), lets
corrupt party `1` add `(δ_x, δ_t)` to its value and MAC shares, and checks the SPDZ MAC relation
`SPDZ.AuthShare.Valid α` (here `t' = α * x'`, since `δ = 0`). -/
noncomputable def macSingleCheckGame (q : ℕ) [NeZero q] (x δ_x δ_t : ZMod q) :
    ProbComp Bool := do
  let alpha ← $ᵗ ZMod q
  let x0 ← $ᵗ ZMod q
  let t0 ← $ᵗ ZMod q
  return decide (((mkAuthShare2 alpha x x0 t0).tamperParty 1 δ_x δ_t).Valid alpha)

/-- `macSingleCheckGame` accepts exactly when the uniform key solves `α * δ_x = δ_t`. -/
private theorem eval_macSingleCheckGame (q : ℕ) [NeZero q] (x δ_x δ_t : ZMod q) :
    ProbComp.eval (macSingleCheckGame q x δ_x δ_t) =
      (PMF.uniformOfFintype (ZMod q)).map fun alpha => decide (alpha * δ_x = δ_t) := by
  simp only [macSingleCheckGame, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  have hbody (alpha x0 t0 : ZMod q) :
      decide (((mkAuthShare2 alpha x x0 t0).tamperParty 1 δ_x δ_t).Valid alpha) =
        decide (alpha * δ_x = δ_t) :=
    decide_eq_decide.mpr (SPDZ.AuthShare.valid_tamperParty_iff (valid_mkAuthShare2 ..) 1 δ_x δ_t)
  simp_rw [hbody, PMF.bind_const]
  rfl

/-- Honest single-input shares (`δ_x = 0`, `δ_t = 0`) pass `macSingleCheckGame` with probability
`1`. -/
theorem probability_macSingleCheckGame_honest (q : ℕ) [NeZero q] (x : ZMod q) :
    Pr[macSingleCheckGame q x 0 0] = 1 := by
  simp [eval_macSingleCheckGame]

/-- **Exact `1 / q` single-input MAC soundness:** for prime `q` and any nonzero input shift
`δ_x ≠ 0`, `macSingleCheckGame q x δ_x δ_t` accepts with probability exactly `1 / q`. -/
theorem probability_macSingleCheckGame_eq {q : ℕ} [Fact (Nat.Prime q)] (x : ZMod q)
    {δ_x δ_t : ZMod q} (hδ : δ_x ≠ 0) :
    Pr[macSingleCheckGame q x δ_x δ_t] = 1 / q := by
  rw [eval_macSingleCheckGame, SPDZ.eval_macKey_guess_eq hδ, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, one_div]

/-! ### 4. Vector of `k` input shares: random-linear-combination and batched MAC checks -/

/-- Two-party vector input sharing of length `k` over `R` authenticated by a single batched
linear-combination MAC tag `t = ∑ j, r j * x j`. -/
@[ext] structure LinearCombAuthVec2 (R : Type) (k : ℕ) where
  /-- Coordinatewise additive sharings `(x_{j,0}, x_{j,1})` of the `k` input elements. -/
  vals : Fin k → AdditiveShare2 R
  /-- Additive sharing `(t₀, t₁)` of the batched linear-combination MAC tag. -/
  tag : AdditiveShare2 R
  deriving DecidableEq, Fintype, Inhabited, Repr

namespace LinearCombAuthVec2

/-- Reconstructed vector of `k` secret inputs `j ↦ x_{j,0} + x_{j,1}`. -/
@[expose] def secretVec {R : Type} [Add R] {k : ℕ} (v : LinearCombAuthVec2 R k) : Fin k → R :=
  fun j => (v.vals j).reconstruct

/-- Reconstructed batched MAC tag `t₀ + t₁`. -/
@[expose] def macTag {R : Type} [Add R] {k : ℕ} (v : LinearCombAuthVec2 R k) : R :=
  v.tag.reconstruct

/-- Validity predicate under linear-combination key `r : Fin k → R`:
`t = ∑ j, r j * x j`. -/
@[expose] def IsValidFor {R : Type} [Semiring R] {k : ℕ}
    (r : Fin k → R) (v : LinearCombAuthVec2 R k) : Prop :=
  v.macTag = ∑ j : Fin k, r j * v.secretVec j

/-- Corrupt party `P₁` adds an offset vector `δ : Fin k → R` to its input shares and `δ_t : R`
to its MAC tag share. -/
@[expose] def tamper1 {R : Type} [Add R] {k : ℕ}
    (v : LinearCombAuthVec2 R k) (δ : Fin k → R) (δ_t : R) : LinearCombAuthVec2 R k :=
  ⟨fun j => (v.vals j).shiftShare1 (δ j), v.tag.shiftShare1 δ_t⟩

/-- **Vector linear-combination tampering equivalence:** when `v` is valid under `r`, the
tampered submission `v.tamper1 δ δ_t` satisfies `t' = ∑ j, r j * x' j` if and only if
`∑ j, r j * δ j = δ_t`. -/
theorem tamper1_isValidFor_iff {R : Type} [CommRing R] {k : ℕ}
    {r : Fin k → R} {v : LinearCombAuthVec2 R k} (hv : v.IsValidFor r)
    (δ : Fin k → R) (δ_t : R) :
    (v.tamper1 δ δ_t).IsValidFor r ↔ ∑ j : Fin k, r j * δ j = δ_t := by
  dsimp only [IsValidFor, tamper1, macTag, secretVec] at hv ⊢
  rw [v.tag.reconstruct_shiftShare1, hv]
  have hsum :
      (∑ j : Fin k, r j * ((v.vals j).shiftShare1 (δ j)).reconstruct) =
        (∑ j : Fin k, r j * (v.vals j).reconstruct) + ∑ j : Fin k, r j * δ j := by
    simp only [AdditiveShare2.reconstruct_shiftShare1, mul_add, Finset.sum_add_distrib]
  rw [hsum]
  exact ⟨fun h => (add_left_cancel h).symm, fun h => by rw [h]⟩

end LinearCombAuthVec2

/-- Sample independent uniform additive shares of `x : Fin k → ZMod q` and of the batched MAC
tag `∑ j, r j * x j`. -/
noncomputable def sampleLinearCombAuthVec2 (q k : ℕ) [NeZero q]
    (r : Fin k → ZMod q) (x : Fin k → ZMod q) :
    ProbComp (LinearCombAuthVec2 (ZMod q) k) := do
  let x0 ← $ᵗ (Fin k → ZMod q)
  let tag ← sampleAdditiveShare2 q (∑ j : Fin k, r j * x j)
  return ⟨fun j => ⟨x0 j, x j - x0 j⟩, tag⟩

/-- Every vector sharing in the support of `sampleLinearCombAuthVec2 q k r x` satisfies
`IsValidFor r`. -/
theorem isValidFor_of_mem_support_sampleLinearCombAuthVec2 {q k : ℕ} [NeZero q]
    {r x : Fin k → ZMod q} {v : LinearCombAuthVec2 (ZMod q) k}
    (hv : v ∈ (ProbComp.eval (sampleLinearCombAuthVec2 q k r x)).support) :
    v.IsValidFor r := by
  simp only [sampleLinearCombAuthVec2, bind_pure_comp, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_uniform, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hv
  rcases hv with ⟨x0, _, tag, htag, rfl⟩
  have htag_valid := isValidFor_of_mem_support_sampleAdditiveShare2 htag
  dsimp only [LinearCombAuthVec2.IsValidFor, LinearCombAuthVec2.macTag,
    LinearCombAuthVec2.secretVec]
  rw [htag_valid]
  congr 1
  ext j
  dsimp only [AdditiveShare2.reconstruct]
  ring

/-- Two-party vector input-consistency game under a fresh uniform linear-combination key
`r ← $ᵗ (Fin k → ZMod q)`: samples `r` and valid additive shares of `x`, applies `P₁`'s
tampering `(δ, δ_t)`, and checks `t' = ∑ j, r j * x' j`. -/
noncomputable def vecLinearCombCheckGame (q k : ℕ) [NeZero q]
    (x δ : Fin k → ZMod q) (δ_t : ZMod q) : ProbComp Bool := do
  let r ← $ᵗ (Fin k → ZMod q)
  let v ← sampleLinearCombAuthVec2 q k r x
  let v' := v.tamper1 δ δ_t
  return decide (v'.macTag = ∑ j : Fin k, r j * v'.secretVec j)

/-- Honest vector shares (`δ = 0`, `δ_t = 0`) pass `vecLinearCombCheckGame` with probability `1`.
-/
theorem probability_vecLinearCombCheckGame_honest (q k : ℕ) [NeZero q]
    (x : Fin k → ZMod q) :
    Pr[vecLinearCombCheckGame q k x 0 0] = 1 := by
  have heval : ProbComp.eval (vecLinearCombCheckGame q k x 0 0) = PMF.pure true := by
    simp only [vecLinearCombCheckGame, bind_pure_comp, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_uniform]
    have hconst :
        (fun r : Fin k → ZMod q =>
          (ProbComp.eval (sampleLinearCombAuthVec2 q k r x)).map
            (fun v => decide ((v.tamper1 0 0).macTag = ∑ j, r j * (v.tamper1 0 0).secretVec j))) =
        fun _ => PMF.pure true := by
      funext r
      calc (ProbComp.eval (sampleLinearCombAuthVec2 q k r x)).map
            (fun v => decide ((v.tamper1 0 0).macTag = ∑ j, r j * (v.tamper1 0 0).secretVec j))
          = (ProbComp.eval (sampleLinearCombAuthVec2 q k r x)).map (fun _ => true) := by
              refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun v hv => ?_
              have hval := isValidFor_of_mem_support_sampleLinearCombAuthVec2 hv
              have hiff := LinearCombAuthVec2.tamper1_isValidFor_iff hval 0 0
              simp only [LinearCombAuthVec2.IsValidFor, Pi.zero_apply, mul_zero,
                Finset.sum_const_zero, iff_true] at hiff
              exact decide_eq_true hiff
        _ = PMF.pure true := PMF.map_const _ true
    rw [hconst]
    exact PMF.bind_const _ (PMF.pure true)
  rw [heval]
  simp

/-- **Exact `1 / q` vector soundness (`ℝ≥0∞`):** for prime `q` and any nonzero tampering vector
`δ ≠ 0`, `vecLinearCombCheckGame q k x δ δ_t` accepts with exact probability `q⁻¹`. -/
theorem eval_vecLinearCombCheckGame_eq {q k : ℕ} [Fact (Nat.Prime q)]
    (x : Fin k → ZMod q) {δ : Fin k → ZMod q} (hδ : δ ≠ 0) (δ_t : ZMod q) :
    (ProbComp.eval (vecLinearCombCheckGame q k x δ δ_t)) true = (q : ℝ≥0∞)⁻¹ := by
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hδ
  have heval :
      ProbComp.eval (vecLinearCombCheckGame q k x δ δ_t) =
        (PMF.uniformOfFintype (Fin k → ZMod q)).map
          (fun r => decide (∑ j : Fin k, r j * δ j = δ_t)) := by
    simp only [vecLinearCombCheckGame, bind_pure_comp, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_uniform, PMF.map]
    refine congrArg _ (funext fun r => ?_)
    calc (ProbComp.eval (sampleLinearCombAuthVec2 q k r x)).bind
          (fun v => PMF.pure (decide ((v.tamper1 δ δ_t).macTag =
            ∑ j, r j * (v.tamper1 δ δ_t).secretVec j)))
        = (ProbComp.eval (sampleLinearCombAuthVec2 q k r x)).map
            (fun v => decide ((v.tamper1 δ δ_t).macTag =
              ∑ j, r j * (v.tamper1 δ δ_t).secretVec j)) := by
            rw [PMF.map]; rfl
      _ = (ProbComp.eval (sampleLinearCombAuthVec2 q k r x)).map
            (fun _ => decide (∑ j : Fin k, r j * δ j = δ_t)) := by
            refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun v hv => ?_
            have hval := isValidFor_of_mem_support_sampleLinearCombAuthVec2 hv
            exact decide_eq_decide.mpr
              (LinearCombAuthVec2.tamper1_isValidFor_iff hval δ δ_t)
      _ = PMF.pure (decide (∑ j : Fin k, r j * δ j = δ_t)) := PMF.map_const _ _
  rw [heval, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  have hpre :
      ((fun r : Fin k → ZMod q => decide (∑ j : Fin k, r j * δ j = δ_t)) ⁻¹' {true}) =
      {r : Fin k → ZMod q | ∑ j : Fin k, r j * δ j = δ_t} := by
    ext r
    simp
  rw [hpre, toOuterMeasure_uniform_linearComb_eq hj₀ δ_t, ZMod.card, one_div]

/-- Real-valued exact `1 / q` soundness for `vecLinearCombCheckGame` when `δ ≠ 0`. -/
theorem probability_vecLinearCombCheckGame_eq {q k : ℕ} [Fact (Nat.Prime q)]
    (x : Fin k → ZMod q) {δ : Fin k → ZMod q} (hδ : δ ≠ 0) (δ_t : ZMod q) :
    Pr[vecLinearCombCheckGame q k x δ δ_t] = 1 / q := by
  rw [eval_vecLinearCombCheckGame_eq x hδ δ_t, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

/-- Batched MAC verification predicate for `k` SPDZ authenticated shares under global MAC key `α`
and random linear-combination weights `r : Fin k → ZMod p`:
`∑ j, r j * γ_j = α * ∑ j, r j * (a_j + δ_j)`, the MAC relation `SPDZ.AuthShare.Valid α` of the
`r`-weighted combination of the shares. -/
@[expose] def batchMacCheckPasses {p n k : ℕ} (alpha : ZMod p) (r : Fin k → ZMod p)
    (s : Fin k → SPDZ.AuthShare p n) : Prop :=
  ∑ j : Fin k, r j * (s j).macSum = alpha * ∑ j : Fin k, r j * ((s j).secret + (s j).delta)

instance {p n k : ℕ} (alpha : ZMod p) (r : Fin k → ZMod p) (s : Fin k → SPDZ.AuthShare p n) :
    Decidable (batchMacCheckPasses alpha r s) :=
  inferInstanceAs (Decidable (_ = _))

/-- **Batched scalar-MAC tampering equivalence:** when every `s j` is valid under `α`, party `i`'s
tampering by `(δ_x, δ_t)` passes `batchMacCheckPasses alpha r` if and only if
`α * ∑ j, r j * δ_x j = ∑ j, r j * δ_t j`. -/
theorem batchMacCheckPasses_tamperParty_iff {p n k : ℕ} {alpha : ZMod p}
    {s : Fin k → SPDZ.AuthShare p n} (hs : ∀ j : Fin k, (s j).Valid alpha) (i : Fin n)
    (r δ_x δ_t : Fin k → ZMod p) :
    batchMacCheckPasses alpha r (fun j => (s j).tamperParty i (δ_x j) (δ_t j)) ↔
      alpha * ∑ j : Fin k, r j * δ_x j = ∑ j : Fin k, r j * δ_t j := by
  have hsum : ∑ j : Fin k, r j * (s j).macSum =
      alpha * ∑ j : Fin k, r j * ((s j).secret + (s j).delta) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hs j]; ring
  have htag : ∑ j : Fin k, r j * ((s j).macSum + δ_t j) =
      ∑ j : Fin k, r j * (s j).macSum + ∑ j : Fin k, r j * δ_t j := by
    simp only [mul_add, Finset.sum_add_distrib]
  have hval : alpha * ∑ j : Fin k, r j * ((s j).secret + δ_x j + (s j).delta) =
      alpha * ∑ j : Fin k, r j * ((s j).secret + (s j).delta) +
        alpha * ∑ j : Fin k, r j * δ_x j := by
    rw [← mul_add, ← Finset.sum_add_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)
  simp only [batchMacCheckPasses, SPDZ.AuthShare.macSum_tamperParty,
    SPDZ.AuthShare.secret_tamperParty, SPDZ.AuthShare.delta_tamperParty]
  rw [htag, hval, hsum]
  exact ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩

/-- Batched `k`-share MAC check game: samples a fresh uniform MAC key `α ← $ᵗ ZMod q` and fresh
uniform linear-combination weights `r ← $ᵗ (Fin k → ZMod q)`, generates uniform two-party
authenticated sharings `mkAuthShare2` of each `x j`, lets corrupt party `1` add `(δ_x j, δ_t j)` to
its shares of the `j`-th input, and checks `batchMacCheckPasses alpha r`. -/
noncomputable def vecBatchMacCheckGame (q k : ℕ) [NeZero q]
    (x δ_x δ_t : Fin k → ZMod q) : ProbComp Bool := do
  let alpha ← $ᵗ ZMod q
  let r ← $ᵗ (Fin k → ZMod q)
  let x0 ← $ᵗ (Fin k → ZMod q)
  let t0 ← $ᵗ (Fin k → ZMod q)
  return decide (batchMacCheckPasses alpha r fun j =>
    (mkAuthShare2 alpha (x j) (x0 j) (t0 j)).tamperParty 1 (δ_x j) (δ_t j))

/-- `vecBatchMacCheckGame` has the output distribution of the standalone `MACCheck`
cheating-equation game `SPDZ.macCheckSoundnessGame` with opening errors `δ_x` and residual shift
`r ↦ ∑ j, r j * δ_t j`. -/
private theorem eval_vecBatchMacCheckGame (q k : ℕ) [NeZero q] (x δ_x δ_t : Fin k → ZMod q) :
    ProbComp.eval (vecBatchMacCheckGame q k x δ_x δ_t) =
      ProbComp.eval (SPDZ.macCheckSoundnessGame q k δ_x fun r => ∑ j : Fin k, r j * δ_t j) := by
  simp only [vecBatchMacCheckGame, SPDZ.macCheckSoundnessGame, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbComp.eval_pure]
  have hbody (alpha : ZMod q) (r x0 t0 : Fin k → ZMod q) :
      decide (batchMacCheckPasses alpha r fun j =>
          (mkAuthShare2 alpha (x j) (x0 j) (t0 j)).tamperParty 1 (δ_x j) (δ_t j)) =
        decide (alpha * linearCombAddHom δ_x r = ∑ j : Fin k, r j * δ_t j) := by
    rw [linearCombAddHom_apply]
    exact decide_eq_decide.mpr
      (batchMacCheckPasses_tamperParty_iff (fun j => valid_mkAuthShare2 ..) 1 r δ_x δ_t)
  simp_rw [hbody, PMF.bind_const]

/-- Honest shares (`δ_x = 0`, `δ_t = 0`) pass `vecBatchMacCheckGame` with probability `1`. -/
theorem probability_vecBatchMacCheckGame_honest (q k : ℕ) [NeZero q]
    (x : Fin k → ZMod q) :
    Pr[vecBatchMacCheckGame q k x 0 0] = 1 := by
  simp [eval_vecBatchMacCheckGame, SPDZ.macCheckSoundnessGame]

/-- **Batched `k`-share scalar-MAC soundness (`≤ 2 / q`):** for prime `q` and any nonzero input
tampering vector `δ_x ≠ 0`, `vecBatchMacCheckGame q k x δ_x δ_t` passes with probability at most
`2 / q`; this is `SPDZ.probability_macCheckSoundnessGame_le` applied to the cheating equation the
tampering induces. -/
theorem probability_vecBatchMacCheckGame_le {q k : ℕ} [Fact (Nat.Prime q)]
    (x : Fin k → ZMod q) {δ_x : Fin k → ZMod q} (hδ : δ_x ≠ 0) (δ_t : Fin k → ZMod q) :
    Pr[vecBatchMacCheckGame q k x δ_x δ_t] ≤ 2 / q := by
  rw [eval_vecBatchMacCheckGame]
  exact SPDZ.probability_macCheckSoundnessGame_le hδ _

end Cslib.Crypto.Protocols.MPC.InputConsistency
