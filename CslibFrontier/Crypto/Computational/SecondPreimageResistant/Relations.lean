/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CollisionResistantToOneWay
public import CslibFrontier.Crypto.Computational.FlipHeadBit
public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Crypto.Computational.SecondPreimageResistant
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible
import CslibFrontier.Probability.Guessing.UniformList
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Implications and separations for second-preimage resistance

This module formalizes the hierarchy
$$\text{collision resistance} \implies
  \text{second-preimage resistance} \implies \text{one-wayness}$$
of [BonehShoup2023], Section 8.11.1, equation (8.17), p. 337, together with Exercise 8.23(b)–(d),
p. 353, and the two strict-separation constructions on bit strings:

* **Second-preimage resistance implies one-wayness under super-polynomial compression**
  ((8.17), second arrow, and Exercise 8.23(b) on bit strings):
  `inverterToSecondPreimage f adversary` feeds `f m` to an `Inverter`, with
  `isPPT_inverterToSecondPreimage`, concrete bounds
  `succProbability_inversionGame_le_secondPreimageGameOn_add` and
  `succProbability_inversionGame_le_two_mul_secondPreimageGameOn_add`, and asymptotic implication
  `SecondPreimageResistantOn.oneWay_of_outputLength` when `2 ^ outLen n / 2 ^ n` is negligible and
  `hpre : ∀ n x x', x.length = n → f x' = f x → valid n x' = true` holds. Because `OneWay` accepts
  arbitrary-length preimages, `hpre` rules out `valid n x' := decide (x'.length = n)` for functions
  with cross-length collisions such as `CollisionResistantToOneWay.keyDigest H`, so the `(8.17)`
  chain passes through any-length `SecondPreimageResistant` (`valid := fun _ _ => true`), where
  `hpre` is vacuous (`rfl`).
* **Collision resistance implies second-preimage resistance** ((8.17), first arrow, and
  Exercise 8.23(d)): the book states this for an unkeyed collision-resistant hash `H`; because
  `HashFamily H` is keyed with `(H key message).length = key.length`,
  `secondPreimageToCollisionFinder adversary r` turns a second-preimage finder for
  `CollisionResistantToOneWay.keyDigest H` at length `3 * n + r` into a `CollisionFinder` for `H`
  at parameter `n` (`isPPT_secondPreimageToCollisionFinder`), with exact zero-loss bound
  `succProbability_secondPreimageGame_keyDigest_le` and asymptotic implication
  `HashFamily.secondPreimageResistant_keyDigest`.
* **One-wayness does not imply second-preimage resistance** ([BonehShoup2023], Section 8.11.1,
  p. 337): `ignoreHeadBit f w = f w.tail` preserves `OneWay` (`OneWay.ignoreHeadBit`, via
  `ignoreHeadBitInverter` and `isPPT_ignoreHeadBitInverter`) while flipping the head bit
  (`flipHeadBit`) wins `secondPreimageGameOn` with probability `1`
  (`not_secondPreimageResistantOn_ignoreHeadBit`).
* **Second-preimage resistance does not imply one-wayness at bounded compression**
  ([BonehShoup2023], Exercise 8.23(c), p. 353, on bit strings): `plantEasyBranch k H` outputs
  `true :: w.drop k` when `w.take k == List.replicate k false` and `false :: H w` otherwise (with
  output lengths tracked by `length_plantEasyBranch`), preserving `SecondPreimageResistantOn` (and
  thus `SecondPreimageResistant`) via `SecondPreimageResistantOn.plantEasyBranch` while failing
  `OneWay` with inversion probability at least `(1 / 2) ^ k` (`not_oneWay_plantEasyBranch`, via
  `plantEasyBranchInverter` and `isPPT_plantEasyBranchInverter`).

## Main definitions

* `Cslib.Crypto.inverterToSecondPreimage`: wrap an `Inverter` into a `SecondPreimageFinder`.
* `Cslib.Crypto.secondPreimageToCollisionFinder`: reduction from
  `secondPreimageGame (keyDigest H)` to `collisionGame H`.
* `Cslib.Crypto.ignoreHeadBit`, `Cslib.Crypto.ignoreHeadBitInverter`:
  the Section 8.11.1 separation construction and its reductions (re-exporting
  `Cslib.Crypto.flipHeadBit` from `CslibFrontier.Crypto.Computational.FlipHeadBit`).
* `Cslib.Crypto.plantEasyBranch`, `Cslib.Crypto.plantEasyBranchInverter`: the bit-string form of
  Exercise 8.23(c) and its inverter.

## Main results

* `Cslib.Crypto.isPPT_inverterToSecondPreimage`,
  `Cslib.Crypto.succProbability_inversionGame_le_secondPreimageGameOn_add`,
  `Cslib.Crypto.succProbability_inversionGame_le_two_mul_secondPreimageGameOn_add`,
  `Cslib.Crypto.SecondPreimageResistantOn.oneWay_of_outputLength`.
* `Cslib.Crypto.isPPT_secondPreimageToCollisionFinder`,
  `Cslib.Crypto.succProbability_secondPreimageGame_keyDigest_le`,
  `Cslib.Crypto.HashFamily.secondPreimageResistant_keyDigest`.
* `Cslib.Crypto.not_secondPreimageResistantOn_ignoreHeadBit`,
  `Cslib.Crypto.isPPT_ignoreHeadBitInverter`, `Cslib.Crypto.OneWay.ignoreHeadBit`.
* `Cslib.Crypto.length_plantEasyBranch`,
  `Cslib.Crypto.SecondPreimageResistantOn.plantEasyBranch`,
  `Cslib.Crypto.isPPT_plantEasyBranchInverter`, `Cslib.Crypto.not_oneWay_plantEasyBranch`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 8.11.1 (equation (8.17), p. 337) and Exercise 8.23(b)–(d) (p. 353).
-/

public section

namespace Cslib.Crypto

open ProbComp Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ## Second-preimage resistance implies one-wayness under super-polynomial compression -/

/-- Wrap an inverter `adversary` into a second-preimage finder by feeding it `f m`
([BonehShoup2023], Exercise 8.23(b), p. 353). -/
def inverterToSecondPreimage (f : List Bool → List Bool) (adversary : Inverter) :
    SecondPreimageFinder :=
  fun n m => adversary n (f m)

/-- Evaluating `f` and running a strict PPT inverter is uniformly strict PPT. -/
@[program_certificate]
theorem isPPT_inverterToSecondPreimage {f : List Bool → List Bool} {adversary : Inverter}
    (hf : ComputableInPolyTime f encBits encBits) (ha : IsPPT encBits adversary) :
    IsPPT encBits (inverterToSecondPreimage f adversary) := by
  unfold inverterToSecondPreimage
  ppt

/-- **Reduction from valid-domain second-preimage search to one-way inversion**: when `f` maps
`n`-bit inputs to `d`-bit digests and every collision with an `n`-bit input lands in `valid n`,
an inverter `adversary` at length `n` succeeds with probability at most
`SPRadvOn[B, f] + 2 ^ d / 2 ^ n`.

The extra hypothesis `hpre` is required because `inversionGame` accepts preimages of arbitrary bit
length while `secondPreimageGameOn` enforces `valid n x'`. It holds automatically for any-length
`valid := fun _ _ => true` (`SecondPreimageResistant`), whereas it fails on `{0,1}ⁿ` for
functions with cross-length collisions such as `CollisionResistantToOneWay.keyDigest H`. -/
theorem succProbability_inversionGame_le_secondPreimageGameOn_add
    {f : List Bool → List Bool} {valid : ℕ → List Bool → Bool} {n d : ℕ}
    (hlen : ∀ w : List Bool, w.length = n → (f w).length = d)
    (hpre : ∀ x x' : List Bool, x.length = n → f x' = f x → valid n x' = true)
    (adversary : Inverter) :
    Game.succProbability (ProbComp.eval (inversionGame f adversary n)) ≤
      Game.succProbability
        (ProbComp.eval (secondPreimageGameOn f valid (inverterToSecondPreimage f adversary) n)) +
        (2 : ℝ≥0) ^ d / (2 : ℝ≥0) ^ n := by
  have hsplit :
      ProbComp.eval (inversionGame f adversary n) true ≤
        ProbComp.eval (secondPreimageGame f (inverterToSecondPreimage f adversary) n) true +
          ∑' m, BitString.uniformList n m * ProbComp.eval (adversary n (f m)) m := by
    simpa only [inversionGame, secondPreimageGame, inverterToSecondPreimage,
      ProbComp.eval_inversionExperiment, ProbComp.eval_secondPreimageExperiment,
      BitString.eval_sampleList] using
      inversionExperiment_le_secondPreimageExperiment_add (BitString.uniformList n) f
        fun y => ProbComp.eval (adversary n y)
  have hguess :
      ∑' m, BitString.uniformList n m * ProbComp.eval (adversary n (f m)) m ≤
        (((2 : ℝ≥0) ^ d / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) := by
    refine (PMF.tsum_uniformList_mul_apply_le f hlen
      (fun y => ProbComp.eval (adversary n y))).trans_eq ?_
    rw [ENNReal.coe_div (pow_ne_zero n two_ne_zero), ENNReal.coe_pow, ENNReal.coe_pow,
      ENNReal.coe_ofNat, one_div, div_eq_mul_inv]
  have hkey :
      ProbComp.eval (inversionGame f adversary n) true ≤
        ProbComp.eval (secondPreimageGame f (inverterToSecondPreimage f adversary) n) true +
          (((2 : ℝ≥0) ^ d / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) :=
    hsplit.trans (add_le_add le_rfl hguess)
  have hbase :
      Game.succProbability (ProbComp.eval (inversionGame f adversary n)) ≤
        Game.succProbability
          (ProbComp.eval (secondPreimageGame f (inverterToSecondPreimage f adversary) n)) +
          (2 : ℝ≥0) ^ d / (2 : ℝ≥0) ^ n := by
    unfold Game.succProbability
    refine (ENNReal.toNNReal_mono
      (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, ENNReal.coe_ne_top⟩) hkey).trans_eq ?_
    rw [ENNReal.toNNReal_add (PMF.apply_ne_top _ _) ENNReal.coe_ne_top, ENNReal.toNNReal_coe]
  have hle :
      Game.succProbability
          (ProbComp.eval (secondPreimageGame f (inverterToSecondPreimage f adversary) n)) ≤
        Game.succProbability
          (ProbComp.eval
            (secondPreimageGameOn f valid (inverterToSecondPreimage f adversary) n)) := by
    rw [secondPreimageGame_eq_secondPreimageGameOn]
    exact succProbability_secondPreimageGameOn_le_of_imp
      (fun x x' hx _ _ hfx => ⟨hpre x x' hx hfx, hfx⟩) _
  exact hbase.trans (add_le_add hle le_rfl)

/-- **Exercise 8.23(b), equation (8.22) on bit strings** ([BonehShoup2023], p. 353) for
`secondPreimageGameOn`: with compression factor `s = 2 ^ n / 2 ^ d` and valid preimages,
`OWadv[A, f] ≤ 2 · SPRadvOn[B, f] + 2 ^ d / 2 ^ n`. -/
theorem succProbability_inversionGame_le_two_mul_secondPreimageGameOn_add
    {f : List Bool → List Bool} {valid : ℕ → List Bool → Bool} {n d : ℕ}
    (hlen : ∀ w : List Bool, w.length = n → (f w).length = d)
    (hpre : ∀ x x' : List Bool, x.length = n → f x' = f x → valid n x' = true)
    (adversary : Inverter) :
    Game.succProbability (ProbComp.eval (inversionGame f adversary n)) ≤
      2 * Game.succProbability
        (ProbComp.eval (secondPreimageGameOn f valid (inverterToSecondPreimage f adversary) n)) +
        (2 : ℝ≥0) ^ d / (2 : ℝ≥0) ^ n :=
  (succProbability_inversionGame_le_secondPreimageGameOn_add hlen hpre adversary).trans
    (add_le_add (le_mul_of_one_le_left zero_le one_le_two) le_rfl)

/-- **Equation (8.17), second implication, and Exercise 8.23(b)** ([BonehShoup2023], pp. 337, 353):
a function that is second-preimage resistant on `valid`, whose `n`-bit inputs have `outLen n`-bit
digests with `2 ^ outLen n / 2 ^ n` negligible (super-polynomial compression factor
`s(n) = 2 ^ n / 2 ^ outLen n`), and whose collisions with `n`-bit inputs satisfy `valid n` (`hpre`),
is one-way.

Note the `hpre` deviation: because `OneWay` accepts preimages of any bit length, `hpre` is needed
whenever `valid` restricts answer lengths; it holds trivially (`fun _ _ _ _ _ => rfl`) for the
any-length specialization `SecondPreimageResistant f` (`valid := fun _ _ => true`), whereas it
fails on `{0,1}ⁿ` for functions with cross-length collisions such as `keyDigest H`. -/
theorem SecondPreimageResistantOn.oneWay_of_outputLength
    {f : List Bool → List Bool} {valid : ℕ → List Bool → Bool} {outLen : ℕ → ℕ}
    (hf : SecondPreimageResistantOn f valid)
    (hlen : ∀ n (w : List Bool), w.length = n → (f w).length = outLen n)
    (hpre : ∀ n (x x' : List Bool), x.length = n → f x' = f x → valid n x' = true)
    (hcomp : Negligible (fun n => (2 : ℝ≥0) ^ outLen n / (2 : ℝ≥0) ^ n)) :
    OneWay f := by
  refine OneWay.of_inversion_negligible hf.polyTime fun adversary hadversary => ?_
  have hspr := hf.negligible (inverterToSecondPreimage f adversary)
    (isPPT_inverterToSecondPreimage hf.polyTime hadversary)
  exact negligible_of_le (hspr.add_fun hcomp) fun n =>
    succProbability_inversionGame_le_secondPreimageGameOn_add (hlen n) (hpre n) adversary

/-! ## Collision resistance implies second-preimage resistance (Exercise 8.23(d) and (8.17)) -/

/-- Turn a second-preimage finder for `CollisionResistantToOneWay.keyDigest H` at input length
`3 * n + r` into a `CollisionFinder` for `H` at security parameter `n` by sampling a random
`(2 * n + r)`-bit message `x` and pairing `x` with the message part of the finder's answer. -/
noncomputable def secondPreimageToCollisionFinder (adversary : SecondPreimageFinder)
    (r : ℕ) : CollisionFinder := fun n key => do
  let message ← BitString.sampleList (2 * n + r)
  let candidate ← adversary (3 * n + r) (key ++ message)
  return (message, candidate.drop (candidate.length / 3))

/-- Sampling a `(2 * n + r)`-bit message, running `adversary (3 * n + r)`, and slicing the answer
is uniformly strict PPT. -/
@[program_certificate]
theorem isPPT_secondPreimageToCollisionFinder {adversary : SecondPreimageFinder}
    (hadversary : IsPPT encBits adversary) (r : ℕ) :
    IsPPT (encPair encBits encBits) (secondPreimageToCollisionFinder adversary r) := by
  unfold secondPreimageToCollisionFinder
  ppt

/-- A second preimage `candidate ≠ key ++ message` of `key ++ message` under `keyDigest H` has the
same key `key` and a colliding message part `candidate.drop (candidate.length / 3) ≠ message`. -/
theorem isCollision_of_keyDigest_secondPreimage {H : List Bool → List Bool → List Bool}
    (hlen : ∀ key message, (H key message).length = key.length) (n : ℕ)
    {candidate key message : List Bool} {r : ℕ}
    (hmessage : message.length = 2 * key.length + r) (hr : r < 3)
    (hne : candidate ≠ key ++ message)
    (h : CollisionResistantToOneWay.keyDigest H candidate =
      CollisionResistantToOneWay.keyDigest H (key ++ message)) :
    isCollision H (fun _ _ => true) n key message
      (candidate.drop (candidate.length / 3)) = true := by
  rw [CollisionResistantToOneWay.keyDigest_append H hmessage hr] at h
  rcases CollisionResistantToOneWay.isCollision_or_eq_of_keyDigest_eq hlen n h with hcol | heq
  · exact hcol
  · exfalso
    apply hne
    simp only [CollisionResistantToOneWay.keyDigest] at h
    have hlength := congrArg List.length h
    simp only [List.length_append, hlen] at hlength
    obtain ⟨hkey, _⟩ := List.append_inj h (by omega)
    calc
      candidate =
          candidate.take (candidate.length / 3) ++ candidate.drop (candidate.length / 3) :=
        (List.take_append_drop _ _).symm
      _ = key ++ message := by rw [hkey, heq]

/-- **Exercise 8.23(d), concrete bound for `keyDigest H`**: finding a second preimage of
`keyDigest H` at length `3 * n + r` with `r < 3` succeeds at most as often as
`secondPreimageToCollisionFinder adversary r` finds a collision for `H` at parameter `n`, with no
guessing loss. -/
theorem succProbability_secondPreimageGame_keyDigest_le
    {H : List Bool → List Bool → List Bool}
    (hlen : ∀ key message, (H key message).length = key.length)
    (adversary : SecondPreimageFinder) (n r : ℕ) (hr : r < 3) :
    Game.succProbability
      (ProbComp.eval
        (secondPreimageGame (CollisionResistantToOneWay.keyDigest H) adversary (3 * n + r))) ≤
      Game.succProbability
        (ProbComp.eval
          (collisionGame H (fun _ _ => true) (secondPreimageToCollisionFinder adversary r) n)) := by
  have hsplit : BitString.uniformList (3 * n + r) = (BitString.uniformList n).bind
      (fun key => (BitString.uniformList (2 * n + r)).map (key ++ ·)) := by
    rw [show 3 * n + r = n + (2 * n + r) by ring]
    exact BitString.uniformList_add n (2 * n + r)
  apply Game.succProbability_mono
  simp only [secondPreimageGame, secondPreimageExperiment, collisionGame,
    secondPreimageToCollisionFinder, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, hsplit, PMF.bind_bind, PMF.bind_map, PMF.pure_bind,
    Function.comp_def]
  refine PMF.bind_apply_mono_on_support _ _ fun key hkey => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun message hmessage => ?_
  have hklen := BitString.length_of_mem_support_uniformList hkey
  have hmlen := BitString.length_of_mem_support_uniformList hmessage
  refine PMF.bind_apply_mono_on_support _ _ fun candidate _ => ?_
  cases hwin :
      ((candidate != key ++ message) &&
        (CollisionResistantToOneWay.keyDigest H candidate ==
          CollisionResistantToOneWay.keyDigest H (key ++ message)))
  · simp
  · rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hwin
    rw [isCollision_of_keyDigest_secondPreimage hlen n (by rw [hmlen, hklen]) hr hwin.1 hwin.2]

/-- **Equation (8.17), first implication, and Exercise 8.23(d)** ([BonehShoup2023], pp. 337, 353):
for a keyed collision-resistant hash family `H` with `(H key message).length = key.length`,
`CollisionResistantToOneWay.keyDigest H` replaces the book's unkeyed `H` and is second-preimage
resistant (and hence also `SecondPreimageResistantOn (keyDigest H) valid` for any `valid` via
`SecondPreimageResistantOn.mono`). -/
theorem HashFamily.secondPreimageResistant_keyDigest
    {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    SecondPreimageResistant (CollisionResistantToOneWay.keyDigest H) := by
  refine SecondPreimageResistantOn.of_negligible
    (CollisionResistantToOneWay.polyTime_keyDigest hH.polyTime)
    fun adversary hadversary => ?_
  have hcol (r : ℕ) := CollisionResistantOn.negligible hH.collisionResistant _
    (isPPT_secondPreimageToCollisionFinder hadversary r)
  have hε := (((hcol 0).add_fun (hcol 1)).add_fun (hcol 2)).div_const (by norm_num : 0 < 3)
  refine negligible_of_le hε fun N => ?_
  obtain ⟨n, r, hr, rfl⟩ : ∃ n r, r < 3 ∧ N = 3 * n + r :=
    ⟨N / 3, N % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod N 3).symm⟩
  rw [show (3 * n + r) / 3 = n by omega, ← secondPreimageGame_eq_secondPreimageGameOn]
  refine (succProbability_secondPreimageGame_keyDigest_le hH.length_eq adversary n r hr).trans ?_
  interval_cases r
  · exact le_add_right (le_add_right le_rfl)
  · exact le_add_right (le_add_left le_rfl)
  · exact le_add_left le_rfl

/-! ## Separations: one-way does not imply second-preimage resistant, and Exercise 8.23(c) -/

/-- Drop the first bit before applying `f`: the bit-string form of `h'(m, b) := h(m)` from
[BonehShoup2023], Section 8.11.1, p. 337. -/
@[expose]
def ignoreHeadBit (f : List Bool → List Bool) (w : List Bool) : List Bool :=
  f w.tail

@[fun_prop]
theorem computableInPolyTime_ignoreHeadBit {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) :
    ComputableInPolyTime (ignoreHeadBit f) encBits encBits := by
  unfold ignoreHeadBit
  polytime

/-- **Section 8.11.1 separation, negative half** ([BonehShoup2023], p. 337) for
`SecondPreimageResistantOn`: for every `f` and every validity predicate `valid` admitting
`flipHeadBit` on sufficiently large `n`-bit inputs (including `fun n w => decide (w.length = n)`),
`ignoreHeadBit f` is not second-preimage resistant on `valid`. -/
theorem not_secondPreimageResistantOn_ignoreHeadBit (f : List Bool → List Bool)
    {valid : ℕ → List Bool → Bool}
    (hvalid : ∀ᶠ n in Filter.atTop, ∀ x : List Bool, x.length = n →
      valid n (flipHeadBit x) = true) :
    ¬ SecondPreimageResistantOn (ignoreHeadBit f) valid := by
  refine not_secondPreimageResistantOn_of_le_succProbability one_ne_zero
    (fun _ w => pure (flipHeadBit w)) computableInPolyTime_flipHeadBit.isPPT ?_
  filter_upwards [hvalid] with n hvn
  rw [succProbability_secondPreimageGameOn_pure_eq_one
    fun x hx => ⟨hvn x hx, flipHeadBit_ne_self x, rfl⟩]

/-- Inverter for `f` at length `n` built from an inverter for `ignoreHeadBit f` at length `n + 1`:
run `adversary (n + 1)` and take the tail of its candidate preimage. -/
def ignoreHeadBitInverter (adversary : Inverter) : Inverter :=
  fun n y => List.tail <$> adversary (n + 1) y

@[program_certificate]
theorem isPPT_ignoreHeadBitInverter {adversary : Inverter} (ha : IsPPT encBits adversary) :
    IsPPT encBits (ignoreHeadBitInverter adversary) := by
  unfold ignoreHeadBitInverter
  ppt

/-- Inverting `ignoreHeadBit f` at length `n + 1` has the exact same success distribution as
inverting `f` at length `n` via `ignoreHeadBitInverter adversary`. -/
theorem eval_inversionGame_ignoreHeadBit_succ (f : List Bool → List Bool)
    (adversary : Inverter) (n : ℕ) :
    ProbComp.eval (inversionGame (ignoreHeadBit f) adversary (n + 1)) =
      ProbComp.eval (inversionGame f (ignoreHeadBitInverter adversary) n) := by
  simp only [inversionGame, inversionExperiment, ignoreHeadBit, ignoreHeadBitInverter,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map, BitString.eval_sampleList,
    BitString.uniformList_succ, PMF.bind_bind, PMF.bind_map, Function.comp_def, List.tail_cons,
    PMF.bind_const]

/-- **Section 8.11.1 separation, positive half** ([BonehShoup2023], p. 337): if `f` is one-way,
then `ignoreHeadBit f` is also one-way (while failing second-preimage resistance by
`not_secondPreimageResistantOn_ignoreHeadBit`). -/
theorem OneWay.ignoreHeadBit {f : List Bool → List Bool} (hf : OneWay f) :
    OneWay (Cslib.Crypto.ignoreHeadBit f) := by
  refine OneWay.of_inversion_negligible (computableInPolyTime_ignoreHeadBit hf.polyTime)
    fun adversary hadversary => ?_
  have hinv := hf.inversion_negligible (ignoreHeadBitInverter adversary)
    (isPPT_ignoreHeadBitInverter hadversary)
  have hshift :
      Negligible (fun N =>
        Game.succProbability
          (ProbComp.eval (inversionGame f (ignoreHeadBitInverter adversary) (N - 1)))) :=
    hinv.comp_of_polynomial_bound (bound := fun m => m + 1)
      (Filter.tendsto_sub_atTop_nat 1) (by fun_prop)
      (Filter.Eventually.of_forall fun N => by omega)
  refine negligible_of_eventually_le hshift ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel, eval_inversionGame_ignoreHeadBit_succ, le_rfl]

/-- The bit-string form of Exercise 8.23(c) ([BonehShoup2023], p. 353): when the first `k` bits of
`w` are all `false` (probability `1 / 2 ^ k` at length `n ≥ k`, so `1 / (2 * s)` with
`2 * s = 2 ^ k`), output `true :: w.drop k`; otherwise output `false :: H w`. -/
@[expose]
def plantEasyBranch (k : ℕ) (H : List Bool → List Bool) (w : List Bool) : List Bool :=
  if w.take k == List.replicate k false then
    true :: w.drop k
  else
    false :: H w

@[fun_prop]
theorem computableInPolyTime_plantEasyBranch (k : ℕ) {H : List Bool → List Bool}
    (hH : ComputableInPolyTime H encBits encBits) :
    ComputableInPolyTime (plantEasyBranch k H) encBits encBits := by
  unfold plantEasyBranch
  polytime

/-- Output length of `plantEasyBranch k H w`: when the first `k` bits of `w` are `false`, it has
length `w.length - k + 1`; otherwise `(H w).length + 1`. Thus if `H` compresses `n`-bit inputs
by `k` bits for `n ≥ k`, `plantEasyBranch k H` compresses `n`-bit inputs by `k - 1` bits. -/
theorem length_plantEasyBranch (k : ℕ) (H : List Bool → List Bool) (w : List Bool) :
    (plantEasyBranch k H w).length =
      if w.take k == List.replicate k false then w.length - k + 1 else (H w).length + 1 := by
  unfold plantEasyBranch
  split_ifs <;> simp

/-- Every second preimage under `plantEasyBranch k H` is a second preimage under `H`: any word
whose first `k` bits are `false` is uniquely determined by `plantEasyBranch k H w`. -/
theorem eq_of_plantEasyBranch_eq (k : ℕ) (H : List Bool → List Bool)
    {w w' : List Bool} (hne : w' ≠ w)
    (heq : plantEasyBranch k H w' = plantEasyBranch k H w) :
    H w' = H w := by
  unfold plantEasyBranch at heq
  split_ifs at heq with hw' hw
  · exfalso
    apply hne
    rw [beq_iff_eq] at hw' hw
    calc
      w' = w'.take k ++ w'.drop k := (List.take_append_drop k w').symm
      _ = w.take k ++ w.drop k := by rw [hw', hw, (List.cons.inj heq).2]
      _ = w := List.take_append_drop k w
  · cases heq
  · cases heq
  · exact (List.cons.inj heq).2

/-- For every second-preimage finder `adversary`, its valid-domain success probability against
`plantEasyBranch k H` is at most its valid-domain success probability against `H`. -/
theorem succProbability_secondPreimageGameOn_plantEasyBranch_le
    (k : ℕ) (H : List Bool → List Bool) (valid : ℕ → List Bool → Bool)
    (adversary : SecondPreimageFinder) (n : ℕ) :
    Game.succProbability
      (ProbComp.eval (secondPreimageGameOn (plantEasyBranch k H) valid adversary n)) ≤
      Game.succProbability (ProbComp.eval (secondPreimageGameOn H valid adversary n)) :=
  succProbability_secondPreimageGameOn_le_of_imp
    (fun _ _ _ hval hne heq => ⟨hval, eq_of_plantEasyBranch_eq k H hne heq⟩) adversary

/-- **Exercise 8.23(c) on bit strings, positive half** ([BonehShoup2023], p. 353): if `H` is
second-preimage resistant on `valid`, then `plantEasyBranch k H` is also second-preimage resistant
on `valid` (and in particular `SecondPreimageResistant` when `H` is). -/
theorem SecondPreimageResistantOn.plantEasyBranch (k : ℕ) {H : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} (hH : SecondPreimageResistantOn H valid) :
    SecondPreimageResistantOn (Cslib.Crypto.plantEasyBranch k H) valid := by
  refine SecondPreimageResistantOn.of_negligible
    (computableInPolyTime_plantEasyBranch k hH.polyTime) fun adversary hadversary => ?_
  exact negligible_of_le (hH.negligible adversary hadversary)
    (succProbability_secondPreimageGameOn_plantEasyBranch_le k H valid adversary)

/-- Inverter for `plantEasyBranch k H`: prepend `k` `false` bits to the tail of the digest. -/
def plantEasyBranchInverter (k : ℕ) : Inverter :=
  fun _ d => pure (List.replicate k false ++ d.tail)

@[program_certificate]
theorem isPPT_plantEasyBranchInverter (k : ℕ) :
    IsPPT encBits (plantEasyBranchInverter k) := by
  have h : ComputableInPolyTime (fun d : List Bool => List.replicate k false ++ d.tail)
      encBits encBits := by polytime
  exact h.isPPT

/-- **Exercise 8.23(c) on bit strings, negative half** ([BonehShoup2023], p. 353): for every `k`
and `H`, `plantEasyBranch k H` is not one-way (at length `n ≥ k`, `plantEasyBranchInverter k`
succeeds with probability at least `(1 / 2) ^ k`). -/
theorem not_oneWay_plantEasyBranch (k : ℕ) (H : List Bool → List Bool) :
    ¬ OneWay (plantEasyBranch k H) := by
  intro hf
  have hneg :=
    hf.inversion_negligible (plantEasyBranchInverter k) (isPPT_plantEasyBranchInverter k)
  have hmass :
      (((1 / 2 : ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞) ≤
        BitString.uniformList k (List.replicate k false) := by
    have hcast : (((1 / 2 : ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞) = (1 : ℝ≥0∞) / 2 ^ k := by
      rw [ENNReal.coe_pow, one_div, ENNReal.coe_inv_two, ← ENNReal.inv_pow, ← one_div]
    have h := BitString.uniformList_map_apply id k (List.replicate k false)
    simp only [PMF.map_id, id_eq] at h
    rw [hcast, h]
    gcongr
    have hmem : (fun _ : Fin k => false) ∈
        Finset.univ.filter
          (fun r : Fin k → Bool => List.ofFn r = List.replicate k false) := by
      simp
    exact_mod_cast Finset.card_pos.mpr ⟨_, hmem⟩
  have hle :
      ∀ᶠ n in Filter.atTop,
        ((1 / 2 : ℝ≥0) ^ k : ℝ≥0) ≤
          Game.succProbability
            (ProbComp.eval
              (inversionGame (plantEasyBranch k H) (plantEasyBranchInverter k) n)) := by
    filter_upwards [Filter.eventually_ge_atTop k] with n hn
    have hsplit :
        BitString.uniformList n =
          (BitString.uniformList k).bind fun pref =>
            (BitString.uniformList (n - k)).map (pref ++ ·) := by
      conv_lhs => rw [show n = k + (n - k) by omega]
      exact BitString.uniformList_add k (n - k)
    have hwin_suf (suf : List Bool) :
        let w := List.replicate k false ++ suf
        (plantEasyBranch k H (List.replicate k false ++ (plantEasyBranch k H w).tail) ==
          plantEasyBranch k H w) = true := by
      dsimp only
      have htake : (List.replicate k false ++ suf).take k = List.replicate k false := by
        simp
      have hdrop : (List.replicate k false ++ suf).drop k = suf := by
        simp
      simp [plantEasyBranch, htake, hdrop]
    have henn :
        (((1 / 2 : ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞) ≤
          ProbComp.eval
            (inversionGame (plantEasyBranch k H) (plantEasyBranchInverter k) n) true := by
      simp only [inversionGame, inversionExperiment, plantEasyBranchInverter, ProbComp.eval_bind,
        ProbComp.eval_pure, BitString.eval_sampleList, hsplit, PMF.bind_bind, PMF.bind_map,
        PMF.pure_bind, Function.comp_def]
      rw [PMF.bind_apply]
      refine (mul_one (((1 / 2 : ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞)).symm.trans_le ?_
      refine (mul_le_mul_of_nonneg_right hmass zero_le).trans ?_
      refine (le_of_eq ?_).trans
        (le_tsum (fun pref => (BitString.uniformList k) pref *
          ((BitString.uniformList (n - k)).bind fun suf =>
            PMF.pure
              (plantEasyBranch k H
                (List.replicate k false ++
                  (plantEasyBranch k H (pref ++ suf)).tail) ==
                plantEasyBranch k H (pref ++ suf))) true)
          (List.replicate k false))
      congr 1
      have hconst :
          ((BitString.uniformList (n - k)).bind fun suf =>
            PMF.pure
              (plantEasyBranch k H
                (List.replicate k false ++
                  (plantEasyBranch k H (List.replicate k false ++ suf)).tail) ==
                plantEasyBranch k H (List.replicate k false ++ suf))) = PMF.pure true := by
        simp only [hwin_suf, PMF.bind_const]
      rw [hconst, PMF.pure_apply_self]
    exact (ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) henn).trans_eq' (ENNReal.toNNReal_coe _)
  have hne0 : ((1 / 2 : ℝ≥0) ^ k : ℝ≥0) ≠ 0 := pow_ne_zero k (by norm_num)
  exact not_negligible_const hne0 (negligible_of_eventually_le hneg hle)

end Cslib.Crypto
