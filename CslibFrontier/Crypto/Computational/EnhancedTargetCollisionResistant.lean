/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Computational.TargetCollisionResistant
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Negligible.Basic
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Probability.PMF
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.InversePolynomial
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime

/-!
# Enhanced target collision resistance

Enhanced target collision resistance ([BonehShoup2023], Exercise 8.27, p. 354) strengthens target
collision resistance (UOWHF): in stage 1 the adversary commits to a target message `m₀` (and saved
state) given only the security parameter `1^n`; after seeing a uniformly sampled key `k`, in
stage 2 it may change *either* the message *or* the key, outputting `(k', m') ≠ (k, m₀)` such
that `H n k' m' = H n k m₀`.

Following the repository's `TargetCollisionResistantOn` conventions,
`EnhancedTargetCollisionResistantOn` samples `k` uniformly from `{0,1}^{keyLen n}`, checks both
message validity (`valid n m₀` and `valid n m'`) and key-length validity (`k'.length = keyLen n`),
and quantifies over uniform strict PPT two-stage finders (`EnhancedTargetCollisionFinder.IsPPT`) on
unary `n`, charging the full saved state passed from `choose` to `find`. Exercise 8.27(d) is
formalized via the fixed-length `T × K` pair encoding `appendKeyHash H n k msg := H n k msg ++ k`
(and `KeyedHashFamily.appendKeyHash`), where equal lengths `k'.length = keyLen n` uniquely recover
`k' = k` from `H n k' m' ++ k' = H n k m₀ ++ k`. Parts (a)–(c) of Exercise 8.27 and Exercise 8.28
are not proved here.

## Main definitions

* `Cslib.Crypto.isEnhancedTargetCollision`: boolean winning condition for `(k', m')` against
  `(k, m₀)`.
* `Cslib.Crypto.EnhancedTargetCollisionFinder`, `Cslib.Crypto.EnhancedTargetCollisionFinder.IsPPT`:
  two-stage enhanced target-collision adversary and its strict PPT admissibility predicate.
* `Cslib.Crypto.enhancedTargetCollisionGame`: the two-stage enhanced target-collision experiment.
* `Cslib.Crypto.EnhancedTargetCollisionResistantOn`,
  `Cslib.Crypto.EnhancedTargetCollisionResistant`,
  `Cslib.Crypto.KeyedHashFamily.EnhancedTargetCollisionResistant`: asymptotic enhanced target
  collision resistance.
* `Cslib.Crypto.TargetCollisionFinder.toEnhancedFinder`: lift a `TargetCollisionFinder` to an
  `EnhancedTargetCollisionFinder` returning `(k, m')`.
* `Cslib.Crypto.appendKeyHash`, `Cslib.Crypto.KeyedHashFamily.appendKeyHash`: Exercise 8.27(d)
  construction `H'(k, m) := H(k, m) ++ k`.
* `Cslib.Crypto.EnhancedTargetCollisionFinder.toTargetFinder`: project `m'` from a `(k', m')`
  enhanced collision finder.

## Main results

* `Cslib.Crypto.EnhancedTargetCollisionResistantOn.negligible`,
  `Cslib.Crypto.EnhancedTargetCollisionResistantOn.of_negligible`,
  `Cslib.Crypto.not_enhancedTargetCollisionResistantOn_of_eventually_le_succProbability`:
  interface and refutation lemmas for enhanced target collision resistance.
* `Cslib.Crypto.EnhancedTargetCollisionResistantOn.targetCollisionResistantOn`,
  `Cslib.Crypto.KeyedHashFamily.EnhancedTargetCollisionResistant.targetCollisionResistant`:
  enhanced target collision resistance implies target collision resistance.
* `Cslib.Crypto.computableInPolyTime_appendKeyHash`: plain polynomial-time certificate for
  `appendKeyHash`.
* `Cslib.Crypto.succProbability_enhancedTargetCollisionGame_appendKeyHash_le`,
  `Cslib.Crypto.TargetCollisionResistantOn.enhancedTargetCollisionResistantOn_appendKeyHash`, and
  `KeyedHashFamily.TargetCollisionResistant.enhancedTargetCollisionResistant_appendKeyHash`:
  Exercise 8.27(d), `H'(k, m) := H(k, m) ++ k` is enhanced target collision-resistant when `H`
  is target collision-resistant.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Exercise 8.27, p. 354.
-/

public section

namespace Cslib.Crypto

open ProbComp Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

/-- Test whether `(k', m')` is a valid enhanced target collision against `(k, m₀)` for `H n` at
security parameter `n` under key length `keyLen n` and message predicate `valid n`
([BonehShoup2023], Exercise 8.27, p. 354): both `m₀` and `m'` satisfy `valid n`, `k'` has length
`keyLen n`, `(k', m') ≠ (k, m₀)`, and `H n k' m' = H n k m₀`. -/
@[expose]
def isEnhancedTargetCollision (keyLen : ℕ → ℕ)
    (H : ℕ → List Bool → List Bool → List Bool) (valid : ℕ → List Bool → Bool)
    (n : ℕ) (k m₀ k' m' : List Bool) : Bool :=
  valid n m₀ && valid n m' && (k'.length == keyLen n) &&
    ((k' != k) || (m' != m₀)) && (H n k' m' == H n k m₀)

@[simp]
theorem isEnhancedTargetCollision_eq_true_iff {keyLen : ℕ → ℕ}
    {H : ℕ → List Bool → List Bool → List Bool} {valid : ℕ → List Bool → Bool}
    {n : ℕ} {k m₀ k' m' : List Bool} :
    isEnhancedTargetCollision keyLen H valid n k m₀ k' m' = true ↔
      valid n m₀ = true ∧ valid n m' = true ∧ k'.length = keyLen n ∧
        (k', m') ≠ (k, m₀) ∧ H n k' m' = H n k m₀ := by
  simp only [isEnhancedTargetCollision, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq, Prod.mk.injEq, not_and_or, and_assoc]

/-- A two-stage enhanced target-collision adversary ([BonehShoup2023], Exercise 8.27, p. 354):
`choose` selects a target message `m₀` and saved state from `1^n` before the hash key is sampled,
and `find` produces a key-message pair `(k', m')` after receiving the sampled key `k`. -/
structure EnhancedTargetCollisionFinder where
  /-- Select `(m₀, state)` given unary `n` before the hash key is chosen. -/
  choose : ℕ → ProbComp (List Bool × List Bool)
  /-- Given unary `n`, saved `state`, and sampled hash `key`, output a candidate `(k', m')`. -/
  find : ℕ → List Bool → List Bool → ProbComp (List Bool × List Bool)

/-- Uniform strict PPT admissibility for both stages of an `EnhancedTargetCollisionFinder`,
charging the full saved-state word passed from `choose` to `find`. -/
structure EnhancedTargetCollisionFinder.IsPPT
    (adversary : EnhancedTargetCollisionFinder) : Prop where
  /-- Target selection is uniform strict PPT on unary `n`. -/
  choose : IsPPTOn encUnary (encPair encBits encBits) adversary.choose
  /-- Enhanced collision search is uniform strict PPT on `(1^n, state, key)`. -/
  find : IsPPTOn (encPair encUnary (encPair encBits encBits)) (encPair encBits encBits)
    (fun ⟨n, state, key⟩ => adversary.find n state key)

/-- The two-stage enhanced target-collision experiment ([BonehShoup2023], Exercise 8.27, p. 354):
run `adversary.choose n` to obtain `(m₀, state)`, sample a uniform `keyLen n`-bit key `k`, run
`adversary.find n state k` to obtain `(k', m')`, and accept iff
`isEnhancedTargetCollision keyLen H valid n k m₀ k' m'` holds. -/
@[expose]
noncomputable def enhancedTargetCollisionGame
    (keyLen : ℕ → ℕ) (H : ℕ → List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool)
    (adversary : EnhancedTargetCollisionFinder) (n : ℕ) : ProbComp Bool := do
  let choice ← adversary.choose n
  let k ← BitString.sampleList (keyLen n)
  let ans ← adversary.find n choice.2 k
  return isEnhancedTargetCollision keyLen H valid n k choice.1 ans.1 ans.2

/-- Enhanced target collision resistance of `H` with key-length schedule `keyLen` on `valid`
against every uniform strict PPT `EnhancedTargetCollisionFinder` ([BonehShoup2023], Exercise 8.27,
p. 354), sampling uniform keys of length `keyLen n`, checking `valid n m₀`, `valid n m'`, and
`k'.length = keyLen n`, and charging saved state on unary `n`. -/
@[expose]
def EnhancedTargetCollisionResistantOn
    (keyLen : ℕ → ℕ) (H : ℕ → List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (enhancedTargetCollisionGame keyLen H valid adversary n))
    (fun _ _ => PMF.pure false)
    EnhancedTargetCollisionFinder.IsPPT

/-- Unrestricted enhanced target collision resistance on all bit strings `List Bool`:
`EnhancedTargetCollisionResistantOn` with every word valid ([BonehShoup2023], Exercise 8.27,
p. 354). -/
abbrev EnhancedTargetCollisionResistant
    (keyLen : ℕ → ℕ) (H : ℕ → List Bool → List Bool → List Bool) : Prop :=
  EnhancedTargetCollisionResistantOn keyLen H (fun _ _ => true)

/-- Unrestricted enhanced target collision resistance of a `KeyedHashFamily` on all `List Bool`
([BonehShoup2023], Exercise 8.27, p. 354). -/
@[expose]
def KeyedHashFamily.EnhancedTargetCollisionResistant (H : KeyedHashFamily) : Prop :=
  Cslib.Crypto.EnhancedTargetCollisionResistant H.keyLen H.eval

/-- Enhanced target collision resistance gives negligible success probability in
`enhancedTargetCollisionGame` for every strict PPT `EnhancedTargetCollisionFinder`. -/
theorem EnhancedTargetCollisionResistantOn.negligible
    {keyLen : ℕ → ℕ} {H : ℕ → List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool}
    (h : EnhancedTargetCollisionResistantOn keyLen H valid)
    (adversary : EnhancedTargetCollisionFinder) (hPPT : adversary.IsPPT) :
    Negligible (fun n => Game.succProbability
      (ProbComp.eval (enhancedTargetCollisionGame keyLen H valid adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- Enhanced target collision resistance holds when every strict PPT
`EnhancedTargetCollisionFinder` has negligible success probability. -/
theorem EnhancedTargetCollisionResistantOn.of_negligible
    {keyLen : ℕ → ℕ} {H : ℕ → List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool}
    (h : ∀ adversary : EnhancedTargetCollisionFinder, adversary.IsPPT →
      Negligible (fun n => Game.succProbability
        (ProbComp.eval (enhancedTargetCollisionGame keyLen H valid adversary n)))) :
    EnhancedTargetCollisionResistantOn keyLen H valid := fun adversary hPPT => by
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- **Finding enhanced target collisions with probability bounded away from zero refutes
`EnhancedTargetCollisionResistantOn`**: a strict PPT adversary whose success probability is
eventually at least a fixed `c > 0`. -/
theorem not_enhancedTargetCollisionResistantOn_of_eventually_le_succProbability
    {keyLen : ℕ → ℕ} {H : ℕ → List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {c : ℝ≥0} (hc : c ≠ 0)
    (adversary : EnhancedTargetCollisionFinder) (hPPT : adversary.IsPPT)
    (h : ∀ᶠ n in Filter.atTop, c ≤ Game.succProbability
      (ProbComp.eval (enhancedTargetCollisionGame keyLen H valid adversary n))) :
    ¬ EnhancedTargetCollisionResistantOn keyLen H valid :=
  fun hETCR => not_negligible_of_eventually_ge hc h (hETCR.negligible adversary hPPT)

/-- Lift any two-stage `TargetCollisionFinder` into an `EnhancedTargetCollisionFinder` by returning
the challenged key `k` unchanged alongside `m₁`. -/
noncomputable def TargetCollisionFinder.toEnhancedFinder
    (adversary : TargetCollisionFinder) : EnhancedTargetCollisionFinder where
  choose := adversary.choose
  find n state key := do
    let m₁ ← adversary.find n state key
    return (key, m₁)

/-- `TargetCollisionFinder.toEnhancedFinder` preserves uniform strict PPT admissibility. -/
theorem TargetCollisionFinder.IsPPT.toEnhancedFinder
    {adversary : TargetCollisionFinder} (ha : adversary.IsPPT) :
    adversary.toEnhancedFinder.IsPPT where
  choose := ha.choose
  find := ha.find.bind_with (by
    polytime : ComputableInPolyTime
      (fun r : (ℕ × List Bool × List Bool) × List Bool => (r.1.2.2, r.2)) _ _).isPPTOn

/-- Running `adversary.toEnhancedFinder` in `enhancedTargetCollisionGame` produces the exact same
output distribution as running `adversary` in `targetCollisionGame`. -/
theorem eval_enhancedTargetCollisionGame_toEnhancedFinder
    (keyLen : ℕ → ℕ) (H : ℕ → List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) (adversary : TargetCollisionFinder) (n : ℕ) :
    ProbComp.eval (enhancedTargetCollisionGame keyLen H valid adversary.toEnhancedFinder n) =
      ProbComp.eval (targetCollisionGame keyLen H valid adversary n) := by
  simp only [enhancedTargetCollisionGame, targetCollisionGame,
    TargetCollisionFinder.toEnhancedFinder, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, bind_assoc, pure_bind]
  apply PMF.bind_congr_on_support; intro choice _
  apply PMF.bind_congr_on_support; intro k hk
  apply PMF.bind_congr_on_support; intro m₁ _
  congr 1
  rw [Bool.eq_iff_iff, isEnhancedTargetCollision_eq_true_iff, isCollision_eq_true_iff]
  simp only [BitString.length_of_mem_support_uniformList hk, ne_eq, Prod.mk.injEq, true_and,
    eq_comm]

/-- Enhanced target collision resistance implies target collision resistance. [BonehShoup2023],
Exercise 8.27, p. 354 defines enhanced target collision resistance and states parts (a)–(d)
without stating this implication explicitly; it follows directly from the definition because a
target collision under the challenge key `k` is an enhanced collision with `k' = k`, giving both
games the same success probability. -/
theorem EnhancedTargetCollisionResistantOn.targetCollisionResistantOn
    {keyLen : ℕ → ℕ} {H : ℕ → List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool}
    (h : EnhancedTargetCollisionResistantOn keyLen H valid) :
    TargetCollisionResistantOn keyLen H valid := by
  apply TargetCollisionResistantOn.of_negligible
  intro adversary hPPT
  simpa only [eval_enhancedTargetCollisionGame_toEnhancedFinder] using
    h.negligible adversary.toEnhancedFinder hPPT.toEnhancedFinder

/-- Any `KeyedHashFamily` that is enhanced target collision-resistant is target
collision-resistant. -/
theorem KeyedHashFamily.EnhancedTargetCollisionResistant.targetCollisionResistant
    {H : KeyedHashFamily} (h : H.EnhancedTargetCollisionResistant) :
    H.TargetCollisionResistant :=
  EnhancedTargetCollisionResistantOn.targetCollisionResistantOn h

/-- Exercise 8.27(d) word construction `H'(k, m) := H(k, m) ++ k` encoding `(H(k, m), k)` in
`T × K` ([BonehShoup2023], Exercise 8.27(d), p. 354): since keys have fixed length `keyLen n`,
equal outputs `H n k' m' ++ k' = H n k m₀ ++ k` uniquely identify `k' = k` and
`H n k' m' = H n k m₀`. -/
@[expose]
def appendKeyHash (H : ℕ → List Bool → List Bool → List Bool)
    (n : ℕ) (k msg : List Bool) : List Bool :=
  H n k msg ++ k

/-- Appending the key to the digest is computable in plain polynomial time whenever `H` is. -/
@[program_certificate]
theorem computableInPolyTime_appendKeyHash
    {H : ℕ → List Bool → List Bool → List Bool}
    (hH : ComputableInPolyTime (fun ⟨n, k, msg⟩ => H n k msg) (encKeyedInput encBits) encBits) :
    ComputableInPolyTime (fun ⟨n, k, msg⟩ => appendKeyHash H n k msg)
      (encKeyedInput encBits) encBits :=
  ComputableInPolyTime.bitsAppend hH (by polytime)

/-- Lift a `KeyedHashFamily` `H` to `H.appendKeyHash` (`H'(k, m) := H(k, m) ++ k`, encoding
`(H(k, m), k)` in `T × K`, [BonehShoup2023], Exercise 8.27(d), p. 354), extending `digestLen n`
to `H.digestLen n + H.keyLen n`. -/
@[expose]
def KeyedHashFamily.appendKeyHash (H : KeyedHashFamily) : KeyedHashFamily where
  keyLen := H.keyLen
  digestLen n := H.digestLen n + H.keyLen n
  eval := Cslib.Crypto.appendKeyHash H.eval
  keyLen_polyTime := H.keyLen_polyTime
  digestLen_polyTime := by
    have := H.digestLen_polyTime
    have := H.keyLen_polyTime
    fun_prop
  polyTime := computableInPolyTime_appendKeyHash H.polyTime
  le_digestLen n := le_trans (H.le_digestLen n) (Nat.le_add_right _ _)
  length_eq n k msg hk := by
    simp only [Cslib.Crypto.appendKeyHash, List.length_append, H.length_eq n k msg hk, hk]

/-- Turn an `EnhancedTargetCollisionFinder` into a `TargetCollisionFinder` by projecting `m'` from
the returned `(k', m')` pair ([BonehShoup2023], Exercise 8.27(d), p. 354). -/
noncomputable def EnhancedTargetCollisionFinder.toTargetFinder
    (adversary : EnhancedTargetCollisionFinder) : TargetCollisionFinder where
  choose := adversary.choose
  find n state key := do
    let ans ← adversary.find n state key
    return ans.2

/-- `EnhancedTargetCollisionFinder.toTargetFinder` preserves uniform strict PPT admissibility. -/
theorem EnhancedTargetCollisionFinder.IsPPT.toTargetFinder
    {adversary : EnhancedTargetCollisionFinder} (ha : adversary.IsPPT) :
    adversary.toTargetFinder.IsPPT where
  choose := ha.choose
  find := ha.find.bind_with (by
    polytime : ComputableInPolyTime
      (fun r : (ℕ × List Bool × List Bool) × (List Bool × List Bool) => r.2.2) _ _).isPPTOn

private theorem eval_enhancedTargetCollisionGame_appendKeyHash_le
    (keyLen : ℕ → ℕ) (H : ℕ → List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) (adversary : EnhancedTargetCollisionFinder) (n : ℕ) :
    (ProbComp.eval (enhancedTargetCollisionGame keyLen (appendKeyHash H) valid adversary n)) true ≤
      (ProbComp.eval (targetCollisionGame keyLen H valid adversary.toTargetFinder n)) true := by
  simp only [enhancedTargetCollisionGame, targetCollisionGame,
    EnhancedTargetCollisionFinder.toTargetFinder, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList, bind_assoc, pure_bind]
  apply PMF.bind_apply_mono_on_support; intro choice _
  apply PMF.bind_apply_mono_on_support; intro k hk
  apply PMF.bind_apply_mono_on_support; intro ans _
  cases hcol : isEnhancedTargetCollision keyLen (appendKeyHash H) valid n k choice.1 ans.1 ans.2
  · simp
  · obtain ⟨hm₀, hm', hk'len, hne, happ⟩ := isEnhancedTargetCollision_eq_true_iff.mp hcol
    obtain ⟨hh, rfl⟩ := List.append_inj' happ
      (hk'len.trans (BitString.length_of_mem_support_uniformList hk).symm)
    rw [isCollision_eq_true_iff.mpr ⟨hm₀, hm', fun heq => hne (Prod.ext rfl heq.symm), hh.symm⟩]

/-- **Boneh–Shoup Exercise 8.27(d) (concrete bound)**: winning probability in
`enhancedTargetCollisionGame` against `appendKeyHash H` is at most the winning probability of
`adversary.toTargetFinder` in `targetCollisionGame` against `H`. -/
theorem succProbability_enhancedTargetCollisionGame_appendKeyHash_le
    (keyLen : ℕ → ℕ) (H : ℕ → List Bool → List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) (adversary : EnhancedTargetCollisionFinder) (n : ℕ) :
    Game.succProbability
        (ProbComp.eval (enhancedTargetCollisionGame keyLen (appendKeyHash H) valid adversary n)) ≤
      Game.succProbability
        (ProbComp.eval (targetCollisionGame keyLen H valid adversary.toTargetFinder n)) :=
  Game.succProbability_mono
    (eval_enhancedTargetCollisionGame_appendKeyHash_le keyLen H valid adversary n)

/-- **Boneh–Shoup Exercise 8.27(d)**: if `H` is target collision-resistant on `valid` with fixed
key length `keyLen`, then `H'(k, m) := H(k, m) ++ k` is enhanced target collision-resistant on
`valid`. -/
theorem TargetCollisionResistantOn.enhancedTargetCollisionResistantOn_appendKeyHash
    {keyLen : ℕ → ℕ} {H : ℕ → List Bool → List Bool → List Bool}
    {valid : ℕ → List Bool → Bool}
    (hTCR : TargetCollisionResistantOn keyLen H valid) :
    EnhancedTargetCollisionResistantOn keyLen (appendKeyHash H) valid := by
  apply EnhancedTargetCollisionResistantOn.of_negligible
  intro adversary hPPT
  exact negligible_of_le
    (hTCR.negligible adversary.toTargetFinder hPPT.toTargetFinder)
    (succProbability_enhancedTargetCollisionGame_appendKeyHash_le keyLen H valid adversary)

/-- **Boneh–Shoup Exercise 8.27(d) (`KeyedHashFamily` form)**: if a `KeyedHashFamily` `H` is
target collision-resistant, then `H.appendKeyHash` is enhanced target collision-resistant. -/
theorem KeyedHashFamily.TargetCollisionResistant.enhancedTargetCollisionResistant_appendKeyHash
    {H : KeyedHashFamily} (hTCR : H.TargetCollisionResistant) :
    H.appendKeyHash.EnhancedTargetCollisionResistant :=
  hTCR.enhancedTargetCollisionResistantOn_appendKeyHash

end Cslib.Crypto
