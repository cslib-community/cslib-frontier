/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Forgery
public import CslibFrontier.Languages.Probabilistic.Repeat
import CslibFrontier.Probability.PMF.Bind

/-!
# Repeated one-way inversion

The repeated one-way game (`repeatedInversionExperiment`, [BonehShoup2023], Attack Game 13.3,
p. 539) draws `t` independent inputs, publishes their images, answers reveal queries with the
corresponding seeds, and asks for a preimage of an unrevealed image. It coincides with the `d = 1`
case (`repeatedIterateExperiment_one`) of `repeatedIterateExperiment`, which treats `n` chains of
`d` iterates as in the iterated generalization of [BonehShoup2023], Exercise 14.15 (p. 612).

Relative to [BonehShoup2023], both games take arbitrary `t, n, d : ℕ`, any seed sampler
`sample : ProbComp X` rather than uniform, and 0-based indices `idx q : ℕ`; out-of-range reveals
return `default` (or `f^[idx q % d] default`) and out-of-range claims lose (`none`). At `d = 0`
the chain game is degenerate: `idx q / 0 = 0` and `idx q % 0 = idx q`, so every slot lies on
chain `0` and the published values are the seeds. On top of that, `repeatedIterateExperiment` and
`repeatedIterateUnrevealedExperiment` diverge from Exercise 14.15 in three respects (checked in
`CslibFrontierTests.Crypto.Game.RepeatedInversion`):
1. A claim for slot `(i, j)` (`0 ≤ j < d`) checks `f^[d - j] x = y_i`, so only `1 ≤ b ≤ d` is
   modeled (`b > d` is not analysed); forbidding reveals at or below the claimed slot compares
   `idx q % d < idx r.1 % d` rather than the printed `b' ≤ b`.
2. Reveals address `0 ≤ j < d`, so the book's `j = d` (the public value) cannot be requested (slot
   `i * d + d` is the next chain's seed, or out-of-range for the last chain).
3. For non-injective `f`, a revealed value above the claimed slot can sit past a merge with a
   side chain, so `chainConsistent` additionally requires `x` to iterate to every revealed value
   above it on its chain (coinciding with `chainUnrevealed` when `f` is injective and `0 < d`,
   `succProbability_repeatedIterateUnrevealedExperiment_of_injective`).

## Main definitions

* `Cslib.Crypto.chainSlot`, `chainKeyGen`, `chainVerify`, `chainUnrevealed`, `chainConsistent`,
  `chainSigner`: chain-game components.
* `Cslib.Crypto.repeatedIterateExperiment`, `repeatedIterateUnrevealedExperiment`: the repeated
  chain game with the chain-consistent and index-corrected unrevealed conditions.
* `Cslib.Crypto.repeatedInversionExperiment`: Attack Game 13.3.

## Main results

* `Cslib.Crypto.repeatedIterateExperiment_one`: the `d = 1` chain game is Attack Game 13.3.
* `Cslib.Crypto.succProbability_repeatedIterateExperiment_le_unrevealed`,
  `succProbability_repeatedIterateUnrevealedExperiment_of_injective`: comparison with the
  index-corrected unrevealed winning condition.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 13.4.1, Attack Game 13.3, p. 539; Exercise 14.15, p. 612.
-/

public section

namespace Cslib.Crypto

open Cslib Probability

variable {Q X : Type} [Inhabited X] [DecidableEq X]

/-! ### Chains and slots -/

/-- The value of slot `k` of the chains with seeds `xs`: position `k % d` of chain `k / d`, that
is, `f^[k % d]` of the seed. A slot outside the range holds the iterate of `default`. -/
@[expose] def chainSlot (f : X → X) (d : ℕ) (xs : List X) (k : ℕ) : X :=
  f^[k % d] (xs.getD (k / d) default)

/-- Draw `n` seeds and publish the top `f^[d] x` of each chain. -/
@[expose] def chainKeyGen (sample : ProbComp X) (f : X → X) (n d : ℕ) :
    ProbComp (List X × List X) := do
  let xs ← OracleComp.replicate n sample
  return (xs.map f^[d], xs)

/-- `x`, claimed for slot `k`, leads to the published top of its chain. -/
@[expose] def chainVerify (f : X → X) (d : ℕ) (ys : List X) (k : ℕ) (x : X) : Bool :=
  ys[k / d]? == some (f^[d - k % d] x)

/-- No slot at or below slot `idx q` on its chain was revealed (the condition of
[BonehShoup2023], Exercise 14.15, with the index corrected). -/
@[expose] def chainUnrevealed (idx : Q → ℕ) (d : ℕ) (q : Q) (_ : X) (log : List (Q × X)) : Bool :=
  log.all fun r => idx r.1 / d != idx q / d || decide (idx q % d < idx r.1 % d)

/-- `chainUnrevealed`, and `x` leads to every value revealed on its chain. -/
@[expose] def chainConsistent (idx : Q → ℕ) (f : X → X) (d : ℕ) (q : Q) (x : X)
    (log : List (Q × X)) : Bool :=
  log.all fun r => idx r.1 / d != idx q / d ||
    (decide (idx q % d < idx r.1 % d) && f^[idx r.1 % d - idx q % d] x == r.2)

/-- The reveal oracle: a request `q` is answered with slot `idx q`. -/
@[expose] def chainSigner (idx : Q → ℕ) (f : X → X) (d : ℕ) : Signer (List X) Q X :=
  .ofSign fun xs q => pure (chainSlot f d xs (idx q))

/-- The repeated game on `n` chains of `d` iterates of `f`, with the chain-consistent winning
condition. -/
@[expose] def repeatedIterateExperiment (idx : Q → ℕ) (sample : ProbComp X) (f : X → X) (n d : ℕ)
    (A : List X → ProbOracleComp (fun _ : Q => X) (Q × X)) : Experiment :=
  forgeExperiment (chainKeyGen sample f n d) (chainSigner idx f d)
    (fun ys _ q => chainVerify f d ys (idx q)) (chainConsistent idx f d) A

/-- The same game with the unrevealed winning condition of Exercise 14.15 (index corrected). -/
@[expose] def repeatedIterateUnrevealedExperiment (idx : Q → ℕ) (sample : ProbComp X) (f : X → X)
    (n d : ℕ) (A : List X → ProbOracleComp (fun _ : Q => X) (Q × X)) : Experiment :=
  forgeExperiment (chainKeyGen sample f n d) (chainSigner idx f d)
    (fun ys _ q => chainVerify f d ys (idx q)) (chainUnrevealed idx d) A

/-- Attack Game 13.3 ([BonehShoup2023], p. 539), generalized to arbitrary `t : ℕ`, any seed
sampler `sample`, and 0-based reveal/claim indices `idx q` (out-of-range reveals return `default`
and out-of-range claims lose). -/
@[expose] def repeatedInversionExperiment {Y : Type} [DecidableEq Y] (idx : Q → ℕ)
    (sample : ProbComp X) (f : X → Y) (t : ℕ)
    (A : List Y → ProbOracleComp (fun _ : Q => X) (Q × X)) : Experiment :=
  forgeExperiment (do let xs ← OracleComp.replicate t sample; return (xs.map f, xs))
    (.ofSign fun xs q => pure (xs.getD (idx q) default))
    (fun ys _ q x => ys[idx q]? == some (f x))
    (fun q _ log => decide (idx q ∉ log.map fun r => idx r.1)) A

/-- With `Q = ℕ` and `idx = id` the freshness test of `repeatedInversionExperiment` is
`freshMessage`. -/
example (k : ℕ) (x : X) (log : List (ℕ × X)) :
    decide (id k ∉ log.map fun r => id r.1) = freshMessage k x log := rfl

/-- At `d = 1` the chain game is Attack Game 13.3. -/
theorem repeatedIterateExperiment_one (idx : Q → ℕ) (sample : ProbComp X) (f : X → X) (t : ℕ)
    (A : List X → ProbOracleComp (fun _ : Q => X) (Q × X)) :
    repeatedIterateExperiment idx sample f t 1 A =
      repeatedInversionExperiment idx sample f t A := by
  have hfresh : chainConsistent idx f 1 =
      fun q _ log => decide (idx q ∉ log.map fun r => idx r.1) := by
    funext q x log
    rw [Bool.eq_iff_iff]
    simp only [chainConsistent, Nat.mod_one, Nat.div_one, lt_self_iff_false, decide_false,
      Bool.false_and, Bool.or_false, List.all_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
      List.mem_map, not_exists, not_and]
  have hsign : chainSigner idx f 1 = .ofSign fun xs q => pure (xs.getD (idx q) default) := by
    simp [chainSigner, chainSlot, Nat.mod_one, Nat.div_one]
  have hver : (fun (ys : List X) (_ : List X) q => chainVerify f 1 ys (idx q)) =
      fun ys _ q x => ys[idx q]? == some (f x) := by
    funext ys _ q x
    simp [chainVerify, Nat.mod_one, Nat.div_one]
  simp only [repeatedIterateExperiment, repeatedInversionExperiment, hfresh, hsign, hver,
    chainKeyGen, Function.iterate_one]

/-! ### The unrevealed winning condition -/

/-- The chain-consistent condition is the stronger one. -/
theorem succProbability_repeatedIterateExperiment_le_unrevealed (idx : Q → ℕ)
    (sample : ProbComp X) (f : X → X) (n d : ℕ)
    (A : List X → ProbOracleComp (fun _ : Q => X) (Q × X)) :
    Experiment.succProbability (repeatedIterateExperiment idx sample f n d A) ≤
      Experiment.succProbability (repeatedIterateUnrevealedExperiment idx sample f n d A) :=
  succProbability_forgeExperiment_mono (fun q x log h => by
    simp only [chainConsistent, chainUnrevealed, List.all_eq_true] at h ⊢
    intro r hr
    have := h r hr
    simp only [Bool.or_eq_true, Bool.and_eq_true] at this ⊢
    exact this.imp id And.left) A

/-- For an injective `f`, a verified claim is the slot value itself, so it leads to every value
revealed above it: on a log of true slot values the two winning conditions agree. -/
private theorem chainUnrevealed_eq_chainConsistent {idx : Q → ℕ} {f : X → X}
    (hf : Function.Injective f) {d : ℕ} (hd : 0 < d) {xs : List X} {q : Q} {x : X}
    {log : List (Q × X)} (hlog : ∀ r ∈ log, r.2 = chainSlot f d xs (idx r.1))
    (hver : chainVerify f d (xs.map f^[d]) (idx q) x = true) :
    chainUnrevealed idx d q x log = chainConsistent idx f d q x log := by
  have hbd : idx q % d < d := Nat.mod_lt _ hd
  have hx : x = f^[idx q % d] (xs.getD (idx q / d) default) := by
    simp only [chainVerify, beq_iff_eq, List.getElem?_map, Option.map_eq_some_iff] at hver
    obtain ⟨y, hy, hfy⟩ := hver
    have hget : xs.getD (idx q / d) default = y := by
      rw [List.getD_eq_getElem?_getD, hy]
      rfl
    apply hf.iterate (d - idx q % d)
    rw [← Function.iterate_add_apply, hget, ← hfy]
    exact congrArg (fun k => f^[k] y) (by omega)
  rw [Bool.eq_iff_iff]
  simp only [chainUnrevealed, chainConsistent, List.all_eq_true, Bool.or_eq_true, bne_iff_ne,
    ne_eq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro h r hr
    rcases h r hr with h1 | h2
    · exact Or.inl h1
    · by_cases hra : idx r.1 / d = idx q / d
      · refine Or.inr ⟨h2, ?_⟩
        rw [hlog r hr, chainSlot, hra, hx, ← Function.iterate_add_apply]
        exact congrArg (fun k => f^[k] (xs.getD (idx q / d) default)) (by omega)
      · exact Or.inl hra
  · intro h r hr
    exact (h r hr).imp id And.left

/-- For an injective `f` and `0 < d`, the two conditions give the same success probability. -/
theorem succProbability_repeatedIterateUnrevealedExperiment_of_injective (idx : Q → ℕ)
    (sample : ProbComp X) {f : X → X} (hf : Function.Injective f) (n : ℕ) {d : ℕ} (hd : 0 < d)
    (A : List X → ProbOracleComp (fun _ : Q => X) (Q × X)) :
    Experiment.succProbability (repeatedIterateUnrevealedExperiment idx sample f n d A) =
      Experiment.succProbability (repeatedIterateExperiment idx sample f n d A) := by
  have h : ProbComp.eval (repeatedIterateUnrevealedExperiment idx sample f n d A) =
      ProbComp.eval (repeatedIterateExperiment idx sample f n d A) := by
    rw [repeatedIterateUnrevealedExperiment, repeatedIterateExperiment, eval_forgeExperiment_eq,
      eval_forgeExperiment_eq]
    refine PMF.bind_congr_on_support _ _ _ fun ks hks => ?_
    simp only [chainKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hks
    obtain ⟨xs, -, rfl⟩ := hks
    dsimp only
    rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨q, x⟩, log⟩ hz => ?_
    have hlog : ∀ r ∈ log, r.2 = chainSlot f d xs (idx r.1) :=
      ProbOracleComp.forall_mem_runLogWith (P := fun p => p.2 = chainSlot f d xs (idx p.1))
        (fun log q program hprog r hr => by
          simp only [chainSigner, Signer.ofSign_apply, Option.some.injEq] at hprog
          subst hprog
          simpa using hr) _ hz
    simp only [Function.comp_apply]
    congr 1
    rcases Bool.eq_false_or_eq_true (chainVerify f d (xs.map f^[d]) (idx q) x) with hv | hv
    · rw [hv, Bool.true_and, Bool.true_and]
      exact chainUnrevealed_eq_chainConsistent hf hd hlog hv
    · rw [hv, Bool.false_and, Bool.false_and]
  rw [Experiment.succProbability, Experiment.succProbability, h]

end Cslib.Crypto
