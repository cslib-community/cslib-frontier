/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Experiment
public import CslibFrontier.Crypto.Primitives.UHF.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Probability.PMF.SupportTsum

/-!
# Computational universal hashing

The adversary receives the unary security parameter and a public setup description. The uniform
hash key for that description stays private. The finite single-pair and multi-query experiments
give the conditional success probabilities. A collision counts only between distinct valid
messages. The message encoding is shared across setup descriptions.

The computational security implication follows by running the certified collision-pair sampler
on the multi-query adversary's list. The list length bound follows from the strict PPT
certificates for the setup and adversary. The converse submits a pair as a two-message batch
and preserves the success probability.

## Main definitions

* `Cslib.Crypto.UHF.collisionGame` and `Cslib.Crypto.UHF.multiQueryGame`: collision games with
  public setup and private keys.
* `Cslib.Crypto.UHF.IsComputationalUHF` and `Cslib.Crypto.UHF.IsMultiQueryUHF`: negligible
  success in the respective games against every uniform strict PPT adversary.
* `Cslib.Crypto.UHF.collisionPairToBatch`: present a single guess as a two-message batch.

## Main results

* `Cslib.Crypto.UHF.succProbability_multiQueryGame_le_collisionPairReduction`: the concrete
  `Q ^ 2 / 2` bound for the certified sampler, averaged over setup.
* `Cslib.Crypto.UHF.IsComputationalUHF.isMultiQueryUHF`: the asymptotic implication for a
  strict PPT setup.
* `Cslib.Crypto.UHF.IsMultiQueryUHF.isComputationalUHF`: the converse via a two-message batch.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Definitions 7.2–7.4 and Lemma 7.1, printed pp. 254–255.
-/

public section

namespace Cslib.Crypto.UHF

open Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

variable {D M : Type} {K Y : D → Type}

-- Tag invalid messages with their own identity so only distinct valid messages can collide.
private def hashOn {T : Type} (valid : M → Bool) (f : M → T) (m : M) : T ⊕ M :=
  if valid m then .inl (f m) else .inr m

private theorem valid_collision_iff_hashOn_eq {T : Type} (valid : M → Bool) (f : M → T)
    (m m' : M) :
    m ≠ m' ∧ valid m = true ∧ valid m' = true ∧ f m = f m' ↔
      m ≠ m' ∧ hashOn valid f m = hashOn valid f m' := by
  cases hm : valid m <;> cases hm' : valid m' <;> simp [hashOn, hm, hm']

/-- Run a collision guesser and submit its two messages in order, including repeated guesses. -/
def collisionPairToBatch (guess : ProbComp (CollisionGuess M)) : ProbComp (List M) :=
  (fun pair => [pair.first, pair.second]) <$> guess

/-- Every supported output of the wrapper contains exactly two messages. -/
theorem length_of_mem_support_collisionPairToBatch {guess : ProbComp (CollisionGuess M)}
    {batch : List M} (hbatch : batch ∈ (ProbComp.eval (collisionPairToBatch guess)).support) :
    batch.length = 2 := by
  rw [collisionPairToBatch, ProbComp.eval_map, PMF.mem_support_map_iff] at hbatch
  obtain ⟨_, _, rfl⟩ := hbatch
  rfl

/-- The batch wrapper adds only the cost of writing a two-element framed list. -/
theorem isPPTOn_collisionPairToBatch {I : Type} {encI : I ↪ List Bool} {encM : M ↪ List Bool}
    {A : I → ProbComp (CollisionGuess M)} (hA : IsPPTOn encI (encCollisionGuess encM) A) :
    IsPPTOn encI (encList encM) (fun i => collisionPairToBatch (A i)) := by
  have hId : ComputableInPolyTime id (encCollisionGuess encM) (encCollisionGuess encM) := .id'
  exact hA.map ((ComputableInPolyTime.cons encM).comp
    ((encCollisionGuess_first_polyTime encM hId).prod
      ((ComputableInPolyTime.cons encM).comp
        ((encCollisionGuess_second_polyTime encM hId).prod (.const [])))))

variable [∀ d, Fintype (K d)] [∀ d, Nonempty (K d)] [DecidableEq M] [∀ d, DecidableEq (Y d)]

/-- Attack Game 7.1 with public setup. The adversary receives `(n, d)` and wins if its two
distinct valid messages collide under a private uniform key from `K d`. -/
@[expose] noncomputable def collisionGame (setup : ℕ → ProbComp D) (valid : ℕ → D → M → Bool)
    (H : ℕ → (d : D) → K d → M → Y d) (A : ℕ × D → ProbComp (CollisionGuess M))
    (n : ℕ) : Game :=
  Game.withSetup (ProbComp.eval (setup n)) fun d => do
    let guess ← A (n, d)
    let k ← ProbComp.uniform (K d)
    return decide (guess.first ≠ guess.second ∧ valid n d guess.first = true ∧
      valid n d guess.second = true ∧ H n d k guess.first = H n d k guess.second)

/-- Attack Game 7.2 with public setup. The adversary receives `(n, d)` and wins if some two
distinct valid messages in its output list collide under a private uniform key from `K d`.
Repeated messages and invalid entries do not contribute a collision. -/
@[expose] noncomputable def multiQueryGame (setup : ℕ → ProbComp D) (valid : ℕ → D → M → Bool)
    (H : ℕ → (d : D) → K d → M → Y d) (A : ℕ × D → ProbComp (List M)) (n : ℕ) : Game :=
  Game.withSetup (ProbComp.eval (setup n)) fun d => do
    let ms ← A (n, d)
    let k ← ProbComp.uniform (K d)
    return decide (∃ m ∈ ms, ∃ m' ∈ ms,
      m ≠ m' ∧ valid n d m = true ∧ valid n d m' = true ∧ H n d k m = H n d k m')

/-- Computational UHF security ([BonehShoup2023], Definition 7.2, printed p. 254) against
uniform strict PPT adversaries. The unary parameter is framed before the public setup encoding.
Invalid guesses lose. The predicate accepts a setup program of arbitrary runtime.
`IsComputationalUHF.isMultiQueryUHF` requires strict PPT setup. The caller supplies the keyed
hash family's recognition, sampling and evaluation requirements from Definition 7.4. -/
@[expose] def IsComputationalUHF (encD : D ↪ List Bool) (encM : M ↪ List Bool)
    (setup : ℕ → ProbComp D) (valid : ℕ → D → M → Bool)
    (H : ℕ → (d : D) → K d → M → Y d) : Prop :=
  Game.Indistinguishable (collisionGame setup valid H) (fun _ _ => PMF.pure false)
    (IsPPTOn (encPair encUnary encD) (encCollisionGuess encM))

/-- Multi-query UHF security ([BonehShoup2023], Definition 7.3, printed p. 254) against uniform
strict PPT adversaries, with the same public inputs and message domain as `IsComputationalUHF`.
The adversary outputs a framed list of messages. The predicate accepts a setup program of
arbitrary runtime. `IsComputationalUHF.isMultiQueryUHF` requires strict PPT setup. -/
@[expose] def IsMultiQueryUHF (encD : D ↪ List Bool) (encM : M ↪ List Bool)
    (setup : ℕ → ProbComp D) (valid : ℕ → D → M → Bool)
    (H : ℕ → (d : D) → K d → M → Y d) : Prop :=
  Game.Indistinguishable (multiQueryGame setup valid H) (fun _ _ => PMF.pure false)
    (IsPPTOn (encPair encUnary encD) (encList encM))

/-- The two-message batch and the original pair win on exactly the same guesses and keys. -/
theorem multiQueryGame_collisionPairToBatch (setup : ℕ → ProbComp D)
    (valid : ℕ → D → M → Bool) (H : ℕ → (d : D) → K d → M → Y d)
    (A : ℕ × D → ProbComp (CollisionGuess M)) (n : ℕ) :
    multiQueryGame setup valid H (fun p => collisionPairToBatch (A p)) n =
      collisionGame setup valid H A n := by
  simp only [multiQueryGame, collisionGame, Game.withSetup, collisionPairToBatch,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_map, Function.comp_def]
  congr 1
  funext d
  congr 1
  funext pair
  congr 1
  funext k
  refine congrArg PMF.pure (decide_eq_decide.mpr ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨?_, fun ⟨hne, hv, hv', hc⟩ =>
    ⟨pair.first, .inl rfl, pair.second, .inr rfl, hne, hv, hv', hc⟩⟩
  rintro ⟨m, rfl | rfl, m', rfl | rfl, hne, hv, hv', hc⟩
  · exact (hne rfl).elim
  · exact ⟨hne, hv, hv', hc⟩
  · exact ⟨hne.symm, hv', hv, hc.symm⟩
  · exact (hne rfl).elim

/-- Multi-query UHF security implies single-pair UHF security by submitting both messages in
one batch. The wrapper leaves the public setup program unchanged. -/
theorem IsMultiQueryUHF.isComputationalUHF {encD : D ↪ List Bool} {encM : M ↪ List Bool}
    {setup : ℕ → ProbComp D} {valid : ℕ → D → M → Bool} {H : ℕ → (d : D) → K d → M → Y d}
    (hH : IsMultiQueryUHF encD encM setup valid H) :
    IsComputationalUHF encD encM setup valid H := by
  refine Game.Indistinguishable.of_negligible_succProbability fun _ hA => ?_
  simpa only [multiQueryGame_collisionPairToBatch] using
    hH.negligible_succProbability _ (isPPTOn_collisionPairToBatch hA)

/-- With at most `Q` messages at each supported setup, the multi-query success probability is
at most `Q ^ 2 / 2` times the success probability of the collision-pair sampler. -/
theorem succProbability_multiQueryGame_le_collisionPairReduction
    (setup : ℕ → ProbComp D) (valid : ℕ → D → M → Bool)
    (H : ℕ → (d : D) → K d → M → Y d) (fallback : M)
    (A : ℕ × D → ProbComp (List M)) (n : ℕ) {Q : ℕ}
    (hA : ∀ d ∈ (ProbComp.eval (setup n)).support,
      ∀ ms ∈ (ProbComp.eval (A (n, d))).support, ms.length ≤ Q) :
    Game.succProbability (multiQueryGame setup valid H A n) ≤ ((Q : ℝ≥0) ^ 2 / 2) *
      Game.succProbability (collisionGame setup valid H
        (fun p => collisionPairReduction fallback (A p)) n) := by
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_mul, Game.coe_succProbability_ennreal, Game.coe_succProbability_ennreal,
    ENNReal.coe_div two_ne_zero, ENNReal.coe_pow, ENNReal.coe_natCast, ENNReal.coe_ofNat]
  simp only [multiQueryGame, collisionGame, Game.withSetup, PMF.bind_apply,
    ← ENNReal.tsum_mul_left]
  simp_rw [mul_left_comm ((Q : ℝ≥0∞) ^ 2 / 2)]
  refine Probability.PMF.tsum_mul_mono_support _ fun d hd => ?_
  simpa only [multiQueryExperiment, collisionExperiment, ← valid_collision_iff_hashOn_eq] using
    eval_multiQueryExperiment_le_collisionPairReduction
      (fun k => hashOn (valid n d) (H n d k)) fallback (A (n, d)) (hA d hd)

/-- Computational UHF security implies multi-query UHF security (Boneh–Shoup Lemma 7.1,
[BonehShoup2023], v0.6, printed pp. 254–255). The public setup is strict PPT and varies with the
security parameter. The reduction uses bounded fair-bit sampling, preserving the `Q ^ 2 / 2`
bound, and outputs a losing repeated guess on exhaustion. The bound on the adversary's output
list length comes from the two strict PPT certificates. -/
theorem IsComputationalUHF.isMultiQueryUHF {encD : D ↪ List Bool} {encM : M ↪ List Bool}
    {setup : ℕ → ProbComp D} {valid : ℕ → D → M → Bool} {H : ℕ → (d : D) → K d → M → Y d}
    (hH : IsComputationalUHF encD encM setup valid H) (hsetup : IsPPTOn encUnary encD setup) :
    IsMultiQueryUHF encD encM setup valid H := by
  refine Game.Indistinguishable.of_negligible_succProbability fun A hA => ?_
  rcases isEmpty_or_nonempty M with hM | ⟨⟨fallback⟩⟩
  · have hnil (ms : List M) : ms = [] := ms.eq_nil_iff_forall_not_mem.mpr fun m _ => hM.false m
    simp [multiQueryGame, Game.withSetup, hnil, Game.succProbability]
  obtain ⟨cs, ds, hs⟩ := hsetup.length_le
  obtain ⟨ca, da, ha⟩ := hA.length_le
  let Q (n : ℕ) := ca * (2 * n + 2 + cs * (n + 1) ^ ds) ^ da
  have hQ : PolynomiallyBounded (fun n => Q n ^ 2) := by
    dsimp only [Q]; fun_prop
  refine negligible_of_le ((hH.negligible_succProbability _
    (isPPTOn_collisionPairReduction hA fallback)).polynomiallyBounded_mul hQ) fun n => ?_
  have hlen (d : D) (hd : d ∈ (ProbComp.eval (setup n)).support)
      (ms : List M) (hms : ms ∈ (ProbComp.eval (A (n, d))).support) : ms.length ≤ Q n := by
    have hsetupLen := hs n d hd
    have houtputLen := ha (n, d) ms hms
    simp only [length_encPair, encUnary_apply, List.length_replicate] at hsetupLen houtputLen
    exact (length_le_length_encList _ _).trans (houtputLen.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)))
  refine (succProbability_multiQueryGame_le_collisionPairReduction setup valid H
    fallback A n hlen).trans (mul_le_mul_left ?_ _)
  rw [Nat.cast_pow]
  exact div_le_self zero_le (by norm_num)

end Cslib.Crypto.UHF
