/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction
public import CslibFrontier.Crypto.Encoding
public import CslibFrontier.Crypto.Game.Forgery
public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
public import CslibFrontier.Languages.Probabilistic.Simulation
public import CslibFrontier.Probability.HashFamily
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.HashFamily.UniformOffset
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Probability.Uniform
import CslibFrontier.Tactic.PMFSwap

/-!
# Carter–Wegman message authentication codes from Δ-universal hashing

Wegman and Carter [WegmanCarter1981] observed that an `ε`-almost-Δ-universal (`ε`-DUF / `ε`-AXU)
hash family `hash : K → M → Y` into a finite additive group `Y`
(`Cslib.Probability.IsDeltaUniversalHash`) yields an unconditional message authentication code when
each hash digest `hash k m` is masked by a uniform one-time pad `r ∈ Y`:
`sign hash k r m = hash k m + r` and `verify hash k r m t = decide (hash k m + r = t)`.

For every fixed `(k, m)`, left addition by `hash k m` is a bijection on `Y`, so `t = hash k m + r`
is uniform on `Y` and independent of `k`, with `r = -hash k m + t`. Under `r = -hash k m + t`, a
forgery `(m', t')` with `m' ≠ m` verifies iff `hash k m' - hash k m = t' - t`, which occurs with
probability at most `ε` over `k ← seed` ([BonehShoup2023], Section 7.6, Lemma 7.11 and
Theorem 7.12). Because each `(k, r, m)` admits a unique valid tag, strong and ordinary
unforgeability coincide.

This module develops the core information-theoretic Carter–Wegman experiments (zero-query, one-time,
and adaptive multi-query issued-counter MACs with zero query degradation [WegmanCarter1981]), the
arbitrary-pad and single-query PRF-pad hybrid bounds, and the shared word-level stateful
`prfLogDistinguisher` reduction framework consumed by the stateful nonce-based
(`CarterWegman.Nonce`), randomized-nonce (`CarterWegman.RandomNonce`), and concrete hash
(`CarterWegman.Instantiations`) modules.

## Main definitions

* `Cslib.Crypto.Protocols.CarterWegman.sign`, `Cslib.Crypto.Protocols.CarterWegman.verify`:
  Carter–Wegman tag generation and verification.
* `Cslib.Crypto.Protocols.CarterWegman.zeroQueryGame`,
  `Cslib.Crypto.Protocols.CarterWegman.OneTimeForger`,
  `Cslib.Crypto.Protocols.CarterWegman.oneTimeGame`,
  `Cslib.Crypto.Protocols.CarterWegman.oneTimeStrongGame`: zero-query and adaptive one-time EUF-CMA
  / SUF-CMA experiments.
* `Cslib.Crypto.Protocols.CarterWegman.CounterForger`,
  `Cslib.Crypto.Protocols.CarterWegman.counterRealHandler`,
  `Cslib.Crypto.Protocols.CarterWegman.counterSimHandler`,
  `Cslib.Crypto.Protocols.CarterWegman.transcriptToPads`,
  `Cslib.Crypto.Protocols.CarterWegman.checkCounterSlot`,
  `Cslib.Crypto.Protocols.CarterWegman.checkCounterEUF`,
  `Cslib.Crypto.Protocols.CarterWegman.checkCounterSUF`,
  `Cslib.Crypto.Protocols.CarterWegman.counterSlotGame`,
  `Cslib.Crypto.Protocols.CarterWegman.counterGame`,
  `Cslib.Crypto.Protocols.CarterWegman.counterStrongGame`: adaptive multi-query issued-counter
  handlers, verification predicates, and experiments.
* `Cslib.Crypto.Protocols.CarterWegman.maskedOneTimeGame`,
  `Cslib.Crypto.Protocols.CarterWegman.maskedOneTimeStrongGame`,
  `Cslib.Crypto.Protocols.CarterWegman.padDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.probPadTest`,
  `Cslib.Crypto.Protocols.CarterWegman.encForgeInput`,
  `Cslib.Crypto.Protocols.CarterWegman.wordProbPadTest`,
  `Cslib.Crypto.Protocols.CarterWegman.prfPadDist`,
  `Cslib.Crypto.Protocols.CarterWegman.prfOneTimeGame`,
  `Cslib.Crypto.Protocols.CarterWegman.prfOneTimeStrongGame`,
  `Cslib.Crypto.Protocols.CarterWegman.prfPadDistinguisher`: arbitrary-pad and single-query PRF-pad
  experiments and distinguishers.
* `Cslib.Crypto.Protocols.CarterWegman.carterWegmanKeyGen`,
  `Cslib.Crypto.Protocols.CarterWegman.encLogCaller`,
  `Cslib.Crypto.Protocols.CarterWegman.prfLogDistinguisher`: shared `(k, prfKey)` key generator,
  caller encoding, and generic stateful log-handler `OracleDistinguisher` for multi-query PRF-pad
  reductions.

## Main results

* `Cslib.Crypto.Protocols.CarterWegman.map_sign_eq_uniform`,
  `Cslib.Crypto.Protocols.CarterWegman.uniform_bind_verify_apply_true`,
  `Cslib.Crypto.Protocols.CarterWegman.zeroQueryGame_apply_true`: uniform tag law and exact
  `1 / |Y|` zero-query verification probability.
* `Cslib.Crypto.Protocols.CarterWegman.oneTimeStrongGame_eq_oneTimeGame`,
  `Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_eq_bind_uniform`,
  `Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.oneTimeStrongGame_le`: the Carter–Wegman instance of
  Boneh–Shoup Theorem 7.12 (`≤ ε`).
* `Cslib.Crypto.Protocols.CarterWegman.run_interpret_counterRealHandler`,
  `Cslib.Crypto.Protocols.CarterWegman.counterStrongGame_eq_counterSlotGame`,
  `Cslib.Crypto.Protocols.CarterWegman.counterSlotGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterStrongGame_le`: multi-query issued-counter simulation
  and `≤ ε` security.
* `Cslib.Crypto.Protocols.CarterWegman.maskedOneTimeGame_toReal_le`,
  `Cslib.Crypto.Protocols.CarterWegman.maskedOneTimeGame_toReal_le_add_advantage`,
  `Cslib.Crypto.Protocols.CarterWegman.maskedOneTimeStrongGame_toReal_le_add_advantage`,
  `Cslib.Crypto.Protocols.CarterWegman.prfOneTimeGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.prfOneTimeGame_ofProbComp_le`,
  `Cslib.Crypto.Protocols.CarterWegman.prfOneTimeStrongGame_ofProbComp_le`,
  `Cslib.Crypto.Protocols.CarterWegman.isOraclePPT_prfPadDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.isPPTOn_wordProbPadTest`,
  `Cslib.Crypto.Protocols.CarterWegman.isOraclePPT_prfPadDistinguisher_wordProbPadTest`:
  arbitrary-pad and single-query PRF-pad bounds and `IsOraclePPT` certificates.
* `Cslib.Crypto.Protocols.CarterWegman.isPPTOn_carterWegmanKeyGen`,
  `Cslib.Crypto.Protocols.CarterWegman.isOraclePPT_prfLogDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.eval_prfRealGame_prfLogDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.eval_prfIdealGame_prfLogDistinguisher_le`: shared key-sampler
  PPT certificate, `IsOraclePPT` admissibility, and real/ideal game simulation for
  `prfLogDistinguisher`.

## References

* [M. N. Wegman, J. L. Carter, *New Hash Functions and Their Use in Authentication and Set
  Equality*][WegmanCarter1981]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 7.4–7.6.
-/

public section

namespace Cslib.Crypto.Protocols.CarterWegman

open Cslib.Probability Cslib.Probability.PMF Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Core Carter–Wegman signing, verification, and pad resampling -/

section Core

variable {K M Y : Type*} [AddGroup Y]

/-- Carter–Wegman tag generation ([WegmanCarter1981]; [BonehShoup2023], Section 7.4):
mask the hash digest `hash k m` by adding the pad `r`. -/
@[expose]
def sign (hash : K → M → Y) (k : K) (r : Y) (m : M) : Y :=
  hash k m + r

/-- Carter–Wegman tag verification: check whether `hash k m + r = t`. -/
@[expose]
def verify [DecidableEq Y] (hash : K → M → Y) (k : K) (r : Y) (m : M) (t : Y) : Bool :=
  decide (hash k m + r = t)

@[simp]
theorem verify_eq_true_iff [DecidableEq Y] (hash : K → M → Y) (k : K) (r : Y) (m : M) (t : Y) :
    verify hash k r m t = true ↔ hash k m + r = t :=
  decide_eq_true_iff

@[simp]
theorem verify_sign [DecidableEq Y] (hash : K → M → Y) (k : K) (r : Y) (m : M) :
    verify hash k r m (sign hash k r m) = true := by
  simp [sign, verify]

/-- Every valid tag for `(k, r, m)` equals `sign hash k r m`. -/
theorem eq_sign_of_verify_eq_true [DecidableEq Y] {hash : K → M → Y} {k : K} {r : Y} {m : M}
    {t : Y} (h : verify hash k r m t = true) :
    t = sign hash k r m :=
  ((verify_eq_true_iff hash k r m t).mp h).symm

/-- Solving for the pad `r` from a message–tag pair `(m, t)`:
`sign hash k r m = t ↔ r = -hash k m + t`. -/
theorem sign_eq_iff_eq_neg_add (hash : K → M → Y) (k : K) (r : Y) (m : M) (t : Y) :
    sign hash k r m = t ↔ r = -hash k m + t :=
  ⟨fun h => by rw [← h, sign, neg_add_cancel_left],
    fun h => by rw [h, sign, add_neg_cancel_left]⟩

/-- Because `(k, r, m)` determines a unique valid tag `sign hash k r m`, pair freshness
`(m', t') ≠ (m, sign hash k r m)` and message freshness `m' ≠ m` agree on all verifying pairs. -/
theorem decide_ne_pair_and_verify_eq [DecidableEq M] [DecidableEq Y]
    (hash : K → M → Y) (k : K) (r : Y) (m : M) (p : M × Y) :
    (decide (p ≠ (m, sign hash k r m)) && verify hash k r p.1 p.2) =
      (decide (p.1 ≠ m) && verify hash k r p.1 p.2) := by
  rcases p with ⟨m', t'⟩
  cases hv : verify hash k r m' t'
  · simp
  · simp +contextual [eq_sign_of_verify_eq_true hv]

/-- For a uniform pad `r ← PMF.uniformOfFintype Y`, the tag `sign hash k r m` is uniformly
distributed on `Y` for every `k` and `m`. -/
theorem map_sign_eq_uniform [Fintype Y] [Nonempty Y] (hash : K → M → Y) (k : K) (m : M) :
    (PMF.uniformOfFintype Y).map (sign hash k · m) = PMF.uniformOfFintype Y :=
  PMF.uniformOfFintype_map_add_left (hash k m)

/-- Under a uniform pad `r ← PMF.uniformOfFintype Y`, any fixed `(m, t)` verifies with probability
`(Fintype.card Y : ℝ≥0∞)⁻¹`. -/
theorem uniform_bind_verify_apply_true [Fintype Y] [Nonempty Y] [DecidableEq Y]
    (hash : K → M → Y) (k : K) (m : M) (t : Y) :
    ((PMF.uniformOfFintype Y).bind fun r => PMF.pure (verify hash k r m t)) true =
      (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  have h : ((PMF.uniformOfFintype Y).bind fun r => PMF.pure (verify hash k r m t)) =
      (PMF.uniformOfFintype Y).map (fun x => decide (x = t)) := by
    conv_rhs => rw [← map_sign_eq_uniform hash k m, PMF.map_comp]
    rfl
  rw [h, map_decide_eq_apply_true, PMF.uniformOfFintype_apply]

end Core

/-! ### Zero-query forgery experiment -/

section ZeroQuery

variable {K M Y : Type} [AddGroup Y] [Fintype Y] [Nonempty Y] [DecidableEq Y]

/-- The zero-query forgery experiment: sample `k ← seed`, `r ← PMF.uniformOfFintype Y`, and
`(m', t') ← forger`, and check whether `verify hash k r m' t' = true`. -/
noncomputable def zeroQueryGame (seed : PMF K) (hash : K → M → Y) (forger : PMF (M × Y)) :
    PMF Bool := do
  let k ← seed
  let r ← PMF.uniformOfFintype Y
  let p ← forger
  return verify hash k r p.1 p.2

/-- Without any signing query, every forgery distribution `forger : PMF (M × Y)` succeeds with
probability **exactly** `1 / |Y|`, regardless of the hash family `hash` or key distribution
`seed`. -/
theorem zeroQueryGame_apply_true (seed : PMF K) (hash : K → M → Y) (forger : PMF (M × Y)) :
    zeroQueryGame seed hash forger true = (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  simp only [pmf_norm, zeroQueryGame]
  pmf_hoist forger
  exact bind_apply_of_forall forger fun ⟨m', t'⟩ =>
    bind_apply_of_forall seed fun k => uniform_bind_verify_apply_true hash k m' t'

end ZeroQuery

/-! ### Adaptive one-time Carter–Wegman EUF-CMA and SUF-CMA (Boneh–Shoup Section 7.6) -/

section OneTime

variable {K M Y : Type} [AddGroup Y] [Fintype Y] [Nonempty Y] [DecidableEq M] [DecidableEq Y]

/-- An adaptive one-time forger against a Carter–Wegman MAC:
it chooses a signing query `m ← query`, receives its tag `t = sign hash k r m`, and outputs a
candidate forgery `(m', t') ← forge m t`. -/
structure OneTimeForger (M Y : Type) where
  /-- Distribution of the single signing query `m`. -/
  query : PMF M
  /-- Forgery distribution given the queried message `m` and its tag `t`. -/
  forge : M → Y → PMF (M × Y)

/-- The adaptive one-time EUF-CMA experiment for Carter–Wegman ([BonehShoup2023],
Theorem 7.12): the forger wins if `m' ≠ m` and `verify hash k r m' t' = true`. -/
noncomputable def oneTimeGame (seed : PMF K) (hash : K → M → Y) (forger : OneTimeForger M Y) :
    PMF Bool := do
  let k ← seed
  let r ← PMF.uniformOfFintype Y
  let m ← forger.query
  let p ← forger.forge m (sign hash k r m)
  return (decide (p.1 ≠ m) && verify hash k r p.1 p.2)

/-- The adaptive one-time SUF-CMA (strong unforgeability) experiment:
the forger wins if `(m', t') ≠ (m, sign hash k r m)` and `verify hash k r m' t' = true`. -/
noncomputable def oneTimeStrongGame (seed : PMF K) (hash : K → M → Y)
    (forger : OneTimeForger M Y) : PMF Bool :=
  oneTimeForgeExperiment
    (seed.bind fun k => (PMF.uniformOfFintype Y).map fun r => (k, r))
    (fun key m => PMF.pure (sign hash key.1 key.2 m))
    (fun key => verify hash key.1 key.2)
    (forger.query.map fun m => (m, m)) forger.forge

/-- Strong unforgeability and ordinary unforgeability coincide for the one-time Carter–Wegman MAC,
because each `(k, r, m)` admits a unique valid tag. -/
theorem oneTimeStrongGame_eq_oneTimeGame (seed : PMF K) (hash : K → M → Y)
    (forger : OneTimeForger M Y) :
    oneTimeStrongGame seed hash forger = oneTimeGame seed hash forger := by
  simp only [oneTimeStrongGame, oneTimeForgeExperiment, oneTimeGame, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.pure_bind,
    freshPair, List.mem_singleton, decide_ne_pair_and_verify_eq]

/-- The queried message `m`, uniform tag `t`, and candidate forgery `p = (m', t')` can be sampled
independently of the hash key `k`, which is drawn last to test
`verify hash k (-hash k m + t) m' t'`. -/
theorem oneTimeGame_eq_bind_uniform (seed : PMF K) (hash : K → M → Y)
    (forger : OneTimeForger M Y) :
    oneTimeGame seed hash forger =
      forger.query.bind fun m =>
        (PMF.uniformOfFintype Y).bind fun t =>
          (forger.forge m t).bind fun p =>
            seed.bind fun k =>
              PMF.pure (decide (p.1 ≠ m) && verify hash k (-hash k m + t) p.1 p.2) := by
  dsimp only [oneTimeGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  conv_lhs =>
    enter [2, k]
    rw [PMF.bind_comm]
    enter [2, m]
    simp only [sign]
    rw [PMF.uniformOfFintype_bind_add_offset (hash k m) fun t r =>
      (forger.forge m t).bind fun p =>
        PMF.pure (decide (p.1 ≠ m) && verify hash k r p.1 p.2)]
  pmf_swap

/-- **One-time Carter–Wegman EUF-CMA security** (the Carter–Wegman instance of
[BonehShoup2023], Theorem 7.12; [WegmanCarter1981]): if `hash` is `ε`-almost-Δ-universal under
`seed` (`IsDeltaUniversalHash seed hash ε`), then every adaptive one-time forger succeeds with
probability at most `ε`. -/
theorem oneTimeGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : OneTimeForger M Y) :
    oneTimeGame seed hash forger true ≤ ε := by
  simp only [pmf_norm, oneTimeGame]
  pmf_hoist forger.query
  exact bind_apply_le_on_support forger.query fun m _ =>
    hh.bind_uniform_offset_le m (forger.forge m) Prod.fst Prod.snd

/-- **One-time Carter–Wegman SUF-CMA security**: under `IsDeltaUniversalHash seed hash ε`, every
adaptive one-time forger has strong-forgery probability at most `ε`. -/
theorem oneTimeStrongGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : OneTimeForger M Y) :
    oneTimeStrongGame seed hash forger true ≤ ε := by
  rw [oneTimeStrongGame_eq_oneTimeGame]
  exact oneTimeGame_le hh forger

end OneTime

/-! ### Adaptive multi-query issued-counter Carter–Wegman MAC -/

section Counter

variable {K M Y : Type} [AddGroup Y]

/-- An adaptive multi-query forger against an issued-counter Carter–Wegman MAC:
it draws private coins `s ← coins`, makes any number of adaptive signing queries `m : M` via
`OracleComp (fun _ : M => Y)` (receiving `t_i = sign hash k r_i m_i` under a fresh pad `r_i` for
the `i`-th query), and outputs a target issued counter index `idx : ℕ`, message `m' : M`, and tag
`t' : Y`. -/
structure CounterForger (M Y : Type) where
  /-- Type of the forger's private coins. -/
  Coins : Type
  /-- Distribution of the forger's private coins. -/
  coins : PMF Coins
  /-- Adaptive oracle program outputting `(idx, m', t')`. -/
  forge : Coins → OracleComp (fun _ : M => Y) (ℕ × M × Y)

/-- Real counter Carter–Wegman signing handler: on query `m`, sample a fresh pad
`r ← PMF.uniformOfFintype Y`, append `(m, r)` to the pad log, and return `sign hash k r m`. -/
noncomputable def counterRealHandler [Fintype Y] [Nonempty Y] (hash : K → M → Y) (k : K) (m : M) :
    StateT (List (M × Y)) PMF Y := fun pads => do
  let r ← PMF.uniformOfFintype Y
  return (sign hash k r m, pads ++ [(m, r)])

/-- Simulated key-independent tag handler: on query `m`, sample a fresh uniform tag
`t ← PMF.uniformOfFintype Y`, append `(m, t)` to the message–tag transcript, and return `t`. -/
noncomputable def counterSimHandler [Fintype Y] [Nonempty Y] (m : M) :
    StateT (List (M × Y)) PMF Y := fun tr => do
  let t ← PMF.uniformOfFintype Y
  return (t, tr ++ [(m, t)])

/-- Reconstruct the pad log `[(m_i, -hash k m_i + t_i)]` from a message–tag transcript
`[(m_i, t_i)]`. -/
def transcriptToPads (hash : K → M → Y) (k : K) (tr : List (M × Y)) : List (M × Y) :=
  tr.map fun p => (p.1, -hash k p.1 + p.2)

/-- Running any adaptive `OracleComp` program against `counterRealHandler hash k` from
`transcriptToPads hash k tr` has the exact distribution of running it against the key-independent
`counterSimHandler` from `tr` and applying `transcriptToPads hash k` to the final transcript. -/
theorem run_interpret_counterRealHandler {α : Type} [Fintype Y] [Nonempty Y] (hash : K → M → Y)
    (k : K) (prog : OracleComp (fun _ : M => Y) α) (tr : List (M × Y)) :
    (OracleComp.interpret (counterRealHandler hash k) prog).run (transcriptToPads hash k tr) =
      ((OracleComp.interpret counterSimHandler prog).run tr).map
        (fun x => (x.1, transcriptToPads hash k x.2)) := by
  refine (OracleComp.run_interpret_map_state counterSimHandler (counterRealHandler hash k)
    (transcriptToPads hash k) (fun m s => ?_) prog tr).symm
  dsimp only [counterSimHandler, counterRealHandler, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, StateT.pure]
  rw [PMF.map_bind]
  symm
  simpa only [pmf_norm, sign, transcriptToPads, List.map_append, List.map_cons, List.map_nil] using
    PMF.uniformOfFintype_bind_add_offset (hash k m) fun t r =>
      PMF.pure (t, transcriptToPads hash k s ++ [(m, r)])

variable [DecidableEq M] [DecidableEq Y]

/-- Issued-slot message-freshness verification predicate on a pad log `pads`: the target counter
`idx` was issued (`pads[idx]? = some (m_idx, r_idx)`, returning `false` on unissued indices),
`m' ≠ m_idx`, and `verify hash k r_idx m' t' = true`. -/
@[expose]
def checkCounterSlot (hash : K → M → Y) (k : K) (pads : List (M × Y))
    (out : ℕ × M × Y) : Bool :=
  let idx := out.1
  let cand := out.2
  let m' := cand.1
  let t' := cand.2
  match pads[idx]? with
  | none => false
  | some (m_idx, r_idx) => decide (m' ≠ m_idx) && verify hash k r_idx m' t'

/-- Issued-counter global-message-freshness EUF-CMA verification predicate on a pad log `pads`:
the target counter `idx` was issued (`pads[idx]? = some (_, r_idx)`, returning `false` on unissued
indices), `m'` was never queried in any issued slot (`!(pads.map Prod.fst).contains m'`), and
`verify hash k r_idx m' t' = true`. -/
def checkCounterEUF (hash : K → M → Y) (k : K) (pads : List (M × Y))
    (out : ℕ × M × Y) : Bool :=
  let idx := out.1
  let cand := out.2
  let m' := cand.1
  let t' := cand.2
  match pads[idx]? with
  | none => false
  | some (_, r_idx) =>
    !(pads.map Prod.fst).contains m' && verify hash k r_idx m' t'

/-- Issued-slot strong SUF-CMA verification predicate on a pad log `pads`: the target counter `idx`
was issued (`pads[idx]? = some (m_idx, r_idx)`, returning `false` on unissued indices), the pair
`(m', t')` differs from the pair `(m_idx, sign hash k r_idx m_idx)` issued at counter `idx`, and
`verify hash k r_idx m' t' = true`. -/
@[expose]
def checkCounterSUF (hash : K → M → Y) (k : K) (pads : List (M × Y))
    (out : ℕ × M × Y) : Bool :=
  let idx := out.1
  let cand := out.2
  let m' := cand.1
  let t' := cand.2
  match pads[idx]? with
  | none => false
  | some (m_idx, r_idx) =>
    decide ((m', t') ≠ (m_idx, sign hash k r_idx m_idx)) &&
      verify hash k r_idx m' t'

/-- Issued-slot SUF-CMA and issued-slot EUF-CMA checks are identical on every pad log and
output. -/
theorem checkCounterSUF_eq_checkCounterSlot (hash : K → M → Y) (k : K) (pads : List (M × Y))
    (out : ℕ × M × Y) :
    checkCounterSUF hash k pads out = checkCounterSlot hash k pads out := by
  dsimp only [checkCounterSUF, checkCounterSlot]
  cases pads[out.1]? with
  | none => rfl
  | some p => exact decide_ne_pair_and_verify_eq hash k p.2 p.1 out.2

/-- Issued-counter global message freshness implies issued-slot message freshness at the target
counter `idx`. -/
theorem checkCounterEUF_imp_checkCounterSlot (hash : K → M → Y) (k : K) (pads : List (M × Y))
    (out : ℕ × M × Y) :
    checkCounterEUF hash k pads out = true → checkCounterSlot hash k pads out = true := by
  dsimp only [checkCounterEUF, checkCounterSlot]
  cases hget : pads[out.1]? with
  | none => simp
  | some p =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
      List.mem_map, decide_eq_true_iff]
    rintro ⟨hnotmem, hv⟩
    refine ⟨fun heq => hnotmem ⟨p, List.mem_of_getElem? hget, heq.symm⟩, hv⟩

variable [Fintype Y] [Nonempty Y]

/-- The issued-slot EUF-CMA experiment for the counter Carter–Wegman MAC (unissued indices `idx`
are rejected). -/
noncomputable def counterSlotGame (seed : PMF K) (hash : K → M → Y)
    (forger : CounterForger M Y) : PMF Bool := do
  let k ← seed
  let s ← forger.coins
  let res ← (OracleComp.interpret (counterRealHandler hash k) (forger.forge s)).run []
  return checkCounterSlot hash k res.2 res.1

/-- The issued-counter global-message-freshness EUF-CMA experiment for the counter Carter–Wegman
MAC (unissued indices `idx` are rejected). -/
noncomputable def counterGame (seed : PMF K) (hash : K → M → Y)
    (forger : CounterForger M Y) : PMF Bool := do
  let k ← seed
  let s ← forger.coins
  let res ← (OracleComp.interpret (counterRealHandler hash k) (forger.forge s)).run []
  return checkCounterEUF hash k res.2 res.1

/-- The issued-slot strong SUF-CMA experiment for the counter Carter–Wegman MAC (unissued indices
`idx` are rejected). -/
noncomputable def counterStrongGame (seed : PMF K) (hash : K → M → Y)
    (forger : CounterForger M Y) : PMF Bool := do
  let k ← seed
  let s ← forger.coins
  let res ← (OracleComp.interpret (counterRealHandler hash k) (forger.forge s)).run []
  return checkCounterSUF hash k res.2 res.1

/-- Issued-slot strong unforgeability (`counterStrongGame`) and issued-slot EUF-CMA
(`counterSlotGame`) have identical outcome distributions. -/
theorem counterStrongGame_eq_counterSlotGame (seed : PMF K) (hash : K → M → Y)
    (forger : CounterForger M Y) :
    counterStrongGame seed hash forger = counterSlotGame seed hash forger := by
  simp only [counterStrongGame, counterSlotGame, checkCounterSUF_eq_checkCounterSlot]

/-- Issued-counter global-message-freshness EUF-CMA success probability is at most issued-slot
EUF-CMA success probability. -/
theorem counterGame_le_counterSlotGame (seed : PMF K) (hash : K → M → Y)
    (forger : CounterForger M Y) :
    counterGame seed hash forger true ≤ counterSlotGame seed hash forger true :=
  bind_apply_mono_on_support seed true fun k _ =>
    bind_apply_mono_on_support forger.coins true fun s _ =>
      map_true_mono ((OracleComp.interpret (counterRealHandler hash k) (forger.forge s)).run [])
        fun res _ => checkCounterEUF_imp_checkCounterSlot hash k res.2 res.1

/-- **Multi-query issued-slot Carter–Wegman security** ([WegmanCarter1981];
[BonehShoup2023], Section 7.4): under `IsDeltaUniversalHash seed hash ε`, every adaptive
multi-query forger succeeds in `counterSlotGame` with probability at most `ε`, with zero
degradation in the number of signing queries. -/
theorem counterSlotGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : CounterForger M Y) :
    counterSlotGame seed hash forger true ≤ ε := by
  dsimp only [counterSlotGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hrun (k : K) (s : forger.Coins) :
      (((OracleComp.interpret (counterRealHandler hash k) (forger.forge s)).run []).bind fun res =>
        PMF.pure (checkCounterSlot hash k res.2 res.1)) =
      (((OracleComp.interpret counterSimHandler (forger.forge s)).run []).bind fun res =>
        PMF.pure (checkCounterSlot hash k (transcriptToPads hash k res.2) res.1)) := by
    have h := run_interpret_counterRealHandler hash k (forger.forge s) []
    simp only [transcriptToPads, List.map_nil] at h
    rw [h, PMF.bind_map]
    rfl
  simp only [hrun]
  pmf_hoist forger.coins
  refine bind_apply_le_on_support forger.coins fun s _ => ?_
  pmf_hoist ((OracleComp.interpret counterSimHandler (forger.forge s)).run [])
  refine bind_apply_le_on_support _ fun ⟨⟨idx, m', t'⟩, tr⟩ _ => ?_
  simp only [checkCounterSlot, transcriptToPads, List.getElem?_map]
  cases tr[idx]? with
  | none => simp
  | some p => exact hh.bind_recovered_offset_le p.1 m' p.2 t'

/-- **Multi-query issued-counter Carter–Wegman EUF-CMA security**: under
`IsDeltaUniversalHash seed hash ε`, every adaptive multi-query forger has issued-counter EUF-CMA
forgery probability at most `ε`. -/
theorem counterGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : CounterForger M Y) :
    counterGame seed hash forger true ≤ ε :=
  (counterGame_le_counterSlotGame seed hash forger).trans (counterSlotGame_le hh forger)

/-- **Multi-query issued-slot Carter–Wegman SUF-CMA security**: under
`IsDeltaUniversalHash seed hash ε`, every adaptive multi-query forger has issued-slot SUF-CMA
forgery probability at most `ε`. -/
theorem counterStrongGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : CounterForger M Y) :
    counterStrongGame seed hash forger true ≤ ε := by
  rw [counterStrongGame_eq_counterSlotGame]
  exact counterSlotGame_le hh forger

end Counter

/-! ### Pseudorandom-pad hybrid decomposition (after Boneh–Shoup Section 7.4) -/

section MaskedPad

variable {K M Y : Type} [AddGroup Y] [DecidableEq M] [DecidableEq Y]

/-- The one-time Carter–Wegman experiment with an arbitrary pad distribution `padDist : PMF Y`
(such as a pseudorandom function output `F(k₂, nonce)`). -/
noncomputable def maskedOneTimeGame (seed : PMF K) (padDist : PMF Y) (hash : K → M → Y)
    (forger : OneTimeForger M Y) : PMF Bool := do
  let k ← seed
  let r ← padDist
  let m ← forger.query
  let p ← forger.forge m (sign hash k r m)
  return (decide (p.1 ≠ m) && verify hash k r p.1 p.2)

/-- The strong one-time Carter–Wegman experiment with an arbitrary pad distribution
`padDist : PMF Y`. -/
noncomputable def maskedOneTimeStrongGame (seed : PMF K) (padDist : PMF Y) (hash : K → M → Y)
    (forger : OneTimeForger M Y) : PMF Bool := do
  let k ← seed
  let r ← padDist
  let m ← forger.query
  let t := sign hash k r m
  let p ← forger.forge m t
  return (decide (p ≠ (m, t)) && verify hash k r p.1 p.2)

@[simp]
theorem maskedOneTimeGame_uniform [Fintype Y] [Nonempty Y] (seed : PMF K) (hash : K → M → Y)
    (forger : OneTimeForger M Y) :
    maskedOneTimeGame seed (PMF.uniformOfFintype Y) hash forger =
      oneTimeGame seed hash forger := by
  rfl

theorem maskedOneTimeStrongGame_eq_maskedOneTimeGame (seed : PMF K) (padDist : PMF Y)
    (hash : K → M → Y) (forger : OneTimeForger M Y) :
    maskedOneTimeStrongGame seed padDist hash forger =
      maskedOneTimeGame seed padDist hash forger := by
  simp only [maskedOneTimeStrongGame, maskedOneTimeGame, decide_ne_pair_and_verify_eq]

/-- The induced pad distinguisher `Y → PMF Bool` that samples `k ← seed`, simulates the one-time
Carter–Wegman experiment using the supplied pad `r : Y`, and outputs `true` iff the forger
produces a valid forgery. -/
@[expose]
noncomputable def padDistinguisher (seed : PMF K) (hash : K → M → Y)
    (forger : OneTimeForger M Y) (r : Y) : PMF Bool := do
  let k ← seed
  let m ← forger.query
  let p ← forger.forge m (sign hash k r m)
  return (decide (p.1 ≠ m) && verify hash k r p.1 p.2)

/-- `maskedOneTimeGame` is equivalent to sampling `r ← padDist` and running
`padDistinguisher seed hash forger r`. -/
theorem maskedOneTimeGame_eq_bind_padDistinguisher (seed : PMF K) (padDist : PMF Y)
    (hash : K → M → Y) (forger : OneTimeForger M Y) :
    maskedOneTimeGame seed padDist hash forger =
      padDist.bind (padDistinguisher seed hash forger) :=
  PMF.bind_comm seed padDist _

/-- `Game.advantage` form of the pseudorandom-pad Carter–Wegman bound (after [BonehShoup2023],
Section 7.4): if `hash` is `ε`-almost-Δ-universal (`ε ≠ ⊤`), the real-valued forgery probability
under `padDist` is bounded by `ε.toReal` plus `Game.advantage` between
`padDist.bind (padDistinguisher seed hash forger)` and
`(PMF.uniformOfFintype Y).bind (padDistinguisher seed hash forger)`. -/
theorem maskedOneTimeGame_toReal_le_add_advantage [Fintype Y] [Nonempty Y] {seed : PMF K}
    {hash : K → M → Y} {ε : ℝ≥0∞} (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    (padDist : PMF Y) (forger : OneTimeForger M Y) :
    (maskedOneTimeGame seed padDist hash forger true).toReal ≤
      ε.toReal +
        (Game.advantage (padDist.bind (padDistinguisher seed hash forger))
          ((PMF.uniformOfFintype Y).bind (padDistinguisher seed hash forger)) : ℝ) := by
  rw [maskedOneTimeGame_eq_bind_padDistinguisher, ← Game.coe_succProbability]
  refine (Game.coe_succProbability_le_add_of_advantage_le le_rfl).trans (add_le_add ?_ le_rfl)
  rw [Game.coe_succProbability, ← maskedOneTimeGame_eq_bind_padDistinguisher,
    maskedOneTimeGame_uniform]
  exact ENNReal.toReal_mono hε (oneTimeGame_le hh forger)

/-- **Pseudorandom-pad Carter–Wegman bound** (after [BonehShoup2023], Section 7.4):
if `hash` is `ε`-almost-Δ-universal (`ε ≠ ⊤`), then the real-valued forgery probability under any
pad distribution `padDist : PMF Y` is bounded by `ε.toReal` plus the distinguishing gap of
`padDistinguisher` between `padDist` and `PMF.uniformOfFintype Y`. -/
theorem maskedOneTimeGame_toReal_le [Fintype Y] [Nonempty Y] {seed : PMF K} {hash : K → M → Y}
    {ε : ℝ≥0∞} (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≠ ⊤) (padDist : PMF Y)
    (forger : OneTimeForger M Y) :
    (maskedOneTimeGame seed padDist hash forger true).toReal ≤
      ε.toReal +
        |((padDist.bind (padDistinguisher seed hash forger)) true).toReal -
          (((PMF.uniformOfFintype Y).bind (padDistinguisher seed hash forger)) true).toReal| := by
  simpa only [Game.coe_advantage, Game.coe_succProbability] using
    maskedOneTimeGame_toReal_le_add_advantage hh hε padDist forger

/-- Strong-unforgeability version of `maskedOneTimeGame_toReal_le_add_advantage`. -/
theorem maskedOneTimeStrongGame_toReal_le_add_advantage [Fintype Y] [Nonempty Y] {seed : PMF K}
    {hash : K → M → Y} {ε : ℝ≥0∞} (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    (padDist : PMF Y) (forger : OneTimeForger M Y) :
    (maskedOneTimeStrongGame seed padDist hash forger true).toReal ≤
      ε.toReal +
        (Game.advantage (padDist.bind (padDistinguisher seed hash forger))
          ((PMF.uniformOfFintype Y).bind (padDistinguisher seed hash forger)) : ℝ) := by
  rw [maskedOneTimeStrongGame_eq_maskedOneTimeGame]
  exact maskedOneTimeGame_toReal_le_add_advantage hh hε padDist forger

/-- Construct a `OneTimeForger` from `ProbComp` query and forgery programs. -/
@[expose]
noncomputable def OneTimeForger.ofProbComp (query : ProbComp M)
    (forge : M → Y → ProbComp (M × Y)) : OneTimeForger M Y where
  query := ProbComp.eval query
  forge m t := ProbComp.eval (forge m t)

/-- Executable `ProbComp` simulation of the one-time Carter–Wegman experiment with a supplied pad
`r : Y`, given `ProbComp` samplers for the hash key `seed`, signing query `query`, and forgery
attempt `forge`. -/
def probPadTest (seed : ProbComp K) (hash : K → M → Y) (query : ProbComp M)
    (forge : M → Y → ProbComp (M × Y)) (r : Y) : ProbComp Bool := do
  let k ← seed
  let m ← query
  let p ← forge m (sign hash k r m)
  return (decide (p.1 ≠ m) && verify hash k r p.1 p.2)

@[simp]
theorem eval_probPadTest (seed : ProbComp K) (hash : K → M → Y) (query : ProbComp M)
    (forge : M → Y → ProbComp (M × Y)) (r : Y) :
    ProbComp.eval (probPadTest seed hash query forge r) =
      padDistinguisher (ProbComp.eval seed) hash (OneTimeForger.ofProbComp query forge) r := by
  simp [probPadTest, padDistinguisher, OneTimeForger.ofProbComp, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.map, Function.comp_def]

end MaskedPad

/-! ### One-query, fixed-nonce PRF-pad reduction (after Boneh–Shoup Section 7.4) -/

section PRFPad

variable {K M : Type} [DecidableEq M]

/-- The one-time pad distribution on `BitString n` obtained by sampling a uniform `n`-bit PRF key
`key ← BitString.uniformList n` and evaluating `family key (List.replicate n false)`. -/
@[expose]
noncomputable def prfPadDist (family : List Bool → List Bool → List Bool) (n : ℕ) :
    PMF (BitString n) :=
  (BitString.uniformList n).map fun key =>
    BitString.ofList n (family key (List.replicate n false))

/-- The one-query, fixed-nonce PRF-masked Carter–Wegman EUF-CMA experiment (after
[BonehShoup2023], Section 7.4): the pad `r : BitString n` is generated by evaluating `family` on a
uniform `n`-bit PRF key at the fixed nonce `List.replicate n false`. -/
@[expose]
noncomputable def prfOneTimeGame (seed : PMF K) (family : List Bool → List Bool → List Bool)
    (n : ℕ) (hash : K → M → BitString n) (forger : OneTimeForger M (BitString n)) : PMF Bool :=
  maskedOneTimeGame seed (prfPadDist family n) hash forger

/-- The one-query, fixed-nonce PRF-masked Carter–Wegman SUF-CMA experiment (after
[BonehShoup2023], Section 7.4). -/
noncomputable def prfOneTimeStrongGame (seed : PMF K)
    (family : List Bool → List Bool → List Bool) (n : ℕ) (hash : K → M → BitString n)
    (forger : OneTimeForger M (BitString n)) : PMF Bool :=
  maskedOneTimeStrongGame seed (prfPadDist family n) hash forger

theorem prfOneTimeStrongGame_eq_prfOneTimeGame (seed : PMF K)
    (family : List Bool → List Bool → List Bool) (n : ℕ) (hash : K → M → BitString n)
    (forger : OneTimeForger M (BitString n)) :
    prfOneTimeStrongGame seed family n hash forger =
      prfOneTimeGame seed family n hash forger :=
  maskedOneTimeStrongGame_eq_maskedOneTimeGame seed (prfPadDist family n) hash forger

/-- Single-query PRF `OracleDistinguisher` induced by a family of `ProbComp` pad tests
`test : (k : ℕ) → BitString k → ProbComp Bool`: at security parameter `n`, query the oracle once at
the fixed nonce `List.replicate n false` and run `test n` on the `n`-bit view of the reply. -/
def prfPadDistinguisher (test : (k : ℕ) → BitString k → ProbComp Bool) :
    OracleDistinguisher := fun n _ => do
  let reply ← ProbOracleComp.query ((), List.replicate n false)
  ProbOracleComp.sample (test n (BitString.ofList n reply))

/-- In `prfRealGame`, `prfPadDistinguisher test` evaluates `test n` on a pad drawn from
`prfPadDist family n`. -/
theorem eval_prfRealGame_prfPadDistinguisher (family : List Bool → List Bool → List Bool)
    (test : (k : ℕ) → BitString k → ProbComp Bool) (n : ℕ) :
    ProbComp.eval (prfRealGame id family (prfPadDistinguisher test) n) =
      (prfPadDist family n).bind (fun r => ProbComp.eval (test n r)) := by
  simp only [pmf_norm, prfRealGame, id_eq, prfPadDistinguisher, prfPadDist,
    BitString.eval_sampleList]
  congr 1
  funext key
  simp [prfOracle]

/-- In `prfIdealGame`, `prfPadDistinguisher test` evaluates `test n` on a uniform pad
`r ← PMF.uniformOfFintype (BitString n)`. -/
theorem eval_prfIdealGame_prfPadDistinguisher (test : (k : ℕ) → BitString k → ProbComp Bool)
    (n : ℕ) :
    ProbComp.eval (prfIdealGame id id (prfPadDistinguisher test) n) =
      (PMF.uniformOfFintype (BitString n)).bind (fun r => ProbComp.eval (test n r)) := by
  conv_rhs =>
    rw [← PMF.pi_map_eval (fun _ => PMF.uniformOfFintype (BitString n))
        (BitString.ofList n (List.replicate n false)),
      PMF.pi_uniformOfFintype, PMF.bind_map]
  simp only [prfIdealGame, id_eq, prfPadDistinguisher, ProbComp.eval_bind, ProbComp.eval_uniform,
    Function.comp_def]
  congr 1
  funext table
  simp [randomFunctionOracle]

/-- **Exact single-query PRF-pad reduction for `prfOneTimeGame`** in the one-query, fixed-nonce
case (after [BonehShoup2023], Section 7.4): replacing the uniform pad
`r ← PMF.uniformOfFintype (BitString n)` with the fixed-nonce PRF pad `prfPadDist family n` bounds
the real-valued one-time forgery probability at parameter `n` by `ε.toReal` plus the concrete PRF
distinguishing advantage of `prfPadDistinguisher test` between `prfRealGame` and `prfIdealGame`.
This is a concrete lemma: the caller supplies the pad test together with the equation `htest` that
it realizes `padDistinguisher seed hash forger`. -/
theorem prfOneTimeGame_le {n : ℕ} {seed : PMF K} {hash : K → M → BitString n} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    (family : List Bool → List Bool → List Bool)
    (forger : OneTimeForger M (BitString n))
    (test : (k : ℕ) → BitString k → ProbComp Bool)
    (htest : ∀ r, padDistinguisher seed hash forger r = ProbComp.eval (test n r)) :
    (prfOneTimeGame seed family n hash forger true).toReal ≤
      ε.toReal +
        (Game.advantage
          (ProbComp.eval (prfRealGame id family (prfPadDistinguisher test) n))
          (ProbComp.eval (prfIdealGame id id (prfPadDistinguisher test) n)) : ℝ) := by
  simp only [eval_prfRealGame_prfPadDistinguisher, eval_prfIdealGame_prfPadDistinguisher, ← htest]
  exact maskedOneTimeGame_toReal_le_add_advantage hh hε (prfPadDist family n) forger

/-- **Exact single-query PRF-pad reduction for `ProbComp` samplers and forgers** in the one-query,
fixed-nonce case (after [BonehShoup2023], Section 7.4): at parameter `n`, any `ProbComp` hash-key
sampler `seed`, query program `query`, and forgery program `forge` induce the single-query PRF
distinguisher via `probPadTest`, without asserting `IsOraclePPT encBool` admissibility or an
asymptotic `PseudorandomFunction` corollary. -/
theorem prfOneTimeGame_ofProbComp_le {n : ℕ} {seed : ProbComp K}
    {hash : K → M → BitString n} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash (ProbComp.eval seed) hash ε) (hε : ε ≠ ⊤)
    (family : List Bool → List Bool → List Bool)
    (query : ProbComp M) (forge : M → BitString n → ProbComp (M × BitString n)) :
    (prfOneTimeGame (ProbComp.eval seed) family n hash
      (OneTimeForger.ofProbComp query forge) true).toReal ≤
      ε.toReal +
        (Game.advantage
          (ProbComp.eval (prfRealGame id family
            (prfPadDistinguisher fun _ r =>
              probPadTest seed hash query forge (BitString.ofList n (List.ofFn r))) n))
          (ProbComp.eval (prfIdealGame id id
            (prfPadDistinguisher fun _ r =>
              probPadTest seed hash query forge (BitString.ofList n (List.ofFn r))) n)) : ℝ) := by
  refine prfOneTimeGame_le hh hε family (OneTimeForger.ofProbComp query forge) _ fun r => ?_
  simp

/-- Strong-unforgeability version of `prfOneTimeGame_ofProbComp_le`. -/
theorem prfOneTimeStrongGame_ofProbComp_le {n : ℕ} {seed : ProbComp K}
    {hash : K → M → BitString n} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash (ProbComp.eval seed) hash ε) (hε : ε ≠ ⊤)
    (family : List Bool → List Bool → List Bool)
    (query : ProbComp M) (forge : M → BitString n → ProbComp (M × BitString n)) :
    (prfOneTimeStrongGame (ProbComp.eval seed) family n hash
      (OneTimeForger.ofProbComp query forge) true).toReal ≤
      ε.toReal +
        (Game.advantage
          (ProbComp.eval (prfRealGame id family
            (prfPadDistinguisher fun _ r =>
              probPadTest seed hash query forge (BitString.ofList n (List.ofFn r))) n))
          (ProbComp.eval (prfIdealGame id id
            (prfPadDistinguisher fun _ r =>
              probPadTest seed hash query forge (BitString.ofList n (List.ofFn r))) n)) : ℝ) := by
  rw [prfOneTimeStrongGame_eq_prfOneTimeGame]
  exact prfOneTimeGame_ofProbComp_le hh hε family query forge

/-- `prfPadDistinguisher test` is uniformly strict oracle-PPT (`IsOraclePPT encBool`) whenever
running `test n` on the `n`-bit view of a raw pad word is uniformly strict PPT in `(n, word)`. -/
theorem isOraclePPT_prfPadDistinguisher
    {test : (k : ℕ) → BitString k → ProbComp Bool}
    (htest : IsPPTOn (encPair encUnary encBits) encBool
      (fun p : ℕ × List Bool => test p.1 (BitString.ofList p.1 p.2))) :
    IsOraclePPT encBool (prfPadDistinguisher test) := by
  have heq : prfPadDistinguisher test =
      (fun n _ => do
        let reply ← List.take n <$> ProbOracleComp.query ((), List.replicate n false)
        ProbOracleComp.sample (test n (BitString.ofList n reply))) := by
    funext n _; simp [prfPadDistinguisher, BitString.ofList_take]
  rw [heq]
  exact ((IsOraclePPTOn.query_take () (by fun_prop) (by fun_prop)).bind_with
    ((htest.preprocess (prepare := fun p : (ℕ × List Bool) × List Bool => (p.1.1, p.2))
      (by fun_prop)).isOraclePPTOn)).isOraclePPT

/-- Input `(1ⁿ, m, t)` of the forgery program of `wordProbPadTest`: the security parameter `n` in
unary, then the queried message and its tag as bit words. The parameter and the message are
framed. -/
abbrev encForgeInput : ℕ × List Bool × List Bool ↪ List Bool :=
  encPair encUnary (encPair encBits encBits)

/-- Executable `ProbComp` one-time pad test induced by a uniform word-level hash-key sampler `seed`,
hash evaluator `hash`, signing query `query`, and forgery program `forge`: at security parameter `n`
and pad `r : BitString n`, it runs `probPadTest` with digest `BitString.ofList n (hash n k m)` and
candidate tag `BitString.ofList n p.2`. -/
def wordProbPadTest (seed : ℕ → ProbComp (List Bool))
    (hash : ℕ → List Bool → List Bool → List Bool)
    (query : ℕ → ProbComp (List Bool))
    (forge : ℕ → List Bool → List Bool → ProbComp (List Bool × List Bool))
    (n : ℕ) (r : BitString n) : ProbComp Bool :=
  probPadTest (seed n) (fun k m => BitString.ofList n (hash n k m)) (query n)
    (fun m t => do
      let p ← forge n m (List.ofFn t)
      return (p.1, BitString.ofList n p.2)) r

@[simp]
theorem eval_wordProbPadTest (seed : ℕ → ProbComp (List Bool))
    (hash : ℕ → List Bool → List Bool → List Bool)
    (query : ℕ → ProbComp (List Bool))
    (forge : ℕ → List Bool → List Bool → ProbComp (List Bool × List Bool))
    (n : ℕ) (r : BitString n) :
    ProbComp.eval (wordProbPadTest seed hash query forge n r) =
      padDistinguisher (ProbComp.eval (seed n))
        (fun k m => BitString.ofList n (hash n k m))
        (OneTimeForger.ofProbComp (query n) (fun m t => do
          let p ← forge n m (List.ofFn t)
          return (p.1, BitString.ofList n p.2))) r := by
  exact eval_probPadTest _ _ _ _ r

/-- If `seed`, `hash`, `query`, and `forge` are uniformly polynomial-time / strict PPT in their
encoded inputs, then `wordProbPadTest` on the `n`-bit view of a raw pad word is uniformly strict
PPT. -/
theorem isPPTOn_wordProbPadTest
    {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {query : ℕ → ProbComp (List Bool)}
    {forge : ℕ → List Bool → List Bool → ProbComp (List Bool × List Bool)}
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    (hquery : IsPPTOn encUnary encBits query)
    (hforge : IsPPTOn encForgeInput (encPair encBits encBits) (fun (n, m, t) => forge n m t)) :
    IsPPTOn (encPair encUnary encBits) encBool
      (fun p : ℕ × List Bool =>
        wordProbPadTest seed hash query forge p.1 (BitString.ofList p.1 p.2)) := by
  have heq : (fun p : ℕ × List Bool =>
      wordProbPadTest seed hash query forge p.1 (BitString.ofList p.1 p.2)) =
      fun p : ℕ × List Bool => do
        let k ← seed p.1
        let m ← query p.1
        let out ← forge p.1 m (BitString.listXor p.1 [hash p.1 k m, p.2])
        return (!(out.1 == m) &&
          (BitString.listXor p.1 [hash p.1 k out.1, p.2] ==
            BitString.listRow p.1 0 out.2)) := by
    funext ⟨n, rawPad⟩
    simp only [wordProbPadTest, probPadTest, sign, verify, bind_assoc, pure_bind,
      BitString.listXor_pair, BitString.listRow_zero, _root_.decide_not,
      Bool.beq_eq_decide_eq, List.ofFn_injective.eq_iff]
  rw [heq]
  exact (hseed.preprocess (by fun_prop)).bind_with
    ((hquery.preprocess (by fun_prop)).bind_with
      ((hforge.preprocess
        (prepare := fun q : ((ℕ × List Bool) × List Bool) × List Bool =>
          (q.1.1.1, q.2, BitString.listXor q.1.1.1 [hash q.1.1.1 q.1.2 q.2, q.1.1.2]))
        (by fun_prop)).bind_with (ComputableInPolyTime.isPPTOn (by fun_prop))))

/-- `prfPadDistinguisher (wordProbPadTest seed hash query forge)` is uniformly strict oracle-PPT
(`IsOraclePPT encBool`) for any uniform polynomial-time / strict-PPT family `(seed, hash, query,
forge)`. -/
theorem isOraclePPT_prfPadDistinguisher_wordProbPadTest
    {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {query : ℕ → ProbComp (List Bool)}
    {forge : ℕ → List Bool → List Bool → ProbComp (List Bool × List Bool)}
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    (hquery : IsPPTOn encUnary encBits query)
    (hforge : IsPPTOn encForgeInput (encPair encBits encBits) (fun (n, m, t) => forge n m t)) :
    IsOraclePPT encBool (prfPadDistinguisher (wordProbPadTest seed hash query forge)) :=
  isOraclePPT_prfPadDistinguisher (isPPTOn_wordProbPadTest hseed hhash hquery hforge)

end PRFPad

/-! ### Shared stateful log-handler PRF reduction -/

section LogHandlerSim

private theorem interpret_deterministic_run_interpret {State α : Type}
    (g : List Bool → List Bool)
    (handler : Unit × List Bool → StateT State (WordOracleComp Unit) (List Bool))
    (prog : WordOracleComp Unit α) (s : State) :
    OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifFin (fun request => pure (g request.2)))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          handler)
        prog).run s) =
    (OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbComp.unifFin k))
        (fun request state =>
          OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifFin (fun req => pure (g req.2)))
            (handler request state)))
      prog).run s := by
  have hf : IsMonadHom (WordOracleComp Unit) ProbComp
      (OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifFin (fun request => pure (g request.2)))) :=
    PFunctor.FreeM.isMonadHom_liftM _
  rw [OracleComp.map_run_interpret hf]
  congr 2
  funext q state
  cases q with
  | inl k => simp [OracleComp.sumHandler, StateT.lift, ProbComp.unifFin]
  | inr request => rfl

private theorem eval_interpret_logHandler_le_runWith_adapt
    {Query : Type} {spec : Query → Type} {Out WState TState : Type}
    (extOracle : List Bool → List Bool)
    (wordHandler : Unit × List Bool → StateT WState (WordOracleComp Unit) (List Bool))
    (typedHandler : (q : Query) → StateT TState PMF (spec q))
    (adaptStep : Unit × List Bool → StateT WState (ProbOracleComp spec) (List Bool))
    (R : TState → WState → Prop)
    (wordCheck : Out × WState → Bool)
    (typedCheck : (Out × WState) × TState → Bool)
    (hstep : ∀ request wstate tstate, R tstate wstate →
      let rhs := ProbOracleComp.runWith typedHandler (adaptStep request wstate) tstate
      rhs.map Prod.fst =
        ProbComp.eval
          (OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifFin (fun req => pure (extOracle req.2)))
            (wordHandler request wstate)) ∧
        ∀ reply wstate' tstate', ((reply, wstate'), tstate') ∈ rhs.support → R tstate' wstate')
    (hcheck : ∀ a wstate tstate, R tstate wstate →
      wordCheck (a, wstate) = true → typedCheck ((a, wstate), tstate) = true)
    (prog : WordOracleComp Unit Out) (wstate : WState) (tstate : TState)
    (hR : R tstate wstate) :
    ((ProbComp.eval
      (OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifFin (fun req => pure (extOracle req.2)))
        ((OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            wordHandler)
          prog).run wstate))).bind fun out => PMF.pure (wordCheck out)) true ≤
    ((ProbOracleComp.runWith typedHandler
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          adaptStep)
        prog).run wstate) tstate).bind fun res => PMF.pure (typedCheck res)) true := by
  rw [interpret_deterministic_run_interpret, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.runWith_eq_run_interpret, ProbOracleComp.runWith_eq_run_interpret]
  induction prog using OracleComp.induction generalizing wstate tstate with
  | pure a =>
    simp only [OracleComp.run_interpret_pure, PMF.monad_pure_eq_pure, PMF.pure_bind]
    by_cases h : wordCheck (a, wstate) = true
    · rw [h, hcheck a wstate tstate hR h]
    · simp [Bool.eq_false_iff.mpr h]
  | query_bind q cont ih =>
    rw [PFunctor.FreeM.bind_eq_bind, OracleComp.run_interpret_bind,
      OracleComp.run_interpret_query,
      OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
      OracleComp.run_interpret_bind]
    cases q with
    | inl m =>
      have hsample :
          (StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)) wstate :
            ProbOracleComp spec (Fin (m + 1) × WState)) =
          (OracleComp.query (Sum.inl m) >>= fun i => pure (i, wstate)) := by
        simp [StateT.lift, ProbOracleComp.sample, ProbComp.unifFin]
      rw [OracleComp.sumHandler, OracleComp.sumHandler, hsample,
        OracleComp.run_interpret_bind, OracleComp.run_interpret_query]
      simp only [pmf_norm, OracleComp.sumHandler, StateT.lift, OracleComp.run_interpret_pure]
      exact bind_apply_mono_on_support (ProbComp.unifOracle m) true fun i _ =>
        ih i wstate tstate hR
    | inr request =>
      dsimp only [OracleComp.sumHandler]
      obtain ⟨hmap, hrel⟩ := hstep request wstate tstate hR
      simp only [PMF.monad_bind_eq_bind, PMF.bind_bind]
      rw [← ProbOracleComp.runWith_eq_run_interpret, ← hmap, PMF.bind_map]
      exact bind_apply_mono_on_support _ true fun ⟨⟨reply, wstate'⟩, tstate'⟩ hmem =>
        ih reply wstate' tstate' (hrel reply wstate' tstate' hmem)

/-- Shared word-level secret-key sampler for computational Carter–Wegman MACs: samples `k ← seed n`
and `prfKey ← BitString.sampleList n`, returning `encPair encBits encBits (k, prfKey)`. -/
@[expose]
noncomputable def carterWegmanKeyGen (seed : ℕ → ProbComp (List Bool)) (n : ℕ) :
    ProbComp (List Bool) := do
  let k ← seed n
  let prfKey ← BitString.sampleList n
  return encPair encBits encBits (k, prfKey)

/-- `carterWegmanKeyGen seed` is uniformly strict PPT whenever `seed` is uniformly strict PPT. -/
theorem isPPTOn_carterWegmanKeyGen {seed : ℕ → ProbComp (List Bool)}
    (hseed : IsPPTOn encUnary encBits seed) :
    IsPPTOn encUnary encBits (carterWegmanKeyGen seed) := by
  refine hseed.bind_with ((ComputableInPolyTime.sampleList (by fun_prop)).bind_with ?_)
  apply ComputableInPolyTime.isPPTOn
  fun_prop

/-- Caller context encoding `((n, aux), k)` for `prfLogDistinguisher`, pairing the distinguisher's
`(n, aux)` input with the sampled hash key `k`. -/
abbrev encLogCaller : (ℕ × List Bool) × List Bool ↪ List Bool :=
  encPair (encPair encUnary encBits) encBits

/-- Generic stateful log-handler `OracleDistinguisher` for multi-query Carter–Wegman PRF reductions:
sample `k ← seed n`, run `adversary n []` from the empty log `[]` under `logHandler n k`, query the
external PRF/RF oracle on `candNonce out` (reading `n` bits), and test `accept n k out`. -/
def prfLogDistinguisher {Entry Out : Type}
    (seed : ℕ → ProbComp (List Bool))
    (logHandler : ℕ → List Bool → Unit × List Bool →
      StateT (List Entry) (WordOracleComp Unit) (List Bool))
    (adversary : (n : ℕ) → List Bool → WordOracleComp Unit Out)
    (candNonce : Out × List Entry → List Bool)
    (accept : ℕ → List Bool → Out × List Entry → List Bool → Bool) :
    OracleDistinguisher := fun n _ => do
  let k ← ProbOracleComp.sample (seed n)
  let out ←
    (OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (logHandler n k))
      (adversary n [])).run []
  (accept n k out) <$> (List.take n <$> ProbOracleComp.query ((), candNonce out))

/-- `prfLogDistinguisher` is uniformly strict oracle-PPT (`IsOraclePPT encBool`) whenever `seed`,
`adversary`, `logHandler`, `candNonce`, and `accept` satisfy the corresponding uniform polytime /
strict-PPT bounds with per-step reply/log growth allowance `resources`. -/
theorem isOraclePPT_prfLogDistinguisher {Entry Out : Type}
    {encOp : Unit ↪ List Bool} {encEntry : Entry ↪ List Bool} {encOut : Out ↪ List Bool}
    {seed : ℕ → ProbComp (List Bool)}
    {logHandler : ℕ → List Bool → Unit × List Bool →
      StateT (List Entry) (WordOracleComp Unit) (List Bool)}
    {adversary : (n : ℕ) → List Bool → WordOracleComp Unit Out}
    {candNonce : Out × List Entry → List Bool}
    {accept : ℕ → List Bool → Out × List Entry → List Bool → Bool}
    (hseed : IsPPTOn encUnary encBits seed)
    (hadversary : IsOraclePPT encOut adversary)
    (hhandler : IsOraclePPTOn
      (encHandlerCall encLogCaller encOp (encList encEntry))
      (encPair encBits (encList encEntry))
      (fun ⟨((n, _), k), request, log⟩ => logHandler n k request log))
    (resources : (ℕ × List Bool) × List Bool → List Bool → ℕ)
    (hresources : ComputableInPolyTime (fun p => resources p.1 p.2)
      (encPair encLogCaller encBits) encUnary)
    (hpreserve : ∀ np k request log,
      ∀ result ∈ OracleComp.support (logHandler np.1 k request log),
        result.1.length ≤ resources (np, k) request.2 ∧
          (encList encEntry result.2).length ≤
            (encList encEntry log).length + resources (np, k) request.2)
    (hcand : ComputableInPolyTime candNonce (encPair encOut (encList encEntry)) encBits)
    (haccept : ComputableInPolyTime
      (fun p : (((ℕ × List Bool) × List Bool) × (Out × List Entry)) × List Bool =>
        accept p.1.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair encLogCaller (encPair encOut (encList encEntry))) encBits) encBool) :
    IsOraclePPT encBool (prfLogDistinguisher seed logHandler adversary candNonce accept) := by
  have hrun : IsOraclePPTOn encLogCaller (encPair encOut (encList encEntry))
      (fun caller : (ℕ × List Bool) × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (logHandler caller.1.1 caller.2))
          (adversary caller.1.1 [])).run []) := by
    apply hadversary.run_interpret_preprocess_open
      (prepare := fun caller : (ℕ × List Bool) × List Bool => (caller.1.1, ([] : List Bool)))
      (initial := fun _ => ([] : List Entry))
      (resources := resources)
      (by fun_prop) hhandler (by fun_prop)
      (fun _ _ => True) (fun _ => trivial) hresources
    intro ⟨np, k⟩ request log _ result hresult
    obtain ⟨h1, h2⟩ := hpreserve np k request log result hresult
    exact ⟨trivial, h1, h2⟩
  exact (((hseed.preprocess (ComputableInPolyTime.fst _ _)).isOraclePPTOn).bind_with
    (hrun.bind_with
      ((IsOraclePPTOn.query_take () (hcand.comp (ComputableInPolyTime.snd _ _))
        (by fun_prop)).map_with haccept))).isOraclePPT

/-- Real-game simulation for `prfLogDistinguisher`: when `prfKey` has length `n`, if interpreting
`prfOracle family n prfKey` into each `logHandler n k` step agrees in `ProbComp.eval` with
`realOracle (encPair encBits encBits (k, prfKey))` and `accept n k out` on the `n`-bit PRF output at
`candNonce out` agrees with `realCheck (encPair encBits encBits (k, prfKey)) out`, then running
`prfLogDistinguisher` in `prfRealGame id family` matches running `realOracle` and `realCheck` under
`k ← seed n`, `prfKey ← BitString.sampleList n`. -/
theorem eval_prfRealGame_prfLogDistinguisher {Entry Out : Type}
    (family : List Bool → List Bool → List Bool)
    (seed : ℕ → ProbComp (List Bool))
    (logHandler : ℕ → List Bool → Unit × List Bool →
      StateT (List Entry) (WordOracleComp Unit) (List Bool))
    (adversary : (n : ℕ) → List Bool → WordOracleComp Unit Out)
    (candNonce : Out × List Entry → List Bool)
    (accept : ℕ → List Bool → Out × List Entry → List Bool → Bool)
    (realOracle : List Bool → Unit × List Bool → StateT (List Entry) ProbComp (List Bool))
    (realCheck : List Bool → Out × List Entry → Bool) (n : ℕ)
    (hstep : ∀ k prfKey, prfKey.length = n → ∀ request state,
      ProbComp.eval
        (OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifFin
            (fun req => pure (prfOracle family n prfKey req.2)))
          (logHandler n k request state)) =
      ProbComp.eval (realOracle (encPair encBits encBits (k, prfKey)) request state))
    (hcheck : ∀ k prfKey, prfKey.length = n → ∀ out,
      accept n k out ((prfOracle family n prfKey (candNonce out)).take n) =
        realCheck (encPair encBits encBits (k, prfKey)) out) :
    ProbComp.eval
      (prfRealGame id family
        (prfLogDistinguisher seed logHandler adversary candNonce accept) n) =
    ProbComp.eval (do
      let sk ← carterWegmanKeyGen seed n
      let out ←
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbComp.unifFin m))
            (realOracle sk))
          (adversary n [])).run []
      pure (realCheck sk out)) := by
  simp only [pmf_norm, prfRealGame, id_eq, ProbOracleComp.run, prfLogDistinguisher,
    carterWegmanKeyGen, Functor.map_map, OracleComp.interpret_bind, OracleComp.interpret_map,
    ProbOracleComp.interpret_sample, ProbOracleComp.interpret_query, ProbComp.interpret_unifFin]
  pmf_hoist (ProbComp.eval (seed n))
  refine PMF.bind_congr_on_support _ _ _ fun k _ => ?_
  refine PMF.bind_congr_on_support _ _ _ fun prfKey hprfKey => ?_
  rw [BitString.eval_sampleList] at hprfKey
  have hprfLen : prfKey.length = n := BitString.length_of_mem_support_uniformList hprfKey
  rw [interpret_deterministic_run_interpret, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.eval_run_interpret_eq_runWith,
    show (fun request state =>
        ProbComp.eval
          (OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifFin
              (fun req => pure (prfOracle family n prfKey req.2)))
            (logHandler n k request state))) = _ from
      funext fun request => funext (hstep k prfKey hprfLen request)]
  refine PMF.bind_congr_on_support _ _ _ fun out _ => ?_
  rw [hcheck k prfKey hprfLen out]

/-- Ideal-game simulation inequality for `prfLogDistinguisher`: bounds the acceptance probability of
`prfLogDistinguisher` in `prfIdealGame id id` by that of a typed stateful `PMF` handler
`typedHandler` composed with a word-to-typed step adapter `adaptStep` under step invariant `R`. -/
theorem eval_prfIdealGame_prfLogDistinguisher_le
    {Query : Type} {spec : Query → Type} {Entry Out TState : Type}
    (seed : ℕ → ProbComp (List Bool))
    (logHandler : ℕ → List Bool → Unit × List Bool →
      StateT (List Entry) (WordOracleComp Unit) (List Bool))
    (adversary : (n : ℕ) → List Bool → WordOracleComp Unit Out)
    (candNonce : Out × List Entry → List Bool)
    (accept : ℕ → List Bool → Out × List Entry → List Bool → Bool) (n : ℕ)
    (typedHandler : List Bool → (BitString n → BitString n) →
      (q : Query) → StateT TState PMF (spec q))
    (adaptStep : Unit × List Bool → StateT (List Entry) (ProbOracleComp spec) (List Bool))
    (initTState : TState)
    (R : TState → List Entry → Prop)
    (typedCheck : List Bool → (BitString n → BitString n) → (Out × List Entry) × TState → Bool)
    (hinit : R initTState [])
    (hstep : ∀ k table request wstate tstate, R tstate wstate →
      let rhs := ProbOracleComp.runWith (typedHandler k table) (adaptStep request wstate) tstate
      rhs.map Prod.fst =
        ProbComp.eval
          (OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifFin
              (fun req => pure (randomFunctionOracle n table req.2)))
            (logHandler n k request wstate)) ∧
        ∀ reply wstate' tstate', ((reply, wstate'), tstate') ∈ rhs.support → R tstate' wstate')
    (hcheck : ∀ k table a wstate tstate, R tstate wstate →
      accept n k (a, wstate) ((randomFunctionOracle n table (candNonce (a, wstate))).take n) =
        true → typedCheck k table ((a, wstate), tstate) = true) :
    ProbComp.eval
      (prfIdealGame id id
        (prfLogDistinguisher seed logHandler adversary candNonce accept) n) true ≤
      ((ProbComp.eval (seed n)).bind fun k =>
        (PMF.uniformOfFintype (BitString n → BitString n)).bind fun table =>
          (ProbOracleComp.runWith (typedHandler k table)
            ((OracleComp.interpret
              (OracleComp.sumHandler
                (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
                adaptStep)
              (adversary n [])).run []) initTState).bind fun res =>
            PMF.pure (typedCheck k table res)) true := by
  simp only [pmf_norm, prfIdealGame, id_eq, ProbOracleComp.run, prfLogDistinguisher,
    Functor.map_map, OracleComp.interpret_bind, OracleComp.interpret_map,
    ProbOracleComp.interpret_sample, ProbOracleComp.interpret_query, ProbComp.interpret_unifFin,
    ProbComp.eval_uniform]
  pmf_hoist (ProbComp.eval (seed n))
  refine bind_apply_mono_on_support (ProbComp.eval (seed n)) true fun k _ => ?_
  refine bind_apply_mono_on_support (PMF.uniformOfFintype (BitString n → BitString n)) true
    fun table _ => ?_
  exact eval_interpret_logHandler_le_runWith_adapt
    (randomFunctionOracle n table)
    (logHandler n k)
    (typedHandler k table)
    adaptStep
    R
    (fun out => accept n k out ((randomFunctionOracle n table (candNonce out)).take n))
    (typedCheck k table)
    (hstep k table)
    (hcheck k table)
    (adversary n []) [] initTState hinit

end LogHandlerSim

end Cslib.Crypto.Protocols.CarterWegman
