/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Experiment
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.ENNRealToReal

/-!
# Symmetric private information retrieval with client preprocessing

This file models single-server symmetric private information retrieval (SPIR) with client
preprocessing in a restricted form of the model of
[Hoover, Persiano and Yeo, Section 6.1, Definition 6.1, pp. 50–51][HooverPersianoYeo2026], and
proves an original information-theoretic storage lower bound for it. That bound is **not**
Theorem 6.2 of the source: Theorem 6.2 is stated in the random oracle model and allows an
interactive online phase in which the client uses randomness. The bound here is for the plain
model, a one-round online phase and a deterministic online client. Its proof follows the counting
argument in the proof of Theorem 6.2 (p. 52). Page numbers are the printed page numbers of
arXiv:2607.06451v3 (September 2026).

The server holds an `n`-bit database `D : Fin n → Bool` and a random value `r : R` drawn once
from `rLaw` and shared between the offline setup and online query phases (with no per-client
server storage):

* **Offline phase** (`Scheme.setup`): a randomized protocol `setup D r : ProbComp (St × Toff)`
  that outputs the client's stored state `st : St` (where "`s`-bit client storage" is modeled by
  `Fintype.card St ≤ 2 ^ s`) and the public offline communication transcript `τoff : Toff`.
* **Online phase** (`Scheme.query`, `Scheme.answer`, `Scheme.reconstruct`): on a `k`-query batch
  tuple `Q : Fin k → Fin n` (ordered, repeats allowed), the client sends the upload message
  `τu = query st Q : Tu`, the server replies with the download message `τd = answer D r τu : Td`,
  and the client outputs `reconstruct st Q τd : Fin k → Bool`.

Unlike client-preprocessing PIR in `Cslib.Crypto.Protocols.PIR.Preprocessing.Scheme`, SPIR
shares server randomness `R` across the offline and online phases, takes a `k`-tuple of queries in
a single batch, and requires **data privacy** against the client in addition to query privacy
against the server [Hoover, Persiano and Yeo, Definition 6.1, pp. 50–51][HooverPersianoYeo2026]:

* `Scheme.IsCorrectWith ε` (`Scheme.IsCorrect` for `ε = 1`): for every database `D` and batch
  tuple `Q`, `Scheme.run D Q` outputs `D ∘ Q` with probability at least `ε`. As in Definition 6.1,
  `ε` is a success probability.
* `Scheme.IsPerfectlyPrivate` (`Scheme.IsPrivateWith δ`, `Scheme.privacyAdvantage`): for every
  database `D` and query tuples `Q₀, Q₁`, the server's view `(r, τoff, τu, τd)` has the same
  distribution (`Scheme.serverView`).
* `Scheme.IsPerfectlyDataPrivate` (`Scheme.IsDataPrivateWith γ`, `Scheme.dataPrivacyAdvantage`):
  for every query tuple `Q` and databases `D₀, D₁` agreeing on `Q` (`D₀ ∘ Q = D₁ ∘ Q`), the
  client's view `(st, τoff, τu, τd)` has the same distribution (`Scheme.clientView`).

The distinguishing games `Scheme.privacyGame` and `Scheme.dataPrivacyGame` are built with
`Cslib.Crypto.Game.withSetup` over `ProbComp.eval P.rLaw`.

## Modelling choices and scope

* **Restricted model.** `Scheme` is the plain model (no random oracle and no oracle-query
  bounds), with a single-round online phase in which `query`, `answer` and `reconstruct` are
  deterministic; all client randomness is sampled during `setup` and stored in `st : St`.
  Definition 6.1 lets `Query` be an interactive two-party protocol, and the proof of Theorem 6.2
  places the client's online coins in a common random string. Fixing those coins does not preserve
  privacy in general, so randomized online clients are covered only by the weaker bound
  `RandomizedScheme.correct_le_card_mul_card_div_two_pow`, which has an extra `Fintype.card Ω`
  factor and is not stated in the source.
* **Perfect, information-theoretic notions.** `Scheme.IsPerfectlyPrivate` and
  `Scheme.IsPerfectlyDataPrivate` are exact equalities of view distributions. They hold against
  every distinguisher, with no computational assumption. Definition 6.1 defines `δ`-privacy and
  `γ`-data privacy against efficient adversaries and calls a scheme perfectly private and
  perfectly data private when `δ = 0` and `γ = 0` (p. 51); we read `δ = γ = 0` as identical view
  distributions.
* **The bound.** When `2 ≤ n`, the two perfect notions make the online transcript
  `τon = (τu, τd)` independent of both `D` and `Q` (`Scheme.eval_onlineTranscript_eq`, the first
  step of the proof of Theorem 6.2). For `k ≤ n`, fixing an injective batch tuple `Q` and counting
  the at most `Fintype.card St` possible outputs of `reconstruct · Q τd` for each `τd` gives
  `ε ≤ Fintype.card St / 2 ^ k` (`Scheme.correct_le_card_div_two_pow`). With
  `Fintype.card St ≤ 2 ^ s` this gives `ε ≤ 2 ^ (s - k)` (`Scheme.correct_le_two_pow_sub`), so in
  the restricted model no scheme is `ε`-correct for `ε > 2 ^ (s - k)`. This matches the threshold
  stated in Theorem 6.2 of arXiv:2607.06451v3 (p. 52). `Scheme.batchSPIR_limitation` restates it
  with the threshold `ε > 1 - 2 ^ (s - k)` stated in the first version, arXiv:2607.06451v1
  (p. 46), which follows for `s < k` because then `2 ^ (s - k) ≤ 1 / 2 ≤ 1 - 2 ^ (s - k)`.
* **The `2 ≤ n` hypothesis** is necessary: at `n = k = 1`, `D₀ ∘ Q = D₁ ∘ Q` forces `D₀ = D₁`, so
  a zero-storage scheme (`Fintype.card St = 1 = 2 ^ 0`, `s = 0 < k = 1`) that sends `D 0` in `τd`
  is perfectly correct, perfectly private, and vacuously perfectly data private. The statement of
  Theorem 6.2, read literally (`s < k ≤ n`), also covers this case.
* **The hypotheses are jointly satisfiable.** For every `n` and `k`, the coordinate-wise toy
  scheme `parallelToyScheme` (in `Cslib.Crypto.Protocols.PIR.Symmetric.Toy`; not from the source)
  is perfectly correct, perfectly private for every batch tuple, and perfectly data private, so
  the bound is not vacuous for genuine batches `k ≥ 2`.
* **Omitted results.** Theorem 6.2 itself (random oracle model, interactive online phase, online
  client randomness), the random-oracle lower bounds of Sections 3–5, the shared-randomness
  statements Lemma 6.3 and Theorem 6.4, the PRF inner-product toy scheme of Section 6.3, and the
  generic-2PC construction of Sections 6.4–6.5 (Theorem 6.5) are not formalized here.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme`: `k`-batch SPIR with client
  preprocessing in the restricted model.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.run`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.serverView`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.clientView`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.onlineTranscript`: execution and
  party views (Definition 6.1).
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.IsCorrectWith`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.IsCorrect`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.IsPerfectlyPrivate`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.IsPerfectlyPrivateOn`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.IsPerfectlyDataPrivate`:
  correctness, privacy, and data privacy predicates.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.privacyGame`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.dataPrivacyGame`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.privacyAdvantage`,
  `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.dataPrivacyAdvantage`:
  distinguishing games and advantages.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.RandomizedScheme`: extension with online
  client randomness `Ω`.

## Main results

* `Scheme.IsPerfectlyPrivate.privacyAdvantage_eq_zero`,
  `Scheme.IsPerfectlyDataPrivate.dataPrivacyAdvantage_eq_zero`:
  perfect privacy and perfect data privacy imply zero distinguishing advantage.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.eval_onlineTranscript_eq`:
  when `2 ≤ n`, perfect privacy and perfect data privacy make the online transcript distribution
  independent of both `D` and `Q` (a step of the proof of Theorem 6.2).
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.correct_le_card_div_two_pow`:
  the original restricted-model bound `ε ≤ Fintype.card St / 2 ^ k` (not Theorem 6.2).
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.batchSPIR_limitation`:
  in the restricted model, no `k`-batch SPIR scheme with `Fintype.card St ≤ 2 ^ s`, `s < k ≤ n`
  and `2 ≤ n` is `ε`-correct for `ε > 1 - 2 ^ (s - k)`, the threshold of arXiv:2607.06451v1
  (not Theorem 6.2).
* `RandomizedScheme.correct_le_card_mul_card_div_two_pow`:
  online-randomized client bound `ε ≤ Fintype.card St * Fintype.card Ω / 2 ^ k` (not in the
  source).

## References

* [A. Hoover, G. Persiano, K. Yeo, *Lower Bounds for PIR with Preprocessing from Blackbox
  Cryptography*][HooverPersianoYeo2026], Section 6.1 (Definition 6.1, pp. 50–51) and Section 6.2
  (the proof of Theorem 6.2, p. 52). FOCS 2026; page numbers from arXiv:2607.06451v3.
-/
public section

namespace Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing

open Cslib.Probability
open scoped ENNReal NNReal

/-- A `k`-batch single-server symmetric private information retrieval (SPIR) scheme with client
preprocessing for `n`-bit databases `D : Fin n → Bool`, shared server randomness `R`, client
storage type `St`, offline transcript `Toff`, online upload message `Tu`, and online download
message `Td` [Hoover, Persiano and Yeo, Definition 6.1, p. 50][HooverPersianoYeo2026]. -/
structure Scheme (n k : ℕ) (R St Toff Tu Td : Type) where
  /-- Distribution of the shared offline/online server randomness `R`. -/
  rLaw : ProbComp R
  /-- Offline two-party setup protocol: given the database `D` and server randomness `r`,
  outputs the client's stored state `st : St` and the offline transcript `τoff : Toff`. -/
  setup : (Fin n → Bool) → R → ProbComp (St × Toff)
  /-- Online client query function: given the client state `st` and `k`-query batch tuple `Q`,
  computes the upload message `τu : Tu`. -/
  query : St → (Fin k → Fin n) → Tu
  /-- Online server answer function: given the database `D`, server randomness `r`, and upload
  message `τu`, computes the download message `τd : Td`. -/
  answer : (Fin n → Bool) → R → Tu → Td
  /-- Online client reconstruction function: given the client state `st`, query tuple `Q`, and
  download message `τd`, reconstructs the `k`-bit batch answer `Fin k → Bool`. -/
  reconstruct : St → (Fin k → Fin n) → Td → (Fin k → Bool)

namespace Scheme

variable {n k : ℕ} {R St Toff Tu Td : Type}
variable (P : Scheme n k R St Toff Tu Td)

/-! ### Execution, party views, and transcripts (Definition 6.1) -/

/-- Client output on database `D` and query tuple `Q` for fixed server randomness `r`. -/
@[expose] def runAt (D : Fin n → Bool) (Q : Fin k → Fin n) (r : R) :
    ProbComp (Fin k → Bool) := do
  let (st, _) ← P.setup D r
  let τu := P.query st Q
  let τd := P.answer D r τu
  pure (P.reconstruct st Q τd)

/-- Full execution of the `k`-batch SPIR scheme on database `D` and query tuple `Q`. -/
@[expose] def run (D : Fin n → Bool) (Q : Fin k → Fin n) : ProbComp (Fin k → Bool) := do
  let r ← P.rLaw
  P.runAt D Q r

/-- The server's view `(r, τoff, τu, τd)` on database `D` and query tuple `Q` for fixed server
randomness `r` [Hoover, Persiano and Yeo, Definition 6.1, p. 51][HooverPersianoYeo2026]. -/
@[expose] def serverViewAt (D : Fin n → Bool) (Q : Fin k → Fin n) (r : R) :
    ProbComp (R × Toff × Tu × Td) := do
  let (st, τoff) ← P.setup D r
  let τu := P.query st Q
  let τd := P.answer D r τu
  pure (r, τoff, τu, τd)

/-- The server's view `(r, τoff, τu, τd)` on database `D` and query tuple `Q`
[Hoover, Persiano and Yeo, Definition 6.1, p. 51][HooverPersianoYeo2026]. -/
@[expose] def serverView (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp (R × Toff × Tu × Td) := do
  let r ← P.rLaw
  P.serverViewAt D Q r

/-- The client's view `(st, τoff, τu, τd)` on database `D` and query tuple `Q` for fixed server
randomness `r` [Hoover, Persiano and Yeo, Definition 6.1, p. 51][HooverPersianoYeo2026]. -/
@[expose] def clientViewAt (D : Fin n → Bool) (Q : Fin k → Fin n) (r : R) :
    ProbComp (St × Toff × Tu × Td) := do
  let (st, τoff) ← P.setup D r
  let τu := P.query st Q
  let τd := P.answer D r τu
  pure (st, τoff, τu, τd)

/-- The client's view `(st, τoff, τu, τd)` on database `D` and query tuple `Q`
[Hoover, Persiano and Yeo, Definition 6.1, p. 51][HooverPersianoYeo2026]. -/
@[expose] def clientView (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp (St × Toff × Tu × Td) := do
  let r ← P.rLaw
  P.clientViewAt D Q r

/-- The online transcript `τon = (τu, τd)` on database `D` and query tuple `Q` for fixed server
randomness `r`. -/
def onlineTranscriptAt (D : Fin n → Bool) (Q : Fin k → Fin n) (r : R) :
    ProbComp (Tu × Td) := do
  let (st, _) ← P.setup D r
  let τu := P.query st Q
  let τd := P.answer D r τu
  pure (τu, τd)

/-- The online transcript `τon = (τu, τd)` on database `D` and query tuple `Q`
[Hoover, Persiano and Yeo, Definition 6.1, p. 50][HooverPersianoYeo2026]. -/
def onlineTranscript (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp (Tu × Td) := do
  let r ← P.rLaw
  P.onlineTranscriptAt D Q r

/-- The online download transcript `τd` on database `D` and query tuple `Q`. -/
def onlineDownload (D : Fin n → Bool) (Q : Fin k → Fin n) : ProbComp Td :=
  Prod.snd <$> P.onlineTranscript D Q

/-! ### Correctness, privacy, and data privacy predicates (Definition 6.1) -/

/-- `ε`-correctness [Hoover, Persiano and Yeo, Definition 6.1, p. 50][HooverPersianoYeo2026]:
for every database `D` and batch query tuple `Q`, the client outputs `D ∘ Q` with probability
at least `ε`. -/
@[expose] def IsCorrectWith (ε : ℝ) : Prop :=
  ∀ (D : Fin n → Bool) (Q : Fin k → Fin n),
    ε ≤ (ProbComp.eval (P.run D Q) (D ∘ Q)).toReal

/-- Perfect correctness (`ε = 1` in Definition 6.1): for every database `D` and query tuple `Q`,
`P.run D Q` outputs `D ∘ Q` with probability `1`. -/
@[expose] def IsCorrect : Prop :=
  ∀ (D : Fin n → Bool) (Q : Fin k → Fin n),
    ProbComp.eval (P.run D Q) = PMF.pure (D ∘ Q)

/-- Perfect query privacy against the server (`δ = 0` in
[Hoover, Persiano and Yeo, Definition 6.1, p. 51][HooverPersianoYeo2026]): for every database `D`
and every pair of batch query tuples `Q₀, Q₁`, the server's view distribution is identical. -/
@[expose] def IsPerfectlyPrivate : Prop :=
  ∀ (D : Fin n → Bool) (Q₀ Q₁ : Fin k → Fin n),
    ProbComp.eval (P.serverView D Q₀) = ProbComp.eval (P.serverView D Q₁)

/-- Perfect query privacy restricted to batch tuples in a set `S` (used for schemes such as Toy 1
that are private on injective query tuples `{Q | Function.Injective Q}`). -/
@[expose] def IsPerfectlyPrivateOn (S : Set (Fin k → Fin n)) : Prop :=
  ∀ (D : Fin n → Bool), ∀ Q₀ ∈ S, ∀ Q₁ ∈ S,
    ProbComp.eval (P.serverView D Q₀) = ProbComp.eval (P.serverView D Q₁)

/-- Perfect data privacy against the client (`γ = 0` in
[Hoover, Persiano and Yeo, Definition 6.1, p. 51][HooverPersianoYeo2026]): for every query tuple
`Q` and databases `D₀, D₁` agreeing on `Q` (`D₀ ∘ Q = D₁ ∘ Q`), the client's view distribution
is identical. -/
@[expose] def IsPerfectlyDataPrivate : Prop :=
  ∀ (D₀ D₁ : Fin n → Bool) (Q : Fin k → Fin n),
    D₀ ∘ Q = D₁ ∘ Q →
      ProbComp.eval (P.clientView D₀ Q) = ProbComp.eval (P.clientView D₁ Q)

theorem isCorrect_iff_isCorrectWith_one : P.IsCorrect ↔ P.IsCorrectWith 1 := by
  refine forall_congr' fun D => forall_congr' fun Q => ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, PMF.pure_apply_self, ENNReal.toReal_one]
  · have hsupp : (ProbComp.eval (P.run D Q)).support = {D ∘ Q} :=
      (PMF.apply_eq_one_iff _ _).mp
        (le_antisymm (PMF.coe_le_one _ _) (ENNReal.ofReal_one ▸ ENNReal.ofReal_le_of_le_toReal h))
    rw [← PMF.map_id (ProbComp.eval (P.run D Q)), Cslib.Probability.PMF.map_eq_pure_iff]
    intro y hy
    rwa [hsupp, Set.mem_singleton_iff] at hy

theorem IsCorrect.isCorrectWith_one {P : Scheme n k R St Toff Tu Td} (h : P.IsCorrect) :
    P.IsCorrectWith 1 :=
  P.isCorrect_iff_isCorrectWith_one.mp h

theorem isPerfectlyPrivate_iff_isPerfectlyPrivateOn_univ :
    P.IsPerfectlyPrivate ↔ P.IsPerfectlyPrivateOn Set.univ :=
  ⟨fun h D Q₀ _ Q₁ _ => h D Q₀ Q₁, fun h D Q₀ Q₁ => h D Q₀ trivial Q₁ trivial⟩

theorem IsPerfectlyPrivate.isPerfectlyPrivateOn {P : Scheme n k R St Toff Tu Td}
    (h : P.IsPerfectlyPrivate) (S : Set (Fin k → Fin n)) : P.IsPerfectlyPrivateOn S :=
  fun D Q₀ _ Q₁ _ => h D Q₀ Q₁

/-! ### Distinguishing experiments, games, and advantages (Definition 6.1) -/

/-- The server privacy distinguishing experiment for fixed server randomness `r : R`. -/
def privacyExperimentAt (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (R × Toff × Tu × Td) → Experiment) (r : R) : Experiment :=
  P.serverViewAt D Q r >>= adv

/-- The server privacy distinguishing experiment on database `D`, query tuple `Q`, and
distinguisher `adv`. -/
def privacyExperiment (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (R × Toff × Tu × Td) → Experiment) : Experiment :=
  P.rLaw >>= P.privacyExperimentAt D Q adv

/-- The server privacy game built with `Game.withSetup` over the server randomness law
`ProbComp.eval P.rLaw`. -/
noncomputable def privacyGame (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (R × Toff × Tu × Td) → Experiment) : Game :=
  Game.withSetup (ProbComp.eval P.rLaw) (P.privacyExperimentAt D Q adv)

theorem eval_privacyExperiment_eq_privacyGame (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (R × Toff × Tu × Td) → Experiment) :
    ProbComp.eval (P.privacyExperiment D Q adv) = P.privacyGame D Q adv :=
  Experiment.eval_bind_eq_withSetup P.rLaw (P.privacyExperimentAt D Q adv)

theorem privacyExperiment_eq_serverView_bind (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (R × Toff × Tu × Td) → Experiment) :
    P.privacyExperiment D Q adv = (P.serverView D Q >>= adv) :=
  (bind_assoc P.rLaw (P.serverViewAt D Q) adv).symm

/-- The distinguishing advantage of a server adversary `adv` between query tuples `Q₀` and `Q₁`
on database `D` [Hoover, Persiano and Yeo, Definition 6.1, p. 51][HooverPersianoYeo2026]. -/
noncomputable def privacyAdvantage (D : Fin n → Bool) (Q₀ Q₁ : Fin k → Fin n)
    (adv : (R × Toff × Tu × Td) → Experiment) : ℝ≥0 :=
  Game.advantage (P.privacyGame D Q₀ adv) (P.privacyGame D Q₁ adv)

theorem privacyAdvantage_eq_distAdvantage (D : Fin n → Bool) (Q₀ Q₁ : Fin k → Fin n)
    (adv : (R × Toff × Tu × Td) → Experiment) :
    P.privacyAdvantage D Q₀ Q₁ adv =
      distAdvantage (P.serverView D Q₀) (P.serverView D Q₁) adv := by
  simp only [privacyAdvantage, ← eval_privacyExperiment_eq_privacyGame,
    privacyExperiment_eq_serverView_bind, distAdvantage, Experiment.advantage]

/-- `δ`-privacy against every server distinguisher `adv`. -/
@[expose] def IsPrivateWith (δ : ℝ≥0) : Prop :=
  ∀ (D : Fin n → Bool) (Q₀ Q₁ : Fin k → Fin n) (adv : (R × Toff × Tu × Td) → Experiment),
    P.privacyAdvantage D Q₀ Q₁ adv ≤ δ

/-- Perfect privacy implies zero privacy distinguishing advantage for every distinguisher `adv`. -/
theorem IsPerfectlyPrivate.privacyAdvantage_eq_zero {P : Scheme n k R St Toff Tu Td}
    (h : P.IsPerfectlyPrivate) (D : Fin n → Bool) (Q₀ Q₁ : Fin k → Fin n)
    (adv : (R × Toff × Tu × Td) → Experiment) :
    P.privacyAdvantage D Q₀ Q₁ adv = 0 := by
  rw [privacyAdvantage_eq_distAdvantage]
  exact distAdvantage_eq_zero_of_eval_eq (h D Q₀ Q₁) adv

/-- Perfect privacy on `S` implies zero privacy distinguishing advantage for every `Q₀, Q₁ ∈ S`. -/
theorem IsPerfectlyPrivateOn.privacyAdvantage_eq_zero {P : Scheme n k R St Toff Tu Td}
    {S : Set (Fin k → Fin n)} (h : P.IsPerfectlyPrivateOn S) (D : Fin n → Bool)
    {Q₀ Q₁ : Fin k → Fin n} (hQ₀ : Q₀ ∈ S) (hQ₁ : Q₁ ∈ S)
    (adv : (R × Toff × Tu × Td) → Experiment) :
    P.privacyAdvantage D Q₀ Q₁ adv = 0 := by
  rw [privacyAdvantage_eq_distAdvantage]
  exact distAdvantage_eq_zero_of_eval_eq (h D Q₀ hQ₀ Q₁ hQ₁) adv

theorem IsPerfectlyPrivate.isPrivateWith_zero {P : Scheme n k R St Toff Tu Td}
    (h : P.IsPerfectlyPrivate) : P.IsPrivateWith 0 :=
  fun D Q₀ Q₁ adv => le_of_eq (h.privacyAdvantage_eq_zero D Q₀ Q₁ adv)

/-- The client data-privacy distinguishing experiment for fixed server randomness `r : R`. -/
def dataPrivacyExperimentAt (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (St × Toff × Tu × Td) → Experiment) (r : R) : Experiment :=
  P.clientViewAt D Q r >>= adv

/-- The client data-privacy distinguishing experiment on database `D`, query tuple `Q`, and
distinguisher `adv`. -/
def dataPrivacyExperiment (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (St × Toff × Tu × Td) → Experiment) : Experiment :=
  P.rLaw >>= P.dataPrivacyExperimentAt D Q adv

/-- The client data-privacy game built with `Game.withSetup` over the server randomness law
`ProbComp.eval P.rLaw`. -/
noncomputable def dataPrivacyGame (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (St × Toff × Tu × Td) → Experiment) : Game :=
  Game.withSetup (ProbComp.eval P.rLaw) (P.dataPrivacyExperimentAt D Q adv)

theorem eval_dataPrivacyExperiment_eq_dataPrivacyGame (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (St × Toff × Tu × Td) → Experiment) :
    ProbComp.eval (P.dataPrivacyExperiment D Q adv) = P.dataPrivacyGame D Q adv :=
  Experiment.eval_bind_eq_withSetup P.rLaw (P.dataPrivacyExperimentAt D Q adv)

theorem dataPrivacyExperiment_eq_clientView_bind (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (St × Toff × Tu × Td) → Experiment) :
    P.dataPrivacyExperiment D Q adv = (P.clientView D Q >>= adv) :=
  (bind_assoc P.rLaw (P.clientViewAt D Q) adv).symm

/-- The distinguishing advantage of a client adversary `adv` between databases `D₀` and `D₁`
on query tuple `Q` [Hoover, Persiano and Yeo, Definition 6.1, p. 51][HooverPersianoYeo2026]. -/
noncomputable def dataPrivacyAdvantage (D₀ D₁ : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (St × Toff × Tu × Td) → Experiment) : ℝ≥0 :=
  Game.advantage (P.dataPrivacyGame D₀ Q adv) (P.dataPrivacyGame D₁ Q adv)

theorem dataPrivacyAdvantage_eq_distAdvantage (D₀ D₁ : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (St × Toff × Tu × Td) → Experiment) :
    P.dataPrivacyAdvantage D₀ D₁ Q adv =
      distAdvantage (P.clientView D₀ Q) (P.clientView D₁ Q) adv := by
  simp only [dataPrivacyAdvantage, ← eval_dataPrivacyExperiment_eq_dataPrivacyGame,
    dataPrivacyExperiment_eq_clientView_bind, distAdvantage, Experiment.advantage]

/-- `γ`-data privacy against every client distinguisher `adv` on databases agreeing at `Q`. -/
@[expose] def IsDataPrivateWith (γ : ℝ≥0) : Prop :=
  ∀ (D₀ D₁ : Fin n → Bool) (Q : Fin k → Fin n),
    D₀ ∘ Q = D₁ ∘ Q →
      ∀ (adv : (St × Toff × Tu × Td) → Experiment),
        P.dataPrivacyAdvantage D₀ D₁ Q adv ≤ γ

/-- Perfect data privacy implies zero data-privacy distinguishing advantage for every
distinguisher `adv` whenever `D₀ ∘ Q = D₁ ∘ Q`. -/
theorem IsPerfectlyDataPrivate.dataPrivacyAdvantage_eq_zero {P : Scheme n k R St Toff Tu Td}
    (h : P.IsPerfectlyDataPrivate) {D₀ D₁ : Fin n → Bool} {Q : Fin k → Fin n}
    (hD : D₀ ∘ Q = D₁ ∘ Q) (adv : (St × Toff × Tu × Td) → Experiment) :
    P.dataPrivacyAdvantage D₀ D₁ Q adv = 0 := by
  rw [dataPrivacyAdvantage_eq_distAdvantage]
  exact distAdvantage_eq_zero_of_eval_eq (h D₀ D₁ Q hD) adv

theorem IsPerfectlyDataPrivate.isDataPrivateWith_zero {P : Scheme n k R St Toff Tu Td}
    (h : P.IsPerfectlyDataPrivate) : P.IsDataPrivateWith 0 :=
  fun _ _ _ hD adv => le_of_eq (h.dataPrivacyAdvantage_eq_zero hD adv)

/-! ### Transcript independence (Section 6.2, first paragraph of Proof of Theorem 6.2) -/

theorem onlineTranscript_eq_map_serverView (D : Fin n → Bool) (Q : Fin k → Fin n) :
    P.onlineTranscript D Q = (fun (_, _, τu, τd) => (τu, τd)) <$> P.serverView D Q := by
  simp only [onlineTranscript, onlineTranscriptAt, serverView, serverViewAt, map_bind, map_pure]

theorem onlineTranscript_eq_map_clientView (D : Fin n → Bool) (Q : Fin k → Fin n) :
    P.onlineTranscript D Q = (fun (_, _, τu, τd) => (τu, τd)) <$> P.clientView D Q := by
  simp only [onlineTranscript, onlineTranscriptAt, clientView, clientViewAt, map_bind, map_pure]

theorem eval_onlineTranscript_eq_map_serverView (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp.eval (P.onlineTranscript D Q) =
      (ProbComp.eval (P.serverView D Q)).map (fun (_, _, τu, τd) => (τu, τd)) := by
  rw [P.onlineTranscript_eq_map_serverView D Q, ProbComp.eval_map]

theorem eval_onlineTranscript_eq_map_clientView (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp.eval (P.onlineTranscript D Q) =
      (ProbComp.eval (P.clientView D Q)).map (fun (_, _, τu, τd) => (τu, τd)) := by
  rw [P.onlineTranscript_eq_map_clientView D Q, ProbComp.eval_map]

/-- Perfect privacy makes the online transcript distribution independent of the query tuple `Q`. -/
theorem IsPerfectlyPrivate.eval_onlineTranscript_eq {P : Scheme n k R St Toff Tu Td}
    (hpriv : P.IsPerfectlyPrivate) (D : Fin n → Bool) (Q₀ Q₁ : Fin k → Fin n) :
    ProbComp.eval (P.onlineTranscript D Q₀) = ProbComp.eval (P.onlineTranscript D Q₁) := by
  rw [P.eval_onlineTranscript_eq_map_serverView D Q₀,
    P.eval_onlineTranscript_eq_map_serverView D Q₁, hpriv D Q₀ Q₁]

/-- Perfect data privacy makes the online transcript distribution invariant under changing the
database outside `Q`. -/
theorem IsPerfectlyDataPrivate.eval_onlineTranscript_eq {P : Scheme n k R St Toff Tu Td}
    (hdpriv : P.IsPerfectlyDataPrivate) {D₀ D₁ : Fin n → Bool} {Q : Fin k → Fin n}
    (hD : D₀ ∘ Q = D₁ ∘ Q) :
    ProbComp.eval (P.onlineTranscript D₀ Q) = ProbComp.eval (P.onlineTranscript D₁ Q) := by
  rw [P.eval_onlineTranscript_eq_map_clientView D₀ Q,
    P.eval_onlineTranscript_eq_map_clientView D₁ Q, hdpriv D₀ D₁ Q hD]

/-- Direct transcript-independence chain from query invariance and invariance under changing the
database outside the queried indices. For `j₀ ≠ j₁` and `Dm = Function.update D₁ j₀ (D₀ j₀)`, it
goes `(D₀, Q₀) → (D₀, const j₀) → (Dm, const j₀) → (Dm, const j₁) → (D₁, const j₁) → (D₁, Q₁)`. -/
private theorem eval_onlineTranscript_eq_of_marginal {P : Scheme n k R St Toff Tu Td}
    (hn : 2 ≤ n)
    (hpriv_on : ∀ D Q₀ Q₁,
      ProbComp.eval (P.onlineTranscript D Q₀) = ProbComp.eval (P.onlineTranscript D Q₁))
    (hdpriv_on : ∀ {D₀ D₁ : Fin n → Bool} {Q : Fin k → Fin n}, D₀ ∘ Q = D₁ ∘ Q →
      ProbComp.eval (P.onlineTranscript D₀ Q) = ProbComp.eval (P.onlineTranscript D₁ Q))
    (D₀ D₁ : Fin n → Bool) (Q₀ Q₁ : Fin k → Fin n) :
    ProbComp.eval (P.onlineTranscript D₀ Q₀) = ProbComp.eval (P.onlineTranscript D₁ Q₁) := by
  have := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j₀, j₁, hj⟩ := exists_pair_ne (Fin n)
  exact (hpriv_on _ _ (fun _ => j₀)).trans <|
    (hdpriv_on (D₁ := Function.update D₁ j₀ (D₀ j₀)) (by funext; simp)).trans <|
      (hpriv_on _ _ (fun _ => j₁)).trans <|
        (hdpriv_on (by funext; simp [hj.symm])).trans (hpriv_on _ _ _)

/-- **Online transcript independence** (the first step of the proof of
[Hoover, Persiano and Yeo, Theorem 6.2, p. 52][HooverPersianoYeo2026]): when `2 ≤ n`, perfect
privacy and perfect data privacy imply that the online transcript `τon = (τu, τd)` has the same
distribution for all databases `D₀, D₁` and all batch query tuples `Q₀, Q₁`. -/
theorem eval_onlineTranscript_eq {P : Scheme n k R St Toff Tu Td} (hn : 2 ≤ n)
    (hpriv : P.IsPerfectlyPrivate) (hdpriv : P.IsPerfectlyDataPrivate)
    (D₀ D₁ : Fin n → Bool) (Q₀ Q₁ : Fin k → Fin n) :
    ProbComp.eval (P.onlineTranscript D₀ Q₀) = ProbComp.eval (P.onlineTranscript D₁ Q₁) :=
  eval_onlineTranscript_eq_of_marginal hn hpriv.eval_onlineTranscript_eq
    hdpriv.eval_onlineTranscript_eq D₀ D₁ Q₀ Q₁

/-- Updating a single database entry `i` preserves the online transcript distribution when
`2 ≤ n`. -/
theorem eval_onlineTranscript_update_eq {P : Scheme n k R St Toff Tu Td} (hn : 2 ≤ n)
    (hpriv : P.IsPerfectlyPrivate) (hdpriv : P.IsPerfectlyDataPrivate)
    (D : Fin n → Bool) (i : Fin n) (b : Bool) (Q : Fin k → Fin n) :
    ProbComp.eval (P.onlineTranscript (Function.update D i b) Q) =
      ProbComp.eval (P.onlineTranscript D Q) :=
  eval_onlineTranscript_eq hn hpriv hdpriv _ _ Q Q

/-- Under `2 ≤ n`, perfect privacy, and perfect data privacy, the download transcript `τd` has the
same distribution for all databases and query tuples. -/
theorem eval_onlineDownload_eq {P : Scheme n k R St Toff Tu Td} (hn : 2 ≤ n)
    (hpriv : P.IsPerfectlyPrivate) (hdpriv : P.IsPerfectlyDataPrivate)
    (D₀ D₁ : Fin n → Bool) (Q₀ Q₁ : Fin k → Fin n) :
    ProbComp.eval (P.onlineDownload D₀ Q₀) = ProbComp.eval (P.onlineDownload D₁ Q₁) := by
  simp only [onlineDownload, ProbComp.eval_map,
    eval_onlineTranscript_eq hn hpriv hdpriv D₀ D₁ Q₀ Q₁]

/-! ### Restricted-model batch bound (after the counting argument in the proof of Theorem 6.2) -/

/-- Auxiliary joint draw of the client state `st` and online download `τd`. -/
private def stateAndDownload (D : Fin n → Bool) (Q : Fin k → Fin n) : ProbComp (St × Td) := do
  let r ← P.rLaw
  let (st, _) ← P.setup D r
  let τu := P.query st Q
  let τd := P.answer D r τu
  pure (st, τd)

private theorem run_eq_map_stateAndDownload (D : Fin n → Bool) (Q : Fin k → Fin n) :
    P.run D Q = (fun (st, τd) => P.reconstruct st Q τd) <$> P.stateAndDownload D Q := by
  simp only [run, runAt, stateAndDownload, map_bind, map_pure]

private theorem onlineDownload_eq_map_stateAndDownload (D : Fin n → Bool) (Q : Fin k → Fin n) :
    P.onlineDownload D Q = Prod.snd <$> P.stateAndDownload D Q := by
  simp only [onlineDownload, onlineTranscript, onlineTranscriptAt, stateAndDownload,
    map_bind, map_pure]

private theorem eval_run_eq_map_stateAndDownload (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp.eval (P.run D Q) =
      (ProbComp.eval (P.stateAndDownload D Q)).map (fun (st, τd) => P.reconstruct st Q τd) := by
  rw [P.run_eq_map_stateAndDownload D Q, ProbComp.eval_map]

private theorem eval_onlineDownload_eq_map_stateAndDownload
    (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp.eval (P.onlineDownload D Q) =
      (ProbComp.eval (P.stateAndDownload D Q)).map Prod.snd := by
  rw [P.onlineDownload_eq_map_stateAndDownload D Q, ProbComp.eval_map]

/-- The finite set of all `k`-bit strings that `reconstruct` can produce on query tuple `Q` and
download message `τd` as `st` ranges over `St`. -/
private def candidateOutputs [Fintype St] (Q : Fin k → Fin n) (τd : Td) :
    Finset (Fin k → Bool) :=
  Finset.univ.image (fun st : St => P.reconstruct st Q τd)

private theorem card_candidateOutputs_le [Fintype St] (Q : Fin k → Fin n) (τd : Td) :
    (P.candidateOutputs Q τd).card ≤ Fintype.card St := by
  simpa only [candidateOutputs, Finset.card_univ] using
    Finset.card_image_le (s := (Finset.univ : Finset St))
      (f := fun st : St => P.reconstruct st Q τd)

private theorem eval_run_le_onlineDownload_candidateOutputs [Fintype St]
    (D : Fin n → Bool) (Q : Fin k → Fin n) (y : Fin k → Bool) :
    ProbComp.eval (P.run D Q) y ≤
      (ProbComp.eval (P.onlineDownload D Q)).map
        (fun τd => decide (y ∈ P.candidateOutputs Q τd)) true := by
  rw [P.eval_run_eq_map_stateAndDownload D Q,
    P.eval_onlineDownload_eq_map_stateAndDownload D Q, PMF.map_comp,
    PMF.map_apply, PMF.map_apply]
  refine tsum_le_tsum fun ⟨st, τd⟩ => ?_
  split_ifs with hy hmem
  · exact le_rfl
  · exact absurd (by simpa only [Function.comp_apply, true_eq_decide_iff, candidateOutputs, hy]
      using Finset.mem_image_of_mem (fun st => P.reconstruct st Q τd) (Finset.mem_univ st)) hmem
  · exact zero_le
  · exact zero_le

/-- Extend a `k`-bit string `y : Fin k → Bool` to an `n`-bit database, padding coordinates
`i ≥ k` with `false`. -/
private def padDB (y : Fin k → Bool) : Fin n → Bool :=
  fun i => if hi : i.val < k then y ⟨i.val, hi⟩ else false

private theorem padDB_comp_castLE (hkn : k ≤ n) (y : Fin k → Bool) :
    padDB (n := n) y ∘ Fin.castLE hkn = y := by
  funext j
  simp [padDB, Fin.castLE]

/-- Core counting bound from database-independence of the online download distribution at the
canonical injective query tuple `Fin.castLE hkn`. -/
private theorem correct_le_card_div_two_pow_of_onlineDownload_eq [Fintype St] {ε : ℝ}
    (hkn : k ≤ n)
    (hdl : ∀ D₁ D₂ : Fin n → Bool,
      ProbComp.eval (P.onlineDownload D₁ (Fin.castLE hkn)) =
        ProbComp.eval (P.onlineDownload D₂ (Fin.castLE hkn)))
    (hcorr : P.IsCorrectWith ε) :
    ε ≤ (Fintype.card St : ℝ) / 2 ^ k := by
  let Q : Fin k → Fin n := Fin.castLE hkn
  let D₀ : Fin n → Bool := fun _ => false
  let τLaw : PMF Td := ProbComp.eval (P.onlineDownload D₀ Q)
  have hsum_ennreal :
      (∑ y : Fin k → Bool, ProbComp.eval (P.run (padDB y) Q) y) ≤ (Fintype.card St : ℝ≥0∞) := by
    calc (∑ y : Fin k → Bool, ProbComp.eval (P.run (padDB y) Q) y)
        ≤ ∑ y : Fin k → Bool, τLaw.map (fun τd => decide (y ∈ P.candidateOutputs Q τd)) true :=
          Finset.sum_le_sum fun y _ => by
            simpa only [τLaw, Q, hdl (padDB y) D₀] using
              P.eval_run_le_onlineDownload_candidateOutputs (padDB y) Q y
      _ = ∑' τd : Td, ∑ y : Fin k → Bool,
            if true = decide (y ∈ P.candidateOutputs Q τd) then τLaw τd else 0 := by
          simp only [PMF.map_apply]
          rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
          exact tsum_congr fun _ => Finset.sum_congr rfl fun _ _ => by congr
      _ ≤ ∑' τd : Td, (Fintype.card St : ℝ≥0∞) * τLaw τd :=
          tsum_le_tsum fun τd => by
            simp only [true_eq_decide_iff, ← Finset.sum_filter, Finset.filter_univ_mem,
              Finset.sum_const, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr (P.card_candidateOutputs_le Q τd)) zero_le
      _ = (Fintype.card St : ℝ≥0∞) := by rw [ENNReal.tsum_mul_left, τLaw.tsum_coe, mul_one]
  have hsum_real :
      (∑ y : Fin k → Bool, (ProbComp.eval (P.run (padDB y) Q) y).toReal) ≤
        (Fintype.card St : ℝ) := by ennreal_to_real using hsum_ennreal
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k), mul_comm]
  calc (2 : ℝ) ^ k * ε = ∑ _y : Fin k → Bool, ε := by simp [Finset.sum_const, Fintype.card_bool]
    _ ≤ ∑ y : Fin k → Bool, (ProbComp.eval (P.run (padDB y) Q) y).toReal :=
        Finset.sum_le_sum fun y _ => by
          simpa only [Q, padDB_comp_castLE hkn y] using hcorr (padDB y) Q
    _ ≤ (Fintype.card St : ℝ) := hsum_real

/-- **Restricted-model batch storage bound.** This is not Theorem 6.2 of
[Hoover, Persiano and Yeo][HooverPersianoYeo2026], which is stated in the random oracle model and
allows an interactive online phase with online client randomness. It is an original
information-theoretic bound for the plain model with a one-round online phase and a deterministic
online client, proved by the counting argument in the proof of Theorem 6.2 (p. 52): if `2 ≤ n`,
`k ≤ n`, and `P` is `ε`-correct, perfectly private, and perfectly data private with finite client
state `St`, then `ε ≤ Fintype.card St / 2 ^ k`. -/
theorem correct_le_card_div_two_pow [Fintype St] {ε : ℝ} (hn : 2 ≤ n) (hkn : k ≤ n)
    (hpriv : P.IsPerfectlyPrivate) (hdpriv : P.IsPerfectlyDataPrivate)
    (hcorr : P.IsCorrectWith ε) :
    ε ≤ (Fintype.card St : ℝ) / 2 ^ k :=
  P.correct_le_card_div_two_pow_of_onlineDownload_eq hkn
    (fun D₁ D₂ => P.eval_onlineDownload_eq hn hpriv hdpriv D₁ D₂ _ _) hcorr

/-- In the restricted model of `correct_le_card_div_two_pow` (not Theorem 6.2), with `s`-bit
client storage (`Fintype.card St ≤ 2 ^ s`), `ε ≤ 2 ^ (s - k)`. So no scheme in this model is
`ε`-correct for `ε > 2 ^ (s - k)`, which matches the threshold stated in Theorem 6.2 of
[Hoover, Persiano and Yeo, p. 52][HooverPersianoYeo2026] (arXiv:2607.06451v3). -/
theorem correct_le_two_pow_sub [Fintype St] {s : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hkn : k ≤ n)
    (hst : Fintype.card St ≤ 2 ^ s) (hpriv : P.IsPerfectlyPrivate)
    (hdpriv : P.IsPerfectlyDataPrivate) (hcorr : P.IsCorrectWith ε) :
    ε ≤ (2 : ℝ) ^ ((s : ℤ) - (k : ℤ)) := by
  have hcore := P.correct_le_card_div_two_pow hn hkn hpriv hdpriv hcorr
  have hcard : (Fintype.card St : ℝ) ≤ (2 : ℝ) ^ s := by exact_mod_cast hst
  have hpow : (2 : ℝ) ^ s / (2 : ℝ) ^ k = (2 : ℝ) ^ ((s : ℤ) - (k : ℤ)) := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
  linarith [div_le_div_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)]

/-- In the restricted model of `correct_le_card_div_two_pow` (not Theorem 6.2), a perfectly
correct, perfectly private, and perfectly data-private `k`-batch SPIR scheme with `2 ≤ n` and
`k ≤ n` requires client state size at least `2 ^ k`. -/
theorem two_pow_le_card_state [Fintype St] (hn : 2 ≤ n) (hkn : k ≤ n)
    (hpriv : P.IsPerfectlyPrivate) (hdpriv : P.IsPerfectlyDataPrivate) (hcorr : P.IsCorrect) :
    2 ^ k ≤ Fintype.card St := by
  have hle := P.correct_le_card_div_two_pow hn hkn hpriv hdpriv hcorr.isCorrectWith_one
  rwa [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k), one_mul, ← Nat.cast_ofNat, ← Nat.cast_pow,
    Nat.cast_le] at hle

/-- **Restricted-model batch limitation.** This is not Theorem 6.2 of
[Hoover, Persiano and Yeo][HooverPersianoYeo2026], which is stated in the random oracle model and
allows an interactive online phase with online client randomness. In the restricted model of
`correct_le_card_div_two_pow` (plain model, one online round, deterministic online client), when
`2 ≤ n`, `s < k ≤ n`, `Fintype.card St ≤ 2 ^ s`, and `ε > 1 - 2 ^ (s - k)`, no `k`-batch SPIR
scheme can be simultaneously `ε`-correct, perfectly private, and perfectly data private. Here
`ε` is a success probability as in Definition 6.1, and `1 - 2 ^ (s - k)` is the threshold stated
in the first version, arXiv:2607.06451v1 (p. 46). The pinned version, arXiv:2607.06451v3,
states `ε > 2 ^ (s - k)` (p. 52); that form is `correct_le_two_pow_sub`. -/
theorem batchSPIR_limitation [Fintype St] {s : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hsk : s < k)
    (hkn : k ≤ n) (hst : Fintype.card St ≤ 2 ^ s)
    (hε : 1 - (2 : ℝ) ^ ((s : ℤ) - (k : ℤ)) < ε) (hpriv : P.IsPerfectlyPrivate)
    (hdpriv : P.IsPerfectlyDataPrivate) : ¬ P.IsCorrectWith ε := by
  intro hcorr
  have hle := P.correct_le_two_pow_sub hn hkn hst hpriv hdpriv hcorr
  have hpow : (2 : ℝ) ^ ((s : ℤ) - (k : ℤ)) ≤ 1 / 2 :=
    (zpow_le_zpow_right₀ (by norm_num) (by omega : (s : ℤ) - k ≤ -1)).trans_eq (by norm_num)
  linarith

end Scheme

/-- Existential form of `Scheme.batchSPIR_limitation`. This is not Theorem 6.2 of
[Hoover, Persiano and Yeo][HooverPersianoYeo2026] (random oracle model, online client
randomness): in the restricted model of `Scheme` (plain model, one online round, deterministic
online client), for `2 ≤ n`, `s < k ≤ n`, and `ε > 1 - 2 ^ (s - k)`, there does not exist a
`k`-batch SPIR scheme with `Fintype.card St ≤ 2 ^ s` that is `ε`-correct, perfectly private, and
perfectly data private. -/
theorem not_exists_scheme_of_lt {n k s : ℕ} {R St Toff Tu Td : Type} [Fintype St] {ε : ℝ}
    (hn : 2 ≤ n) (hsk : s < k) (hkn : k ≤ n) (hst : Fintype.card St ≤ 2 ^ s)
    (hε : 1 - (2 : ℝ) ^ ((s : ℤ) - (k : ℤ)) < ε) :
    ¬ ∃ P : Scheme n k R St Toff Tu Td,
      P.IsCorrectWith ε ∧ P.IsPerfectlyPrivate ∧ P.IsPerfectlyDataPrivate := by
  rintro ⟨P, hcorr, hpriv, hdpriv⟩
  exact P.batchSPIR_limitation hn hsk hkn hst hε hpriv hdpriv hcorr

/-! ### Online-randomized client extension (`RandomizedScheme`) -/

/-- Extension of `Scheme` in which the client also draws fresh online randomness `ω : Ω` from
`ωLaw` during the `Query` phase. As in Definition 6.1, `ω` is ephemeral to the online query and
is not part of the client's preprocessing state `st : St` in `clientView`.

In the plain model without placing online client coins in a shared common random string,
conditioning on fixed online coins need not preserve privacy; instead, counting over
`(st, ω) : St × Ω` gives the explicit bound `ε ≤ Fintype.card St * Fintype.card Ω / 2 ^ k`
(`RandomizedScheme.correct_le_card_mul_card_div_two_pow`). -/
structure RandomizedScheme (n k : ℕ) (R St Ω Toff Tu Td : Type) where
  /-- Distribution of the shared offline/online server randomness `R`. -/
  rLaw : ProbComp R
  /-- Distribution of the client's ephemeral online query randomness `Ω`. -/
  ωLaw : ProbComp Ω
  /-- Offline setup protocol. -/
  setup : (Fin n → Bool) → R → ProbComp (St × Toff)
  /-- Online client query function using stored state `st` and online coins `ω`. -/
  query : St → Ω → (Fin k → Fin n) → Tu
  /-- Online server answer function. -/
  answer : (Fin n → Bool) → R → Tu → Td
  /-- Online client reconstruction function using stored state `st` and online coins `ω`. -/
  reconstruct : St → Ω → (Fin k → Fin n) → Td → (Fin k → Bool)

namespace RandomizedScheme

variable {n k : ℕ} {R St Ω Toff Tu Td : Type}
variable (P : RandomizedScheme n k R St Ω Toff Tu Td)

/-- Full execution of `P` on database `D` and batch query tuple `Q`. -/
@[expose] def run (D : Fin n → Bool) (Q : Fin k → Fin n) : ProbComp (Fin k → Bool) := do
  let r ← P.rLaw
  let (st, _) ← P.setup D r
  let ω ← P.ωLaw
  let τu := P.query st ω Q
  let τd := P.answer D r τu
  pure (P.reconstruct st ω Q τd)

/-- Server view `(r, τoff, τu, τd)` on database `D` and query tuple `Q`. -/
def serverView (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp (R × Toff × Tu × Td) := do
  let r ← P.rLaw
  let (st, τoff) ← P.setup D r
  let ω ← P.ωLaw
  let τu := P.query st ω Q
  let τd := P.answer D r τu
  pure (r, τoff, τu, τd)

/-- Client view `(st, τoff, τu, τd)` on database `D` and query tuple `Q` (without ephemeral
online coins `ω`, matching Definition 6.1). -/
def clientView (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp (St × Toff × Tu × Td) := do
  let r ← P.rLaw
  let (st, τoff) ← P.setup D r
  let ω ← P.ωLaw
  let τu := P.query st ω Q
  let τd := P.answer D r τu
  pure (st, τoff, τu, τd)

/-- Online transcript `τon = (τu, τd)` on database `D` and query tuple `Q`. -/
def onlineTranscript (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp (Tu × Td) := do
  let r ← P.rLaw
  let (st, _) ← P.setup D r
  let ω ← P.ωLaw
  let τu := P.query st ω Q
  let τd := P.answer D r τu
  pure (τu, τd)

/-- `ε`-correctness for a randomized-online-client scheme. -/
@[expose] def IsCorrectWith (ε : ℝ) : Prop :=
  ∀ (D : Fin n → Bool) (Q : Fin k → Fin n),
    ε ≤ (ProbComp.eval (P.run D Q) (D ∘ Q)).toReal

/-- Perfect server privacy for a randomized-online-client scheme. -/
@[expose] def IsPerfectlyPrivate : Prop :=
  ∀ (D : Fin n → Bool) (Q₀ Q₁ : Fin k → Fin n),
    ProbComp.eval (P.serverView D Q₀) = ProbComp.eval (P.serverView D Q₁)

/-- Perfect client data privacy for a randomized-online-client scheme. -/
@[expose] def IsPerfectlyDataPrivate : Prop :=
  ∀ (D₀ D₁ : Fin n → Bool) (Q : Fin k → Fin n),
    D₀ ∘ Q = D₁ ∘ Q →
      ProbComp.eval (P.clientView D₀ Q) = ProbComp.eval (P.clientView D₁ Q)

/-- Fold `ωLaw` into the setup state `(st, ω) : St × Ω` to reuse the deterministic-client
transcript-independence and counting argument on the online transcript marginal. -/
private def toProductScheme : Scheme n k R (St × Ω) Toff Tu Td where
  rLaw := P.rLaw
  setup D r := do
    let (st, τoff) ← P.setup D r
    let ω ← P.ωLaw
    pure ((st, ω), τoff)
  query := fun (st, ω) Q => P.query st ω Q
  answer := P.answer
  reconstruct := fun (st, ω) Q τd => P.reconstruct st ω Q τd

private theorem run_toProductScheme (D : Fin n → Bool) (Q : Fin k → Fin n) :
    P.toProductScheme.run D Q = P.run D Q := by
  simp only [toProductScheme, Scheme.run, Scheme.runAt, run, bind_assoc, pure_bind]

private theorem serverView_toProductScheme (D : Fin n → Bool) (Q : Fin k → Fin n) :
    P.toProductScheme.serverView D Q = P.serverView D Q := by
  simp only [toProductScheme, Scheme.serverView, Scheme.serverViewAt, serverView,
    bind_assoc, pure_bind]

private theorem onlineTranscript_toProductScheme (D : Fin n → Bool) (Q : Fin k → Fin n) :
    P.toProductScheme.onlineTranscript D Q =
      (fun (_, _, τu, τd) => (τu, τd)) <$> P.clientView D Q := by
  simp only [toProductScheme, Scheme.onlineTranscript, Scheme.onlineTranscriptAt, clientView,
    bind_assoc, pure_bind, map_bind, map_pure]

/-- **Online-randomized client batch bound** (an original extension, not stated in the source,
and not Theorem 6.2): if `2 ≤ n`, `k ≤ n`, and `P` is
`ε`-correct, perfectly private, and perfectly data private with finite client state `St` and
finite online coin space `Ω`, then `ε ≤ Fintype.card St * Fintype.card Ω / 2 ^ k`. -/
theorem correct_le_card_mul_card_div_two_pow [Fintype St] [Fintype Ω] {ε : ℝ}
    (hn : 2 ≤ n) (hkn : k ≤ n) (hpriv : P.IsPerfectlyPrivate)
    (hdpriv : P.IsPerfectlyDataPrivate) (hcorr : P.IsCorrectWith ε) :
    ε ≤ (Fintype.card St * Fintype.card Ω : ℝ) / 2 ^ k := by
  have hpriv_prod : P.toProductScheme.IsPerfectlyPrivate := fun D Q₀ Q₁ => by
    simp only [serverView_toProductScheme, hpriv D Q₀ Q₁]
  have hdpriv_on : ∀ {D₀ D₁ : Fin n → Bool} {Q : Fin k → Fin n}, D₀ ∘ Q = D₁ ∘ Q →
      ProbComp.eval (P.toProductScheme.onlineTranscript D₀ Q) =
        ProbComp.eval (P.toProductScheme.onlineTranscript D₁ Q) := fun hD => by
    simp only [onlineTranscript_toProductScheme, ProbComp.eval_map, hdpriv _ _ _ hD]
  have hle := P.toProductScheme.correct_le_card_div_two_pow_of_onlineDownload_eq hkn
    (fun D₁ D₂ => by simp only [Scheme.onlineDownload, ProbComp.eval_map,
      Scheme.eval_onlineTranscript_eq_of_marginal hn hpriv_prod.eval_onlineTranscript_eq
        hdpriv_on D₁ D₂ (Fin.castLE hkn) (Fin.castLE hkn)])
    fun D Q => P.run_toProductScheme D Q ▸ hcorr D Q
  rwa [Fintype.card_prod, Nat.cast_mul] at hle

end RandomizedScheme

end Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing
