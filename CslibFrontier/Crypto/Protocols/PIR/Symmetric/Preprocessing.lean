/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Experiment
public import CslibFrontier.Crypto.Protocols.PIR.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Support
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Symmetric private information retrieval with client preprocessing

In the single-server symmetric private information retrieval (SPIR) with client preprocessing
model of [Hoover, Persiano and Yeo, Section 6.1, Definition 6.1][HooverPersianoYeo2026],
the server holds an `n`-bit database `D : Fin n → Bool` and a random value `r : R` drawn once
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
against the server [Hoover, Persiano and Yeo, Definition 6.1, pp. 44–45][HooverPersianoYeo2026]:

* `Scheme.IsCorrectWith ε` (`Scheme.IsCorrect` for `ε = 1`): for every database `D` and batch
  tuple `Q`, `Scheme.run D Q` outputs `D ∘ Q` with probability at least `ε`.
* `Scheme.IsPerfectlyPrivate` (`Scheme.IsPrivateWith δ`, `Scheme.privacyAdvantage`): for every
  database `D` and query tuples `Q₀, Q₁`, the server's view `(r, τoff, τu, τd)` has the same
  distribution (`Scheme.serverView`).
* `Scheme.IsPerfectlyDataPrivate` (`Scheme.IsDataPrivateWith γ`, `Scheme.dataPrivacyAdvantage`):
  for every query tuple `Q` and databases `D₀, D₁` agreeing on `Q` (`D₀ ∘ Q = D₁ ∘ Q`), the
  client's view `(st, τoff, τu, τd)` has the same distribution (`Scheme.clientView`).

The distinguishing games `Scheme.privacyGame` and `Scheme.dataPrivacyGame` are built with
`Cslib.Crypto.Game.withSetup` over `ProbComp.eval P.rLaw`.

## Modelling choices and scope

* **Plain model, one-round online phase, deterministic online client.** `Scheme` models the plain
  model (without a random oracle or oracle-query bounds) and a single-round online phase in which
  `query`, `answer`, and `reconstruct` are deterministic and all client randomness is sampled
  during `setup` and stored in `st : St`. (In the source's proof of Theorem 6.2, client online
  coins are placed in a common random string; conditioning on fixed client coins does not preserve
  privacy in general. `RandomizedScheme` extends the syntax with online client coins `ω : Ω` not
  included in the client view and proves the corresponding bound with an explicit `Fintype.card Ω`
  factor, `RandomizedScheme.correct_le_card_mul_card_div_two_pow`.)
* **Core batch lower bound and the `2 ≤ n` hypothesis.** When `2 ≤ n`, perfect privacy and perfect
  data privacy make the online transcript `τon = (τu, τd)` independent of both `D` and `Q`
  (`Scheme.eval_onlineTranscript_eq`). For `k ≤ n`, fixing an injective batch tuple `Q` and
  counting the at most `Fintype.card St` possible outputs of `reconstruct · Q τd` for each `τd`
  yields the core bound `ε ≤ Fintype.card St / 2 ^ k` (`Scheme.correct_le_card_div_two_pow`).
  When `Fintype.card St ≤ 2 ^ s` and `s < k ≤ n`, this gives `ε ≤ 2 ^ (s - k) ≤ 1 / 2 ≤
  1 - 2 ^ (s - k)`, which is strictly stronger than the paper's threshold `ε ≤ 1 - 2 ^ (s - k)`
  and implies the paper-form impossibility `Scheme.batchSPIR_limitation` (the plain-model,
  one-round, deterministic-online-client version of
  [Hoover, Persiano and Yeo, Theorem 6.2, p. 46][HooverPersianoYeo2026]). The hypothesis `2 ≤ n`
  is necessary: at `n = k = 1`, `D₀ ∘ Q = D₁ ∘ Q` forces `D₀ = D₁`, so a zero-storage scheme
  (`Fintype.card St = 1 = 2 ^ 0`, `s = 0 < k = 1`) that sends `D 0` in `τd` is perfectly correct,
  perfectly private, and vacuously perfectly data private.
* **The hypotheses are jointly satisfiable.** For every `n` and `k`, the coordinate-wise toy scheme
  `parallelToyScheme` (in `Cslib.Crypto.Protocols.PIR.Symmetric.Toy`; not from the source) is
  perfectly correct, perfectly private for every batch tuple, and perfectly data private, so the
  core bound is not vacuous for genuine batches `k ≥ 2`. All three notions are perfect
  (information-theoretic): they quantify over every distinguisher without any computational
  assumption, matching `δ = γ = 0` in Definition 6.1.
* **Omitted results.** Random-oracle / relativized lower bounds (Sections 3–5 and the ROM
  phrasing of Theorem 6.2), the informal shared-randomness correlation statements (Lemma 6.3 and
  Theorem 6.4), the PRF inner-product toy scheme (Section 6.3, Toy 2), and the generic-2PC +
  invertible-PRF construction (Sections 6.4–6.5, Theorem 6.5) are not formalized here.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme`: `k`-batch SPIR with client
  preprocessing.
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
  independent of both `D` and `Q`.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.correct_le_card_div_two_pow`:
  core batch lower bound `ε ≤ Fintype.card St / 2 ^ k`.
* `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing.Scheme.batchSPIR_limitation`:
  impossibility of `k`-batch SPIR with `Fintype.card St ≤ 2 ^ s`, `s < k ≤ n`, `2 ≤ n`, and
  `ε > 1 - 2 ^ (s - k)` (Theorem 6.2 in the plain, one-round, deterministic-online-client model).
* `RandomizedScheme.correct_le_card_mul_card_div_two_pow`:
  online-randomized client bound `ε ≤ Fintype.card St * Fintype.card Ω / 2 ^ k`.

## References

* [A. Hoover, G. Persiano, K. Yeo, *Lower Bounds for PIR with Preprocessing from Blackbox
  Cryptography*][HooverPersianoYeo2026], Section 6.1 (Definition 6.1, pp. 44–45) and Section 6.2
  (Theorem 6.2, p. 46)
-/

public section

namespace Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing

open Cslib.Probability
open scoped ENNReal NNReal

/-- A `k`-batch single-server symmetric private information retrieval (SPIR) scheme with client
preprocessing for `n`-bit databases `D : Fin n → Bool`, shared server randomness `R`, client
storage type `St`, offline transcript `Toff`, online upload message `Tu`, and online download
message `Td` [Hoover, Persiano and Yeo, Definition 6.1, p. 44][HooverPersianoYeo2026]. -/
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
randomness `r` [Hoover, Persiano and Yeo, Definition 6.1, p. 45][HooverPersianoYeo2026]. -/
@[expose] def serverViewAt (D : Fin n → Bool) (Q : Fin k → Fin n) (r : R) :
    ProbComp (R × Toff × Tu × Td) := do
  let (st, τoff) ← P.setup D r
  let τu := P.query st Q
  let τd := P.answer D r τu
  pure (r, τoff, τu, τd)

/-- The server's view `(r, τoff, τu, τd)` on database `D` and query tuple `Q`
[Hoover, Persiano and Yeo, Definition 6.1, p. 45][HooverPersianoYeo2026]. -/
@[expose] def serverView (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp (R × Toff × Tu × Td) := do
  let r ← P.rLaw
  P.serverViewAt D Q r

/-- The client's view `(st, τoff, τu, τd)` on database `D` and query tuple `Q` for fixed server
randomness `r` [Hoover, Persiano and Yeo, Definition 6.1, p. 45][HooverPersianoYeo2026]. -/
@[expose] def clientViewAt (D : Fin n → Bool) (Q : Fin k → Fin n) (r : R) :
    ProbComp (St × Toff × Tu × Td) := do
  let (st, τoff) ← P.setup D r
  let τu := P.query st Q
  let τd := P.answer D r τu
  pure (st, τoff, τu, τd)

/-- The client's view `(st, τoff, τu, τd)` on database `D` and query tuple `Q`
[Hoover, Persiano and Yeo, Definition 6.1, p. 45][HooverPersianoYeo2026]. -/
@[expose] def clientView (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp (St × Toff × Tu × Td) := do
  let r ← P.rLaw
  P.clientViewAt D Q r

/-- The online transcript `τon = (τu, τd)` on database `D` and query tuple `Q` for fixed server
randomness `r`. -/
@[expose] def onlineTranscriptAt (D : Fin n → Bool) (Q : Fin k → Fin n) (r : R) :
    ProbComp (Tu × Td) := do
  let (st, _) ← P.setup D r
  let τu := P.query st Q
  let τd := P.answer D r τu
  pure (τu, τd)

/-- The online transcript `τon = (τu, τd)` on database `D` and query tuple `Q`
[Hoover, Persiano and Yeo, Definition 6.1, p. 44][HooverPersianoYeo2026]. -/
@[expose] def onlineTranscript (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp (Tu × Td) := do
  let r ← P.rLaw
  P.onlineTranscriptAt D Q r

/-- The online download transcript `τd` on database `D` and query tuple `Q`. -/
@[expose] def onlineDownload (D : Fin n → Bool) (Q : Fin k → Fin n) : ProbComp Td :=
  Prod.snd <$> P.onlineTranscript D Q

/-! ### Correctness, privacy, and data privacy predicates (Definition 6.1) -/

/-- `ε`-correctness [Hoover, Persiano and Yeo, Definition 6.1, p. 45][HooverPersianoYeo2026]:
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
[Hoover, Persiano and Yeo, Definition 6.1, p. 45][HooverPersianoYeo2026]): for every database `D`
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
[Hoover, Persiano and Yeo, Definition 6.1, p. 45][HooverPersianoYeo2026]): for every query tuple
`Q` and databases `D₀, D₁` agreeing on `Q` (`D₀ ∘ Q = D₁ ∘ Q`), the client's view distribution
is identical. -/
@[expose] def IsPerfectlyDataPrivate : Prop :=
  ∀ (D₀ D₁ : Fin n → Bool) (Q : Fin k → Fin n),
    D₀ ∘ Q = D₁ ∘ Q →
      ProbComp.eval (P.clientView D₀ Q) = ProbComp.eval (P.clientView D₁ Q)

theorem isCorrect_iff_isCorrectWith_one : P.IsCorrect ↔ P.IsCorrectWith 1 := by
  refine forall_congr' fun D => forall_congr' fun Q => ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, PMF.pure_apply_self, ENNReal.toReal_one]
  · have hle1 : ProbComp.eval (P.run D Q) (D ∘ Q) ≤ 1 := PMF.coe_le_one _ _
    have hge1 : (1 : ℝ≥0∞) ≤ ProbComp.eval (P.run D Q) (D ∘ Q) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_of_le_toReal h
    have hsupp : (ProbComp.eval (P.run D Q)).support = {D ∘ Q} :=
      (PMF.apply_eq_one_iff _ _).mp (le_antisymm hle1 hge1)
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
@[expose] def privacyExperimentAt (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (R × Toff × Tu × Td) → Experiment) (r : R) : Experiment :=
  P.serverViewAt D Q r >>= adv

/-- The server privacy distinguishing experiment on database `D`, query tuple `Q`, and
distinguisher `adv`. -/
@[expose] def privacyExperiment (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (R × Toff × Tu × Td) → Experiment) : Experiment :=
  P.rLaw >>= P.privacyExperimentAt D Q adv

/-- The server privacy game built with `Game.withSetup` over the server randomness law
`ProbComp.eval P.rLaw`. -/
@[expose] noncomputable def privacyGame (D : Fin n → Bool) (Q : Fin k → Fin n)
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
on database `D` [Hoover, Persiano and Yeo, Definition 6.1, p. 45][HooverPersianoYeo2026]. -/
@[expose] noncomputable def privacyAdvantage (D : Fin n → Bool) (Q₀ Q₁ : Fin k → Fin n)
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
@[expose] def dataPrivacyExperimentAt (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (St × Toff × Tu × Td) → Experiment) (r : R) : Experiment :=
  P.clientViewAt D Q r >>= adv

/-- The client data-privacy distinguishing experiment on database `D`, query tuple `Q`, and
distinguisher `adv`. -/
@[expose] def dataPrivacyExperiment (D : Fin n → Bool) (Q : Fin k → Fin n)
    (adv : (St × Toff × Tu × Td) → Experiment) : Experiment :=
  P.rLaw >>= P.dataPrivacyExperimentAt D Q adv

/-- The client data-privacy game built with `Game.withSetup` over the server randomness law
`ProbComp.eval P.rLaw`. -/
@[expose] noncomputable def dataPrivacyGame (D : Fin n → Bool) (Q : Fin k → Fin n)
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
on query tuple `Q` [Hoover, Persiano and Yeo, Definition 6.1, p. 45][HooverPersianoYeo2026]. -/
@[expose] noncomputable def dataPrivacyAdvantage (D₀ D₁ : Fin n → Bool) (Q : Fin k → Fin n)
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

/-- Helper: when `2 ≤ n`, every index `i : Fin n` has a distinct index `j ≠ i`. -/
private theorem exists_ne_of_two_le (hn : 2 ≤ n) (i : Fin n) : ∃ j : Fin n, j ≠ i := by
  by_cases hi : i.val = 0
  · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
    simp only [Fin.ext_iff] at h
    omega
  · refine ⟨⟨0, by omega⟩, fun h => ?_⟩
    simp only [Fin.ext_iff] at h
    omega

/-- General transcript-independence step from query-invariance and outside-`Q` database
invariance of `onlineTranscript`. -/
private theorem eval_onlineTranscript_update_eq_of_marginal {P : Scheme n k R St Toff Tu Td}
    (hn : 2 ≤ n)
    (hpriv_on : ∀ D Q₀ Q₁,
      ProbComp.eval (P.onlineTranscript D Q₀) = ProbComp.eval (P.onlineTranscript D Q₁))
    (hdpriv_on : ∀ {D₀ D₁ : Fin n → Bool} {Q : Fin k → Fin n}, D₀ ∘ Q = D₁ ∘ Q →
      ProbComp.eval (P.onlineTranscript D₀ Q) = ProbComp.eval (P.onlineTranscript D₁ Q))
    (D : Fin n → Bool) (i : Fin n) (b : Bool) (Q : Fin k → Fin n) :
    ProbComp.eval (P.onlineTranscript (Function.update D i b) Q) =
      ProbComp.eval (P.onlineTranscript D Q) := by
  obtain ⟨j, hj⟩ := exists_ne_of_two_le hn i
  let Q' : Fin k → Fin n := fun _ => j
  have hagree : Function.update D i b ∘ Q' = D ∘ Q' := by
    funext m
    exact Function.update_of_ne hj b D
  calc
    ProbComp.eval (P.onlineTranscript (Function.update D i b) Q)
        = ProbComp.eval (P.onlineTranscript (Function.update D i b) Q') :=
          hpriv_on _ Q Q'
    _ = ProbComp.eval (P.onlineTranscript D Q') :=
          hdpriv_on hagree
    _ = ProbComp.eval (P.onlineTranscript D Q) :=
          hpriv_on _ Q' Q

/-- Flipping or updating a single database entry `i` preserves the online transcript distribution
when `2 ≤ n`: chain `(D', Q) → (D', const j) → (D, const j) → (D, Q)` for `j ≠ i`. -/
theorem eval_onlineTranscript_update_eq {P : Scheme n k R St Toff Tu Td} (hn : 2 ≤ n)
    (hpriv : P.IsPerfectlyPrivate) (hdpriv : P.IsPerfectlyDataPrivate)
    (D : Fin n → Bool) (i : Fin n) (b : Bool) (Q : Fin k → Fin n) :
    ProbComp.eval (P.onlineTranscript (Function.update D i b) Q) =
      ProbComp.eval (P.onlineTranscript D Q) :=
  eval_onlineTranscript_update_eq_of_marginal hn hpriv.eval_onlineTranscript_eq
    hdpriv.eval_onlineTranscript_eq D i b Q

/-- Auxiliary induction on the number of disagreeing coordinates between `D₀` and `D₁`. -/
private theorem eval_onlineTranscript_eq_of_card_diff {P : Scheme n k R St Toff Tu Td}
    (hn : 2 ≤ n)
    (hpriv_on : ∀ D Q₀ Q₁,
      ProbComp.eval (P.onlineTranscript D Q₀) = ProbComp.eval (P.onlineTranscript D Q₁))
    (hdpriv_on : ∀ {D₀ D₁ : Fin n → Bool} {Q : Fin k → Fin n}, D₀ ∘ Q = D₁ ∘ Q →
      ProbComp.eval (P.onlineTranscript D₀ Q) = ProbComp.eval (P.onlineTranscript D₁ Q))
    (Q : Fin k → Fin n) :
    ∀ (m : ℕ) (D₀ D₁ : Fin n → Bool),
      (Finset.univ.filter (fun i => D₀ i ≠ D₁ i)).card = m →
        ProbComp.eval (P.onlineTranscript D₀ Q) = ProbComp.eval (P.onlineTranscript D₁ Q)
  | 0, D₀, D₁, hm => by
    have hD : D₀ = D₁ := by
      funext i
      by_contra hne
      have hmem : i ∈ Finset.univ.filter (fun j => D₀ j ≠ D₁ j) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
      rw [Finset.card_eq_zero.mp hm] at hmem
      exact Finset.notMem_empty i hmem
    rw [hD]
  | m + 1, D₀, D₁, hm => by
    have hne_empty : (Finset.univ.filter (fun i => D₀ i ≠ D₁ i)).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨i, hi⟩ := hne_empty
    have hcard_erase :
        (Finset.univ.filter (fun j => Function.update D₀ i (D₁ i) j ≠ D₁ j)).card = m := by
      have hfilter :
          Finset.univ.filter (fun j => Function.update D₀ i (D₁ i) j ≠ D₁ j) =
            (Finset.univ.filter (fun j => D₀ j ≠ D₁ j)).erase i := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        by_cases hji : j = i
        · subst hji
          simp
        · simp [hji]
      rw [hfilter, Finset.card_erase_of_mem hi, hm]
      rfl
    calc
      ProbComp.eval (P.onlineTranscript D₀ Q)
          = ProbComp.eval (P.onlineTranscript (Function.update D₀ i (D₁ i)) Q) :=
            (eval_onlineTranscript_update_eq_of_marginal hn hpriv_on hdpriv_on
              D₀ i (D₁ i) Q).symm
      _ = ProbComp.eval (P.onlineTranscript D₁ Q) :=
            eval_onlineTranscript_eq_of_card_diff hn hpriv_on hdpriv_on Q m
              (Function.update D₀ i (D₁ i)) D₁ hcard_erase

/-- **Online transcript independence** ([Hoover, Persiano and Yeo, Proof of Theorem 6.2,
p. 46][HooverPersianoYeo2026]): when `2 ≤ n`, perfect privacy and perfect data privacy imply that
the online transcript `τon = (τu, τd)` has the exact same distribution for all databases `D₀, D₁`
and all batch query tuples `Q₀, Q₁`. -/
theorem eval_onlineTranscript_eq {P : Scheme n k R St Toff Tu Td} (hn : 2 ≤ n)
    (hpriv : P.IsPerfectlyPrivate) (hdpriv : P.IsPerfectlyDataPrivate)
    (D₀ D₁ : Fin n → Bool) (Q₀ Q₁ : Fin k → Fin n) :
    ProbComp.eval (P.onlineTranscript D₀ Q₀) = ProbComp.eval (P.onlineTranscript D₁ Q₁) := by
  calc
    ProbComp.eval (P.onlineTranscript D₀ Q₀)
        = ProbComp.eval (P.onlineTranscript D₁ Q₀) :=
          eval_onlineTranscript_eq_of_card_diff hn hpriv.eval_onlineTranscript_eq
            hdpriv.eval_onlineTranscript_eq Q₀ _ D₀ D₁ rfl
    _ = ProbComp.eval (P.onlineTranscript D₁ Q₁) :=
          hpriv.eval_onlineTranscript_eq D₁ Q₀ Q₁

/-- Under `2 ≤ n`, perfect privacy, and perfect data privacy, the download transcript `τd` has the
same distribution for all databases and query tuples. -/
theorem eval_onlineDownload_eq {P : Scheme n k R St Toff Tu Td} (hn : 2 ≤ n)
    (hpriv : P.IsPerfectlyPrivate) (hdpriv : P.IsPerfectlyDataPrivate)
    (D₀ D₁ : Fin n → Bool) (Q₀ Q₁ : Fin k → Fin n) :
    ProbComp.eval (P.onlineDownload D₀ Q₀) = ProbComp.eval (P.onlineDownload D₁ Q₁) := by
  simp only [onlineDownload, ProbComp.eval_map,
    eval_onlineTranscript_eq hn hpriv hdpriv D₀ D₁ Q₀ Q₁]

/-! ### Core batch SPIR lower bound (Theorem 6.2) -/

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
  refine Summable.tsum_le_tsum (fun ⟨st, τd⟩ => ?_) CompleteLattice.summable
    CompleteLattice.summable
  split_ifs with hy hmem
  · exact le_rfl
  · exfalso
    refine hmem ?_
    simp only [Function.comp_apply, true_eq_decide_iff, candidateOutputs, hy]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ st)
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
      (∑ y : Fin k → Bool, ProbComp.eval (P.run (padDB y) Q) y) ≤
        (Fintype.card St : ℝ≥0∞) := by
    calc
      (∑ y : Fin k → Bool, ProbComp.eval (P.run (padDB y) Q) y)
          ≤ ∑ y : Fin k → Bool,
              τLaw.map (fun τd => decide (y ∈ P.candidateOutputs Q τd)) true := by
            refine Finset.sum_le_sum fun y _ => ?_
            have h := P.eval_run_le_onlineDownload_candidateOutputs (padDB y) Q y
            rwa [hdl (padDB y) D₀] at h
      _ = ∑' τd : Td, ∑ y : Fin k → Bool,
            (if true = decide (y ∈ P.candidateOutputs Q τd) then τLaw τd else 0) := by
            simp only [PMF.map_apply]
            rw [← Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
            exact tsum_congr fun _ => Finset.sum_congr rfl fun _ _ => by congr
      _ ≤ ∑' τd : Td, (Fintype.card St : ℝ≥0∞) * τLaw τd := by
            refine Summable.tsum_le_tsum (fun τd => ?_) CompleteLattice.summable
              CompleteLattice.summable
            have hinner :
                (∑ y : Fin k → Bool,
                  if true = decide (y ∈ P.candidateOutputs Q τd) then τLaw τd else 0) =
                  ((P.candidateOutputs Q τd).card : ℝ≥0∞) * τLaw τd := by
              simp only [true_eq_decide_iff, ← Finset.sum_filter, Finset.filter_univ_mem,
                Finset.sum_const, nsmul_eq_mul]
            rw [hinner]
            gcongr
            exact Nat.cast_le.mpr (P.card_candidateOutputs_le Q τd)
      _ = (Fintype.card St : ℝ≥0∞) := by
            rw [ENNReal.tsum_mul_left, τLaw.tsum_coe, mul_one]
  have hsum_real :
      (∑ y : Fin k → Bool, (ProbComp.eval (P.run (padDB y) Q) y).toReal) ≤
        (Fintype.card St : ℝ) := by
    have hne_top : ∀ y ∈ (Finset.univ : Finset (Fin k → Bool)),
        ProbComp.eval (P.run (padDB y) Q) y ≠ ⊤ :=
      fun y _ => ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one _ _)
    rw [← ENNReal.toReal_sum hne_top, ← ENNReal.toReal_natCast (Fintype.card St)]
    exact ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hsum_ennreal
  have h2k_mul : (2 : ℝ) ^ k * ε ≤ (Fintype.card St : ℝ) := by
    calc
      (2 : ℝ) ^ k * ε
          = ∑ _y : Fin k → Bool, ε := by
            simp [Finset.sum_const, Fintype.card_bool]
      _ ≤ ∑ y : Fin k → Bool, (ProbComp.eval (P.run (padDB y) Q) y).toReal := by
            refine Finset.sum_le_sum fun y _ => ?_
            have h := hcorr (padDB y) Q
            rwa [padDB_comp_castLE hkn y] at h
      _ ≤ (Fintype.card St : ℝ) := hsum_real
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [le_div_iff₀ h2k_pos, mul_comm]
  exact h2k_mul

/-- **Core batch SPIR lower bound** ([Hoover, Persiano and Yeo, Theorem 6.2,
p. 46][HooverPersianoYeo2026], plain-model one-round deterministic-online-client core): if
`2 ≤ n`, `k ≤ n`, and `P` is `ε`-correct, perfectly private, and perfectly data private with
finite client state `St`, then `ε ≤ Fintype.card St / 2 ^ k`. -/
theorem correct_le_card_div_two_pow [Fintype St] {ε : ℝ} (hn : 2 ≤ n) (hkn : k ≤ n)
    (hpriv : P.IsPerfectlyPrivate) (hdpriv : P.IsPerfectlyDataPrivate)
    (hcorr : P.IsCorrectWith ε) :
    ε ≤ (Fintype.card St : ℝ) / 2 ^ k :=
  P.correct_le_card_div_two_pow_of_onlineDownload_eq hkn
    (fun D₁ D₂ => P.eval_onlineDownload_eq hn hpriv hdpriv D₁ D₂ _ _) hcorr

/-- With `s`-bit client storage (`Fintype.card St ≤ 2 ^ s`), `ε ≤ 2 ^ (s - k)`. -/
theorem correct_le_two_pow_sub [Fintype St] {s : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hkn : k ≤ n)
    (hst : Fintype.card St ≤ 2 ^ s) (hpriv : P.IsPerfectlyPrivate)
    (hdpriv : P.IsPerfectlyDataPrivate) (hcorr : P.IsCorrectWith ε) :
    ε ≤ (2 : ℝ) ^ ((s : ℤ) - (k : ℤ)) := by
  have hcore := P.correct_le_card_div_two_pow hn hkn hpriv hdpriv hcorr
  have hcard : (Fintype.card St : ℝ) ≤ (2 : ℝ) ^ s := by exact_mod_cast hst
  have hpow : (2 : ℝ) ^ s / (2 : ℝ) ^ k = (2 : ℝ) ^ ((s : ℤ) - (k : ℤ)) := by
    rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
  linarith [div_le_div_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)]

/-- A perfectly correct, perfectly private, and perfectly data-private `k`-batch SPIR scheme
with `2 ≤ n` and `k ≤ n` requires client state size at least `2 ^ k`. -/
theorem two_pow_le_card_state [Fintype St] (hn : 2 ≤ n) (hkn : k ≤ n)
    (hpriv : P.IsPerfectlyPrivate) (hdpriv : P.IsPerfectlyDataPrivate) (hcorr : P.IsCorrect) :
    2 ^ k ≤ Fintype.card St := by
  have hle := P.correct_le_card_div_two_pow hn hkn hpriv hdpriv hcorr.isCorrectWith_one
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hmul : (2 : ℝ) ^ k ≤ (Fintype.card St : ℝ) := by
    rwa [le_div_iff₀ h2k_pos, one_mul] at hle
  exact_mod_cast hmul

/-- **Batch SPIR limitation** ([Hoover, Persiano and Yeo, Theorem 6.2,
p. 46][HooverPersianoYeo2026], plain-model one-round deterministic-online-client corollary):
when `2 ≤ n`, `s < k ≤ n`, `Fintype.card St ≤ 2 ^ s`, and `ε > 1 - 2 ^ (s - k)`, no `k`-batch
SPIR scheme can be simultaneously `ε`-correct, perfectly private, and perfectly data private. -/
theorem batchSPIR_limitation [Fintype St] {s : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hsk : s < k)
    (hkn : k ≤ n) (hst : Fintype.card St ≤ 2 ^ s)
    (hε : 1 - (2 : ℝ) ^ ((s : ℤ) - (k : ℤ)) < ε) (hpriv : P.IsPerfectlyPrivate)
    (hdpriv : P.IsPerfectlyDataPrivate) : ¬ P.IsCorrectWith ε := by
  intro hcorr
  have hle := P.correct_le_two_pow_sub hn hkn hst hpriv hdpriv hcorr
  have hexp_le : (s : ℤ) - (k : ℤ) ≤ -1 := by omega
  have hpow_le_half : (2 : ℝ) ^ ((s : ℤ) - (k : ℤ)) ≤ 1 / 2 := by
    calc
      (2 : ℝ) ^ ((s : ℤ) - (k : ℤ)) ≤ (2 : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) hexp_le
      _ = 1 / 2 := by norm_num
  linarith

end Scheme

/-- Existential form of `Scheme.batchSPIR_limitation` ([Hoover, Persiano and Yeo, Theorem 6.2,
p. 46][HooverPersianoYeo2026]): for `2 ≤ n`, `s < k ≤ n`, and `ε > 1 - 2 ^ (s - k)`, there does
not exist a `k`-batch SPIR scheme with `Fintype.card St ≤ 2 ^ s` that is `ε`-correct, perfectly
private, and perfectly data private. -/
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
@[expose] def serverView (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp (R × Toff × Tu × Td) := do
  let r ← P.rLaw
  let (st, τoff) ← P.setup D r
  let ω ← P.ωLaw
  let τu := P.query st ω Q
  let τd := P.answer D r τu
  pure (r, τoff, τu, τd)

/-- Client view `(st, τoff, τu, τd)` on database `D` and query tuple `Q` (without ephemeral
online coins `ω`, matching Definition 6.1). -/
@[expose] def clientView (D : Fin n → Bool) (Q : Fin k → Fin n) :
    ProbComp (St × Toff × Tu × Td) := do
  let r ← P.rLaw
  let (st, τoff) ← P.setup D r
  let ω ← P.ωLaw
  let τu := P.query st ω Q
  let τd := P.answer D r τu
  pure (st, τoff, τu, τd)

/-- Online transcript `τon = (τu, τd)` on database `D` and query tuple `Q`. -/
@[expose] def onlineTranscript (D : Fin n → Bool) (Q : Fin k → Fin n) :
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

/-- **Online-randomized client batch SPIR lower bound**: if `2 ≤ n`, `k ≤ n`, and `P` is
`ε`-correct, perfectly private, and perfectly data private with finite client state `St` and
finite online coin space `Ω`, then `ε ≤ Fintype.card St * Fintype.card Ω / 2 ^ k`. -/
theorem correct_le_card_mul_card_div_two_pow [Fintype St] [Fintype Ω] {ε : ℝ}
    (hn : 2 ≤ n) (hkn : k ≤ n) (hpriv : P.IsPerfectlyPrivate)
    (hdpriv : P.IsPerfectlyDataPrivate) (hcorr : P.IsCorrectWith ε) :
    ε ≤ (Fintype.card St * Fintype.card Ω : ℝ) / 2 ^ k := by
  have hpriv_prod : P.toProductScheme.IsPerfectlyPrivate := fun D Q₀ Q₁ => by
    rw [P.serverView_toProductScheme, P.serverView_toProductScheme, hpriv D Q₀ Q₁]
  have hdpriv_on : ∀ {D₀ D₁ : Fin n → Bool} {Q : Fin k → Fin n}, D₀ ∘ Q = D₁ ∘ Q →
      ProbComp.eval (P.toProductScheme.onlineTranscript D₀ Q) =
        ProbComp.eval (P.toProductScheme.onlineTranscript D₁ Q) := fun hD => by
    rw [P.onlineTranscript_toProductScheme, P.onlineTranscript_toProductScheme,
      ProbComp.eval_map, ProbComp.eval_map, hdpriv _ _ _ hD]
  have hdl : ∀ D₁ D₂ : Fin n → Bool,
      ProbComp.eval (P.toProductScheme.onlineDownload D₁ (Fin.castLE hkn)) =
        ProbComp.eval (P.toProductScheme.onlineDownload D₂ (Fin.castLE hkn)) := by
    intro D₁ D₂
    simp only [Scheme.onlineDownload, ProbComp.eval_map,
      Scheme.eval_onlineTranscript_eq_of_card_diff hn hpriv_prod.eval_onlineTranscript_eq
        hdpriv_on (Fin.castLE hkn) _ D₁ D₂ rfl]
  have hcorr_prod : P.toProductScheme.IsCorrectWith ε := fun D Q => by
    rw [P.run_toProductScheme]
    exact hcorr D Q
  have hle := P.toProductScheme.correct_le_card_div_two_pow_of_onlineDownload_eq hkn hdl hcorr_prod
  rwa [Fintype.card_prod, Nat.cast_mul] at hle

end RandomizedScheme

end Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing
