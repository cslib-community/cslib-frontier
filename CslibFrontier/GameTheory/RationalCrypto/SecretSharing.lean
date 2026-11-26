/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Basic
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Shamir
public import CslibFrontier.GameTheory.Strategic.Payoff
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rational Secret Sharing

In **rational secret sharing** ([HalpernTeague2004]; [AbrahamDolevGonenHalpern2006];
[DodisRabin2007], Section 8.5.2), self-interested parties hold shares of a secret and interact to
reconstruct it. Unlike Byzantine adversaries, rational parties maximize utility with strict
exclusivity and correctness preferences `U⁺ > U > U⁻`:

1. `uPlus` (`U⁺`): the party learns the secret while at least one other party fails to learn it;
2. `uAll` (`U`): every party learns the secret;
3. `uMinus` (`U⁻`): the party fails to learn the secret (whether nobody learns or others learn
   while this party fails).

General utility-maximization game infrastructure (`Cslib.GameTheory.PayoffGame`, `IsPureNash`,
`IsCoalitionProofUpTo`, `WeaklyDominatesOn`, `idowdsIter`, and `HasBackwardInductionDominance`)
lives in `CslibFrontier.GameTheory.Strategic.Payoff`, bridged directly to
`Cslib.GameTheory.CostGame` and `CostGame.idowdsSeq` in
`CslibFrontier.GameTheory.Strategic.Dominance`.

This module formalizes the `(t, n)` and `(n, n)` rational secret-sharing reconstruction games and
two foundational results:

1. **Halpern–Teague bounded-round impossibility** ([HalpernTeague2004]; [DodisRabin2007],
   Section 8.5.2(a)):
   - In single-round (or final-round) simultaneous `(t, n)` broadcast (`2 ≤ t ≤ n`), withholding
     weakly dominates broadcasting for every player, so a single step of iterated deletion of
     weakly dominated strategies (`IDoWDS`) eliminates broadcasting and leaves only `"never
     broadcast"` (`ReconstructionGame.idowdsIter_simultaneousGame_one`).
   - More generally, in any `T`-round cutoff mechanism admitting `HasBackwardInductionDominance`,
     `k` steps of `IDoWDS` eliminate the top `k` participation horizons and `T` steps leave only
     `0` (`"never broadcast"`, `PayoffGame.idowdsIter_eq_singleton_zero`). This applies
     unconditionally to the `T`-round `(t, n)` gradual-release game
     (`ReconstructionGame.idowdsIter_gradualReleaseGame`,
     `ReconstructionGame.idowdsIter_uniformRampGame`), while in the `T`-round known-final-round
     dummy-prefix game (`ReconstructionGame.knownHorizonGame`), final-round withholding eliminates
     full participation in one step so no surviving profile reconstructs the secret.
2. **Randomized geometric-termination protocol (`k < n` utility-dependent regime)**
   ([HalpernTeague2004]; [AbrahamDolevGonenHalpern2006]; [DodisRabin2007], Section 8.5.2(b) and
   Theorem 8.9):
   - In each round `r : ℕ`, a dealer (or preprocessed mediator) distributes fresh shares using an
     information-theoretic `AccessScheme` (such as `shamirUniformAccessScheme`), sharing the
     genuine secret with probability `p ∈ (0, 1)` and a dummy value with probability `1 - p`, while
     honest players broadcast simultaneously and abort all future rounds if any player withholds.
   - Define the critical stopping threshold `criticalStoppingProb = (U - U⁻) / (U⁺ - U⁻) ∈ (0, 1)`.
   - **Stage game:** for `p ≤ criticalStoppingProb`, honest simultaneous broadcast is a pure Nash
     equilibrium of every stage (`honest_isPureNash_geometricStageGame`), and a strict pure Nash
     equilibrium when `p < criticalStoppingProb` (`honest_isStrictPureNash_geometricStageGame`).
     For `n`-out-of-`n` reconstruction with `p < criticalStoppingProb`, honest broadcast weakly
     dominates withholding and is the unique strategy surviving `IDoWDS` in each stage
     (`idowdsIter_geometricStageGame_one`).
   - **Infinite-horizon cryptographic protocol with joint-view share-pooling coalitions:** by
     `AccessScheme.viewDist_eq_of_not_authorized`, no unauthorized coalition `C` pooling its joint
     share view `(j : C) → Share j.1` and pooling its unbroadcast shares with the round's broadcast
     set (`GeometricProtocol.learnedFromCoalition`) can distinguish genuine shares from dummy
     shares before deciding its joint round action `CoalitionStrategy C`. An exact telescoping
     identity over all `r : ℕ` (`uAll_sub_geometricExpectedUtility`) shows that honest
     simultaneous broadcast achieves expected utility `U` and, when `p ≤ criticalStoppingProb`, is
     immune to arbitrary joint multi-round share-inspecting coalition deviations for every
     unauthorized coalition (`honestProfile_isJointCoalitionProof`, giving `(t - 1)`-resilience
     `honestProfile_isJointCoalitionProofUpTo` for `(t, n)` threshold schemes, which strictly
     subsumes independent strategies via `payoff_piecewise_le_coalitionPayoff` and
     `IsJointCoalitionProofUpTo.toPayoffGame`). Moreover, across the entire no-honest-majority
     threshold regime `n < 2 * t - 1`, `p ≤ criticalStoppingProb` is both necessary and sufficient
     for `(t - 1)`-coalitional resilience (`honestProfile_isJointCoalitionProofUpTo_iff`). When
     `p < criticalStoppingProb`, any unilateral strategy that withholds with positive probability in
     some round achieves strictly less than `U` (`payoff_lt_uAll_of_withholdProb_pos`).

**Scope boundary vs `[DodisRabin2007]`, Theorem 8.9:** Theorem 8.9 in `[DodisRabin2007]` states
`k`-resilient equilibria *surviving `IDoWDS`* across three expected-round regimes (`k < n`
utility-dependent; `k < n/2` fixed rounds with utility parameter; `k < n/3` utility-independent).
Here, `IDoWDS` survival is proved on the one-shot `n`-out-of-`n` stage game `geometricStageGame`
(`idowdsIter_geometricStageGame_one`), and only the `k < n` (`t - 1 < n`) utility-dependent
geometric-termination regime is formalized for multi-round `GeometricProtocol`; fixed-round
`k < n/2` and utility-independent `k < n/3` protocols are out of scope.

## Main definitions

* `Cslib.GameTheory.RationalCrypto.SecretSharingPrefs`: rational secret-sharing utility levels
  `uMinus < uAll < uPlus` (`U⁻ < U < U⁺`), outcome utility `outcomeUtility`, and threshold
  `criticalStoppingProb = (uAll - uMinus) / (uPlus - uMinus)`.
* `Cslib.GameTheory.RationalCrypto.ReconstructionGame`, `ReconstructionGame.allOfAll`: `(t, n)`
  and `(n, n)` rational secret-sharing reconstruction games (`simultaneousGame`,
  `gradualReleaseGame`, `uniformRampGame`, `knownHorizonGame`, `geometricStageGame`).
* `Cslib.GameTheory.RationalCrypto.GeometricProtocol`, `GeometricProtocol.ofShamir`,
  `GeometricProtocol.CoalitionStrategy`, `GeometricProtocol.learnedFromCoalition`,
  `GeometricProtocol.coalitionPayoff`, `GeometricProtocol.IsJointCoalitionProofUpTo`:
  infinite-horizon geometric-stopping rational secret-sharing protocol over any `AccessScheme`
  (and finite-field Shamir sharing) with pooled joint-view coalition deviations.

## Main results

* `ReconstructionGame.withhold_weaklyDominates_broadcast`,
  `ReconstructionGame.idowdsIter_simultaneousGame_one`: in simultaneous `(t, n)` share broadcast
  (`2 ≤ t ≤ n`), withholding weakly dominates broadcasting and is the unique survivor of `IDoWDS`.
* `ReconstructionGame.hasBackwardInductionDominance_gradualReleaseGame`,
  `ReconstructionGame.idowdsIter_gradualReleaseGame`,
  `ReconstructionGame.hasBackwardInductionDominance_uniformRampGame`,
  `ReconstructionGame.idowdsIter_uniformRampGame`: `T`-round `(t, n)` gradual-release mechanisms
  collapse to `{0}` after `T` rounds of `IDoWDS`.
* `ReconstructionGame.payoff_knownHorizonGame_eq_uMinus_of_mem_idowdsIter_one`: in the `T`-round
  known-final-round protocol (`1 ≤ T`), full participation is eliminated in one step of `IDoWDS`
  and every surviving profile yields `uMinus`.
* `ReconstructionGame.honest_isStrictPureNash_geometricStageGame`,
  `ReconstructionGame.honest_isPureNash_geometricStageGame_iff`,
  `ReconstructionGame.idowdsIter_geometricStageGame_one`: stage strict Nash equilibrium, exact
  `n`-out-of-`n` Nash threshold characterization, and stage `IDoWDS` uniqueness for
  `p < criticalStoppingProb`.
* `uAll_sub_geometricExpectedUtility`: exact infinite-horizon telescoping identity for expected
  utility under arbitrary round withholding probabilities.
* `GeometricProtocol.roundCoalitionBroadcastDist_eq`,
  `GeometricProtocol.honestProfile_isJointCoalitionProof`,
  `GeometricProtocol.honestProfile_isJointCoalitionProofUpTo`,
  `GeometricProtocol.ofShamir_honestProfile_isJointCoalitionProofUpTo`,
  `GeometricProtocol.IsJointCoalitionProofUpTo.toPayoffGame`: for
  `stopProb ≤ criticalStoppingProb`, honest simultaneous broadcast is resilient against arbitrary
  multi-round joint-view share-pooling coalition deviations (`(t - 1)`-resilient for `(t, n)`
  threshold and Shamir schemes), subsuming independent-strategy deviations.
* `GeometricProtocol.honestProfile_isJointCoalitionProofUpTo_iff`: in any `(t, n)` threshold
  scheme in the no-honest-majority regime `n < 2 * t - 1`, `honestProfile` is `(t - 1)`-resilient
  against pooled joint-view coalitions if and only if `stopProb ≤ criticalStoppingProb`.
* `GeometricProtocol.payoff_lt_uAll_of_withholdProb_pos`,
  `GeometricProtocol.honestProfile_isPureNash_iff`: strict optimality against positive-probability
  withholding when `stopProb < criticalStoppingProb`, and exact `n`-out-of-`n` Nash equilibrium
  characterization.

## References

* [J. Y. Halpern, V. Teague,
  *Rational Secret Sharing and Multiparty Computation*][HalpernTeague2004]
* [I. Abraham, D. Dolev, R. Gonen, J. Y. Halpern,
  *Distributed Computing Meets Game Theory*][AbrahamDolevGonenHalpern2006]
* [Y. Dodis, T. Rabin, *Cryptography and Game Theory*][DodisRabin2007], Section 8.5.2 and
  Theorem 8.9
-/

public section

namespace Cslib.GameTheory.RationalCrypto

open Cslib.Crypto.Protocols.SecretSharing
open Cslib.Probability Cslib.Probability.PMF
open Finset Filter Topology

/-! ### Rational secret-sharing preferences (`U⁺ > U > U⁻`) and `(t, n)` reconstruction -/

/-- Utility levels of a rational secret-sharing player ([HalpernTeague2004];
[AbrahamDolevGonenHalpern2006]; [DodisRabin2007], Section 8.5.2), satisfying `U⁺ > U > U⁻`:
learning the secret while at least one other party fails (`uPlus`) is strictly preferred to
everyone learning (`uAll`), which is strictly preferred to failing to learn (`uMinus`). -/
structure SecretSharingPrefs where
  /-- Payoff `U⁺` when the player learns the secret and at least one other player does not. -/
  uPlus : ℝ
  /-- Payoff `U` when all players learn the secret. -/
  uAll : ℝ
  /-- Payoff `U⁻` when the player fails to learn the secret. -/
  uMinus : ℝ
  /-- Correctness preference: all learning strictly beats failing to learn (`U⁻ < U`). -/
  uMinus_lt_uAll : uMinus < uAll
  /-- Exclusivity preference: learning while denying another beats all learning (`U < U⁺`). -/
  uAll_lt_uPlus : uAll < uPlus

namespace SecretSharingPrefs

/-- Transitive strict preference `U⁻ < U⁺`. -/
theorem uMinus_lt_uPlus (prefs : SecretSharingPrefs) : prefs.uMinus < prefs.uPlus :=
  prefs.uMinus_lt_uAll.trans prefs.uAll_lt_uPlus

private theorem uPlus_sub_uMinus_pos (prefs : SecretSharingPrefs) :
    0 < prefs.uPlus - prefs.uMinus :=
  sub_pos.mpr prefs.uMinus_lt_uPlus

private theorem uAll_sub_uMinus_pos (prefs : SecretSharingPrefs) :
    0 < prefs.uAll - prefs.uMinus :=
  sub_pos.mpr prefs.uMinus_lt_uAll

/-- Payoff of player `i` when `learned : Finset ι` is the set of players who reconstruct the
secret: `uAll` if everyone learns, `uPlus` if `i` learns and some player does not, and `uMinus` if
`i` fails to learn. -/
def outcomeUtility {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prefs : SecretSharingPrefs) (learned : Finset ι) (i : ι) : ℝ :=
  if i ∈ learned then
    if learned = Finset.univ then prefs.uAll else prefs.uPlus
  else
    prefs.uMinus

@[simp]
theorem outcomeUtility_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prefs : SecretSharingPrefs) (i : ι) :
    prefs.outcomeUtility (Finset.univ : Finset ι) i = prefs.uAll := by
  simp [outcomeUtility]

@[simp]
theorem outcomeUtility_empty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prefs : SecretSharingPrefs) (i : ι) :
    prefs.outcomeUtility (∅ : Finset ι) i = prefs.uMinus := by
  simp [outcomeUtility]

theorem outcomeUtility_of_not_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prefs : SecretSharingPrefs) {learned : Finset ι} {i : ι} (hi : i ∉ learned) :
    prefs.outcomeUtility learned i = prefs.uMinus := by
  simp [outcomeUtility, hi]

theorem outcomeUtility_of_mem_of_ne_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prefs : SecretSharingPrefs) {learned : Finset ι} {i : ι}
    (hi : i ∈ learned) (hne : learned ≠ Finset.univ) :
    prefs.outcomeUtility learned i = prefs.uPlus := by
  simp [outcomeUtility, hi, hne]

/-- Every outcome gives player `i` utility at most `uPlus`. -/
theorem outcomeUtility_le_uPlus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prefs : SecretSharingPrefs) (learned : Finset ι) (i : ι) :
    prefs.outcomeUtility learned i ≤ prefs.uPlus := by
  unfold outcomeUtility
  split_ifs
  · exact prefs.uAll_lt_uPlus.le
  · exact le_rfl
  · exact prefs.uMinus_lt_uPlus.le

/-- Every outcome gives player `i` utility at least `uMinus`. -/
theorem uMinus_le_outcomeUtility {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prefs : SecretSharingPrefs) (learned : Finset ι) (i : ι) :
    prefs.uMinus ≤ prefs.outcomeUtility learned i := by
  unfold outcomeUtility
  split_ifs
  · exact prefs.uMinus_lt_uAll.le
  · exact prefs.uMinus_lt_uPlus.le
  · exact le_rfl

/-- The **critical stopping probability** `(U - U⁻) / (U⁺ - U⁻) ∈ (0, 1)` governing incentive
compatibility in randomized geometric-termination secret-sharing protocols ([HalpernTeague2004];
[AbrahamDolevGonenHalpern2006]; [DodisRabin2007], Section 8.5.2(b)). -/
noncomputable def criticalStoppingProb (prefs : SecretSharingPrefs) : ℝ :=
  (prefs.uAll - prefs.uMinus) / (prefs.uPlus - prefs.uMinus)

theorem criticalStoppingProb_eq (prefs : SecretSharingPrefs) :
    prefs.criticalStoppingProb = (prefs.uAll - prefs.uMinus) / (prefs.uPlus - prefs.uMinus) := by
  rfl

theorem criticalStoppingProb_pos (prefs : SecretSharingPrefs) :
    0 < prefs.criticalStoppingProb :=
  div_pos prefs.uAll_sub_uMinus_pos prefs.uPlus_sub_uMinus_pos

theorem criticalStoppingProb_lt_one (prefs : SecretSharingPrefs) :
    prefs.criticalStoppingProb < 1 :=
  (div_lt_one prefs.uPlus_sub_uMinus_pos).mpr (by linarith [prefs.uAll_lt_uPlus])

/-- Withholding in a round with genuine-share probability `p` yields at most `uAll` (`p U⁺ +
(1 - p) U⁻ ≤ U`) if and only if `p ≤ criticalStoppingProb`. -/
theorem temptation_le_uAll_iff (prefs : SecretSharingPrefs) {p : ℝ} :
    p * prefs.uPlus + (1 - p) * prefs.uMinus ≤ prefs.uAll ↔
      p ≤ prefs.criticalStoppingProb := by
  rw [criticalStoppingProb, le_div_iff₀ prefs.uPlus_sub_uMinus_pos]
  constructor <;> intro h <;> linarith

/-- Withholding in a round with genuine-share probability `p` yields strictly less than `uAll`
(`p U⁺ + (1 - p) U⁻ < U`) if and only if `p < criticalStoppingProb`. -/
theorem temptation_lt_uAll_iff (prefs : SecretSharingPrefs) {p : ℝ} :
    p * prefs.uPlus + (1 - p) * prefs.uMinus < prefs.uAll ↔
      p < prefs.criticalStoppingProb := by
  rw [criticalStoppingProb, lt_div_iff₀ prefs.uPlus_sub_uMinus_pos]
  constructor <;> intro h <;> linarith

end SecretSharingPrefs

/-- Parameters of a **`t`-out-of-`n` rational secret-sharing reconstruction game** on a finite
player set `ι` (`2 ≤ t ≤ Fintype.card ι`), with specialization `ReconstructionGame.allOfAll` for
`n`-out-of-`n` sharing ([HalpernTeague2004]; [DodisRabin2007], Section 8.5.2). -/
structure ReconstructionGame (ι : Type*) [Fintype ι] where
  /-- Player preference parameters `U⁺ > U > U⁻`. -/
  prefs : SecretSharingPrefs
  /-- Reconstruction threshold `t` (minimum number of shares needed to recover the secret). -/
  threshold : ℕ
  /-- At least two shares are required, so no single party knows the secret a priori. -/
  two_le_threshold : 2 ≤ threshold
  /-- The grand coalition of all parties can reconstruct the secret. -/
  threshold_le_card : threshold ≤ Fintype.card ι

namespace ReconstructionGame

private theorem idowdsIter_bool_one_eq_singleton {ι : Type*} [DecidableEq ι]
    (G : PayoffGame ι (fun _ => Bool)) (kept : Bool)
    (hdom : ∀ i, G.WeaklyDominatesOn (fun _ => Set.univ) i kept (!kept)) :
    G.idowdsIter 1 = fun _ => {kept} := by
  funext i
  ext b
  by_cases hbk : b = kept
  · subst hbk
    simp only [PayoffGame.mem_idowdsIter_succ_iff, PayoffGame.idowdsIter_zero, Set.mem_univ,
      true_and, Set.mem_singleton_iff, iff_true]
    rintro ⟨a, _, ha⟩
    by_cases hak : a = b
    · subst hak
      exact G.not_weaklyDominatesOn_self _ i a ha
    · have hne : a = !b := by cases a <;> cases b <;> first | exact absurd rfl hak | rfl
      subst hne
      obtain ⟨hle, _⟩ := ha
      obtain ⟨_, s, _, hlt⟩ := hdom i
      exact (hle s fun _ => Set.mem_univ _).not_gt hlt
  · have hne : b = !kept := by cases b <;> cases kept <;> first | exact absurd rfl hbk | rfl
    subst hne
    simp only [PayoffGame.mem_idowdsIter_succ_iff, PayoffGame.idowdsIter_zero, Set.mem_univ,
      true_and, Set.mem_singleton_iff, Bool.not_eq_self, iff_false, not_not]
    exact ⟨kept, Set.mem_univ _, hdom i⟩

section Model

variable {ι : Type*} [Fintype ι]

/-- Canonical **`n`-out-of-`n` rational secret-sharing reconstruction game**, where every party's
share is required (`threshold = Fintype.card ι`). -/
def allOfAll (ι : Type*) [Fintype ι] (prefs : SecretSharingPrefs)
    (hcard : 2 ≤ Fintype.card ι) : ReconstructionGame ι where
  prefs := prefs
  threshold := Fintype.card ι
  two_le_threshold := hcard
  threshold_le_card := le_rfl

@[simp]
theorem allOfAll_prefs (prefs : SecretSharingPrefs) (hcard : 2 ≤ Fintype.card ι) :
    (allOfAll ι prefs hcard).prefs = prefs := by
  rfl

@[simp]
theorem allOfAll_threshold (prefs : SecretSharingPrefs) (hcard : 2 ≤ Fintype.card ι) :
    (allOfAll ι prefs hcard).threshold = Fintype.card ι := by
  rfl

/-- The underlying `(threshold, n)` monotone `AccessStructure` of `R`. -/
def accessStructure (R : ReconstructionGame ι) : AccessStructure ι :=
  AccessStructure.threshold ι R.threshold

@[simp]
theorem accessStructure_authorized_iff (R : ReconstructionGame ι) (s : Finset ι) :
    R.accessStructure.authorized s ↔ R.threshold ≤ s.card := by
  rfl

/-- When `R.threshold = Fintype.card ι` (`n`-out-of-`n`), `R.accessStructure` coincides with
`AccessStructure.all ι`. -/
theorem accessStructure_eq_all_of_threshold_eq_card (R : ReconstructionGame ι)
    (hfull : R.threshold = Fintype.card ι) :
    R.accessStructure = AccessStructure.all ι := by
  rw [accessStructure, hfull, AccessStructure.all_eq_threshold]

/-- The set of parties whose share is broadcast under Boolean action profile `s : ι → Bool`. -/
def broadcastSet (s : ι → Bool) : Finset ι :=
  Finset.univ.filter fun j => s j = true

@[simp]
theorem mem_broadcastSet_iff {s : ι → Bool} {j : ι} :
    j ∈ broadcastSet s ↔ s j = true := by
  simp [broadcastSet]

@[simp]
theorem broadcastSet_const_true : broadcastSet (fun _ : ι => true) = Finset.univ := by
  ext j
  simp [broadcastSet]

@[simp]
theorem broadcastSet_const_false : broadcastSet (fun _ : ι => false) = ∅ := by
  ext j
  simp [broadcastSet]

section Broadcast

variable [DecidableEq ι] (R : ReconstructionGame ι)

/-- The set of players who reconstruct the secret when `B : Finset ι` is the set of publicly
broadcast shares: player `j` holds `insert j B`, so `j` learns iff `threshold ≤ (insert j B).card`.
-/
def learnedSet (B : Finset ι) : Finset ι :=
  Finset.univ.filter fun j => R.threshold ≤ (insert j B).card

@[simp]
theorem mem_learnedSet_iff {B : Finset ι} {j : ι} :
    j ∈ R.learnedSet B ↔ R.threshold ≤ (insert j B).card := by
  simp [learnedSet]

/-- Compatibility with `AccessScheme`: for any secret-sharing scheme with `(t, n)` threshold access
structure, `j ∈ R.learnedSet B` iff `insert j B` is an authorized coalition. -/
theorem mem_learnedSet_iff_authorized {Secret Key : Type*} {Share : ι → Type*}
    (scheme : AccessScheme Secret Key ι Share)
    (hacc : scheme.access = R.accessStructure) (B : Finset ι) (j : ι) :
    j ∈ R.learnedSet B ↔ scheme.access.authorized (insert j B) := by
  rw [mem_learnedSet_iff, hacc, accessStructure_authorized_iff]

@[simp]
theorem learnedSet_empty : R.learnedSet ∅ = ∅ := by
  ext j
  simp only [mem_learnedSet_iff, Finset.insert_empty, Finset.card_singleton,
    Finset.notMem_empty, iff_false]
  linarith [R.two_le_threshold]

theorem learnedSet_eq_univ_of_threshold_le {B : Finset ι} (hB : R.threshold ≤ B.card) :
    R.learnedSet B = Finset.univ := by
  ext j
  simp only [mem_learnedSet_iff, Finset.mem_univ, iff_true]
  exact hB.trans (Finset.card_le_card (Finset.subset_insert j B))

@[simp]
theorem learnedSet_univ : R.learnedSet Finset.univ = Finset.univ :=
  R.learnedSet_eq_univ_of_threshold_le R.threshold_le_card

/-- **No-exclusivity lemma for broadcasters**: any player `i` who broadcasts its share (`i ∈ B`)
can never obtain `uPlus`; its payoff is `uAll` if `threshold ≤ B.card` and `uMinus` otherwise. -/
theorem outcomeUtility_of_mem_broadcast (B : Finset ι) {i : ι} (hi : i ∈ B) :
    R.prefs.outcomeUtility (R.learnedSet B) i =
      if R.threshold ≤ B.card then R.prefs.uAll else R.prefs.uMinus := by
  split_ifs with hB
  · rw [R.learnedSet_eq_univ_of_threshold_le hB, SecretSharingPrefs.outcomeUtility_univ]
  · refine R.prefs.outcomeUtility_of_not_mem ?_
    rw [mem_learnedSet_iff, Finset.insert_eq_of_mem hi]
    exact hB

/-- Exact comparison between withholding (`B := S`) and broadcasting (`B := insert i S`) when `S`
(`i ∉ S`) is the set of other players who broadcast:
- if `S.card + 1 < threshold`, both give `uMinus`;
- if `S.card + 1 = threshold` (`i` is pivotal), withholding gives `uPlus` while broadcasting gives
  `uAll`;
- if `threshold ≤ S.card`, both give `uAll`. -/
private theorem outcomeUtility_withhold_vs_broadcast {S : Finset ι} {i : ι} (hi : i ∉ S) :
    (S.card + 1 < R.threshold →
        R.prefs.outcomeUtility (R.learnedSet S) i = R.prefs.uMinus ∧
          R.prefs.outcomeUtility (R.learnedSet (insert i S)) i = R.prefs.uMinus) ∧
      (S.card + 1 = R.threshold →
        R.prefs.outcomeUtility (R.learnedSet S) i = R.prefs.uPlus ∧
          R.prefs.outcomeUtility (R.learnedSet (insert i S)) i = R.prefs.uAll) ∧
      (R.threshold ≤ S.card →
        R.prefs.outcomeUtility (R.learnedSet S) i = R.prefs.uAll ∧
          R.prefs.outcomeUtility (R.learnedSet (insert i S)) i = R.prefs.uAll) := by
  have hcard : (insert i S).card = S.card + 1 := Finset.card_insert_of_notMem hi
  refine ⟨fun hlt => ⟨?_, ?_⟩, fun heq => ⟨?_, ?_⟩, fun hge => ⟨?_, ?_⟩⟩
  · refine R.prefs.outcomeUtility_of_not_mem ?_
    rw [mem_learnedSet_iff, hcard]
    omega
  · rw [R.outcomeUtility_of_mem_broadcast (insert i S) (Finset.mem_insert_self i S), hcard]
    split_ifs with h
    · omega
    · rfl
  · have hpos : 0 < S.card := by linarith [R.two_le_threshold]
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    have himem : i ∈ R.learnedSet S := by
      rw [mem_learnedSet_iff, hcard]
      omega
    have hjnot : j ∉ R.learnedSet S := by
      rw [mem_learnedSet_iff, Finset.insert_eq_of_mem hj]
      omega
    have hne : R.learnedSet S ≠ Finset.univ := fun h => hjnot (h ▸ Finset.mem_univ j)
    exact R.prefs.outcomeUtility_of_mem_of_ne_univ himem hne
  · rw [R.outcomeUtility_of_mem_broadcast (insert i S) (Finset.mem_insert_self i S), hcard]
    split_ifs with h
    · rfl
    · omega
  · rw [R.learnedSet_eq_univ_of_threshold_le hge, SecretSharingPrefs.outcomeUtility_univ]
  · rw [R.learnedSet_eq_univ_of_threshold_le (hge.trans (by omega : S.card ≤ (insert i S).card)),
      SecretSharingPrefs.outcomeUtility_univ]

omit [DecidableEq ι] in
/-- Existence of a pivotal opponent subset `S ⊆ univ.erase i` of cardinality `threshold - 1`. -/
private theorem exists_pivotal_opponents (i : ι) :
    ∃ S : Finset ι, i ∉ S ∧ S.card + 1 = R.threshold := by
  classical
  have h1 := R.two_le_threshold
  have h2 := R.threshold_le_card
  have hle : R.threshold - 1 ≤ (Finset.univ.erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    omega
  obtain ⟨S, hSub, hScard⟩ := Finset.exists_subset_card_eq hle
  exact ⟨S, fun hiS => (Finset.notMem_erase i Finset.univ) (hSub hiS), by omega⟩

/-! ### Theorem 1: Halpern–Teague deterministic bounded-round impossibility -/

/-- The **simultaneous `(t, n)` share-broadcast game** ([HalpernTeague2004]; [DodisRabin2007],
Section 8.5.2(a)): each player chooses `true` (broadcast share) or `false` (withhold share). -/
def simultaneousGame : PayoffGame ι (fun _ => Bool) where
  payoff i s := R.prefs.outcomeUtility (R.learnedSet (broadcastSet s)) i

@[simp]
theorem simultaneousGame_payoff (i : ι) (s : ι → Bool) :
    R.simultaneousGame.payoff i s = R.prefs.outcomeUtility (R.learnedSet (broadcastSet s)) i := by
  rfl

private theorem broadcastSet_update_false (s : ι → Bool) (i : ι) :
    broadcastSet (Function.update s i false) = (broadcastSet s).erase i := by
  ext j
  rcases eq_or_ne j i with rfl | hne
  · simp [broadcastSet]
  · simp [broadcastSet, hne]

private theorem broadcastSet_update_true (s : ι → Bool) (i : ι) :
    broadcastSet (Function.update s i true) = insert i ((broadcastSet s).erase i) := by
  ext j
  rcases eq_or_ne j i with rfl | hne
  · simp [broadcastSet]
  · simp [broadcastSet, hne]

/-- **Halpern–Teague single-round / final-round weak dominance** ([HalpernTeague2004];
[DodisRabin2007], Section 8.5.2(a)): in any `(t, n)` reconstruction game (`2 ≤ t ≤ n`),
withholding (`false`) weakly dominates broadcasting (`true`) for every player. -/
theorem withhold_weaklyDominates_broadcast (i : ι) :
    R.simultaneousGame.WeaklyDominatesOn (fun _ => Set.univ) i false true := by
  refine ⟨fun s _ => ?_, ?_⟩
  · simp only [simultaneousGame, broadcastSet_update_false, broadcastSet_update_true]
    set S := (broadcastSet s).erase i
    have hi : i ∉ S := Finset.notMem_erase i _
    obtain ⟨hlt, heq, hge⟩ := R.outcomeUtility_withhold_vs_broadcast hi
    rcases lt_trichotomy (S.card + 1) R.threshold with h | h | h
    · rw [(hlt h).1, (hlt h).2]
    · rw [(heq h).1, (heq h).2]
      exact R.prefs.uAll_lt_uPlus.le
    · rw [(hge (by omega)).1, (hge (by omega)).2]
  · obtain ⟨S, hiS, hScard⟩ := R.exists_pivotal_opponents i
    refine ⟨fun j => decide (j ∈ S), fun _ => Set.mem_univ _, ?_⟩
    have hBS : (broadcastSet fun j => decide (j ∈ S)).erase i = S := by
      ext j
      simp only [Finset.mem_erase, ne_eq, mem_broadcastSet_iff, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun hj => ⟨fun hji => hiS (hji ▸ hj), hj⟩⟩
    simp only [simultaneousGame, broadcastSet_update_false, broadcastSet_update_true, hBS]
    obtain ⟨_, heq, _⟩ := R.outcomeUtility_withhold_vs_broadcast hiS
    obtain ⟨h0, h1⟩ := heq hScard
    rw [h0, h1]
    exact R.prefs.uAll_lt_uPlus

/-- **Halpern–Teague single-round `IDoWDS` collapse**: in simultaneous `(t, n)` share broadcast,
one round of `IDoWDS` eliminates `true` (`broadcast`) and leaves only `{false}` (`"never
broadcast"`), yielding `learnedSet = ∅` and utility `uMinus` for every player. -/
theorem idowdsIter_simultaneousGame_one :
    R.simultaneousGame.idowdsIter 1 = fun _ => {false} :=
  idowdsIter_bool_one_eq_singleton R.simultaneousGame false R.withhold_weaklyDominates_broadcast

omit [DecidableEq ι] in
/-- Active broadcasters at round `m` under cutoff profile `s : ι → Fin (T + 1)`: players choosing
cutoff strictly greater than `m`. -/
private def roundActive {T : ℕ} (s : ι → Fin (T + 1)) (m : ℕ) : Finset ι :=
  Finset.univ.filter fun j => m < (s j).val

/-- Recursive evaluation of a **`T`-round `(t, n)` gradual-release / ramp reconstruction protocol**
from round `m` onward: at round `m < T`, if at least `threshold` players broadcast (`roundActive s
m`), play advances to round `m + 1` (succeeding with `uAll` once all `T` rounds pass); otherwise
the protocol terminates at round `m`, revealing the round-`m` threshold reconstruction with
probability `q ⟨m, _⟩` and yielding `uMinus` with probability `1 - q ⟨m, _⟩`. -/
private def rampPayoffFrom (R : ReconstructionGame ι) {T : ℕ} (q : Fin T → ℝ)
    (s : ι → Fin (T + 1)) (i : ι) : ℕ → ℝ
  | m =>
    if hm : m < T then
      if R.threshold ≤ (roundActive s m).card then
        rampPayoffFrom R q s i (m + 1)
      else
        q ⟨m, hm⟩ * R.prefs.outcomeUtility (R.learnedSet (roundActive s m)) i +
          (1 - q ⟨m, hm⟩) * R.prefs.uMinus
    else
      R.prefs.uAll
termination_by m => T - m

/-- The **`T`-round `(t, n)` gradual-release / ramp reconstruction game** ([HalpernTeague2004];
[DodisRabin2007], Section 8.5.2(a)): player `i` chooses how many rounds `s i : Fin (T + 1)` to
broadcast honestly (`0` = never broadcast, `T` = broadcast in all `T` rounds), with round-`m`
reconstruction weight `q m`. -/
def gradualReleaseGame (R : ReconstructionGame ι) (T : ℕ) (q : Fin T → ℝ) :
    PayoffGame ι (fun _ => Fin (T + 1)) where
  payoff i s := rampPayoffFrom R q s i 0

/-- Canonical `T`-round uniform-ramp reconstruction game with strictly increasing round weights
`q m = (m + 1) / T`. -/
noncomputable def uniformRampGame (R : ReconstructionGame ι) (T : ℕ) :
    PayoffGame ι (fun _ => Fin (T + 1)) :=
  R.gradualReleaseGame T fun m => ((m.val : ℝ) + 1) / (T : ℝ)

/-- The **`T`-round known-final-round `(t, n)` reconstruction game** ([DodisRabin2007],
Section 8.5.2(a)): rounds `< T - 1` are pure dummy check rounds (`q m = 0`) and round `T - 1`
carries the genuine `(t, n)` secret shares (`q (T - 1) = 1`). -/
def knownHorizonGame (R : ReconstructionGame ι) (T : ℕ) :
    PayoffGame ι (fun _ => Fin (T + 1)) :=
  R.gradualReleaseGame T fun m => if m.val + 1 = T then 1 else 0

omit [DecidableEq ι] in
private theorem roundActive_congr_lt {T : ℕ} {s₁ s₂ : ι → Fin (T + 1)} {m : ℕ}
    (h : ∀ j, (m < (s₁ j).val ↔ m < (s₂ j).val)) :
    roundActive s₁ m = roundActive s₂ m := by
  ext j
  simp only [roundActive, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h j

private theorem rampPayoffFrom_lt_pos (R : ReconstructionGame ι) {T : ℕ} (q : Fin T → ℝ)
    (s : ι → Fin (T + 1)) (i : ι) {m : ℕ} (hm : m < T)
    (hcard : R.threshold ≤ (roundActive s m).card) :
    rampPayoffFrom R q s i m = rampPayoffFrom R q s i (m + 1) := by
  rw [rampPayoffFrom]
  split_ifs
  rfl

private theorem rampPayoffFrom_lt_neg (R : ReconstructionGame ι) {T : ℕ} (q : Fin T → ℝ)
    (s : ι → Fin (T + 1)) (i : ι) {m : ℕ} (hm : m < T)
    (hcard : ¬ R.threshold ≤ (roundActive s m).card) :
    rampPayoffFrom R q s i m =
      q ⟨m, hm⟩ * R.prefs.outcomeUtility (R.learnedSet (roundActive s m)) i +
        (1 - q ⟨m, hm⟩) * R.prefs.uMinus := by
  rw [rampPayoffFrom]
  split_ifs
  rfl

private theorem rampPayoffFrom_ge (R : ReconstructionGame ι) {T : ℕ} (q : Fin T → ℝ)
    (s : ι → Fin (T + 1)) (i : ι) {m : ℕ} (hm : ¬ m < T) :
    rampPayoffFrom R q s i m = R.prefs.uAll := by
  rw [rampPayoffFrom]
  split_ifs
  rfl

private theorem rampPayoffFrom_congr_before (R : ReconstructionGame ι) {T : ℕ} (q : Fin T → ℝ)
    {s₁ s₂ : ι → Fin (T + 1)} (i : ι) {M : ℕ}
    (hbefore : ∀ r < M, roundActive s₁ r = roundActive s₂ r) :
    ∀ r ≤ M, (∀ c < r, R.threshold ≤ (roundActive s₁ c).card) →
      (rampPayoffFrom R q s₁ i r = rampPayoffFrom R q s₂ i r ∨
        ((∀ c < M, R.threshold ≤ (roundActive s₁ c).card) ∧
          rampPayoffFrom R q s₁ i r = rampPayoffFrom R q s₁ i M ∧
          rampPayoffFrom R q s₂ i r = rampPayoffFrom R q s₂ i M)) := by
  intro r hr
  induction hdiff : M - r generalizing r with
  | zero =>
    have hrm : r = M := by omega
    subst hrm
    intro hprev
    exact Or.inr ⟨hprev, rfl, rfl⟩
  | succ d ih =>
    have hrM : r < M := by omega
    intro hprev
    by_cases hT : r < T
    · have hact : roundActive s₁ r = roundActive s₂ r := hbefore r hrM
      by_cases hcard : R.threshold ≤ (roundActive s₁ r).card
      · have hcard2 : R.threshold ≤ (roundActive s₂ r).card := hact ▸ hcard
        have hstep1 := rampPayoffFrom_lt_pos R q s₁ i hT hcard
        have hstep2 := rampPayoffFrom_lt_pos R q s₂ i hT hcard2
        have hprev' : ∀ c < r + 1, R.threshold ≤ (roundActive s₁ c).card := by
          intro c hc
          rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hlt | rfl
          · exact hprev c hlt
          · exact hcard
        rcases ih (r := r + 1) (by omega) (by omega) hprev' with heq | ⟨hall, he1, he2⟩
        · exact Or.inl (hstep1.trans (heq.trans hstep2.symm))
        · exact Or.inr ⟨hall, hstep1.trans he1, hstep2.trans he2⟩
      · have hcard2 : ¬ R.threshold ≤ (roundActive s₂ r).card := hact ▸ hcard
        refine Or.inl ?_
        rw [rampPayoffFrom_lt_neg R q s₁ i hT hcard,
          rampPayoffFrom_lt_neg R q s₂ i hT hcard2, hact]
    · refine Or.inl ?_
      rw [rampPayoffFrom_ge R q s₁ i hT, rampPayoffFrom_ge R q s₂ i hT]

private theorem rampPayoffFrom_zero_eq_at (R : ReconstructionGame ι) {T : ℕ} (q : Fin T → ℝ)
    (s : ι → Fin (T + 1)) (i : ι) {M : ℕ}
    (hall : ∀ c < M, R.threshold ≤ (roundActive s c).card) :
    rampPayoffFrom R q s i 0 = rampPayoffFrom R q s i M := by
  induction M with
  | zero => rfl
  | succ M ih =>
    have hprev : ∀ c < M, R.threshold ≤ (roundActive s c).card :=
      fun c hc => hall c (Nat.lt_succ_of_lt hc)
    rw [ih hprev]
    by_cases hMT : M < T
    · exact rampPayoffFrom_lt_pos R q s i hMT (hall M (Nat.lt_succ_self M))
    · rw [rampPayoffFrom_ge R q s i hMT, rampPayoffFrom_ge R q s i (by omega)]

private theorem rampPayoffFrom_eq_or_reach (R : ReconstructionGame ι) {T : ℕ} (q : Fin T → ℝ)
    {s₁ s₂ : ι → Fin (T + 1)} (i : ι) {M : ℕ}
    (hbefore : ∀ r < M, roundActive s₁ r = roundActive s₂ r) :
    rampPayoffFrom R q s₁ i 0 = rampPayoffFrom R q s₂ i 0 ∨
      ((∀ c < M, R.threshold ≤ (roundActive s₁ c).card) ∧
        rampPayoffFrom R q s₁ i 0 = rampPayoffFrom R q s₁ i M ∧
        rampPayoffFrom R q s₂ i 0 = rampPayoffFrom R q s₂ i M) :=
  rampPayoffFrom_congr_before R q i hbefore 0 (Nat.zero_le M)
    (fun _ hc => absurd hc (Nat.not_lt_zero _))

/-- A round in which nobody broadcasts ends with `uMinus` before the horizon and `uAll` after it. -/
private theorem rampPayoffFrom_of_roundActive_eq_empty (R : ReconstructionGame ι) {T : ℕ}
    (q : Fin T → ℝ) {s : ι → Fin (T + 1)} (i : ι) {r : ℕ} (hr : roundActive s r = ∅) :
    rampPayoffFrom R q s i r = if r < T then R.prefs.uMinus else R.prefs.uAll := by
  split_ifs with hrT
  · have hc : ¬ R.threshold ≤ (roundActive s r).card := by
      rw [hr, Finset.card_empty]
      linarith [R.two_le_threshold]
    rw [rampPayoffFrom_lt_neg R q s i hrT hc, hr, learnedSet_empty,
      SecretSharingPrefs.outcomeUtility_empty]
    ring
  · exact rampPayoffFrom_ge R q s i hrT

/-- One-round comparison at round `m < T`: if withholding leaves the active set `S` (`i ∉ S`) and
participating leaves `insert i S`, then participating is no better, provided the continuation after
a pivotal participation is at most the pivotal withholding payoff and continuations compare when `i`
is not needed. -/
private theorem rampPayoffFrom_insert_le (R : ReconstructionGame ι) {T : ℕ} (q : Fin T → ℝ)
    {s₀ s₁ : ι → Fin (T + 1)} (i : ι) {m : ℕ} (hm : m < T) {S : Finset ι} (hiS : i ∉ S)
    (hact0 : roundActive s₀ m = S) (hact1 : roundActive s₁ m = insert i S)
    (hpiv : rampPayoffFrom R q s₁ i (m + 1) ≤
      q ⟨m, hm⟩ * R.prefs.uPlus + (1 - q ⟨m, hm⟩) * R.prefs.uMinus)
    (hcont : R.threshold ≤ S.card →
      rampPayoffFrom R q s₁ i (m + 1) ≤ rampPayoffFrom R q s₀ i (m + 1)) :
    rampPayoffFrom R q s₁ i m ≤ rampPayoffFrom R q s₀ i m := by
  have hcard1 : (roundActive s₁ m).card = S.card + 1 := by
    rw [hact1, Finset.card_insert_of_notMem hiS]
  obtain ⟨hlt, heq, hge⟩ := R.outcomeUtility_withhold_vs_broadcast hiS
  rcases lt_trichotomy (S.card + 1) R.threshold with h | h | h
  · rw [rampPayoffFrom_lt_neg R q s₀ i hm (by rw [hact0]; omega), hact0, (hlt h).1,
      rampPayoffFrom_lt_neg R q s₁ i hm (by omega), hact1, (hlt h).2]
  · rw [rampPayoffFrom_lt_neg R q s₀ i hm (by rw [hact0]; omega), hact0, (heq h).1,
      rampPayoffFrom_lt_pos R q s₁ i hm (by omega)]
    exact hpiv
  · rw [rampPayoffFrom_lt_pos R q s₀ i hm (by rw [hact0]; omega),
      rampPayoffFrom_lt_pos R q s₁ i hm (by omega)]
    exact hcont (by omega)

private theorem roundActive_update_of_le {T : ℕ} (s : ι → Fin (T + 1)) (i : ι)
    {a : Fin (T + 1)} {m : ℕ} (ha : a.val ≤ m) :
    roundActive (Function.update s i a) m = (roundActive s m).erase i := by
  ext j
  rcases eq_or_ne j i with rfl | hne
  · simp [roundActive, Nat.not_lt.mpr ha]
  · simp [roundActive, hne]

private theorem roundActive_update_of_lt {T : ℕ} (s : ι → Fin (T + 1)) (i : ι)
    {a : Fin (T + 1)} {m : ℕ} (ha : m < a.val) :
    roundActive (Function.update s i a) m = insert i ((roundActive s m).erase i) := by
  ext j
  rcases eq_or_ne j i with rfl | hne
  · simp [roundActive, ha]
  · simp [roundActive, hne]

/-- Construct an opponent cutoff profile where every `j ∈ S` plays `val` and all others play `0`,
overwriting `i` later via `Function.update`. -/
private def pivotalCutoffProfile {T : ℕ} (S : Finset ι) (val : Fin (T + 1)) :
    ι → Fin (T + 1) :=
  fun j => if j ∈ S then val else 0

private theorem roundActive_update_pivotal_lt {T : ℕ} {S : Finset ι} {i : ι}
    {val a : Fin (T + 1)} {r : ℕ} (hr_a : r < a.val) (hr_val : r < val.val) :
    roundActive (Function.update (pivotalCutoffProfile S val) i a) r = insert i S := by
  ext j
  rcases eq_or_ne j i with rfl | hne
  · simp [roundActive, hr_a]
  · simp only [roundActive, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.update_of_ne hne, pivotalCutoffProfile, Finset.mem_insert, hne, false_or]
    split_ifs with hj <;> simp [hj, hr_val]

private theorem roundActive_update_pivotal_self {T : ℕ} {S : Finset ι} {i : ι} (hi : i ∉ S)
    {val a : Fin (T + 1)} (hr_val : a.val < val.val) :
    roundActive (Function.update (pivotalCutoffProfile S val) i a) a.val = S := by
  ext j
  rcases eq_or_ne j i with rfl | hne
  · simp [roundActive, hi]
  · simp only [roundActive, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.update_of_ne hne, pivotalCutoffProfile]
    split_ifs with hj <;> simp [hj, hr_val]

private theorem rampPayoffFrom_pivotal_withhold (R : ReconstructionGame ι) {T : ℕ}
    (q : Fin T → ℝ) {S : Finset ι} {i : ι} (hiS : i ∉ S) (hScard : S.card + 1 = R.threshold)
    {val a : Fin (T + 1)} (ha : a.val < T) (hval : a.val < val.val) :
    rampPayoffFrom R q (Function.update (pivotalCutoffProfile S val) i a) i 0 =
      q ⟨a.val, ha⟩ * R.prefs.uPlus + (1 - q ⟨a.val, ha⟩) * R.prefs.uMinus := by
  have hall : ∀ c < a.val, R.threshold ≤
      (roundActive (Function.update (pivotalCutoffProfile S val) i a) c).card := fun c hc => by
    rw [roundActive_update_pivotal_lt hc (hc.trans hval), Finset.card_insert_of_notMem hiS]
    omega
  have hact := roundActive_update_pivotal_self hiS (a := a) (val := val) hval
  obtain ⟨_, heq, _⟩ := R.outcomeUtility_withhold_vs_broadcast hiS
  rw [rampPayoffFrom_zero_eq_at R q _ i hall,
    rampPayoffFrom_lt_neg R q _ i ha (by rw [hact]; omega), hact, (heq hScard).1]

private theorem rampPayoffFrom_pivotal_self (R : ReconstructionGame ι) {T : ℕ}
    (q : Fin T → ℝ) {S : Finset ι} {i : ι} (hiS : i ∉ S) (hScard : S.card + 1 = R.threshold)
    (val : Fin (T + 1)) :
    rampPayoffFrom R q (Function.update (pivotalCutoffProfile S val) i val) i 0 =
      if val.val < T then R.prefs.uMinus else R.prefs.uAll := by
  have hall : ∀ c < val.val, R.threshold ≤
      (roundActive (Function.update (pivotalCutoffProfile S val) i val) c).card := fun c hc => by
    rw [roundActive_update_pivotal_lt hc hc, Finset.card_insert_of_notMem hiS]
    omega
  have hemp : roundActive (Function.update (pivotalCutoffProfile S val) i val) val.val = ∅ := by
    ext j
    rcases eq_or_ne j i with rfl | hne
    · simp [roundActive]
    · simp only [roundActive, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.update_of_ne hne, pivotalCutoffProfile, Finset.notMem_empty, iff_false, not_lt]
      split_ifs <;> simp
  rw [rampPayoffFrom_zero_eq_at R q _ i hall, rampPayoffFrom_of_roundActive_eq_empty R q i hemp]

/-- **Backward-induction dominance for `gradualReleaseGame`**: whenever `q` has positive, strictly
increasing round weights ending at `1`, the `T`-round `(t, n)` gradual-release game satisfies
`PayoffGame.HasBackwardInductionDominance`. -/
theorem hasBackwardInductionDominance_gradualReleaseGame (R : ReconstructionGame ι) {T : ℕ}
    {q : Fin T → ℝ} (hq_pos : ∀ m : Fin T, 0 < q m) (hq_mono : StrictMono q)
    (hq_last : ∀ hT : 0 < T, q ⟨T - 1, Nat.sub_lt hT zero_lt_one⟩ = 1) :
    (R.gradualReleaseGame T q).HasBackwardInductionDominance := by
  intro m hm
  set Rset : ∀ _ : ι, Set (Fin (T + 1)) := fun _ => { r | r.val ≤ m + 1 }
  let mFin : Fin (T + 1) := ⟨m, by omega⟩
  let mSuccFin : Fin (T + 1) := ⟨m + 1, by omega⟩
  have hpiv : ∀ m' (hm' : m' < T), (if m' + 1 < T then R.prefs.uMinus else R.prefs.uAll) <
      q ⟨m', hm'⟩ * R.prefs.uPlus + (1 - q ⟨m', hm'⟩) * R.prefs.uMinus := by
    intro m' hm'
    split_ifs with hm1
    · nlinarith [R.prefs.uMinus_lt_uPlus, hq_pos ⟨m', hm'⟩]
    · have hT_lt : T - 1 < T := Nat.sub_lt (by omega) zero_lt_one
      have hm_eq : ⟨m', hm'⟩ = (⟨T - 1, hT_lt⟩ : Fin T) := Fin.ext (by dsimp; omega)
      rw [hm_eq, hq_last (by omega)]
      linarith [R.prefs.uAll_lt_uPlus]
  refine ⟨fun i => ⟨fun s hs => ?_, ?_⟩, fun i r hr => ?_⟩
  · -- Part 1a: `m` is at least as good as `m + 1` against all `s ∈ Rset`.
    set s₀ := Function.update s i mFin
    set s₁ := Function.update s i mSuccFin
    have hbefore : ∀ c < m, roundActive s₀ c = roundActive s₁ c := fun c hc =>
      roundActive_congr_lt fun j => by
        rcases eq_or_ne j i with rfl | hne
        · simp only [s₀, s₁, Function.update_self, mFin, mSuccFin]; omega
        · simp [s₀, s₁, Function.update_of_ne hne]
    rcases rampPayoffFrom_eq_or_reach R q i hbefore with heq | ⟨_, he0, he1⟩
    · exact heq.ge
    · unfold gradualReleaseGame
      dsimp only
      rw [he0, he1]
      have hnext : ∀ a : Fin (T + 1), a.val ≤ m + 1 →
          rampPayoffFrom R q (Function.update s i a) i (m + 1) =
            if m + 1 < T then R.prefs.uMinus else R.prefs.uAll := fun a ha => by
        refine rampPayoffFrom_of_roundActive_eq_empty R q i ?_
        ext j
        simp only [roundActive, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false, not_lt]
        rcases eq_or_ne j i with rfl | hne
        · simpa using ha
        · simpa [Function.update_of_ne hne, Rset] using hs j
      exact rampPayoffFrom_insert_le R q i hm (Finset.notMem_erase i _)
        (roundActive_update_of_le s i le_rfl)
        (roundActive_update_of_lt s i (Nat.lt_succ_self m))
        ((hnext mSuccFin le_rfl).trans_le (hpiv m hm).le)
        fun _ => (hnext mSuccFin le_rfl).trans_le (hnext mFin (Nat.le_succ m)).ge
  · -- Part 1b: Strict inequality witness for `m` vs `m + 1` in `Rset`.
    obtain ⟨S, hiS, hScard⟩ := R.exists_pivotal_opponents i
    refine ⟨pivotalCutoffProfile S mSuccFin, fun j => ?_, ?_⟩
    · simp only [pivotalCutoffProfile, Rset, Set.mem_ofPred_eq]
      split_ifs <;> simp [mSuccFin]
    · unfold gradualReleaseGame
      dsimp only
      rw [rampPayoffFrom_pivotal_withhold R q hiS hScard (a := mFin) hm (Nat.lt_succ_self m),
        rampPayoffFrom_pivotal_self R q hiS hScard mSuccFin]
      exact hpiv m hm
  · -- Part 2: No `r ≤ m` is weakly dominated on `Rset`.
    rintro ⟨r', hr'_mem, hdom⟩
    have hr'le : r'.val ≤ m + 1 := hr'_mem
    obtain ⟨S, hiS, hScard⟩ := R.exists_pivotal_opponents i
    have hrT : r.val < T := by omega
    let rSucc : Fin (T + 1) := ⟨r.val + 1, by omega⟩
    let s := pivotalCutoffProfile S rSucc
    have hs_mem : ∀ j, s j ∈ Rset j := fun j => by
      simp only [s, pivotalCutoffProfile, Rset, Set.mem_ofPred_eq]
      split_ifs
      · dsimp [rSucc]; omega
      · simp
    have hcmp := hdom.1 s hs_mem
    unfold gradualReleaseGame at hcmp
    dsimp only at hcmp
    rw [rampPayoffFrom_pivotal_withhold R q hiS hScard (a := r) hrT (Nat.lt_succ_self r.val)]
      at hcmp
    rcases lt_trichotomy r'.val r.val with hlt_r' | heq_r' | hgt_r'
    · have hr'T : r'.val < T := by omega
      rw [rampPayoffFrom_pivotal_withhold R q hiS hScard (a := r') hr'T
        (by dsimp [rSucc]; omega)] at hcmp
      have hq_lt : q ⟨r'.val, hr'T⟩ < q ⟨r.val, hrT⟩ := hq_mono hlt_r'
      nlinarith [R.prefs.uMinus_lt_uPlus]
    · obtain rfl := Fin.ext heq_r'
      exact (R.gradualReleaseGame T q).not_weaklyDominatesOn_self Rset i r' hdom
    · have hall_r' : ∀ c < r.val + 1,
          R.threshold ≤ (roundActive (Function.update s i r') c).card := fun c hc => by
        rw [roundActive_update_pivotal_lt (a := r') (val := rSucc) (by omega) hc,
          Finset.card_insert_of_notMem hiS]
        omega
      have hpay_r' : rampPayoffFrom R q (Function.update s i r') i 0 ≤
          if r.val + 1 < T then R.prefs.uMinus else R.prefs.uAll := by
        rw [rampPayoffFrom_zero_eq_at R q _ i hall_r']
        split_ifs with hr1T
        · have hsub : roundActive (Function.update s i r') (r.val + 1) ⊆ {i} := fun j hj => by
            rcases eq_or_ne j i with rfl | hne
            · exact Finset.mem_singleton_self j
            · simp only [roundActive, Finset.mem_filter, Finset.mem_univ, true_and,
                Function.update_of_ne hne, s, pivotalCutoffProfile] at hj
              split_ifs at hj <;> dsimp [rSucc] at hj <;> omega
          have hle1 := (Finset.card_le_card (Finset.insert_subset (Finset.mem_singleton_self i)
            hsub)).trans (Finset.card_singleton i).le
          have hle0 := Finset.card_le_card (Finset.subset_insert i
            (roundActive (Function.update s i r') (r.val + 1)))
          have h2 := R.two_le_threshold
          rw [rampPayoffFrom_lt_neg R q _ i hr1T (by omega),
            R.prefs.outcomeUtility_of_not_mem (by rw [mem_learnedSet_iff]; omega)]
          linarith
        · rw [rampPayoffFrom_ge R q _ i hr1T]
      linarith [hpiv r.val hrT]

/-- **Halpern–Teague bounded-round `IDoWDS` impossibility (`T`-round gradual release)**
([HalpernTeague2004]; [DodisRabin2007], Section 8.5.2(a)): in any `T`-round `(t, n)`
gradual-release reconstruction game with positive strictly increasing round weights ending at `1`,
`T` rounds of `IDoWDS` eliminate every positive participation horizon and leave only `{0}`
(`"never broadcast"`). -/
theorem idowdsIter_gradualReleaseGame (R : ReconstructionGame ι) {T : ℕ} {q : Fin T → ℝ}
    (hq_pos : ∀ m : Fin T, 0 < q m) (hq_mono : StrictMono q)
    (hq_last : ∀ hT : 0 < T, q ⟨T - 1, Nat.sub_lt hT zero_lt_one⟩ = 1) :
    (R.gradualReleaseGame T q).idowdsIter T = fun _ => {0} :=
  PayoffGame.idowdsIter_eq_singleton_zero
    (R.hasBackwardInductionDominance_gradualReleaseGame hq_pos hq_mono hq_last)

/-- **Backward-induction dominance for `uniformRampGame`**: for every `T : ℕ` and every `(t, n)`
reconstruction game (`2 ≤ t ≤ n`), `R.uniformRampGame T` satisfies
`PayoffGame.HasBackwardInductionDominance`. -/
theorem hasBackwardInductionDominance_uniformRampGame (R : ReconstructionGame ι) (T : ℕ) :
    (R.uniformRampGame T).HasBackwardInductionDominance := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · intro m hm
    exact absurd hm (Nat.not_lt_zero m)
  · refine R.hasBackwardInductionDominance_gradualReleaseGame (fun m => ?_) (fun a b hab => ?_)
      (fun _ => ?_)
    · positivity
    · exact div_lt_div_of_pos_right
        (by linarith [show (a.val : ℝ) < (b.val : ℝ) from Nat.cast_lt.mpr hab])
        (Nat.cast_pos.mpr hT)
    · have hcast : ((T - 1 : ℕ) : ℝ) + 1 = (T : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hT
      rw [hcast]
      exact div_self (Nat.cast_ne_zero.mpr hT.ne')

/-- **Unconditional `T`-round `IDoWDS` collapse for `uniformRampGame`**: for every `T : ℕ` and
every `(t, n)` reconstruction game (`2 ≤ t ≤ n`), `(R.uniformRampGame T).idowdsIter T = fun _ =>
{0}`. -/
theorem idowdsIter_uniformRampGame (R : ReconstructionGame ι) (T : ℕ) :
    (R.uniformRampGame T).idowdsIter T = fun _ => {0} :=
  PayoffGame.idowdsIter_eq_singleton_zero (R.hasBackwardInductionDominance_uniformRampGame T)

/-- In the **`T`-round known-final-round protocol** (`1 ≤ T`, pure dummy rounds `< T - 1` and
genuine round `T - 1`), withholding in the final round (`T - 1`) weakly dominates honest
participation through round `T`, so one round of `IDoWDS` eliminates `Fin.last T` and every
surviving profile gives every player `uMinus` (failure to learn the secret). -/
theorem payoff_knownHorizonGame_eq_uMinus_of_mem_idowdsIter_one (R : ReconstructionGame ι)
    {T : ℕ} (hT : 1 ≤ T)
    {s : ι → Fin (T + 1)} (hs : ∀ j, s j ∈ (R.knownHorizonGame T).idowdsIter 1 j) (i : ι) :
    (R.knownHorizonGame T).payoff i s = R.prefs.uMinus := by
  let qK : Fin T → ℝ := fun m => if m.val + 1 = T then 1 else 0
  have hm : T - 1 < T := by omega
  have hq1 : qK ⟨T - 1, hm⟩ = 1 := ite_eq_left (by dsimp; omega)
  have hnot_last : ∀ j, (s j).val ≤ T - 1 := by
    intro j
    have hmem : ¬ (R.knownHorizonGame T).IsWeaklyDominatedOn
        ((R.knownHorizonGame T).idowdsIter 0) j (s j) :=
      ((PayoffGame.mem_idowdsIter_succ_iff (G := R.knownHorizonGame T) (k := 0)).mp (hs j)).2
    by_contra hgt
    have hj_last : s j = Fin.last T := by
      ext; dsimp [Fin.last]; omega
    rw [hj_last] at hmem
    refine hmem ⟨⟨T - 1, by omega⟩, by rw [PayoffGame.idowdsIter_zero]; exact Set.mem_univ _,
      ⟨fun s' _ => ?_, ?_⟩⟩
    · set s₀ := Function.update s' j ⟨T - 1, by omega⟩
      set s₁ := Function.update s' j (Fin.last T)
      have hbefore : ∀ c < T - 1, roundActive s₀ c = roundActive s₁ c := fun c hc =>
        roundActive_congr_lt fun l => by
          rcases eq_or_ne l j with rfl | hne
          · simp only [s₀, s₁, Function.update_self, Fin.last]; omega
          · simp [s₀, s₁, Function.update_of_ne hne]
      rcases rampPayoffFrom_eq_or_reach R qK j hbefore with heq | ⟨_, he0, he1⟩
      · exact heq.ge
      · unfold knownHorizonGame gradualReleaseGame
        dsimp only
        change rampPayoffFrom R qK s₁ j 0 ≤ rampPayoffFrom R qK s₀ j 0
        rw [he0, he1]
        have hlast_false : ¬ (T - 1 + 1 < T) := by omega
        refine rampPayoffFrom_insert_le R qK j hm (Finset.notMem_erase j _)
          (roundActive_update_of_le s' j le_rfl)
          (roundActive_update_of_lt s' j hm) ?_ fun _ => ?_
        · rw [rampPayoffFrom_ge R qK s₁ j hlast_false, hq1]
          linarith [R.prefs.uAll_lt_uPlus]
        · rw [rampPayoffFrom_ge R qK s₁ j hlast_false, rampPayoffFrom_ge R qK s₀ j hlast_false]
    · obtain ⟨S, hjS, hScard⟩ := R.exists_pivotal_opponents j
      refine ⟨pivotalCutoffProfile S (Fin.last T), ?_, ?_⟩
      · intro _
        simp [PayoffGame.idowdsIter_zero]
      · unfold knownHorizonGame gradualReleaseGame
        dsimp only
        change rampPayoffFrom R qK _ j 0 < rampPayoffFrom R qK _ j 0
        rw [rampPayoffFrom_pivotal_withhold R qK hjS hScard (a := ⟨T - 1, by omega⟩) hm hm,
          rampPayoffFrom_pivotal_self R qK hjS hScard (Fin.last T), hq1,
          ite_eq_right (by simp [Fin.last])]
        linarith [R.prefs.uAll_lt_uPlus]
  unfold knownHorizonGame gradualReleaseGame
  dsimp only
  change rampPayoffFrom R qK s i 0 = R.prefs.uMinus
  suffices ∀ r ≤ T - 1, rampPayoffFrom R qK s i r = R.prefs.uMinus from this 0 (Nat.zero_le _)
  intro r hr
  induction hdiff : (T - 1) - r generalizing r with
  | zero =>
    obtain rfl : r = T - 1 := by omega
    have hempty : roundActive s (T - 1) = ∅ := by
      ext j
      simp [roundActive, hnot_last j]
    rw [rampPayoffFrom_of_roundActive_eq_empty R qK i hempty, ite_eq_left hm]
  | succ d ih =>
    have hrT : r < T := by omega
    by_cases hcard : R.threshold ≤ (roundActive s r).card
    · rw [rampPayoffFrom_lt_pos R qK s i hrT hcard]
      exact ih (r + 1) (by omega) (by omega)
    · rw [rampPayoffFrom_lt_neg R qK s i hrT hcard,
        show qK ⟨r, hrT⟩ = 0 from ite_eq_right (by dsimp; omega)]
      ring

/-! ### Stage analysis of the randomized geometric-termination protocol -/

/-- Single-stage game at an active round of the **randomized geometric-termination protocol** with
stopping parameter `p ∈ (0, 1)` ([HalpernTeague2004]; [AbrahamDolevGonenHalpern2006];
[DodisRabin2007], Section 8.5.2(b)): if every player broadcasts (`∀ j, s j = true`), play either
reconstructs the secret (`p`) or continues to an identical subgame with equilibrium value `uAll`
(`1 - p`), giving `uAll`; if any player withholds, the round yields `learnedSet (broadcastSet s)`
when genuine (`p`) and triggers grim-abort `uMinus` when dummy (`1 - p`). -/
def geometricStageGame (p : ℝ) : PayoffGame ι (fun _ => Bool) where
  payoff i s :=
    if ∀ j, s j = true then
      R.prefs.uAll
    else
      p * R.prefs.outcomeUtility (R.learnedSet (broadcastSet s)) i +
        (1 - p) * R.prefs.uMinus

@[simp]
theorem geometricStageGame_payoff (p : ℝ) (i : ι) (s : ι → Bool) :
    (R.geometricStageGame p).payoff i s =
      if ∀ j, s j = true then
        R.prefs.uAll
      else
        p * R.prefs.outcomeUtility (R.learnedSet (broadcastSet s)) i +
          (1 - p) * R.prefs.uMinus := by
  rfl

private theorem geometricStageGame_update_false_le (p : ℝ) (hp0 : 0 ≤ p) (i : ι) :
    (R.geometricStageGame p).payoff i (Function.update (fun _ : ι => true) i false) ≤
      p * R.prefs.uPlus + (1 - p) * R.prefs.uMinus := by
  have hnot_all : ¬ ∀ j, Function.update (fun _ : ι => true) i false j = true :=
    fun h => Bool.false_ne_true (by simpa using h i)
  rw [geometricStageGame_payoff]
  split_ifs
  have hle : R.prefs.outcomeUtility
      (R.learnedSet (broadcastSet (Function.update (fun _ : ι => true) i false))) i ≤
      R.prefs.uPlus :=
    R.prefs.outcomeUtility_le_uPlus _ i
  nlinarith

/-- For `0 ≤ p ≤ criticalStoppingProb`, honest simultaneous broadcast (`fun _ => true`) is a
**pure Nash equilibrium** of `R.geometricStageGame p` for every `(t, n)` reconstruction game
(`2 ≤ t ≤ n`). -/
theorem honest_isPureNash_geometricStageGame {p : ℝ} (hp0 : 0 ≤ p)
    (hp : p ≤ R.prefs.criticalStoppingProb) :
    (R.geometricStageGame p).IsPureNash (fun _ => true) := by
  have htrue : ∀ i, (R.geometricStageGame p).payoff i (fun _ => true) = R.prefs.uAll := fun i => by
    simp [geometricStageGame_payoff]
  intro i b
  cases b
  · rw [htrue i]
    exact (R.geometricStageGame_update_false_le p hp0 i).trans
      (R.prefs.temptation_le_uAll_iff.mpr hp)
  · simp [Function.update_eq_self]

/-- For `0 ≤ p < criticalStoppingProb`, honest simultaneous broadcast (`fun _ => true`) is a
**strict pure Nash equilibrium** of `R.geometricStageGame p` for every `(t, n)` reconstruction
game (`2 ≤ t ≤ n`). -/
theorem honest_isStrictPureNash_geometricStageGame {p : ℝ} (hp0 : 0 ≤ p)
    (hp : p < R.prefs.criticalStoppingProb) :
    (R.geometricStageGame p).IsStrictPureNash (fun _ => true) := by
  have htrue : ∀ i, (R.geometricStageGame p).payoff i (fun _ => true) = R.prefs.uAll := fun i => by
    simp [geometricStageGame_payoff]
  intro i b hb
  cases b
  · rw [htrue i]
    exact (R.geometricStageGame_update_false_le p hp0 i).trans_lt
      (R.prefs.temptation_lt_uAll_iff.mpr hp)
  · exact absurd rfl hb

/-- **Exact stage Nash characterization for `n`-out-of-`n`**: when `R.threshold = Fintype.card ι`
and `0 ≤ p`, honest simultaneous broadcast is a pure Nash equilibrium of `R.geometricStageGame p`
if and only if `p ≤ criticalStoppingProb`. -/
theorem honest_isPureNash_geometricStageGame_iff {p : ℝ} (hp0 : 0 ≤ p)
    (hfull : R.threshold = Fintype.card ι) [Nonempty ι] :
    (R.geometricStageGame p).IsPureNash (fun _ => true) ↔
      p ≤ R.prefs.criticalStoppingProb := by
  refine ⟨fun h => ?_, R.honest_isPureNash_geometricStageGame hp0⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hi := h i false
  have hall_t : ∀ _ : ι, true = true := fun _ => rfl
  have hnot_all : ¬ ∀ j, Function.update (fun _ : ι => true) i false j = true :=
    fun hall => Bool.false_ne_true (by simpa using hall i)
  have hB : broadcastSet (Function.update (fun _ : ι => true) i false) = Finset.univ.erase i := by
    rw [broadcastSet_update_false, broadcastSet_const_true]
  have hiS : i ∉ Finset.univ.erase i := Finset.notMem_erase i _
  have hcard : (Finset.univ.erase i).card + 1 = R.threshold := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, hfull]
    have := R.two_le_threshold
    omega
  obtain ⟨_, heq, _⟩ := R.outcomeUtility_withhold_vs_broadcast hiS
  obtain ⟨hu0, _⟩ := heq hcard
  dsimp only [geometricStageGame] at hi
  split_ifs at hi
  rw [hB, hu0] at hi
  exact R.prefs.temptation_le_uAll_iff.mp hi

/-- **Stage weak dominance for `n`-out-of-`n`**: when `R.threshold = Fintype.card ι` and `0 ≤ p <
criticalStoppingProb`, honest broadcast (`true`) weakly dominates withholding (`false`) in
`R.geometricStageGame p` (reversing the deterministic `p = 1` dominance direction). -/
theorem broadcast_weaklyDominates_withhold_geometricStageGame {p : ℝ} (hp0 : 0 ≤ p)
    (hp : p < R.prefs.criticalStoppingProb) (hfull : R.threshold = Fintype.card ι) (i : ι) :
    (R.geometricStageGame p).WeaklyDominatesOn (fun _ => Set.univ) i true false := by
  refine ⟨fun s _ => ?_, ⟨fun _ => true, fun _ => Set.mem_univ _, ?_⟩⟩
  · by_cases hall : ∀ j ≠ i, s j = true
    · have hall_true : ∀ j, Function.update s i true j = true := fun j => by
        rcases eq_or_ne j i with rfl | hne
        · simp
        · simp [Function.update_of_ne hne, hall j hne]
      have hnot_all : ¬ ∀ j, Function.update s i false j = true :=
        fun h => Bool.false_ne_true (by simpa using h i)
      dsimp only [geometricStageGame]
      split_ifs
      have hle := R.prefs.outcomeUtility_le_uPlus
        (R.learnedSet (broadcastSet (Function.update s i false))) i
      nlinarith [R.prefs.temptation_lt_uAll_iff.mpr hp]
    · push Not at hall
      obtain ⟨j, hji, hjf⟩ := hall
      have hj_false : s j = false := Bool.eq_false_iff.mpr hjf
      have hpay : ∀ b : Bool, (R.geometricStageGame p).payoff i (Function.update s i b) =
          p * R.prefs.uMinus + (1 - p) * R.prefs.uMinus := fun b => by
        have hnot_b : ¬ ∀ l, Function.update s i b l = true := fun h => by
          simpa [Function.update_of_ne hji, hj_false] using h j
        have hsub : insert i (broadcastSet (Function.update s i b)) ⊆ Finset.univ.erase j :=
          Finset.subset_erase.mpr ⟨Finset.subset_univ _, by simp [hji, hj_false]⟩
        have hle := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ] at hle
        have := R.two_le_threshold
        rw [geometricStageGame_payoff, ite_eq_right hnot_b,
          R.prefs.outcomeUtility_of_not_mem (by rw [mem_learnedSet_iff]; omega)]
      rw [hpay true, hpay false]
  · simpa only [Function.update_eq_self] using
      R.honest_isStrictPureNash_geometricStageGame hp0 hp i false Bool.false_ne_true

/-- **Stage `IDoWDS` survival for `n`-out-of-`n`**: when `0 ≤ p < criticalStoppingProb`, one round
of `IDoWDS` on `R.geometricStageGame p` eliminates withholding and leaves only `{true}`
(`"honest broadcast"`, matching [DodisRabin2007], Theorem 8.9's one-shot stage argument; the
multi-round `k < n/2` and `k < n/3` variants are outside this module's scope). -/
theorem idowdsIter_geometricStageGame_one {p : ℝ} (hp0 : 0 ≤ p)
    (hp : p < R.prefs.criticalStoppingProb) (hfull : R.threshold = Fintype.card ι) :
    (R.geometricStageGame p).idowdsIter 1 = fun _ => {true} :=
  idowdsIter_bool_one_eq_singleton (R.geometricStageGame p) true
    (R.broadcast_weaklyDominates_withhold_geometricStageGame hp0 hp hfull)

end Broadcast

end Model

end ReconstructionGame

/-! ### Infinite-horizon randomized geometric-termination protocol over `AccessScheme` -/

/-- Probability of reaching round `r` under independent round stopping probability `p` and
round-by-round withholding probabilities `q : ℕ → ℝ`: rounds `0, ..., r - 1` were all dummy rounds
and nobody withheld in those rounds. -/
def reachProb (p : ℝ) (q : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∏ m ∈ Finset.range r, (1 - p) * (1 - q m)

@[simp]
theorem reachProb_zero (p : ℝ) (q : ℕ → ℝ) : reachProb p q 0 = 1 := by
  rfl

theorem reachProb_succ (p : ℝ) (q : ℕ → ℝ) (r : ℕ) :
    reachProb p q (r + 1) = reachProb p q r * ((1 - p) * (1 - q r)) :=
  Finset.prod_range_succ _ r

theorem reachProb_nonneg {p : ℝ} {q : ℕ → ℝ} (hp1 : p ≤ 1) (hq1 : ∀ r, q r ≤ 1) (r : ℕ) :
    0 ≤ reachProb p q r :=
  Finset.prod_nonneg fun m _ => mul_nonneg (by linarith) (by linarith [hq1 m])

private theorem reachProb_le_pow {p : ℝ} {q : ℕ → ℝ} (hp1 : p ≤ 1)
    (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1) (r : ℕ) :
    reachProb p q r ≤ (1 - p) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [reachProb_succ, pow_succ]
    have hfac : (1 - p) * (1 - q r) ≤ 1 - p :=
      mul_le_of_le_one_right (by linarith) (by linarith [hq0 r])
    exact mul_le_mul ih hfac (mul_nonneg (by linarith) (by linarith [hq1 r]))
      (pow_nonneg (by linarith) r)

theorem summable_reachProb {p : ℝ} {q : ℕ → ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1) :
    Summable (reachProb p q) :=
  (summable_geometric_of_lt_one (by linarith) (by linarith)).of_nonneg_of_le
    (reachProb_nonneg hp1 hq1) (reachProb_le_pow hp1 hq0 hq1)

private theorem tendsto_reachProb_zero {p : ℝ} {q : ℕ → ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1) :
    Tendsto (reachProb p q) atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith))
    (reachProb_nonneg hp1 hq1) (reachProb_le_pow hp1 hq0 hq1)

/-- Telescoping total termination probability: for `p ∈ (0, 1]` and `q r ∈ [0, 1]`, the round
termination weights `reachProb p q r * ((1 - q r) * p + q r)` sum to `1`. -/
theorem hasSum_reachProb_termination {p : ℝ} {q : ℕ → ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1) :
    HasSum (fun r => reachProb p q r * ((1 - q r) * p + q r)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg fun r =>
    mul_nonneg (reachProb_nonneg hp1 hq1 r)
      (add_nonneg (mul_nonneg (by linarith [hq1 r]) hp0.le) (hq0 r))]
  have hterm : ∀ r, reachProb p q r * ((1 - q r) * p + q r) =
      reachProb p q r - reachProb p q (r + 1) := fun r => by
    rw [reachProb_succ]
    ring
  simp only [hterm, Finset.sum_range_sub' (reachProb p q), reachProb_zero]
  simpa using tendsto_const_nhds.sub (tendsto_reachProb_zero hp0 hp1 hq0 hq1)

/-- Infinite-horizon expected utility of a player (when pivotal upon withholding) under stopping
probability `p` and round withholding probabilities `q : ℕ → ℝ`. -/
noncomputable def geometricExpectedUtility (prefs : SecretSharingPrefs) (p : ℝ)
    (q : ℕ → ℝ) : ℝ :=
  ∑' r : ℕ, reachProb p q r *
    ((1 - q r) * p * prefs.uAll + q r * (p * prefs.uPlus + (1 - p) * prefs.uMinus))

/-- Honest participation (`q = 0`) achieves exact expected utility `uAll`. -/
@[simp]
theorem geometricExpectedUtility_zero (prefs : SecretSharingPrefs) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    geometricExpectedUtility prefs p (fun _ => 0) = prefs.uAll := by
  have h := (hasSum_reachProb_termination (q := fun _ => 0) hp0 hp1
    (fun _ => le_rfl) (fun _ => zero_le_one)).mul_right prefs.uAll
  simpa only [geometricExpectedUtility, sub_zero, one_mul, zero_mul, add_zero, mul_assoc] using
    h.tsum_eq

private theorem summable_reachProb_mul_q {p : ℝ} {q : ℕ → ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1) :
    Summable fun r => reachProb p q r * q r :=
  (summable_reachProb hp0 hp1 hq0 hq1).of_nonneg_of_le
    (fun r => mul_nonneg (reachProb_nonneg hp1 hq1 r) (hq0 r))
    (fun r => mul_le_of_le_one_right (reachProb_nonneg hp1 hq1 r) (hq1 r))

private theorem summable_geometricExpectedUtility_term (prefs : SecretSharingPrefs) {p : ℝ}
    {q : ℕ → ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1) :
    Summable fun r => reachProb p q r *
      ((1 - q r) * p * prefs.uAll + q r * (p * prefs.uPlus + (1 - p) * prefs.uMinus)) := by
  have hrewrite : (fun r => reachProb p q r *
      ((1 - q r) * p * prefs.uAll + q r * (p * prefs.uPlus + (1 - p) * prefs.uMinus))) =
      fun r => reachProb p q r * ((1 - q r) * p + q r) * prefs.uAll -
        (prefs.uAll - (p * prefs.uPlus + (1 - p) * prefs.uMinus)) * (reachProb p q r * q r) := by
    funext r
    ring
  rw [hrewrite]
  exact ((hasSum_reachProb_termination hp0 hp1 hq0 hq1).mul_right prefs.uAll).summable.sub
    ((summable_reachProb_mul_q hp0 hp1 hq0 hq1).mul_left _)

/-- **Exact telescoping utility gap identity**: for `p ∈ (0, 1]` and `q r ∈ [0, 1]`, the expected
utility shortfall below `uAll` factors as the per-round incentive margin `uAll - (p uPlus +
(1 - p) uMinus)` times `∑' r, reachProb p q r * q r`. -/
theorem uAll_sub_geometricExpectedUtility (prefs : SecretSharingPrefs) {p : ℝ} {q : ℕ → ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1) :
    prefs.uAll - geometricExpectedUtility prefs p q =
      (prefs.uAll - (p * prefs.uPlus + (1 - p) * prefs.uMinus)) *
        ∑' r : ℕ, reachProb p q r * q r := by
  have h1 := (hasSum_reachProb_termination hp0 hp1 hq0 hq1).mul_right prefs.uAll
  have hs_term := summable_geometricExpectedUtility_term prefs hp0 hp1 hq0 hq1
  have hu : prefs.uAll = ∑' r : ℕ, reachProb p q r * ((1 - q r) * p + q r) * prefs.uAll := by
    simpa only [one_mul] using h1.tsum_eq.symm
  calc
    prefs.uAll - geometricExpectedUtility prefs p q
      = (∑' r : ℕ, reachProb p q r * ((1 - q r) * p + q r) * prefs.uAll) -
          ∑' r : ℕ, reachProb p q r *
            ((1 - q r) * p * prefs.uAll + q r * (p * prefs.uPlus + (1 - p) * prefs.uMinus)) := by
        rw [← hu, geometricExpectedUtility]
    _ = ∑' r : ℕ, (prefs.uAll - (p * prefs.uPlus + (1 - p) * prefs.uMinus)) *
          (reachProb p q r * q r) := by
        rw [← h1.summable.tsum_sub hs_term]
        congr 1; funext r; ring
    _ = (prefs.uAll - (p * prefs.uPlus + (1 - p) * prefs.uMinus)) *
          ∑' r : ℕ, reachProb p q r * q r := tsum_mul_left

/-- **Infinite-horizon cryptographic geometric-termination protocol** ([HalpernTeague2004];
[AbrahamDolevGonenHalpern2006]; [DodisRabin2007], Section 8.5.2(b) and Theorem 8.9) instantiated
over an arbitrary `AccessScheme`: in each round `r : ℕ`, fresh shares are drawn from `source ∈
scheme.sources` for `genuine` (probability `stopProb ∈ (0, 1)`) or `dummy` (probability
`1 - stopProb`), and honest parties broadcast simultaneously under grim-trigger abort. -/
structure GeometricProtocol (ι Payload Key : Type*) (Share : ι → Type*) [Fintype ι] where
  /-- Rational secret-sharing preference levels `U⁺ > U > U⁻`. -/
  prefs : SecretSharingPrefs
  /-- Underlying secret-sharing scheme over `Payload`. -/
  scheme : AccessScheme Payload Key ι Share
  /-- Per-round randomness source in `scheme.sources`. -/
  source : PMF Key
  /-- Validity of `source` for perfect unauthorized-coalition privacy. -/
  source_mem : source ∈ scheme.sources
  /-- Payload shared in the genuine terminal round. -/
  genuine : Payload
  /-- Payload shared in dummy continuation rounds. -/
  dummy : Payload
  /-- Independent round stopping probability `p ∈ (0, 1)`. -/
  stopProb : ℝ
  /-- Positive genuine-round probability (`0 < p`). -/
  stopProb_pos : 0 < stopProb
  /-- Positive continuation probability (`p < 1`). -/
  stopProb_lt_one : stopProb < 1
  /-- The grand coalition of all parties is authorized to reconstruct the secret. -/
  univ_authorized : scheme.access.authorized Finset.univ

namespace GeometricProtocol

section ShamirConstructor

/-- Canonical instantiation of `GeometricProtocol` from finite-field Shamir `(k + 1, n)` secret
sharing (`shamirUniformAccessScheme` from
`CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Shamir`, matching [DodisRabin2007],
Section 8.1.2 and Theorem 8.9). -/
noncomputable def ofShamir {F ι : Type*} [Field F] [Fintype F] [Nonempty F] [Fintype ι]
    (prefs : SecretSharingPrefs) (params : Shamir.Params F ι) (genuine dummy : F)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    GeometricProtocol ι F (Shamir.Randomness params) (fun _ => F) where
  prefs := prefs
  scheme := shamirUniformAccessScheme params
  source := uniformOfFintype (Shamir.Randomness params)
  source_mem := Set.mem_singleton _
  genuine := genuine
  dummy := dummy
  stopProb := p
  stopProb_pos := hp0
  stopProb_lt_one := hp1
  univ_authorized := by
    simp only [shamirUniformAccessScheme_access, shamirAccessStructure,
      AccessStructure.threshold_authorized_iff, Finset.card_univ]
    exact params.threshold_lt_card

@[simp]
theorem ofShamir_prefs {F ι : Type*} [Field F] [Fintype F] [Nonempty F] [Fintype ι]
    (prefs : SecretSharingPrefs) (params : Shamir.Params F ι) (genuine dummy : F)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (ofShamir prefs params genuine dummy p hp0 hp1).prefs = prefs := by
  rfl

@[simp]
theorem ofShamir_scheme {F ι : Type*} [Field F] [Fintype F] [Nonempty F] [Fintype ι]
    (prefs : SecretSharingPrefs) (params : Shamir.Params F ι) (genuine dummy : F)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (ofShamir prefs params genuine dummy p hp0 hp1).scheme = shamirUniformAccessScheme params := by
  rfl

@[simp]
theorem ofShamir_source {F ι : Type*} [Field F] [Fintype F] [Nonempty F] [Fintype ι]
    (prefs : SecretSharingPrefs) (params : Shamir.Params F ι) (genuine dummy : F)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (ofShamir prefs params genuine dummy p hp0 hp1).source =
      uniformOfFintype (Shamir.Randomness params) := by
  rfl

@[simp]
theorem ofShamir_genuine {F ι : Type*} [Field F] [Fintype F] [Nonempty F] [Fintype ι]
    (prefs : SecretSharingPrefs) (params : Shamir.Params F ι) (genuine dummy : F)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (ofShamir prefs params genuine dummy p hp0 hp1).genuine = genuine := by
  rfl

@[simp]
theorem ofShamir_dummy {F ι : Type*} [Field F] [Fintype F] [Nonempty F] [Fintype ι]
    (prefs : SecretSharingPrefs) (params : Shamir.Params F ι) (genuine dummy : F)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (ofShamir prefs params genuine dummy p hp0 hp1).dummy = dummy := by
  rfl

@[simp]
theorem ofShamir_stopProb {F ι : Type*} [Field F] [Fintype F] [Nonempty F] [Fintype ι]
    (prefs : SecretSharingPrefs) (params : Shamir.Params F ι) (genuine dummy : F)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (ofShamir prefs params genuine dummy p hp0 hp1).stopProb = p := by
  rfl

end ShamirConstructor

section Semantics

variable {ι Payload Key : Type*} {Share : ι → Type*} [Fintype ι] [DecidableEq ι]
  (proto : GeometricProtocol ι Payload Key Share)

/-- Pure multi-round share-inspecting strategy of party `i`: at round `r : ℕ`, upon receiving its
round-`r` share `sh : Share i` (given no earlier abort occurred), decide whether to broadcast
(`true`) or withhold (`false`). -/
abbrev Strategy (i : ι) := ℕ → Share i → Bool

/-- Joint multi-round strategy of a coalition `C : Finset ι`: at round `r : ℕ`, all members of `C`
pool their round-`r` shares `(j : C) → Share j.1` and jointly choose each member's broadcast
action `C → Bool`. -/
abbrev CoalitionStrategy (C : Finset ι) := ℕ → ((j : C) → Share j.1) → (C → Bool)

/-- Lift an individual strategy family `τ` to a `CoalitionStrategy` where each member `j ∈ C`
depends solely on its own share. -/
def CoalitionStrategy.ofProfile (C : Finset ι) (τ : ∀ i, Strategy (Share := Share) i) :
    CoalitionStrategy (Share := Share) C :=
  fun r v j => τ j.1 r (v j)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem CoalitionStrategy.ofProfile_apply (C : Finset ι)
    (τ : ∀ i, Strategy (Share := Share) i) (r : ℕ) (v : (j : C) → Share j.1) (j : C) :
    CoalitionStrategy.ofProfile C τ r v j = τ j.1 r (v j) := by
  rfl

/-- The **honest simultaneous broadcast profile**: every party broadcasts its share in every active
round (combined with the protocol's grim-trigger abort if any party previously withheld). -/
def honestProfile : ∀ i, Strategy (Share := Share) i :=
  fun _ _ _ => true

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem honestProfile_apply (i : ι) (r : ℕ) (sh : Share i) :
    honestProfile (Share := Share) i r sh = true := by
  rfl

/-- Distribution of the simultaneous broadcast vector `ι → Bool` in round `r` when `payload` is
shared under `proto.source` and players run per-party strategies `σ`. -/
noncomputable def roundBroadcastDist (σ : ∀ i, Strategy (Share := Share) i)
    (r : ℕ) (payload : Payload) : PMF (ι → Bool) :=
  proto.source.map fun k j => σ j r (proto.scheme.share k payload j)

omit [DecidableEq ι] in
theorem roundBroadcastDist_eq_map (σ : ∀ i, Strategy (Share := Share) i)
    (r : ℕ) (payload : Payload) :
    proto.roundBroadcastDist σ r payload =
      proto.source.map fun k j => σ j r (proto.scheme.share k payload j) := by
  rfl

/-- Distribution of the simultaneous broadcast vector `ι → Bool` in round `r` when coalition `C`
pools its round-`r` shares via joint strategy `τC : CoalitionStrategy C` and all parties outside `C`
broadcast honestly (`true`). -/
noncomputable def roundCoalitionBroadcastDist (C : Finset ι)
    (τC : CoalitionStrategy (Share := Share) C) (r : ℕ) (payload : Payload) :
    PMF (ι → Bool) :=
  (proto.scheme.viewDist proto.source C payload).map fun v j =>
    if hj : j ∈ C then τC r v ⟨j, hj⟩ else true

theorem roundCoalitionBroadcastDist_ofProfile (C : Finset ι)
    (τ : ∀ i, Strategy (Share := Share) i) (r : ℕ) (payload : Payload) :
    proto.roundCoalitionBroadcastDist C (CoalitionStrategy.ofProfile C τ) r payload =
      proto.roundBroadcastDist (C.piecewise τ honestProfile) r payload := by
  simp only [roundCoalitionBroadcastDist, roundBroadcastDist, AccessScheme.viewDist,
    AccessStructure.viewDistOf, PMF.map_comp, CoalitionStrategy.ofProfile_apply]
  congr 1
  funext k j
  by_cases hj : j ∈ C
  · simp [Function.comp_apply, hj]
  · simp [Function.comp_apply, hj, honestProfile_apply]

/-- **Cryptographic share-indistinguishability bridge for share-pooling coalitions**: when an
unauthorized coalition `C` (`¬ proto.scheme.access.authorized C`) pools its joint share view via
`τC : CoalitionStrategy C`, the induced round-`r` broadcast distribution `PMF (ι → Bool)` is
identical in genuine rounds and dummy rounds. -/
theorem roundCoalitionBroadcastDist_eq {C : Finset ι}
    (hC : ¬ proto.scheme.access.authorized C)
    (τC : CoalitionStrategy (Share := Share) C) (r : ℕ) :
    proto.roundCoalitionBroadcastDist C τC r proto.genuine =
      proto.roundCoalitionBroadcastDist C τC r proto.dummy := by
  simp only [roundCoalitionBroadcastDist,
    proto.scheme.viewDist_eq_of_not_authorized proto.source_mem hC proto.genuine proto.dummy]

/-- Specialization of `roundCoalitionBroadcastDist_eq` to per-party deviating strategies
`C.piecewise τ honestProfile`. -/
theorem roundBroadcastDist_piecewise_eq {C : Finset ι}
    (hC : ¬ proto.scheme.access.authorized C)
    (τ : ∀ i, Strategy (Share := Share) i) (r : ℕ) :
    proto.roundBroadcastDist (C.piecewise τ honestProfile) r proto.genuine =
      proto.roundBroadcastDist (C.piecewise τ honestProfile) r proto.dummy := by
  rw [← proto.roundCoalitionBroadcastDist_ofProfile C τ r proto.genuine,
    ← proto.roundCoalitionBroadcastDist_ofProfile C τ r proto.dummy]
  exact proto.roundCoalitionBroadcastDist_eq hC _ r

private theorem mem_support_roundCoalitionBroadcastDist {C : Finset ι}
    {τC : CoalitionStrategy (Share := Share) C} {r : ℕ} {payload : Payload} {b : ι → Bool}
    (hb : b ∈ (proto.roundCoalitionBroadcastDist C τC r payload).support) {j : ι} (hj : j ∉ C) :
    b j = true := by
  rw [roundCoalitionBroadcastDist, PMF.mem_support_map_iff] at hb
  obtain ⟨v, _, hv⟩ := hb
  have hbj : (if h : j ∈ C then τC r v ⟨j, h⟩ else true) = b j := congrFun hv j
  split_ifs at hbj
  exact hbj.symm

/-- Set of players who reconstruct the secret when broadcast vector `b : ι → Bool` occurs in a
genuine round without coalition share-pooling: player `m` sees `insert m (broadcastSet b)`. -/
noncomputable def learnedFromVec (b : ι → Bool) : Finset ι :=
  open Classical in
  Finset.univ.filter fun m =>
    proto.scheme.access.authorized (insert m (ReconstructionGame.broadcastSet b))

@[simp]
theorem mem_learnedFromVec_iff {b : ι → Bool} {m : ι} :
    m ∈ proto.learnedFromVec b ↔
      proto.scheme.access.authorized (insert m (ReconstructionGame.broadcastSet b)) := by
  classical
  simp [learnedFromVec]

@[simp]
theorem learnedFromVec_const_true :
    proto.learnedFromVec (fun _ => true) = Finset.univ := by
  ext m
  simp [mem_learnedFromVec_iff, ReconstructionGame.broadcastSet_const_true, proto.univ_authorized]

/-- Set of players who reconstruct the secret in a genuine round when coalition `C` pools all of
its own unbroadcast shares with the publicly broadcast shares `broadcastSet b`: members `m ∈ C`
hold `C ∪ broadcastSet b`, while honest outsiders `m ∉ C` hold `insert m (broadcastSet b)`. -/
noncomputable def learnedFromCoalition (C : Finset ι) (b : ι → Bool) : Finset ι :=
  open Classical in
  Finset.univ.filter fun m =>
    proto.scheme.access.authorized
      (if m ∈ C then C ∪ ReconstructionGame.broadcastSet b
       else insert m (ReconstructionGame.broadcastSet b))

@[simp]
theorem mem_learnedFromCoalition_iff {C : Finset ι} {b : ι → Bool} {m : ι} :
    m ∈ proto.learnedFromCoalition C b ↔
      proto.scheme.access.authorized
        (if m ∈ C then C ∪ ReconstructionGame.broadcastSet b
         else insert m (ReconstructionGame.broadcastSet b)) := by
  classical
  simp [learnedFromCoalition]

@[simp]
theorem learnedFromCoalition_const_true (C : Finset ι) :
    proto.learnedFromCoalition C (fun _ => true) = Finset.univ := by
  ext m
  rw [mem_learnedFromCoalition_iff, ReconstructionGame.broadcastSet_const_true]
  simp only [Finset.mem_univ, iff_true]
  split_ifs
  · rw [Finset.union_eq_right.mpr (Finset.subset_univ C)]
    exact proto.univ_authorized
  · simp [proto.univ_authorized]

@[simp]
theorem learnedFromCoalition_singleton (i : ι) (b : ι → Bool) :
    proto.learnedFromCoalition {i} b = proto.learnedFromVec b := by
  ext m
  simp only [mem_learnedFromCoalition_iff, mem_learnedFromVec_iff, Finset.mem_singleton]
  split_ifs with hmi
  · subst hmi; rw [Finset.singleton_union]
  · rfl

private theorem outcomeUtility_learnedFromVec_le_coalition {C : Finset ι} {h₀ : ι}
    (hh₀C : h₀ ∉ C) {b : ι → Bool} (hh₀B : h₀ ∈ ReconstructionGame.broadcastSet b)
    {i : ι} (hiC : i ∈ C) :
    proto.prefs.outcomeUtility (proto.learnedFromVec b) i ≤
      proto.prefs.outcomeUtility (proto.learnedFromCoalition C b) i := by
  let B := ReconstructionGame.broadcastSet b
  by_cases hB : proto.scheme.access.authorized B
  · have hLv : proto.learnedFromVec b = Finset.univ := by
      ext m
      simp only [mem_learnedFromVec_iff, Finset.mem_univ, iff_true]
      exact proto.scheme.access.mono (Finset.subset_insert m B) hB
    have hLc : proto.learnedFromCoalition C b = Finset.univ := by
      ext m
      simp only [mem_learnedFromCoalition_iff, Finset.mem_univ, iff_true]
      split_ifs
      · exact proto.scheme.access.mono Finset.subset_union_right hB
      · exact proto.scheme.access.mono (Finset.subset_insert m B) hB
    rw [hLv, hLc]
  · have hh₀_not : h₀ ∉ proto.learnedFromCoalition C b := by
      simp only [mem_learnedFromCoalition_iff, hh₀C, ↓reduceIte, Finset.insert_eq_of_mem hh₀B]
      exact hB
    have hne_univ : proto.learnedFromCoalition C b ≠ Finset.univ :=
      fun h => hh₀_not (h ▸ Finset.mem_univ h₀)
    by_cases hiV : i ∈ proto.learnedFromVec b
    · have hiC' : i ∈ proto.learnedFromCoalition C b := by
        rw [mem_learnedFromVec_iff] at hiV
        simp only [mem_learnedFromCoalition_iff, hiC, ↓reduceIte]
        exact proto.scheme.access.mono
          (Finset.insert_subset (Finset.subset_union_left hiC) Finset.subset_union_right) hiV
      rw [proto.prefs.outcomeUtility_of_mem_of_ne_univ hiC' hne_univ]
      exact proto.prefs.outcomeUtility_le_uPlus _ i
    · rw [proto.prefs.outcomeUtility_of_not_mem hiV]
      exact proto.prefs.uMinus_le_outcomeUtility _ i

/-- Probability that all players broadcast in dummy round `r` under per-party strategies `σ`. -/
noncomputable def roundContinueProb (σ : ∀ i, Strategy (Share := Share) i) (r : ℕ) : ℝ :=
  (proto.roundBroadcastDist σ r proto.dummy (fun _ => true)).toReal

omit [DecidableEq ι] in
theorem roundContinueProb_eq (σ : ∀ i, Strategy (Share := Share) i) (r : ℕ) :
    proto.roundContinueProb σ r =
      (proto.roundBroadcastDist σ r proto.dummy (fun _ => true)).toReal := by
  rfl

/-- Probability that all players broadcast in dummy round `r` under coalition strategy `τC` against
honest outsiders. -/
noncomputable def coalitionContinueProb (C : Finset ι)
    (τC : CoalitionStrategy (Share := Share) C) (r : ℕ) : ℝ :=
  (proto.roundCoalitionBroadcastDist C τC r proto.dummy (fun _ => true)).toReal

@[simp]
theorem coalitionContinueProb_ofProfile (C : Finset ι)
    (τ : ∀ i, Strategy (Share := Share) i) (r : ℕ) :
    proto.coalitionContinueProb C (CoalitionStrategy.ofProfile C τ) r =
      proto.roundContinueProb (C.piecewise τ honestProfile) r := by
  simp only [coalitionContinueProb, roundContinueProb, roundCoalitionBroadcastDist_ofProfile]

/-- Expected payoff of player `i` conditioned on round `r` being the genuine round under per-party
strategies `σ`. -/
noncomputable def genuineStagePayoff (σ : ∀ i, Strategy (Share := Share) i)
    (r : ℕ) (i : ι) : ℝ :=
  ∑ b : ι → Bool, (proto.roundBroadcastDist σ r proto.genuine b).toReal *
    proto.prefs.outcomeUtility (proto.learnedFromVec b) i

/-- Expected payoff of player `i` conditioned on round `r` being the genuine round under joint
share-pooling coalition strategy `τC` (with pooled reconstruction `learnedFromCoalition C`). -/
noncomputable def coalitionGenuineStagePayoff (C : Finset ι)
    (τC : CoalitionStrategy (Share := Share) C) (r : ℕ) (i : ι) : ℝ :=
  ∑ b : ι → Bool, (proto.roundCoalitionBroadcastDist C τC r proto.genuine b).toReal *
    proto.prefs.outcomeUtility (proto.learnedFromCoalition C b) i

private noncomputable def evalHorizon (dGen dDum : ℕ → PMF (ι → Bool))
    (L : (ι → Bool) → Finset ι) (i : ι) : ℝ :=
  let q : ℕ → ℝ := fun r => 1 - (dDum r (fun _ => true)).toReal
  ∑' r : ℕ, reachProb proto.stopProb q r *
    (proto.stopProb *
        (∑ b : ι → Bool, (dGen r b).toReal * proto.prefs.outcomeUtility (L b) i) +
      (1 - proto.stopProb) * q r * proto.prefs.uMinus)

/-- Full infinite-horizon strategic game of `proto` over per-party share-inspecting strategies. -/
noncomputable def toPayoffGame : PayoffGame ι (Strategy (Share := Share)) where
  payoff i σ := proto.evalHorizon
    (fun r => proto.roundBroadcastDist σ r proto.genuine)
    (fun r => proto.roundBroadcastDist σ r proto.dummy)
    proto.learnedFromVec i

theorem toPayoffGame_payoff (σ : ∀ i, Strategy (Share := Share) i) (i : ι) :
    proto.toPayoffGame.payoff i σ =
      ∑' r : ℕ,
        reachProb proto.stopProb (fun m => 1 - proto.roundContinueProb σ m) r *
          (proto.stopProb * proto.genuineStagePayoff σ r i +
            (1 - proto.stopProb) * (1 - proto.roundContinueProb σ r) * proto.prefs.uMinus) := by
  rfl

/-- Infinite-horizon expected payoff of player `i` when coalition `C` pools its round-`r` shares via
`τC : CoalitionStrategy C`, outsiders play `honestProfile`, and `C` pools unbroadcast shares in the
genuine round (`learnedFromCoalition C`). -/
noncomputable def coalitionPayoff (C : Finset ι)
    (τC : CoalitionStrategy (Share := Share) C) (i : ι) : ℝ :=
  proto.evalHorizon
    (fun r => proto.roundCoalitionBroadcastDist C τC r proto.genuine)
    (fun r => proto.roundCoalitionBroadcastDist C τC r proto.dummy)
    (proto.learnedFromCoalition C) i

theorem coalitionPayoff_eq (C : Finset ι)
    (τC : CoalitionStrategy (Share := Share) C) (i : ι) :
    proto.coalitionPayoff C τC i =
      ∑' r : ℕ,
        reachProb proto.stopProb (fun m => 1 - proto.coalitionContinueProb C τC m) r *
          (proto.stopProb * proto.coalitionGenuineStagePayoff C τC r i +
            (1 - proto.stopProb) * (1 - proto.coalitionContinueProb C τC r) *
              proto.prefs.uMinus) := by
  rfl

/-- `honestProfile` is **jointly coalition-proof up to size `k`** (`k`-resilient against
share-pooling coalitions; [AbrahamDolevGonenHalpern2006]; [DodisRabin2007], Theorem 8.9's `k < n`
regime) if no coalition `C` of cardinality at most `k` can strictly increase any member's expected
utility using any joint `CoalitionStrategy C` with pooled reconstruction
`learnedFromCoalition C`. -/
@[expose] def IsJointCoalitionProofUpTo (k : ℕ) : Prop :=
  ∀ (C : Finset ι), C.card ≤ k → ∀ (τC : CoalitionStrategy (Share := Share) C), ∀ i ∈ C,
    proto.coalitionPayoff C τC i ≤ proto.toPayoffGame.payoff i honestProfile

omit [Fintype ι] [DecidableEq ι] in
private theorem continueProb_bounds (d : PMF (ι → Bool)) :
    0 ≤ 1 - (d (fun _ => true)).toReal ∧ 1 - (d (fun _ => true)).toReal ≤ 1 := by
  have h0 : 0 ≤ (d (fun _ => true)).toReal := ENNReal.toReal_nonneg
  have h1 : (d (fun _ => true)).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
  exact ⟨by linarith, by linarith⟩

/-- Under `honestProfile`, every player achieves exact expected utility `uAll`. -/
@[simp]
theorem payoff_honestProfile (i : ι) :
    proto.toPayoffGame.payoff i honestProfile = proto.prefs.uAll := by
  have hdist : ∀ r payload,
      proto.roundBroadcastDist honestProfile r payload = PMF.pure (fun _ => true) := by
    intro r payload
    rw [roundBroadcastDist_eq_map]
    exact PMF.map_const proto.source _
  have hcont : ∀ r, 1 - proto.roundContinueProb honestProfile r = 0 := by
    intro r
    simp [roundContinueProb, hdist]
  have hgen : ∀ r, proto.genuineStagePayoff honestProfile r i = proto.prefs.uAll := by
    intro r
    unfold genuineStagePayoff
    rw [hdist, Fintype.sum_eq_single (fun _ : ι => true) fun b hbne => by
      simp [PMF.pure_apply, hbne]]
    simp
  rw [toPayoffGame_payoff]
  simp only [hcont, hgen]
  have hmatch : (∑' r : ℕ, reachProb proto.stopProb (fun _ => 0) r *
      (proto.stopProb * proto.prefs.uAll +
        (1 - proto.stopProb) * 0 * proto.prefs.uMinus)) =
      geometricExpectedUtility proto.prefs proto.stopProb (fun _ => 0) := by
    unfold geometricExpectedUtility
    congr 1; funext r; ring
  rw [hmatch]
  exact geometricExpectedUtility_zero proto.prefs proto.stopProb_pos proto.stopProb_lt_one.le

private theorem stage_le_of_eq (d : PMF (ι → Bool)) {L : (ι → Bool) → Finset ι}
    (hL : L (fun _ => true) = Finset.univ) (i : ι) :
    ∑ b : ι → Bool, (d b).toReal * proto.prefs.outcomeUtility (L b) i ≤
      (d (fun _ => true)).toReal * proto.prefs.uAll +
        (1 - (d (fun _ => true)).toReal) * proto.prefs.uPlus := by
  have herase_sum : ∑ b ∈ Finset.univ.erase (fun _ : ι => true), (d b).toReal =
      1 - (d (fun _ => true)).toReal := by
    have := Finset.add_sum_erase Finset.univ (fun b => (d b).toReal)
      (Finset.mem_univ (fun _ : ι => true))
    linarith [sum_toReal d]
  calc ∑ b : ι → Bool, (d b).toReal * proto.prefs.outcomeUtility (L b) i
      = (d (fun _ => true)).toReal * proto.prefs.outcomeUtility (L (fun _ => true)) i +
          ∑ b ∈ Finset.univ.erase (fun _ : ι => true),
            (d b).toReal * proto.prefs.outcomeUtility (L b) i :=
        (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (fun _ : ι => true))).symm
    _ ≤ (d (fun _ => true)).toReal * proto.prefs.uAll +
          ∑ b ∈ Finset.univ.erase (fun _ : ι => true), (d b).toReal * proto.prefs.uPlus := by
        rw [hL, SecretSharingPrefs.outcomeUtility_univ]
        gcongr with b hb
        exact proto.prefs.outcomeUtility_le_uPlus _ i
    _ = (d (fun _ => true)).toReal * proto.prefs.uAll +
          (1 - (d (fun _ => true)).toReal) * proto.prefs.uPlus := by
        rw [← Finset.sum_mul, herase_sum]

private theorem summable_evalHorizon (dGen dDum : ℕ → PMF (ι → Bool))
    (L : (ι → Bool) → Finset ι) (i : ι) :
    let q : ℕ → ℝ := fun r => 1 - (dDum r (fun _ => true)).toReal
    Summable fun r => reachProb proto.stopProb q r *
      (proto.stopProb *
          (∑ b : ι → Bool, (dGen r b).toReal * proto.prefs.outcomeUtility (L b) i) +
        (1 - proto.stopProb) * q r * proto.prefs.uMinus) := by
  intro q
  have hq0 : ∀ r, 0 ≤ q r := fun r => (continueProb_bounds (dDum r)).1
  have hq1 : ∀ r, q r ≤ 1 := fun r => (continueProb_bounds (dDum r)).2
  have hp0 := proto.stopProb_pos
  have hp1 := proto.stopProb_lt_one.le
  have hreach_sum := summable_reachProb hp0 hp1 hq0 hq1
  let B : ℝ := |proto.prefs.uPlus| + |proto.prefs.uAll| + |proto.prefs.uMinus| + 1
  have hM_le_B : |proto.prefs.uMinus| ≤ B := by
    dsimp [B]; linarith [abs_nonneg proto.prefs.uPlus, abs_nonneg proto.prefs.uAll]
  have hP_le_B : |proto.prefs.uPlus| ≤ B := by
    dsimp [B]; linarith [abs_nonneg proto.prefs.uAll, abs_nonneg proto.prefs.uMinus]
  have hgen_abs : ∀ r,
      |∑ b : ι → Bool, (dGen r b).toReal * proto.prefs.outcomeUtility (L b) i| ≤ B := by
    intro r
    calc
      |∑ b : ι → Bool, (dGen r b).toReal * proto.prefs.outcomeUtility (L b) i|
        ≤ ∑ b : ι → Bool, |(dGen r b).toReal * proto.prefs.outcomeUtility (L b) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ b : ι → Bool, (dGen r b).toReal * B := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          have hlo := proto.prefs.uMinus_le_outcomeUtility (L b) i
          have hhi := proto.prefs.outcomeUtility_le_uPlus (L b) i
          obtain ⟨hm1, _⟩ := abs_le.mp hM_le_B
          obtain ⟨_, hp2⟩ := abs_le.mp hP_le_B
          exact abs_le.mpr ⟨by linarith, by linarith⟩
      _ = B := by rw [← Finset.sum_mul, sum_toReal, one_mul]
  refine Summable.of_norm_bounded (hreach_sum.mul_right (2 * B)) fun r => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (reachProb_nonneg hp1 hq1 r)]
  refine mul_le_mul_of_nonneg_left ?_ (reachProb_nonneg hp1 hq1 r)
  have h1 : |proto.stopProb *
      ∑ b : ι → Bool, (dGen r b).toReal * proto.prefs.outcomeUtility (L b) i| ≤ B := by
    rw [abs_mul, abs_of_pos hp0]
    exact (mul_le_mul_of_nonneg_right hp1 (abs_nonneg _)).trans
      (by rw [one_mul]; exact hgen_abs r)
  have h2 : |(1 - proto.stopProb) * q r * proto.prefs.uMinus| ≤ B := by
    have hqr0 := hq0 r
    have hqr1 := hq1 r
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hqr0]
    have hc : (1 - proto.stopProb) * q r ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hc (abs_nonneg _)).trans (by rw [one_mul]; exact hM_le_B)
  exact (abs_add_le _ _).trans (by linarith)

private theorem evalHorizon_le_geometricExpectedUtility {d : ℕ → PMF (ι → Bool)}
    {L : (ι → Bool) → Finset ι} (hL : L (fun _ => true) = Finset.univ) (i : ι) :
    proto.evalHorizon d d L i ≤
      geometricExpectedUtility proto.prefs proto.stopProb
        (fun r => 1 - (d r (fun _ => true)).toReal) := by
  set q : ℕ → ℝ := fun r => 1 - (d r (fun _ => true)).toReal
  have hq0 : ∀ r, 0 ≤ q r := fun r => (continueProb_bounds (d r)).1
  have hq1 : ∀ r, q r ≤ 1 := fun r => (continueProb_bounds (d r)).2
  have hp0 := proto.stopProb_pos
  have hp1 := proto.stopProb_lt_one.le
  have hterm_le : ∀ r : ℕ,
      reachProb proto.stopProb q r *
          (proto.stopProb *
              (∑ b : ι → Bool, (d r b).toReal * proto.prefs.outcomeUtility (L b) i) +
            (1 - proto.stopProb) * q r * proto.prefs.uMinus) ≤
        reachProb proto.stopProb q r *
          ((1 - q r) * proto.stopProb * proto.prefs.uAll +
            q r * (proto.stopProb * proto.prefs.uPlus +
              (1 - proto.stopProb) * proto.prefs.uMinus)) := by
    intro r
    refine mul_le_mul_of_nonneg_left ?_ (reachProb_nonneg hp1 hq1 r)
    have hgen := proto.stage_le_of_eq (d r) hL i
    have h1q : (d r (fun _ => true)).toReal = 1 - q r := by simp [q]
    rw [h1q] at hgen
    nlinarith
  have hsum_rhs := summable_geometricExpectedUtility_term proto.prefs hp0 hp1 hq0 hq1
  exact (proto.summable_evalHorizon d d L i).tsum_le_tsum hterm_le hsum_rhs

private theorem evalHorizon_tsum_le_of_pointwise
    {dGen₁ dDum₁ dGen₂ dDum₂ : ℕ → PMF (ι → Bool)} {L₁ L₂ : (ι → Bool) → Finset ι} {i : ι}
    (hGen : ∀ r b, dGen₁ r b = dGen₂ r b)
    (hDum : ∀ r, dDum₁ r (fun _ => true) = dDum₂ r (fun _ => true))
    (hL : ∀ r b, dGen₁ r b ≠ 0 →
      proto.prefs.outcomeUtility (L₁ b) i ≤ proto.prefs.outcomeUtility (L₂ b) i) :
    proto.evalHorizon dGen₁ dDum₁ L₁ i ≤ proto.evalHorizon dGen₂ dDum₂ L₂ i := by
  have hdum_toReal : ∀ r,
      (dDum₂ r (fun _ => true)).toReal = (dDum₁ r (fun _ => true)).toReal :=
    fun r => congrArg ENNReal.toReal (hDum r).symm
  have hterm : ∀ r : ℕ,
      reachProb proto.stopProb (fun m => 1 - (dDum₁ m (fun _ => true)).toReal) r *
          (proto.stopProb *
              (∑ b : ι → Bool, (dGen₁ r b).toReal * proto.prefs.outcomeUtility (L₁ b) i) +
            (1 - proto.stopProb) * (1 - (dDum₁ r (fun _ => true)).toReal) *
              proto.prefs.uMinus) ≤
        reachProb proto.stopProb (fun m => 1 - (dDum₁ m (fun _ => true)).toReal) r *
          (proto.stopProb *
              (∑ b : ι → Bool, (dGen₂ r b).toReal * proto.prefs.outcomeUtility (L₂ b) i) +
            (1 - proto.stopProb) * (1 - (dDum₁ r (fun _ => true)).toReal) *
              proto.prefs.uMinus) := by
    intro r
    refine mul_le_mul_of_nonneg_left ?_
      (reachProb_nonneg proto.stopProb_lt_one.le
        (fun m => (continueProb_bounds (dDum₁ m)).2) r)
    have hsum_le :
        ∑ b : ι → Bool, (dGen₁ r b).toReal * proto.prefs.outcomeUtility (L₁ b) i ≤
          ∑ b : ι → Bool, (dGen₂ r b).toReal * proto.prefs.outcomeUtility (L₂ b) i := by
      refine Finset.sum_le_sum fun b _ => ?_
      by_cases hb : dGen₁ r b = 0
      · have hb2 : dGen₂ r b = 0 := by rw [← hGen r b, hb]
        simp [hb, hb2]
      · rw [← hGen r b]
        exact mul_le_mul_of_nonneg_left (hL r b hb) ENNReal.toReal_nonneg
    nlinarith [proto.stopProb_pos]
  unfold evalHorizon
  dsimp only
  simp_rw [hdum_toReal]
  refine (proto.summable_evalHorizon dGen₁ dDum₁ L₁ i).tsum_le_tsum hterm ?_
  simpa only [hdum_toReal] using proto.summable_evalHorizon dGen₂ dDum₂ L₂ i
/-- Upper bound on a deviating unauthorized coalition's infinite-horizon payoff under joint
share-pooling strategies `τC : CoalitionStrategy C` by `geometricExpectedUtility`. -/
theorem payoff_coalition_le_geometricExpectedUtility {C : Finset ι}
    (hC : ¬ proto.scheme.access.authorized C)
    (τC : CoalitionStrategy (Share := Share) C) (i : ι) :
    proto.coalitionPayoff C τC i ≤
      geometricExpectedUtility proto.prefs proto.stopProb
        (fun r => 1 - proto.coalitionContinueProb C τC r) := by
  unfold coalitionPayoff coalitionContinueProb
  simp_rw [proto.roundCoalitionBroadcastDist_eq hC τC]
  exact proto.evalHorizon_le_geometricExpectedUtility (proto.learnedFromCoalition_const_true C) i

/-- Upper bound on a deviating unauthorized coalition's infinite-horizon payoff under per-party
strategies `C.piecewise τ honestProfile` by `geometricExpectedUtility`. -/
theorem payoff_piecewise_le_geometricExpectedUtility {C : Finset ι}
    (hC : ¬ proto.scheme.access.authorized C)
    (τ : ∀ i, Strategy (Share := Share) i) (i : ι) :
    proto.toPayoffGame.payoff i (C.piecewise τ honestProfile) ≤
      geometricExpectedUtility proto.prefs proto.stopProb
        (fun r => 1 - proto.roundContinueProb (C.piecewise τ honestProfile) r) := by
  unfold toPayoffGame roundContinueProb
  dsimp only
  simp_rw [proto.roundBroadcastDist_piecewise_eq hC τ]
  exact proto.evalHorizon_le_geometricExpectedUtility proto.learnedFromVec_const_true i

/-- **Joint coalition strategies subsume independent per-party deviations**: for any coalition
`C ≠ Finset.univ` (`∃ h₀ ∉ C`), any per-party deviation `τ` yields member `i ∈ C` at most the
pooled coalition payoff `coalitionPayoff C (CoalitionStrategy.ofProfile C τ) i`. -/
theorem payoff_piecewise_le_coalitionPayoff {C : Finset ι} (hC : C ≠ Finset.univ)
    (τ : ∀ i, Strategy (Share := Share) i) {i : ι} (hi : i ∈ C) :
    proto.toPayoffGame.payoff i (C.piecewise τ honestProfile) ≤
      proto.coalitionPayoff C (CoalitionStrategy.ofProfile C τ) i := by
  obtain ⟨h₀, hh₀C⟩ := not_forall.mp (mt Finset.eq_univ_iff_forall.mpr hC)
  refine proto.evalHorizon_tsum_le_of_pointwise
    (fun r b => (proto.roundCoalitionBroadcastDist_ofProfile C τ r proto.genuine ▸ rfl))
    (fun r => (proto.roundCoalitionBroadcastDist_ofProfile C τ r proto.dummy ▸ rfl)) ?_
  intro r b hb
  have hb_supp : b ∈ (proto.roundCoalitionBroadcastDist C (CoalitionStrategy.ofProfile C τ)
      r proto.genuine).support := by
    rw [proto.roundCoalitionBroadcastDist_ofProfile, PMF.mem_support_iff]
    exact hb
  have hh₀_true := proto.mem_support_roundCoalitionBroadcastDist hb_supp hh₀C
  have hh₀B : h₀ ∈ ReconstructionGame.broadcastSet b :=
    ReconstructionGame.mem_broadcastSet_iff.mpr hh₀_true
  exact proto.outcomeUtility_learnedFromVec_le_coalition hh₀C hh₀B hi

omit [DecidableEq ι] in
private theorem geometricExpectedUtility_le_uAll
    (hp : proto.stopProb ≤ proto.prefs.criticalStoppingProb)
    {q : ℕ → ℝ} (hq0 : ∀ r, 0 ≤ q r) (hq1 : ∀ r, q r ≤ 1) :
    geometricExpectedUtility proto.prefs proto.stopProb q ≤ proto.prefs.uAll := by
  have hgap := uAll_sub_geometricExpectedUtility proto.prefs proto.stopProb_pos
    proto.stopProb_lt_one.le hq0 hq1
  have hmargin : 0 ≤ proto.prefs.uAll -
      (proto.stopProb * proto.prefs.uPlus + (1 - proto.stopProb) * proto.prefs.uMinus) := by
    have := proto.prefs.temptation_le_uAll_iff.mpr hp
    linarith
  have htsum_nonneg : 0 ≤ ∑' r : ℕ, reachProb proto.stopProb q r * q r :=
    tsum_nonneg fun r => mul_nonneg (reachProb_nonneg proto.stopProb_lt_one.le hq1 r) (hq0 r)
  have hprod_nonneg : 0 ≤ proto.prefs.uAll -
      geometricExpectedUtility proto.prefs proto.stopProb q := by
    rw [hgap]
    exact mul_nonneg hmargin htsum_nonneg
  linarith

/-- **Cryptographic Geometric-Termination Coalition Resilience for Share-Pooling Coalitions**
([HalpernTeague2004]; [AbrahamDolevGonenHalpern2006]; [DodisRabin2007], Section 8.5.2(b) and
Theorem 8.9's `k < n` utility-dependent regime): when `stopProb ≤ prefs.criticalStoppingProb`, no
unauthorized coalition `C` (`¬ scheme.access.authorized C`) can increase any player's expected
utility above `uAll` by any joint multi-round share-inspecting deviation `CoalitionStrategy C` even
when pooling all coalition shares under `learnedFromCoalition`. -/
theorem honestProfile_isJointCoalitionProof
    (hp : proto.stopProb ≤ proto.prefs.criticalStoppingProb)
    {C : Finset ι} (hC : ¬ proto.scheme.access.authorized C)
    (τC : CoalitionStrategy (Share := Share) C) (i : ι) :
    proto.coalitionPayoff C τC i ≤ proto.toPayoffGame.payoff i honestProfile := by
  rw [proto.payoff_honestProfile i]
  exact (proto.payoff_coalition_le_geometricExpectedUtility hC τC i).trans
    (proto.geometricExpectedUtility_le_uAll hp
      (fun r => (continueProb_bounds _).1) (fun r => (continueProb_bounds _).2))

/-- **`(t - 1)`-coalitional resilience against share-pooling coalitions**
([AbrahamDolevGonenHalpern2006]; [DodisRabin2007], Theorem 8.9's `k < n` regime): when
`proto.scheme` has threshold `t` (`1 ≤ t`) and `stopProb ≤ criticalStoppingProb`, `honestProfile`
is jointly coalition-proof against all share-pooling coalitions of size at most `t - 1`.
Unlike `[DodisRabin2007]`, Theorem 8.9, survival of iterated deletion of weakly dominated
strategies (`IDoWDS`) on multi-round `GeometricProtocol` is not claimed here (only stage-game
`IDoWDS` uniqueness is formalized in `ReconstructionGame.idowdsIter_geometricStageGame_one`). -/
theorem honestProfile_isJointCoalitionProofUpTo {t : ℕ} (ht : 1 ≤ t)
    (hacc : proto.scheme.access = AccessStructure.threshold ι t)
    (hp : proto.stopProb ≤ proto.prefs.criticalStoppingProb) :
    proto.IsJointCoalitionProofUpTo (t - 1) := by
  intro C hC τC i _
  refine proto.honestProfile_isJointCoalitionProof hp ?_ τC i
  rw [hacc, AccessStructure.threshold_authorized_iff]
  omega

/-- In `GeometricProtocol.ofShamir`, when `p ≤ prefs.criticalStoppingProb`, `honestProfile` is
jointly coalition-proof up to Shamir polynomial degree `params.threshold` (`(t - 1)`-resilient
against share-pooling coalitions for `t = params.threshold + 1`). -/
theorem ofShamir_honestProfile_isJointCoalitionProofUpTo
    {F ι : Type*} [Field F] [Fintype F] [Nonempty F] [Fintype ι] [DecidableEq ι]
    (prefs : SecretSharingPrefs) (params : Shamir.Params F ι) (genuine dummy : F)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hp : p ≤ prefs.criticalStoppingProb) :
    (ofShamir prefs params genuine dummy p hp0 hp1).IsJointCoalitionProofUpTo params.threshold :=
  (ofShamir prefs params genuine dummy p hp0 hp1).honestProfile_isJointCoalitionProofUpTo
    (Nat.succ_le_succ (Nat.zero_le _)) rfl hp

/-- Joint coalition-proofness up to `k < Fintype.card ι` implies `PayoffGame.IsCoalitionProofUpTo`
against independent per-party deviations. -/
theorem IsJointCoalitionProofUpTo.toPayoffGame {proto : GeometricProtocol ι Payload Key Share}
    {k : ℕ} (h : proto.IsJointCoalitionProofUpTo k) (hk : k < Fintype.card ι) :
    proto.toPayoffGame.IsCoalitionProofUpTo k honestProfile := by
  intro C hC τ i hiC
  have hC_ne : C ≠ Finset.univ := fun heq => by
    rw [heq, Finset.card_univ] at hC
    omega
  exact (proto.payoff_piecewise_le_coalitionPayoff hC_ne τ hiC).trans
    (h C hC (CoalitionStrategy.ofProfile C τ) i hiC)

/-- **Theorem 2 (Cryptographic Geometric-Termination Coalition Resilience)**: when
`stopProb ≤ prefs.criticalStoppingProb`, no unauthorized coalition `C`
(`¬ scheme.access.authorized C`) can increase any player's expected utility above `uAll` by any
per-party multi-round share-inspecting deviation. -/
theorem honestProfile_isCoalitionProof (hp : proto.stopProb ≤ proto.prefs.criticalStoppingProb)
    {C : Finset ι} (hC : ¬ proto.scheme.access.authorized C)
    (τ : ∀ i, Strategy (Share := Share) i) (i : ι) :
    proto.toPayoffGame.payoff i (C.piecewise τ honestProfile) ≤
      proto.toPayoffGame.payoff i honestProfile := by
  rw [proto.payoff_honestProfile i]
  exact (proto.payoff_piecewise_le_geometricExpectedUtility hC τ i).trans
    (proto.geometricExpectedUtility_le_uAll hp
      (fun r => (continueProb_bounds _).1) (fun r => (continueProb_bounds _).2))

/-- **`(t - 1)`-coalitional resilience (`IsCoalitionProofUpTo (t - 1)`) for `(t, n)` threshold
schemes**: corollary of `honestProfile_isJointCoalitionProofUpTo`. -/
theorem honestProfile_isCoalitionProofUpTo {t : ℕ} (ht : 1 ≤ t)
    (hacc : proto.scheme.access = AccessStructure.threshold ι t)
    (hp : proto.stopProb ≤ proto.prefs.criticalStoppingProb) :
    proto.toPayoffGame.IsCoalitionProofUpTo (t - 1) honestProfile := by
  have ht_le : t ≤ Fintype.card ι := by
    have := proto.univ_authorized
    rwa [hacc, AccessStructure.threshold_authorized_iff, Finset.card_univ] at this
  exact (proto.honestProfile_isJointCoalitionProofUpTo ht hacc hp).toPayoffGame (by omega)

/-- In `GeometricProtocol.ofShamir`, when `p ≤ prefs.criticalStoppingProb`, `honestProfile` is
coalition-proof up to Shamir polynomial degree `params.threshold` (`(t - 1)`-resilient for
`t = params.threshold + 1`). -/
theorem ofShamir_honestProfile_isCoalitionProofUpTo
    {F ι : Type*} [Field F] [Fintype F] [Nonempty F] [Fintype ι] [DecidableEq ι]
    (prefs : SecretSharingPrefs) (params : Shamir.Params F ι) (genuine dummy : F)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hp : p ≤ prefs.criticalStoppingProb) :
    (ofShamir prefs params genuine dummy p hp0 hp1).toPayoffGame.IsCoalitionProofUpTo
      params.threshold honestProfile :=
  (ofShamir_honestProfile_isJointCoalitionProofUpTo
    prefs params genuine dummy p hp0 hp1 hp).toPayoffGame params.threshold_lt_card

/-- Exact expected payoff of coalition member `i ∈ C` when a nonempty proper coalition `C` whose
complement `Finset.univ \ C` is unauthorized withholds unconditionally in round `0` (`fun _ _ _ =>
false`): `C` learns exclusively in genuine round `0` (`stopProb * uPlus + (1 - stopProb) * uMinus`).
-/
theorem coalitionPayoff_const_false {C : Finset ι} (hC_ne : C.Nonempty) (hC_univ : C ≠ Finset.univ)
    (hOut : ¬ proto.scheme.access.authorized (Finset.univ \ C)) {i : ι} (hi : i ∈ C) :
    proto.coalitionPayoff C (fun _ _ _ => false) i =
      proto.stopProb * proto.prefs.uPlus + (1 - proto.stopProb) * proto.prefs.uMinus := by
  let bC : ι → Bool := fun j => decide (j ∉ C)
  have hdist : ∀ r payload,
      proto.roundCoalitionBroadcastDist C (fun _ _ _ => false) r payload = PMF.pure bC := by
    intro r payload
    unfold roundCoalitionBroadcastDist
    have hfn : (fun (v : (j : C) → Share j.1) (j : ι) =>
        if hj : j ∈ C then false else true) = fun _ => bC := by
      funext v j
      by_cases hj : j ∈ C <;> simp [bC, hj]
    rw [hfn]
    exact PMF.map_const _ bC
  have hbC_ne : bC ≠ (fun _ => true) := by
    obtain ⟨j₀, hj₀⟩ := hC_ne
    intro h
    have hj := congrFun h j₀
    simp [bC, hj₀] at hj
  have hcont : ∀ r, proto.coalitionContinueProb C (fun _ _ _ => false) r = 0 := fun r => by
    simp [coalitionContinueProb, hdist, PMF.pure_apply, hbC_ne.symm]
  have hB : ReconstructionGame.broadcastSet bC = Finset.univ \ C := by
    ext j
    simp [bC, ReconstructionGame.mem_broadcastSet_iff]
  have hL : proto.learnedFromCoalition C bC = C := by
    ext m
    rw [mem_learnedFromCoalition_iff, hB]
    by_cases hm : m ∈ C
    · simp [hm, Finset.union_sdiff_of_subset (Finset.subset_univ C), proto.univ_authorized]
    · simp [hm, Finset.insert_eq_of_mem (Finset.mem_sdiff.mpr ⟨Finset.mem_univ m, hm⟩), hOut]
  have hgen0 : proto.coalitionGenuineStagePayoff C (fun _ _ _ => false) 0 i =
      proto.prefs.uPlus := by
    unfold coalitionGenuineStagePayoff
    rw [hdist, Fintype.sum_eq_single bC fun b hbne => by simp [PMF.pure_apply, hbne]]
    simp [hL, proto.prefs.outcomeUtility_of_mem_of_ne_univ hi hC_univ]
  rw [coalitionPayoff_eq, tsum_eq_single 0]
  · simp [reachProb_zero, hcont, hgen0]
  · intro r hr
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
    simp [reachProb_succ, hcont]

/-- **Sharp no-honest-majority threshold characterization** ([AbrahamDolevGonenHalpern2006];
[DodisRabin2007]): in any `(t, n)` threshold scheme with `1 ≤ t` in the no-honest-majority regime
`Fintype.card ι < 2 * t - 1`, `honestProfile` is `(t - 1)`-coalitionally resilient against
share-pooling coalitions if and only if `stopProb ≤ prefs.criticalStoppingProb`. -/
theorem honestProfile_isJointCoalitionProofUpTo_iff {t : ℕ} (ht : 1 ≤ t)
    (hno_maj : Fintype.card ι < 2 * t - 1)
    (hacc : proto.scheme.access = AccessStructure.threshold ι t) :
    proto.IsJointCoalitionProofUpTo (t - 1) ↔
      proto.stopProb ≤ proto.prefs.criticalStoppingProb := by
  refine ⟨fun h => ?_, proto.honestProfile_isJointCoalitionProofUpTo ht hacc⟩
  have ht_le : t ≤ Fintype.card ι := by
    have := proto.univ_authorized
    rwa [hacc, AccessStructure.threshold_authorized_iff, Finset.card_univ] at this
  obtain ⟨C, _, hCcard⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι))
    (by rw [Finset.card_univ]; omega : t - 1 ≤ (Finset.univ : Finset ι).card)
  have hC_ne : C.Nonempty := Finset.card_pos.mp (by omega)
  have hC_univ : C ≠ Finset.univ := fun heq => by
    rw [heq, Finset.card_univ] at hCcard; omega
  have hOut : ¬ proto.scheme.access.authorized (Finset.univ \ C) := by
    rw [hacc, AccessStructure.threshold_authorized_iff, Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ]
    omega
  have ⟨i, hi⟩ := hC_ne
  have hle := h C (by omega) (fun _ _ _ => false) i hi
  rw [proto.payoff_honestProfile i, proto.coalitionPayoff_const_false hC_ne hC_univ hOut hi] at hle
  exact proto.prefs.temptation_le_uAll_iff.mp hle

/-- **Strict optimality of `honestProfile` for `stopProb < criticalStoppingProb`**: if singleton
`{i}` is unauthorized and player `i` deviates to any share-inspecting strategy `σ_i` that withholds
with positive probability in at least one round, player `i`'s expected utility is strictly less
than `uAll`. -/
theorem payoff_lt_uAll_of_withholdProb_pos
    (hp : proto.stopProb < proto.prefs.criticalStoppingProb)
    {i : ι} (hi : ¬ proto.scheme.access.authorized {i})
    {σ_i : Strategy (Share := Share) i}
    (hwithhold : ∃ r : ℕ,
      0 < 1 - proto.roundContinueProb (Function.update honestProfile i σ_i) r) :
    proto.toPayoffGame.payoff i (Function.update honestProfile i σ_i) <
      proto.toPayoffGame.payoff i honestProfile := by
  classical
  rw [proto.payoff_honestProfile i]
  set σ := Function.update honestProfile i σ_i
  set q : ℕ → ℝ := fun r => 1 - proto.roundContinueProb σ r
  have hq0 : ∀ r, 0 ≤ q r := fun r => (continueProb_bounds _).1
  have hq1 : ∀ r, q r ≤ 1 := fun r => (continueProb_bounds _).2
  let r₀ := Nat.find hwithhold
  have hr₀_pos : 0 < q r₀ := Nat.find_spec hwithhold
  have hreach_pos : 0 < reachProb proto.stopProb q r₀ :=
    Finset.prod_pos fun m hm => by
      have hm_zero : q m = 0 := by linarith [Nat.find_min hwithhold (Finset.mem_range.mp hm), hq0 m]
      rw [hm_zero]
      linarith [proto.stopProb_lt_one]
  have htsum_pos : 0 < ∑' r : ℕ, reachProb proto.stopProb q r * q r :=
    (summable_reachProb_mul_q proto.stopProb_pos proto.stopProb_lt_one.le hq0 hq1).tsum_pos
      (fun r => mul_nonneg (reachProb_nonneg proto.stopProb_lt_one.le hq1 r) (hq0 r))
      r₀ (mul_pos hreach_pos hr₀_pos)
  have hmargin_pos : 0 < proto.prefs.uAll -
      (proto.stopProb * proto.prefs.uPlus + (1 - proto.stopProb) * proto.prefs.uMinus) := by
    linarith [proto.prefs.temptation_lt_uAll_iff.mpr hp]
  have hgap := uAll_sub_geometricExpectedUtility proto.prefs proto.stopProb_pos
    proto.stopProb_lt_one.le hq0 hq1
  have hpiece : σ = ({i} : Finset ι).piecewise σ honestProfile := by
    simp [σ, Finset.piecewise_singleton]
  have hlt_geom : geometricExpectedUtility proto.prefs proto.stopProb q < proto.prefs.uAll := by
    linarith [mul_pos hmargin_pos htsum_pos]
  have hle_geom := proto.payoff_piecewise_le_geometricExpectedUtility hi σ i
  rw [← hpiece] at hle_geom
  exact hle_geom.trans_lt hlt_geom

/-- **Exact Nash equilibrium characterization for `n`-out-of-`n` geometric protocol**: when
`proto.scheme.access = AccessStructure.all ι` and `2 ≤ Fintype.card ι`, `honestProfile` is a pure
Nash equilibrium of `proto.toPayoffGame` if and only if `stopProb ≤ prefs.criticalStoppingProb`
(and is `(n - 1)`-coalitionally resilient when that bound holds). -/
theorem honestProfile_isPureNash_iff
    (hall_acc : proto.scheme.access = AccessStructure.all ι) (hcard : 2 ≤ Fintype.card ι) :
    proto.toPayoffGame.IsPureNash honestProfile ↔
      proto.stopProb ≤ proto.prefs.criticalStoppingProb := by
  refine ⟨fun hnash => ?_, fun hp => ?_⟩
  · obtain ⟨i⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
    let τ₀ : ∀ j, Strategy (Share := Share) j := fun _ _ _ => false
    have hC_univ : ({i} : Finset ι) ≠ Finset.univ :=
      ne_of_apply_ne Finset.card (by rw [Finset.card_singleton, Finset.card_univ]; omega)
    have hOut : ¬ proto.scheme.access.authorized (Finset.univ \ {i}) := by
      rw [hall_acc, AccessStructure.all_authorized_iff]
      exact fun h => (Finset.mem_sdiff.mp (h i)).2 (Finset.mem_singleton_self i)
    have hpay_eq : proto.toPayoffGame.payoff i (Function.update honestProfile i (τ₀ i)) =
        proto.coalitionPayoff {i} (CoalitionStrategy.ofProfile {i} τ₀) i := by
      rw [← Finset.piecewise_singleton]
      unfold toPayoffGame coalitionPayoff
      dsimp only
      simp_rw [proto.roundCoalitionBroadcastDist_ofProfile,
        funext (proto.learnedFromCoalition_singleton i)]
    have hle := hnash i (τ₀ i)
    rw [proto.payoff_honestProfile i, hpay_eq] at hle
    change proto.coalitionPayoff {i} (fun _ _ _ => false) i ≤ proto.prefs.uAll at hle
    rw [proto.coalitionPayoff_const_false (Finset.singleton_nonempty i) hC_univ hOut
      (Finset.mem_singleton_self i)] at hle
    exact proto.prefs.temptation_le_uAll_iff.mp hle
  · have hthresh : proto.scheme.access = AccessStructure.threshold ι (Fintype.card ι) := by
      rw [hall_acc, AccessStructure.all_eq_threshold]
    exact (proto.honestProfile_isCoalitionProofUpTo (by omega) hthresh hp).isPureNash (by omega)

end Semantics

end GeometricProtocol

end Cslib.GameTheory.RationalCrypto
