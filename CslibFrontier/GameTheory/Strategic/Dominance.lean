/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Nash
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.RelClasses
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Strategic dominance, iterated deletion, and swap-regret decay

This module develops dominant strategies, strict and weak strategic dominance, restriction of games
to strategy subsets, iterated deletion of strictly and weakly dominated strategies, and the
vanishing weight placed on `ε`-strictly dominated strategies under low swap regret, following
[NisanRoughgardenTardosVazirani2007]:

* **Dominant strategies and dominant equilibria** ([TardosVazirani2007], Sections 1.3.1 and 1.3.3,
  pp. 10–12): `CostGame.IsDominantStrategy`, `CostGame.IsDominantEquilibrium` (with
  `IsDominantEquilibrium.isPureNash`), and strict counterparts `CostGame.IsStrictlyDominantStrategy`
  and `CostGame.IsStrictlyDominantEquilibrium` (whose equilibrium is the unique pure Nash
  equilibrium by [TardosVazirani2007], Section 1.3.3, p. 12, and by derived extension also the
  unique mixed Nash equilibrium).
* **Strict, `ε`-strict, and weak dominance** ([BlumMansour2007AGT], Section 4.4.4, p. 91;
  [DodisRabin2007], Section 8.5.2, Definition 8.8, p. 200): `CostGame.IsStrictlyDominated`,
  `CostGame.IsEpsStrictlyDominated`, `CostGame.IsEpsStrictlyDominatedMixed` (domination by a mixed
  strategy), and `CostGame.IsWeaklyDominated` (with explicit binary relations `*By`).
* **Restriction and iterated deletion of strictly dominated strategies (`IDoSDS`)** (derived
  library development extending pure-strategy strict dominance; not stated in
  [TardosVazirani2007], Sections 1.3.1–1.3.3, pp. 10–12): restricting a `CostGame` to strategy
  subsets (`CostGame.restrict`) and eliminating strategies strictly dominated by surviving pure
  strategies preserves both pure and mixed Nash equilibria in both directions (no mixed Nash
  equilibrium puts positive probability on a strictly dominated strategy, equilibria of the
  restricted game lift by zero extension to equilibria of `G`, and each `CostGame.IDoSDSStep`
  requires a surviving pure dominator in the restricted game). Consequently, if `CostGame.IDoSDS`
  reduces the game to a singleton profile `s⋆`, then `s⋆` is the unique pure Nash equilibrium and
  its point-mass profile is the unique mixed Nash equilibrium
  (`IDoSDS.isPureNash_iff_eq_of_singleton`, `IDoSDS.isMixedNash_iff_eq_single_of_singleton`).
* **Iterated deletion of weakly dominated strategies (`IDoWDS`)** ([DodisRabin2007], Section 8.5.2,
  Definition 8.8 and Footnote 9, p. 200): both the relational `CostGame.IDoWDSStep` /
  `CostGame.IDoWDS` allowing arbitrary deletion schedules (which can be order-dependent) and the
  simultaneous deletion sequence `CostGame.idowdsSeq` with limit `CostGame.idowdsLimit`, which on
  any finite nonempty game stabilizes in finitely many steps to a nonempty, undominated surviving
  set (`exists_idowdsSeq_eq_idowdsLimit`, `idowdsLimit_nonempty`,
  `not_isWeaklyDominated_idowdsLimit`).
* **Decay of dominated strategies under swap regret** ([BlumMansour2007AGT], Theorem 4.13, p. 92):
  if player `i` plays mixed strategies over `T > 0` steps with swap regret at most `R` against its
  realized `deviationCost` sequence, then the time-averaged weight placed on any set of `ε`-strictly
  dominated actions (`ε > 0`, dominated by mixed — and in particular pure — actions) is at most
  `R / (ε * T)`.

All definitions follow `Cslib.GameTheory.CostGame` cost-minimization conventions (`cost = -u`), so
dominating actions achieve lower or equal cost.

## Main definitions

* `Cslib.GameTheory.CostGame.IsDominantStrategy`: a strategy achieving minimal cost against every
  opponent profile.
* `Cslib.GameTheory.CostGame.IsDominantEquilibrium`: a profile of dominant strategies.
* `Cslib.GameTheory.CostGame.IsStrictlyDominantStrategy`,
  `Cslib.GameTheory.CostGame.IsStrictlyDominantEquilibrium`: strict dominant strategies and
  equilibria.
* `Cslib.GameTheory.CostGame.IsStrictlyDominatedBy`,
  `Cslib.GameTheory.CostGame.IsStrictlyDominated`: strict strategic dominance by a pure strategy.
* `Cslib.GameTheory.CostGame.IsEpsStrictlyDominatedBy`,
  `Cslib.GameTheory.CostGame.IsEpsStrictlyDominated`: pure `ε`-strict strategic dominance.
* `Cslib.GameTheory.CostGame.IsEpsStrictlyDominatedByMixed`,
  `Cslib.GameTheory.CostGame.IsEpsStrictlyDominatedMixed`: `ε`-strict strategic dominance by a
  mixed strategy.
* `Cslib.GameTheory.CostGame.IsWeaklyDominatedBy`,
  `Cslib.GameTheory.CostGame.IsWeaklyDominated`: weak strategic dominance.
* `Cslib.GameTheory.CostGame.restrict`: restriction of a `CostGame` to strategy subsets.
* `Cslib.GameTheory.CostGame.IDoSDSStep`, `Cslib.GameTheory.CostGame.IDoSDS`: one-step and
  iterated deletion of strategies strictly dominated by pure strategies.
* `Cslib.GameTheory.CostGame.IDoWDSStep`, `Cslib.GameTheory.CostGame.IDoWDS`,
  `Cslib.GameTheory.CostGame.idowdsSeq`, `Cslib.GameTheory.CostGame.idowdsLimit`: relational and
  simultaneous iterated deletion of weakly dominated strategies.

## Main results

* `Cslib.GameTheory.CostGame.IsDominantEquilibrium.isPureNash`: a dominant-strategy equilibrium is a
  pure Nash equilibrium.
* `Cslib.GameTheory.CostGame.IsStrictlyDominantEquilibrium.eq_of_isPureNash`,
  `Cslib.GameTheory.CostGame.IsStrictlyDominantEquilibrium.eq_single_of_isMixedNash`: a strictly
  dominant equilibrium is the unique pure and mixed Nash equilibrium.
* `Cslib.GameTheory.CostGame.IsMixedNash.eq_zero_of_isStrictlyDominated`: no mixed Nash equilibrium
  puts positive weight on a strictly dominated strategy.
* `Cslib.GameTheory.CostGame.isPureNash_iff_restrict`,
  `Cslib.GameTheory.CostGame.isMixedNash_iff_restrict`: eliminating strictly dominated strategies
  preserves pure and mixed Nash equilibria in both directions.
* `Cslib.GameTheory.CostGame.IDoSDS.isPureNash_iff`,
  `Cslib.GameTheory.CostGame.IDoSDS.isMixedNash_iff_restrict`: equilibrium preservation across
  arbitrary `IDoSDS` chains.
* `Cslib.GameTheory.CostGame.IDoSDS.isPureNash_iff_eq_of_singleton`,
  `Cslib.GameTheory.CostGame.IDoSDS.isMixedNash_iff_eq_single_of_singleton`: a unique `IDoSDS`
  survivor is the unique pure and mixed Nash equilibrium.
* `Cslib.GameTheory.CostGame.exists_idowdsSeq_eq_idowdsLimit`,
  `Cslib.GameTheory.CostGame.idowdsLimit_nonempty`,
  `Cslib.GameTheory.CostGame.not_isWeaklyDominated_idowdsLimit`: finite-stage stabilization,
  non-emptiness, and fixed-point property of simultaneous `IDoWDS` on finite nonempty games.
* `Cslib.GameTheory.CostGame.timeAverage_weight_isEpsStrictlyDominatedMixed_set_le`,
  `Cslib.GameTheory.CostGame.timeAverage_weight_isEpsStrictlyDominatedMixed_le`: **Theorem 4.13**
  of [BlumMansour2007AGT], bounding the time-averaged weight on `ε`-strictly dominated strategies
  by `R / (ε * T)`.

## References

* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
* [Y. Dodis and T. Rabin, *Cryptography and Game Theory*][DodisRabin2007]
* [N. Nisan, T. Roughgarden, É. Tardos, and V. V. Vazirani (eds.),
  *Algorithmic Game Theory*][NisanRoughgardenTardosVazirani2007]
* [É. Tardos and V. V. Vazirani, *Basic Solution Concepts and Computational
  Issues*][TardosVazirani2007]
-/

public section

namespace Cslib.GameTheory.CostGame

open Finset Function

section BasicDominance

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] (G : CostGame ι S)

/-- Strategy `a` is a **dominant strategy** for player `i` ([TardosVazirani2007], Section 1.3.1,
p. 11): regardless of the strategies chosen by all players in `s`, switching coordinate `i` to `a`
never increases player `i`'s cost. -/
@[expose] def IsDominantStrategy (i : ι) (a : S i) : Prop :=
  ∀ s : ∀ j, S j, G.cost i (update s i a) ≤ G.cost i s

/-- A profile `s` is a **dominant-strategy equilibrium** (dominant strategy solution,
[TardosVazirani2007], Section 1.3.1, p. 11) if every player plays a dominant strategy. -/
@[expose] def IsDominantEquilibrium (s : ∀ i, S i) : Prop :=
  ∀ i, G.IsDominantStrategy i (s i)

/-- Strategy `a` is a **strictly dominant strategy** for player `i` ([TardosVazirani2007],
Section 1.3.3, p. 12): against every opponent profile, `a` strictly beats every other strategy
`b ≠ a`. -/
@[expose] def IsStrictlyDominantStrategy (i : ι) (a : S i) : Prop :=
  ∀ (s : ∀ j, S j) (b : S i), b ≠ a → G.cost i (update s i a) < G.cost i (update s i b)

/-- A profile `s` is a **strictly dominant equilibrium** ([TardosVazirani2007], Section 1.3.3,
p. 12) if every player plays a strictly dominant strategy. -/
@[expose] def IsStrictlyDominantEquilibrium (s : ∀ i, S i) : Prop :=
  ∀ i, G.IsStrictlyDominantStrategy i (s i)

/-- Strategy `a` of player `i` is **strictly dominated by** `b` if `b` achieves strictly lower cost
than `a` against every profile of the other players. -/
@[expose] def IsStrictlyDominatedBy (i : ι) (a b : S i) : Prop :=
  ∀ s : ∀ j, S j, G.cost i (update s i b) < G.cost i (update s i a)

/-- Strategy `a` of player `i` is **strictly dominated** if some pure strategy `b` strictly
dominates it. -/
@[expose] def IsStrictlyDominated (i : ι) (a : S i) : Prop :=
  ∃ b : S i, G.IsStrictlyDominatedBy i a b

/-- Strategy `a` of player `i` is **`ε`-strictly dominated by** `b` ([BlumMansour2007AGT],
Section 4.4.4, p. 91) if playing `b` instead of `a` saves at least `ε` in cost against every
profile of the other players. -/
@[expose] def IsEpsStrictlyDominatedBy (ε : ℝ) (i : ι) (a b : S i) : Prop :=
  ∀ s : ∀ j, S j, G.cost i (update s i b) + ε ≤ G.cost i (update s i a)

/-- Strategy `a` of player `i` is **`ε`-strictly dominated** ([BlumMansour2007AGT], Section 4.4.4,
p. 91) if some pure strategy `b` `ε`-strictly dominates it. -/
@[expose] def IsEpsStrictlyDominated (ε : ℝ) (i : ι) (a : S i) : Prop :=
  ∃ b : S i, G.IsEpsStrictlyDominatedBy ε i a b

/-- Strategy `a` of player `i` is **weakly dominated by** `b` ([DodisRabin2007], Definition 8.8,
p. 200) if `b` never costs more than `a` and strictly lowers cost on at least one profile. -/
@[expose] def IsWeaklyDominatedBy (i : ι) (a b : S i) : Prop :=
  (∀ s : ∀ j, S j, G.cost i (update s i b) ≤ G.cost i (update s i a)) ∧
    ∃ s : ∀ j, S j, G.cost i (update s i b) < G.cost i (update s i a)

/-- Strategy `a` of player `i` is **weakly dominated** ([DodisRabin2007], Definition 8.8, p. 200)
if some pure strategy `b` weakly dominates it. -/
@[expose] def IsWeaklyDominated (i : ι) (a : S i) : Prop :=
  ∃ b : S i, G.IsWeaklyDominatedBy i a b

variable {G}

theorem isDominantStrategy_iff {i : ι} {a : S i} :
    G.IsDominantStrategy i a ↔
      ∀ (s : ∀ j, S j) (b : S i), G.cost i (update s i a) ≤ G.cost i (update s i b) := by
  constructor
  · intro h s b
    simpa only [update_idem] using h (update s i b)
  · intro h s
    simpa only [update_eq_self] using h s (s i)

/-- A dominant-strategy equilibrium is a pure Nash equilibrium ([TardosVazirani2007], Section 1.3.3,
p. 12). -/
theorem IsDominantEquilibrium.isPureNash {s : ∀ i, S i} (h : G.IsDominantEquilibrium s) :
    G.IsPureNash s := fun i a => by
  simpa only [update_idem, update_eq_self] using h i (update s i a)

theorem IsStrictlyDominantStrategy.isDominantStrategy {i : ι} {a : S i}
    (h : G.IsStrictlyDominantStrategy i a) : G.IsDominantStrategy i a := by
  refine isDominantStrategy_iff.2 fun s b => ?_
  by_cases hba : b = a
  · subst hba
    exact le_rfl
  · exact (h s b hba).le

theorem IsStrictlyDominantEquilibrium.isDominantEquilibrium {s : ∀ i, S i}
    (h : G.IsStrictlyDominantEquilibrium s) : G.IsDominantEquilibrium s :=
  fun i => (h i).isDominantStrategy

/-- A strictly dominant equilibrium is the unique pure Nash equilibrium ([TardosVazirani2007],
Section 1.3.3, p. 12). -/
theorem IsStrictlyDominantEquilibrium.eq_of_isPureNash {s t : ∀ i, S i}
    (hs : G.IsStrictlyDominantEquilibrium s) (ht : G.IsPureNash t) : t = s := by
  funext i
  by_contra hne
  have hlt := hs i t (t i) hne
  rw [update_eq_self] at hlt
  exact (ht i (s i)).not_gt hlt

theorem IsStrictlyDominatedBy.trans {i : ι} {a b c : S i}
    (hab : G.IsStrictlyDominatedBy i a b) (hbc : G.IsStrictlyDominatedBy i b c) :
    G.IsStrictlyDominatedBy i a c :=
  fun s => (hbc s).trans (hab s)

theorem IsStrictlyDominatedBy.ne [∀ j, Nonempty (S j)] {i : ι} {a b : S i}
    (hab : G.IsStrictlyDominatedBy i a b) : a ≠ b := by
  rintro rfl
  exact lt_irrefl _ (hab Classical.ofNonempty)

theorem IsEpsStrictlyDominatedBy.isStrictlyDominatedBy {ε : ℝ} (hε : 0 < ε) {i : ι} {a b : S i}
    (h : G.IsEpsStrictlyDominatedBy ε i a b) : G.IsStrictlyDominatedBy i a b :=
  fun s => by linarith [h s]

theorem IsEpsStrictlyDominated.isStrictlyDominated {ε : ℝ} (hε : 0 < ε) {i : ι} {a : S i}
    (h : G.IsEpsStrictlyDominated ε i a) : G.IsStrictlyDominated i a :=
  let ⟨b, hb⟩ := h
  ⟨b, hb.isStrictlyDominatedBy hε⟩

theorem IsStrictlyDominatedBy.isWeaklyDominatedBy [∀ j, Nonempty (S j)] {i : ι} {a b : S i}
    (h : G.IsStrictlyDominatedBy i a b) : G.IsWeaklyDominatedBy i a b :=
  ⟨fun s => (h s).le, ⟨Classical.ofNonempty, h Classical.ofNonempty⟩⟩

theorem IsStrictlyDominated.isWeaklyDominated [∀ j, Nonempty (S j)] {i : ι} {a : S i}
    (h : G.IsStrictlyDominated i a) : G.IsWeaklyDominated i a :=
  let ⟨b, hb⟩ := h
  ⟨b, hb.isWeaklyDominatedBy⟩

/-- No pure Nash equilibrium plays a strictly dominated strategy. -/
theorem IsPureNash.not_isStrictlyDominated {s : ∀ i, S i} (hs : G.IsPureNash s) (i : ι) :
    ¬ G.IsStrictlyDominated i (s i) := by
  rintro ⟨b, hb⟩
  have hlt := hb s
  rw [update_eq_self] at hlt
  exact (hs i b).not_gt hlt

end BasicDominance

section MixedDominance

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)]
  {G : CostGame ι S}

omit [DecidableEq ι] in
/-- Any profile of mixed strategies assigns strictly positive product weight to at least one pure
profile. -/
private theorem exists_productWeight_pos {p : ∀ i, S i → ℝ}
    (hp : ∀ i, IsMixedStrategy (p i)) : ∃ s : ∀ i, S i, 0 < productWeight p s := by
  classical
  have hsum : ∑ s, productWeight p s = 1 := sum_productWeight fun j => (hp j).sum_eq_one
  by_contra h
  push Not at h
  have h0 : ∑ s, productWeight p s = 0 := sum_eq_zero fun s _ =>
    le_antisymm (h s) (productWeight_nonneg (fun j => (hp j).nonneg) s)
  linarith

omit [Fintype ι] in
/-- Strategy `a` of player `i` is **`ε`-strictly dominated by a mixed strategy** `q`
([BlumMansour2007AGT], Section 4.4.4, p. 91) if `q` is a mixed strategy saving at least `ε` in
expected cost over `a` against every profile of the other players. -/
@[expose] def IsEpsStrictlyDominatedByMixed (G : CostGame ι S) (ε : ℝ) (i : ι) (a : S i)
    (q : S i → ℝ) : Prop :=
  IsMixedStrategy q ∧
    ∀ s : ∀ j, S j, (∑ b : S i, q b * G.cost i (update s i b)) + ε ≤ G.cost i (update s i a)

omit [Fintype ι] in
/-- Strategy `a` of player `i` is **`ε`-strictly dominated by some mixed strategy**
([BlumMansour2007AGT], Section 4.4.4, p. 91). -/
@[expose] def IsEpsStrictlyDominatedMixed (G : CostGame ι S) (ε : ℝ) (i : ι) (a : S i) : Prop :=
  ∃ q : S i → ℝ, G.IsEpsStrictlyDominatedByMixed ε i a q

omit [Fintype ι] in
/-- Every pure `ε`-strictly dominating action induces a mixed `ε`-strictly dominating point mass. -/
theorem IsEpsStrictlyDominatedBy.isEpsStrictlyDominatedByMixed {i : ι} [DecidableEq (S i)]
    {ε : ℝ} {a b : S i} (hab : G.IsEpsStrictlyDominatedBy ε i a b) :
    G.IsEpsStrictlyDominatedByMixed ε i a (Pi.single b 1) := by
  refine ⟨isMixedStrategy_single b, fun s => ?_⟩
  simpa only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ,
    ↓reduceIte] using hab s

omit [Fintype ι] in
/-- If `a` is `ε`-strictly dominated by a pure action, it is also `ε`-strictly dominated by a mixed
strategy. -/
theorem IsEpsStrictlyDominated.isEpsStrictlyDominatedMixed {ε : ℝ} {i : ι} {a : S i}
    (ha : G.IsEpsStrictlyDominated ε i a) : G.IsEpsStrictlyDominatedMixed ε i a := by
  classical
  obtain ⟨b, hb⟩ := ha
  exact ⟨Pi.single b 1, hb.isEpsStrictlyDominatedByMixed⟩

/-- If `b` strictly dominates `a`, then `b` has strictly lower expected cost than `a` against any
profile of mixed strategies. -/
theorem IsStrictlyDominatedBy.deviationCost_lt {p : ∀ i, S i → ℝ}
    (hp : ∀ i, IsMixedStrategy (p i)) {i : ι} {a b : S i}
    (hab : G.IsStrictlyDominatedBy i a b) :
    G.deviationCost p i b < G.deviationCost p i a := by
  rw [deviationCost_def, deviationCost_def]
  obtain ⟨s₀, hs₀⟩ := exists_productWeight_pos hp
  refine sum_lt_sum (fun s _ => ?_) ⟨s₀, mem_univ s₀, mul_lt_mul_of_pos_left (hab s₀) hs₀⟩
  exact mul_le_mul_of_nonneg_left (hab s).le (productWeight_nonneg (fun j => (hp j).nonneg) s)

/-- If mixed strategy `q` `ε`-strictly dominates `a`, then `q` saves at least `ε` in expected cost
over `a` against any profile of mixed strategies `p`. -/
theorem IsEpsStrictlyDominatedByMixed.sum_mul_deviationCost_add_le {p : ∀ i, S i → ℝ}
    (hp : ∀ i, IsMixedStrategy (p i)) {ε : ℝ} {i : ι} {a : S i} {q : S i → ℝ}
    (hqa : G.IsEpsStrictlyDominatedByMixed ε i a q) :
    (∑ b : S i, q b * G.deviationCost p i b) + ε ≤ G.deviationCost p i a := by
  have hsum : ∑ s, productWeight p s = 1 := sum_productWeight fun j => (hp j).sum_eq_one
  have hswap : ∑ b : S i, q b * G.deviationCost p i b =
      ∑ s, productWeight p s * ∑ b : S i, q b * G.cost i (update s i b) := by
    simp_rw [deviationCost_def, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun s _ => sum_congr rfl fun b _ => by ring
  rw [hswap, deviationCost_def]
  calc (∑ s, productWeight p s * ∑ b : S i, q b * G.cost i (update s i b)) + ε
      = ∑ s, productWeight p s * ((∑ b : S i, q b * G.cost i (update s i b)) + ε) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, hsum, one_mul]
    _ ≤ ∑ s, productWeight p s * G.cost i (update s i a) :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hqa.2 s)
          (productWeight_nonneg (fun j => (hp j).nonneg) s)

/-- Also deduce `IsEpsStrictlyDominatedBy.deviationCost_add_le` from the mixed-dominance lemma. -/
theorem IsEpsStrictlyDominatedBy.deviationCost_add_le {p : ∀ i, S i → ℝ}
    (hp : ∀ i, IsMixedStrategy (p i)) {ε : ℝ} {i : ι} {a b : S i}
    (hab : G.IsEpsStrictlyDominatedBy ε i a b) :
    G.deviationCost p i b + ε ≤ G.deviationCost p i a := by
  classical
  have h := hab.isEpsStrictlyDominatedByMixed.sum_mul_deviationCost_add_le hp
  simpa only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ,
    ↓reduceIte] using h

omit [Fintype ι] [∀ i, Fintype (S i)] in
/-- In a finite game with nonempty strategy sets, strict dominance is equivalent to `ε`-strict
dominance for some `ε > 0`. -/
theorem isStrictlyDominated_iff_exists_isEpsStrictlyDominated [Finite ι] [∀ j, Finite (S j)]
    [∀ j, Nonempty (S j)] {i : ι} {a : S i} :
    G.IsStrictlyDominated i a ↔ ∃ ε > 0, G.IsEpsStrictlyDominated ε i a := by
  cases nonempty_fintype ι
  have := fun j => Fintype.ofFinite (S j)
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨s₀, -, hs₀⟩ := univ.exists_min_image
      (fun s : ∀ j, S j => G.cost i (update s i a) - G.cost i (update s i b)) univ_nonempty
    refine ⟨G.cost i (update s₀ i a) - G.cost i (update s₀ i b), sub_pos.2 (hb s₀), b, fun s => ?_⟩
    linarith [hs₀ s (mem_univ s)]
  · rintro ⟨ε, hε, h⟩
    exact h.isStrictlyDominated hε

/-- No mixed Nash equilibrium assigns positive probability to a strictly dominated strategy. -/
theorem IsMixedNash.eq_zero_of_isStrictlyDominated {p : ∀ i, S i → ℝ} (hp : G.IsMixedNash p)
    {i : ι} {a : S i} (ha : G.IsStrictlyDominated i a) : p i a = 0 := by
  obtain ⟨b, hab⟩ := ha
  rcases ((hp.1 i).nonneg a).eq_or_lt with h0 | hpos
  · exact h0.symm
  · have heq := hp.deviationCost_eq_of_pos i hpos
    have hle := hp.2 i b
    have hlt := hab.deviationCost_lt hp.1
    linarith

/-- Extending the pure-Nash uniqueness of [TardosVazirani2007], Section 1.3.3, p. 12 to mixed
strategies: every mixed Nash equilibrium puts weight `1` on each player's strictly dominant
strategy. -/
theorem IsStrictlyDominantEquilibrium.eq_single_of_isMixedNash [∀ j, DecidableEq (S j)]
    {s : ∀ i, S i} (hs : G.IsStrictlyDominantEquilibrium s) {p : ∀ i, S i → ℝ}
    (hp : G.IsMixedNash p) : p = fun i => Pi.single (s i) 1 := by
  funext i a
  by_cases ha : a = s i
  · subst ha
    have hzero : ∀ b ≠ s i, p i b = 0 := fun b hb =>
      hp.eq_zero_of_isStrictlyDominated ⟨s i, fun t => hs i t b hb⟩
    have hsum := (hp.1 i).sum_eq_one
    rw [Fintype.sum_eq_single (s i) hzero] at hsum
    simpa only [Pi.single_eq_same] using hsum
  · rw [Pi.single_eq_of_ne ha]
    exact hp.eq_zero_of_isStrictlyDominated ⟨s i, fun t => hs i t a ha⟩

end MixedDominance

/-! ### Restriction to strategy subsets and iterated deletion -/

section Restriction

variable {ι : Type*} {S : ι → Type*}

/-- The **restriction** of `G` to strategy subsets `A i ⊆ S i`: each player `i` chooses from the
subtype `A i` and incurs its original cost in `G`. -/
def restrict (G : CostGame ι S) (A : ∀ i, Set (S i)) : CostGame ι (fun i => A i) where
  cost i s := G.cost i fun j => (s j : S j)

@[simp]
theorem restrict_cost (G : CostGame ι S) (A : ∀ i, Set (S i)) (i : ι) (s : ∀ j, A j) :
    (G.restrict A).cost i s = G.cost i fun j => (s j : S j) := by rfl

open Classical in
/-- Zero-extension of a family of functions `q i : A i → ℝ` on strategy subsets to the full
strategy spaces `S i → ℝ`. -/
private noncomputable def liftMixed (A : ∀ i, Set (S i)) (q : ∀ i, A i → ℝ) (i : ι) (a : S i) :
    ℝ :=
  if ha : a ∈ A i then q i ⟨a, ha⟩ else 0

private theorem restrict_cost_update [DecidableEq ι] (G : CostGame ι S) {A : ∀ i, Set (S i)}
    (s : ∀ i, A i) (i : ι) (a : A i) :
    (G.restrict A).cost i (update s i a) = G.cost i (update (fun j => (s j : S j)) i a.val) :=
  congrArg (G.cost i) (funext (apply_update (fun j => ((↑) : A j → S j)) s i a))

section PureRestriction

variable [DecidableEq ι] {G : CostGame ι S} {A : ∀ i, Set (S i)}

/-- Eliminating strategies that are strictly dominated by remaining strategies preserves pure Nash
equilibria in both directions. -/
theorem isPureNash_iff_restrict
    (hA : ∀ i (a : S i), a ∉ A i → ∃ b ∈ A i, G.IsStrictlyDominatedBy i a b)
    (s : ∀ i, S i) :
    G.IsPureNash s ↔ ∃ hs : ∀ i, s i ∈ A i, (G.restrict A).IsPureNash fun i => ⟨s i, hs i⟩ := by
  constructor
  · intro hs
    have hmem : ∀ i, s i ∈ A i := fun i => by
      by_contra hni
      obtain ⟨b, -, hb⟩ := hA i (s i) hni
      exact hs.not_isStrictlyDominated i ⟨b, hb⟩
    refine ⟨hmem, fun i a => ?_⟩
    rw [restrict_cost_update]
    exact hs i a.val
  · rintro ⟨hmem, hs⟩ i a
    by_cases ha : a ∈ A i
    · have h := hs i ⟨a, ha⟩
      rwa [restrict_cost_update] at h
    · obtain ⟨b, hbA, hb⟩ := hA i a ha
      have h := hs i ⟨b, hbA⟩
      rw [restrict_cost_update] at h
      exact h.trans (hb s).le

end PureRestriction

section MixedRestriction

variable [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] {G : CostGame ι S}
  {A : ∀ i, Set (S i)}

omit [Fintype ι] [DecidableEq ι] in
private theorem sum_subtype_eq_sum_liftMixed [∀ i, Fintype (A i)] (q : ∀ i, A i → ℝ) (i : ι) :
    ∑ a : A i, q i a = ∑ a : S i, liftMixed A q i a := by
  classical
  dsimp only [liftMixed]
  have hfilter : (∑ a : S i, if ha : a ∈ A i then q i ⟨a, ha⟩ else 0) =
      ∑ a ∈ univ.filter (· ∈ A i), (if ha : a ∈ A i then q i ⟨a, ha⟩ else 0) := by
    symm
    refine Finset.sum_subset (subset_univ _) fun a _ hnot => ?_
    have ha : a ∉ A i := by simpa only [mem_filter, mem_univ, true_and] using hnot
    simp only [ha, dite_false]
  rw [hfilter]
  exact Finset.sum_bij (fun (a : A i) _ => a.val)
    (fun a _ => mem_filter.2 ⟨mem_univ _, a.property⟩)
    (fun a₁ _ a₂ _ h => Subtype.ext h)
    (fun b hb => ⟨⟨b, (mem_filter.1 hb).2⟩, mem_univ _, rfl⟩)
    (fun a _ => by simp only [a.property, dite_true])

omit [Fintype ι] [DecidableEq ι] in
private theorem isMixedStrategy_liftMixed_iff [∀ i, Fintype (A i)] (q : ∀ i, A i → ℝ) (i : ι) :
    IsMixedStrategy (liftMixed A q i) ↔ IsMixedStrategy (q i) := by
  constructor
  · intro h
    refine isMixedStrategy_iff.2 ⟨fun a => ?_, ?_⟩
    · have ha := h.nonneg a.val
      simpa only [liftMixed, a.property, dite_true] using ha
    · rw [sum_subtype_eq_sum_liftMixed]
      exact h.sum_eq_one
  · intro h
    refine isMixedStrategy_iff.2 ⟨fun a => ?_, ?_⟩
    · dsimp only [liftMixed]
      split_ifs with ha
      · exact h.nonneg ⟨a, ha⟩
      · exact le_rfl
    · rw [← sum_subtype_eq_sum_liftMixed]
      exact h.sum_eq_one

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
open scoped Classical in
private theorem productWeight_liftMixed (q : ∀ i, A i → ℝ) (s : ∀ i, S i) :
    productWeight (liftMixed A q) s =
      if hs : ∀ i, s i ∈ A i then productWeight q (fun i => ⟨s i, hs i⟩) else 0 := by
  rw [productWeight_def]
  split_ifs with hs
  · rw [productWeight_def]
    exact prod_congr rfl fun i _ => by simp only [liftMixed, hs i, dite_true]
  · push Not at hs
    obtain ⟨i, hi⟩ := hs
    exact prod_eq_zero (mem_univ i) (by simp only [liftMixed, hi, dite_false])

private theorem sum_productWeight_liftMixed_mul [∀ i, Fintype (A i)] (q : ∀ i, A i → ℝ)
    (f : (∀ i, S i) → ℝ) :
    ∑ s : ∀ i, S i, productWeight (liftMixed A q) s * f s =
      ∑ s : ∀ i, A i, productWeight q s * f (fun i => (s i : S i)) := by
  classical
  have h1 : ∀ s : ∀ i, S i, productWeight (liftMixed A q) s * f s =
      if hs : ∀ i, s i ∈ A i then productWeight q (fun i => ⟨s i, hs i⟩) * f s else 0 := by
    intro s
    rw [productWeight_liftMixed]
    split_ifs <;> simp only [zero_mul]
  simp_rw [h1]
  have hfilter :
      (∑ s : ∀ i, S i,
          if hs : ∀ i, s i ∈ A i then productWeight q (fun i => ⟨s i, hs i⟩) * f s else 0) =
        ∑ s ∈ univ.filter (fun s : ∀ i, S i => ∀ i, s i ∈ A i),
          (if hs : ∀ i, s i ∈ A i then productWeight q (fun i => ⟨s i, hs i⟩) * f s else 0) := by
    symm
    refine Finset.sum_subset (subset_univ _) fun s _ hnot => ?_
    have hs : ¬ ∀ i, s i ∈ A i := by simpa only [mem_filter, mem_univ, true_and] using hnot
    simp only [hs, dite_false]
  rw [hfilter]
  symm
  exact Finset.sum_bij (fun (s : ∀ i, A i) _ i => (s i : S i))
    (fun s _ => mem_filter.2 ⟨mem_univ _, fun i => (s i).property⟩)
    (fun s₁ _ s₂ _ h => funext fun i => Subtype.ext (congrFun h i))
    (fun s hs => ⟨fun i => ⟨s i, (mem_filter.1 hs).2 i⟩, mem_univ _, rfl⟩)
    (fun s _ => by
      have hs : ∀ i, ((s i : A i) : S i) ∈ A i := fun i => (s i).property
      rw [dite_eq_left_of_eq_true (eq_true hs)])

private theorem expectedCost_restrict_eq [∀ i, Fintype (A i)] (q : ∀ i, A i → ℝ) (i : ι) :
    (G.restrict A).expectedCost q i = G.expectedCost (liftMixed A q) i := by
  rw [expectedCost_def, expectedCost_def, sum_productWeight_liftMixed_mul]
  rfl

private theorem deviationCost_restrict_eq [∀ i, Fintype (A i)] (q : ∀ i, A i → ℝ) (i : ι)
    (a : A i) :
    (G.restrict A).deviationCost q i a = G.deviationCost (liftMixed A q) i a.val := by
  rw [deviationCost_def, deviationCost_def, sum_productWeight_liftMixed_mul]
  exact sum_congr rfl fun s _ => by rw [restrict_cost_update]

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] in
private theorem liftMixed_restrict_eq_self {p : ∀ i, S i → ℝ}
    (hp : ∀ i a, a ∉ A i → p i a = 0) :
    liftMixed A (fun i (a : A i) => p i a.val) = p := by
  funext i a
  dsimp only [liftMixed]
  split_ifs with ha
  · rfl
  · exact (hp i a ha).symm

/-- Characterization of `IsMixedNash` on `G.restrict A` for a full-space strategy profile `p`
supported on `A`. -/
private theorem isMixedNash_restrict_iff_supported [∀ i, Fintype (A i)] {p : ∀ i, S i → ℝ} :
    ((∀ i a, a ∉ A i → p i a = 0) ∧ (G.restrict A).IsMixedNash fun i a => p i a.val) ↔
      (∀ i, IsMixedStrategy (p i)) ∧ (∀ i a, a ∉ A i → p i a = 0) ∧
        ∀ i, ∀ a ∈ A i, G.expectedCost p i ≤ G.deviationCost p i a := by
  constructor
  · rintro ⟨hzero, hq⟩
    have hlift := liftMixed_restrict_eq_self hzero
    refine ⟨fun i => ?_, hzero, fun i a ha => ?_⟩
    · rw [← hlift]
      exact (isMixedStrategy_liftMixed_iff _ i).2 (hq.1 i)
    · have h := hq.2 i ⟨a, ha⟩
      rwa [expectedCost_restrict_eq, deviationCost_restrict_eq, hlift] at h
  · rintro ⟨hp, hzero, hle⟩
    have hlift := liftMixed_restrict_eq_self hzero
    refine ⟨hzero, fun i => ?_, fun i a => ?_⟩
    · exact (isMixedStrategy_liftMixed_iff (fun j (b : A j) => p j b.val) i).1
        (hlift.symm ▸ hp i)
    · rw [expectedCost_restrict_eq, deviationCost_restrict_eq, hlift]
      exact hle i a.val a.property

/-- Eliminating strategies strictly dominated by remaining strategies preserves mixed Nash
equilibria in both directions: every equilibrium of `G` puts zero weight outside `A` and restricts
to an equilibrium of `G.restrict A`, and every equilibrium of `G.restrict A` lifts by zero
extension to `G`. -/
theorem isMixedNash_iff_restrict [∀ i, Fintype (A i)]
    (hA : ∀ i (a : S i), a ∉ A i → ∃ b ∈ A i, G.IsStrictlyDominatedBy i a b)
    (p : ∀ i, S i → ℝ) :
    G.IsMixedNash p ↔
      (∀ i a, a ∉ A i → p i a = 0) ∧ (G.restrict A).IsMixedNash fun i a => p i a.val := by
  rw [isMixedNash_restrict_iff_supported]
  constructor
  · intro hp
    refine ⟨hp.1, fun i a ha => ?_, fun i a _ => hp.2 i a⟩
    obtain ⟨b, -, hb⟩ := hA i a ha
    exact hp.eq_zero_of_isStrictlyDominated ⟨b, hb⟩
  · rintro ⟨hp, hzero, hle⟩
    refine ⟨hp, fun i a => ?_⟩
    by_cases ha : a ∈ A i
    · exact hle i a ha
    · obtain ⟨b, hbA, hb⟩ := hA i a ha
      exact (hle i b hbA).trans (hb.deviationCost_lt hp).le

end MixedRestriction

/-! ### Iterated deletion of strictly and weakly dominated strategies -/

section IteratedDeletion

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] (G : CostGame ι S)

/-- One step of **iterated deletion of strictly dominated strategies (`IDoSDS`)**: `B i ⊆ A i` for
every player `i`, and every strategy `a ∈ A i \ B i` removed at this step is strictly dominated in
`G.restrict A` by some surviving strategy `b ∈ B i`. -/
@[expose] def IDoSDSStep (A B : ∀ i, Set (S i)) : Prop :=
  (∀ i, B i ⊆ A i) ∧ ∀ i (a : S i) (ha : a ∈ A i), a ∉ B i →
    ∃ (b : S i) (hbA : b ∈ A i), b ∈ B i ∧
      (G.restrict A).IsStrictlyDominatedBy i ⟨a, ha⟩ ⟨b, hbA⟩

/-- **Iterated deletion of strictly dominated strategies (`IDoSDS`)**: the reflexive–transitive
closure of `IDoSDSStep`. -/
@[expose] def IDoSDS : (∀ i, Set (S i)) → (∀ i, Set (S i)) → Prop :=
  Relation.ReflTransGen G.IDoSDSStep

/-- One step of **iterated deletion of weakly dominated strategies (`IDoWDS`)**
([DodisRabin2007], Definition 8.8 and Footnote 9, p. 200): `B i ⊆ A i` for every player `i`, and
every strategy `a ∈ A i \ B i` removed at this step is weakly dominated in `G.restrict A`. -/
@[expose] def IDoWDSStep (A B : ∀ i, Set (S i)) : Prop :=
  (∀ i, B i ⊆ A i) ∧ ∀ i (a : S i) (ha : a ∈ A i), a ∉ B i →
    (G.restrict A).IsWeaklyDominated i ⟨a, ha⟩

/-- Relational **iterated deletion of weakly dominated strategies (`IDoWDS`)**, allowing arbitrary
deletion orders ([DodisRabin2007], Footnote 9, p. 200). -/
@[expose] def IDoWDS : (∀ i, Set (S i)) → (∀ i, Set (S i)) → Prop :=
  Relation.ReflTransGen G.IDoWDSStep

variable {G}

/-- The canonical simultaneous **iterated deletion of weakly dominated strategies** sequence of
[DodisRabin2007], Definition 8.8, p. 200: `S_i^0 = S_i` and
`S_i^{k+1} = S_i^k \ DOM_i(S_1^k, …, S_n^k)`. -/
def idowdsSeq (G : CostGame ι S) : ℕ → ∀ i, Set (S i)
  | 0 => fun _ => Set.univ
  | k + 1 => fun i =>
      {a | ∃ ha : a ∈ G.idowdsSeq k i, ¬ (G.restrict (G.idowdsSeq k)).IsWeaklyDominated i ⟨a, ha⟩}

@[simp]
theorem idowdsSeq_zero (G : CostGame ι S) : G.idowdsSeq 0 = fun _ => Set.univ := by rfl

@[simp]
theorem idowdsSeq_succ (G : CostGame ι S) (k : ℕ) :
    G.idowdsSeq (k + 1) = fun i =>
      {a | ∃ ha : a ∈ G.idowdsSeq k i,
        ¬ (G.restrict (G.idowdsSeq k)).IsWeaklyDominated i ⟨a, ha⟩} := by rfl

/-- The surviving strategy set `S_i^∞ = ⋂_k S_i^k` of simultaneous `IDoWDS`
([DodisRabin2007], Definition 8.8, p. 200). -/
def idowdsLimit (G : CostGame ι S) (i : ι) : Set (S i) :=
  ⋂ k : ℕ, G.idowdsSeq k i

@[simp]
theorem mem_idowdsLimit_iff (G : CostGame ι S) (i : ι) (a : S i) :
    a ∈ G.idowdsLimit i ↔ ∀ k, a ∈ G.idowdsSeq k i :=
  Set.mem_iInter

theorem idowdsSeq_subset_of_le {m n : ℕ} (hmn : m ≤ n) (i : ι) :
    G.idowdsSeq n i ⊆ G.idowdsSeq m i := by
  induction hmn with
  | refl => exact Set.Subset.rfl
  | step _ ih => exact fun a ha => ih ha.1

theorem idowdsStep_idowdsSeq (k : ℕ) :
    G.IDoWDSStep (G.idowdsSeq k) (G.idowdsSeq (k + 1)) :=
  ⟨fun _ _ ha => ha.1, fun _ _ ha hnot => not_not.1 fun hnd => hnot ⟨ha, hnd⟩⟩

/-- Every stage of the simultaneous `idowdsSeq` sequence is reachable by relational `IDoWDS`. -/
theorem idowds_idowdsSeq (k : ℕ) :
    G.IDoWDS (fun _ => Set.univ) (G.idowdsSeq k) := by
  induction k with
  | zero => exact .refl
  | succ k ih => exact ih.tail (idowdsStep_idowdsSeq k)

/-- On a finite game, every player with a nonempty strategy set has a strategy that is not weakly
dominated (minimizing total cost summed across all profiles). -/
theorem exists_not_isWeaklyDominated [Finite ι] [∀ j, Finite (S j)] (G : CostGame ι S)
    {i : ι} [Nonempty (S i)] :
    ∃ a : S i, ¬ G.IsWeaklyDominated i a := by
  cases nonempty_fintype ι
  have := fun j => Fintype.ofFinite (S j)
  obtain ⟨a, -, ha⟩ := (univ : Finset (S i)).exists_min_image
    (fun a => ∑ s : ∀ j, S j, G.cost i (update s i a)) univ_nonempty
  refine ⟨a, fun ⟨b, hle, s₀, hlt⟩ => (ha b (mem_univ b)).not_gt ?_⟩
  exact sum_lt_sum (fun s _ => hle s) ⟨s₀, mem_univ s₀, hlt⟩

/-- On a finite game with nonempty strategy sets, every stage of simultaneous `IDoWDS` retains at
least one strategy for every player. -/
theorem idowdsSeq_nonempty [Finite ι] [∀ j, Finite (S j)] [∀ j, Nonempty (S j)]
    (G : CostGame ι S) (k : ℕ) (i : ι) : (G.idowdsSeq k i).Nonempty := by
  induction k generalizing i with
  | zero => exact Set.univ_nonempty
  | succ k ih =>
    have : Nonempty (G.idowdsSeq k i) := (ih i).to_subtype
    obtain ⟨⟨a, ha⟩, hnd⟩ := (G.restrict (G.idowdsSeq k)).exists_not_isWeaklyDominated (i := i)
    exact ⟨a, ha, hnd⟩

/-- On a finite game, the simultaneous `IDoWDS` sequence stabilizes at a finite stage `K`, where it
equals `G.idowdsLimit`. -/
theorem exists_idowdsSeq_eq_idowdsLimit [Finite ι] [∀ j, Finite (S j)] (G : CostGame ι S) :
    ∃ K : ℕ, ∀ k, K ≤ k → G.idowdsSeq k = G.idowdsLimit := by
  cases nonempty_fintype ι
  have := fun j => Fintype.ofFinite (S j)
  classical
  let cardAt (k : ℕ) : ℕ := ∑ i : ι, (univ.filter (· ∈ G.idowdsSeq k i)).card
  obtain ⟨_, ⟨K, rfl⟩, hK_min⟩ :=
    WellFounded.has_min Nat.lt_wfRel.wf (Set.range cardAt) ⟨cardAt 0, 0, rfl⟩
  have hsub_step : ∀ i : ι,
      univ.filter (· ∈ G.idowdsSeq (K + 1) i) ⊆ univ.filter (· ∈ G.idowdsSeq K i) :=
    fun i a ha => mem_filter.2 ⟨mem_univ a, (mem_filter.1 ha).2.1⟩
  have hcard_le : ∀ i ∈ univ, (univ.filter (· ∈ G.idowdsSeq (K + 1) i)).card ≤
      (univ.filter (· ∈ G.idowdsSeq K i)).card := fun i _ => card_le_card (hsub_step i)
  have hcard_eq : cardAt (K + 1) = cardAt K :=
    le_antisymm (sum_le_sum hcard_le) (not_lt.1 (hK_min (cardAt (K + 1)) ⟨K + 1, rfl⟩))
  have hstep_eq : G.idowdsSeq (K + 1) = G.idowdsSeq K := by
    funext i
    ext a
    simpa only [mem_filter, mem_univ, true_and] using Finset.ext_iff.1 (eq_of_subset_of_card_le
      (hsub_step i) ((sum_eq_sum_iff_of_le hcard_le).1 hcard_eq i (mem_univ i)).ge) a
  have hconst : ∀ k, K ≤ k → G.idowdsSeq k = G.idowdsSeq K := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k _ ih => rw [← hstep_eq, idowdsSeq_succ, idowdsSeq_succ, ih]
  refine ⟨K, fun k hk => (hconst k hk).trans ?_⟩
  funext i
  ext a
  rw [mem_idowdsLimit_iff]
  refine ⟨fun ha k => ?_, fun h => h K⟩
  rcases le_total k K with hk | hk
  · exact idowdsSeq_subset_of_le hk i ha
  · rwa [hconst k hk]

/-- On a finite game with nonempty strategy sets, the simultaneous `IDoWDS` limit `G.idowdsLimit i`
is nonempty for every player `i`. -/
theorem idowdsLimit_nonempty [Finite ι] [∀ j, Finite (S j)] [∀ j, Nonempty (S j)]
    (G : CostGame ι S) (i : ι) : (G.idowdsLimit i).Nonempty := by
  obtain ⟨K, hK⟩ := G.exists_idowdsSeq_eq_idowdsLimit
  rw [← hK K le_rfl]
  exact G.idowdsSeq_nonempty K i

/-- No strategy surviving simultaneous `IDoWDS` is weakly dominated in
`G.restrict G.idowdsLimit`. -/
theorem not_isWeaklyDominated_idowdsLimit [Finite ι] [∀ j, Finite (S j)] (G : CostGame ι S)
    (i : ι) (a : G.idowdsLimit i) :
    ¬ (G.restrict G.idowdsLimit).IsWeaklyDominated i a := by
  obtain ⟨K, hK⟩ := G.exists_idowdsSeq_eq_idowdsLimit
  have hK0 : G.idowdsSeq K = G.idowdsLimit := hK K le_rfl
  have hK1 : G.idowdsSeq (K + 1) = G.idowdsLimit := hK (K + 1) (Nat.le_succ K)
  have ha1 : a.val ∈ G.idowdsSeq (K + 1) i := hK1.symm ▸ a.property
  rw [idowdsSeq_succ] at ha1
  obtain ⟨haK, hnd⟩ := ha1
  generalize hL : G.idowdsSeq K = L at haK hnd hK0
  subst hK0
  exact hnd

theorem IDoSDSStep.idowdsStep {A B : ∀ i, Set (S i)} [∀ i, Nonempty (A i)]
    (h : G.IDoSDSStep A B) : G.IDoWDSStep A B :=
  ⟨h.1, fun i a ha hnot =>
    let ⟨b, hbA, _, hdom⟩ := h.2 i a ha hnot
    ⟨⟨b, hbA⟩, hdom.isWeaklyDominatedBy⟩⟩

/-- Deleting a single strictly dominated strategy `a₀ ∈ A i₀` (dominated by `b₀ ∈ A i₀`) is a valid
`IDoSDSStep` whenever all strategy subsets `A j` are nonempty. -/
theorem idosdsStep_erase_single {A : ∀ i, Set (S i)} [∀ j, Nonempty (A j)]
    {i₀ : ι} {a₀ b₀ : S i₀} (ha₀ : a₀ ∈ A i₀) (hb₀ : b₀ ∈ A i₀)
    (hdom : (G.restrict A).IsStrictlyDominatedBy i₀ ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩) :
    G.IDoSDSStep A (update A i₀ (A i₀ \ {a₀})) := by
  refine ⟨fun i => ?_, fun i a ha hnot => ?_⟩
  · by_cases hi : i = i₀
    · subst hi
      rw [update_self]
      exact Set.sdiff_subset
    · rw [update_of_ne hi]
  · by_cases hi : i = i₀
    · subst hi
      rw [update_self] at hnot ⊢
      obtain rfl : a = a₀ := not_not.1 fun hne => hnot ⟨ha, hne⟩
      have hb_ne : b₀ ≠ a := fun h => hdom.ne (Subtype.ext h.symm)
      exact ⟨b₀, hb₀, ⟨hb₀, hb_ne⟩, hdom⟩
    · rw [update_of_ne hi] at hnot
      exact (hnot ha).elim

/-- On a game with finite, nonempty strategy subsets `A i`, simultaneously deleting all strictly
dominated strategies of `G.restrict A` is a valid `IDoSDSStep`: by finiteness and transitivity of
strict dominance, every strictly dominated strategy is dominated by an undominated survivor. -/
theorem idosdsStep_simultaneous (A : ∀ i, Set (S i)) [∀ i, Finite (A i)] [∀ i, Nonempty (A i)] :
    G.IDoSDSStep A
      (fun i => {a | ∃ ha : a ∈ A i, ¬ (G.restrict A).IsStrictlyDominated i ⟨a, ha⟩}) := by
  have := fun i => Fintype.ofFinite (A i)
  refine ⟨fun i a ha => ha.1, fun i a ha hnot => ?_⟩
  obtain ⟨b₀, hb₀⟩ : (G.restrict A).IsStrictlyDominated i ⟨a, ha⟩ :=
    not_not.1 fun hnd => hnot ⟨ha, hnd⟩
  classical
  let domSet : Finset (A i) :=
    univ.filter fun b => (G.restrict A).IsStrictlyDominatedBy i ⟨a, ha⟩ b
  have hne : domSet.Nonempty := ⟨b₀, mem_filter.2 ⟨mem_univ _, hb₀⟩⟩
  obtain ⟨bMin, hbMin_mem, hbMin_min⟩ := domSet.exists_min_image
    (fun b => (univ.filter fun c : A i => (G.restrict A).IsStrictlyDominatedBy i b c).card) hne
  have habMin : (G.restrict A).IsStrictlyDominatedBy i ⟨a, ha⟩ bMin :=
    (mem_filter.1 hbMin_mem).2
  have hndMin : ¬ (G.restrict A).IsStrictlyDominated i bMin := by
    rintro ⟨c, hbc⟩
    have hsub : (univ.filter fun d : A i => (G.restrict A).IsStrictlyDominatedBy i c d) ⊂
        (univ.filter fun d : A i => (G.restrict A).IsStrictlyDominatedBy i bMin d) := by
      refine (ssubset_iff_of_subset fun d hd => ?_).2 ⟨c, ?_, fun h => (mem_filter.1 h).2.ne rfl⟩
      · exact mem_filter.2 ⟨mem_univ _, hbc.trans (mem_filter.1 hd).2⟩
      · exact mem_filter.2 ⟨mem_univ _, hbc⟩
    exact (Finset.card_lt_card hsub).not_ge
      (hbMin_min c (mem_filter.2 ⟨mem_univ _, habMin.trans hbc⟩))
  exact ⟨bMin.val, bMin.property, ⟨bMin.property, hndMin⟩, habMin⟩

private theorem IDoSDSStep.isPureNash_restrict_iff {A B : ∀ i, Set (S i)}
    (hstep : G.IDoSDSStep A B) (s : ∀ i, S i) :
    (∃ hsA : ∀ i, s i ∈ A i, (G.restrict A).IsPureNash fun i => ⟨s i, hsA i⟩) ↔
      ∃ hsB : ∀ i, s i ∈ B i, (G.restrict B).IsPureNash fun i => ⟨s i, hsB i⟩ := by
  constructor
  · rintro ⟨hsA, hpA⟩
    have hsB : ∀ i, s i ∈ B i := fun i => by
      by_contra hni
      obtain ⟨b, hbA, -, hdom⟩ := hstep.2 i (s i) (hsA i) hni
      exact hpA.not_isStrictlyDominated i ⟨⟨b, hbA⟩, hdom⟩
    refine ⟨hsB, fun i b => ?_⟩
    have h := hpA i ⟨b.val, hstep.1 i b.property⟩
    rw [restrict_cost_update] at h ⊢
    exact h
  · rintro ⟨hsB, hpB⟩
    have hsA : ∀ i, s i ∈ A i := fun i => hstep.1 i (hsB i)
    refine ⟨hsA, fun i a => ?_⟩
    by_cases haB : a.val ∈ B i
    · have h := hpB i ⟨a.val, haB⟩
      rw [restrict_cost_update] at h ⊢
      exact h
    · obtain ⟨b, hbA, hbB, hdom⟩ := hstep.2 i a.val a.property haB
      have h := hpB i ⟨b, hbB⟩
      have hlt := hdom fun j => ⟨s j, hsA j⟩
      simp only [restrict_cost_update] at h hlt ⊢
      exact h.trans hlt.le

/-- **Iterated deletion of strictly dominated strategies preserves pure Nash equilibria**: if
`G.IDoSDS (fun _ => Set.univ) A` (where each `IDoSDSStep` requires a surviving pure dominator in
the restricted game), then the pure Nash equilibria of `G` are in bijection with those of
`G.restrict A`. -/
theorem IDoSDS.isPureNash_iff {A : ∀ i, Set (S i)}
    (h : G.IDoSDS (fun _ => Set.univ) A) (s : ∀ i, S i) :
    G.IsPureNash s ↔ ∃ hs : ∀ i, s i ∈ A i, (G.restrict A).IsPureNash fun i => ⟨s i, hs i⟩ := by
  rw [isPureNash_iff_restrict (A := fun _ => Set.univ) (fun _ _ ha => (ha trivial).elim) s]
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hstep.isPureNash_restrict_iff s)

/-- **Unique pure Nash equilibrium from `IDoSDS`**: if iterated deletion of strictly dominated
strategies leaves a single profile `sStar`, then `sStar` is the unique pure Nash equilibrium of
`G`. -/
theorem IDoSDS.isPureNash_iff_eq_of_singleton {sStar : ∀ i, S i}
    (h : G.IDoSDS (fun _ => Set.univ) (fun i => {sStar i})) (s : ∀ i, S i) :
    G.IsPureNash s ↔ s = sStar := by
  rw [h.isPureNash_iff]
  constructor
  · rintro ⟨hs, _⟩
    funext i
    exact hs i
  · rintro rfl
    refine ⟨fun _ => rfl, fun i a => ?_⟩
    have ha : a = ⟨s i, rfl⟩ := Subtype.ext a.property
    rw [ha, update_eq_self]

section MixedIDoSDS

variable [Fintype ι] [∀ i, Fintype (S i)]

private theorem deviationCost_lt_of_restrict_strictlyDominatedBy {A : ∀ i, Set (S i)}
    {p : ∀ i, S i → ℝ} (hp : ∀ i, IsMixedStrategy (p i))
    (hsupp : ∀ i a, a ∉ A i → p i a = 0)
    {i : ι} {a b : S i} (ha : a ∈ A i) (hb : b ∈ A i)
    (hdom : (G.restrict A).IsStrictlyDominatedBy i ⟨a, ha⟩ ⟨b, hb⟩) :
    G.deviationCost p i b < G.deviationCost p i a := by
  rw [deviationCost_def, deviationCost_def]
  obtain ⟨s₀, hs₀⟩ := exists_productWeight_pos hp
  have hlt : ∀ {s : ∀ j, S j}, 0 < productWeight p s →
      G.cost i (update s i b) < G.cost i (update s i a) := by
    intro s hs
    have hA : ∀ j, s j ∈ A j := fun j => Classical.by_contradiction fun hj => hs.ne' <| by
      rw [productWeight_def]
      exact prod_eq_zero (mem_univ j) (hsupp j (s j) hj)
    simpa only [restrict_cost_update] using hdom fun j => ⟨s j, hA j⟩
  refine sum_lt_sum (fun s _ => ?_) ⟨s₀, mem_univ s₀, mul_lt_mul_of_pos_left (hlt hs₀) hs₀⟩
  rcases (productWeight_nonneg (fun j => (hp j).nonneg) s).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (hlt hpos).le hpos.le

private theorem IDoSDSStep.supported_mixedNash_iff {A B : ∀ i, Set (S i)}
    (hstep : G.IDoSDSStep A B) (p : ∀ i, S i → ℝ) :
    ((∀ i, IsMixedStrategy (p i)) ∧ (∀ i a, a ∉ A i → p i a = 0) ∧
        ∀ i, ∀ a ∈ A i, G.expectedCost p i ≤ G.deviationCost p i a) ↔
      (∀ i, IsMixedStrategy (p i)) ∧ (∀ i a, a ∉ B i → p i a = 0) ∧
        ∀ i, ∀ b ∈ B i, G.expectedCost p i ≤ G.deviationCost p i b := by
  constructor
  · rintro ⟨hp, hsuppA, hleA⟩
    have hsuppB : ∀ i a, a ∉ B i → p i a = 0 := fun i a haB => by
      by_cases haA : a ∈ A i
      · rcases ((hp i).nonneg a).eq_or_lt with h0 | hpos
        · exact h0.symm
        · obtain ⟨b, hbA, -, hdom⟩ := hstep.2 i a haA haB
          have hdev_lt := deviationCost_lt_of_restrict_strictlyDominatedBy hp hsuppA haA hbA hdom
          -- Since `p i a > 0` and `p` is optimal across `A i` (which contains its support),
          -- `deviationCost p i a` must equal `expectedCost p i`, contradicting `b ∈ A i`.
          have hsum_eq : ∑ c, p i c * G.expectedCost p i < ∑ c, p i c * G.deviationCost p i c := by
            refine sum_lt_sum (fun c _ => ?_) ⟨a, mem_univ a, ?_⟩
            · by_cases hcA : c ∈ A i
              · exact mul_le_mul_of_nonneg_left (hleA i c hcA) ((hp i).nonneg c)
              · rw [hsuppA i c hcA, zero_mul, zero_mul]
            · exact mul_lt_mul_of_pos_left ((hleA i b hbA).trans_lt hdev_lt) hpos
          rw [← sum_mul, (hp i).sum_eq_one, one_mul,
            G.sum_mul_deviationCost_eq_expectedCost p (hp i).sum_eq_one] at hsum_eq
          exact (lt_irrefl _ hsum_eq).elim
      · exact hsuppA i a haA
    exact ⟨hp, hsuppB, fun i b hbB => hleA i b (hstep.1 i hbB)⟩
  · rintro ⟨hp, hsuppB, hleB⟩
    have hsuppA : ∀ i a, a ∉ A i → p i a = 0 :=
      fun i a haA => hsuppB i a fun haB => haA (hstep.1 i haB)
    refine ⟨hp, hsuppA, fun i a haA => ?_⟩
    by_cases haB : a ∈ B i
    · exact hleB i a haB
    · obtain ⟨b, hbA, hbB, hdom⟩ := hstep.2 i a haA haB
      exact (hleB i b hbB).trans
        (deviationCost_lt_of_restrict_strictlyDominatedBy hp hsuppA haA hbA hdom).le

/-- **Iterated deletion of strictly dominated strategies preserves mixed Nash equilibria**: if
`G.IDoSDS (fun _ => Set.univ) A` (where each `IDoSDSStep` requires a surviving pure dominator in
the restricted game), then `p` is a mixed Nash equilibrium of `G` iff `p` vanishes outside `A` and
its restriction is a mixed Nash equilibrium of `G.restrict A`. -/
theorem IDoSDS.isMixedNash_iff_restrict {A : ∀ i, Set (S i)} [∀ i, Fintype (A i)]
    (h : G.IDoSDS (fun _ => Set.univ) A) (p : ∀ i, S i → ℝ) :
    G.IsMixedNash p ↔
      (∀ i a, a ∉ A i → p i a = 0) ∧ (G.restrict A).IsMixedNash fun i a => p i a.val := by
  rw [isMixedNash_restrict_iff_supported]
  have huniv : G.IsMixedNash p ↔
      (∀ i, IsMixedStrategy (p i)) ∧
        (∀ i a, a ∉ (fun _ => Set.univ : ∀ i, Set (S i)) i → p i a = 0) ∧
        ∀ i, ∀ a ∈ (fun _ => Set.univ : ∀ i, Set (S i)) i,
          G.expectedCost p i ≤ G.deviationCost p i a := by
    simp only [IsMixedNash, Set.mem_univ, not_true_eq_false, IsEmpty.forall_iff, implies_true,
      forall_const, true_and]
  rw [huniv]
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hstep.supported_mixedNash_iff p)

/-- **Unique mixed Nash equilibrium from `IDoSDS`**: if iterated deletion of strictly dominated
strategies leaves a single profile `sStar`, then `fun i => Pi.single (sStar i) 1` is the unique
mixed Nash equilibrium of `G`. -/
theorem IDoSDS.isMixedNash_iff_eq_single_of_singleton [∀ i, DecidableEq (S i)] {sStar : ∀ i, S i}
    (h : G.IDoSDS (fun _ => Set.univ) (fun i => {sStar i})) (p : ∀ i, S i → ℝ) :
    G.IsMixedNash p ↔ p = fun i => Pi.single (sStar i) 1 := by
  rw [h.isMixedNash_iff_restrict p, isMixedNash_restrict_iff_supported]
  constructor
  · rintro ⟨hp, hzero, -⟩
    funext i a
    by_cases ha : a = sStar i
    · subst ha
      have hsum := (hp i).sum_eq_one
      rw [Fintype.sum_eq_single (sStar i) (hzero i)] at hsum
      simpa only [Pi.single_eq_same] using hsum
    · rw [Pi.single_eq_of_ne ha]
      exact hzero i a ha
  · rintro rfl
    refine ⟨fun i => isMixedStrategy_single (sStar i), fun i a ha => Pi.single_eq_of_ne ha _, ?_⟩
    rintro i a (rfl : a = sStar i)
    rw [expectedCost_single, deviationCost_single, update_eq_self]

end MixedIDoSDS

end IteratedDeletion

end Restriction

/-! ### Theorem 4.13: Swap regret bounds weight on `ε`-strictly dominated strategies -/

section SwapRegretDominance

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)]
  (G : CostGame ι S)

/-- **Swap regret bounds the weight on actions `ε`-strictly dominated by mixed strategies**
([BlumMansour2007AGT], Section 4.4.4 and Theorem 4.13, pp. 91–92): if over `T > 0` rounds every
player plays mixed strategies `p t` and player `i` has swap regret at most `R` against its
`deviationCost` sequence, then for any set `D` of strategies each `ε`-strictly dominated by some
mixed strategy (`ε > 0`), the time-averaged probability mass player `i` places on `D` is at most
`R / (ε * T)`. -/
theorem timeAverage_weight_isEpsStrictlyDominatedMixed_set_le
    {p : ℕ → ∀ j, S j → ℝ} {T : ℕ} (hT : 0 < T)
    (hp : ∀ t j, IsMixedStrategy (p t j))
    {i : ι} {R ε : ℝ} (hε : 0 < ε)
    (hR : ∀ δ : S i → S i,
      ∑ t ∈ range T, ∑ a, p t i a * G.deviationCost (p t) i a
        ≤ ∑ t ∈ range T, ∑ a, p t i a * G.deviationCost (p t) i (δ a) + R)
    (D : Finset (S i)) (hD : ∀ a ∈ D, G.IsEpsStrictlyDominatedMixed ε i a) :
    (∑ t ∈ range T, ∑ a ∈ D, p t i a) / (T : ℝ) ≤ R / (ε * T) := by
  classical
  have hchoose : ∀ a : S i, ∃ b : S i,
      a ∈ D → ∑ t ∈ range T, p t i a * G.deviationCost (p t) i b +
          ε * ∑ t ∈ range T, p t i a ≤
        ∑ t ∈ range T, p t i a * G.deviationCost (p t) i a := by
    intro a
    by_cases ha : a ∈ D
    · obtain ⟨q, hq⟩ := hD a ha
      have hne : (univ : Finset (S i)).Nonempty := ⟨a, mem_univ a⟩
      obtain ⟨bMin, _, hbMin⟩ := univ.exists_min_image
        (fun b : S i => ∑ t ∈ range T, p t i a * G.deviationCost (p t) i b) hne
      refine ⟨bMin, fun _ => ?_⟩
      have hmin_le : ∑ t ∈ range T, p t i a * G.deviationCost (p t) i bMin ≤
          ∑ b : S i, q b * ∑ t ∈ range T, p t i a * G.deviationCost (p t) i b := by
        calc ∑ t ∈ range T, p t i a * G.deviationCost (p t) i bMin
            = ∑ b : S i, q b * ∑ t ∈ range T, p t i a * G.deviationCost (p t) i bMin := by
              rw [← sum_mul, hq.1.sum_eq_one, one_mul]
          _ ≤ ∑ b : S i, q b * ∑ t ∈ range T, p t i a * G.deviationCost (p t) i b :=
              sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hbMin b (mem_univ b)) (hq.1.nonneg b)
      have havg : ∑ b : S i, q b * ∑ t ∈ range T, p t i a * G.deviationCost (p t) i b =
          ∑ t ∈ range T, p t i a * ∑ b : S i, q b * G.deviationCost (p t) i b := by
        simp_rw [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun t _ => sum_congr rfl fun b _ => by ring
      have hstep : ∑ t ∈ range T, p t i a * (∑ b : S i, q b * G.deviationCost (p t) i b) +
          ε * ∑ t ∈ range T, p t i a ≤
          ∑ t ∈ range T, p t i a * G.deviationCost (p t) i a := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_le_sum fun t _ => ?_
        have hdom := hq.sum_mul_deviationCost_add_le (hp t)
        have hmul := mul_le_mul_of_nonneg_left hdom ((hp t i).nonneg a)
        linarith
      linarith [hmin_le, havg, hstep]
    · exact ⟨a, fun h => (ha h).elim⟩
  let δ : S i → S i := fun a => if a ∈ D then (hchoose a).choose else a
  have hby_action : ∑ a : S i, (if a ∈ D then ε * ∑ t ∈ range T, p t i a else 0) +
      ∑ a : S i, ∑ t ∈ range T, p t i a * G.deviationCost (p t) i (δ a) ≤
      ∑ a : S i, ∑ t ∈ range T, p t i a * G.deviationCost (p t) i a := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun a _ => ?_
    dsimp only [δ]
    split_ifs with ha
    · linarith [(hchoose a).choose_spec ha]
    · rw [zero_add]
  have hD_sum : ∑ a : S i, (if a ∈ D then ε * ∑ t ∈ range T, p t i a else 0) =
      ε * ∑ t ∈ range T, ∑ a ∈ D, p t i a := by
    rw [sum_ite_mem, univ_inter, ← mul_sum, sum_comm]
  rw [hD_sum, sum_comm (s := univ) (t := range T),
    sum_comm (s := univ) (t := range T)] at hby_action
  have htot : ε * ∑ t ∈ range T, ∑ a ∈ D, p t i a ≤ R := by linarith [hR δ]
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.2 hT
  have hεT_pos : 0 < ε * T := mul_pos hε hT_pos
  rw [div_le_div_iff₀ hT_pos hεT_pos]
  nlinarith

/-- Single-action mixed-dominance form of **Theorem 4.13** ([BlumMansour2007AGT], Section 4.4.4,
pp. 91–92). -/
theorem timeAverage_weight_isEpsStrictlyDominatedMixed_le
    {p : ℕ → ∀ j, S j → ℝ} {T : ℕ} (hT : 0 < T)
    (hp : ∀ t j, IsMixedStrategy (p t j))
    {i : ι} {R ε : ℝ} (hε : 0 < ε)
    (hR : ∀ δ : S i → S i,
      ∑ t ∈ range T, ∑ b, p t i b * G.deviationCost (p t) i b
        ≤ ∑ t ∈ range T, ∑ b, p t i b * G.deviationCost (p t) i (δ b) + R)
    {a : S i} (ha : G.IsEpsStrictlyDominatedMixed ε i a) :
    (∑ t ∈ range T, p t i a) / (T : ℝ) ≤ R / (ε * T) := by
  classical
  simpa only [sum_singleton] using
    G.timeAverage_weight_isEpsStrictlyDominatedMixed_set_le hT hp hε hR {a}
      (fun b hb => (mem_singleton.1 hb) ▸ ha)

end SwapRegretDominance

end Cslib.GameTheory.CostGame
