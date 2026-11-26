/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Dominance
public import CslibFrontier.GameTheory.Strategic.StrongNash

/-!
# Payoff-maximization strategic games, coalitional resilience, and `IDoWDS`

This module defines normal-form strategic games in utility-maximization form (`PayoffGame`), bridges
them to `Cslib.GameTheory.CostGame` via utility negation (`PayoffGame.toCostGame`), and develops:

* Pure Nash equilibria (`PayoffGame.IsPureNash`, `PayoffGame.IsStrictPureNash`) and `k`-resilient
  coalitional stability (`PayoffGame.IsCoalitionProofUpTo`), bridged to `CostGame.IsPureNash` and
  `CostGame.IsStrongNash`.
* Weak strategic dominance relative to strategy subsets (`PayoffGame.WeaklyDominatesOn`,
  `PayoffGame.IsWeaklyDominatedOn`), bridged directly to `CostGame.IsWeaklyDominatedBy` and
  `CostGame.IsWeaklyDominated` on `(G.toCostGame).restrict R`, and simultaneous **iterated deletion
  of weakly dominated strategies (`IDoWDS`)** (`PayoffGame.idowdsStep`, `PayoffGame.idowdsIter`),
  defined via `CostGame.idowdsSeq` on `G.toCostGame` ([DodisRabin2007], Definition 8.8, p. 200).
* Backward-induction weak dominance (`PayoffGame.HasBackwardInductionDominance`) for `T`-round
  cutoff games, proving `k`-step survival `≤ T - k` (`PayoffGame.idowdsIter_eq_le_sub`) and
  collapse to `"never participate"` `{0}` after `T` steps
  (`PayoffGame.idowdsIter_eq_singleton_zero`).

## Main definitions

* `Cslib.GameTheory.PayoffGame`: strategic game in utility-maximization form.
* `Cslib.GameTheory.PayoffGame.toCostGame`: cost-minimization game with `cost i s = -payoff i s`.
* `Cslib.GameTheory.PayoffGame.IsPureNash`, `Cslib.GameTheory.PayoffGame.IsStrictPureNash`:
  weak and strict pure Nash equilibria.
* `Cslib.GameTheory.PayoffGame.IsCoalitionProofUpTo`: `k`-resilient coalitional stability.
* `Cslib.GameTheory.PayoffGame.WeaklyDominatesOn`,
  `Cslib.GameTheory.PayoffGame.IsWeaklyDominatedOn`,
  `Cslib.GameTheory.PayoffGame.idowdsStep`, `Cslib.GameTheory.PayoffGame.idowdsIter`:
  weak dominance and simultaneous `IDoWDS`.
* `Cslib.GameTheory.PayoffGame.HasBackwardInductionDominance`: backward-induction weak dominance
  condition on `T`-round cutoff games.

## Main results

* `Cslib.GameTheory.PayoffGame.isPureNash_toCostGame_iff`,
  `Cslib.GameTheory.PayoffGame.IsCoalitionProofUpTo.isStrongNash_toCostGame`: bridges to
  `CostGame` equilibrium notions.
* `Cslib.GameTheory.PayoffGame.weaklyDominatesOn_iff_toCostGame`,
  `Cslib.GameTheory.PayoffGame.isWeaklyDominatedOn_iff_toCostGame`,
  `Cslib.GameTheory.PayoffGame.idowdsIter_eq_toCostGame_idowdsSeq`: exact correspondence between
  `PayoffGame` weak dominance/`IDoWDS` and `CostGame` weak dominance/`idowdsSeq`.
* `Cslib.GameTheory.PayoffGame.idowdsIter_eq_le_sub`,
  `Cslib.GameTheory.PayoffGame.idowdsIter_eq_singleton_zero`: `T`-round backward-induction collapse.

## References

* [I. Abraham, D. Dolev, R. Gonen, J. Y. Halpern,
  *Distributed Computing Meets Game Theory*][AbrahamDolevGonenHalpern2006]
* [Y. Dodis and T. Rabin, *Cryptography and Game Theory*][DodisRabin2007], Section 8.4.1 and
  Definition 8.8
* [J. Y. Halpern and V. Teague,
  *Rational Secret Sharing and Multiparty Computation*][HalpernTeague2004]
-/

public section

namespace Cslib.GameTheory

/-- A strategic (normal-form) game in **utility-maximization form**: player `i` chooses a strategy
in `S i`, and `payoff i s` is player `i`'s real-valued utility at profile `s : ∀ i, S i`. -/
structure PayoffGame (ι : Type*) (S : ι → Type*) where
  /-- The utility of player `i` at strategy profile `s`. -/
  payoff : ι → (∀ i, S i) → ℝ

namespace PayoffGame

section General

variable {ι : Type*} {S : ι → Type*} (G : PayoffGame ι S)

/-- View a payoff-maximization game as a `CostGame` with negated utilities `-payoff i s`. -/
@[expose] def toCostGame : CostGame ι S where
  cost i s := -G.payoff i s

@[simp]
theorem toCostGame_cost (i : ι) (s : ∀ i, S i) :
    G.toCostGame.cost i s = -G.payoff i s :=
  rfl

section DecidablePlayer

variable [DecidableEq ι]

/-- A profile `s` is a **pure Nash equilibrium** if no player can strictly increase its payoff by a
unilateral deviation. -/
@[expose] def IsPureNash (s : ∀ i, S i) : Prop :=
  ∀ i (a : S i), G.payoff i (Function.update s i a) ≤ G.payoff i s

/-- A profile `s` is a **strict pure Nash equilibrium** if every non-equilibrium unilateral
deviation `a ≠ s i` strictly decreases the deviating player's payoff. -/
@[expose] def IsStrictPureNash (s : ∀ i, S i) : Prop :=
  ∀ i (a : S i), a ≠ s i → G.payoff i (Function.update s i a) < G.payoff i s

/-- Pure Nash equilibria of `G` coincide with pure Nash equilibria of `G.toCostGame`. -/
theorem isPureNash_toCostGame_iff {s : ∀ i, S i} :
    G.toCostGame.IsPureNash s ↔ G.IsPureNash s := by
  simp only [CostGame.IsPureNash, IsPureNash, toCostGame_cost, neg_le_neg_iff]

/-- Every strict pure Nash equilibrium is a pure Nash equilibrium. -/
theorem IsStrictPureNash.isPureNash {G : PayoffGame ι S} {s : ∀ i, S i}
    (h : G.IsStrictPureNash s) : G.IsPureNash s :=
  fun i a => (eq_or_ne a (s i)).elim (fun ha => by simp [ha]) fun hne => (h i a hne).le

/-- A profile `s` is **coalition-proof up to size `k`** (`k`-resilient in the strong uniform sense
that no member of a deviating coalition of size at most `k` strictly gains; compare
[DodisRabin2007], Section 8.4.1, and [AbrahamDolevGonenHalpern2006]) if for every coalition `C`
with `C.card ≤ k` and every joint deviation `t`, every member `i ∈ C` has payoff at most
`G.payoff i s`. -/
@[expose] def IsCoalitionProofUpTo (k : ℕ) (s : ∀ i, S i) : Prop :=
  ∀ (C : Finset ι), C.card ≤ k → ∀ (t : ∀ i, S i), ∀ i ∈ C,
    G.payoff i (C.piecewise t s) ≤ G.payoff i s

/-- Coalition-proofness up to `k ≥ 1` implies `IsPureNash` via singleton coalitions. -/
theorem IsCoalitionProofUpTo.isPureNash {G : PayoffGame ι S} {k : ℕ} {s : ∀ i, S i}
    (h : G.IsCoalitionProofUpTo k s) (hk : 1 ≤ k) : G.IsPureNash s := fun i a => by
  simpa [Finset.piecewise_singleton] using
    h {i} (by simp [hk]) (Function.update s i a) i (Finset.mem_singleton_self i)

/-- Coalition-proofness up to `Fintype.card ι` implies `CostGame.IsStrongNash` on `G.toCostGame`. -/
theorem IsCoalitionProofUpTo.isStrongNash_toCostGame [Fintype ι] {G : PayoffGame ι S} {k : ℕ}
    {s : ∀ i, S i} (h : G.IsCoalitionProofUpTo k s) (hk : Fintype.card ι ≤ k) :
    G.toCostGame.IsStrongNash s := by
  rintro C t ⟨_, i, hi, hlt⟩
  simp only [toCostGame_cost, neg_lt_neg_iff] at hlt
  exact (h C (C.card_le_univ.trans hk) t i hi).not_gt hlt

/-- Strategy `a` **weakly dominates** strategy `b` for player `i` relative to surviving strategy
sets `R` ([DodisRabin2007], Definition 8.8; [HalpernTeague2004]): `a` is at least as good as `b`
against all profiles in `R`, and strictly better against at least one profile in `R`. -/
@[expose] def WeaklyDominatesOn (R : ∀ i, Set (S i)) (i : ι) (a b : S i) : Prop :=
  (∀ s : ∀ j, S j, (∀ j, s j ∈ R j) →
      G.payoff i (Function.update s i b) ≤ G.payoff i (Function.update s i a)) ∧
    ∃ s : ∀ j, S j, (∀ j, s j ∈ R j) ∧
      G.payoff i (Function.update s i b) < G.payoff i (Function.update s i a)

/-- Strategy `b` of player `i` is **weakly dominated** in `R` if some strategy `a ∈ R i` weakly
dominates `b` relative to `R`. -/
@[expose] def IsWeaklyDominatedOn (R : ∀ i, Set (S i)) (i : ι) (b : S i) : Prop :=
  ∃ a ∈ R i, G.WeaklyDominatesOn R i a b

/-- Weak dominance in `PayoffGame` on `R` coincides with weak dominance in the restricted
negated-utility `CostGame`. -/
theorem weaklyDominatesOn_iff_toCostGame {R : ∀ j, Set (S j)} {i : ι} {a b : S i}
    (ha : a ∈ R i) (hb : b ∈ R i) :
    G.WeaklyDominatesOn R i a b ↔
      (G.toCostGame.restrict R).IsWeaklyDominatedBy i ⟨b, hb⟩ ⟨a, ha⟩ := by
  have hcoe (r : ∀ j, R j) (x : R i) :
      (fun j => ((Function.update r i x j : R j) : S j)) =
        Function.update (fun j => (r j : S j)) i x.1 :=
    funext (Function.apply_update (fun j (y : R j) => (y : S j)) r i x)
  simp only [WeaklyDominatesOn, CostGame.IsWeaklyDominatedBy, CostGame.restrict_cost,
    toCostGame_cost, hcoe, neg_le_neg_iff, neg_lt_neg_iff]
  exact ⟨fun ⟨hle, s, hs, hlt⟩ =>
      ⟨fun r => hle _ fun j => (r j).2, ⟨fun j => ⟨s j, hs j⟩, hlt⟩⟩,
    fun ⟨hle, r, hlt⟩ =>
      ⟨fun s hs => hle fun j => ⟨s j, hs j⟩, fun j => (r j).1, fun j => (r j).2, hlt⟩⟩

/-- Weakly dominated strategies in `PayoffGame` on `R` coincide with `CostGame.IsWeaklyDominated`
on `G.toCostGame.restrict R` ([DodisRabin2007], Definition 8.8). -/
theorem isWeaklyDominatedOn_iff_toCostGame {R : ∀ j, Set (S j)} {i : ι} {b : S i}
    (hb : b ∈ R i) :
    G.IsWeaklyDominatedOn R i b ↔
      (G.toCostGame.restrict R).IsWeaklyDominated i ⟨b, hb⟩ :=
  ⟨fun ⟨a, ha, hdom⟩ => ⟨⟨a, ha⟩, (G.weaklyDominatesOn_iff_toCostGame ha hb).mp hdom⟩,
    fun ⟨⟨a, ha⟩, hdom⟩ => ⟨a, ha, (G.weaklyDominatesOn_iff_toCostGame ha hb).mpr hdom⟩⟩

/-- One simultaneous round of **deletion of weakly dominated strategies** ([DodisRabin2007],
Definition 8.8). -/
def idowdsStep (R : ∀ i, Set (S i)) : ∀ i, Set (S i) :=
  fun i => { b ∈ R i | ¬ G.IsWeaklyDominatedOn R i b }

@[simp]
theorem mem_idowdsStep_iff {R : ∀ i, Set (S i)} {i : ι} {b : S i} :
    b ∈ G.idowdsStep R i ↔ b ∈ R i ∧ ¬ G.IsWeaklyDominatedOn R i b := by
  rfl

/-- `idowdsStep` matches one simultaneous step of `CostGame.idowdsSeq` on `G.toCostGame`. -/
theorem idowdsStep_eq_cost (R : ∀ i, Set (S i)) :
    G.idowdsStep R = fun i =>
      { b | ∃ hb : b ∈ R i, ¬ (G.toCostGame.restrict R).IsWeaklyDominated i ⟨b, hb⟩ } := by
  funext i
  ext b
  simp only [mem_idowdsStep_iff, Set.mem_ofPred_eq]
  exact ⟨fun ⟨hb, hnd⟩ => ⟨hb, mt (G.isWeaklyDominatedOn_iff_toCostGame hb).mpr hnd⟩,
    fun ⟨hb, hnd⟩ => ⟨hb, mt (G.isWeaklyDominatedOn_iff_toCostGame hb).mp hnd⟩⟩

/-- `k`-fold **iterated deletion of weakly dominated strategies (`IDoWDS`)**, backed directly by
`CostGame.idowdsSeq` on `G.toCostGame` ([DodisRabin2007], Definition 8.8). -/
def idowdsIter (k : ℕ) : ∀ i, Set (S i) :=
  G.toCostGame.idowdsSeq k

theorem idowdsIter_eq_toCostGame_idowdsSeq (k : ℕ) :
    G.idowdsIter k = G.toCostGame.idowdsSeq k := by
  rfl

@[simp]
theorem idowdsIter_zero : G.idowdsIter 0 = fun _ => Set.univ := by
  rw [idowdsIter_eq_toCostGame_idowdsSeq, CostGame.idowdsSeq_zero]

theorem idowdsIter_succ (k : ℕ) : G.idowdsIter (k + 1) = G.idowdsStep (G.idowdsIter k) := by
  rw [idowdsIter, CostGame.idowdsSeq_succ, ← idowdsIter_eq_toCostGame_idowdsSeq]
  exact (G.idowdsStep_eq_cost (G.idowdsIter k)).symm

@[simp]
theorem mem_idowdsIter_succ_iff {k : ℕ} {i : ι} {b : S i} :
    b ∈ G.idowdsIter (k + 1) i ↔
      b ∈ G.idowdsIter k i ∧ ¬ G.IsWeaklyDominatedOn (G.idowdsIter k) i b := by
  rw [idowdsIter_succ, mem_idowdsStep_iff]

/-- Every stage of `G.idowdsIter` is reachable by relational `CostGame.IDoWDS` on `G.toCostGame`.
-/
theorem idowds_toCostGame_idowdsIter (k : ℕ) :
    G.toCostGame.IDoWDS (fun _ => Set.univ) (G.idowdsIter k) :=
  G.toCostGame.idowds_idowdsSeq k

/-- On a finite game with nonempty strategy sets, every stage of `G.idowdsIter` retains at least
one strategy per player. -/
theorem idowdsIter_nonempty [Finite ι] [∀ j, Finite (S j)] [∀ j, Nonempty (S j)]
    (k : ℕ) (i : ι) : (G.idowdsIter k i).Nonempty :=
  G.toCostGame.idowdsSeq_nonempty k i

/-- No strategy weakly dominates itself. -/
theorem not_weaklyDominatesOn_self (R : ∀ i, Set (S i)) (i : ι) (a : S i) :
    ¬ G.WeaklyDominatesOn R i a a := by
  rintro ⟨_, s, _, hlt⟩
  exact lt_irrefl _ hlt

end DecidablePlayer

end General

/-! ### General `T`-round backward-induction weak-dominance collapse -/

section BackwardInduction

variable {ι : Type*} [DecidableEq ι] {T : ℕ}

/-- A `T`-round cutoff game on `Fin (T + 1)` (`0` = never broadcast, `m + 1` = participate through
round `m + 1`) has **backward-induction weak dominance** if at every active horizon `m < T`, once
cutoffs above `m + 1` have been eliminated, stopping at `m` weakly dominates continuing to `m + 1`
and no cutoff `≤ m` is weakly dominated. -/
@[expose] def HasBackwardInductionDominance (G : PayoffGame ι (fun _ => Fin (T + 1))) : Prop :=
  ∀ m (hm : m < T),
    let R : ∀ _ : ι, Set (Fin (T + 1)) := fun _ => { r | r.val ≤ m + 1 }
    (∀ i, G.WeaklyDominatesOn R i ⟨m, by omega⟩ ⟨m + 1, by omega⟩) ∧
      ∀ i (r : Fin (T + 1)), r.val ≤ m → ¬ G.IsWeaklyDominatedOn R i r

private theorem idowdsStep_cutoff_eq {G : PayoffGame ι (fun _ => Fin (T + 1))}
    (hbi : G.HasBackwardInductionDominance) {m : ℕ} (hm : m < T) :
    G.idowdsStep (fun _ => { r : Fin (T + 1) | r.val ≤ m + 1 }) =
      fun _ => { r : Fin (T + 1) | r.val ≤ m } := by
  obtain ⟨hdom, hsurv⟩ := hbi m hm
  funext i
  ext r
  simp only [mem_idowdsStep_iff, Set.mem_ofPred_eq]
  refine ⟨fun ⟨hrle, hndom⟩ => ?_, fun hrle => ⟨Nat.le_succ_of_le hrle, hsurv i r hrle⟩⟩
  rcases Nat.eq_or_lt_of_le hrle with heq | hlt
  · rw [show r = ⟨m + 1, by omega⟩ from Fin.ext heq] at hndom
    exact (hndom ⟨⟨m, by omega⟩, Nat.le_succ m, hdom i⟩).elim
  · omega

/-- Under `HasBackwardInductionDominance`, after `k ≤ T` rounds of `IDoWDS`, the surviving
strategies of every player are precisely the cutoffs `r ≤ T - k`. -/
theorem idowdsIter_eq_le_sub {G : PayoffGame ι (fun _ => Fin (T + 1))}
    (hbi : G.HasBackwardInductionDominance) {k : ℕ} (hk : k ≤ T) :
    G.idowdsIter k = fun _ => { r : Fin (T + 1) | r.val ≤ T - k } := by
  induction k with
  | zero =>
    funext i
    ext r
    simp [Nat.le_of_lt_succ r.isLt]
  | succ k ih =>
    rw [idowdsIter_succ, ih (Nat.le_of_succ_le hk), show T - k = (T - (k + 1)) + 1 by omega]
    exact idowdsStep_cutoff_eq hbi (by omega)

/-- **Abstract Halpern–Teague backward-induction collapse**: in any `T`-round cutoff mechanism with
backward-induction weak dominance, `T` rounds of `IDoWDS` eliminate every positive participation
horizon and leave only `{0}` (`"never broadcast"`). -/
theorem idowdsIter_eq_singleton_zero {G : PayoffGame ι (fun _ => Fin (T + 1))}
    (hbi : G.HasBackwardInductionDominance) :
    G.idowdsIter T = fun _ => {0} := by
  rw [idowdsIter_eq_le_sub hbi le_rfl]
  funext i
  ext r
  simp only [Nat.sub_self, Set.mem_ofPred_eq, Nat.le_zero, Set.mem_singleton_iff, Fin.ext_iff,
    Fin.val_zero]

end BackwardInduction

end PayoffGame

end Cslib.GameTheory
