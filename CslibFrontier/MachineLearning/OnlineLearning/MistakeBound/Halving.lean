/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Littlestone
public import Mathlib.Data.Nat.Log

/-!
# The halving algorithm

The **plurality halving algorithm** [Littlestone1988, §3, Algorithm 1;
DanielySabatoBenDavidShalevShwartz2015] learns a finite class `C : Finset (α → β)`. It keeps the
concepts of `C` consistent with the history (`consistent C h`) and, among `default : β` and the
labels output on `x` by `consistent C h`, predicts the least label maximizing the number of
consistent voters (`halving`). Because only labels realized by `C` (plus `default`) are inspected,
`halving` is computable even when `β` is infinite (for example `ℕ` or `ℚ`); for `β = Bool`
(`default = false`, `false < true`), it coincides with Littlestone's majority vote with ties broken
towards `false`.

Whenever `halving` errs on `(x, y)` for a consistent target `c` (`c x = y`), `y` is among the
candidate labels, so the predicted label `ŷ ≠ y` received at least as many votes in `consistent C h`
as `y`. Because the two voter sets are disjoint, at least half of the consistent concepts are
eliminated (`two_pow_mistakesFrom_halving_le`). Thus `halving` makes at most `⌊log₂ |C|⌋` mistakes
(`mistakeBound_halving_le`, [Littlestone1988, §3, Theorem 1]). Using `Finset.exists_max_image` when
no order on `β` is given, `optimalMistakeBound C ≤ ⌊log₂ |C|⌋` holds for every nonempty
`[DecidableEq β]` (`optimalMistakeBound_le_log_card`, [Littlestone1988, §3, Theorem 2]), and
`littlestoneDim C ≤ ⌊log₂ |C|⌋` holds with no assumptions on `β` (`littlestoneDim_le_log_card`).

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.consistent`: the concepts of a finite class
  that are consistent with a history.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.halving`: the computable plurality halving
  algorithm.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakeBound_halving_le`:
  [Littlestone1988, §3, Theorem 1; DanielySabatoBenDavidShalevShwartz2015], plurality halving makes
  at most `⌊log₂ |C|⌋` mistakes.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.optimalMistakeBound_le_log_card`:
  [Littlestone1988, §3, Theorem 2], `optimalMistakeBound C ≤ ⌊log₂ |C|⌋` for every finite class over
  a nonempty label type.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.littlestoneDim_le_log_card`: the Littlestone
  dimension of a finite class is at most `⌊log₂ |C|⌋` for arbitrary label types `β`.

## References

* [A. Daniely, S. Sabato, S. Ben-David, S. Shalev-Shwartz, *Multiclass Learnability and the ERM
  Principle*][DanielySabatoBenDavidShalevShwartz2015]
* [N. Littlestone, *Learning quickly when irrelevant attributes abound: a new linear-threshold
  algorithm*][Littlestone1988]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

variable {α β : Type*}

section Consistent

variable [DecidableEq β]

/-- The concepts of the finite class `C` that agree with every example of the history `h`
(Littlestone's `CONSIST`). -/
@[expose] def consistent (C : Finset (α → β)) (h : List (α × β)) : Finset (α → β) :=
  C.filter fun c => ∀ p ∈ h, c p.1 = p.2

@[simp] theorem consistent_nil (C : Finset (α → β)) : consistent C [] = C := by
  ext; simp [consistent]

theorem consistent_append_singleton (C : Finset (α → β)) (h : List (α × β)) (x : α) (y : β) :
    consistent C (h ++ [(x, y)]) = (consistent C h).filter (fun c => c x = y) := by
  ext c
  simp only [consistent, Finset.mem_filter, List.mem_append, List.mem_singleton]
  exact ⟨fun ⟨hc, hp⟩ => ⟨⟨hc, fun p hp' => hp p (.inl hp')⟩, hp _ (.inr rfl)⟩,
    fun ⟨⟨hc, hp⟩, hxy⟩ => ⟨hc, fun p hp' => hp'.elim (hp p) (· ▸ hxy)⟩⟩

theorem coe_consistent (C : Finset (α → β)) (h : List (α × β)) :
    (consistent C h : Set (α → β)) = versionSpace (C : Set (α → β)) h := by
  ext c
  simp [consistent, versionSpace]

/-- Any learner `A` that always predicts a label with at least as many consistent voters as every
realizable label eliminates at least half of `consistent C h` on each mistake. -/
private theorem two_pow_mistakesFrom_le_of_card_filter_le (C : Finset (α → β))
    (A : OnlineLearner α β)
    (hvote : ∀ h x y, (∃ c ∈ consistent C h, c x = y) →
      ((consistent C h).filter (fun c => c x = y)).card ≤
        ((consistent C h).filter (fun c => c x = A h x)).card)
    (h S : List (α × β)) (hS : ∃ c ∈ consistent C h, ∀ p ∈ S, c p.1 = p.2) :
    2 ^ mistakesFrom A h S ≤ (consistent C h).card := by
  classical
  induction S generalizing h with
  | nil =>
    obtain ⟨c, hc, -⟩ := hS
    simpa using Finset.card_pos.mpr ⟨c, hc⟩
  | cons p S ih =>
    obtain ⟨x, y⟩ := p
    obtain ⟨c, hc, hcS⟩ := hS
    have hcx : c x = y := hcS (x, y) List.mem_cons_self
    have ih' := ih (h ++ [(x, y)]) ⟨c, by
        rw [consistent_append_singleton]
        exact Finset.mem_filter.mpr ⟨hc, hcx⟩,
      fun q hq => hcS q (List.mem_cons_of_mem _ hq)⟩
    rw [consistent_append_singleton] at ih'
    rw [mistakesFrom_cons]
    split
    · rw [zero_add]
      exact ih'.trans (Finset.card_filter_le _ _)
    · rename_i hne
      have hle_vote := hvote h x y ⟨c, hc, hcx⟩
      have hunion := Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset (fun c => c x = y) (consistent C h))
        (Finset.filter_subset (fun c => c x = A h x) (consistent C h)))
      rw [Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ hcy hcŷ =>
        hne (hcŷ.symm.trans hcy))] at hunion
      rw [pow_add, pow_one]; omega

end Consistent

/-! ### Plurality halving -/

section Halving

variable [DecidableEq β] [LinearOrder β] [Inhabited β]

/-- The plurality halving algorithm [Littlestone1988, §3, Algorithm 1;
DanielySabatoBenDavidShalevShwartz2015]: among `default` and the labels assigned to `x` by
`consistent C h`, predict the least label maximizing the number of consistent concepts that output
it. For `β = Bool`, ties break towards `false`, matching Littlestone's binary halving rule. -/
@[expose] def halving (C : Finset (α → β)) : OnlineLearner α β := fun h x =>
  let candidates : Finset β := insert default ((consistent C h).image (fun c => c x))
  let vote : β → ℕ := fun y => ((consistent C h).filter (fun c => c x = y)).card
  let maxVote : ℕ := candidates.sup vote
  (candidates.filter fun y => vote y = maxVote).min' <| by
    obtain ⟨y, hy, hmax⟩ :=
      Finset.exists_mem_eq_sup candidates (Finset.insert_nonempty _ _) vote
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, hmax.symm⟩⟩

private theorem card_filter_le_card_filter_halving (C : Finset (α → β)) (h : List (α × β))
    (x : α) (y : β) (hy : ∃ c ∈ consistent C h, c x = y) :
    ((consistent C h).filter (fun c => c x = y)).card ≤
      ((consistent C h).filter (fun c => c x = halving C h x)).card := by
  let candidates : Finset β := insert default ((consistent C h).image (fun c => c x))
  let vote : β → ℕ := fun z => ((consistent C h).filter (fun c => c x = z)).card
  have hmem : halving C h x ∈ candidates.filter (fun z => vote z = candidates.sup vote) := by
    unfold halving
    exact Finset.min'_mem _ _
  obtain ⟨c, hc, rfl⟩ := hy
  exact (Finset.le_sup (f := vote)
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨c, hc, rfl⟩))).trans_eq
    (Finset.mem_filter.mp hmem).2.symm

/-- After the history `h`, each mistake of plurality halving eliminates at least half of the
consistent concepts, so `2 ^ mistakes ≤ |consistent C h|` on rounds labelled by some consistent
concept. -/
theorem two_pow_mistakesFrom_halving_le (C : Finset (α → β)) (h S : List (α × β))
    (hS : ∃ c ∈ consistent C h, ∀ p ∈ S, c p.1 = p.2) :
    2 ^ mistakesFrom (halving C) h S ≤ (consistent C h).card :=
  two_pow_mistakesFrom_le_of_card_filter_le C (halving C)
    (card_filter_le_card_filter_halving C) h S hS

theorem mistakes_halving_le_log (C : Finset (α → β)) (S : List (α × β))
    (hS : Realizable (C : Set (α → β)) S) : mistakes (halving C) S ≤ Nat.log 2 C.card := by
  obtain ⟨c, hc, hcS⟩ := realizable_iff.mp hS
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  rw [mistakes]
  simpa using two_pow_mistakesFrom_halving_le C [] S ⟨c, by simpa using hc, hcS⟩

/-- **The halving bound** [Littlestone1988, §3, Theorem 1; DanielySabatoBenDavidShalevShwartz2015]:
on a finite class `C`, plurality halving makes at most `⌊log₂ |C|⌋` mistakes. -/
theorem mistakeBound_halving_le (C : Finset (α → β)) :
    mistakeBound (halving C) (C : Set (α → β)) ≤ Nat.log 2 C.card :=
  mistakeBound_le_iff.mpr fun S hS => by exact_mod_cast mistakes_halving_le_log C S hS

end Halving

/-! ### Order-free finite-class bounds -/

/-- [Littlestone1988, §3, Theorem 2]: the optimal mistake bound of a finite class `C` over any
nonempty label type is at most `⌊log₂ |C|⌋`. -/
theorem optimalMistakeBound_le_log_card [DecidableEq β] [Nonempty β] (C : Finset (α → β)) :
    optimalMistakeBound (C : Set (α → β)) ≤ Nat.log 2 C.card := by
  classical
  let y₀ : β := Classical.arbitrary β
  let A : OnlineLearner α β := fun h x =>
    let candidates : Finset β := insert y₀ ((consistent C h).image (fun c => c x))
    let vote : β → ℕ := fun y => ((consistent C h).filter (fun c => c x = y)).card
    (Finset.exists_max_image candidates vote (Finset.insert_nonempty _ _)).choose
  refine (optimalMistakeBound_le A _).trans (mistakeBound_le_iff.mpr fun S hS => ?_)
  obtain ⟨c, hc, hcS⟩ := realizable_iff.mp hS
  have h2 := two_pow_mistakesFrom_le_of_card_filter_le C A (fun h x y ⟨c', hc', hcx⟩ => by
    have hspec := (Finset.exists_max_image
      (insert y₀ ((consistent C h).image (fun c => c x)))
      (fun z => ((consistent C h).filter (fun c => c x = z)).card)
      (Finset.insert_nonempty _ _)).choose_spec
    exact hspec.2 y (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨c', hc', hcx⟩)))
    [] S ⟨c, by simpa using hc, hcS⟩
  rw [consistent_nil] at h2
  exact_mod_cast Nat.le_log_of_pow_le (by norm_num) h2

/-- A complete `d`-mistake tree for a finite class `C` requires at least `2 ^ d` concepts in `C`,
for arbitrary instance and label types. -/
theorem two_pow_le_card_of_hasMistakeTree {d : ℕ} (C : Finset (α → β))
    (hd : HasMistakeTree d (C : Set (α → β))) : 2 ^ d ≤ C.card := by
  classical
  induction d generalizing C with
  | zero =>
    obtain ⟨c, hc⟩ := hd
    exact Finset.card_pos.mpr ⟨c, Finset.mem_coe.mp hc⟩
  | succ d ih =>
    obtain ⟨x, y₀, y₁, hne, h0, h1⟩ := hd
    let C₀ := C.filter fun c => c x = y₀
    let C₁ := C.filter fun c => c x = y₁
    have hC₀ : versionSpace (C : Set (α → β)) [(x, y₀)] = (C₀ : Set (α → β)) := by
      ext
      simp [C₀, versionSpace]
    have hC₁ : versionSpace (C : Set (α → β)) [(x, y₁)] = (C₁ : Set (α → β)) := by
      ext
      simp [C₁, versionSpace]
    rw [hC₀] at h0
    rw [hC₁] at h1
    have ih₀ := ih C₀ h0
    have ih₁ := ih C₁ h1
    have hdisj : Disjoint C₀ C₁ :=
      Finset.disjoint_filter.mpr fun _ _ hc₀ hc₁ => hne (hc₀.symm.trans hc₁)
    have hunion : (C₀ ∪ C₁).card ≤ C.card :=
      Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _))
    rw [Finset.card_union_of_disjoint hdisj] at hunion
    rw [pow_succ]; omega

/-- The Littlestone dimension of a finite class `C` is at most `⌊log₂ |C|⌋`, without any finiteness
or order assumptions on `β`. -/
theorem littlestoneDim_le_log_card (C : Finset (α → β)) :
    littlestoneDim (C : Set (α → β)) ≤ Nat.log 2 C.card :=
  littlestoneDim_le_iff.mpr fun _ hd => by
    exact_mod_cast Nat.le_log_of_pow_le (by norm_num) (two_pow_le_card_of_hasMistakeTree C hd)

end Cslib.MachineLearning.OnlineLearning.MistakeBound
