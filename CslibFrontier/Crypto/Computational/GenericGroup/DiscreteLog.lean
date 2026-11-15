/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GenericGroup.Relabel
public import CslibFrontier.Crypto.Game
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Algebra.Field.ZMod

/-!
# Discrete logarithm in the generic group model

The discrete-logarithm game in the generic group model of [BonehShoup2023], Section 16.3, and the
bound of Theorem 16.3 (p. 693): for prime `q`, an adversary that makes at most `T` queries to the
group oracle outputs the discrete logarithm with probability at most `((3T + 2)² / 2 + 1) / q`.

`dlogGame A` draws a uniform injective labeling `L : ZMod q ↪ S` and a uniform `α : ZMod q`, gives
the adversary `L 1` and `L α`, runs it against the group oracle of `L` (`runLabeled`) and wins when
it outputs `α`. The adversary's budget is `ProbOracleComp.IsQueryBounded`: at most `T` labeling and
group-operation queries on every path, whatever its private coins; coin draws are free.

This is an unconditional bound on query-bounded programs in an idealized model. It takes no
hardness assumption and is not a statement about any specific group: as the book says (p. 695),
the bound says nothing about the difficulty of discrete logarithm in any specific group. It applies
to adversaries that are otherwise unbounded.

Primality of `q` is needed for the theorem, not only for its proof: for `q = dᵏ` an adversary can
recover `α` digit by digit, with probability `1`, from fewer queries than the bound allows (for
example `q = 512` with `9` queries). The proof uses primality only in the fact that two distinct
linear forms `c X + d` agree at no more than one point of `ZMod q`.

It differs from the book's setting as follows.

1. `S` is any finite type, not a set of bit strings; `Nonempty (ZMod q ↪ S)` is the book's
   `|S| ≥ q`.
2. The adversary may use private coins; the book's adversary is a computationally unbounded
   algorithm, and nothing beyond the query bound is assumed here either.
3. The challenger does not make labeling queries; it reads `L 1` and `L α` directly, which gives
   the same distribution.
4. Groups are additive: the label of `β` stands for `β • g`, the book's `g^β`.

The proof follows the book's (Games 0–2): reduce to labels in `ZMod q` with a uniform permutation
as labeling (`Cslib.Crypto.GenericGroup.relabel`), sample the permutation lazily, and replace it by
a table on linear forms that is identical until two distinct forms agree at `α`. The sharp form
`succProbability_dlogGame_le_choose` is what the proof gives before the book rounds the number of
pairs of forms, `(3T + 2).choose 2`, up to `(3T + 2)² / 2`.

## Main definitions

* `Cslib.Crypto.GenericGroup.dlogGame`: the discrete-logarithm game in the generic group model.

## Main results

* `Cslib.Crypto.GenericGroup.succProbability_dlogGame_le`: Theorem 16.3, the bound
  `((3T + 2)² / 2 + 1) / q`.
* `Cslib.Crypto.GenericGroup.succProbability_dlogGame_le_choose`: the sharp form
  `((3T + 2).choose 2 + 1) / q`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 16.3, Theorem 16.3 and its proof, pp. 693–695.
-/

public section

namespace Cslib.Crypto.GenericGroup

open Probability
open scoped NNReal ENNReal

variable {q : ℕ} {S : Type}

/-- The discrete-logarithm game in the generic group model ([BonehShoup2023], Theorem 16.3): a
uniform injective labeling `L` and a uniform `α`; the adversary gets `L 1` and `L α`, runs against
the group oracle of `L`, and wins when it outputs `α`. -/
noncomputable def dlogGame [NeZero q] [Fintype S] [Nonempty (ZMod q ↪ S)]
    (A : S → S → ProbOracleComp (GroupOracleSpec q S) (ZMod q)) : Game := do
  let L ← PMF.uniformOfFintype (ZMod q ↪ S)
  let α ← PMF.uniformOfFintype (ZMod q)
  let guess ← runLabeled L (A (L 1) (L α))
  return decide (guess = α)

/-! ### Reduction to a uniform permutation as labeling -/

/-- The game with labels in `ZMod q` and a uniform permutation as labeling. -/
private noncomputable def permDlogGame [NeZero q]
    (A : ZMod q → ZMod q → ProbOracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)) : Game := do
  let σ ← PMF.uniformOfFintype (Equiv.Perm (ZMod q))
  let α ← PMF.uniformOfFintype (ZMod q)
  let guess ← runLabeled (σ : ZMod q → ZMod q) (A (σ 1) (σ α))
  return decide (guess = α)

private theorem dlogGame_eq_bind_permDlogGame [NeZero q] [Fintype S] [Nonempty (ZMod q ↪ S)]
    (A : S → S → ProbOracleComp (GroupOracleSpec q S) (ZMod q)) :
    dlogGame A = (PMF.uniformOfFintype (ZMod q ↪ S)).bind fun j =>
      permDlogGame fun g u => relabel j (A (j g) (j u)) := by
  unfold dlogGame permDlogGame
  simp only [PMF.monad_bind_eq_bind]
  rw [uniform_embedding_bind_eq]
  refine congrArg _ (funext fun j => congrArg _ (funext fun σ => congrArg _ (funext fun α => ?_)))
  rw [runLabeled_relabel]
  rfl

/-! ### Where primality is used -/

/-- Two distinct linear forms over `ZMod q`, `q` prime, agree at no more than one point. -/
private theorem card_filter_affine_eq_le_one (hq : q.Prime) {c d c' d' : ZMod q}
    (h : (c, d) ≠ (c', d')) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    (Finset.univ.filter fun α : ZMod q => c * α + d = c' * α + d').card ≤ 1 := by
  have : Fact q.Prime := ⟨hq⟩
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_cases hc : c = c'
  · subst hc
    exact absurd (by simpa using ha : d = d') fun hd => h (by rw [hd])
  · have hne : c - c' ≠ 0 := sub_ne_zero.mpr hc
    exact mul_left_cancel₀ hne (by linear_combination ha - hb)

/-! ### Bijective labels -/

/-- The core of the proof: Theorem 16.3 for labels in `ZMod q` and a uniform permutation as
labeling. -/
private theorem succProbability_permDlogGame_le [NeZero q] (hq : q.Prime) {T : ℕ}
    {A : ZMod q → ZMod q → ProbOracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)}
    (hA : ∀ g u, (A g u).IsQueryBounded T) :
    (permDlogGame A).succProbability ≤ (((3 * T + 2).choose 2 + 1 : ℕ) : ℝ≥0) / q := by
  sorry

/-! ### Theorem 16.3 -/

/-- **Theorem 16.3, sharp form.** For prime `q` and an adversary that makes at most `T` queries to
the group oracle on every path, the discrete-logarithm game in the generic group model is won with
probability at most `((3T + 2).choose 2 + 1) / q`. This is the bound the proof of
[BonehShoup2023], Theorem 16.3, gives before it rounds `(3T + 2).choose 2` up to `(3T + 2)² / 2`;
it is attained at `T = 0`. -/
theorem succProbability_dlogGame_le_choose [NeZero q] [Fintype S] [Nonempty (ZMod q ↪ S)]
    (hq : q.Prime) {T : ℕ} {A : S → S → ProbOracleComp (GroupOracleSpec q S) (ZMod q)}
    (hA : ∀ g u, (A g u).IsQueryBounded T) :
    (dlogGame A).succProbability ≤ (((3 * T + 2).choose 2 + 1 : ℕ) : ℝ≥0) / q := by
  rw [dlogGame_eq_bind_permDlogGame]
  have hb := PMF.bind_apply_le_on_support (PMF.uniformOfFintype (ZMod q ↪ S))
    (f := fun j => permDlogGame fun g u => relabel j (A (j g) (j u))) (b := true)
    (c := (((((3 * T + 2).choose 2 + 1 : ℕ) : ℝ≥0) / q : ℝ≥0) : ℝ≥0∞)) fun j _ => by
      have h := succProbability_permDlogGame_le hq (T := T)
        (A := fun g u => relabel j (A (j g) (j u))) fun g u => isQueryBounded_relabel j (hA _ _)
      calc (permDlogGame fun g u => relabel j (A (j g) (j u))) true
          = (((permDlogGame fun g u => relabel j (A (j g) (j u))) true).toNNReal : ℝ≥0∞) :=
            (ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)).symm
        _ ≤ _ := ENNReal.coe_le_coe.mpr h
  exact (ENNReal.toNNReal_mono ENNReal.coe_ne_top hb).trans_eq (ENNReal.toNNReal_coe _)

/-- **Theorem 16.3** ([BonehShoup2023], p. 693, eq. (16.6)). For prime `q` and an adversary that
makes at most `T` queries to the group oracle on every path, the discrete-logarithm game in the
generic group model is won with probability at most `((3T + 2)² / 2 + 1) / q`. -/
theorem succProbability_dlogGame_le [NeZero q] [Fintype S] [Nonempty (ZMod q ↪ S)]
    (hq : q.Prime) {T : ℕ} {A : S → S → ProbOracleComp (GroupOracleSpec q S) (ZMod q)}
    (hA : ∀ g u, (A g u).IsQueryBounded T) :
    (dlogGame A).succProbability ≤ ((3 * T + 2 : ℝ≥0) ^ 2 / 2 + 1) / q := by
  refine (succProbability_dlogGame_le_choose hq hA).trans ?_
  gcongr
  have h : ((3 * T + 2).choose 2 : ℝ≥0) ≤ (3 * T + 2 : ℝ≥0) ^ 2 / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    have h2 : (3 * T + 2).choose 2 * 2 ≤ (3 * T + 2) ^ 2 := by
      rw [Nat.choose_two_right]
      calc (3 * T + 2) * (3 * T + 2 - 1) / 2 * 2 ≤ (3 * T + 2) * (3 * T + 2 - 1) :=
            Nat.div_mul_le_self _ _
        _ ≤ (3 * T + 2) ^ 2 := by
            rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    exact_mod_cast h2
  push_cast
  exact add_le_add_left h 1

end Cslib.Crypto.GenericGroup
