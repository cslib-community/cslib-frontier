/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GenericGroup.Relabel
public import CslibFrontier.Crypto.Game
import CslibFrontier.Crypto.Computational.GenericGroup.LinearGame
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Discrete logarithm in the generic group model

The discrete-logarithm game in the generic group model of [BonehShoup2023], Section 16.3, and the
bound of Theorem 16.3 (p. 693): for prime `q`, an adversary that makes at most `T` queries to the
group oracle outputs the discrete logarithm with probability at most `((3T + 2)² / 2 + 1) / q`.

`dlogGame A` draws a uniform injective labeling `L : ZMod q ↪ S` and a uniform `α : ZMod q`, gives
the adversary `L 1` and `L α`, runs it against the group oracle of `L` (`runLabeled`) and wins when
it outputs `α`. The adversary's budget is `ProbOracleComp.IsQueryBounded`: at most `T` labeling and
group-operation queries on every path, whatever its private coins; coin draws are free.

This is a query bound on query-bounded programs in an idealized model; it assumes no computational
hardness and is not a statement about any specific group: as the book says (p. 695), the bound
says nothing about the difficulty of discrete logarithm in any specific group. It applies to
adversaries that are otherwise unbounded.

As in the book, `q` is prime; the bound is not claimed for composite `q`. For groups of
prime-power order the book reduces discrete logarithm to the prime case (Section 16.1.2, p. 684).
The proof uses primality only in the fact that two distinct linear forms `c X + d` agree at no more
than one point of `ZMod q`.

It differs from the book's setting as follows.

1. `S` is any finite type, not a set of bit strings; `Nonempty (ZMod q ↪ S)` is the book's
   `|S| ≥ q`.
2. The adversary may use private coins; the book's adversary is a computationally unbounded
   algorithm, and nothing beyond the query bound is assumed here either.
3. The challenger does not make labeling queries; it reads `L 1` and `L α` directly, which gives
   the same distribution.
4. Groups are additive: the label of `β` stands for `β • g`, the book's `g^β`.

The proof follows the book's (Games 0–2) and is an instance of
`Cslib.Crypto.GenericGroup.succProbability_linearGame_le`, the bound for games with linear inputs:
one unknown `α`, no output labels, and the test that the output value is `α`, which holds at one
point in `q`. That proof reduces to labels in `ZMod q` with a uniform permutation as labeling
(`Cslib.Crypto.GenericGroup.relabel`), samples the permutation lazily, and replaces it by a table
on linear forms that is identical until two distinct forms agree at `α`. The sharp form
`succProbability_dlogGame_le_choose` is what the proof gives before the book rounds the number of
pairs of forms, `(3T + 2).choose 2`, up to `(3T + 2)² / 2`. An adversary that wins with probability
at least one half has `q ≤ (3T + 2)² + 2` (`le_of_half_le_succProbability_dlogGame`), so `T` is at
least about `√q / 3`, as the book remarks after the theorem (p. 695).

## Main definitions

* `Cslib.Crypto.GenericGroup.dlogGame`: the discrete-logarithm game in the generic group model.

## Main results

* `Cslib.Crypto.GenericGroup.succProbability_dlogGame_le`: Theorem 16.3, the bound
  `((3T + 2)² / 2 + 1) / q`.
* `Cslib.Crypto.GenericGroup.succProbability_dlogGame_le_choose`: the sharp form
  `((3T + 2).choose 2 + 1) / q`.
* `Cslib.Crypto.GenericGroup.le_of_half_le_succProbability_dlogGame`: success probability one half
  needs `q ≤ (3T + 2)² + 2`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 16.3, Theorem 16.3 and its proof, pp. 693–695.
-/

public section

namespace Cslib.Crypto.GenericGroup

open Probability OracleComp
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

/-- The discrete-logarithm game is the game with linear inputs with one unknown, no output labels,
and the test that the output value is the unknown. -/
private theorem dlogGame_eq_linearGame [NeZero q] [Fintype S] [DecidableEq S]
    [Nonempty (ZMod q ↪ S)] (A : S → S → ProbOracleComp (GroupOracleSpec q S) (ZMod q)) :
    dlogGame A = linearGame (ι := Unit) (κ := Empty) (fun x guess _ => decide (guess = x ()))
      (fun g u => (fun guess => (guess, Empty.elim)) <$> A g (u ())) := by
  unfold dlogGame linearGame
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine congrArg (PMF.bind _) (funext fun L => ?_)
  rw [← PMF.uniformOfFintype_map_equiv (Equiv.funUnique Unit (ZMod q)), PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun x => ?_)
  rw [runLabeled, OracleComp.interpret_map, PMF.monad_map_eq_map, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun guess => congrArg PMF.pure (decide_eq_decide.mpr
    ⟨fun h => ⟨Empty.elim, fun k => k.elim, decide_eq_true h⟩, fun ⟨_, _, hv⟩ => ?_⟩))
  exact of_decide_eq_true hv

/-- **Theorem 16.3, sharp form.** For prime `q` and an adversary that makes at most `T` queries to
the group oracle on every path, the discrete-logarithm game in the generic group model is won with
probability at most `((3T + 2).choose 2 + 1) / q`. This is the bound the proof of
[BonehShoup2023], Theorem 16.3, gives before it rounds `(3T + 2).choose 2` up to `(3T + 2)² / 2`. -/
theorem succProbability_dlogGame_le_choose [NeZero q] [Fintype S] [Nonempty (ZMod q ↪ S)]
    (hq : q.Prime) {T : ℕ} {A : S → S → ProbOracleComp (GroupOracleSpec q S) (ZMod q)}
    (hA : ∀ g u, (A g u).IsQueryBounded T) :
    (dlogGame A).succProbability ≤ (((3 * T + 2).choose 2 + 1 : ℕ) : ℝ≥0) / q := by
  classical
  have hW (guess : ZMod q) (_ : Empty → (Unit → ZMod q) × ZMod q) :
      (((Finset.univ.filter fun x : Unit → ZMod q => decide (guess = x ())).card : ℕ) : ℝ≥0) ≤
        1 / q * (q : ℝ≥0) ^ Fintype.card Unit := by
    have hcard : (Finset.univ.filter fun x : Unit → ZMod q => decide (guess = x ())).card ≤ 1 :=
      Finset.card_le_one.mpr fun x hx y hy => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hx hy
        funext u
        rw [← hx, ← hy]
    rw [Fintype.card_unit, pow_one, one_div, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hq.ne_zero)]
    exact_mod_cast hcard
  rw [dlogGame_eq_linearGame]
  refine (succProbability_linearGame_le hq (fun x guess _ => decide (guess = x ()))
    (A := fun g u => (fun guess => (guess, Empty.elim)) <$> A g (u ()))
    (fun g u => (OracleComp.isCostBounded_map_iff _ _ _).mpr (hA g (u ()))) _ hW).trans_eq ?_
  rw [Fintype.card_unit, Fintype.card_empty, ← add_div]
  push_cast
  rfl

/-- **Theorem 16.3** ([BonehShoup2023], p. 693, eq. (16.6)). For prime `q` and an adversary that
makes at most `T` queries to the group oracle on every path, the discrete-logarithm game in the
generic group model is won with probability at most `((3T + 2)² / 2 + 1) / q`. -/
theorem succProbability_dlogGame_le [NeZero q] [Fintype S] [Nonempty (ZMod q ↪ S)]
    (hq : q.Prime) {T : ℕ} {A : S → S → ProbOracleComp (GroupOracleSpec q S) (ZMod q)}
    (hA : ∀ g u, (A g u).IsQueryBounded T) :
    (dlogGame A).succProbability ≤ ((3 * T + 2 : ℝ≥0) ^ 2 / 2 + 1) / q := by
  refine (succProbability_dlogGame_le_choose hq hA).trans ?_
  have h := Nat.choose_le_pow_div (α := ℝ≥0) 2 (3 * T + 2)
  rw [Nat.factorial_two] at h
  push_cast at h ⊢
  gcongr

/-- **Success probability one half** (the remark after Theorem 16.3, [BonehShoup2023], p. 695).
For prime `q`, an adversary that makes at most `T` queries to the group oracle on every path and
wins the discrete-logarithm game with probability at least `1 / 2` has `q ≤ (3T + 2)² + 2`: `T`
is at least about `√q / 3`. -/
theorem le_of_half_le_succProbability_dlogGame [NeZero q] [Fintype S] [Nonempty (ZMod q ↪ S)]
    (hq : q.Prime) {T : ℕ} {A : S → S → ProbOracleComp (GroupOracleSpec q S) (ZMod q)}
    (hA : ∀ g u, (A g u).IsQueryBounded T) (h : 1 / 2 ≤ (dlogGame A).succProbability) :
    q ≤ (3 * T + 2) ^ 2 + 2 := by
  have h' := h.trans (succProbability_dlogGame_le hq hA)
  rw [le_div_iff₀ (Nat.cast_pos.mpr hq.pos)] at h'
  have h'' : ((1 / 2 * q : ℝ≥0) : ℝ) ≤ (((3 * T + 2 : ℝ≥0) ^ 2 / 2 + 1 : ℝ≥0) : ℝ) := h'
  push_cast at h''
  exact_mod_cast (by push_cast; linarith : (q : ℝ) ≤ ((3 * T + 2) ^ 2 + 2 : ℕ))

end Cslib.Crypto.GenericGroup
