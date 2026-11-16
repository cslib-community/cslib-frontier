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
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Computational Diffie–Hellman in the generic group model

A lower bound for computational Diffie–Hellman (CDH) in the generic group model of
[BonehShoup2023], Section 16.3: part (a) of Exercise 16.5 (p. 708), which asks to adapt the proof
of Theorem 16.3 to CDH. The bound is not stated in the book: the exercise states none, and the one
below is what the adapted proof gives. For prime `q`, an adversary that makes at most `T` queries
to the group oracle outputs the label of `α β` with probability at most `((3T + 4)² / 2 + 2) / q`.

`cdhGame A` draws a uniform injective labeling `L : ZMod q ↪ S` and uniform `α β : ZMod q`, gives
the adversary `L 1`, `L α` and `L β`, runs it against the group oracle of `L` (`runLabeled`), and
wins when it outputs `L (α * β)`. As for `Cslib.Crypto.GenericGroup.dlogGame`, the budget is
`ProbOracleComp.IsQueryBounded`: at most `T` labeling and group-operation queries on every path,
whatever the adversary's private coins. Since the adversary outputs a label, the game compares
elements of `S` and takes `DecidableEq S`, which `dlogGame` does not need.

This is a query bound in an idealized model: it assumes no computational hardness, says nothing
about CDH in any specific group, and applies to adversaries that are otherwise unbounded.

The proof is an instance of `Cslib.Crypto.GenericGroup.succProbability_linearGame_le`, the bound
for games with linear inputs, with two unknowns `α` and `β`, one output label, and the test that the
output is the label of `α β`. It differs from the bound of Theorem 16.3 in two places.

1. The table of linear forms holds at most `3T + 4` forms, not `3T + 2`: one more for the second
   challenge `L β`, and one for the output, whose form the challenger looks up because the output
   is a label, where a discrete-logarithm adversary outputs an exponent.
2. The guess term is `2 / q`, not `1 / q`: the output is a fixed linear form `a X + b Y + c`, and
   `X Y = a X + b Y + c` holds at no more than `2q - 1` of the `q²` points when `q` is prime, where
   a guess of the discrete logarithm is right at one point in `q`.

`q` is prime, as in Theorem 16.3; the proof uses it twice, for collisions between two distinct
linear forms and for the count of solutions of `X Y = a X + b Y + c`. The bound is not claimed for
composite `q`, and it fails there: for `q = 2¹⁰`, recovering `α` bit by bit and then asking for the
label of `α β` wins with probability one using `12` queries, where the sharp form gives `391 / 512`.
That attack was checked by computation and is not formalized. Part (b) of the exercise, the
interactive CDH (ICDH) problem of Definition 12.4, is not formalized here.

## Main definitions

* `Cslib.Crypto.GenericGroup.cdhGame`: the CDH game in the generic group model.

## Main results

* `Cslib.Crypto.GenericGroup.succProbability_cdhGame_le`: the bound `((3T + 4)² / 2 + 2) / q`.
* `Cslib.Crypto.GenericGroup.succProbability_cdhGame_le_choose`: the sharp form
  `((3T + 4).choose 2 + 2) / q`.
* `Cslib.Crypto.GenericGroup.le_of_half_le_succProbability_cdhGame`: success probability one half
  needs `q ≤ (3T + 4)² + 4`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Exercise 16.5 (p. 708); Section 16.3, Theorem 16.3 and its proof, pp. 693–695.
-/

public section

namespace Cslib.Crypto.GenericGroup

open Probability OracleComp
open scoped NNReal

variable {q : ℕ} {S : Type}

/-- The CDH game in the generic group model ([BonehShoup2023], Exercise 16.5(a)): a uniform
injective labeling `L` and uniform `α` and `β`; the adversary gets `L 1`, `L α` and `L β`, runs
against the group oracle of `L`, and wins when it outputs `L (α * β)`. -/
noncomputable def cdhGame [NeZero q] [Fintype S] [DecidableEq S] [Nonempty (ZMod q ↪ S)]
    (A : S → S → S → ProbOracleComp (GroupOracleSpec q S) S) : Game := do
  let L ← PMF.uniformOfFintype (ZMod q ↪ S)
  let α ← PMF.uniformOfFintype (ZMod q)
  let β ← PMF.uniformOfFintype (ZMod q)
  let w ← runLabeled L (A (L 1) (L α) (L β))
  return decide (w = L (α * β))

/-- Over `ZMod q`, `q` prime, `x y = a x + b y + c` has at most `2q - 1` solutions: it is
`(x - b) (y - a) = c + a b`, so `x = b` with any `y`, or one `y` for each other `x`. -/
private theorem card_filter_mul_eq_le [Fact q.Prime] (a b c : ZMod q) :
    (Finset.univ.filter fun p : ZMod q × ZMod q =>
      p.1 * p.2 = a * p.1 + b * p.2 + c).card ≤ 2 * q - 1 := by
  have hsub : (Finset.univ.filter fun p : ZMod q × ZMod q => p.1 * p.2 = a * p.1 + b * p.2 + c) ⊆
      (({b} : Finset (ZMod q)) ×ˢ Finset.univ) ∪
        ((Finset.univ.erase b).image fun x => (x, a + (c + a * b) * (x - b)⁻¹)) := by
    rintro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases hx : x = b
    · exact Finset.mem_union_left _ (by simp [hx])
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, by simp [hx], ?_⟩)
      have hy : (x - b) * (y - a) = c + a * b := by linear_combination hp
      rw [← hy, mul_comm (x - b), mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hx), mul_one,
        add_sub_cancel]
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ q + (q - 1) := add_le_add (by simp [ZMod.card]) (Finset.card_image_le.trans (by
        simp [ZMod.card]))
    _ = 2 * q - 1 := by have := (Fact.out : q.Prime).pos; omega

/-- Two independent uniform draws from `ZMod q` are one uniform draw of a point `Fin 2 → ZMod q`. -/
private theorem uniform_finTwo_bind [NeZero q] {β : Type} (k : ZMod q → ZMod q → PMF β) :
    (PMF.uniformOfFintype (Fin 2 → ZMod q)).bind (fun x => k (x 0) (x 1)) =
      (PMF.uniformOfFintype (ZMod q)).bind fun a => (PMF.uniformOfFintype (ZMod q)).bind fun b =>
        k a b := by
  rw [← PMF.uniformOfFintype_map_equiv (piFinTwoEquiv fun _ => ZMod q).symm, PMF.bind_map,
    ← PMF.uniformOfFintype_prod, PMF.bind_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [PMF.bind_map]
  rfl

/-- The CDH game is the game with linear inputs with two unknowns, one output label, and the test
that the output label is that of the product of the unknowns. -/
private theorem cdhGame_eq_linearGame [NeZero q] [Fintype S] [DecidableEq S]
    [Nonempty (ZMod q ↪ S)] (A : S → S → S → ProbOracleComp (GroupOracleSpec q S) S) :
    cdhGame A = linearGame (ι := Fin 2) (κ := Unit) (γ := Unit)
      (fun x _ v => decide (v () = x 0 * x 1))
      (fun g u => (fun w => ((), fun _ => w)) <$> A g (u 0) (u 1)) := by
  unfold cdhGame linearGame
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine congrArg _ (funext fun L => ?_)
  rw [← uniform_finTwo_bind]
  refine congrArg (PMF.bind _) (funext fun x => ?_)
  unfold runLabeled
  rw [OracleComp.interpret_map, PMF.monad_map_eq_map, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun w => congrArg PMF.pure (decide_eq_decide.mpr
    ⟨fun h => ⟨fun _ => x 0 * x 1, fun _ => h.symm, by simp⟩, fun ⟨v, hv, hvx⟩ => ?_⟩))
  exact (hv ()).symm.trans (congrArg L (of_decide_eq_true hvx))

/-- **CDH in the generic group model, sharp form** ([BonehShoup2023], Exercise 16.5(a)). For prime
`q` and an adversary that makes at most `T` queries to the group oracle on every path, the CDH game
in the generic group model is won with probability at most `((3T + 4).choose 2 + 2) / q`. -/
theorem succProbability_cdhGame_le_choose [NeZero q] [Fintype S] [DecidableEq S]
    [Nonempty (ZMod q ↪ S)] (hq : q.Prime) {T : ℕ}
    {A : S → S → S → ProbOracleComp (GroupOracleSpec q S) S}
    (hA : ∀ g u v, (A g u v).IsQueryBounded T) :
    (cdhGame A).succProbability ≤ (((3 * T + 4).choose 2 + 2 : ℕ) : ℝ≥0) / q := by
  have : Fact q.Prime := ⟨hq⟩
  rw [cdhGame_eq_linearGame]
  refine (succProbability_linearGame_le hq (fun x _ v => decide (v () = x 0 * x 1))
    (A := fun g u => (fun w => ((), fun _ => w)) <$> A g (u 0) (u 1))
    (fun g u => (OracleComp.isCostBounded_map_iff _ _ _).mpr (hA g (u 0) (u 1))) (2 / q)
    fun _ F => ?_).trans_eq ?_
  · have hcard : (Finset.univ.filter fun x : Fin 2 → ZMod q =>
        decide (∑ i, (F ()).1 i * x i + (F ()).2 = x 0 * x 1) = true).card ≤ 2 * q - 1 := by
      refine (Finset.card_le_card_of_injOn (fun x => (x 0, x 1)) (fun x hx => ?_)
        fun x _ y _ hxy => ?_).trans (card_filter_mul_eq_le ((F ()).1 0) ((F ()).1 1) (F ()).2)
      · rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
        simp only [Finset.mem_univ, true_and, decide_eq_true_eq, Fin.sum_univ_two] at hx ⊢
        exact hx.symm
      · simp only [Prod.mk.injEq] at hxy
        funext i
        fin_cases i
        exacts [hxy.1, hxy.2]
    calc ((_ : ℕ) : ℝ≥0) ≤ ((2 * q : ℕ) : ℝ≥0) := by exact_mod_cast hcard.trans (Nat.sub_le _ _)
      _ = 2 / q * (q : ℝ≥0) ^ Fintype.card (Fin 2) := by
        rw [Fintype.card_fin]
        push_cast
        field_simp
  · rw [Fintype.card_fin, Fintype.card_unit, ← add_div]
    push_cast
    rfl

/-- **CDH in the generic group model** ([BonehShoup2023], Exercise 16.5(a), in the form of (16.6)).
For prime `q` and an adversary that makes at most `T` queries to the group oracle on every path,
the CDH game in the generic group model is won with probability at most
`((3T + 4)² / 2 + 2) / q`. -/
theorem succProbability_cdhGame_le [NeZero q] [Fintype S] [DecidableEq S]
    [Nonempty (ZMod q ↪ S)] (hq : q.Prime) {T : ℕ}
    {A : S → S → S → ProbOracleComp (GroupOracleSpec q S) S}
    (hA : ∀ g u v, (A g u v).IsQueryBounded T) :
    (cdhGame A).succProbability ≤ ((3 * T + 4 : ℝ≥0) ^ 2 / 2 + 2) / q := by
  refine (succProbability_cdhGame_le_choose hq hA).trans ?_
  have h := Nat.choose_le_pow_div (α := ℝ≥0) 2 (3 * T + 4)
  rw [Nat.factorial_two] at h
  push_cast at h ⊢
  gcongr

/-- **Success probability one half** ([BonehShoup2023], Exercise 16.5(a)). For prime `q`, an
adversary that makes at most `T` queries to the group oracle on every path and wins the CDH game
with probability at least `1 / 2` has `q ≤ (3T + 4)² + 4`: `T` is at least about `√q / 3`. -/
theorem le_of_half_le_succProbability_cdhGame [NeZero q] [Fintype S] [DecidableEq S]
    [Nonempty (ZMod q ↪ S)] (hq : q.Prime) {T : ℕ}
    {A : S → S → S → ProbOracleComp (GroupOracleSpec q S) S}
    (hA : ∀ g u v, (A g u v).IsQueryBounded T) (h : 1 / 2 ≤ (cdhGame A).succProbability) :
    q ≤ (3 * T + 4) ^ 2 + 4 := by
  have h' := h.trans (succProbability_cdhGame_le hq hA)
  rw [le_div_iff₀ (Nat.cast_pos.mpr hq.pos)] at h'
  have h'' : ((1 / 2 * q : ℝ≥0) : ℝ) ≤ (((3 * T + 4 : ℝ≥0) ^ 2 / 2 + 2 : ℝ≥0) : ℝ) := h'
  push_cast at h''
  exact_mod_cast (by push_cast; linarith : (q : ℝ) ≤ ((3 * T + 4) ^ 2 + 4 : ℕ))

end Cslib.Crypto.GenericGroup
