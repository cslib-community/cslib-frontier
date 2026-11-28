/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Frontier.Compiler.GateSweep.Steiner
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Scores
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Nat.Card
import CslibFrontier.Foundations.Data.Set.Card
import CslibFrontier.Foundations.Probability.EfronStein
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Discrete uniform gate sweeps and unit-fanout forest grouping

This file constructs low-width layouts on `Compiler.Node c` and balanced two-colorings for
quadratic-form correlation using only finite uniform averages (`𝔼`) over `κ → Fin M`:

* **Supporting-line tangents** (`one_sub_pow_add_pow_le`, `one_sub_two_pow_le_tangent`,
  `two_pow_neg_ge_tangent`, `four_mul_one_sub_two_pow_le`). Elementary convexity of
  `α^k + (1 - α)^k` caps every threshold straddle probability `1 - (j/M)^k - (1 - j/M)^k` at the
  midpoint value `1 - 2^{1 - k}`, and discrete secant lines bound `1 - 2^{1 - k}` above at
  `(k₀, k₀ + 1)`.
* **Uniform bucket layouts** (`exists_layout_signalWidth_le`). Combining coordinate independence
  with `Fintype.exists_forall_abs_sub_expect_le`
  (`CslibFrontier/Foundations/Probability/EfronStein.lean`) and sorting `Node c` by uniform bucket
  scores `Node c → Fin M` bounds `signalWidth c π` by
  `∑_w (1 - 2^{1 - |support w|}) + (r + 1) |Node c| / M + (r + 1) √(M |Node c|)`.
* **Unit-fanout forest grouping** (`exists_layout_signalWidth_reuse_le`). At fan-in two, bottom-up
  splitting of the unit-fanout gate forest into pieces of size at most `2 B + 1` eliminates every
  unsevered fan-out-one gate wire from strict bucket cuts while severing at most
  `|Node c| / (B + 1)` edges.
* **Balanced two-coloring cuts** (`exists_node_cut_margin`). A uniform `Node c → Bool` cut
  simultaneously controls monochromatic reachable inputs on both sides and straddling inner gates.
-/

public section

namespace Cslib.Circuits.Frontier.Compiler

open Set
open scoped BigOperators

/-! ### Elementary convexity and supporting-line tangents -/

/-- Midpoint convexity of `α ↦ α^k + (1 - α)^k` on `[0, 1]`: for `k ≥ 1`,
`1 - α^k - (1 - α)^k ≤ 1 - (1/2)^{k - 1}`. -/
theorem one_sub_pow_add_pow_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    1 - α ^ k - (1 - α) ^ k ≤ 1 - (1 / 2 : ℝ) ^ (k - 1) := by
  have h1α : 0 ≤ 1 - α := by linarith
  suffices hmid : ∀ m : ℕ, (1 / 2 : ℝ) ^ m ≤ α ^ (m + 1) + (1 - α) ^ (m + 1) by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
    have hm := hmid m
    simp only [Nat.add_sub_cancel]
    linarith
  intro m
  induction m with
  | zero =>
    norm_num
  | succ m ih =>
    have hprod : 0 ≤ (α ^ (m + 1) - (1 - α) ^ (m + 1)) * (α - (1 - α)) := by
      rcases le_total α (1 - α) with hle | hge
      · have hp : α ^ (m + 1) ≤ (1 - α) ^ (m + 1) := pow_le_pow_left₀ h0 hle (m + 1)
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      · have hp : (1 - α) ^ (m + 1) ≤ α ^ (m + 1) := pow_le_pow_left₀ h1α hge (m + 1)
        exact mul_nonneg (by linarith) (by linarith)
    have hid : 2 * (α ^ (m + 1 + 1) + (1 - α) ^ (m + 1 + 1)) -
        (α ^ (m + 1) + (1 - α) ^ (m + 1)) =
        (α ^ (m + 1) - (1 - α) ^ (m + 1)) * (α - (1 - α)) := by
      ring
    have hpow : (1 / 2 : ℝ) ^ (m + 1) = (1 / 2) * (1 / 2 : ℝ) ^ m := by ring
    linarith

/-- Discrete supporting secant of `k ↦ 1 - 2^{1 - k}` through `k = k₀` and `k = k₀ + 1`. -/
theorem one_sub_two_pow_le_tangent (k₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (1 : ℝ) - (1 / 2 : ℝ) ^ (k - 1) ≤
      (1 - (k₀ + 2 : ℝ) / (2 : ℝ) ^ k₀) + (k : ℝ) / (2 : ℝ) ^ k₀ := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k₀ := by positivity
  have hcore : (k₀ + 2 : ℝ) ≤ (2 : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ (k - 1) + k := by
    rcases lt_or_ge (k₀ + 1) k with hbig | hsmall
    · have hk' : (k₀ + 2 : ℝ) ≤ k := by exact_mod_cast (show k₀ + 2 ≤ k by omega)
      have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ (k - 1) := by positivity
      linarith
    · set d := k₀ + 1 - k
      have hk₀_eq : k₀ = d + (k - 1) := by omega
      have hprod : (2 : ℝ) ^ k₀ * (1 / 2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ d := by
        rw [hk₀_eq, pow_add, mul_assoc, ← mul_pow]
        norm_num
      have hd : d + 1 ≤ 2 ^ d := Nat.succ_le_of_lt d.lt_two_pow_self
      have hnat : k₀ + 2 ≤ 2 ^ d + k := by omega
      have hreal : (k₀ + 2 : ℝ) ≤ ((2 ^ d + k : ℕ) : ℝ) := by exact_mod_cast hnat
      cast_linarith
  have hdiv : ((k₀ : ℝ) + 2) / (2 : ℝ) ^ k₀ ≤ (1 / 2 : ℝ) ^ (k - 1) + (k : ℝ) / (2 : ℝ) ^ k₀ := by
    rw [← mul_div_cancel_left₀ ((1 / 2 : ℝ) ^ (k - 1)) hpos.ne', ← add_div]
    exact div_le_div_of_nonneg_right hcore hpos.le
  linarith

/-- Discrete supporting secant of `k ↦ 2^{-k}` through `k = k₀ - 1` and `k = k₀` (`k₀ ≥ 1`). -/
theorem two_pow_neg_ge_tangent {k₀ : ℕ} (hk₀ : 1 ≤ k₀) {k : ℕ} (hk : 1 ≤ k) :
    ((k₀ + 1 : ℝ) - k) / (2 : ℝ) ^ k₀ ≤ (1 / 2 : ℝ) ^ k := by
  have htan := one_sub_two_pow_le_tangent (k₀ - 1) hk
  have hsub : ((k₀ - 1 : ℕ) : ℝ) + 2 = (k₀ : ℝ) + 1 := by
    rw [Nat.cast_sub hk₀]
    ring
  rw [hsub] at htan
  have hk₀_pow : (2 : ℝ) ^ k₀ = 2 * (2 : ℝ) ^ (k₀ - 1) := by
    conv_lhs => rw [show k₀ = (k₀ - 1) + 1 by omega, pow_succ']
  have hk_pow : (1 / 2 : ℝ) ^ k = (1 / 2) * (1 / 2 : ℝ) ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (k₀ - 1) := by positivity
  rw [hk₀_pow, hk_pow]
  have hmul : ((k₀ + 1 : ℝ) - k) / (2 * (2 : ℝ) ^ (k₀ - 1)) =
      (1 / 2) * (((k₀ + 1 : ℝ) / (2 : ℝ) ^ (k₀ - 1)) - (k : ℝ) / (2 : ℝ) ^ (k₀ - 1)) := by
    field_simp
  rw [hmul]
  linarith

/-- Tight universal linear upper bound `4 (1 - 2^{1 - k}) ≤ k` for all `k : ℕ` (with equality at
`k = 0, 2, 3`). -/
theorem four_mul_one_sub_two_pow_le : ∀ k : ℕ, 4 * ((1 : ℝ) - (1 / 2 : ℝ) ^ (k - 1)) ≤ k
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | 3 => by norm_num
  | m + 4 => by
    have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (m + 3) := by positivity
    have hm : (4 : ℝ) ≤ (m + 4 : ℕ) := by exact_mod_cast Nat.le_add_left 4 m
    change 4 * ((1 : ℝ) - (1 / 2 : ℝ) ^ (m + 3)) ≤ (m + 4 : ℕ)
    linarith

/-! ### Product indicator expectations on finite buckets -/

section Concentration

/-- The uniform expectation that all coordinates in `S` satisfy `p` is `(𝔼 a, 1[p a]) ^ |S|`. -/
private theorem expect_all_apply {κ α : Type*} [Fintype κ] [DecidableEq κ] [Fintype α] [Nonempty α]
    (S : Finset κ) (p : α → Prop) [DecidablePred p] :
    (𝔼 ω : κ → α, if ∀ u ∈ S, p (ω u) then (1 : ℝ) else 0) =
      (𝔼 a : α, if p a then (1 : ℝ) else 0) ^ S.card := by
  have hboole (ω : κ → α) :
      (if ∀ u ∈ S, p (ω u) then (1 : ℝ) else 0) =
        ∏ u ∈ S, (if p (ω u) then (1 : ℝ) else 0) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert u₀ S hu₀ ih =>
      rw [Finset.prod_insert hu₀, ← ih]
      by_cases h1 : p (ω u₀) <;> by_cases h2 : ∀ u ∈ S, p (ω u) <;>
        simp [h1, h2]
  simp_rw [hboole]
  clear hboole
  rw [← Finset.prod_const]
  induction S using Finset.induction_on with
  | empty => simp
  | @insert u₀ S hu₀ ih =>
    rw [← Fintype.expect_expect_update
      (fun ω : κ → α => ∏ u ∈ insert u₀ S, if p (ω u) then (1 : ℝ) else 0) u₀]
    have hinner (ω : κ → α) :
        (𝔼 a : α, ∏ u ∈ insert u₀ S, if p (Function.update ω u₀ a u) then (1 : ℝ) else 0) =
          (∏ u ∈ S, if p (ω u) then (1 : ℝ) else 0) * 𝔼 a : α, if p a then (1 : ℝ) else 0 := by
      have hprod (a : α) :
          (∏ u ∈ insert u₀ S, if p (Function.update ω u₀ a u) then (1 : ℝ) else 0) =
            (∏ u ∈ S, if p (ω u) then (1 : ℝ) else 0) * (if p a then (1 : ℝ) else 0) := by
        rw [Finset.prod_insert hu₀, Function.update_self, mul_comm]
        congr 1
        refine Finset.prod_congr rfl fun u hu => ?_
        have hne : u ≠ u₀ := fun heq => hu₀ (heq ▸ hu)
        rw [Function.update_of_ne hne]
      simp_rw [hprod, ← Finset.mul_expect]
    simp_rw [hinner, mul_comm _ (𝔼 a : α, if p a then (1 : ℝ) else 0), ← Finset.mul_expect]
    rw [ih, Finset.prod_insert hu₀]

/-- Uniform probability on `Fin M` of falling strictly below `j ≤ M`. -/
private theorem expect_fin_lt {M j : ℕ} (hj : j ≤ M) :
    (𝔼 a : Fin M, if (a : ℕ) < j then (1 : ℝ) else 0) = (j : ℝ) / M := by
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole, Fintype.card_fin]
  have hcard : (Finset.univ.filter fun a : Fin M => (a : ℕ) < j).card = j := by
    let emb : {k : ℕ // k ∈ Finset.range j} ↪ Fin M :=
      ⟨fun k => ⟨k.val, lt_of_lt_of_le (Finset.mem_range.mp k.property) hj⟩,
        fun _ _ h => Subtype.ext (Fin.mk.inj h)⟩
    have hmap : (Finset.range j).attach.map emb =
        Finset.univ.filter fun a : Fin M => (a : ℕ) < j := by
      ext a
      simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_range,
        Finset.mem_filter, Finset.mem_univ, emb]
      exact ⟨fun ⟨k, hk, heq⟩ => heq ▸ hk, fun ha => ⟨a.val, ha, rfl⟩⟩
    rw [← hmap, Finset.card_map, Finset.card_attach, Finset.card_range]
  rw [hcard]

/-- Uniform probability on `Fin M` of falling at or above `j ≤ M`. -/
private theorem expect_fin_ge {M : ℕ} [NeZero M] {j : ℕ} (hj : j ≤ M) :
    (𝔼 a : Fin M, if j ≤ (a : ℕ) then (1 : ℝ) else 0) = 1 - (j : ℝ) / M := by
  have hcompl (a : Fin M) :
      (if j ≤ (a : ℕ) then (1 : ℝ) else 0) = 1 - if (a : ℕ) < j then (1 : ℝ) else 0 := by
    by_cases h : (a : ℕ) < j
    · have hnot : ¬ j ≤ (a : ℕ) := not_le.mpr h
      simp only [hnot, ↓reduceIte, h, sub_self]
    · have hle : j ≤ (a : ℕ) := not_lt.mp h
      simp only [hle, ↓reduceIte, h, sub_zero]
  simp_rw [hcompl]
  rw [Finset.expect_sub_distrib, Fintype.expect_const, expect_fin_lt hj]

/-- Uniform probability on `Fin M` of hitting bucket `j < M`. -/
private theorem expect_fin_eq {M j : ℕ} (hj : j < M) :
    (𝔼 a : Fin M, if (a : ℕ) = j then (1 : ℝ) else 0) = 1 / (M : ℝ) := by
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole, Fintype.card_fin]
  have hflt : (Finset.univ.filter fun a : Fin M => (a : ℕ) = j) = {⟨j, hj⟩} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  rw [hflt, Finset.card_singleton, Nat.cast_one]

/-- Changing a predicate on a subset `T` changes the cardinality of a filtered finset by at most
`#T`. -/
private theorem abs_card_filter_sub_le {α : Type*} [Fintype α]
    (p q : α → Prop) [DecidablePred p] [DecidablePred q] (T : Finset α)
    (hagree : ∀ x, x ∉ T → (p x ↔ q x)) :
    |((Finset.univ.filter p).card : ℝ) - (Finset.univ.filter q).card| ≤ T.card := by
  classical
  have hsub₁ : Finset.univ.filter p ⊆ Finset.univ.filter q ∪ T := fun x hx => by
    by_cases hxT : x ∈ T
    · exact Finset.mem_union_right _ hxT
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ x, (hagree x hxT).mp (Finset.mem_filter.mp hx).2⟩)
  have hsub₂ : Finset.univ.filter q ⊆ Finset.univ.filter p ∪ T := fun x hx => by
    by_cases hxT : x ∈ T
    · exact Finset.mem_union_right _ hxT
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ x, (hagree x hxT).mpr (Finset.mem_filter.mp hx).2⟩)
  have h1 : (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card + T.card :=
    (Finset.card_le_card hsub₁).trans (Finset.card_union_le _ _)
  have h2 : (Finset.univ.filter q).card ≤ (Finset.univ.filter p).card + T.card :=
    (Finset.card_le_card hsub₂).trans (Finset.card_union_le _ _)
  exact abs_le.mpr ⟨by cast_linarith [h2, h1], by cast_linarith⟩

/-- Updating coordinate `u` of `ω` changes `# {x | P x ω}` by at most `# {x | u ∈ S x}` whenever
`P x` depends only on `S x`. -/
private theorem abs_card_filter_update_le {α κ β : Type*} [Fintype α] [DecidableEq κ]
    (S : α → Finset κ) {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (ω : κ → β) (u : κ) (a b : β)
    (hlocal : ∀ x, (∀ v ∈ S x, Function.update ω u a v = Function.update ω u b v) → (p x ↔ q x)) :
    |((Finset.univ.filter p).card : ℝ) - (Finset.univ.filter q).card| ≤
      (Finset.univ.filter fun x => u ∈ S x).card := by
  refine abs_card_filter_sub_le p q (Finset.univ.filter fun x => u ∈ S x) fun x hx =>
    hlocal x fun v hv => ?_
  have hvu : v ≠ u := fun heq => hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, heq ▸ hv⟩)
  rw [Function.update_of_ne hvu, Function.update_of_ne hvu]

end Concentration

/-! ### Bottom-up splitting of bounded-degree forests -/

section ForestSplit

private def subCompAux {V : Type*} [Fintype V] [DecidableEq V] (parent : V → Option V)
    (rank : V → ℕ) (hrank : ∀ v u, parent v = some u → rank v < rank u) (B : ℕ) :
    (k : ℕ) → {u : V // rank u < k} → Finset V
  | 0, ⟨_, hk⟩ => absurd hk (Nat.not_lt_zero _)
  | k + 1, ⟨u, hk⟩ =>
    insert u ((Finset.univ.filter fun v => parent v = some u).attach.biUnion fun v =>
      have hv : rank v.val < k := by
        have := hrank v.val u (Finset.mem_filter.mp v.property).2
        omega
      let sc := subCompAux parent rank hrank B k ⟨v.val, hv⟩
      if sc.card ≤ B then sc else ∅)

private theorem subCompAux_irrel {V : Type*} [Fintype V] [DecidableEq V] (parent : V → Option V)
    (rank : V → ℕ) (hrank : ∀ v u, parent v = some u → rank v < rank u) (B : ℕ) :
    ∀ (k₁ k₂ : ℕ) (u : V) (h₁ : rank u < k₁) (h₂ : rank u < k₂),
      subCompAux parent rank hrank B k₁ ⟨u, h₁⟩ = subCompAux parent rank hrank B k₂ ⟨u, h₂⟩
  | 0, _, _, h₁, _ => absurd h₁ (Nat.not_lt_zero _)
  | _, 0, _, _, h₂ => absurd h₂ (Nat.not_lt_zero _)
  | k₁ + 1, k₂ + 1, u, h₁, h₂ => by
    simp only [subCompAux]
    congr 1
    refine Finset.biUnion_congr rfl fun v _ => ?_
    have hvp : parent v.val = some u := (Finset.mem_filter.mp v.property).2
    have hv₁ : rank v.val < k₁ := by have := hrank v.val u hvp; omega
    have hv₂ : rank v.val < k₂ := by have := hrank v.val u hvp; omega
    have heq := subCompAux_irrel parent rank hrank B k₁ k₂ v.val hv₁ hv₂
    rw [heq]

private def subComp {V : Type*} [Fintype V] [DecidableEq V] (parent : V → Option V)
    (rank : V → ℕ) (hrank : ∀ v u, parent v = some u → rank v < rank u) (B : ℕ) (u : V) :
    Finset V :=
  subCompAux parent rank hrank B (rank u + 1) ⟨u, Nat.lt_succ_self _⟩

private theorem subComp_eq {V : Type*} [Fintype V] [DecidableEq V] (parent : V → Option V)
    (rank : V → ℕ) (hrank : ∀ v u, parent v = some u → rank v < rank u) (B : ℕ) (u : V) :
    subComp parent rank hrank B u = insert u ((Finset.univ.filter fun v =>
      parent v = some u ∧ (subComp parent rank hrank B v).card ≤ B).biUnion
        (subComp parent rank hrank B)) := by
  ext x
  have hlhs : x ∈ subComp parent rank hrank B u ↔
      x = u ∨ ∃ (v : V) (hvp : parent v = some u),
        let sc := subCompAux parent rank hrank B (rank u) ⟨v, hrank v u hvp⟩
        x ∈ if sc.card ≤ B then sc else ∅ := by
    simp only [subComp, subCompAux, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_attach,
      true_and, Subtype.exists, Finset.mem_filter, Finset.mem_univ]
  rw [hlhs, Finset.mem_insert, Finset.mem_biUnion]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨v, hvp, hx⟩
    have heq : subCompAux parent rank hrank B (rank u) ⟨v, hrank v u hvp⟩ =
        subComp parent rank hrank B v :=
      subCompAux_irrel parent rank hrank B (rank u) (rank v + 1) v (hrank v u hvp)
        (Nat.lt_succ_self _)
    dsimp only at hx
    rw [heq] at hx
    split_ifs at hx with hle
    · exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvp, hle⟩, hx⟩
    · simp at hx
  · rintro ⟨v, hv, hx⟩
    obtain ⟨hvp, hle⟩ := (Finset.mem_filter.mp hv).2
    have heq : subCompAux parent rank hrank B (rank u) ⟨v, hrank v u hvp⟩ =
        subComp parent rank hrank B v :=
      subCompAux_irrel parent rank hrank B (rank u) (rank v + 1) v (hrank v u hvp)
        (Nat.lt_succ_self _)
    refine ⟨v, hvp, ?_⟩
    dsimp only
    rw [heq]
    simp only [hle, ↓reduceIte]
    exact hx

private def walkUp {V : Type*} [Fintype V] [DecidableEq V] (parent : V → Option V)
    (rank : V → ℕ) (hrank : ∀ v u, parent v = some u → rank v < rank u) (B : ℕ) :
    ℕ → V → V
  | 0, x => x
  | fuel + 1, x =>
    match parent x with
    | some p => if (subComp parent rank hrank B x).card ≤ B then
        walkUp parent rank hrank B fuel p else x
    | none => x

private theorem walkUp_irrel {V : Type*} [Fintype V] [DecidableEq V] (parent : V → Option V)
    (rank : V → ℕ) (hrank : ∀ v u, parent v = some u → rank v < rank u) (B : ℕ) :
    ∀ (f₁ f₂ : ℕ) (x : V),
      Finset.univ.sup rank < rank x + f₁ →
      Finset.univ.sup rank < rank x + f₂ →
      walkUp parent rank hrank B f₁ x = walkUp parent rank hrank B f₂ x
  | 0, _, x, h₁, _ => by
    have hx : rank x ≤ Finset.univ.sup rank := Finset.le_sup (Finset.mem_univ x)
    omega
  | _, 0, x, _, h₂ => by
    have hx : rank x ≤ Finset.univ.sup rank := Finset.le_sup (Finset.mem_univ x)
    omega
  | f₁ + 1, f₂ + 1, x, h₁, h₂ => by
    simp only [walkUp]
    cases hp : parent x with
    | none => rfl
    | some p =>
      dsimp only
      split_ifs with hle
      · have hr : rank x < rank p := hrank x p hp
        exact walkUp_irrel parent rank hrank B f₁ f₂ p (by omega) (by omega)
      · rfl

private def pieceRoot {V : Type*} [Fintype V] [DecidableEq V] (parent : V → Option V)
    (rank : V → ℕ) (hrank : ∀ v u, parent v = some u → rank v < rank u) (B : ℕ) (x : V) : V :=
  walkUp parent rank hrank B (Finset.univ.sup rank + 1 - rank x) x

private theorem pieceRoot_eq {V : Type*} [Fintype V] [DecidableEq V] (parent : V → Option V)
    (rank : V → ℕ) (hrank : ∀ v u, parent v = some u → rank v < rank u) (B : ℕ) (x : V) :
    pieceRoot parent rank hrank B x =
      match parent x with
      | some p => if (subComp parent rank hrank B x).card ≤ B then
          pieceRoot parent rank hrank B p else x
      | none => x := by
  have hx : rank x ≤ Finset.univ.sup rank := Finset.le_sup (Finset.mem_univ x)
  have hfuel : Finset.univ.sup rank < rank x + (Finset.univ.sup rank + 1) := by omega
  have hw := walkUp_irrel parent rank hrank B (Finset.univ.sup rank + 1 - rank x)
    (Finset.univ.sup rank + 1) x (by omega) hfuel
  dsimp only [pieceRoot]
  rw [hw]
  simp only [walkUp]
  cases hp : parent x with
  | none => rfl
  | some p =>
    dsimp only
    split_ifs with hle
    · have hr : rank x < rank p := hrank x p hp
      have hp_le : rank p ≤ Finset.univ.sup rank := Finset.le_sup (Finset.mem_univ p)
      exact walkUp_irrel parent rank hrank B (Finset.univ.sup rank)
        (Finset.univ.sup rank + 1 - rank p) p (by omega) (by omega)
    · rfl

/-- **Bottom-up forest partitioning.** Every directed forest on `V` in which each vertex has at most
two incoming edges (`parent v = some u` with `rank v < rank u`) decomposes into pieces
`piece : V → V` of size at most `2 B + 1` severing at most `|V| / (B + 1)` edges. -/
private theorem exists_forest_pieces {V : Type*} [Fintype V] [DecidableEq V]
    (parent : V → Option V) (rank : V → ℕ)
    (hrank : ∀ v u, parent v = some u → rank v < rank u)
    (hdeg : ∀ u : V, (Finset.univ.filter fun v => parent v = some u).card ≤ 2) (B : ℕ) :
    ∃ piece : V → V,
      (∀ r : V, {x : V | piece x = r}.ncard ≤ 2 * B + 1) ∧
      (B + 1) * {v : V | ∃ u, parent v = some u ∧ piece v ≠ piece u}.ncard ≤ Fintype.card V := by
  let sc := subComp parent rank hrank B
  let rt := pieceRoot parent rank hrank B
  have hcard_sc (u : V) : (sc u).card ≤ 2 * B + 1 := by
    dsimp only [sc]
    rw [subComp_eq]
    let kids := Finset.univ.filter fun v => parent v = some u ∧ (sc v).card ≤ B
    have hkids : kids.card ≤ 2 :=
      (Finset.card_le_card fun v hv =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2.1⟩).trans (hdeg u)
    have := Finset.card_biUnion_le_card_mul kids sc B fun v hv => (Finset.mem_filter.mp hv).2.2
    calc (insert u (kids.biUnion sc)).card
        ≤ (kids.biUnion sc).card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 * B + 1 := by nlinarith
  have hmem_rt : ∀ (k : ℕ) (u : V), rank u < k → ∀ x ∈ sc u, rt x = rt u := by
    intro k
    induction k with
    | zero => intro u hk; exact absurd hk (Nat.not_lt_zero _)
    | succ k ih =>
      intro u hk x hx
      dsimp only [sc] at hx
      rw [subComp_eq] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · rfl
      · obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp hx'
        obtain ⟨hvp, hvB⟩ := (Finset.mem_filter.mp hv).2
        have hrv : rank v < k := by have := hrank v u hvp; omega
        have heq₁ : rt x = rt v := ih v hrv x hxv
        have heq₂ : rt v = rt u := by
          dsimp only [rt]
          rw [pieceRoot_eq, hvp]
          simp only [hvB, ↓reduceIte]
        exact heq₁.trans heq₂
  have hsub_rt : ∀ (f : ℕ) (x : V), Finset.univ.sup rank < rank x + f → sc x ⊆ sc (rt x) := by
    intro f
    induction f with
    | zero =>
      intro x hf
      have := Finset.le_sup (f := rank) (Finset.mem_univ x)
      omega
    | succ f ih =>
      intro x hf
      have hrt := pieceRoot_eq parent rank hrank B x
      change rt x = _ at hrt
      cases hp : parent x with
      | none =>
        rw [hp] at hrt
        rw [hrt]
      | some p =>
        rw [hp] at hrt
        dsimp only at hrt
        split_ifs at hrt with hle
        · rw [hrt]
          have hstep : sc x ⊆ sc p := by
            intro z hz
            dsimp only [sc]
            rw [subComp_eq]
            refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨x, ?_, hz⟩)
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hp, hle⟩
          have hr : rank x < rank p := hrank x p hp
          exact hstep.trans (ih p (by omega))
        · rw [hrt]
  refine ⟨rt, fun r => ?_, ?_⟩
  · have hsub : {x : V | rt x = r} ⊆ (sc r : Set V) := by
      intro x (hx : rt x = r)
      subst hx
      refine hsub_rt (Finset.univ.sup rank + 1) x
        (by have := Finset.le_sup (f := rank) (Finset.mem_univ x); omega) ?_
      dsimp only [sc]
      rw [subComp_eq]
      exact Finset.mem_insert_self x _
    exact (ncard_le_ncard hsub (toFinite _)).trans ((ncard_coe_finset (sc r)).trans_le (hcard_sc r))
  · have hheavy : {v : V | ∃ u, parent v = some u ∧ rt v ≠ rt u} ⊆
        {r : V | B + 1 ≤ {x ∈ (univ : Set V) | rt x = r}.ncard} := by
      rintro v ⟨u, hvu, hne⟩
      have hrt := pieceRoot_eq parent rank hrank B v
      change rt v = _ at hrt
      rw [hvu] at hrt
      dsimp only at hrt
      have hnotB : ¬ (subComp parent rank hrank B v).card ≤ B := fun hle => by
        simp only [hle, ↓reduceIte] at hrt
        exact hne hrt
      simp only [hnotB, ↓reduceIte] at hrt
      have hsub : (sc v : Set V) ⊆ {x ∈ (univ : Set V) | rt x = v} := by
        intro x hx
        exact ⟨mem_univ x, (hmem_rt (rank v + 1) v (Nat.lt_succ_self _) x hx).trans hrt⟩
      have hcard := (ncard_coe_finset (sc v)).symm.trans_le (ncard_le_ncard hsub (toFinite _))
      change B + 1 ≤ _
      dsimp only [sc] at hcard
      omega
    calc (B + 1) * {v : V | ∃ u, parent v = some u ∧ rt v ≠ rt u}.ncard
        ≤ (B + 1) * {r : V | B + 1 ≤ {x ∈ (univ : Set V) | rt x = r}.ncard}.ncard :=
          Nat.mul_le_mul_left (B + 1) (ncard_le_ncard hheavy (toFinite _))
      _ ≤ (univ : Set V).ncard :=
          Set.mul_ncard_setOf_le_ncard_fiber_le (toFinite _) rt (B + 1)
      _ = Fintype.card V := by rw [ncard_univ, Nat.card_eq_fintype_card]

end ForestSplit

/-! ### Uniform bucket layouts on `Node c` -/

section BucketLayouts

variable {σ : Signature} {n m : ℕ}

/-- **Master piece-grouped uniform bucket layout.** Given any assignment `piece : Node c → κ` whose
fibers have size at most `R` on a circuit of fan-in at most `r`, and any bucket count `M ≥ 1`, some
layout `π : Layout (Node c)` bounds `signalWidth c π` by
`∑_w (1 - 2^{1 - |piece(support w)|}) + (r + 1)|Node c|/M + (r + 1)√(M R |Node c|)`. -/
theorem exists_layout_signalWidth_of_piece (c : Circuit σ n m) {r : ℕ} (hfan : c.FanInAtMost r)
    {κ : Type*} [Finite κ] [Fintype (ActiveSignal c)]
    (piece : Node c → κ) {R : ℕ} (hR : ∀ u : κ, {v : Node c | piece v = u}.ncard ≤ R)
    {M : ℕ} (hM : 1 ≤ M) :
    ∃ π : Layout (Node c),
      (signalWidth c π : ℝ) ≤
        (∑ w : ActiveSignal c,
          (1 - (1 / 2 : ℝ) ^ ((toFinite (piece '' support c w)).toFinset.card - 1))) +
        ((r + 1) * Nat.card (Node c) : ℝ) / M +
        (r + 1 : ℝ) * √((M * R * Nat.card (Node c) : ℝ)) := by
  classical
  have : NeZero M := ⟨by omega⟩
  have := Fintype.ofFinite κ
  have := Fintype.ofFinite (Node c)
  let P : ActiveSignal c → Finset κ := fun w => (toFinite (piece '' support c w)).toFinset
  have hP_ne (w : ActiveSignal c) : (P w).Nonempty := by
    obtain ⟨v, hv⟩ := support_nonempty w
    exact ⟨piece v, (toFinite _).mem_toFinset.mpr ⟨v, hv, rfl⟩⟩
  have hP_card_le (w : ActiveSignal c) : (P w).card ≤ (support c w).ncard := by
    rw [← ncard_eq_toFinset_card _ (toFinite _)]
    exact ncard_image_le (toFinite _)
  let bad : Fin M → (κ → Fin M) → ActiveSignal c → Prop := fun j ω w =>
    ((∃ u ∈ P w, (ω u : ℕ) < j.val) ∧ (∃ u ∈ P w, j.val ≤ (ω u : ℕ))) ∨
      ∃ u ∈ P w, (ω u : ℕ) = j.val
  let f : Fin M → (κ → Fin M) → ℝ := fun j ω =>
    ((Finset.univ.filter fun w : ActiveSignal c => bad j ω w).card : ℝ)
  let T : κ → Finset (ActiveSignal c) := fun u => Finset.univ.filter fun w => u ∈ P w
  have hosc : ∀ (j : Fin M) (ω : κ → Fin M) (u : κ) (a b : Fin M),
      |f j (Function.update ω u a) - f j (Function.update ω u b)| ≤ (T u).card :=
    fun _ ω u a b => abs_card_filter_update_le P ω u a b fun _ hag => or_congr
      (and_congr (exists_congr fun z => and_congr_right fun hz => by rw [hag z hz])
        (exists_congr fun z => and_congr_right fun hz => by rw [hag z hz]))
      (exists_congr fun z => and_congr_right fun hz => by rw [hag z hz])
  have hT_le (u : κ) : (T u).card ≤ (r + 1) * {v : Node c | piece v = u}.ncard := by
    have hsub : T u ⊆ (Finset.univ.filter fun v => piece v = u).biUnion fun v =>
        Finset.univ.filter fun w : ActiveSignal c => v ∈ support c w := by
      intro w hw
      obtain ⟨v, hv, hpv⟩ := (toFinite _).mem_toFinset.mp (Finset.mem_filter.mp hw).2
      simpa using ⟨v, hpv, hv⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    rw [ncard_eq_toFinset_card', toFinset_ofPred, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun v _ => ?_
    simpa [ncard_eq_toFinset_card'] using ncard_activeSignal_mem_support_le hfan v
  have hsum_sq : ∑ _j : Fin M, ∑ u : κ, ((T u).card : ℝ) ^ 2 ≤
      ((r + 1 : ℝ) ^ 2) * (M * R * Nat.card (Node c)) := by
    have hfib_sum : ∑ u : κ, ({v : Node c | piece v = u}.ncard : ℝ) = Nat.card (Node c) := by
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ,
        Finset.card_eq_sum_card_fiberwise fun v _ => Finset.mem_univ (piece v), Nat.cast_sum]
      simp only [ncard_eq_toFinset_card', toFinset_ofPred]
    have hinner : ∑ u : κ, ((T u).card : ℝ) ^ 2 ≤ ((r + 1 : ℝ) ^ 2 * R) * Nat.card (Node c) := by
      rw [← hfib_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun u _ => ?_
      have hT : ((T u).card : ℝ) ≤ (r + 1) * {v : Node c | piece v = u}.ncard := by
        exact_mod_cast hT_le u
      have huR : ({v : Node c | piece v = u}.ncard : ℝ) ≤ R := by exact_mod_cast hR u
      nlinarith [pow_le_pow_left₀ (Nat.cast_nonneg _) hT 2, mul_nonneg (mul_nonneg
        (sq_nonneg ((r : ℝ) + 1)) (Nat.cast_nonneg {v : Node c | piece v = u}.ncard))
        (sub_nonneg.2 huR)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg (α := ℝ) M)]
  have hexp_f (j : Fin M) :
      (𝔼 ω : κ → Fin M, f j ω) ≤
        (∑ w : ActiveSignal c, (1 - (1 / 2 : ℝ) ^ ((P w).card - 1))) +
        ((r + 1) * Nat.card (Node c) : ℝ) / M := by
    have hterm (w : ActiveSignal c) :
        (𝔼 ω : κ → Fin M, if bad j ω w then (1 : ℝ) else 0) ≤
          (1 - (1 / 2 : ℝ) ^ ((P w).card - 1)) + ((P w).card : ℝ) / M := by
      have hpwise (ω : κ → Fin M) :
          (if bad j ω w then (1 : ℝ) else 0) ≤
            (1 - (if ∀ u ∈ P w, (ω u : ℕ) < j.val then (1 : ℝ) else 0) -
              (if ∀ u ∈ P w, j.val ≤ (ω u : ℕ) then (1 : ℝ) else 0)) +
            ∑ u ∈ P w, if (ω u : ℕ) = j.val then (1 : ℝ) else 0 := by
        obtain ⟨u₀, hu₀⟩ := hP_ne w
        have hS0 : (0 : ℝ) ≤ ∑ u ∈ P w, if (ω u : ℕ) = j.val then (1 : ℝ) else 0 :=
          Finset.sum_nonneg fun _ _ => by positivity
        by_cases ha1 : ∀ u ∈ P w, (ω u : ℕ) < j.val
        · have ha2 : ¬∀ u ∈ P w, j.val ≤ (ω u : ℕ) := fun h => (h u₀ hu₀).not_gt (ha1 u₀ hu₀)
          have hb : ¬bad j ω w := by
            rintro (⟨_, u, hu, h⟩ | ⟨u, hu, h⟩) <;> have := ha1 u hu <;> omega
          simp only [hb, eq_true ha1, ha2, ↓reduceIte]
          linarith
        by_cases ha2 : ∀ u ∈ P w, j.val ≤ (ω u : ℕ)
        · simp only [ha1, eq_true ha2, ↓reduceIte]
          split_ifs with hb
          · obtain ⟨⟨u, hu, h⟩, _⟩ | ⟨u, hu, h⟩ := hb
            · exact absurd (ha2 u hu) (by omega)
            · have h1 := Finset.single_le_sum
                (f := fun u => if (ω u : ℕ) = j.val then (1 : ℝ) else 0)
                (fun _ _ => by positivity) hu
              simp only [h, ↓reduceIte] at h1
              linarith
          · linarith
        · simp only [ha1, ha2, ↓reduceIte]
          split_ifs <;> linarith
      have hexp_le₁ := Finset.expect_le_expect fun ω (_ : ω ∈ Finset.univ) => hpwise ω
      rw [Finset.expect_add_distrib, Finset.expect_sub_distrib, Finset.expect_sub_distrib,
        Fintype.expect_const, expect_all_apply (P w) (fun a : Fin M => (a : ℕ) < j.val),
        expect_all_apply (P w) (fun a : Fin M => j.val ≤ (a : ℕ)),
        expect_fin_lt j.isLt.le, expect_fin_ge j.isLt.le, Finset.expect_sum_comm] at hexp_le₁
      have hone (u : κ) :
          (𝔼 ω : κ → Fin M, if (ω u : ℕ) = j.val then (1 : ℝ) else 0) = 1 / (M : ℝ) := by
        rw [← Fintype.expect_expect_update
          (fun ω : κ → Fin M => if (ω u : ℕ) = j.val then (1 : ℝ) else 0) u]
        simp only [Function.update_self, expect_fin_eq j.isLt, Fintype.expect_const]
      rw [Finset.sum_congr rfl fun u _ => hone u, Finset.sum_const, nsmul_eq_mul,
        mul_one_div] at hexp_le₁
      have h1 : (j.val : ℝ) / M ≤ 1 :=
        (div_le_one (by positivity)).mpr (by exact_mod_cast j.isLt.le)
      have hconv := one_sub_pow_add_pow_le (by positivity) h1 (Finset.card_pos.mpr (hP_ne w))
      linarith
    have hinc : ∑ w : ActiveSignal c, ((P w).card : ℝ) ≤ (r + 1) * Nat.card (Node c) := by
      have h1 : ∑ w : ActiveSignal c, (P w).card ≤ (r + 1) * Nat.card (Node c) := by
        calc ∑ w : ActiveSignal c, (P w).card
            ≤ ∑ w : ActiveSignal c, (support c w).ncard :=
              Finset.sum_le_sum fun w _ => hP_card_le w
          _ ≤ (r + 1) * Nat.card (InnerGate c) + m := sum_ncard_support_le_card_innerGate hfan
          _ ≤ (r + 1) * (Nat.card (InnerGate c) + m) := by nlinarith
          _ = (r + 1) * Nat.card (Node c) := by
              rw [Nat.card_congr (Node.equiv c), Nat.card_sum,
                Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin]
      exact_mod_cast h1
    simp only [f, Finset.natCast_card_filter, Finset.expect_sum_comm]
    have hsum1 := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => hterm w
    rw [Finset.sum_add_distrib, ← Finset.sum_div] at hsum1
    have hdiv := div_le_div_of_nonneg_right hinc (Nat.cast_nonneg M)
    linarith
  obtain ⟨ω, hω⟩ := Fintype.exists_forall_abs_sub_expect_le f (fun _ u => ((T u).card : ℝ))
    (fun _ _ => Nat.cast_nonneg _) hosc
  let score : Node c → ℝ := fun v => ((ω (piece v) : ℕ) : ℝ)
  obtain ⟨π, hπ⟩ := Layout.exists_threshold score
  refine ⟨π, ?_⟩
  rw [← width_steinerGraph_eq]
  have hdev : √(∑ _j : Fin M, ∑ u : κ, ((T u).card : ℝ) ^ 2) ≤
      (r + 1 : ℝ) * √((M * R * Nat.card (Node c) : ℝ)) := by
    calc √(∑ _j : Fin M, ∑ u : κ, ((T u).card : ℝ) ^ 2)
        ≤ √(((r + 1 : ℝ) ^ 2) * (M * R * Nat.card (Node c))) := Real.sqrt_le_sqrt hsum_sq
      _ = (r + 1 : ℝ) * √((M * R * Nat.card (Node c) : ℝ)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hB_nn : 0 ≤ (∑ w : ActiveSignal c, (1 - (1 / 2 : ℝ) ^ ((P w).card - 1))) +
      ((r + 1) * Nat.card (Node c) : ℝ) / M +
      (r + 1 : ℝ) * √((M * R * Nat.card (Node c) : ℝ)) := by
    have hsum_nn : 0 ≤ ∑ w : ActiveSignal c, (1 - (1 / 2 : ℝ) ^ ((P w).card - 1)) :=
      Finset.sum_nonneg fun w _ => sub_nonneg.2 (pow_le_one₀ (by norm_num) (by norm_num))
    positivity
  refine (steinerGraph c π).width_le_of_ncard_frontier_le π hB_nn fun t ht => ?_
  rw [ncard_frontier_steinerGraph_eq]
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · rw [Layout.initial_zero, signalFrontier_empty, ncard_empty, Nat.cast_zero]
    exact hB_nn
  · obtain ⟨μ, hlo, hhi⟩ := hπ t ht
    have hμ0 : 0 ≤ μ := (Nat.cast_nonneg _).trans (hlo (π.symm ⟨0, ht0.trans ht⟩) (by
      rw [Layout.mem_initial, π.apply_symm_apply]
      exact ht0))
    have hμM : μ < M := (hhi (π.symm ⟨t, ht⟩) (by
      rw [Layout.mem_initial, π.apply_symm_apply]
      exact Nat.lt_irrefl t)).trans_lt (by simp only [score]; exact_mod_cast (ω _).isLt)
    let j : Fin M := ⟨⌊μ⌋₊, (Nat.floor_lt hμ0).2 hμM⟩
    have hfront_le : ((signalFrontier c (π.initial t)).ncard : ℝ) ≤ f j ω := by
      rw [ncard_eq_toFinset_card _ (toFinite _)]
      refine Nat.cast_le.mpr (Finset.card_le_card fun w hw => ?_)
      obtain ⟨⟨u, hu, huP⟩, ⟨v, hv, hvPc⟩⟩ := (toFinite _).mem_toFinset.mp hw
      have huP' : piece u ∈ P w := (toFinite _).mem_toFinset.mpr ⟨u, hu, rfl⟩
      have hvP' : piece v ∈ P w := (toFinite _).mem_toFinset.mpr ⟨v, hv, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ w, ?_⟩
      rcases (Nat.le_floor (hlo u huP)).lt_or_eq with hlt | heq
      · exact Or.inl ⟨⟨piece u, huP', hlt⟩, ⟨piece v, hvP', Nat.floor_le_of_le (hhi v hvPc)⟩⟩
      · exact Or.inr ⟨piece u, huP', heq⟩
    linarith [hexp_f j, (le_abs_self _).trans (hω j)]

/-- **Discrete uniform gate-sweep layout.** For any `M ≥ 1` and circuit `c` of fan-in at most `r`,
some layout `π : Layout (Node c)` satisfies
`signalWidth c π ≤ ∑_w (1 - 2^{1 - |support w|}) + (r + 1)|Node c|/M + (r + 1)√(M |Node c|)`. -/
theorem exists_layout_signalWidth_le (c : Circuit σ n m) {r : ℕ} (hfan : c.FanInAtMost r)
    [Fintype (ActiveSignal c)] {M : ℕ} (hM : 1 ≤ M) :
    ∃ π : Layout (Node c),
      (signalWidth c π : ℝ) ≤
        (∑ w : ActiveSignal c, (1 - (1 / 2 : ℝ) ^ ((support c w).ncard - 1))) +
        ((r + 1) * Nat.card (Node c) : ℝ) / M +
        (r + 1 : ℝ) * √((M * Nat.card (Node c) : ℝ)) := by
  obtain ⟨π, hπ⟩ := exists_layout_signalWidth_of_piece c hfan (id : Node c → Node c)
    (R := 1) (fun u => by
      have hsub : {v : Node c | id v = u} = {u} := Set.ext fun _ => Iff.rfl
      rw [hsub, ncard_singleton]) hM
  refine ⟨π, hπ.trans_eq ?_⟩
  have hcard (w : ActiveSignal c) :
      (toFinite ((id : Node c → Node c) '' support c w)).toFinset.card = (support c w).ncard := by
    rw [← ncard_eq_toFinset_card _ (toFinite _), image_id]
  simp_rw [hcard, Nat.cast_one, mul_one]

/-- **Low-reuse uniform gate-sweep layout at fan-in two.** Grouping unit-fanout gate trees into
pieces of size at most `2 B + 1` eliminates unsevered unit-fanout gates from strict cuts, leaving at
most `|Node c| / (2 (B + 1))` from severed tree edges. -/
theorem exists_layout_signalWidth_reuse_le (c : Circuit σ n m) (hfan : c.FanInAtMost 2)
    [Fintype (ActiveSignal c)] [DecidablePred (IsUnitGateSignal c)] (B : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    ∃ π : Layout (Node c),
      (signalWidth c π : ℝ) ≤
        (∑ w : ActiveSignal c with ¬IsUnitGateSignal c w,
          (1 - (1 / 2 : ℝ) ^ ((support c w).ncard - 1))) +
        (Nat.card (Node c) : ℝ) / (2 * (B + 1)) +
        (3 * Nat.card (Node c) : ℝ) / M +
        3 * √((M * (2 * B + 1) * Nat.card (Node c) : ℝ)) := by
  classical
  have := Fintype.ofFinite (Node c)
  let parent : Node c → Option (Node c) := fun v =>
    match v with
    | .output _ => none
    | .gate g =>
      if hg : IsUnitGateSignal c (.gate g) then
        some (exists_support_eq_pair_of_isUnitGateSignal hg).choose
      else none
  have hparent_spec : ∀ v u, parent v = some u →
      ∃ (g : InnerGate c) (hg : IsUnitGateSignal c (.gate g)),
        v = .gate g ∧ (Node.gate g).rank < u.rank ∧ support c (.gate g) = {Node.gate g, u} := by
    intro v u h
    cases v with
    | output _ => cases h
    | gate g =>
      dsimp only [parent] at h
      split_ifs at h with hg
      obtain rfl := Option.some.inj h
      have hspec := (exists_support_eq_pair_of_isUnitGateSignal hg).choose_spec
      exact ⟨g, hg, rfl, hspec.1, hspec.2⟩
  have hrank : ∀ v u, parent v = some u → v.rank < u.rank := fun v u h =>
    let ⟨_, _, hv, hlt, _⟩ := hparent_spec v u h; hv ▸ hlt
  have hdeg : ∀ u : Node c, (Finset.univ.filter fun v => parent v = some u).card ≤ 2 := by
    intro u
    have hsub : (Finset.univ.filter fun v => parent v = some u : Set (Node c)) ⊆
        Node.gate '' {g : InnerGate c | u ∈ support c (.gate g) ∧ Node.gate g ≠ u} := by
      intro v hv
      obtain ⟨g, _, rfl, hlt, hsup⟩ := hparent_spec v u (Finset.mem_filter.mp hv).2
      refine ⟨g, ⟨?_, fun heq => lt_irrefl _ (heq ▸ hlt)⟩, rfl⟩
      rw [hsup]
      exact mem_insert_of_mem _ (mem_singleton u)
    rw [← ncard_coe_finset]
    exact (ncard_le_ncard hsub).trans <| (ncard_image_le (toFinite _)).trans <|
      (ncard_gate_mem_support_ne_le hfan u).trans_eq (by decide)
  obtain ⟨piece, hR, hsev⟩ := exists_forest_pieces parent Node.rank hrank hdeg B
  obtain ⟨π, hπ⟩ := exists_layout_signalWidth_of_piece c hfan piece hR hM
  refine ⟨π, hπ.trans ?_⟩
  let P : ActiveSignal c → Finset (Node c) := fun w => (toFinite (piece '' support c w)).toFinset
  have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ (IsUnitGateSignal c)
    (fun w => (1 - (1 / 2 : ℝ) ^ ((P w).card - 1)))).symm
  have hnonUnit : ∑ w : ActiveSignal c with ¬IsUnitGateSignal c w,
      (1 - (1 / 2 : ℝ) ^ ((P w).card - 1)) ≤
      ∑ w : ActiveSignal c with ¬IsUnitGateSignal c w,
        (1 - (1 / 2 : ℝ) ^ ((support c w).ncard - 1)) := by
    refine Finset.sum_le_sum fun w _ =>
      sub_le_sub_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_) 1
    have hle : (P w).card ≤ (support c w).ncard := by
      rw [← ncard_eq_toFinset_card _ (toFinite _)]
      exact ncard_image_le (toFinite _)
    omega
  have hUnit : ∑ w : ActiveSignal c with IsUnitGateSignal c w,
      (1 - (1 / 2 : ℝ) ^ ((P w).card - 1)) ≤
      (Nat.card (Node c) : ℝ) / (2 * (B + 1)) := by
    let sevSet : Finset (ActiveSignal c) := Finset.univ.filter fun w =>
      IsUnitGateSignal c w ∧ ∃ g u, w = .gate g ∧ parent (.gate g) = some u ∧
        piece (.gate g) ≠ piece u
    have hterm_unit (w : ActiveSignal c) (hw : w ∈ Finset.univ.filter (IsUnitGateSignal c)) :
        (1 - (1 / 2 : ℝ) ^ ((P w).card - 1)) ≤ if w ∈ sevSet then (1 / 2 : ℝ) else 0 := by
      have huw : IsUnitGateSignal c w := (Finset.mem_filter.mp hw).2
      cases w with
      | input _ _ => exact absurd huw id
      | gate g =>
        have hpar : parent (.gate g) =
            some (exists_support_eq_pair_of_isUnitGateSignal huw).choose := by
          simp only [parent, huw, ↓reduceDIte]
        set u := (exists_support_eq_pair_of_isUnitGateSignal huw).choose
        have hsup : support c (.gate g) = {Node.gate g, u} :=
          (exists_support_eq_pair_of_isUnitGateSignal huw).choose_spec.2
        by_cases hneq : piece (.gate g) = piece u
        · have hcard1 : (P (.gate g)).card = 1 := by
            have himg : piece '' support c (.gate g) = {piece u} := by
              rw [hsup, image_pair, hneq, pair_eq_singleton]
            rw [← ncard_eq_toFinset_card _ (toFinite _), himg, ncard_singleton]
          have hnsev : ActiveSignal.gate g ∉ sevSet := by
            intro hmem
            obtain ⟨_, g', u', heq, hp', hne'⟩ := (Finset.mem_filter.mp hmem).2
            cases ActiveSignal.gate.inj heq
            rw [hpar] at hp'
            cases Option.some.inj hp'
            exact hne' hneq
          simp only [hcard1, Nat.sub_self, pow_zero, sub_self, hnsev, ↓reduceIte, le_refl]
        · have hmem : ActiveSignal.gate g ∈ sevSet :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, huw, g, u, rfl, hpar, hneq⟩
          have hcard_le : (P (.gate g)).card ≤ 2 := by
            rw [← ncard_eq_toFinset_card _ (toFinite _)]
            exact (ncard_image_le (toFinite _)).trans_eq (ncard_support_gate_eq_two huw)
          have hp : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ ((P (.gate g)).card - 1) :=
            (pow_one _).symm.trans_le (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
          simp only [hmem, ↓reduceIte]
          linarith
    have hsev_card : sevSet.card ≤
        {v : Node c | ∃ u, parent v = some u ∧ piece v ≠ piece u}.ncard := by
      let toOpt : ActiveSignal c → Option (Node c)
        | .gate g => some (.gate g)
        | .input _ _ => none
      rw [← ncard_coe_finset]
      refine (ncard_le_ncard_of_injOn toOpt (fun w hw => ?_) (fun a ha b hb h => ?_)).trans_eq
        (ncard_image_of_injective _ (Option.some_injective _))
      · obtain ⟨_, g, u, rfl, hp, hne⟩ := (Finset.mem_filter.mp hw).2
        exact ⟨.gate g, ⟨u, hp, hne⟩, rfl⟩
      · obtain ⟨_, g₁, _, rfl, _, _⟩ := (Finset.mem_filter.mp ha).2
        obtain ⟨_, g₂, _, rfl, _, _⟩ := (Finset.mem_filter.mp hb).2
        cases Node.gate.inj (Option.some.inj h)
        rfl
    have hsevR : ((B + 1 : ℝ)) * sevSet.card ≤ Nat.card (Node c) := by
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast (Nat.mul_le_mul_left (B + 1) hsev_card).trans hsev
    have hBpos : (0 : ℝ) < 2 * (B + 1) := by positivity
    calc ∑ w : ActiveSignal c with IsUnitGateSignal c w, (1 - (1 / 2 : ℝ) ^ ((P w).card - 1))
        ≤ ∑ w ∈ Finset.univ.filter (IsUnitGateSignal c),
            if w ∈ sevSet then (1 / 2 : ℝ) else 0 := Finset.sum_le_sum hterm_unit
      _ ≤ ∑ w : ActiveSignal c, if w ∈ sevSet then (1 / 2 : ℝ) else 0 :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => by split_ifs <;> norm_num
      _ = (sevSet.card : ℝ) / 2 := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ (Nat.card (Node c) : ℝ) / (2 * (B + 1)) := by
          rw [div_le_div_iff₀ two_pos hBpos]
          linarith
  have h21 : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
  have h2B1 : ((2 * B + 1 : ℕ) : ℝ) = 2 * (B : ℝ) + 1 := by push_cast; ring
  rw [h21, h2B1]
  linarith [hsplit, hnonUnit, hUnit]

/-! ### Balanced two-colorings on `Node c` for quadratic-form correlation -/

private theorem card_filter_mem_support_le_deg {c : Circuit σ n m} {α : Type*} [Fintype α]
    (emb : α ↪ ActiveSignal c) (u : Node c) :
    (Finset.univ.filter fun x : α =>
      u ∈ (toFinite (support c (emb x))).toFinset).card ≤
      {w : ActiveSignal c | u ∈ support c w}.ncard := by
  let T := Finset.univ.filter fun x : α => u ∈ (toFinite (support c (emb x))).toFinset
  have hsub : (T.map emb : Set (ActiveSignal c)) ⊆ {w | u ∈ support c w} := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hw
    exact (toFinite (support c (emb x))).mem_toFinset.mp (Finset.mem_filter.mp hx).2
  calc T.card = (T.map emb).card := (Finset.card_map emb).symm
    _ = (T.map emb : Set (ActiveSignal c)).ncard := (ncard_coe_finset _).symm
    _ ≤ {w : ActiveSignal c | u ∈ support c w}.ncard := ncard_le_ncard hsub (toFinite _)

/-- **Simultaneous two-coloring margin on `Node c`.** Under a uniform `Node c → Bool` cut, some
node set `A ⊆ Node c` simultaneously makes the monochromatic reachable input sets `L` (in `A`) and
`R'` (in `Aᶜ`) at least `∑_i 2^{-|support i|} - (r + 1)√(3 |Node c|)` while cutting at most
`∑_g (1 - 2^{1 - |support g|}) + (r + 1)√(3 |Node c|)` inner-gate signals. -/
theorem exists_node_cut_margin (c : Circuit σ n m) {r : ℕ} (hfan : c.FanInAtMost r)
    [Fintype {i : Fin n // Reach c (.input i)}] [Fintype (InnerGate c)] :
    ∃ A : Set (Node c),
      (∑ i : {i : Fin n // Reach c (.input i)},
        (1 / 2 : ℝ) ^ (support c (.input i.val i.property)).ncard) -
        (r + 1 : ℝ) * √(3 * (Nat.card (Node c) : ℝ)) ≤
          ({i : Fin n | ∃ hi : Reach c (.input i), support c (.input i hi) ⊆ A}.ncard : ℝ) ∧
      (∑ i : {i : Fin n // Reach c (.input i)},
        (1 / 2 : ℝ) ^ (support c (.input i.val i.property)).ncard) -
        (r + 1 : ℝ) * √(3 * (Nat.card (Node c) : ℝ)) ≤
          ({i : Fin n | ∃ hi : Reach c (.input i), support c (.input i hi) ⊆ Aᶜ}.ncard : ℝ) ∧
      ({g : InnerGate c | ActiveSignal.gate g ∈ signalFrontier c A}.ncard : ℝ) ≤
        (∑ g : InnerGate c, (1 - (1 / 2 : ℝ) ^ ((support c (.gate g)).ncard - 1))) +
          (r + 1 : ℝ) * √(3 * (Nat.card (Node c) : ℝ)) := by
  classical
  have := Fintype.ofFinite (Node c)
  let emb_in : {i : Fin n // Reach c (.input i)} ↪ ActiveSignal c :=
    ⟨fun x => .input x.val x.property, fun _ _ h => Subtype.ext (ActiveSignal.input.inj h)⟩
  let emb_gt : InnerGate c ↪ ActiveSignal c :=
    ⟨ActiveSignal.gate, fun _ _ h => ActiveSignal.gate.inj h⟩
  let S_in (x : {i : Fin n // Reach c (.input i)}) : Finset (Node c) :=
    (toFinite (support c (.input x.val x.property))).toFinset
  let S_gt (g : InnerGate c) : Finset (Node c) :=
    (toFinite (support c (.gate g))).toFinset
  let f : Fin 3 → (Node c → Bool) → ℝ
    | ⟨0, _⟩, ω => ((Finset.univ.filter fun x : {i : Fin n // Reach c (.input i)} =>
        ∀ v ∈ S_in x, ω v = false).card : ℝ)
    | ⟨1, _⟩, ω => ((Finset.univ.filter fun x : {i : Fin n // Reach c (.input i)} =>
        ∀ v ∈ S_in x, ω v = true).card : ℝ)
    | ⟨2, _⟩, ω => ((Finset.univ.filter fun g : InnerGate c =>
        (∃ v ∈ S_gt g, ω v = false) ∧ (∃ v ∈ S_gt g, ω v = true)).card : ℝ)
  let deg (u : Node c) : ℕ := {w : ActiveSignal c | u ∈ support c w}.ncard
  have hdeg_le (u : Node c) : deg u ≤ r + 1 := ncard_activeSignal_mem_support_le hfan u
  have hosc : ∀ (j : Fin 3) (ω : Node c → Bool) (u : Node c) (a b : Bool),
      |f j (Function.update ω u a) - f j (Function.update ω u b)| ≤ deg u := by
    rintro ⟨j, hj⟩ ω u a b
    match j, hj with
    | 0, _ | 1, _ =>
      exact (abs_card_filter_update_le S_in ω u a b fun _ h =>
        forall₂_congr fun v hv => by rw [h v hv]).trans
          (Nat.cast_le.mpr (card_filter_mem_support_le_deg emb_in u))
    | 2, _ =>
      exact (abs_card_filter_update_le S_gt ω u a b fun _ h => and_congr
        (exists_congr fun v => and_congr_right fun hv => by rw [h v hv])
        (exists_congr fun v => and_congr_right fun hv => by rw [h v hv])).trans
          (Nat.cast_le.mpr (card_filter_mem_support_le_deg emb_gt u))
    | k + 3, hk => exact absurd hk (by omega)
  obtain ⟨ω, hω⟩ := Fintype.exists_forall_abs_sub_expect_le f (fun _ u => (deg u : ℝ))
    (fun _ _ => Nat.cast_nonneg _) hosc
  have hdev : √(∑ _j : Fin 3, ∑ u : Node c, (deg u : ℝ) ^ 2) ≤
      (r + 1 : ℝ) * √(3 * (Nat.card (Node c) : ℝ)) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    refine (Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun u _ =>
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hdeg_le u : (deg u : ℝ) ≤ r + 1)
        2).trans_eq ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.card_eq_fintype_card]
    ring
  have hexp0 (b : Bool) :
      (𝔼 ω' : Node c → Bool,
        ((Finset.univ.filter fun x : {i : Fin n // Reach c (.input i)} =>
          ∀ v ∈ S_in x, ω' v = b).card : ℝ)) =
        ∑ x : {i : Fin n // Reach c (.input i)},
          (1 / 2 : ℝ) ^ (support c (.input x.val x.property)).ncard := by
    simp only [Finset.natCast_card_filter, Finset.expect_sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [expect_all_apply (S_in x) (fun a : Bool => a = b), Fintype.expect_bool,
      ← ncard_eq_toFinset_card _ (toFinite (support c (.input x.val x.property)))]
    cases b <;> norm_num
  have hexp2 :
      (𝔼 ω' : Node c → Bool, f ⟨2, by decide⟩ ω') =
        ∑ g : InnerGate c, (1 - (1 / 2 : ℝ) ^ ((support c (.gate g)).ncard - 1)) := by
    dsimp only [f]
    simp only [Finset.natCast_card_filter, Finset.expect_sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    obtain ⟨v₀, hv₀⟩ := support_nonempty (.gate g)
    have hv₀' : v₀ ∈ S_gt g := (toFinite _).mem_toFinset.mpr hv₀
    have hstr (ω' : Node c → Bool) :
        (if (∃ v ∈ S_gt g, ω' v = false) ∧ (∃ v ∈ S_gt g, ω' v = true) then (1 : ℝ) else 0) =
          1 - (if ∀ v ∈ S_gt g, ω' v = false then (1 : ℝ) else 0) -
            (if ∀ v ∈ S_gt g, ω' v = true then (1 : ℝ) else 0) := by
      by_cases hf0 : ∀ v ∈ S_gt g, ω' v = false
      · have hf1 : ¬∀ v ∈ S_gt g, ω' v = true := fun h => by simpa [hf0 v₀ hv₀'] using h v₀ hv₀'
        have hn : ¬((∃ v ∈ S_gt g, ω' v = false) ∧ ∃ v ∈ S_gt g, ω' v = true) :=
          fun ⟨_, v, hv, h⟩ => by simp [hf0 v hv] at h
        simp only [hn, eq_true hf0, hf1, ↓reduceIte]
        norm_num
      by_cases hf1 : ∀ v ∈ S_gt g, ω' v = true
      · have hn : ¬((∃ v ∈ S_gt g, ω' v = false) ∧ ∃ v ∈ S_gt g, ω' v = true) :=
          fun ⟨⟨v, hv, h⟩, _⟩ => by simp [hf1 v hv] at h
        simp only [hn, hf0, eq_true hf1, ↓reduceIte]
        norm_num
      · have hy : (∃ v ∈ S_gt g, ω' v = false) ∧ ∃ v ∈ S_gt g, ω' v = true := by
          push Not at hf0 hf1
          simp only [ne_eq, Bool.not_eq_true, Bool.not_eq_false] at hf0 hf1
          exact ⟨hf1, hf0⟩
        simp only [hy, hf0, hf1, ↓reduceIte]
        norm_num
    simp_rw [hstr]
    rw [Finset.expect_sub_distrib, Finset.expect_sub_distrib, Fintype.expect_const,
      expect_all_apply (S_gt g) (fun a : Bool => a = false),
      expect_all_apply (S_gt g) (fun a : Bool => a = true),
      Fintype.expect_bool, Fintype.expect_bool]
    have hcard_eq : (S_gt g).card = (support c (.gate g)).ncard :=
      (ncard_eq_toFinset_card _ (toFinite _)).symm
    rw [hcard_eq]
    have hk' : (support c (.gate g)).ncard = ((support c (.gate g)).ncard - 1) + 1 := by
      have := two_le_ncard_support_gate g
      omega
    have hpow2 : 2 * (1 / 2 : ℝ) ^ (support c (.gate g)).ncard =
        (1 / 2 : ℝ) ^ ((support c (.gate g)).ncard - 1) := by
      conv_lhs => rw [hk', pow_succ']
      ring
    norm_num at hpow2 ⊢
    linarith
  let A : Set (Node c) := {v | ω v = false}
  have hcard_in (b : Bool) (B : Set (Node c)) (hB : ∀ v, v ∈ B ↔ ω v = b) :
      ({i : Fin n | ∃ hi : Reach c (.input i), support c (.input i hi) ⊆ B}.ncard : ℝ) =
        (Finset.univ.filter fun x : {i : Fin n // Reach c (.input i)} =>
          ∀ v ∈ S_in x, ω v = b).card := by
    let S_b := Finset.univ.filter fun x : {i : Fin n // Reach c (.input i)} =>
      ∀ v ∈ S_in x, ω v = b
    have himg : (Subtype.val '' (S_b : Set {i : Fin n // Reach c (.input i)})) =
        {i : Fin n | ∃ hi : Reach c (.input i), support c (.input i hi) ⊆ B} := by
      ext i
      simp only [mem_image, Finset.mem_coe, S_b, Finset.mem_filter, Finset.mem_univ, true_and,
        Subtype.exists, S_in, Finite.mem_toFinset, subset_def, hB]
      exact ⟨fun ⟨a, h, hv, ha⟩ => ha ▸ ⟨h, hv⟩, fun ⟨hi, hv⟩ => ⟨i, hi, hv, rfl⟩⟩
    rw [← himg, ncard_image_of_injective _ Subtype.val_injective, ncard_coe_finset]
  refine ⟨A, ?_, ?_, ?_⟩
  · have hcardL : ({i : Fin n | ∃ hi : Reach c (.input i), support c (.input i hi) ⊆ A}.ncard : ℝ) =
        f ⟨0, by decide⟩ ω := hcard_in false A fun _ => Iff.rfl
    have hb0 := (abs_le.mp (hω ⟨0, by decide⟩)).1
    have hm0 : 𝔼 ω', f ⟨0, by decide⟩ ω' = _ := hexp0 false
    linarith
  · have hcardR :
        ({i : Fin n | ∃ hi : Reach c (.input i), support c (.input i hi) ⊆ Aᶜ}.ncard : ℝ) =
          f ⟨1, by decide⟩ ω :=
      hcard_in true Aᶜ fun _ => by simp only [A, mem_compl_iff, mem_ofPred_eq, Bool.not_eq_false]
    have hb1 := (abs_le.mp (hω ⟨1, by decide⟩)).1
    have hm1 : 𝔼 ω', f ⟨1, by decide⟩ ω' = _ := hexp0 true
    linarith
  · have hcardG : ({g : InnerGate c | ActiveSignal.gate g ∈ signalFrontier c A}.ncard : ℝ) =
        f ⟨2, by decide⟩ ω := by
      let S₂ := Finset.univ.filter fun g : InnerGate c =>
        (∃ v ∈ S_gt g, ω v = false) ∧ (∃ v ∈ S_gt g, ω v = true)
      have heq : (S₂ : Set (InnerGate c)) =
          {g : InnerGate c | ActiveSignal.gate g ∈ signalFrontier c A} := by
        ext g
        simp only [Finset.mem_coe, S₂, Finset.mem_filter, Finset.mem_univ, true_and, S_gt,
          Finite.mem_toFinset, signalFrontier, A, mem_compl_iff, mem_ofPred_eq, Bool.not_eq_false,
          Set.Nonempty, mem_inter_iff]
      rw [← heq, ncard_coe_finset]
    have hb2 := (abs_le.mp (hω ⟨2, by decide⟩)).2
    linarith [hexp2]

end BucketLayouts

end Cslib.Circuits.Frontier.Compiler
