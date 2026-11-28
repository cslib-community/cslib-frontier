/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Gate
import CslibFrontier.Foundations.Data.List.FlatMapRange
import CslibFrontier.Foundations.Data.List.GetD
import Mathlib.Data.List.GetD

/-!
# Gadgets define their fresh variables in order

A list of gates *defines* the variables `β, β + 1, …` when its gate `i` is a defining gate (its
operation `Gate.Op.IsDefining`) with output `β + i` whose arguments are smaller than `β + i`
(`Cslib.Complexity.CookLevin.Quasilinear.Defining`). Then any assignment of the variables below
`β` extends to one satisfying all its gates (`Cslib.Complexity.CookLevin.Quasilinear.
exists_extension`, with the rank `id`). Each gadget of
`CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Gate` defines its fresh variables
when its inputs are below its base.

## Main definitions

* `Cslib.Complexity.CookLevin.Quasilinear.Defining`.

## Main results

* `Cslib.Complexity.CookLevin.Quasilinear.defining_cons_iff`,
  `Cslib.Complexity.CookLevin.Quasilinear.defining_append`.
* `Cslib.Complexity.CookLevin.Quasilinear.defining_eqGadget`, `defining_ltGadget`,
  `defining_addGadget`, `defining_matchGadget`, `defining_tableGadget`.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Quasilinear

/-- The gates of `l` define the variables `β, β + 1, …` in order, each from smaller variables. -/
def Defining (β : ℕ) (l : List Gate) : Prop :=
  ∀ i (h : i < l.length), l[i].op.IsDefining ∧ l[i].out = β + i ∧ l[i].a < β + i ∧ l[i].b < β + i ∧
    l[i].c < β + i

/-- No gates define nothing. -/
@[simp] theorem defining_nil (β : ℕ) : Defining β [] := fun _ h => absurd h (by simp)

/-- The gates of two lists define one after the other. -/
theorem defining_append {β : ℕ} {l₁ l₂ : List Gate} (h₁ : Defining β l₁)
    (h₂ : Defining (β + l₁.length) l₂) : Defining β (l₁ ++ l₂) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases hi₁ : i < l₁.length
  · rw [List.getElem_append_left hi₁]
    exact h₁ i hi₁
  · rw [List.getElem_append_right (by omega)]
    obtain ⟨h1, h2, h3, h4, h5⟩ := h₂ (i - l₁.length) (by omega)
    exact ⟨h1, by rw [h2]; omega, by omega, by omega, by omega⟩

/-- Blocks of `K` gates, the `i`-th defining from `β + K * i`, define in order. -/
private theorem defining_flatMap_range {β K : ℕ} {T : ℕ → List Gate} (hT : ∀ i, (T i).length = K)
    (hdef : ∀ i, Defining (β + K * i) (T i)) (m : ℕ) :
    Defining β ((List.range m).flatMap T) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append]
    refine defining_append ih ?_
    rw [List.length_flatMap_range hT]
    simpa using hdef m

/-- **A gate followed by gates defines** when the gate is a defining gate with output `β` and
arguments below `β`, and the rest define from `β + 1`. -/
@[simp] theorem defining_cons_iff {β : ℕ} {g : Gate} {l : List Gate} :
    Defining β (g :: l) ↔
      (g.op.IsDefining ∧ g.out = β ∧ g.a < β ∧ g.b < β ∧ g.c < β) ∧ Defining (β + 1) l := by
  constructor
  · intro h
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    refine ⟨h0, fun i hi => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := h (i + 1) (by simpa using hi)
    simp only [List.getElem_cons_succ] at h1 h2 h3 h4 h5
    exact ⟨h1, by omega, by omega, by omega, by omega⟩
  · rintro ⟨hg, hl⟩ i hi
    rcases i with _ | i
    · simpa using hg
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hl i (by simpa using hi)
      simp only [List.getElem_cons_succ]
      exact ⟨h1, by omega, by omega, by omega, by omega⟩

section Gadgets

variable {β : ℕ}

/-- Defaulted lookups of a list of pairs of variables below `β` are below `β`. -/
private theorem getD_lt_of_forall {l : List (ℕ × ℕ)} (hl : ∀ p ∈ l, p.1 < β ∧ p.2 < β) (hβ : 0 < β)
    (i : ℕ) : (l.getD i (0, 0)).1 < β ∧ (l.getD i (0, 0)).2 < β := by
  by_cases hi : i < l.length
  · exact hl _ (List.getD_mem _ hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    simpa using hβ

/-- The equality gadget has two gates per pair. -/
@[simp] theorem length_eqGadget (β tt : ℕ) (ps : List (ℕ × ℕ)) :
    (eqGadget β tt ps).length = 2 * ps.length := by
  unfold eqGadget
  apply List.length_flatMap_range
  intro i
  rfl

/-- The equality gadget defines its fresh variables in order. -/
theorem defining_eqGadget {tt : ℕ} {ps : List (ℕ × ℕ)} (hps : ∀ p ∈ ps, p.1 < β ∧ p.2 < β)
    (htt : tt < β) : Defining β (eqGadget β tt ps) := by
  have hβ : 0 < β := by omega
  refine defining_flatMap_range (K := 2) (fun _ => rfl) (fun i => ?_) _
  have h := getD_lt_of_forall hps hβ i
  simp only [defining_cons_iff, defining_nil, Gate.Op.IsDefining, ne_eq, reduceCtorEq,
    not_false_eq_true, and_true, true_and]
  split_ifs <;> omega

/-- The comparison gadget has five gates per digit. -/
@[simp] theorem length_ltGadget (β ff : ℕ) (ps : List (ℕ × ℕ)) :
    (ltGadget β ff ps).length = 5 * ps.length := by
  unfold ltGadget
  apply List.length_flatMap_range
  intro i
  rfl

/-- The comparison gadget defines its fresh variables in order. -/
theorem defining_ltGadget {ff : ℕ} {ps : List (ℕ × ℕ)} (hps : ∀ p ∈ ps, p.1 < β ∧ p.2 < β)
    (hff : ff < β) : Defining β (ltGadget β ff ps) := by
  have hβ : 0 < β := by omega
  refine defining_flatMap_range (K := 5) (fun _ => rfl) (fun i => ?_) _
  have h := getD_lt_of_forall hps hβ i
  simp only [defining_cons_iff, defining_nil, Gate.Op.IsDefining, ne_eq, reduceCtorEq,
    not_false_eq_true, and_true, true_and]
  split_ifs <;> omega

/-- The addition gadget has nine gates per digit. -/
@[simp] theorem length_addGadget (β tt P Q : ℕ) (ps : List (ℕ × ℕ)) :
    (addGadget β tt P Q ps).length = 9 * ps.length := by
  unfold addGadget
  apply List.length_flatMap_range
  intro i
  rfl

/-- The addition gadget defines its fresh variables in order. -/
theorem defining_addGadget {tt P Q : ℕ} {ps : List (ℕ × ℕ)}
    (hps : ∀ p ∈ ps, p.1 < β ∧ p.2 < β) (htt : tt < β) (hP : P < β) (hQ : Q < β) :
    Defining β (addGadget β tt P Q ps) := by
  have hβ : 0 < β := by omega
  refine defining_flatMap_range (K := 9) (fun _ => rfl) (fun i => ?_) _
  have h := getD_lt_of_forall hps hβ i
  simp only [defining_cons_iff, defining_nil, Gate.Op.IsDefining, ne_eq, reduceCtorEq,
    not_false_eq_true, and_true, true_and]
  split_ifs <;> omega

/-- The match gadget has two gates per literal. -/
@[simp] theorem length_matchGadget (β tt : ℕ) (lits : List (ℕ × Bool)) :
    (matchGadget β tt lits).length = 2 * lits.length := by
  unfold matchGadget
  apply List.length_flatMap_range
  intro i
  rfl

/-- The match gadget defines its fresh variables in order. -/
theorem defining_matchGadget {tt : ℕ} {lits : List (ℕ × Bool)} (hl : ∀ l ∈ lits, l.1 < β)
    (htt : tt < β) : Defining β (matchGadget β tt lits) := by
  have hβ : 0 < β := by omega
  refine defining_flatMap_range (K := 2) (fun _ => rfl) (fun i => ?_) _
  have h : (lits.getD i (0, true)).1 < β := by
    by_cases hi : i < lits.length
    · exact hl _ (List.getD_mem _ hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      simpa using hβ
  simp only [defining_cons_iff, defining_nil, Gate.Op.IsDefining, ne_eq, reduceCtorEq,
    not_false_eq_true, and_true, true_and]
  split_ifs <;> omega

/-- The table gadget has `2 w` gates per pattern and one more gate per pattern. -/
theorem length_tableGadget (β tt ff w : ℕ) {pats : List (List (ℕ × Bool))}
    (hlen : ∀ π ∈ pats, π.length = w) :
    (tableGadget β tt ff w pats).length = 2 * w * pats.length + pats.length := by
  have hT : ∀ r, (matchGadget (β + 2 * w * r) tt (pats.getD r [])).length = 2 * w ∨
      pats.length ≤ r := by
    intro r
    rw [length_matchGadget]
    rw [List.getD_eq_getElem?_getD]
    rcases h : pats[r]? with _ | π
    · right
      simpa using h
    · left
      simp [hlen π (List.mem_of_getElem? h)]
  unfold tableGadget
  rw [List.length_append, List.length_map, List.length_range]
  congr 1
  -- the blocks below the number of patterns have length `2 w`
  have : ∀ m ≤ pats.length, ((List.range m).flatMap fun r =>
      matchGadget (β + 2 * w * r) tt (pats.getD r [])).length = 2 * w * m := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ih (by omega)]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rcases hT m with h | h
      · rw [h, Nat.mul_succ]
      · omega
  exact this _ le_rfl

/-- The table gadget defines its fresh variables in order. -/
theorem defining_tableGadget {tt ff w : ℕ} {pats : List (List (ℕ × Bool))}
    (hpats : ∀ π ∈ pats, π.length = w ∧ ∀ l ∈ π, l.1 < β) (htt : tt < β) (hff : ff < β) :
    Defining β (tableGadget β tt ff w pats) := by
  have hβ : 0 < β := by omega
  unfold tableGadget
  -- the match blocks
  have hblocks : ∀ m ≤ pats.length, Defining β ((List.range m).flatMap fun r =>
      matchGadget (β + 2 * w * r) tt (pats.getD r [])) ∧
      ((List.range m).flatMap fun r =>
        matchGadget (β + 2 * w * r) tt (pats.getD r [])).length = 2 * w * m := by
    intro m hm
    induction m with
    | zero => exact ⟨by simp, by simp⟩
    | succ m ih =>
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hmem : pats.getD m [] ∈ pats := List.getD_mem _ (by omega)
      obtain ⟨hl, hlt⟩ := hpats _ hmem
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine ⟨defining_append ih1 ?_, ?_⟩
      · rw [ih2]
        exact defining_matchGadget (fun l hl' => by have := hlt l hl'; omega) (by omega)
      · rw [List.length_append, ih2, length_matchGadget, hl, Nat.mul_succ]
  obtain ⟨hb1, hb2⟩ := hblocks _ le_rfl
  refine defining_append hb1 ?_
  rw [hb2]
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  simp only [List.getElem_map, List.getElem_range]
  refine ⟨by simp [Gate.Op.IsDefining], by trivial, ?_, ?_, by omega⟩
  · split_ifs <;> omega
  · have hmem : pats.getD i [] ∈ pats := List.getD_mem _ hi
    obtain ⟨hl, -⟩ := hpats _ hmem
    unfold matchOut
    rw [hl]
    split_ifs with hw
    · omega
    · have : 2 * w * i + 2 * w ≤ 2 * w * pats.length := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ hi
      omega

end Gadgets

end Cslib.Complexity.CookLevin.Quasilinear
