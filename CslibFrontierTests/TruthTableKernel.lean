/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Reduction.TruthTable

/-! The resource-parametric truth-table, positive truth-table, `(k₁ * k₂)` bounded composition, and
self-query-avoiding autoreduction APIs work without importing machines or complexity classes. -/

namespace CslibFrontierTests.TruthTableKernel

open Cslib.Complexity

/-! ### Bounded `(k₁ * k₂)` truth-table composition and slice recovery -/

/-- Direct check of `truthTableAnswers_drop_take` on a `2 * 3` block-indexed batch. -/
example (C : Set ℕ) (a : ℕ) :
    let q₁ : ℕ × ℕ → ℕ := fun p => 10 * p.1 + p.2
    let r₂ : ℕ → ℕ := fun b => b % 3 + 1
    let q₂ : ℕ × ℕ → ℕ := fun p => 100 * p.1 + p.2
    let Q := truthTableCompQuery q₁ q₂ fun _ => 3
    ((truthTableAnswers (Q ⁻¹' C) (fun _ => 2 * 3) a).drop (1 * 3)).take (r₂ (q₁ (a, 1))) =
      truthTableAnswers (q₂ ⁻¹' C) r₂ (q₁ (a, 1)) := by
  intro q₁ r₂ q₂ Q
  have hr₂ : r₂ (q₁ (a, 1)) ≤ 3 := by dsimp [r₂]; omega
  exact truthTableAnswers_drop_take (by dsimp; omega) fun j hj =>
    truthTableCompQuery_mul_add q₁ q₂ (fun _ => 3) a 1 (hj.trans_le hr₂)

/-- Composing a `2`-query XOR reduction with itself via `TruthTableReducibleBy.trans_bounded` gives
a `4`-query reduction. -/
example (C : Set ℕ) :
    let step (X : Set ℕ) : Set ℕ := {n | (2 * n ∈ X) ≠ (2 * n + 1 ∈ X)}
    TruthTableReducibleBy (fun r _ _ => ∀ a, r a ≤ 4) (step (step C)) C := by
  intro step
  have hstep : ∀ X : Set ℕ, TruthTableReducibleBy (fun r _ _ => ∀ a, r a ≤ 2) (step X) X := by
    intro X
    classical
    refine ⟨fun _ => 2, fun p => 2 * p.1 + p.2,
      fun x => x.2.headD false ^^ (x.2.drop 1).headD false, fun _ => le_rfl, fun n => ?_⟩
    simp only [step, Set.mem_ofPred_eq, truthTableAnswers, Set.mem_preimage]
    by_cases h₀ : 2 * n ∈ X <;> by_cases h₁ : 2 * n + 1 ∈ X <;>
      simp [List.ofFn_succ, h₀, h₁]
  exact TruthTableReducibleBy.trans_bounded (k₁ := 2) (k₂ := 2)
    (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ hmul => hmul)
    (hstep (step C)) (hstep C)

/-! ### Bounded `DTT` and `CTT` composition with variable/zero inner counts -/

/-- `DTTReducibleBy.trans_bounded` remains exact even when the inner query count is `0 < k₂` and an
unused inner query slot lands in the target `{true}`. -/
example :
    DTTReducibleBy (fun r _ => ∀ a, r a ≤ 1 * 2) (∅ : Set Bool) ({true} : Set Bool) := by
  have h₁ : DTTReducibleBy (fun r _ => ∀ a, r a ≤ 1) (∅ : Set Bool) (∅ : Set Bool) :=
    ⟨fun _ => 1, fun _ => false, fun _ => le_rfl, fun _ => by simp⟩
  -- `r₂` asks `0 ≤ 2` queries, while unused index `1` maps to `true ∈ {true}`.
  have h₂ : DTTReducibleBy (fun r _ => ∀ b, r b ≤ 2) (∅ : Set Bool) ({true} : Set Bool) :=
    ⟨fun _ => 0, fun p => decide (p.2 = 1), fun _ => Nat.zero_le _, fun _ => by simp⟩
  exact DTTReducibleBy.trans_bounded (fun _ _ h => h) (fun _ _ h => h)
    (fun _ _ _ _ _ _ hmul => hmul) h₁ h₂

/-- `CTTReducibleBy.trans_bounded` composes bounded conjunctive reductions with bound `k₁ * k₂`. -/
example (C : Set ℕ) :
    CTTReducibleBy (fun r _ => ∀ a, r a ≤ 2 * 2)
      {n | (n ∈ C ∧ n + 1 ∈ C) ∧ (n + 2 ∈ C ∧ n + 3 ∈ C)} C := by
  have h₁ : CTTReducibleBy (fun r _ => ∀ a, r a ≤ 2)
      {n | (n ∈ C ∧ n + 1 ∈ C) ∧ (n + 2 ∈ C ∧ n + 3 ∈ C)} {m | m ∈ C ∧ m + 1 ∈ C} := by
    refine ⟨fun _ => 2, fun p => p.1 + 2 * p.2, fun _ => le_rfl, fun n => ?_⟩
    constructor
    · rintro ⟨h₀, h₁⟩ i hi
      obtain _ | _ | i := i
      · simpa using h₀
      · simpa [Nat.add_assoc] using h₁
      · simp at hi; omega
    · intro h
      exact ⟨by simpa using h 0 (by simp), by simpa [Nat.add_assoc] using h 1 (by simp)⟩
  have h₂ : CTTReducibleBy (fun r _ => ∀ b, r b ≤ 2) {m | m ∈ C ∧ m + 1 ∈ C} C := by
    refine ⟨fun _ => 2, fun p => p.1 + p.2, fun _ => le_rfl, fun m => ?_⟩
    constructor
    · rintro ⟨h₀, h₁⟩ j hj
      obtain _ | _ | j := j
      · simpa using h₀
      · simpa using h₁
      · simp at hj; omega
    · intro h
      exact ⟨by simpa using h 0 (by simp), by simpa using h 1 (by simp)⟩
  exact CTTReducibleBy.trans_bounded (fun _ _ h => h) (fun _ _ h => h)
    (fun _ _ _ _ _ _ hmul => hmul) h₁ h₂

/-! ### Positive truth-table embeddings and composition -/

/-- Composing a disjunctive reduction with a conjunctive reduction yields a positive truth-table
reduction via `DTTReducibleBy.pttReducibleBy`, `CTTReducibleBy.pttReducibleBy`, and
`PTTReducibleBy.trans_bounded`. -/
example (C : Set ℕ) :
    PTTReducibleBy (fun r _ _ => ∀ a, r a ≤ 2 * 2)
      {n | (n ∈ C ∧ n + 1 ∈ C) ∨ (n + 2 ∈ C ∧ n + 3 ∈ C)} C := by
  have hdtt : DTTReducibleBy (fun r _ => ∀ a, r a ≤ 2)
      {n | (n ∈ C ∧ n + 1 ∈ C) ∨ (n + 2 ∈ C ∧ n + 3 ∈ C)} {m | m ∈ C ∧ m + 1 ∈ C} := by
    refine ⟨fun _ => 2, fun p => p.1 + 2 * p.2, fun _ => le_rfl, fun n => ?_⟩
    constructor
    · rintro (h₀ | h₁)
      · exact ⟨0, by simp, by simpa using h₀⟩
      · exact ⟨1, by simp, by simpa [Nat.add_assoc] using h₁⟩
    · rintro ⟨i, hi, h⟩
      obtain _ | _ | i := i
      · exact .inl (by simpa using h)
      · exact .inr (by simpa [Nat.add_assoc] using h)
      · simp at hi; omega
  have hctt : CTTReducibleBy (fun r _ => ∀ b, r b ≤ 2) {m | m ∈ C ∧ m + 1 ∈ C} C := by
    refine ⟨fun _ => 2, fun p => p.1 + p.2, fun _ => le_rfl, fun m => ?_⟩
    constructor
    · rintro ⟨h₀, h₁⟩ j hj
      obtain _ | _ | j := j
      · simpa using h₀
      · simpa using h₁
      · simp at hj; omega
    · intro h
      exact ⟨by simpa using h 0 (by simp), by simpa using h 1 (by simp)⟩
  exact PTTReducibleBy.trans_bounded (k₁ := 2) (k₂ := 2)
    (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ _ hmul => hmul)
    (hdtt.pttReducibleBy fun _ _ h => h)
    (hctt.pttReducibleBy fun _ _ h => h)

/-! ### Self-query-avoiding autoreductions and singleton separation -/

/-- Even numbers are fixed-point-free many-one autoreducible by `n ↦ n + 2`, hence `dtt`-, `ctt`-,
and `ptt`-autoreducible, and so is their complement. -/
example :
    let E : Set ℕ := {n | n % 2 = 0}
    ManyOneAutoreducibleBy (fun _ => True) E ∧
      DTTAutoreducibleBy (fun _ _ => True) E ∧
      CTTAutoreducibleBy (fun _ _ => True) Eᶜ ∧
      PTTAutoreducibleBy (fun _ _ _ => True) E := by
  intro E
  have hm : ManyOneAutoreducibleBy (fun _ => True) E :=
    ⟨fun n => n + 2, ⟨trivial, fun n => by dsimp; omega⟩, fun n => by simp [E]⟩
  have hdtt : DTTAutoreducibleBy (fun _ _ => True) E := hm.dttAutoreducibleBy fun _ _ => trivial
  exact ⟨hm, hdtt, dttAutoreducibleBy_iff_cttAutoreducibleBy_compl.mp hdtt,
    hm.pttAutoreducibleBy fun _ _ => trivial⟩

/-- `{true}` is not fixed-point-free many-one autoreducible, yet Boolean negation reduces `{true}ᶜ`
to `{true}` and therefore gives a `1`-query truth-table autoreduction of `{true}` and `{true}ᶜ`. -/
example :
    ¬ ManyOneAutoreducibleBy (fun _ => True) ({true} : Set Bool) ∧
      TruthTableAutoreducibleBy (fun r _ _ => ∀ b, r b ≤ 1) ({true} : Set Bool) ∧
      TruthTableAutoreducibleBy (fun r _ _ => ∀ b, r b ≤ 1) ({true}ᶜ : Set Bool) := by
  have hcompl : ManyOneReducibleBy (fun _ => True) ({true}ᶜ : Set Bool) ({true} : Set Bool) :=
    ⟨Bool.not, trivial, fun b => by cases b <;> simp⟩
  have hauto : TruthTableAutoreducibleBy (fun r _ _ => ∀ b, r b ≤ 1) ({true} : Set Bool) :=
    hcompl.truthTableAutoreducibleBy_of_compl fun _ _ _ => le_rfl
  exact ⟨not_manyOneAutoreducibleBy_singleton true, hauto, hauto.compl fun _ _ _ h => h⟩

end CslibFrontierTests.TruthTableKernel
