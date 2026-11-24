/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.DSteps
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Sums over executions as sums over choices

A family of steps in which step `i` chooses `a` from a list and writes the names that belong to
`i`. The states after all steps are then indexed by the functions that make the choices
(`Interpreter.funs`), and sums over them are sums over all functions (`Interpreter.sum_funs`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `NS1.Picks`.

## Main definitions

* `Interpreter.funs`.

## Main results

* `Interpreter.execAll_choices`: the states after a family of choices.
* `Interpreter.execAll_det`, `Interpreter.execAll_checks_pos`, `Interpreter.execAll_checks_neg`:
  deterministic steps and checks.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A]

variable {ι : Type} [DecidableEq ι]

/-- All functions on a list of indices, with values from lists. -/
@[expose] def funs {α : Type} (opts : ι → List α) (f0 : ι → α) : List ι → List (ι → α)
  | [] => [f0]
  | i :: s => (opts i).flatMap fun a => (funs opts (Function.update f0 i a) s)

theorem funs_eq_of_not_mem {α : Type} (opts : ι → List α)
    {s : List ι} {f0 f : ι → α} (h : f ∈ funs opts f0 s) {i : ι}
    (hi : i ∉ s) : f i = f0 i := by
  induction s generalizing f0 with
  | nil =>
    simp only [funs, List.mem_singleton] at h
    rw [h]
  | cons j s ih =>
    simp only [funs, List.mem_flatMap] at h
    obtain ⟨a, ha, h⟩ := h
    rw [List.mem_cons, not_or] at hi
    rw [ih h hi.2, Function.update_of_ne hi.1]

/-- Sums over all functions. -/
theorem sum_funs {α : Type} [Fintype α] [DecidableEq α] [Fintype ι] (opts : ι → List α)
    (hopts : ∀ i, (opts i).Nodup)
    (s : List ι) (hs : s.Nodup) (f0 : ι → α) (Φ : (ι → α) → A) :
    ((funs opts f0 s).map Φ).sum = ∑ f : ι → α,
        if (∀ i ∈ s, f i ∈ opts i) ∧ (∀ i, i ∉ s → f i = f0 i) then Φ f else 0 := by
  induction s generalizing f0 with
  | nil =>
    have : ∀ f : ι → α,
        ((∀ i ∈ ([] : List ι), f i ∈ opts i) ∧ ∀ i, i ∉ ([] : List ι) → f i = f0 i) ↔ f = f0 := by
      intro f
      simp [funext_iff]
    simp only
        [this, funs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
            Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  | cons i s ih =>
    rw [List.nodup_cons] at hs
    rw [funs, List.sum_map_flatMap]
    simp only [ih hs.2]
    have h1 : ∀ a,
        (∑ f : ι → α,
            if (∀ j ∈ s, f j ∈ opts j) ∧
                (∀ j, j ∉ s → f j = Function.update f0 i a j) then Φ f else 0) =
        ∑ f : ι → α,
            if f i =
                a then (if (∀ j ∈ s, f j ∈ opts j) ∧
                    (∀ j, j ∉ i :: s → f j = f0 j) then Φ f else 0) else 0 := by
      intro a
      refine Finset.sum_congr rfl fun f _ => ?_
      by_cases ha : f i = a
      · rw [ite_eq_left ha]
        refine if_congr (and_congr_right fun _ => ?_) rfl rfl
        constructor
        · intro h j hj
          rw [List.mem_cons, not_or] at hj
          rw [h j hj.2, Function.update_of_ne hj.1]
        · intro h j hj
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self, ha]
          · rw [Function.update_of_ne hji]
            exact h j (by rw [List.mem_cons, not_or]; exact ⟨hji, hj⟩)
      · rw [ite_eq_right ha, ite_eq_right]
        rintro ⟨-, h⟩
        apply ha
        rw [h i hs.1, Function.update_self]
    simp only [h1]
    have h2 : ((opts i).map fun a => ∑ f : ι → α, if f i = a then
        (if (∀ j ∈ s, f j ∈ opts j) ∧ (∀ j, j ∉ i :: s → f j = f0 j) then Φ f else 0) else 0).sum =
        ∑ a ∈ (opts i).toFinset, ∑ f : ι → α, if f i = a then
        (if (∀ j ∈ s, f j ∈ opts j) ∧ (∀ j, j ∉ i :: s → f j = f0 j) then Φ f else 0) else 0 := by
      rw [List.sum_toFinset _ (hopts i)]
    rw [h2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_ite_eq]
    simp only [List.mem_toFinset]
    by_cases hf : f i ∈ opts i
    · rw [ite_eq_left hf]
      refine if_congr (and_congr_left fun _ => ?_) rfl rfl
      simp [hf]
    · rw [ite_eq_right hf, ite_eq_right]
      rintro ⟨h, -⟩
      exact hf (h i List.mem_cons_self)

/-- **Choices.** Step `i` gives, for every `a` in `opts i`, the state `ov i a st`. -/
theorem execAll_choices {α St : Type} {m : ℕ} {L : St → List Bool → Tree} {opts : ι → List α}
    {step : ι → DStep}
    {ov : ι → α → St → St} (good : St → Prop)
    (hst : ∀ i st, good st → (step i).exec m (L st) = (opts i).map fun a => L (ov i a st))
    (hgood : ∀ i st, ∀ a ∈ opts i, good st → good (ov i a st)) {s : List ι} (hs : s.Nodup) {st : St}
    (hσ : good st) (f0 : ι → α) (Φ : (List Bool → Tree) → A) :
    ((execAll m (s.map step) (L st)).map Φ).sum =
      ((funs opts f0 s).map fun f => Φ (L (s.foldl (fun st i => ov i (f i) st) st))).sum := by
  induction s generalizing st f0 with
  | nil => simp [execAll, funs]
  | cons i s ih =>
    rw [List.nodup_cons] at hs
    rw [List.map_cons, sum_execAll_cons, hst i st hσ, List.map_map, funs, List.sum_map_flatMap]
    congr 1
    refine List.map_congr_left fun a ha => ?_
    simp only [Function.comp_apply]
    rw [ih hs.2 (hgood i st a ha hσ) (Function.update f0 i a)]
    congr 1
    refine List.map_congr_left fun f hf => ?_
    have hfi : f i = a := by
      rw [funs_eq_of_not_mem opts hf hs.1, Function.update_self]
    rw [List.foldl_cons, hfi]

omit [DecidableEq ι] in
/-- Deterministic steps. -/
theorem execAll_det {St : Type} {m : ℕ} {L : St → List Bool → Tree} {step : ι → DStep}
    {ov : ι → St → St}
    (good : List ι → St → Prop)
        (hst : ∀ i s st,
            good (i :: s) st → (step i).exec m (L st) = [L (ov i st)] ∧ good s (ov i st))
    {s : List ι} {st : St} (hσ : good s st) :
    execAll m (s.map step) (L st) = [L (s.foldl (fun st i => ov i st) st)] := by
  induction s generalizing st with
  | nil => rfl
  | cons i s ih =>
    obtain ⟨h1, h2⟩ := hst i s st hσ
    rw [List.map_cons, execAll, h1, List.flatMap_cons, List.flatMap_nil, List.append_nil, ih h2,
        List.foldl_cons]

/-- Checks that are passed. -/
theorem execAll_checks_pos {m : ℕ} {ps : List (List Bool)} {σ : List Bool → Tree}
    (h : ∀ p ∈ ps, σ p ≠ .nil) :
    execAll m (ps.map DStep.check) σ = [σ] := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, execAll, DStep.exec, ite_eq_right (h p List.mem_cons_self),
        List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- Checks that are not passed. -/
theorem execAll_checks_neg {m : ℕ} {ps : List (List Bool)} {σ : List Bool → Tree}
    (h : ∃ p ∈ ps, σ p = .nil) :
    execAll m (ps.map DStep.check) σ = [] := by
  induction ps with
  | nil => simp at h
  | cons p ps ih =>
    rw [List.map_cons, execAll, DStep.exec]
    by_cases hp : σ p = .nil
    · rw [ite_eq_left hp]
      rfl
    · rw [ite_eq_right hp, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine ih ?_
      obtain ⟨q, hq, hq'⟩ := h
      rcases List.mem_cons.1 hq with rfl | hq
      · exact absurd hq' hp
      · exact ⟨q, hq, hq'⟩

end Cslib.Circuits.Arithmetic.Separation.Interpreter
