/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Defs
import Mathlib.Data.Fin.Basic

/-!
# Consecutive pairs in lists

This module provides lemmas about `List.consecutivePairs` and its interaction with `flatMap`.
-/

public section

namespace List

@[simp] theorem consecutivePairs_nil {α : Type*} :
    List.consecutivePairs ([] : List α) = [] := rfl

@[simp] theorem consecutivePairs_cons_cons {α : Type*} (a b : α) (l : List α) :
    List.consecutivePairs (a :: b :: l) = (a, b) :: List.consecutivePairs (b :: l) := rfl

@[simp] theorem consecutivePairs_singleton {α : Type*} (a : α) :
    List.consecutivePairs [a] = [] := rfl

theorem consecutivePairs_append {α : Type*} {l₁ l₂ : List α}
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    List.consecutivePairs (l₁ ++ l₂) =
      List.consecutivePairs l₁ ++ (l₁.getLast h₁, l₂.head h₂) :: List.consecutivePairs l₂ := by
  induction l₁ with
  | nil => exact absurd rfl h₁
  | cons a xs ih =>
    rcases xs with _ | ⟨b, ys⟩
    · rcases l₂ with _ | ⟨c, zs⟩
      · exact absurd rfl h₂
      · rfl
    · simp only [List.cons_append, consecutivePairs_cons_cons,
        List.getLast_cons (List.cons_ne_nil b ys)]
      exact congrArg ((a, b) :: ·) (ih (List.cons_ne_nil b ys))

theorem flatMap_ne_nil {α β : Type*} {L : List β} (hL : L ≠ [])
    {f : β → List α} (hf : ∀ b ∈ L, f b ≠ []) :
    L.flatMap f ≠ [] := by
  rcases L with _ | ⟨b, bs⟩
  · exact absurd rfl hL
  · simp [hf b List.mem_cons_self]

theorem head_flatMap {α β : Type*} {L : List β} (hL : L ≠ [])
    {f : β → List α} (hf : ∀ b ∈ L, f b ≠ []) :
    (L.flatMap f).head (flatMap_ne_nil hL hf) = (f (L.head hL)).head (hf _ (List.head_mem hL)) := by
  rcases L with _ | ⟨b, bs⟩
  · exact absurd rfl hL
  · simp [List.head_append_of_ne_nil (hf b List.mem_cons_self)]

theorem getLast_flatMap {α β : Type*} {L : List β} (hL : L ≠ [])
    {f : β → List α} (hf : ∀ b ∈ L, f b ≠ []) :
    (L.flatMap f).getLast (flatMap_ne_nil hL hf) =
      (f (L.getLast hL)).getLast (hf _ (List.getLast_mem hL)) := by
  induction L with
  | nil => exact absurd rfl hL
  | cons b bs ih =>
    rcases bs with _ | ⟨b', bs'⟩
    · simp
    · have htail : b' :: bs' ≠ [] := List.cons_ne_nil b' bs'
      have hft : ∀ x ∈ b' :: bs', f x ≠ [] := fun x hx => hf x (List.mem_cons_of_mem b hx)
      have h1 : ((b :: b' :: bs').flatMap f).getLast (flatMap_ne_nil hL hf) =
          ((b' :: bs').flatMap f).getLast (flatMap_ne_nil htail hft) :=
        List.getLast_append_of_ne_nil _ (flatMap_ne_nil htail hft)
      rw [h1, ih htail hft]
      simp only [List.getLast_cons htail]

theorem mem_consecutivePairs_flatMap {α β : Type*} {L : List β} (hL : L ≠ [])
    {f : β → List α} (hf : ∀ b, f b ≠ []) {x y : α} :
    (x, y) ∈ List.consecutivePairs (L.flatMap f) ↔
      (∃ b ∈ L, (x, y) ∈ List.consecutivePairs (f b)) ∨
      (∃ p ∈ List.consecutivePairs L,
        x = (f p.1).getLast (hf p.1) ∧ y = (f p.2).head (hf p.2)) := by
  induction L with
  | nil => exact absurd rfl hL
  | cons b bs ih =>
    rcases bs with _ | ⟨b', bs'⟩
    · simp
    · have htail : b' :: bs' ≠ [] := List.cons_ne_nil b' bs'
      rw [List.flatMap_cons,
        List.consecutivePairs_append (hf b) (flatMap_ne_nil htail fun z _ => hf z),
        List.mem_append, List.mem_cons, Prod.mk.injEq, ih htail,
        head_flatMap htail fun z _ => hf z, List.head_cons]
      simp only [consecutivePairs_cons_cons, List.mem_cons]
      constructor
      · rintro (h | ⟨rfl, rfl⟩ | ⟨c, hc, hxy⟩ | ⟨p, hp, h1, h2⟩)
        · exact Or.inl ⟨b, Or.inl rfl, h⟩
        · exact Or.inr ⟨(b, b'), Or.inl rfl, rfl, rfl⟩
        · exact Or.inl ⟨c, Or.inr hc, hxy⟩
        · exact Or.inr ⟨p, Or.inr hp, h1, h2⟩
      · rintro (⟨c, rfl | hc, hxy⟩ | ⟨⟨p₁, p₂⟩, hbb | hp, h1, h2⟩)
        · exact Or.inl hxy
        · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hxy⟩))
        · cases hbb; exact Or.inr (Or.inl ⟨h1, h2⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨(p₁, p₂), hp, h1, h2⟩))

theorem getElem_mem_consecutivePairs {α : Type*} (l : List α) (i : ℕ)
    (hi : i + 1 < l.length) : (l[i], l[i + 1]) ∈ List.consecutivePairs l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    rcases xs, i with ⟨_ | ⟨b, ys⟩, _ | j⟩
    · simp at hi
    · simp at hi
    · simp
    · exact List.mem_cons_of_mem _ (ih j (by simpa using hi))

theorem mem_consecutivePairs_iff_exists_getElem {α : Type*} {l : List α} {x y : α} :
    (x, y) ∈ List.consecutivePairs l ↔
      ∃ i, ∃ hi : i + 1 < l.length, l[i] = x ∧ l[i + 1] = y := by
  induction l with
  | nil => simp
  | cons a xs ih =>
    rcases xs with _ | ⟨b, ys⟩
    · simp
    · simp only [consecutivePairs_cons_cons, List.mem_cons, Prod.mk.injEq, ih]
      refine ⟨?_, ?_⟩
      · rintro (⟨rfl, rfl⟩ | ⟨j, hj, h1, h2⟩)
        · exact ⟨0, by simp, rfl, rfl⟩
        · exact ⟨j + 1, Nat.succ_lt_succ hj, h1, h2⟩
      · rintro ⟨_ | j, hi, h1, h2⟩
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨j, Nat.lt_of_succ_lt_succ hi, h1, h2⟩

theorem step_mem_cyclicPairs {α : Type*} (l : List α) [NeZero l.length] (hl : l ≠ [])
    (i : Fin l.length) (h2 : 2 ≤ l.length) :
    (l[i.1], l[(i + 1 : Fin l.length).1]) ∈
      (l.getLast hl, l.head hl) :: List.consecutivePairs l := by
  have h1 : (1 : Fin l.length).1 = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  by_cases hlast : i.1 + 1 = l.length
  · have hi1 : (i + 1 : Fin l.length).1 = 0 := by
      rw [Fin.val_add, h1, hlast, Nat.mod_self]
    have hlast_eq : l[i.1] = l.getLast hl := by
      rw [List.getLast_eq_getElem hl]
      congr 1
      omega
    rw [hlast_eq]
    simp only [hi1, ← List.head_eq_getElem hl, List.mem_cons, true_or]
  · have hlt : i.1 + 1 < l.length := by omega
    have hi1 : (i + 1 : Fin l.length).1 = i.1 + 1 := by
      rw [Fin.val_add, h1]
      exact Nat.mod_eq_of_lt hlt
    simp only [hi1]
    exact List.mem_cons_of_mem _ (getElem_mem_consecutivePairs l i.1 hlt)

theorem cyclicPairs_mem_iff {α : Type*} (l : List α) [NeZero l.length] (hl : l ≠ [])
    (h2 : 2 ≤ l.length) {x y : α} :
    (∃ i : Fin l.length, l[i.1] = x ∧ l[(i + 1 : Fin l.length).1] = y) ↔
      (x, y) ∈ (l.getLast hl, l.head hl) :: List.consecutivePairs l := by
  have h1 : (1 : Fin l.length).1 = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨fun ⟨i, hxi, hyi⟩ => hxi ▸ hyi ▸ step_mem_cyclicPairs l hl i h2, ?_⟩
  rw [List.mem_cons, Prod.mk.injEq, mem_consecutivePairs_iff_exists_getElem]
  rintro (⟨rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩)
  · refine ⟨⟨l.length - 1, by omega⟩, (List.getLast_eq_getElem hl).symm, ?_⟩
    have hi1 : (⟨l.length - 1, by omega⟩ + 1 : Fin l.length).1 = 0 := by
      rw [Fin.val_add, h1]
      dsimp only
      rw [show l.length - 1 + 1 = l.length by omega, Nat.mod_self]
    simp only [hi1, ← List.head_eq_getElem hl]
  · refine ⟨⟨j, by omega⟩, rfl, ?_⟩
    have hi1 : (⟨j, by omega⟩ + 1 : Fin l.length).1 = j + 1 := by
      rw [Fin.val_add, h1]
      exact Nat.mod_eq_of_lt hj
    simp only [hi1]

end List
