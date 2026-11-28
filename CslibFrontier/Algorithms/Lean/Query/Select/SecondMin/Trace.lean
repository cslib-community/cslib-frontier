/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Induction

/-!
# Counting comparisons in the second-minimum adversary

A chronological trace records each comparison as a pair of its smaller and larger entries.
Each undefeated input represents weight `2 ^ k`, where `k` is its number of victories over
previously undefeated inputs. When two undefeated inputs meet, the one with greater or equal
weight wins. Its doubled weight covers the two old weights, so the total never decreases.

If only the minimum remains undefeated, it therefore won at least `⌈log₂ n⌉` such comparisons.
Every input other than the minimum and the reported second minimum also needs a loss to someone
other than the minimum. Those comparisons are disjoint from the minimum's wins.
-/

public section

namespace Cslib.Query.SecondMin

variable {α : Type*}

/-- An entry has lost when a distinct winner was observed against it. -/
@[expose] def Lost (E : List (α × α)) (x : α) : Prop := ∃ w, w ≠ x ∧ (w, x) ∈ E

private theorem lost_snoc {E : List (α × α)} {w l x : α} :
    Lost (E ++ [(w, l)]) x ↔ Lost E x ∨ (w ≠ l ∧ x = l) := by
  simp only [Lost, List.mem_append, List.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨v, hv, h | ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨v, hv, h⟩
    · exact Or.inr ⟨hv, rfl⟩
  · rintro (⟨v, hv, h⟩ | ⟨h, rfl⟩)
    · exact ⟨v, hv, Or.inl h⟩
    · exact ⟨w, h, Or.inr ⟨rfl, rfl⟩⟩

open Classical in
/-- Number of strict comparisons won by `x` in which an input received its first loss. -/
noncomputable def firstWins (S : Finset α) (E : List (α × α)) (x : α) : ℕ :=
  E.reverseRecOn (motive := fun _ => ℕ) 0 fun T p k =>
    k + if p.1 ≠ p.2 ∧ p.2 ∈ S ∧ ¬ Lost T p.2 then (if x = p.1 then 1 else 0) else 0

open Classical in
private theorem firstWins_snoc (S : Finset α) (E : List (α × α)) (w l x : α) :
    firstWins S (E ++ [(w, l)]) x = firstWins S E x +
      if w ≠ l ∧ l ∈ S ∧ ¬ Lost E l then (if x = w then 1 else 0) else 0 := by
  simp [firstWins]

/-- Traces in which an undefeated input can lose only to another undefeated input that has
won at least as many first losses. Self comparisons are allowed. -/
inductive Trace (S : Finset α) : List (α × α) → Prop
  | nil : Trace S []
  | snoc {E : List (α × α)} (hE : Trace S E) (w l : α)
      (h : w ≠ l → l ∈ S → ¬ Lost E l →
        w ∈ S ∧ ¬ Lost E w ∧ firstWins S E l ≤ firstWins S E w) :
      Trace S (E ++ [(w, l)])

open Classical in
private noncomputable def weight (S : Finset α) (E : List (α × α)) (x : α) : ℕ :=
  if Lost E x then 0 else 2 ^ firstWins S E x

private theorem Trace.card_le_sum_weight {S : Finset α} {E : List (α × α)} (h : Trace S E) :
    S.card ≤ ∑ x ∈ S, weight S E x := by
  classical
  induction h with
  | nil => simp [weight, Lost, firstWins]
  | @snoc T _ w l step ih =>
    apply ih.trans
    by_cases fresh : w ≠ l ∧ l ∈ S ∧ ¬ Lost T l
    · obtain ⟨hwS, hwu, hdegree⟩ := step fresh.1 fresh.2.1 fresh.2.2
      have hle : weight S T l ≤ weight S T w := by
        simpa [weight, fresh.2.2, hwu] using
          Nat.pow_le_pow_right (by decide : 0 < 2) hdegree
      -- Adding the lost weight back at l leaves exactly an extra copy of the winner's weight.
      have point (x : α) : weight S (T ++ [(w, l)]) x + (if x = l then weight S T l else 0) =
          weight S T x + (if x = w then weight S T w else 0) := by
        obtain rfl | hxw := eq_or_ne x w
        · simp [weight, firstWins_snoc, lost_snoc, fresh, hwu, pow_succ, Nat.mul_two]
        obtain rfl | hxl := eq_or_ne x l
        · simp [weight, lost_snoc, fresh.1, hxw]
        · simp [weight, firstWins_snoc, lost_snoc, fresh, hxw, hxl]
      have hsum := Finset.sum_congr (s₁ := S) rfl fun x _ => point x
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', hwS, fresh.2.1, ↓reduceIte] at hsum
      omega
    · refine Finset.sum_le_sum fun x hx => ?_
      have unchanged : Lost (T ++ [(w, l)]) x ↔ Lost T x := by
        rw [lost_snoc]
        grind
      simp [weight, firstWins_snoc, fresh, unchanged]

/-- At least one input remains undefeated on a trace with nonempty input. -/
theorem Trace.exists_unbeaten {S : Finset α} {E : List (α × α)} (h : Trace S E)
    (hs : S.Nonempty) : ∃ m ∈ S, ¬ Lost E m := by
  classical
  by_contra! hall
  have hzero : ∑ x ∈ S, weight S E x = 0 :=
    Finset.sum_eq_zero fun x hx => by simp [weight, hall x hx]
  have := h.card_le_sum_weight
  have := Finset.card_pos.mpr hs
  omega

private theorem firstWins_le_wins (S : Finset α) (E : List (α × α)) (m : α) [DecidableEq α] :
    firstWins S E m ≤ (E.filter fun p => decide (p.1 = m)).length := by
  classical
  induction E using List.reverseRecOn with
  | nil => simp [firstWins]
  | append_singleton E p ih =>
    obtain ⟨w, l⟩ := p
    rw [firstWins_snoc, List.filter_append, List.length_append]
    by_cases h : w = m
    · subst w
      simp only [decide_true, List.filter_cons_of_pos, List.filter_nil, List.length_singleton]
      split_ifs <;> omega
    · simp [h, Ne.symm h, ih]

/-- If only `m` is undefeated and every input except `m` and `second` lost to another winner,
the trace contains at least `n + ⌈log₂ n⌉ − 2` comparisons. -/
theorem Trace.lowerBound {S : Finset α} {E : List (α × α)} {m second : α} (h : Trace S E)
    (hm : m ∈ S) (hroot : ¬ Lost E m) (hlost : ∀ x ∈ S, x ≠ m → Lost E x)
    (hother : ∀ x ∈ S, x ≠ m → x ≠ second → ∃ w, w ≠ m ∧ w ≠ x ∧ (w, x) ∈ E) :
    S.card + Nat.clog 2 S.card - 2 ≤ E.length := by
  classical
  have hmass := h.card_le_sum_weight
  rw [Finset.sum_eq_single_of_mem m hm fun x hx hxm => by simp [weight, hlost x hx hxm]] at hmass
  have hlog := Nat.clog_le_of_le_pow (by simpa [weight, hroot] using hmass :
    S.card ≤ 2 ^ firstWins S E m)
  let won (p : α × α) := decide (p.1 = m)
  have hsub : (S.erase m).erase second ⊆ ((E.filter (!won ·)).map Prod.snd).toFinset := by
    intro x hx
    obtain ⟨hxs, hxm, hxS⟩ := (by simpa only [Finset.mem_erase] using hx :
      x ≠ second ∧ x ≠ m ∧ x ∈ S)
    obtain ⟨w, hwm, _, hwx⟩ := hother x hxS hxm hxs
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨(w, x), List.mem_filter.mpr ⟨hwx, by simp [won, hwm]⟩, rfl⟩)
  have hothers := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  rw [List.length_map] at hothers
  have h₁ := Finset.pred_card_le_card_erase (s := S) (a := m)
  have h₂ := Finset.pred_card_le_card_erase (s := S.erase m) (a := second)
  have hmWins : firstWins S E m ≤ (E.filter won).length := firstWins_le_wins S E m
  have hsplit := E.length_eq_length_filter_add won
  omega

end Cslib.Query.SecondMin
