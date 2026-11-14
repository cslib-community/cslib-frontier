/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/ENat/Lattice.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.ENat.Lattice
import Mathlib.Order.SuccPred.CompleteLinearOrder

/-!
# Least-cost bounds in `ℕ∞` and `ℕ`

A complexity measure defined as `⨅ w : {w // P w}, cost w.1` over a subtype of witnesses is at
most a finite budget `k` exactly when some witness costs at most `k`. This is the `ℕ∞` case of
Mathlib's `iInf_le_iff_of_not_isPredPrelimit`: a finite `k` is covered by `k + 1`, so it is not a
predecessor prelimit. This module packages the upper/lower bound characterizations, attainment when
a witness exists, and monotonicity for `ℕ∞`-valued subtype infima, two-parameter indexed subtype
infima (used by private-coin communication models), and `ℕ`-valued `sInf` complexity measures (used
by decision-tree models).

## Main results

* `ENat.iInf_le_natCast_iff`, `ENat.iInf_natCast_le_natCast_iff`: `⨅ i, f i ≤ k ↔ ∃ i, f i ≤ k`
  for a finite `k`.
* `ENat.iInf_subtype_le`, `ENat.le_iInf_subtype_iff`, `ENat.iInf_subtype_le_natCast_iff`,
  `ENat.iInf_subtype_natCast_le_natCast_iff`, `ENat.iInf_subtype_natCast_ne_top_iff`,
  `ENat.exists_eq_iInf_subtype_natCast`, `ENat.iInf_subtype_mono`: shared least-cost API for
  `⨅ w : {w // P w}, cost w.1`.
* `ENat.iInf₂_subtype_natCast_le`, `ENat.le_iInf₂_subtype_natCast_iff`,
  `ENat.iInf₂_subtype_natCast_le_natCast_iff`, `ENat.iInf₂_subtype_natCast_mono`: the same for a
  two-parameter family of witness types.
* `Nat.sInf_le_of_le`, `Nat.exists_eq_sInf_of_exists`, `Nat.sInf_le_iff_of_exists`,
  `Nat.le_sInf_iff_of_exists`, `Nat.sInf_mono_of_exists`: shared least-cost API for
  `sInf {d : ℕ | ∃ w, P w ∧ cost w ≤ d}` when a witness exists.
-/

public section

namespace ENat

variable {ι α : Sort*} {P Q : α → Prop} {c : α → ℕ∞} {d : α → ℕ}

/-- An infimum in `ℕ∞` is at most a finite `k` exactly when some term is: the `ℕ∞` case of
`iInf_le_iff_of_not_isPredPrelimit`. -/
theorem iInf_le_natCast_iff {f : ι → ℕ∞} {k : ℕ} : ⨅ i, f i ≤ k ↔ ∃ i, f i ≤ k :=
  iInf_le_iff_of_not_isPredPrelimit fun h =>
    h _ (Order.covBy_succ_of_not_isMax (not_isMax_iff_ne_top.2 (natCast_ne_top k)))

/-- An infimum of natural numbers is at most `k` exactly when some term is. -/
theorem iInf_natCast_le_natCast_iff {f : ι → ℕ} {k : ℕ} :
    ⨅ i, (f i : ℕ∞) ≤ k ↔ ∃ i, f i ≤ k := by
  simp only [iInf_le_natCast_iff, natCast_le_natCast]

/-- Any witness satisfying `P` bounds the least cost over `{w // P w}` from above. -/
theorem iInf_subtype_le {w : α} (hw : P w) : (⨅ w : {w : α // P w}, c w.1) ≤ c w :=
  iInf_le (fun w : {w : α // P w} => c w.1) ⟨w, hw⟩

/-- Lower bounds on a subtype infimum are lower bounds on every witness satisfying `P`. -/
theorem le_iInf_subtype_iff {k : ℕ∞} :
    k ≤ (⨅ w : {w : α // P w}, c w.1) ↔ ∀ w, P w → k ≤ c w := by
  simp only [le_iInf_iff, Subtype.forall]

/-- Upper bounds by a finite budget `k` on a subtype infimum in `ℕ∞` are witnessed by some `w`
satisfying `P`. -/
theorem iInf_subtype_le_natCast_iff {k : ℕ} :
    (⨅ w : {w : α // P w}, c w.1) ≤ k ↔ ∃ w, P w ∧ c w ≤ k := by
  simp only [iInf_le_natCast_iff, Subtype.exists, exists_prop]

/-- Relaxing the witness predicate cannot increase the least cost. -/
theorem iInf_subtype_mono (hPQ : ∀ w, P w → Q w) :
    (⨅ w : {w : α // Q w}, c w.1) ≤ ⨅ w : {w : α // P w}, c w.1 :=
  le_iInf fun w => iInf_le_of_le ⟨w.1, hPQ w.1 w.2⟩ le_rfl

/-- Mapping witnesses of `P` to witnesses of `R` without increasing cost bounds the least cost of
`R` by that of `P`. -/
theorem iInf_subtype_le_iInf_subtype {β : Sort*} {c' : β → ℕ∞} {R : β → Prop} (f : α → β)
    (hPR : ∀ w, P w → R (f w)) (hc : ∀ w, P w → c' (f w) ≤ c w) :
    (⨅ u : {u : β // R u}, c' u.1) ≤ ⨅ w : {w : α // P w}, c w.1 :=
  le_iInf fun w => (iInf_subtype_le (hPR w.1 w.2)).trans (hc w.1 w.2)

/-- Any witness satisfying `P` bounds the least natural-number cost over `{w // P w}`. -/
theorem iInf_subtype_natCast_le {w : α} (hw : P w) :
    (⨅ w : {w : α // P w}, (d w.1 : ℕ∞)) ≤ d w :=
  iInf_subtype_le (c := fun w => (d w : ℕ∞)) hw

/-- The least natural-number cost over `{w // P w}` is finite exactly when a witness exists. -/
theorem iInf_subtype_natCast_ne_top_iff :
    (⨅ w : {w : α // P w}, (d w.1 : ℕ∞)) ≠ ⊤ ↔ ∃ w, P w := by
  rw [ENat.iInf_natCast_ne_top, nonempty_subtype]

/-- When a witness satisfying `P` exists, some witness attains the least natural-number cost. -/
theorem exists_eq_iInf_subtype_natCast (h : ∃ w, P w) :
    ∃ w, P w ∧ (d w : ℕ∞) = ⨅ w : {w : α // P w}, (d w.1 : ℕ∞) := by
  have : Nonempty {w : α // P w} := nonempty_subtype.mpr h
  obtain ⟨⟨w, hw⟩, hmin⟩ := ENat.exists_eq_iInf (fun w : {w : α // P w} => (d w.1 : ℕ∞))
  exact ⟨w, hw, hmin⟩

/-- The least natural-number cost over `{w // P w}` is at most `k` iff some witness costs at most
`k`. -/
theorem iInf_subtype_natCast_le_natCast_iff {k : ℕ} :
    (⨅ w : {w : α // P w}, (d w.1 : ℕ∞)) ≤ k ↔ ∃ w, P w ∧ d w ≤ k := by
  simp only [iInf_natCast_le_natCast_iff, Subtype.exists, exists_prop]

/-- Lower bounds on the least natural-number cost over `{w // P w}` are lower bounds on every
witness satisfying `P`. -/
theorem le_iInf_subtype_natCast_iff {k : ℕ∞} :
    k ≤ (⨅ w : {w : α // P w}, (d w.1 : ℕ∞)) ↔ ∀ w, P w → k ≤ d w :=
  le_iInf_subtype_iff (c := fun w => (d w : ℕ∞))

/-- Relaxing the witness predicate cannot increase the least natural-number cost. -/
theorem iInf_subtype_natCast_mono (hPQ : ∀ w, P w → Q w) :
    (⨅ w : {w : α // Q w}, (d w.1 : ℕ∞)) ≤ ⨅ w : {w : α // P w}, (d w.1 : ℕ∞) :=
  iInf_subtype_mono (c := fun w => (d w : ℕ∞)) hPQ

/-- `iInf_subtype_natCast_le` transported along an equivalence of witness predicates. -/
theorem iInf_subtype_natCast_le_of_iff (hPQ : ∀ w, P w ↔ Q w) {w : α} (hw : Q w) :
    (⨅ w : {w : α // P w}, (d w.1 : ℕ∞)) ≤ d w :=
  iInf_subtype_natCast_le ((hPQ w).mpr hw)

/-- `iInf_subtype_natCast_le_natCast_iff` transported along an equivalence of witness predicates. -/
theorem iInf_subtype_natCast_le_natCast_iff_of_iff (hPQ : ∀ w, P w ↔ Q w) {k : ℕ} :
    (⨅ w : {w : α // P w}, (d w.1 : ℕ∞)) ≤ k ↔ ∃ w, Q w ∧ d w ≤ k := by
  simp only [iInf_subtype_natCast_le_natCast_iff, hPQ]

/-- `le_iInf_subtype_iff` transported along an equivalence of witness predicates. -/
theorem le_iInf_subtype_iff_of_iff (hPQ : ∀ w, P w ↔ Q w) {k : ℕ∞} :
    k ≤ (⨅ w : {w : α // P w}, c w.1) ↔ ∀ w, Q w → k ≤ c w := by
  simp only [le_iInf_subtype_iff, hPQ]

/-- `le_iInf_subtype_natCast_iff` transported along an equivalence of witness predicates. -/
theorem le_iInf_subtype_natCast_iff_of_iff (hPQ : ∀ w, P w ↔ Q w) {k : ℕ∞} :
    k ≤ (⨅ w : {w : α // P w}, (d w.1 : ℕ∞)) ↔ ∀ w, Q w → k ≤ d w :=
  le_iInf_subtype_iff_of_iff (c := fun w => (d w : ℕ∞)) hPQ

section Indexed2

variable {β : Sort*} {γ : α → β → Sort*} {R S : ∀ a b, γ a b → Prop} {g : ∀ a b, γ a b → ℕ}

/-- Any witness in a two-parameter family bounds the least cost from above. -/
theorem iInf₂_subtype_natCast_le {a : α} {b : β} {w : γ a b} (hw : R a b w) :
    (⨅ (a : α) (b : β) (w : {w : γ a b // R a b w}), (g a b w.1 : ℕ∞)) ≤ g a b w :=
  (iInf_le _ a).trans <| (iInf_le _ b).trans <| iInf_subtype_natCast_le hw

/-- Lower bounds on a two-parameter subtype infimum are lower bounds on every witness. -/
theorem le_iInf₂_subtype_natCast_iff {k : ℕ∞} :
    k ≤ (⨅ (a : α) (b : β) (w : {w : γ a b // R a b w}), (g a b w.1 : ℕ∞)) ↔
      ∀ a b (w : γ a b), R a b w → k ≤ g a b w := by
  simp only [le_iInf_iff, Subtype.forall]

/-- Upper bounds by a finite budget `k` on a two-parameter subtype infimum are witnessed by some
`a`, `b`, and `w`. -/
theorem iInf₂_subtype_natCast_le_natCast_iff {k : ℕ} :
    (⨅ (a : α) (b : β) (w : {w : γ a b // R a b w}), (g a b w.1 : ℕ∞)) ≤ k ↔
      ∃ a b, ∃ w : γ a b, R a b w ∧ g a b w ≤ k := by
  simp only [iInf_le_natCast_iff, natCast_le_natCast, Subtype.exists, exists_prop]

/-- Relaxing the witness predicate in a two-parameter family cannot increase the least cost. -/
theorem iInf₂_subtype_natCast_mono (hRS : ∀ a b w, R a b w → S a b w) :
    (⨅ (a : α) (b : β) (w : {w : γ a b // S a b w}), (g a b w.1 : ℕ∞)) ≤
      ⨅ (a : α) (b : β) (w : {w : γ a b // R a b w}), (g a b w.1 : ℕ∞) :=
  le_iInf₂_subtype_natCast_iff.mpr fun _ _ _ hw => iInf₂_subtype_natCast_le (hRS _ _ _ hw)

end Indexed2

/-- An `ℕ∞` value characterized at every finite budget `c : ℕ` by `x ≤ c ↔ ∀ a, P a → f a ≤ c` is
the supremum `⨆ (a : α) (_ : P a), f a`. -/
theorem eq_iSup₂_of_le_natCast_iff {x : ℕ∞} {f : α → ℕ∞}
    (h : ∀ c : ℕ, x ≤ c ↔ ∀ a, P a → f a ≤ c) :
    x = ⨆ (a : α) (_ : P a), f a := by
  refine le_antisymm ?_ (iSup₂_le fun a ha => ?_)
  · cases hsup : ⨆ (a : α) (_ : P a), f a using ENat.recTopCoe with
    | top => exact le_top
    | coe c =>
      exact (h c).mpr fun a ha =>
        hsup ▸ le_iSup₂ (f := fun (a : α) (_ : P a) => f a) a ha
  · cases hx : x using ENat.recTopCoe with
    | top => exact le_top
    | coe c => exact (h c).mp hx.le a ha

end ENat

namespace Nat

variable {α : Sort*} {P Q : α → Prop} {c : α → ℕ}

/-- Any witness satisfying `P` bounds `sInf {d | ∃ w, P w ∧ c w ≤ d}` from above. -/
theorem sInf_le_of_le {w : α} (hw : P w) :
    sInf {d : ℕ | ∃ w : α, P w ∧ c w ≤ d} ≤ c w :=
  Nat.sInf_le ⟨w, hw, le_rfl⟩

/-- When some witness satisfies `P`, a witness attains `sInf {d | ∃ w, P w ∧ c w ≤ d}`. -/
theorem exists_eq_sInf_of_exists (c : α → ℕ) (hex : ∃ w : α, P w) :
    ∃ w : α, P w ∧ c w = sInf {d : ℕ | ∃ w : α, P w ∧ c w ≤ d} := by
  obtain ⟨w₀, hw₀⟩ := hex
  obtain ⟨w, hw, hd⟩ :=
    Nat.sInf_mem (s := {d : ℕ | ∃ w : α, P w ∧ c w ≤ d}) ⟨c w₀, w₀, hw₀, le_rfl⟩
  exact ⟨w, hw, le_antisymm hd (sInf_le_of_le hw)⟩

/-- When a witness attains the least cost, the least cost is at most `d` iff some witness costs at
most `d`. -/
theorem sInf_le_iff_of_exists
    (hmin : ∃ w : α, P w ∧ c w = sInf {d : ℕ | ∃ w : α, P w ∧ c w ≤ d}) {d : ℕ} :
    sInf {d : ℕ | ∃ w : α, P w ∧ c w ≤ d} ≤ d ↔ ∃ w : α, P w ∧ c w ≤ d :=
  ⟨fun h => hmin.imp fun _ ⟨hw, hd⟩ => ⟨hw, hd.trans_le h⟩,
    fun ⟨_, hw, hd⟩ => (sInf_le_of_le hw).trans hd⟩

/-- When a witness attains the least cost, lower bounds on the least cost are lower bounds on every
witness. -/
theorem le_sInf_iff_of_exists
    (hmin : ∃ w : α, P w ∧ c w = sInf {d : ℕ | ∃ w : α, P w ∧ c w ≤ d}) {d : ℕ} :
    d ≤ sInf {d : ℕ | ∃ w : α, P w ∧ c w ≤ d} ↔ ∀ w : α, P w → d ≤ c w :=
  ⟨fun h _ hw => h.trans (sInf_le_of_le hw), fun h =>
    let ⟨w, hw, hd⟩ := hmin
    (h w hw).trans_eq hd⟩

/-- When a witness attains the least cost for `P`, relaxing `P` to `Q` cannot increase the least
cost. -/
theorem sInf_mono_of_exists
    (hmin : ∃ w : α, P w ∧ c w = sInf {d : ℕ | ∃ w : α, P w ∧ c w ≤ d})
    (hPQ : ∀ w : α, P w → Q w) :
    sInf {d : ℕ | ∃ w : α, Q w ∧ c w ≤ d} ≤ sInf {d : ℕ | ∃ w : α, P w ∧ c w ≤ d} :=
  let ⟨_, hw, hd⟩ := hmin
  (sInf_le_of_le (hPQ _ hw)).trans_eq hd

/-- A natural number `x` characterized by `x ≤ d ↔ ∀ a, f a ≤ d` on a nonempty index type equals
the supremum `⨆ a, f a`. -/
theorem eq_ciSup_of_le_iff [Nonempty α] {x : ℕ} {f : α → ℕ}
    (h : ∀ d : ℕ, x ≤ d ↔ ∀ a, f a ≤ d) :
    x = ⨆ a, f a := by
  have hbdd : BddAbove (Set.range f) := ⟨x, Set.forall_mem_range.mpr ((h x).mp le_rfl)⟩
  exact le_antisymm ((h _).mpr (le_ciSup hbdd)) (ciSup_le ((h x).mp le_rfl))

/-- A natural number `x` characterized by `x ≤ d ↔ ∀ a, f a ≤ d` on a nonempty index type is
attained by some `a`. -/
theorem exists_eq_of_le_iff [Nonempty α] {x : ℕ} {f : α → ℕ}
    (h : ∀ d : ℕ, x ≤ d ↔ ∀ a, f a ≤ d) :
    ∃ a, f a = x := by
  have hbdd : BddAbove (Set.range f) := ⟨x, Set.forall_mem_range.mpr ((h x).mp le_rfl)⟩
  obtain ⟨a, ha⟩ := Nat.sSup_mem (Set.range_nonempty _) hbdd
  exact ⟨a, ha.trans (eq_ciSup_of_le_iff h).symm⟩

end Nat
