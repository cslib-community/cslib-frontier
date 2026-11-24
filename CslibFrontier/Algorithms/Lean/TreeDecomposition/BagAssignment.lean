/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.List.Nodup

/-!
# Bag assignments indexed in radix `q`

For dynamic programming over a tree decomposition of a constraint satisfaction problem over a finite
domain of size `q > 0`, tables at a bag listed by `L : List V` are indexed by natural numbers
`m < q ^ L.length` in mixed-arity base `q`.

* `ofRadix q L m`: decodes `m` into an assignment `V → ℕ` taking values `< q` on `L` and `0`
  outside `L`.
* `ofRadixFin q hq L m`: decodes `m` into a `Fin q`-valued assignment along `L`.
* `toRadix q L α`: encodes an assignment `α : V → ℕ` restricted to `L` as a number in
  `Finset.range (q ^ L.length)`.

Machine-level running-time bounds for radix lookup, bag projection, and constraint evaluation live
in `CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP`.

## Main definitions

* `Cslib.Algorithms.Lean.TreeDecomposition.ofRadix`
* `Cslib.Algorithms.Lean.TreeDecomposition.ofRadixFin`
* `Cslib.Algorithms.Lean.TreeDecomposition.toRadix`

## Main results

* `Cslib.Algorithms.Lean.TreeDecomposition.toRadix_ofRadix`: when `L.Nodup` and
  `m < q ^ L.length`, `toRadix q L (ofRadix q L m) = m`.
* `Cslib.Algorithms.Lean.TreeDecomposition.ofRadix_toRadix`: when `∀ v ∈ L, α v < q`,
  `ofRadix q L (toRadix q L α)` agrees with `α` on `L`.
-/

public section

namespace Cslib.Algorithms.Lean.TreeDecomposition

section Radix

variable {V : Type*} [DecidableEq V]

/-- Decode `m` in base `q` into an assignment along the variable list `L`, defaulting to `0` off
`L`. -/
@[expose] def ofRadix (q : ℕ) : List V → ℕ → (V → ℕ)
  | [], _, _ => 0
  | v :: L, m, x => if x = v then m % q else ofRadix q L (m / q) x

/-- Decode `m` in base `q` into a `Fin q`-valued assignment along `L`. -/
@[expose] def ofRadixFin (q : ℕ) (hq : 0 < q) (L : List V) (m : ℕ) (x : V) : Fin q :=
  ⟨ofRadix q L m x, by
    induction L generalizing m with
    | nil => exact hq
    | cons v L ih =>
      dsimp only [ofRadix]
      split_ifs
      · exact Nat.mod_lt m hq
      · exact ih (m / q)⟩

/-- Encode `α` on `L` in base `q`, reduced modulo `q` at each entry. -/
@[expose] def toRadix (q : ℕ) : List V → (V → ℕ) → ℕ
  | [], _ => 0
  | v :: L, α => α v % q + q * toRadix q L α

omit [DecidableEq V] in
@[simp] theorem toRadix_nil (q : ℕ) (α : V → ℕ) : toRadix q [] α = 0 := rfl

omit [DecidableEq V] in
@[simp] theorem toRadix_cons (q : ℕ) (v : V) (L : List V) (α : V → ℕ) :
    toRadix q (v :: L) α = α v % q + q * toRadix q L α := rfl

theorem ofRadix_lt {q : ℕ} (hq : 0 < q) (L : List V) (m : ℕ) (x : V) :
    ofRadix q L m x < q :=
  (ofRadixFin q hq L m x).isLt

theorem ofRadix_eq_zero_of_notMem {q : ℕ} (L : List V) (m : ℕ) {x : V} (hx : x ∉ L) :
    ofRadix q L m x = 0 := by
  induction L generalizing m with
  | nil => rfl
  | cons v L ih =>
    rw [List.mem_cons, not_or] at hx
    simp only [ofRadix, ite_eq_right (fun h => hx.1 h)]
    exact ih (m / q) hx.2

theorem ofRadix_cons_self {q : ℕ} (v : V) (L : List V) (m : ℕ) :
    ofRadix q (v :: L) m v = m % q := by
  simp [ofRadix]

theorem ofRadix_cons_ne {q : ℕ} {u x : V} (h : x ≠ u) (L : List V) (m : ℕ) :
    ofRadix q (u :: L) m x = ofRadix q L (m / q) x := by
  simp [ofRadix, h]

omit [DecidableEq V] in
theorem toRadix_congr {q : ℕ} {L : List V} {α β : V → ℕ}
    (h : ∀ v ∈ L, α v = β v) : toRadix q L α = toRadix q L β := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    simp only [toRadix, h v List.mem_cons_self,
      ih (fun w hw => h w (List.mem_cons_of_mem _ hw))]

omit [DecidableEq V] in
theorem toRadix_lt {q : ℕ} (hq : 0 < q) (L : List V) (α : V → ℕ) :
    toRadix q L α < q ^ L.length := by
  induction L with
  | nil => simp [toRadix]
  | cons v L ih =>
    simp only [toRadix, List.length_cons, Nat.pow_succ, Nat.mul_comm (q ^ L.length) q]
    have hm : α v % q < q := Nat.mod_lt _ hq
    have hmul : q * (toRadix q L α + 1) ≤ q * q ^ L.length := Nat.mul_le_mul_left q ih
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

theorem toRadix_ofRadix {q : ℕ} {L : List V} (hL : L.Nodup) {m : ℕ}
    (hm : m < q ^ L.length) : toRadix q L (ofRadix q L m) = m := by
  induction L generalizing m with
  | nil =>
    simp only [List.length_nil, Nat.pow_zero] at hm
    simp only [toRadix]
    omega
  | cons v L ih =>
    rw [List.nodup_cons] at hL
    simp only [List.length_cons, Nat.pow_succ, Nat.mul_comm (q ^ L.length) q] at hm
    have hmdiv : m / q < q ^ L.length := Nat.div_lt_of_lt_mul hm
    have hrest : toRadix q L (ofRadix q (v :: L) m) = toRadix q L (ofRadix q L (m / q)) := by
      refine toRadix_congr fun w hw => ?_
      exact ofRadix_cons_ne (fun h => by subst h; exact hL.1 hw) L m
    simp only [toRadix, ofRadix_cons_self, hrest, ih hL.2 hmdiv]
    rw [Nat.mod_mod, Nat.mod_add_div]

theorem ofRadix_toRadix {q : ℕ} (hq : 0 < q) {L : List V} {α : V → ℕ}
    (hα : ∀ v ∈ L, α v < q) {x : V} (hx : x ∈ L) :
    ofRadix q L (toRadix q L α) x = α x := by
  induction L with
  | nil => exact absurd hx List.not_mem_nil
  | cons v L ih =>
    have hmod : toRadix q (v :: L) α % q = α v := by
      rw [toRadix_cons, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (Nat.mod_lt _ hq),
        Nat.mod_eq_of_lt (hα v List.mem_cons_self)]
    have hdiv : toRadix q (v :: L) α / q = toRadix q L α := by
      rw [toRadix_cons, Nat.add_mul_div_left _ _ hq,
        Nat.div_eq_of_lt (Nat.mod_lt _ hq), Nat.zero_add]
    by_cases hxv : x = v
    · subst hxv
      rw [ofRadix_cons_self, hmod]
    · have hxL : x ∈ L := (List.mem_cons.1 hx).resolve_left hxv
      rw [ofRadix_cons_ne hxv, hdiv]
      exact ih (fun w hw => hα w (List.mem_cons_of_mem _ hw)) hxL

end Radix

end Cslib.Algorithms.Lean.TreeDecomposition
