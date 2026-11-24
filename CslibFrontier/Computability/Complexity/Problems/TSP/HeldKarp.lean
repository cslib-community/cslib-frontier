/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TSP.HeldKarp
public import CslibFrontier.Computability.Complexity.Problems.TSP
public import CslibFrontier.Computability.Complexity.FineGrained
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Tactic.EncLen
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deciding `TSP` by the Bellman–Held–Karp algorithm

This file connects the Bellman–Held–Karp dynamic program
`Cslib.Algorithms.Lean.TSP.heldKarp` [Bellman1962] [HeldKarp1962] to the decision problem
`Cslib.Complexity.TSP` on instances `x : TSPInstance` and certifies its exponential running time
on deterministic multi-tape Turing machines.

An instance `x` with `x.dist.length = n + 1` has the cities `0, …, n` at distances
`TSP.dist x.dist i j`, and it belongs to `TSP` when some ordering of all cities has closed tour
length at most `x.bound`. The tour length is the closed-walk cost `cycleCost (dist x.dist)`
(`TSP.tourLength_eq_cycleCost`), which is invariant under rotation (`cycleCost_append_comm`), so
such a tour can be taken to start at city `0`, which is the normal form `heldKarp` optimizes over.

For the multi-tape Turing-machine realization, the DP table of `2 ^ n` subset rows (each row
holding `n + 1` optional binary tour costs `List (Option ℕ)`) is processed in streaming passes
via a cyclic bit-rotation butterfly (`evens table ++ passOdds row i table`): each pass pairs
adjacent even/odd entries (`i ∉ S` vs. `i ∈ S`), relaxes `S` from `S \ {i}`, and moves bit `i`
to the back of the table ordering so that `n` passes restore the original order and complete one
Bellman–Held–Karp stage, repeated `n` times (`O(2 ^ n · poly(|encTSP x|))` total steps, with zero
quadratic `4 ^ n` table-copying overhead). Composing with the polynomial-time reduction
`HamCycle.toTSP` decides `HamCycle` within `2 ^ (n - 1) · poly(|encGraph G|)` multi-tape steps.

## Main definitions

* `Cslib.Complexity.TSP.heldKarpDecide`: run `heldKarp` on the distance matrix and compare the
  optimal tour length with the budget.

## Main results

* `Cslib.Complexity.TSP.tourLength_eq_cycleCost`: tour length is the cost of the closed walk.
* `Cslib.Complexity.TSP.mem_TSP_iff_heldKarp_le`: `x ∈ TSP` exactly when the Bellman–Held–Karp
  optimum is at most `x.bound`.
* `Cslib.Complexity.TSP.heldKarpDecide_eq_true_iff`: `heldKarpDecide` decides `TSP`.
* `Cslib.Complexity.TSP.exists_computableInO_heldKarpDecide`,
  `Cslib.Complexity.TSP.decidableInExpTime`: `TSP` is decidable on multi-tape Turing machines in
  time `2 ^ (n - 1) · poly(|encTSP x|)`.
* `Cslib.Complexity.HamCycle.heldKarpDecide_toTSP_eq_true_iff`,
  `Cslib.Complexity.HamCycle.exists_computableInO_heldKarpDecide_toTSP`,
  `Cslib.Complexity.HamCycle.decidableInExpTime`: `HamCycle` is decidable on multi-tape Turing
  machines in time `2 ^ (n - 1) · poly(|encGraph G|)` through `HamCycle.toTSP`.

## References

* [R. Bellman, *Dynamic programming treatment of the travelling salesman problem*][Bellman1962]
* [M. Held and R. M. Karp, *A dynamic programming approach to sequencing
  problems*][HeldKarp1962]
* [F. V. Fomin and D. Kratsch, *Exact Exponential Algorithms*][FominKratsch2010], Section 1.2
-/

public section

namespace Cslib.Complexity.TSP

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.TSP

/-- The length of a tour is the cost of the closed walk through its cities under `dist D`. -/
theorem tourLength_eq_cycleCost (D : List (List ℕ)) (p : List ℕ) :
    tourLength D p = cycleCost (dist D) p :=
  rfl

private theorem walkCost_succ_eq_tourLength (D : List (List ℕ)) {n : ℕ} (L : List (Fin n)) :
    walkCost (fun i j : Fin (n + 1) => dist D i j) 0 (L.map Fin.succ) 0 =
      tourLength D (0 :: L.map fun i : Fin n => (i : ℕ) + 1) := by
  rw [tourLength_eq_cycleCost, cycleCost_cons,
    ← walkCost_map Fin.val (dist D) (0 : Fin (n + 1)) (L.map Fin.succ) 0]
  simp only [List.map_map, Function.comp_def, Fin.val_succ, Fin.val_zero]

/-- **`TSP` by the Bellman–Held–Karp algorithm.** An instance with `n + 1` cities belongs to
`TSP` exactly when the optimal tour computed by `heldKarp` has length at most the budget. -/
theorem mem_TSP_iff_heldKarp_le {x : TSPInstance} {n : ℕ} (hn : x.dist.length = n + 1) :
    x ∈ TSP ↔ heldKarp (fun i j : Fin (n + 1) => dist x.dist i j) ≤ x.bound := by
  set d : Fin (n + 1) → Fin (n + 1) → ℕ := fun i j => dist x.dist i j
  constructor
  · rintro ⟨p, hp, hb⟩
    rw [hn] at hp
    obtain ⟨A, B, rfl⟩ := List.append_of_mem (hp.symm.subset (List.mem_range.2 (Nat.succ_pos n)))
    have hp' : (0 :: (B ++ A)).Perm (List.range (n + 1)) := List.perm_append_comm.symm.trans hp
    have hrot : tourLength x.dist (A ++ 0 :: B) = tourLength x.dist (0 :: (B ++ A)) :=
      cycleCost_append_comm (dist x.dist) A (0 :: B)
    have hnd := hp'.nodup_iff.2 List.nodup_range
    have hpos : ∀ v ∈ B ++ A, v ≠ 0 := fun v hv h => (List.nodup_cons.1 hnd).1 (h ▸ hv)
    have hR : ∀ v ∈ B ++ A, v - 1 < n := fun v hv => by
      have h1 := List.mem_range.1 (hp'.subset (List.mem_cons_of_mem _ hv))
      have h2 := hpos v hv
      omega
    set L : List (Fin n) := (B ++ A).pmap (fun v hv => ⟨v - 1, hv⟩) hR
    have hLmap : L.map (fun i : Fin n => (i : ℕ) + 1) = B ++ A := by
      rw [List.map_pmap]
      refine List.pmap_eq_self.2 fun v hv => ?_
      have := hpos v hv
      simp only
      omega
    have hLnd : L.Nodup := by
      have h : (L.map fun i : Fin n => (i : ℕ) + 1).Nodup := hLmap ▸ (List.nodup_cons.1 hnd).2
      exact h.of_map _
    have hLuniv : L.toFinset = Finset.univ := by
      ext i
      simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
      have hi : (i : ℕ) + 1 ∈ B ++ A := by
        have := hp'.symm.subset (List.mem_range.2 (by omega : (i : ℕ) + 1 < n + 1))
        exact (List.mem_cons.1 this).resolve_left (by omega)
      rw [← hLmap, List.mem_map] at hi
      obtain ⟨j, hj, hji⟩ := hi
      have hij : j = i := Fin.ext (by omega)
      exact hij ▸ hj
    calc heldKarp d ≤ walkCost d 0 (L.map Fin.succ) 0 :=
          (isLeast_heldKarp d).2 ⟨L, hLnd, hLuniv, rfl⟩
      _ = tourLength x.dist (A ++ 0 :: B) := by rw [walkCost_succ_eq_tourLength, hLmap, hrot]
      _ ≤ x.bound := hb
  · intro h
    obtain ⟨⟨L, hnd, hL, hc⟩, -⟩ := isLeast_heldKarp d
    refine ⟨0 :: L.map fun i : Fin n => (i : ℕ) + 1, ?_, ?_⟩
    · rw [hn]
      refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 fun v => ?_
      · refine List.nodup_cons.2 ⟨by simp, hnd.map fun i j h => Fin.ext (by simpa using h)⟩
      · simp only [List.mem_cons, List.mem_map, List.mem_range]
        constructor
        · rintro (rfl | ⟨i, -, rfl⟩)
          · omega
          · have := i.isLt
            omega
        · intro hv
          rcases v with _ | v
          · exact Or.inl rfl
          · refine Or.inr ⟨⟨v, by omega⟩, ?_, rfl⟩
            rw [← List.mem_toFinset, hL]
            exact Finset.mem_univ _
    · rw [← walkCost_succ_eq_tourLength, hc]
      exact h

/-- Decide `TSP` by the Bellman–Held–Karp algorithm [HeldKarp1962]: run `heldKarp` on the
distance matrix and compare the optimal tour length with the budget. The empty matrix is a
yes-instance, witnessed by the empty tour. -/
@[expose] def heldKarpDecide (x : TSPInstance) : Bool :=
  match x.dist.length with
  | 0 => true
  | n + 1 => decide (heldKarp (fun i j : Fin (n + 1) => dist x.dist i j) ≤ x.bound)

/-- `heldKarpDecide` decides `TSP`. -/
theorem heldKarpDecide_eq_true_iff (x : TSPInstance) :
    heldKarpDecide x = true ↔ x ∈ TSP := by
  unfold heldKarpDecide
  split
  · rename_i h
    simp only [true_iff]
    refine ⟨[], ?_, by simp [tourLength]⟩
    rw [h, List.range_zero]
  · rename_i n h
    simp only [decide_eq_true_eq]
    exact (mem_TSP_iff_heldKarp_le h).symm

/-! ## Multi-tape Turing-machine exponential-time realization -/

section TuringRealization

open Turing.MultiTapeTM ComputableInPolyTime

private abbrev Row := List (Option ℕ)

private abbrev encRow : Row ↪ List Bool := encList (encOption encNat)

private def optMin (a b : Option ℕ) : Option ℕ :=
  match a, b with
  | none, b => b
  | a, none => a
  | some x, some y => some (min x y)

private def relaxRow (distRow : List ℕ) (u : Option ℕ) (r : Row) : Row :=
  match u with
  | none => r
  | some base =>
      r.zipIdx.map fun p => optMin p.1 (some (base + distRow.getD p.2 0))

private theorem length_relaxRow (distRow : List ℕ) (u : Option ℕ) (r : Row) :
    (relaxRow distRow u r).length = r.length := by
  cases u <;> simp [relaxRow]

private theorem getElem?_relaxRow (distRow : List ℕ) (u : Option ℕ) (r : Row) (t : ℕ) :
    (relaxRow distRow u r)[t]? =
      match u with
      | none => r[t]?
      | some base => r[t]?.map fun cur => optMin cur (some (base + distRow.getD t 0)) := by
  cases u with
  | none => rfl
  | some base =>
    dsimp [relaxRow]
    by_cases ht : t < r.length
    · rw [List.getElem?_eq_getElem (by simpa using ht), List.getElem_map, List.getElem_zipIdx,
        List.getElem?_eq_getElem ht, Option.map_some, Nat.zero_add]
    · have ht' : r.length ≤ t := Nat.le_of_not_lt ht
      rw [List.getElem?_eq_none (by simpa using ht'), List.getElem?_eq_none ht', Option.map_none]

private theorem getD_relaxRow (distRow : List ℕ) (u : Option ℕ) (r : Row) {t : ℕ}
    (ht : t < r.length) :
    (relaxRow distRow u r).getD t none =
      match u with
      | none => r.getD t none
      | some base => optMin (r.getD t none) (some (base + distRow.getD t 0)) := by
  rw [List.getD_eq_getElem?_getD, getElem?_relaxRow, List.getD_eq_getElem?_getD]
  cases u with
  | none => rfl
  | some base =>
    dsimp only
    rw [List.getElem?_eq_getElem ht, Option.map_some, Option.getD_some,
      List.getD_eq_getElem _ _ ht]

private def evens {α : Type*} : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: rest => a :: evens rest

private def odds {α : Type*} : List α → List α
  | [] => []
  | [_] => []
  | _ :: b :: rest => b :: odds rest

private def passOddsList {α : Type*} (f : α → α → α) : List α → List α
  | a :: b :: rest => f a b :: passOddsList f rest
  | _ => []

private def passStep {α : Type*} (f : α → α → α) (L : List α) : List α :=
  evens L ++ passOddsList f L

private def interleave {α : Type*} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: interleave ys xs
termination_by xs ys => xs.length + ys.length
decreasing_by
  simp_wf
  omega

private theorem length_interleave {α : Type*} (xs ys : List α) :
    (interleave xs ys).length = xs.length + ys.length := by
  suffices h : ∀ k (xs ys : List α), xs.length + ys.length ≤ k →
      (interleave xs ys).length = xs.length + ys.length from h _ xs ys le_rfl
  intro k
  induction k with
  | zero =>
    intro xs ys hk
    cases xs <;> cases ys <;> simp_all [interleave]
  | succ k ih =>
    intro xs ys hk
    cases xs with
    | nil => simp [interleave]
    | cons x xs =>
      have hlen : ys.length + xs.length ≤ k := by
        simp only [List.length_cons] at hk
        omega
      rw [interleave, List.length_cons, ih ys xs hlen, List.length_cons]
      omega

private theorem evens_interleave {α : Type*} (xs ys : List α) (h : xs.length = ys.length) :
    evens (interleave xs ys) = xs := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [interleave, evens]
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons] at h
      simp only [interleave, evens, ih ys (by omega)]

private theorem passOddsList_interleave {α : Type*} (f : α → α → α) (xs ys : List α)
    (h : xs.length = ys.length) :
    passOddsList f (interleave xs ys) = List.zipWith f xs ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [interleave, passOddsList]
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons] at h
      simp only [interleave, passOddsList, List.zipWith_cons_cons, ih ys (by omega)]

private theorem interleave_append {α : Type*} (xs₁ ys₁ xs₂ ys₂ : List α)
    (h : xs₁.length = ys₁.length) :
    interleave xs₁ ys₁ ++ interleave xs₂ ys₂ = interleave (xs₁ ++ xs₂) (ys₁ ++ ys₂) := by
  induction xs₁ generalizing ys₁ with
  | nil =>
    cases ys₁ with
    | nil => simp [interleave]
    | cons _ _ => simp at h
  | cons x xs₁ ih =>
    cases ys₁ with
    | nil => simp at h
    | cons y ys₁ =>
      simp only [List.length_cons] at h
      simp only [interleave, List.cons_append, ih ys₁ (by omega)]

private def tabulateLSB {α : Type*} : ℕ → (List Bool → α) → List α
  | 0, f => [f []]
  | m + 1, f => interleave (tabulateLSB m (fun bs => f (false :: bs)))
      (tabulateLSB m (fun bs => f (true :: bs)))

private theorem length_tabulateLSB {α : Type*} (m : ℕ) (f : List Bool → α) :
    (tabulateLSB m f).length = 2 ^ m := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    simp only [tabulateLSB, length_interleave, ih, pow_succ]
    omega

private theorem tabulateLSB_congr {α : Type*} {m : ℕ} {f g : List Bool → α}
    (h : ∀ bs, bs.length = m → f bs = g bs) :
    tabulateLSB m f = tabulateLSB m g := by
  induction m generalizing f g with
  | zero => simp [tabulateLSB, h [] rfl]
  | succ m ih =>
    simp only [tabulateLSB]
    congr 1
    · exact ih fun bs hbs => h (false :: bs) (by simp [hbs])
    · exact ih fun bs hbs => h (true :: bs) (by simp [hbs])

private theorem zipWith_tabulateLSB {α : Type*} (m : ℕ) (f : α → α → α)
    (g₁ g₂ : List Bool → α) :
    List.zipWith f (tabulateLSB m g₁) (tabulateLSB m g₂) =
      tabulateLSB m fun bs => f (g₁ bs) (g₂ bs) := by
  induction m generalizing g₁ g₂ with
  | zero => rfl
  | succ m ih =>
    have hlen1 : (tabulateLSB m fun bs => g₁ (false :: bs)).length =
        (tabulateLSB m fun bs => g₁ (true :: bs)).length := by
      simp [length_tabulateLSB]
    have hlen2 : (tabulateLSB m fun bs => g₂ (false :: bs)).length =
        (tabulateLSB m fun bs => g₂ (true :: bs)).length := by
      simp [length_tabulateLSB]
    have key : ∀ (a₁ b₁ a₂ b₂ : List α), a₁.length = b₁.length → a₂.length = b₂.length →
        a₁.length = a₂.length →
        List.zipWith f (interleave a₁ b₁) (interleave a₂ b₂) =
          interleave (List.zipWith f a₁ a₂) (List.zipWith f b₁ b₂) := by
      intro a₁ b₁ a₂ b₂ h1 h2 h12
      induction a₁ generalizing b₁ a₂ b₂ with
      | nil =>
        cases b₁ <;> cases a₂ <;> cases b₂ <;> simp at h1 h2 h12 ⊢
        simp [interleave]
      | cons x xs ih' =>
        cases b₁ with
        | nil => simp at h1
        | cons y ys =>
          cases a₂ with
          | nil => simp at h12
          | cons u us =>
            cases b₂ with
            | nil => simp at h2
            | cons v vs =>
              simp only [List.length_cons] at h1 h2 h12
              simp only [interleave, List.zipWith_cons_cons, ih' ys us vs (by omega) (by omega)
                (by omega)]
    rw [tabulateLSB, tabulateLSB, tabulateLSB,
      key _ _ _ _ hlen1 hlen2 (by simp [length_tabulateLSB]), ih, ih]

private theorem tabulateLSB_append_eq {α : Type*} (m : ℕ) (g : List Bool → α) :
    tabulateLSB m (fun bs => g (bs ++ [false])) ++
        tabulateLSB m (fun bs => g (bs ++ [true])) =
      tabulateLSB (m + 1) g := by
  induction m generalizing g with
  | zero => simp [tabulateLSB, interleave]
  | succ m ih =>
    rw [tabulateLSB, tabulateLSB, interleave_append _ _ _ _ (by simp [length_tabulateLSB])]
    simp only [List.cons_append]
    rw [ih (fun bs => g (false :: bs)), ih (fun bs => g (true :: bs))]
    rfl

private theorem getLast?_interleave {α : Type*} (xs ys : List α)
    (h : xs.length = ys.length) (hne : ys ≠ []) :
    (interleave xs ys).getLast? = ys.getLast? := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => exact absurd rfl hne
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => exact absurd rfl hne
    | cons y ys =>
      cases ys with
      | nil =>
        cases xs with
        | nil => simp [interleave]
        | cons _ _ => simp at h
      | cons y' ys' =>
        cases xs with
        | nil => simp at h
        | cons x' xs' =>
          have hlen : (x' :: xs').length = (y' :: ys').length := by
            simp only [List.length_cons] at h ⊢
            omega
          have ih' := ih (y' :: ys') hlen (List.cons_ne_nil _ _)
          simpa [interleave] using ih'

private theorem getLast?_tabulateLSB {α : Type*} (m : ℕ) (g : List Bool → α) :
    (tabulateLSB m g).getLast? = some (g (List.replicate m true)) := by
  induction m generalizing g with
  | zero => rfl
  | succ m ih =>
    rw [tabulateLSB, getLast?_interleave _ _ (by simp [length_tabulateLSB])
      (by intro he; have := congrArg List.length he; simp [length_tabulateLSB] at this),
      ih fun bs => g (true :: bs), List.replicate_succ]

private theorem foldl_last_tabulateLSB {α : Type*} (m : ℕ) (g : List Bool → α) (d : α) :
    (tabulateLSB m g).foldl (fun _ x => x) d = g (List.replicate m true) := by
  have hne : tabulateLSB m g ≠ [] := by
    intro he
    have := congrArg List.length he
    simp [length_tabulateLSB] at this
  have hfl (l : List α) (hne : l ≠ []) (d : α) :
      some (l.foldl (fun _ x => x) d) = l.getLast? := by
    induction l generalizing d with
    | nil => exact absurd rfl hne
    | cons a t ih =>
      cases t with
      | nil => simp
      | cons b t =>
        simp only [List.foldl_cons, List.getLast?_cons_cons]
        exact ih (List.cons_ne_nil _ _) a
  have h := hfl (tabulateLSB m g) hne d
  rw [getLast?_tabulateLSB] at h
  exact Option.some.inj h

private def setOfBits (n : ℕ) (bs : List Bool) : Finset (Fin n) :=
  Finset.univ.filter fun j => bs.getD j.val false = true

private theorem setOfBits_replicate_true (n : ℕ) :
    setOfBits n (List.replicate n true) = Finset.univ := by
  ext j
  simp [setOfBits]

private theorem setOfBits_replicate_false (n : ℕ) :
    setOfBits n (List.replicate n false) = ∅ := by
  ext j
  simp only [setOfBits, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false]
  rw [List.getD_eq_getElem _ _ (by simp [j.isLt]), List.getElem_replicate]
  decide

private theorem rotate_cons_rotate_sub {α : Type*} {n i : ℕ} (hi : i < n) (b : α)
    (r : List α) (hr : r.length + 1 = n) :
    (r ++ [b]).rotate (n - (i + 1)) = (b :: r).rotate (n - i) := by
  have h1 : r ++ [b] = (b :: r).rotate 1 := by simp [List.rotate_cons_succ]
  rw [h1, List.rotate_rotate]
  congr 1
  omega

private theorem getD_rotate_cons {n i : ℕ} (hi : i < n) (b : Bool)
    (r : List Bool) (hr : r.length + 1 = n) (d : Bool) (j : Fin n) :
    ((b :: r).rotate (n - i)).getD j.val d =
      if j.val = i then b else ((false :: r).rotate (n - i)).getD j.val d := by
  have hlen : (b :: r).length = n := by simp [hr]
  have hlenf : (false :: r).length = n := by simp [hr]
  have hj : j.val < ((b :: r).rotate (n - i)).length := by
    rw [List.length_rotate, hlen]; exact j.isLt
  have hjf : j.val < ((false :: r).rotate (n - i)).length := by
    rw [List.length_rotate, hlenf]; exact j.isLt
  rw [List.getD_eq_getElem _ _ hj, List.getElem_rotate]
  by_cases hji : j.val = i
  · subst hji
    have hmod : (j.val + (n - j.val)) % (b :: r).length = 0 := by
      rw [hlen, Nat.add_sub_of_le j.isLt.le, Nat.mod_self]
    simp only [hmod, List.getElem_cons_zero, ↓reduceIte]
  · rw [ite_eq_right hji, List.getD_eq_getElem _ _ hjf, List.getElem_rotate]
    have hnz : (j.val + (n - i)) % n ≠ 0 := by
      intro h0
      rcases Nat.lt_or_ge j.val i with hlt | hgt
      · have hsum : j.val + (n - i) < n := by omega
        rw [Nat.mod_eq_of_lt hsum] at h0
        omega
      · have hlt' : i < j.val := Nat.lt_of_le_of_ne hgt (Ne.symm hji)
        have hsum : j.val + (n - i) = (j.val - i) + n := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h0
        omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hnz
    have hk1 : (j.val + (n - i)) % (b :: r).length = k + 1 := by rw [hlen]; exact hk
    have hk2 : (j.val + (n - i)) % (false :: r).length = k + 1 := by rw [hlenf]; exact hk
    simp only [hk1, hk2, List.getElem_cons_succ]

private theorem setOfBits_rotate_true {n i : ℕ} (hi : i < n) (r : List Bool)
    (hr : r.length + 1 = n) :
    setOfBits n ((true :: r).rotate (n - i)) =
      insert ⟨i, hi⟩ (setOfBits n ((false :: r).rotate (n - i))) := by
  ext j
  simp only [setOfBits, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.ext_iff]
  rw [getD_rotate_cons hi true r hr false j]
  by_cases hji : j.val = i
  · simp [hji]
  · simp [hji]

private theorem setOfBits_rotate_true_erase {n i : ℕ} (hi : i < n) (r : List Bool)
    (hr : r.length + 1 = n) :
    (setOfBits n ((true :: r).rotate (n - i))).erase ⟨i, hi⟩ =
      setOfBits n ((false :: r).rotate (n - i)) := by
  rw [setOfBits_rotate_true hi r hr, Finset.erase_insert]
  simp only [setOfBits, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [getD_rotate_cons hi false r hr false ⟨i, hi⟩]
  simp

private theorem passStep_tabulateLSB_rotate {n i : ℕ} (hn : 0 < n) (hi : i < n)
    (f : Row → Row → Row) (G : Finset (Fin n) → Row) :
    passStep f (tabulateLSB n fun bs => G (setOfBits n (bs.rotate (n - i)))) =
      tabulateLSB n fun bs =>
        let S := setOfBits n (bs.rotate (n - (i + 1)))
        if ⟨i, hi⟩ ∈ S then f (G (S.erase ⟨i, hi⟩)) (G S) else G S := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [passStep, tabulateLSB,
    evens_interleave _ _ (by simp [length_tabulateLSB]),
    passOddsList_interleave _ _ _ (by simp [length_tabulateLSB]),
    zipWith_tabulateLSB, ← tabulateLSB_append_eq]
  refine congrArg₂ (· ++ ·) (tabulateLSB_congr fun r hr => ?_) (tabulateLSB_congr fun r hr => ?_)
  · have hlen : r.length + 1 = m + 1 := by omega
    rw [rotate_cons_rotate_sub hi false r hlen]
    have hnot : (⟨i, hi⟩ : Fin (m + 1)) ∉ setOfBits (m + 1) ((false :: r).rotate (m + 1 - i)) := by
      simp only [setOfBits, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [getD_rotate_cons hi false r hlen false ⟨i, hi⟩]
      simp
    simp [hnot]
  · have hlen : r.length + 1 = m + 1 := by omega
    rw [rotate_cons_rotate_sub hi true r hlen]
    have hmem : (⟨i, hi⟩ : Fin (m + 1)) ∈ setOfBits (m + 1) ((true :: r).rotate (m + 1 - i)) := by
      simp only [setOfBits, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [getD_rotate_cons hi true r hlen false ⟨i, hi⟩]
      simp
    simp [hmem, setOfBits_rotate_true_erase hi r hlen]

/-! ### Streaming list-pass combinator and DP correctness -/

private theorem evens_odds_streamEmit (L : List Row) :
    ∀ b : Bool,
      encList encRow (if b then evens L else odds L) =
        streamEmit (fun p : Bool × Row => !p.1)
          (fun p => encList encRow (if p.1 then [p.2] else [])) b L := by
  match L with
  | [] => intro b; cases b <;> rfl
  | [a] => intro b; cases b <;> simp [evens, odds, streamEmit, encList_cons, encList_nil]
  | a :: b' :: rest =>
    intro b
    have ih := evens_odds_streamEmit rest
    cases b
    · simpa [odds, streamEmit, encList_cons, encList_nil] using ih false
    · simpa [evens, streamEmit, encList_cons, encList_nil] using ih true

private theorem length_encList_evens_or_odds_le (b : Bool) (L : List Row) :
    (encList encRow (if b then evens L else odds L)).length ≤ (encList encRow L).length := by
  match L with
  | [] => cases b <;> simp [evens, odds]
  | [a] => cases b <;> simp [evens, odds]
  | a :: b' :: rest =>
    have ih := length_encList_evens_or_odds_le b rest
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, odds, encList_cons, List.length_append] at ih ⊢
      omega
    · simp only [↓reduceIte, evens, encList_cons, List.length_append] at ih ⊢
      omega

private theorem computableInO_evens :
    ∃ d, ComputableInO (evens (α := Row)) (encList encRow) (encList encRow)
      (fun L => (encList encRow L).length +
        (L.length + 1) * (listMax (fun r => (encRow r).length) L + 1) ^ d)
      (fun L => (encList encRow L).length +
        (listMax (fun r => (encRow r).length) L + 1) ^ d) := by
  have hnext : ComputableInPolyTime (fun p : Bool × Row => !p.1)
      (encPair encBool encRow) encBool :=
    (ComputableInDegree.of_finite Bool.not).computableInPolyTime.comp (fst encBool encRow)
  have hemit : ComputableInPolyTime (fun p : Bool × Row => if p.1 then [p.2] else [])
      (encPair encBool encRow) (encList encRow) := by
    fun_prop
  obtain ⟨c, d, h⟩ := ComputableInTimeAndSpace.streamFold_pair_list
    (encA := encRow) (encS := encBool) (encB := encRow)
    (encIn := encPair encBool (encList encRow))
    (init := Prod.fst) (elems := Prod.snd)
    (fun _ => rfl)
    hnext hemit
    (g := fun p : Bool × List Row => if p.1 then evens p.2 else odds p.2)
    (fun p => evens_odds_streamEmit p.2 p.1)
    (lMax := fun p => listMax (fun r => (encRow r).length) p.2 + 1)
    (fun _ _ _ => by simp [encBool_apply])
    (fun p j hj => (le_listMax (f := fun r => (encRow r).length) (List.getElem_mem hj)).trans
      (Nat.le_succ _))
  have hpair : ComputableInO (fun p : Bool × List Row => if p.1 then evens p.2 else odds p.2)
      (encPair encBool (encList encRow)) (encList encRow)
      (fun p => (encList encRow p.2).length +
        (p.2.length + 1) * (listMax (fun r => (encRow r).length) p.2 + 1) ^ d)
      (fun p => (encList encRow p.2).length +
        (listMax (fun r => (encRow r).length) p.2 + 1) ^ d) := by
    have hpow : ∀ L : List Row, (listMax (fun r => (encRow r).length) L + 2) ^ d ≤
        2 ^ d * (listMax (fun r => (encRow r).length) L + 1) ^ d := fun L => by
      have hle : listMax (fun r => (encRow r).length) L + 2 ≤
          2 * (listMax (fun r => (encRow r).length) L + 1) := by omega
      calc (listMax (fun r => (encRow r).length) L + 2) ^ d
          ≤ (2 * (listMax (fun r => (encRow r).length) L + 1)) ^ d :=
            Nat.pow_le_pow_left hle d
        _ = 2 ^ d * (listMax (fun r => (encRow r).length) L + 1) ^ d := Nat.mul_pow _ _ _
    let C₀ := 2 ^ d * (c + 1) + 4 * (c + 1) + 4
    have hc2d : 2 ^ d * c ≤ C₀ := by
      have : 2 ^ d * c ≤ 2 ^ d * (c + 1) := Nat.mul_le_mul_left _ (Nat.le_succ c)
      dsimp [C₀]; omega
    refine ComputableInO.of_bounds h C₀ (fun p => ?_) (fun p => ?_) (fun p => ?_)
    · have hlen_p : (encPair encBool (encList encRow) p).length ≤
          (encList encRow p.2).length + 3 := by
        rw [length_encPair]
        cases p.1 <;> simp [encBool_apply]
        all_goals omega
      have hmul_le : (p.2.length + 1) * (listMax (fun r => (encRow r).length) p.2 + 2) ^ d ≤
          2 ^ d * ((p.2.length + 1) * (listMax (fun r => (encRow r).length) p.2 + 1) ^ d) := by
        calc _ ≤ (p.2.length + 1) * (2 ^ d * (listMax (fun r => (encRow r).length) p.2 + 1) ^ d) :=
              Nat.mul_le_mul_left _ (hpow p.2)
          _ = _ := by ring
      set A := (encList encRow p.2).length
      set B := (p.2.length + 1) * (listMax (fun r => (encRow r).length) p.2 + 1) ^ d
      have hcA : c ≤ C₀ := by dsimp [C₀]; omega
      have hc4 : 4 * c ≤ C₀ := by dsimp [C₀]; omega
      calc c * ((encPair encBool (encList encRow) p).length +
              (p.2.length + 1) * (listMax (fun r => (encRow r).length) p.2 + 2) ^ d + 1)
          ≤ c * (A + 4 + 2 ^ d * B) := Nat.mul_le_mul_left c (by omega)
        _ = c * A + (2 ^ d * c) * B + 4 * c := by ring
        _ ≤ C₀ * A + C₀ * B + C₀ * 1 := by
            have h1 := Nat.mul_le_mul_right A hcA
            have h2 := Nat.mul_le_mul_right B hc2d
            omega
        _ = C₀ * (A + B + 1) := by ring
    · have _ := hpow p.2
      set B := (listMax (fun r => (encRow r).length) p.2 + 1) ^ d
      have hc1 : c ≤ C₀ := by dsimp [C₀]; omega
      calc c * ((listMax (fun r => (encRow r).length) p.2 + 2) ^ d + 1)
          ≤ c * (2 ^ d * B + 1) := Nat.mul_le_mul_left c (by omega)
        _ = (2 ^ d * c) * B + c := by ring
        _ ≤ C₀ * B + C₀ := by
            have h1 := Nat.mul_le_mul_right B hc2d
            omega
        _ ≤ C₀ * ((encList encRow p.2).length + B + 1) := by
            have hle : B + 1 ≤ (encList encRow p.2).length + B + 1 := by omega
            calc C₀ * B + C₀ = C₀ * (B + 1) := by ring
              _ ≤ C₀ * ((encList encRow p.2).length + B + 1) := Nat.mul_le_mul_left _ hle
    · have h1 := length_encList_evens_or_odds_le p.1 p.2
      have hpos : 1 ≤ 2 ^ d * (c + 1) + 4 * (c + 1) + 4 := by omega
      calc (encList encRow (if p.1 then evens p.2 else odds p.2)).length
          ≤ (encList encRow p.2).length := h1
        _ ≤ (encList encRow p.2).length +
            (listMax (fun r => (encRow r).length) p.2 + 1) ^ d + 1 := by omega
        _ = 1 * ((encList encRow p.2).length +
            (listMax (fun r => (encRow r).length) p.2 + 1) ^ d + 1) := by ring
        _ ≤ (2 ^ d * (c + 1) + 4 * (c + 1) + 4) * ((encList encRow p.2).length +
            (listMax (fun r => (encRow r).length) p.2 + 1) ^ d + 1) :=
            Nat.mul_le_mul_right _ hpos
  have hwrap : ComputableInO (fun L : List Row => (true, L))
      (encList encRow) (encPair encBool (encList encRow))
      (fun L => (encList encRow L).length) (fun L => (encList encRow L).length) := by
    have hp := (ComputableInO.const (encIn := encList encRow) (encMid := encBool) true).prod
      (ComputableInO.id' (encMid := encList encRow))
    exact hp.mono 2 (fun _ => by omega) (fun _ => by omega)
  exact ⟨d, (hpair.comp hwrap).mono 2 (fun _ => by dsimp; omega) (fun _ => by dsimp; omega)⟩

private abbrev OddParams := List ℕ × ℕ

private abbrev encOddParams : OddParams ↪ List Bool := encPair (encList encNat) encUnary

private abbrev OddState := OddParams × Option Row

private abbrev encOddState : OddState ↪ List Bool := encPair encOddParams (encOption encRow)

private def oddNext (q : OddState × Row) : OddState :=
  (q.1.1, match q.1.2 with | none => some q.2 | some _ => none)

private def oddEmit (q : OddState × Row) : List Row :=
  match q.1.2 with
  | none => []
  | some r₀ => [relaxRow q.1.1.1 (r₀.getD (q.1.1.2 + 1) none) q.2]

private def passOddsFrom : Option Row → OddParams → List Row → List Row
  | none, _, [] => []
  | none, _, [_] => []
  | none, p, a :: b :: rest =>
      relaxRow p.1 (a.getD (p.2 + 1) none) b :: passOddsFrom none p rest
  | some _, _, [] => []
  | some a, p, b :: rest =>
      relaxRow p.1 (a.getD (p.2 + 1) none) b :: passOddsFrom none p rest

private theorem passOddsFrom_none_eq (p : OddParams) (L : List Row) :
    passOddsFrom none p L =
      passOddsList (fun r₀ r₁ => relaxRow p.1 (r₀.getD (p.2 + 1) none) r₁) L := by
  match L with
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest =>
    simp [passOddsFrom, passOddsList, passOddsFrom_none_eq p rest]

private theorem passOddsFrom_streamEmit (o : Option Row) (p : OddParams) (L : List Row) :
    encList encRow (passOddsFrom o p L) =
      streamEmit oddNext (fun q => encList encRow (oddEmit q)) (p, o) L := by
  match o, L with
  | none, [] => rfl
  | none, [a] => simp [passOddsFrom, streamEmit, oddEmit]
  | none, a :: b :: rest =>
    rw [passOddsFrom, streamEmit, oddNext, oddEmit]
    simp only [encList_nil, List.nil_append, streamEmit, oddNext, oddEmit, encList_cons,
      List.append_nil]
    exact congrArg _ (passOddsFrom_streamEmit none p rest)
  | some r₀, [] => rfl
  | some r₀, a :: rest =>
    rw [passOddsFrom, streamEmit, oddNext, oddEmit]
    simp only [encList_cons, encList_nil, List.append_nil]
    exact congrArg _ (passOddsFrom_streamEmit none p rest)

private theorem streamState_oddNext_mem (L : List Row) (j : ℕ) (p : OddParams) (o : Option Row) :
    (streamState (p, o) oddNext L j).1 = p ∧
      ((streamState (p, o) oddNext L j).2 = none ∨
        (streamState (p, o) oddNext L j).2 = o ∨
        ∃ r ∈ L, (streamState (p, o) oddNext L j).2 = some r) := by
  have htake : ∀ xs : List Row, xs ⊆ L → ∀ s : Option Row,
      (xs.foldl (fun st r => oddNext (st, r)) (p, s)).1 = p ∧
        ((xs.foldl (fun st r => oddNext (st, r)) (p, s)).2 = none ∨
          (xs.foldl (fun st r => oddNext (st, r)) (p, s)).2 = s ∨
          ∃ r ∈ L, (xs.foldl (fun st r => oddNext (st, r)) (p, s)).2 = some r) := by
    intro xs hsub s
    induction xs generalizing s with
    | nil => exact ⟨rfl, Or.inr (Or.inl rfl)⟩
    | cons a xs ih =>
      simp only [List.foldl_cons, oddNext]
      have ha : a ∈ L := hsub List.mem_cons_self
      have hsub' : xs ⊆ L := fun z hz => hsub (List.mem_cons_of_mem _ hz)
      cases s with
      | none =>
        obtain ⟨h1, h2⟩ := ih hsub' (some a)
        refine ⟨h1, ?_⟩
        rcases h2 with h2 | h2 | ⟨r, hr, h2⟩
        · exact Or.inl h2
        · exact Or.inr (Or.inr ⟨a, ha, h2⟩)
        · exact Or.inr (Or.inr ⟨r, hr, h2⟩)
      | some s₀ =>
        obtain ⟨h1, h2⟩ := ih hsub' none
        refine ⟨h1, ?_⟩
        rcases h2 with h2 | h2 | ⟨r, hr, h2⟩
        · exact Or.inl h2
        · exact Or.inl h2
        · exact Or.inr (Or.inr ⟨r, hr, h2⟩)
  exact htake (L.take j) (List.take_subset j L) o

private theorem computableInPolyTime_optMin :
    ComputableInPolyTime (fun p : Option ℕ × Option ℕ => optMin p.1 p.2)
      (encPair (encOption encNat) (encOption encNat)) (encOption encNat) := by
  have heq : (fun p : Option ℕ × Option ℕ => optMin p.1 p.2) = fun p =>
      p.1.elim p.2 fun x => p.2.elim (some x) fun y => some (if x ≤ y then x else y) := by
    funext ⟨a, b⟩
    cases a <;> cases b <;> simp [optMin, Nat.min_def]
  rw [heq]
  refine optionElimWithInput (fst _ _) (snd _ _) ?_
  refine optionElimWithInput (snd _ (encOption encNat) |>.comp (fst _ _))
    (optionSome _ |>.comp (snd _ _)) ?_
  refine (optionSome encNat).comp ?_
  exact (binary_le.comp
    ((snd (encPair (encOption encNat) (encOption encNat)) encNat |>.comp (fst _ _)).prod
      (snd _ _))).ite_decide
    (snd (encPair (encOption encNat) (encOption encNat)) encNat |>.comp (fst _ _))
    (snd _ _)

private theorem computableInPolyTime_relaxRow :
    ComputableInPolyTime (fun p : (List ℕ × Option ℕ) × Row => relaxRow p.1.1 p.1.2 p.2)
      (encPair (encPair (encList encNat) (encOption encNat)) encRow) encRow := by
  have heq : (fun p : (List ℕ × Option ℕ) × Row => relaxRow p.1.1 p.1.2 p.2) = fun p =>
      p.1.2.elim p.2 fun base => p.2.zipIdx.map fun q =>
        optMin q.1 (some (base + p.1.1.getD q.2 0)) := by
    funext ⟨⟨d, u⟩, r⟩
    cases u <;> rfl
  rw [heq]
  refine optionElimWithInput (snd _ _ |>.comp (fst _ _)) (snd _ _) ?_
  refine mapWithInput (zipIdx (encOption encNat) |>.comp (snd _ _ |>.comp (fst _ _))) ?_
  let encCtx := encPair (encPair (encPair (encList encNat) (encOption encNat)) encRow) encNat
  have hcur : ComputableInPolyTime
      (fun q : (((List ℕ × Option ℕ) × Row) × ℕ) × (Option ℕ × ℕ) => q.2.1)
      (encPair encCtx (encPair (encOption encNat) encUnary)) (encOption encNat) := by fun_prop
  have hdistq : ComputableInPolyTime
      (fun q : (((List ℕ × Option ℕ) × Row) × ℕ) × (Option ℕ × ℕ) =>
        q.1.1.1.1.getD q.2.2 0)
      (encPair encCtx (encPair (encOption encNat) encUnary)) encNat := by fun_prop
  have hbase : ComputableInPolyTime
      (fun q : (((List ℕ × Option ℕ) × Row) × ℕ) × (Option ℕ × ℕ) => q.1.2)
      (encPair encCtx (encPair (encOption encNat) encUnary)) encNat := by fun_prop
  exact computableInPolyTime_optMin.comp
    (hcur.prod ((optionSome _).comp (binary_add' hbase hdistq)))

private theorem computableInO_passOdds :
    ∃ d, ComputableInO (fun p : OddParams × List Row => passOddsFrom none p.1 p.2)
      (encPair encOddParams (encList encRow)) (encList encRow)
      (fun p => (encPair encOddParams (encList encRow) p).length +
        (p.2.length + 1) *
          ((encOddParams p.1).length + listMax (fun r => (encRow r).length) p.2 + 1) ^ d)
      (fun p => (encOddParams p.1).length + (encList encRow p.2).length +
        (p.2.length + 1) *
          (listMax (fun r => (encRow r).length) p.2 +
            (encOddParams p.1).length + 1) ^ d) := by
  have hnext : ComputableInPolyTime oddNext (encPair encOddState encRow) encOddState := by
    have heq : oddNext = fun q => (q.1.1, q.1.2.elim (some q.2) (fun _ => none)) := by
      funext ⟨⟨_, o⟩, _⟩
      cases o <;> rfl
    rw [heq]
    refine ((fst encOddParams (encOption encRow)).comp (fst encOddState encRow)).prod ?_
    exact optionElimWithInput
      ((snd encOddParams (encOption encRow)).comp (fst encOddState encRow))
      ((optionSome encRow).comp (snd encOddState encRow))
      (const (encIn := encPair (encPair encOddState encRow) encRow) (encOut := encOption encRow)
        none)
  have hemit : ComputableInPolyTime oddEmit (encPair encOddState encRow) (encList encRow) := by
    have heq : oddEmit = fun q =>
        q.1.2.elim [] (fun r₀ => [relaxRow q.1.1.1 (r₀.getD (q.1.1.2 + 1) none) q.2]) := by
      funext ⟨⟨_, o⟩, _⟩
      cases o <;> rfl
    rw [heq]
    refine optionElimWithInput
      ((snd encOddParams (encOption encRow)).comp (fst encOddState encRow))
      (const (encIn := encPair encOddState encRow) (encOut := encList encRow) []) ?_
    have hd : ComputableInPolyTime
        (fun q : (OddState × Row) × Row => q.1.1.1.1)
        (encPair (encPair encOddState encRow) encRow) (encList encNat) := by fun_prop
    have hi : ComputableInPolyTime
        (fun q : (OddState × Row) × Row => q.1.1.1.2 + 1)
        (encPair (encPair encOddState encRow) encRow) encUnary := by fun_prop
    have hu : ComputableInPolyTime
        (fun q : (OddState × Row) × Row => q.2.getD (q.1.1.1.2 + 1) none)
        (encPair (encPair encOddState encRow) encRow) (encOption encNat) :=
      listGetDWithInput (snd (encPair encOddState encRow) encRow) hi none
    have hr1 : ComputableInPolyTime
        (fun q : (OddState × Row) × Row => q.1.2)
        (encPair (encPair encOddState encRow) encRow) encRow := by fun_prop
    exact (computableInPolyTime_relaxRow.comp ((hd.prod hu).prod hr1)).cons'
      (const (encIn := encPair (encPair encOddState encRow) encRow) (encOut := encList encRow) [])
  obtain ⟨c, d, h⟩ := ComputableInTimeAndSpace.streamFold_pair_list
    (encA := encRow) (encS := encOddState) (encB := encRow)
    (encIn := encPair encOddState (encList encRow))
    (init := Prod.fst) (elems := Prod.snd)
    (fun _ => rfl)
    hnext hemit
    (g := fun q : OddState × List Row => passOddsFrom q.1.2 q.1.1 q.2)
    (fun q => passOddsFrom_streamEmit q.1.2 q.1.1 q.2)
    (lMax := fun q => 2 * (encOddParams q.1.1).length + 2 * (encOption encRow q.1.2).length +
      listMax (fun r => (encRow r).length) q.2 + 4)
    (fun q j _ => by
      obtain ⟨h1, h2⟩ := streamState_oddNext_mem q.2 j q.1.1 q.1.2
      rw [length_encPair, h1]
      rcases h2 with h2 | h2 | ⟨r, hr, h2⟩
      · rw [h2]; simp; omega
      · rw [h2]; omega
      · rw [h2, encOption_some, List.length_cons]
        have := le_listMax (f := fun r => (encRow r).length) hr
        omega)
    (fun q j hj => (le_listMax (f := fun r => (encRow r).length) (List.getElem_mem hj)).trans
      (by omega))
  have hwrap : ComputableInO (fun p : OddParams × List Row => ((p.1, none), p.2))
      (encPair encOddParams (encList encRow)) (encPair encOddState (encList encRow))
      (fun p => (encPair encOddParams (encList encRow) p).length)
      (fun p => (encPair encOddParams (encList encRow) p).length) := by
    have hp := ((ComputableInO.fst encOddParams (encList encRow)).prod
      (ComputableInO.const (encIn := encPair encOddParams (encList encRow))
        (encMid := encOption encRow) (none : Option Row))).prod
      (ComputableInO.snd encOddParams (encList encRow))
    refine hp.mono 3 (fun p => ?_) (fun p => ?_)
    all_goals simp only [length_encPair]; omega
  have haux : ComputableInO (fun q : OddState × List Row => passOddsFrom q.1.2 q.1.1 q.2)
      (encPair encOddState (encList encRow)) (encList encRow)
      (fun q => (encOddParams q.1.1).length + (encOption encRow q.1.2).length +
        (encList encRow q.2).length +
        (q.2.length + 1) * (listMax (fun r => (encRow r).length) q.2 +
          (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) ^ d)
      (fun q => (encOddParams q.1.1).length + (encOption encRow q.1.2).length +
        (encList encRow q.2).length +
        (q.2.length + 1) * (listMax (fun r => (encRow r).length) q.2 +
          (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) ^ d) := by
    have hpow_le : ∀ q : OddState × List Row,
        (2 * (encOddParams q.1.1).length + 2 * (encOption encRow q.1.2).length +
            listMax (fun r => (encRow r).length) q.2 + 5) ^ d ≤
          5 ^ d * (listMax (fun r => (encRow r).length) q.2 +
            (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) ^ d := by
      intro q
      have hle : 2 * (encOddParams q.1.1).length + 2 * (encOption encRow q.1.2).length +
          listMax (fun r => (encRow r).length) q.2 + 5 ≤
          5 * (listMax (fun r => (encRow r).length) q.2 +
            (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) := by omega
      calc _ ≤ (5 * (listMax (fun r => (encRow r).length) q.2 +
            (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1)) ^ d :=
              Nat.pow_le_pow_left hle d
        _ = 5 ^ d * _ ^ d := Nat.mul_pow _ _ _
    have hlen_in : ∀ q : OddState × List Row,
        (encPair encOddState (encList encRow) q).length ≤
          4 * ((encOddParams q.1.1).length + (encOption encRow q.1.2).length) +
            (encList encRow q.2).length + 3 := by
      intro q
      simp only [length_encPair]
      omega
    let C₀ := 5 ^ d * (c + 1) + 4 * (c + 1) + 4
    have h5dc : 5 ^ d * c ≤ C₀ := by
      have : 5 ^ d * c ≤ 5 ^ d * (c + 1) := Nat.mul_le_mul_left _ (Nat.le_succ c)
      dsimp [C₀]; omega
    have hmain : ∀ q : OddState × List Row,
        c * ((encPair encOddState (encList encRow) q).length +
          (q.2.length + 1) * (2 * (encOddParams q.1.1).length +
            2 * (encOption encRow q.1.2).length +
            listMax (fun r => (encRow r).length) q.2 + 5) ^ d + 1) ≤
        C₀ * ((encOddParams q.1.1).length + (encOption encRow q.1.2).length +
          (encList encRow q.2).length + (q.2.length + 1) *
          (listMax (fun r => (encRow r).length) q.2 +
            (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) ^ d + 1) :=
      fun q => by
        have hp := hpow_le q
        have hin := hlen_in q
        have hmul : (q.2.length + 1) * (2 * (encOddParams q.1.1).length +
              2 * (encOption encRow q.1.2).length +
              listMax (fun r => (encRow r).length) q.2 + 5) ^ d ≤
            5 ^ d * ((q.2.length + 1) * (listMax (fun r => (encRow r).length) q.2 +
              (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) ^ d) := by
          calc _ ≤ (q.2.length + 1) * (5 ^ d * (listMax (fun r => (encRow r).length) q.2 +
                (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) ^ d) :=
                Nat.mul_le_mul_left _ hp
            _ = _ := by ring
        set A := (encOddParams q.1.1).length + (encOption encRow q.1.2).length +
            (encList encRow q.2).length
        set B := (q.2.length + 1) * (listMax (fun r => (encRow r).length) q.2 +
            (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) ^ d
        have h4c : 4 * c ≤ C₀ := by dsimp [C₀]; omega
        calc c * ((encPair encOddState (encList encRow) q).length +
                (q.2.length + 1) * (2 * (encOddParams q.1.1).length +
                  2 * (encOption encRow q.1.2).length +
                  listMax (fun r => (encRow r).length) q.2 + 5) ^ d + 1)
            ≤ c * (4 * ((encOddParams q.1.1).length + (encOption encRow q.1.2).length) +
                (encList encRow q.2).length + 4 + 5 ^ d * B) := Nat.mul_le_mul_left c (by omega)
          _ ≤ c * (4 * A + 4 + 5 ^ d * B) := Nat.mul_le_mul_left c (by omega)
          _ = (4 * c) * A + (5 ^ d * c) * B + 4 * c := by ring
          _ ≤ C₀ * A + C₀ * B + C₀ * 1 := by
              have h1 := Nat.mul_le_mul_right A h4c
              have h2 := Nat.mul_le_mul_right B h5dc
              omega
          _ = C₀ * (A + B + 1) := by ring
    refine ComputableInO.of_bounds h C₀ (fun q => hmain q) (fun q => ?_)
      (fun q => (h.length_le q).trans (hmain q))
    · have hp := hpow_le q
      have hmul : (2 * (encOddParams q.1.1).length + 2 * (encOption encRow q.1.2).length +
            listMax (fun r => (encRow r).length) q.2 + 5) ^ d ≤
          5 ^ d * ((q.2.length + 1) * (listMax (fun r => (encRow r).length) q.2 +
            (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) ^ d) := by
        have hlen_pos : 1 ≤ q.2.length + 1 := Nat.succ_pos _
        calc _ ≤ 5 ^ d * (listMax (fun r => (encRow r).length) q.2 +
              (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) ^ d := hp
          _ = 1 * (5 ^ d * (listMax (fun r => (encRow r).length) q.2 +
              (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) ^ d) := by ring
          _ ≤ (q.2.length + 1) * (5 ^ d * (listMax (fun r => (encRow r).length) q.2 +
              (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) ^ d) :=
              Nat.mul_le_mul_right _ hlen_pos
          _ = _ := by ring
      set B := (q.2.length + 1) * (listMax (fun r => (encRow r).length) q.2 +
          (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) ^ d
      have hc : c ≤ C₀ := by dsimp [C₀]; omega
      calc c * ((2 * (encOddParams q.1.1).length + 2 * (encOption encRow q.1.2).length +
              listMax (fun r => (encRow r).length) q.2 + 4 + 1) ^ d + 1)
          = c * ((2 * (encOddParams q.1.1).length + 2 * (encOption encRow q.1.2).length +
              listMax (fun r => (encRow r).length) q.2 + 5) ^ d + 1) := by
              simp only [Nat.add_assoc]
        _ ≤ c * (5 ^ d * B + 1) := Nat.mul_le_mul_left c (by omega)
        _ = (5 ^ d * c) * B + c := by ring
        _ ≤ C₀ * B + C₀ * 1 := by
            have h1 := Nat.mul_le_mul_right B h5dc
            omega
        _ ≤ C₀ * ((encOddParams q.1.1).length + (encOption encRow q.1.2).length +
              (encList encRow q.2).length + B + 1) := by
            have hle : B + 1 ≤ (encOddParams q.1.1).length + (encOption encRow q.1.2).length +
                (encList encRow q.2).length + B + 1 := by omega
            calc C₀ * B + C₀ * 1 = C₀ * (B + 1) := by ring
              _ ≤ C₀ * _ := Nat.mul_le_mul_left _ hle
  refine ⟨d, (haux.comp hwrap).mono 4 (fun p => ?_) (fun p => ?_)⟩
  · have hlen_p : (encPair encOddParams (encList encRow) p).length =
        2 * (encOddParams p.1).length + 1 + (encList encRow p.2).length :=
      length_encPair p
    simp only [encOption_none, List.length_nil, add_zero]
    rw [add_comm (listMax (fun r => (encRow r).length) p.2) ((encOddParams p.1).length)]
    omega
  · have hlen_p : (encPair encOddParams (encList encRow) p).length =
        2 * (encOddParams p.1).length + 1 + (encList encRow p.2).length :=
      length_encPair p
    simp only [encOption_none, List.length_nil, add_zero]
    omega

private theorem length_encRow_foldl_last_le (L : List Row) :
    (encRow (L.foldl (fun _ r => r) [])).length ≤ listMax (fun r => (encRow r).length) L := by
  have hmem : ∀ (xs : List Row) (acc : Row),
      xs.foldl (fun _ r => r) acc = acc ∨ xs.foldl (fun _ r => r) acc ∈ xs := by
    intro xs acc
    induction xs generalizing acc with
    | nil => exact Or.inl rfl
    | cons a xs ih =>
      simp only [List.foldl_cons]
      rcases ih a with h | h
      · rw [h]; exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ h)
  rcases hmem L [] with h | h
  · rw [h]; simp
  · exact le_listMax (f := fun r => (encRow r).length) h

private theorem computableInO_lastRow :
    ComputableInO (fun L : List Row => L.foldl (fun _ r => r) [])
      (encList encRow) encRow
      (fun L => (encList encRow L).length + L.length * (listMax (fun r => (encRow r).length) L + 1))
      (fun L => (encList encRow L).length + listMax (fun r => (encRow r).length) L) := by
  obtain ⟨cnext, hnext⟩ := Internal.NormalForm.linear
    (PairEncoding.snd (enc₁ := encRow) (enc₂ := encRow) (enc := encPair encRow encRow))
  obtain ⟨ce, he⟩ := computableInTimeAndSpace_of_const (encIn := encPair encRow encRow)
    (encOut := encUnit) ()
  have hstate_le : ∀ (L : List Row) (j : ℕ),
      (encRow ((L.take j).foldl (fun _ r => r) [])).length ≤
        listMax (fun r => (encRow r).length) L := fun L j =>
    (length_encRow_foldl_last_le (L.take j)).trans
      (listMax_le (fun r hr => le_listMax (f := fun r => (encRow r).length)
        (List.take_subset j L hr)))
  let K := 3 * cnext + 2 * ce + 6
  obtain ⟨c, hc⟩ := ComputableTidilyInTimeAndSpace.streamFold_pair_sum
    (g := fun p : Unit × List Row => p.2.foldl (fun _ r => r) [])
    (encIn := encPair encUnit (encList encRow)) (encOut := encRow)
    (encA := encRow) (encS := encRow) (encE := encUnit) (encF := encRow)
    Internal.NativeCompiler.frameValueReader
    (fun r => frame (encRow r)) (fun r => frame_ne_nil (encRow r))
    (fun r rest => Internal.NativeCompiler.read_frameValueReader (encRow r) rest)
    (fun _ => []) Prod.snd
    (fun p => by cases p.1; rfl)
    hnext he.computableTidilyInTimeAndSpace computableTidilyInTimeAndSpace_id
    (fun p => by
      simp [streamState, encRow])
    (roundCost := fun p _ => K * (listMax (fun r => (encRow r).length) p.2 + 1))
    (sMax := fun p => K * (listMax (fun r => (encRow r).length) p.2 + 1))
    (lMax := fun p => listMax (fun r => (encRow r).length) p.2)
    (fun p j hj => by
      have h0 := hstate_le p.2 j
      have h1 := hstate_le p.2 (j + 1)
      have ha := le_listMax (f := fun r => (encRow r).length) (List.getElem_mem hj)
      have hlen : (encPair encRow encRow (streamState [] Prod.snd p.2 j, p.2[j])).length + 1 ≤
          3 * (listMax (fun r => (encRow r).length) p.2 + 1) := by
        rw [length_encPair]
        simp only [streamState] at h0 ⊢
        omega
      set M := listMax (fun r => (encRow r).length) p.2 + 1
      have hpos : 1 ≤ M := Nat.succ_pos _
      simp only [streamState] at h0 h1 hlen ⊢
      have hce : 2 * ce + 2 + (encRow ((p.2.take j).foldl (fun _ r => r) [])).length +
            (encRow ((p.2.take (j + 1)).foldl (fun _ r => r) [])).length +
            (encRow p.2[j]).length + 1 ≤ (2 * ce + 6) * M := by
        have hM1 : (encRow ((p.2.take j).foldl (fun _ r => r) [])).length ≤ M :=
          h0.trans (Nat.le_succ _)
        have hM2 : (encRow ((p.2.take (j + 1)).foldl (fun _ r => r) [])).length ≤ M :=
          h1.trans (Nat.le_succ _)
        have hM3 : (encRow p.2[j]).length ≤ M := ha.trans (Nat.le_succ _)
        have hm := Nat.mul_le_mul_left (2 * ce + 2) hpos
        have h4M : 2 * ce + 2 + 4 * M ≤ (2 * ce + 6) * M := by
          calc 2 * ce + 2 + 4 * M ≤ (2 * ce + 2) * M + 4 * M := by omega
            _ = (2 * ce + 6) * M := by ring
        omega
      calc cnext * ((encPair encRow encRow (List.foldl (fun _ r => r) [] (p.2.take j),
              p.2[j])).length + 1) +
            (2 * ce + 2) +
            (encRow ((p.2.take j).foldl (fun _ r => r) [])).length +
            (encRow ((p.2.take (j + 1)).foldl (fun _ r => r) [])).length +
            (encRow p.2[j]).length + 1
          ≤ cnext * (3 * M) + (2 * ce + 6) * M := by
              have hcn := Nat.mul_le_mul_left cnext hlen
              omega
        _ = K * M := by dsimp [K]; ring)
    (fun p j hj => by
      have h0 := hstate_le p.2 j
      have ha := le_listMax (f := fun r => (encRow r).length) (List.getElem_mem hj)
      have hlen : (encPair encRow encRow (streamState [] Prod.snd p.2 j, p.2[j])).length + 1 ≤
          3 * (listMax (fun r => (encRow r).length) p.2 + 1) := by
        rw [length_encPair]
        simp only [streamState] at h0 ⊢
        omega
      set M := listMax (fun r => (encRow r).length) p.2 + 1
      calc cnext * ((encPair encRow encRow (streamState [] Prod.snd p.2 j, p.2[j])).length + 1) + 0
          ≤ cnext * (3 * M) := Nat.mul_le_mul_left cnext hlen
        _ = (3 * cnext) * M := by ring
        _ ≤ K * M := Nat.mul_le_mul_right M (by dsimp [K]; omega))
    (fun p j _ => hstate_le p.2 j)
    (fun p j hj => le_listMax (f := fun r => (encRow r).length) (List.getElem_mem hj))
  have hwrap : ComputableInO (fun L : List Row => ((), L))
      (encList encRow) (encPair encUnit (encList encRow))
      (fun L => (encList encRow L).length) (fun L => (encList encRow L).length) := by
    have hp := (ComputableInO.const (encIn := encList encRow) (encMid := encUnit) ()).prod
      (ComputableInO.id' (encMid := encList encRow))
    exact hp.mono 2 (fun _ => by omega) (fun _ => by omega)
  have hpair : ComputableInO (fun p : Unit × List Row => p.2.foldl (fun _ r => r) [])
      (encPair encUnit (encList encRow)) encRow
      (fun p => (encList encRow p.2).length +
        p.2.length * (listMax (fun r => (encRow r).length) p.2 + 1))
      (fun p => listMax (fun r => (encRow r).length) p.2) := by
    refine ComputableInO.of_bounds (ComputableTidilyInTimeAndSpace.computableInTimeAndSpace hc)
      (c * (K + 8) + 1) (fun p => ?_) (fun p => ?_) (fun p => ?_)
    · have hf := hstate_le p.2 p.2.length
      simp only [streamState, List.take_length, Finset.sum_const, Finset.card_range, smul_eq_mul,
        encPair_apply, encUnit_apply, Turing.MultiTapeTM.frame_nil, List.length_append,
        List.length_singleton] at hf ⊢
      have hm : p.2.length * (K * (listMax (fun r => (encRow r).length) p.2 + 1)) =
          K * (p.2.length * (listMax (fun r => (encRow r).length) p.2 + 1)) := by ring
      have hlm : listMax (fun r => (encRow r).length) p.2 ≤
          p.2.length * (listMax (fun r => (encRow r).length) p.2 + 1) := by
        cases p.2 with
        | nil => simp [listMax]
        | cons _ _ => simp only [List.length_cons]; nlinarith only
      set A := (encList encRow p.2).length
      set B := p.2.length * (listMax (fun r => (encRow r).length) p.2 + 1)
      calc c * (2 * (encRow (p.2.foldl (fun x r => r) [])).length + 4 + (1 + A) +
              p.2.length * (K * (listMax (fun r => (encRow r).length) p.2 + 1)) +
              listMax (fun r => (encRow r).length) p.2 + 1)
          = c * (2 * (encRow (p.2.foldl (fun x r => r) [])).length + 6 + A + K * B +
              listMax (fun r => (encRow r).length) p.2) := by rw [hm]; ring
        _ ≤ c * (A + (K + 3) * B + 6) := by
            have hle : 2 * (encRow (p.2.foldl (fun x r => r) [])).length +
                listMax (fun r => (encRow r).length) p.2 ≤ 3 * B := by omega
            have : (K + 3) * B = K * B + 3 * B := by ring
            exact Nat.mul_le_mul_left c (by omega)
        _ ≤ c * ((K + 8) * (A + B + 1)) := by
            have : (K + 8) * (A + B + 1) = (K + 8) * A + (K + 8) * B + (K + 8) := by ring
            have hA : A ≤ (K + 8) * A := Nat.le_mul_of_pos_left A (by omega)
            have hB : (K + 3) * B ≤ (K + 8) * B := Nat.mul_le_mul_right B (by omega)
            exact Nat.mul_le_mul_left c (by omega)
        _ = (c * (K + 8)) * (A + B + 1) := by ring
        _ ≤ (c * (K + 8) + 1) * (A + B + 1) := Nat.mul_le_mul_right _ (by omega)
    · nlinarith only
    · have hf := hstate_le p.2 p.2.length
      simp only [List.take_length] at hf
      calc (encRow (p.2.foldl (fun x r => r) [])).length
          ≤ listMax (fun r => (encRow r).length) p.2 + 1 := hf.trans (Nat.le_succ _)
        _ ≤ (c * (K + 8) + 1) * (listMax (fun r => (encRow r).length) p.2 + 1) :=
            Nat.le_mul_of_pos_left _ (by omega)
  exact (hpair.comp hwrap).mono 2 (fun _ => by dsimp; omega) (fun _ => by dsimp; omega)

/-! ### Full DP iteration and semantic equivalence -/

private def row0 (D : List (List ℕ)) : Row :=
  (List.range D.length).map fun t => some (dist D 0 t)

private def noneRow (len : ℕ) : Row :=
  List.replicate len none

private def doubleStep (p : List Row × List Row) : List Row × List Row :=
  (p.1 ++ p.2, p.2 ++ p.2)

private def initTable (D : List (List ℕ)) : List Row :=
  (doubleStep^[D.length - 1] ([row0 D], [noneRow D.length])).1

private theorem iterate_doubleStep (a b : Row) (k : ℕ) :
    (doubleStep^[k] ([a], [b])).1 = [a] ++ List.replicate (2 ^ k - 1) b ∧
      (doubleStep^[k] ([a], [b])).2 = List.replicate (2 ^ k) b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', doubleStep]
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    refine ⟨?_, ?_⟩
    · have hlen : 2 ^ k - 1 + 2 ^ k = 2 ^ (k + 1) - 1 := by
        rw [Nat.pow_succ, Nat.mul_two]
        omega
      rw [ih.1, ih.2, List.append_assoc, ← List.replicate_add, hlen]
    · rw [ih.2, ← List.replicate_add, Nat.pow_succ, Nat.mul_two]

private theorem interleave_replicate {α : Type*} (m : ℕ) (b : α) :
    interleave (List.replicate m b) (List.replicate m b) = List.replicate (2 * m) b := by
  induction m with
  | zero => simp [interleave]
  | succ m ih =>
    rw [List.replicate_succ, interleave, interleave, ih,
      show 2 * (m + 1) = (2 * m + 1) + 1 by omega, List.replicate_succ, List.replicate_succ]

private theorem tabulateLSB_eq_single_false (a b : Row) (n : ℕ) :
    tabulateLSB n (fun bs => if bs = List.replicate n false then a else b) =
      [a] ++ List.replicate (2 ^ n - 1) b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tabulateLSB]
    have h1 : tabulateLSB n
        (fun bs => if false :: bs = List.replicate (n + 1) false then a else b) =
        [a] ++ List.replicate (2 ^ n - 1) b := by
      simpa [List.replicate_succ] using ih
    have h2 : tabulateLSB n
        (fun bs => if true :: bs = List.replicate (n + 1) false then a else b) =
        List.replicate (2 ^ n) b := by
      have hconst : tabulateLSB n
          (fun bs => if true :: bs = List.replicate (n + 1) false then a else b) =
          tabulateLSB n (fun _ => b) :=
        tabulateLSB_congr fun bs _ => by simp [List.replicate_succ]
      rw [hconst]
      clear h1 hconst ih
      induction n with
      | zero => rfl
      | succ k ihk =>
        rw [tabulateLSB, ihk, interleave_replicate, Nat.pow_succ, Nat.mul_comm]
    rw [h1, h2]
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    obtain ⟨p, hp⟩ : ∃ p, 2 ^ n = p + 1 := ⟨2 ^ n - 1, by omega⟩
    rw [hp, show p + 1 - 1 = p by omega, List.replicate_succ, List.singleton_append, interleave,
      interleave, interleave_replicate, pow_succ, hp, show (p + 1) * 2 = (2 * p + 1) + 1 by omega,
      Nat.add_sub_cancel, List.replicate_succ]
    rfl

private abbrev HKState := (List (List ℕ) × ℕ) × List Row

private abbrev encHKState : HKState ↪ List Bool :=
  encPair (encPair (encList (encList encNat)) encUnary) (encList encRow)

private def hkInit (x : TSPInstance) : HKState :=
  ((x.dist, 0), initTable x.dist)

private def hkStep (st : HKState) : HKState :=
  let D := st.1.1
  let i := st.1.2
  let L := st.2
  let n := D.length - 1
  let iNext := if i + 1 = n then 0 else i + 1
  let row := D.getD (i + 1) []
  let LNext := evens L ++ passOddsFrom none (row, i) L
  ((D, iNext), LNext)

private def tmOptCost (x : TSPInstance) : ℕ :=
  let n := x.dist.length - 1
  let fin := (hkStep^[n * n] (hkInit x)).2
  let last := fin.foldl (fun _ r => r) []
  (last.headD none).getD 0

private def tmDecide (x : TSPInstance) : Bool :=
  match x.dist.length with
  | 0 => true
  | _ + 1 => decide (tmOptCost x ≤ x.bound)

private def maxDist (D : List (List ℕ)) : ℕ :=
  listMax (listMax id) D

private theorem dist_le_maxDist (D : List (List ℕ)) (i j : ℕ) :
    dist D i j ≤ maxDist D := by
  unfold dist maxDist
  simp_rw [List.getD_eq_getElem?_getD]
  rcases h1 : D[i]? with _ | row
  · simp
  · simp only [Option.getD_some]
    rcases h2 : row[j]? with _ | a
    · simp
    · simp only [Option.getD_some]
      exact (le_listMax (f := id) (List.mem_of_getElem? h2)).trans
        (le_listMax (f := listMax id) (List.mem_of_getElem? h1))

private theorem maxDist_lt_two_pow (x : TSPInstance) :
    maxDist x.dist < 2 ^ (encTSP x).length := by
  suffices h : maxDist x.dist ≤ 2 ^ (encTSP x).length - 1 by
    have hpos : 0 < 2 ^ (encTSP x).length := Nat.two_pow_pos _
    omega
  refine listMax_le fun row hrow => listMax_le fun a ha => ?_
  have ha_len : (encNat a).length ≤ (encList encNat row).length :=
    length_le_encList_of_mem encNat ha
  have hr_len : (encList encNat row).length ≤ (encList (encList encNat) x.dist).length :=
    length_le_encList_of_mem (encList encNat) hrow
  have hx_len : (encList (encList encNat) x.dist).length ≤ (encTSP x).length := by
    rw [encTSP_apply]
    enc_len
  have hlt : a < 2 ^ (encNat a).length := by
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact Nat.lt_size_self a
  exact Nat.le_sub_one_of_lt
    (hlt.trans_le (Nat.pow_le_pow_right (by decide) (ha_len.trans (hr_len.trans hx_len))))

private theorem walkCost_le_mul_maxDist (D : List (List ℕ)) {n : ℕ}
    (a : Fin (n + 1)) (L : List (Fin (n + 1))) (b : Fin (n + 1)) :
    walkCost (fun i j : Fin (n + 1) => dist D i j) a L b ≤ (L.length + 1) * maxDist D := by
  induction L generalizing a with
  | nil => simpa [walkCost] using dist_le_maxDist D a b
  | cons x L ih =>
    simp only [walkCost, List.length_cons]
    have hx := dist_le_maxDist D a x
    have hL := ih x
    nlinarith only [hx, hL]

private def ValidFun (D : List (List ℕ)) (n : ℕ) (G : Finset (Fin n) → Row) : Prop :=
  ∀ S : Finset (Fin n), (G S).length = n + 1 ∧
    ∀ t : Fin (n + 1), ∀ v, (G S).getD t.val none = some v →
      v ∈ walkCosts (fun i j : Fin (n + 1) => dist D i j) S t

private def StageComplete (D : List (List ℕ)) (n r : ℕ) (G : Finset (Fin n) → Row) : Prop :=
  ValidFun D n G ∧ ∀ S : Finset (Fin n), S.card ≤ r → ∀ t : Fin (n + 1),
    ∃ v, (G S).getD t.val none = some v ∧
      IsLeast (walkCosts (fun i j : Fin (n + 1) => dist D i j) S t) v

private theorem validFun_pass {D : List (List ℕ)} {n i : ℕ} (hi : i < n)
    {G : Finset (Fin n) → Row} (hG : ValidFun D n G) :
    let G' : Finset (Fin n) → Row := fun S =>
      if ⟨i, hi⟩ ∈ S then
        relaxRow (D.getD (i + 1) []) ((G (S.erase ⟨i, hi⟩)).getD (i + 1) none) (G S)
      else G S
    ValidFun D n G' ∧
      (∀ S : Finset (Fin n), ∀ t : ℕ, ∀ u, (G S).getD t none = some u →
        ∃ v, (G' S).getD t none = some v ∧ v ≤ u) ∧
      (∀ S : Finset (Fin n), ⟨i, hi⟩ ∈ S → ∀ t : Fin (n + 1), ∀ u,
        (G (S.erase ⟨i, hi⟩)).getD (i + 1) none = some u →
        ∃ v, (G' S).getD t.val none = some v ∧ v ≤ u + dist D (i + 1) t.val) := by
  intro G'
  refine ⟨fun S => ?_, fun S t u hu => ?_, fun S hmem t u hu => ?_⟩
  · by_cases hmem : (⟨i, hi⟩ : Fin n) ∈ S
    · simp only [G', hmem, ↓reduceIte]
      have hlenS := (hG S).1
      refine ⟨(length_relaxRow _ _ _).trans hlenS, fun t v hv => ?_⟩
      rw [getD_relaxRow _ _ _ (by rw [hlenS]; exact t.isLt)] at hv
      cases hu : (G (S.erase ⟨i, hi⟩)).getD (i + 1) none with
      | none =>
        rw [hu] at hv
        exact (hG S).2 t v hv
      | some u =>
        rw [hu] at hv
        obtain ⟨L', hnd', hL', hu_eq⟩ := (hG (S.erase ⟨i, hi⟩)).2 ⟨i + 1, by omega⟩ u hu
        have hcand_mem :
            u + (D.getD (i + 1) []).getD t.val 0 ∈
              walkCosts (fun i j : Fin (n + 1) => dist D i j) S t := by
          refine ⟨L' ++ [⟨i, hi⟩], ?_, ?_, ?_⟩
          · refine List.nodup_append.2 ⟨hnd', List.nodup_singleton _, fun x hx y hy he => ?_⟩
            rw [List.mem_singleton] at hy
            subst hy he
            have hxS : ⟨i, hi⟩ ∈ S.erase ⟨i, hi⟩ := hL' ▸ (List.mem_toFinset.2 hx)
            exact (Finset.notMem_erase _ S) hxS
          · rw [List.toFinset_append, hL', List.toFinset_cons, List.toFinset_nil, Finset.union_comm,
              Finset.insert_union, Finset.empty_union, Finset.insert_erase hmem]
          · simp only [List.map_append, List.map_cons, List.map_nil, walkCost_append_singleton,
              Fin.val_succ, dist]
            exact congrArg (· + (D.getD (i + 1) []).getD t.val 0) hu_eq
        cases hcur : (G S).getD t.val none with
        | none =>
          rw [hcur] at hv
          unfold optMin at hv
          obtain rfl := Option.some.inj hv
          exact hcand_mem
        | some cur =>
          rw [hcur] at hv
          unfold optMin at hv
          obtain rfl := Option.some.inj hv
          rcases min_cases cur (u + (D.getD (i + 1) []).getD t.val 0) with ⟨he, -⟩ | ⟨he, -⟩
          · rw [he]
            exact (hG S).2 t cur hcur
          · rw [he]
            exact hcand_mem
    · simp only [G', hmem, ↓reduceIte]
      exact hG S
  · by_cases hmem : (⟨i, hi⟩ : Fin n) ∈ S
    · simp only [G', hmem, ↓reduceIte]
      by_cases ht : t < (G S).length
      · rw [getD_relaxRow _ _ _ ht, hu]
        cases hprev : (G (S.erase ⟨i, hi⟩)).getD (i + 1) none with
        | none => exact ⟨u, rfl, le_rfl⟩
        | some b =>
          simp only [optMin]
          exact ⟨min u (b + (D.getD (i + 1) []).getD t 0), rfl, min_le_left _ _⟩
      · have hlen := (hG S).1
        rw [List.getD_eq_default _ _ (by omega)] at hu
        cases hu
    · simp only [G', hmem, ↓reduceIte]
      exact ⟨u, hu, le_rfl⟩
  · simp only [G', hmem, ↓reduceIte]
    rw [getD_relaxRow _ _ _ (by rw [(hG S).1]; exact t.isLt), hu]
    cases hcur : (G S).getD t.val none with
    | none => exact ⟨u + dist D (i + 1) t.val, rfl, le_rfl⟩
    | some c => exact ⟨min c (u + dist D (i + 1) t.val), rfl, min_le_right _ _⟩

private theorem stage_correct {D : List (List ℕ)} {n : ℕ} (hn : 0 < n) (r : ℕ)
    (G₀ : Finset (Fin n) → Row) (hG₀ : StageComplete D n r G₀) :
    let step : ℕ × List Row → ℕ × List Row := fun q =>
      (q.1 + 1, passStep (fun r₀ r₁ => relaxRow (D.getD (q.1 + 1) []) (r₀.getD (q.1 + 1) none) r₁)
        q.2)
    ∀ i ≤ n, ∃ G : Finset (Fin n) → Row,
      (step^[i] (0, tabulateLSB n fun bs => G₀ (setOfBits n bs))).1 = i ∧
      (step^[i] (0, tabulateLSB n fun bs => G₀ (setOfBits n bs))).2 =
        tabulateLSB n (fun bs => G (setOfBits n (bs.rotate (n - i)))) ∧
      ValidFun D n G ∧
      (∀ S : Finset (Fin n), ∀ t : ℕ, ∀ u, (G₀ S).getD t none = some u →
        ∃ v, (G S).getD t none = some v ∧ v ≤ u) ∧
      (∀ j < i, ∀ (hj : j < n), ∀ S : Finset (Fin n), ⟨j, hj⟩ ∈ S →
        (S.erase ⟨j, hj⟩).card ≤ r → ∀ t : Fin (n + 1),
          ∃ v, (G S).getD t.val none = some v ∧
            ∀ u, (G₀ (S.erase ⟨j, hj⟩)).getD (j + 1) none = some u →
              v ≤ u + dist D (j + 1) t.val) := by
  intro step i hi
  induction i with
  | zero =>
    refine ⟨G₀, rfl, ?_, hG₀.1, fun S t u hu => ⟨u, hu, le_rfl⟩, fun j hj => absurd hj (by omega)⟩
    refine tabulateLSB_congr fun bs hbs => ?_
    rw [Nat.sub_zero, show bs.rotate n = bs from by rw [← hbs, List.rotate_length]]
  | succ i ih =>
    obtain ⟨G, hfst, hsnd, hVG, hmono, hdone⟩ := ih (by omega)
    have hit : (step^[i + 1] (0, tabulateLSB n fun bs => G₀ (setOfBits n bs))) =
        (i + 1, passStep (fun r₀ r₁ => relaxRow (D.getD (i + 1) []) (r₀.getD (i + 1) none) r₁)
          (tabulateLSB n fun bs => G (setOfBits n (bs.rotate (n - i))))) := by
      rw [Function.iterate_succ_apply']
      dsimp only [step]
      rw [hfst, hsnd]
    let G' : Finset (Fin n) → Row := fun S =>
      if ⟨i, hi⟩ ∈ S then
        relaxRow (D.getD (i + 1) []) ((G (S.erase ⟨i, hi⟩)).getD (i + 1) none) (G S)
      else G S
    obtain ⟨hVG', hstep_mono, hstep_relax⟩ := validFun_pass hi hVG
    have hpass_eq : passStep (fun r₀ r₁ => relaxRow (D.getD (i + 1) []) (r₀.getD (i + 1) none) r₁)
        (tabulateLSB n fun bs => G (setOfBits n (bs.rotate (n - i)))) =
        tabulateLSB n fun bs => G' (setOfBits n (bs.rotate (n - (i + 1)))) :=
      passStep_tabulateLSB_rotate hn hi _ G
    refine ⟨G', by rw [hit], by rw [hit, hpass_eq], hVG',
      fun S t u hu => ?_, fun j hj hjn S hS hcard t => ?_⟩
    · obtain ⟨v₁, hv₁, hle₁⟩ := hmono S t u hu
      obtain ⟨v₂, hv₂, hle₂⟩ := hstep_mono S t v₁ hv₁
      exact ⟨v₂, hv₂, hle₂.trans hle₁⟩
    · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hj) with hjlt | rfl
      · obtain ⟨v₁, hv₁, hle₁⟩ := hdone j hjlt hjn S hS hcard t
        obtain ⟨v₂, hv₂, hle₂⟩ := hstep_mono S t.val v₁ hv₁
        exact ⟨v₂, hv₂, fun u hu => (hle₂).trans (hle₁ u hu)⟩
      · obtain ⟨u₀, hu₀, -⟩ := hG₀.2 (S.erase ⟨j, hjn⟩) hcard ⟨j + 1, by omega⟩
        obtain ⟨u₁, hu₁, hle₁⟩ := hmono (S.erase ⟨j, hjn⟩) (j + 1) u₀ hu₀
        obtain ⟨v₂, hv₂, hle₂⟩ := hstep_relax S hS t u₁ hu₁
        refine ⟨v₂, hv₂, fun u hu => ?_⟩
        rw [Fin.val_mk] at hu₀
        rw [hu₀] at hu
        obtain rfl := Option.some.inj hu
        exact hle₂.trans (Nat.add_le_add_right hle₁ _)

private theorem stage_complete_succ {D : List (List ℕ)} {n r : ℕ} (_hn : 0 < n)
    (G₀ : Finset (Fin n) → Row) (hG₀ : StageComplete D n r G₀)
    (G_end : Finset (Fin n) → Row) (hVG : ValidFun D n G_end)
    (hmono : ∀ S : Finset (Fin n), ∀ t : ℕ, ∀ u, (G₀ S).getD t none = some u →
      ∃ v, (G_end S).getD t none = some v ∧ v ≤ u)
    (hdone : ∀ j < n, ∀ (hj : j < n), ∀ S : Finset (Fin n), ⟨j, hj⟩ ∈ S →
      (S.erase ⟨j, hj⟩).card ≤ r → ∀ t : Fin (n + 1),
        ∃ v, (G_end S).getD t.val none = some v ∧
          ∀ u, (G₀ (S.erase ⟨j, hj⟩)).getD (j + 1) none = some u → v ≤ u + dist D (j + 1) t.val) :
    StageComplete D n (r + 1) G_end := by
  refine ⟨hVG, fun S hS t => ?_⟩
  rcases Nat.lt_or_eq_of_le hS with hlt | heq
  · obtain ⟨u, hu, hu_least⟩ := hG₀.2 S (Nat.lt_succ_iff.1 hlt) t
    obtain ⟨v, hv, hvu⟩ := hmono S t.val u hu
    refine ⟨v, hv, (hVG S).2 t v hv, fun w hw => (hvu.trans (hu_least.2 hw))⟩
  · have hpos : 0 < S.card := by omega
    obtain ⟨a₀, ha₀⟩ := Finset.card_pos.1 hpos
    have hcard_er : (S.erase a₀).card ≤ r := by
      rw [Finset.card_erase_of_mem ha₀, heq]
      simp
    obtain ⟨v, hv, hle_v⟩ := hdone a₀.val a₀.isLt a₀.isLt S ha₀ hcard_er t
    refine ⟨v, hv, (hVG S).2 t v hv, fun w hw => ?_⟩
    obtain ⟨L, hLnd, hLset, rfl⟩ := hw
    have hLne : L ≠ [] := by
      intro hnil
      subst hnil
      simp only [List.toFinset_nil] at hLset
      rw [← hLset] at hpos
      simp at hpos
    let L' := L.dropLast
    let j := L.getLast hLne
    have hLsplit : L = L' ++ [j] := (List.dropLast_append_getLast hLne).symm
    have hnd_split : (L' ++ [j]).Nodup := hLsplit ▸ hLnd
    have hj_mem : j ∈ S := by
      rw [← hLset, List.mem_toFinset]
      exact List.getLast_mem hLne
    have hnd' : L'.Nodup := (List.nodup_append.1 hnd_split).1
    have hj_nmem : j ∉ L' := fun h =>
      (List.nodup_append.1 hnd_split).2.2 j h j List.mem_cons_self rfl
    have hL'_set : L'.toFinset = S.erase j := by
      ext z
      simp only [← hLset, hLsplit, List.mem_toFinset, List.mem_append, List.mem_singleton,
        Finset.mem_erase]
      constructor
      · intro hz
        exact ⟨fun hzeq => hj_nmem (hzeq ▸ hz), Or.inl hz⟩
      · rintro ⟨hne, hz | rfl⟩
        · exact hz
        · exact absurd rfl hne
    have hcard_er' : (S.erase j).card ≤ r := by
      rw [Finset.card_erase_of_mem hj_mem, heq]
      simp
    obtain ⟨u, hu, hu_least⟩ := hG₀.2 (S.erase j) hcard_er' j.succ
    obtain ⟨v', hv', hle_v'⟩ := hdone j.val j.isLt j.isLt S hj_mem hcard_er' t
    rw [hv] at hv'
    obtain rfl := Option.some.inj hv'
    have hu_le : u ≤ walkCost (fun a b : Fin (n + 1) => dist D a b) 0 (L'.map Fin.succ) j.succ :=
      hu_least.2 ⟨L', hnd', hL'_set, rfl⟩
    have hwc : walkCost (fun a b : Fin (n + 1) => dist D a b) 0 (L.map Fin.succ) t =
        walkCost (fun a b : Fin (n + 1) => dist D a b) 0 (L'.map Fin.succ) j.succ +
          dist D (j.val + 1) t.val := by
      conv_lhs => rw [hLsplit]
      simp [List.map_append, walkCost_append_singleton]
    rw [hwc]
    exact (hle_v' u hu).trans (Nat.add_le_add_right hu_le _)

private theorem hkStep_invariant (x : TSPInstance) {n : ℕ} (hn_eq : x.dist.length = n + 1) :
    (∃ G_end : Finset (Fin n) → Row,
      (hkStep^[n * n] (hkInit x)).2 = tabulateLSB n (fun bs => G_end (setOfBits n bs)) ∧
      StageComplete x.dist n n G_end) ∧
    (∀ k ≤ n * n, ∃ G : Finset (Fin n) → Row,
      (hkStep^[k] (hkInit x)).1 = (x.dist, k % n) ∧
      (hkStep^[k] (hkInit x)).2 =
        tabulateLSB n (fun bs => G (setOfBits n (bs.rotate (n - k % n)))) ∧
      ValidFun x.dist n G) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · let G₀ : Finset (Fin 0) → Row := fun _ => row0 x.dist
    have hV0 : ValidFun x.dist 0 G₀ := fun S => ⟨by simp [G₀, row0, hn_eq], fun t v hv => by
      simp only [G₀, row0, hn_eq, List.range_succ, List.range_zero, List.nil_append,
        List.map_cons, List.map_nil] at hv
      have ht0 : t = 0 := Fin.ext (by omega)
      subst ht0
      simp only [Fin.val_zero, List.getD_cons_zero] at hv
      obtain rfl := Option.some.inj hv
      exact ⟨[], List.nodup_nil, by ext i; exact i.elim0, rfl⟩⟩
    have hS0 : StageComplete x.dist 0 0 G₀ := ⟨hV0, fun S _ t => by
      have hS : S = ∅ := by ext i; exact i.elim0
      subst hS
      have ht0 : t = 0 := Fin.ext (by omega)
      subst ht0
      exact ⟨dist x.dist 0 0, by simp [G₀, row0, hn_eq], isLeast_walkCosts_empty _ _⟩⟩
    refine ⟨⟨G₀, by simp [hkInit, initTable, row0, tabulateLSB, G₀, hn_eq], hS0⟩, fun k hk => ?_⟩
    obtain rfl : k = 0 := by omega
    exact ⟨G₀, rfl, by simp [hkInit, initTable, row0, tabulateLSB, G₀, hn_eq], hV0⟩
  · let G₀ : Finset (Fin n) → Row := fun S =>
      if S = ∅ then row0 x.dist else noneRow (n + 1)
    have hStage0 : StageComplete x.dist n 0 G₀ := by
      refine ⟨fun S => ⟨?_, fun t v hv => ?_⟩, fun S hS t => ?_⟩
      · by_cases hS : S = ∅ <;> simp [G₀, hS, row0, noneRow, hn_eq]
      · by_cases hS : S = ∅
        · subst hS
          have ht_lt : t.val < x.dist.length := by rw [hn_eq]; exact t.isLt
          simp only [G₀, ↓reduceIte, row0, List.getD_eq_getElem?_getD,
            List.getElem?_map, List.getElem?_range ht_lt, Option.map_some, Option.getD_some] at hv
          obtain rfl := Option.some.inj hv
          exact ⟨[], List.nodup_nil, rfl, rfl⟩
        · simp only [G₀, hS, ↓reduceIte, noneRow] at hv
          rw [List.getD_eq_getElem _ _ (by simp [t.isLt]), List.getElem_replicate] at hv
          cases hv
      · have hS' : S = ∅ := Finset.card_eq_zero.1 (by omega)
        subst hS'
        have ht_lt : t.val < x.dist.length := by rw [hn_eq]; exact t.isLt
        refine ⟨dist x.dist 0 t.val, ?_, isLeast_walkCosts_empty _ t⟩
        simp only [G₀, ↓reduceIte, row0, List.getD_eq_getElem?_getD,
          List.getElem?_map, List.getElem?_range ht_lt, Option.map_some, Option.getD_some]
    have hinit : hkInit x = ((x.dist, 0), tabulateLSB n fun bs => G₀ (setOfBits n bs)) := by
      rw [hkInit, initTable, hn_eq, Nat.succ_sub_one, (iterate_doubleStep _ _ n).1]
      have hcongr : tabulateLSB n (fun bs => G₀ (setOfBits n bs)) =
          tabulateLSB n (fun bs =>
            if bs = List.replicate n false then row0 x.dist else noneRow (n + 1)) := by
        refine tabulateLSB_congr fun bs hbs => ?_
        have hiff : setOfBits n bs = ∅ ↔ bs = List.replicate n false := by
          constructor
          · intro h
            refine List.ext_getElem (by simp [hbs]) fun j hj₁ hj₂ => ?_
            rw [List.getElem_replicate]
            have hnot : (⟨j, hj₁.trans_eq hbs⟩ : Fin n) ∉ setOfBits n bs := by rw [h]; simp
            simp only [setOfBits, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
            rw [List.getD_eq_getElem _ _ hj₁] at hnot
            cases hb : bs[j]
            · rfl
            · exact absurd hb hnot
          · rintro rfl
            exact setOfBits_replicate_false n
        simp [G₀, hiff]
      rw [hcongr, tabulateLSB_eq_single_false]
    let step1 : ℕ × List Row → ℕ × List Row := fun q =>
      (q.1 + 1, passStep (fun r₀ r₁ =>
        relaxRow (x.dist.getD (q.1 + 1) []) (r₀.getD (q.1 + 1) none) r₁) q.2)
    have hsync : ∀ (r : ℕ) (G_r : Finset (Fin n) → Row),
        (hkStep^[r * n] (hkInit x)).1 = (x.dist, 0) →
        (hkStep^[r * n] (hkInit x)).2 = tabulateLSB n (fun bs => G_r (setOfBits n bs)) →
        StageComplete x.dist n r G_r →
        ∀ i ≤ n,
          (hkStep^[r * n + i] (hkInit x)).1 = (x.dist, if i = n then 0 else i) ∧
          (hkStep^[r * n + i] (hkInit x)).2 =
            (step1^[i] (0, tabulateLSB n fun bs => G_r (setOfBits n bs))).2 := by
      intro r G_r h1 h2 hSr i hi
      induction i with
      | zero => simp [h1, h2]
      | succ i ihi =>
        obtain ⟨hs1, hs2⟩ := ihi (by omega)
        have hi_ne : i ≠ n := by omega
        simp only [hi_ne, ↓reduceIte] at hs1
        have hstep_i : (step1^[i] (0, tabulateLSB n fun bs => G_r (setOfBits n bs))).1 = i := by
          obtain ⟨_, hfst, -⟩ := stage_correct hn_pos r G_r hSr i (by omega)
          exact hfst
        rw [← Nat.add_assoc, Function.iterate_succ_apply', Function.iterate_succ_apply' step1,
          hkStep]
        simp only [hs1, hs2, hn_eq, Nat.succ_sub_one]
        refine ⟨by simp, ?_⟩
        dsimp only [step1]
        rw [hstep_i, passStep]
        exact congrArg _ (passOddsFrom_none_eq _ _)
    have hstage : ∀ r ≤ n, ∃ G_r : Finset (Fin n) → Row,
        (hkStep^[r * n] (hkInit x)).1 = (x.dist, 0) ∧
        (hkStep^[r * n] (hkInit x)).2 = tabulateLSB n (fun bs => G_r (setOfBits n bs)) ∧
        StageComplete x.dist n r G_r := by
      intro r hr
      induction r with
      | zero =>
        exact ⟨G₀, by rw [Nat.zero_mul]; exact congrArg Prod.fst hinit,
          by rw [Nat.zero_mul]; exact congrArg Prod.snd hinit, hStage0⟩
      | succ r ih =>
        obtain ⟨G_r, h1, h2, hSr⟩ := ih (by omega)
        obtain ⟨G_end, hfst, hsnd, hVG, hmono, hdone⟩ := stage_correct hn_pos r G_r hSr n le_rfl
        have hSr1 : StageComplete x.dist n (r + 1) G_end :=
          stage_complete_succ hn_pos G_r hSr G_end hVG hmono hdone
        obtain ⟨hs1, hs2⟩ := hsync r G_r h1 h2 hSr n le_rfl
        simp only [↓reduceIte] at hs1
        have heq_mul : (r + 1) * n = r * n + n := by ring
        rw [heq_mul, hs1, hs2, hsnd]
        have hrot0 : (fun bs : List Bool => G_end (setOfBits n (bs.rotate (n - n)))) =
            fun bs => G_end (setOfBits n bs) := by
          funext bs
          simp
        exact ⟨G_end, rfl, by rw [hrot0], hSr1⟩
    refine ⟨?_, fun k hk => ?_⟩
    · obtain ⟨G_end, -, h2, hSn⟩ := hstage n le_rfl
      exact ⟨G_end, h2, hSn⟩
    · let r := k / n
      let i := k % n
      have hdiv_mod : r * n + i = k := by rw [mul_comm]; exact Nat.div_add_mod k n
      have hi_lt : i < n := Nat.mod_lt k hn_pos
      have hr_le : r ≤ n := by
        have : r * n ≤ n * n := (Nat.le_add_right _ i).trans (hdiv_mod.symm ▸ hk)
        exact Nat.le_of_mul_le_mul_right this hn_pos
      obtain ⟨G_r, h1, h2, hSr⟩ := hstage r hr_le
      obtain ⟨G, -, hsnd, hVG, -⟩ := stage_correct hn_pos r G_r hSr i hi_lt.le
      obtain ⟨hs1, hs2⟩ := hsync r G_r h1 h2 hSr i hi_lt.le
      have hi_ne : i ≠ n := hi_lt.ne
      simp only [hi_ne, ↓reduceIte] at hs1
      have hmod_eq : (r * n + i) % n = i := by
        rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hi_lt]
      rw [← hdiv_mod, hmod_eq]
      exact ⟨G, hs1, by rw [hs2, hsnd], hVG⟩

private theorem tmOptCost_eq_heldKarp (x : TSPInstance) {n : ℕ} (hn : x.dist.length = n + 1) :
    tmOptCost x = heldKarp (fun i j : Fin (n + 1) => dist x.dist i j) := by
  dsimp only [tmOptCost]
  rw [hn, Nat.succ_sub_one]
  obtain ⟨⟨G, h2, hSn⟩, -⟩ := hkStep_invariant x hn
  have hfold : (hkStep^[n * n] (hkInit x)).2.foldl (fun _ r => r) [] =
      G (setOfBits n (List.replicate n true)) := by
    rw [h2, foldl_last_tabulateLSB]
  rw [hfold, setOfBits_replicate_true]
  obtain ⟨v, hv, hv_least⟩ := hSn.2 Finset.univ (by rw [Finset.card_univ, Fintype.card_fin]) 0
  have hhead : ((G Finset.univ).headD none).getD 0 = v := by
    rw [List.headD_eq_head?_getD]
    have h0 := hv
    rw [Fin.val_zero, List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?] at h0
    rw [h0]
    rfl
  rw [hhead]
  exact hv_least.unique (isLeast_heldKarp _)

private theorem tmDecide_eq_heldKarpDecide (x : TSPInstance) :
    tmDecide x = heldKarpDecide x := by
  unfold tmDecide heldKarpDecide
  cases h : x.dist.length with
  | zero => rfl
  | succ n =>
    simp only [tmOptCost_eq_heldKarp x h]

private theorem mod_le_encTSP_length {x : TSPInstance} {n k : ℕ} (hx : x.dist.length = n + 1)
    (hk : k ≤ n * n) : k % n ≤ (encTSP x).length := by
  have hdist_le : (encList (encList encNat) x.dist).length ≤ (encTSP x).length := by
    rw [encTSP_apply]; enc_len
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · have : k = 0 := by omega
    subst this
    simp
  · have hn_le : n + 1 ≤ (encTSP x).length := by
      rw [← hx]
      exact (length_le_length_encList (encList encNat) x.dist).trans hdist_le
    have := Nat.mod_lt k hn_pos
    omega

private theorem hkState_size_bound (x : TSPInstance) {n : ℕ} (hn : x.dist.length = n + 1)
    {k : ℕ} (hk : k ≤ n * n) :
    let st := hkStep^[k] (hkInit x)
    st.1 = (x.dist, k % n) ∧
      st.2.length = 2 ^ n ∧
      (∀ r ∈ st.2, (encRow r).length ≤ 4 * ((encTSP x).length + 1) ^ 2) ∧
      (encList encRow st.2).length ≤ 2 ^ n * (8 * ((encTSP x).length + 1) ^ 2 + 2) + 1 ∧
      (encHKState st).length ≤ 2 ^ n * (8 * ((encTSP x).length + 1) ^ 2 + 2) +
        6 * ((encTSP x).length + 1) := by
  intro st
  obtain ⟨-, hstep_inv⟩ := hkStep_invariant x hn
  obtain ⟨G, h1, h2, hVG⟩ := hstep_inv k hk
  have hlen_st2 : st.2.length = 2 ^ n := by
    dsimp [st]
    rw [h2, length_tabulateLSB]
  have hmem_row : ∀ r ∈ st.2, ∃ S : Finset (Fin n), r = G S := by
    intro r hr
    dsimp [st] at hr
    rw [h2] at hr
    clear h1 h2 hlen_st2 hk
    have htab : ∀ (m : ℕ) (f : List Bool → Row) (a : Row),
        a ∈ tabulateLSB m f → ∃ bs, a = f bs := by
      intro m f a ha
      induction m generalizing f with
      | zero =>
        simp only [tabulateLSB, List.mem_singleton] at ha
        exact ⟨[], ha⟩
      | succ m ih =>
        have hinter : ∀ (k : ℕ) (xs ys : List Row) (z : Row),
            xs.length + ys.length ≤ k → z ∈ interleave xs ys → z ∈ xs ∨ z ∈ ys := by
          intro k
          induction k with
          | zero =>
            intro xs ys z hk hz
            cases xs with
            | nil => rw [interleave] at hz; exact Or.inr hz
            | cons _ _ => simp at hk
          | succ k ihi =>
            intro xs ys z hk hz
            cases xs with
            | nil => rw [interleave] at hz; exact Or.inr hz
            | cons x xs =>
              rw [interleave] at hz
              rcases List.mem_cons.1 hz with rfl | hz
              · exact Or.inl List.mem_cons_self
              · rcases ihi ys xs z (by simp at hk; omega) hz with h | h
                · exact Or.inr h
                · exact Or.inl (List.mem_cons_of_mem _ h)
        rcases hinter _ _ _ a le_rfl ha with h | h
        · obtain ⟨bs, hbs⟩ := ih _ h
          exact ⟨false :: bs, hbs⟩
        · obtain ⟨bs, hbs⟩ := ih _ h
          exact ⟨true :: bs, hbs⟩
    obtain ⟨bs, rfl⟩ := htab n _ r hr
    exact ⟨_, rfl⟩
  have hrow_len : ∀ r ∈ st.2, (encRow r).length ≤ 4 * ((encTSP x).length + 1) ^ 2 := by
    intro r hr
    obtain ⟨S, rfl⟩ := hmem_row r hr
    obtain ⟨hGS_len, hGS_val⟩ := hVG S
    have hn_le_L : n + 1 ≤ (encTSP x).length := by
      rw [← hn]
      refine (length_le_length_encList (encList encNat) x.dist).trans ?_
      rw [encTSP_apply]
      enc_len
    have hmax_lt : maxDist x.dist < 2 ^ (encTSP x).length := maxDist_lt_two_pow x
    have hL_lt : n + 1 < 2 ^ (encTSP x).length := hn_le_L.trans_lt Nat.lt_two_pow_self
    have hopt_le : ∀ o ∈ G S, (encOption encNat o).length ≤ 2 * (encTSP x).length + 1 := by
      intro o ho
      cases o with
      | none => simp
      | some v =>
        obtain ⟨j, hj, hj_eq⟩ := List.mem_iff_getElem.1 ho
        have hv : (G S).getD j none = some v := by
          rw [List.getD_eq_getElem _ _ hj, hj_eq]
        obtain ⟨L, hLnd, hLset, rfl⟩ := hGS_val ⟨j, hGS_len ▸ hj⟩ v hv
        have hL_len : L.length ≤ n := by
          have := List.toFinset_card_of_nodup hLnd
          rw [hLset] at this
          calc L.length = S.card := this.symm
            _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
            _ = n := Fintype.card_fin n
        have hwc := walkCost_le_mul_maxDist x.dist (0 : Fin (n + 1)) (L.map Fin.succ)
          ⟨j, hGS_len ▸ hj⟩
        simp only [List.length_map] at hwc
        have hlt2 : walkCost (fun a b : Fin (n + 1) => dist x.dist a b) 0 (L.map Fin.succ)
            ⟨j, hGS_len ▸ hj⟩ < 2 ^ (2 * (encTSP x).length) := by
          calc _ ≤ (L.length + 1) * maxDist x.dist := hwc
            _ ≤ (n + 1) * maxDist x.dist := Nat.mul_le_mul_right _ (by omega)
            _ < 2 ^ (encTSP x).length * 2 ^ (encTSP x).length :=
              Nat.mul_lt_mul_of_lt_of_lt hL_lt hmax_lt
            _ = 2 ^ (2 * (encTSP x).length) := by rw [← pow_add, two_mul]
        have hnat := length_encNat_le_of_lt_two_pow hlt2
        simp only [encOption_some, List.length_cons]
        omega
    calc (encRow (G S)).length
        ≤ (G S).length * (2 * (2 * (encTSP x).length + 1) + 1) :=
          length_encList_le (encOption encNat) (G S) hopt_le
      _ = (n + 1) * (4 * (encTSP x).length + 3) := by rw [hGS_len]; ring
      _ ≤ (encTSP x).length * (4 * (encTSP x).length + 3) := Nat.mul_le_mul_right _ hn_le_L
      _ ≤ 4 * ((encTSP x).length + 1) ^ 2 := by nlinarith only
  have htab_len : (encList encRow st.2).length ≤
      2 ^ n * (8 * ((encTSP x).length + 1) ^ 2 + 2) + 1 := by
    have hsum := length_encList_le encRow st.2 hrow_len
    rw [hlen_st2] at hsum
    exact hsum.trans (by nlinarith only [Nat.one_le_two_pow (n := n)])
  refine ⟨h1, hlen_st2, hrow_len, htab_len, ?_⟩
  have h1' : st.1 = (x.dist, k % n) := h1
  have hdist_le : (encList (encList encNat) x.dist).length ≤ (encTSP x).length := by
    rw [encTSP_apply]; enc_len
  have hmod_le := mod_le_encTSP_length hn hk
  rw [show encHKState st = encPair (encPair (encList (encList encNat)) encUnary)
    (encList encRow) (st.1, st.2) from rfl, length_encPair, h1', length_encPair,
    encUnary_apply, List.length_replicate]
  dsimp only
  omega

private theorem computableInO_hkInit :
    ∃ d, ComputableInO hkInit encTSP encHKState
      (fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ d)
      (fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ d) := by
  have hdist : ComputableInPolyTime TSPInstance.dist encTSP (encList (encList encNat)) := by
    fun_prop
  have hrow0 : ComputableInPolyTime (fun x : TSPInstance => [row0 x.dist])
      encTSP (encList encRow) := by
    have hr : ComputableInPolyTime row0 (encList (encList encNat)) encRow := by
      unfold row0
      refine mapWithInput (range.comp (length_list _)) ?_
      have h0 : ComputableInPolyTime (fun p : List (List ℕ) × ℕ => (p.1.getD 0 []).getD p.2 0)
          (encPair (encList (encList encNat)) encUnary) encNat := by fun_prop
      exact (optionSome _).comp h0
    exact (hr.comp hdist).cons' (const [])
  have hnone : ComputableInPolyTime (fun x : TSPInstance => [noneRow x.dist.length])
      encTSP (encList encRow) := by
    have hnr : ComputableInPolyTime noneRow encUnary encRow := by
      unfold noneRow
      fun_prop
    exact (hnr.comp ((length_list _).comp hdist)).cons' (const [])
  have hinitP : ComputableInPolyTime
      (fun x : TSPInstance => ([row0 x.dist], [noneRow x.dist.length]))
      encTSP (encPair (encList encRow) (encList encRow)) := hrow0.prod hnone
  obtain ⟨Ti, Si, hTi, hSi, hi⟩ := hinitP.exists_computableInO
  have hn_poly : ComputableInPolyTime (fun x : TSPInstance => x.dist.length - 1) encTSP encNat :=
    unary_to_binary.comp (ComputableInDegree.unary_pred.computableInPolyTime.comp
      ((length_list _).comp hdist))
  obtain ⟨Tn, Sn, hTn, hSn, hn⟩ := hn_poly.exists_computableInO
  have hstep : ComputableInO doubleStep
      (encPair (encList encRow) (encList encRow)) (encPair (encList encRow) (encList encRow))
      (fun p => (encPair (encList encRow) (encList encRow) p).length)
      (fun p => (encPair (encList encRow) (encList encRow) p).length) := by
    have hp := (ComputableInO.listAppend' (ComputableInO.fst (encList encRow) (encList encRow))
      (ComputableInO.snd (encList encRow) (encList encRow))).prod
      (ComputableInO.listAppend' (ComputableInO.snd (encList encRow) (encList encRow))
        (ComputableInO.snd (encList encRow) (encList encRow)))
    refine hp.mono 4 (fun p => ?_) (fun p => ?_)
    all_goals simp only [length_encPair]; omega
  let B : TSPInstance → ℕ := fun x =>
    2 ^ (x.dist.length - 1) * (32 * ((encTSP x).length + 1) ^ 2 + 16) + 16
  have hrow0_len : ∀ x : TSPInstance, (encRow (row0 x.dist)).length ≤
      3 * ((encTSP x).length + 1) ^ 2 := by
    intro x
    have hlen_d : x.dist.length ≤ (encTSP x).length := by
      refine (length_le_length_encList (encList encNat) x.dist).trans ?_
      rw [encTSP_apply]; enc_len
    have hmax := maxDist_lt_two_pow x
    have hopt : ∀ o ∈ row0 x.dist, (encOption encNat o).length ≤ (encTSP x).length + 1 := by
      intro o ho
      simp only [row0, List.mem_map, List.mem_range] at ho
      obtain ⟨t, -, rfl⟩ := ho
      have hd := (dist_le_maxDist x.dist 0 t).trans_lt hmax
      have hnat := length_encNat_le_of_lt_two_pow hd
      simp only [encOption_some, List.length_cons]
      omega
    have h1 := length_encList_le (encOption encNat) (row0 x.dist) hopt
    simp only [row0, List.length_map, List.length_range] at h1
    change (encRow (row0 x.dist)).length ≤
      x.dist.length * (2 * ((encTSP x).length + 1) + 1) at h1
    nlinarith only [h1, hlen_d]
  have hnone_len : ∀ x : TSPInstance, (encRow (noneRow x.dist.length)).length ≤
      3 * (encTSP x).length := by
    intro x
    have hlen_d : x.dist.length ≤ (encTSP x).length := by
      refine (length_le_length_encList (encList encNat) x.dist).trans ?_
      rw [encTSP_apply]; enc_len
    have hsum : (encList (encOption encNat) (noneRow x.dist.length)).length = x.dist.length := by
      rw [noneRow, length_encList, List.map_replicate, List.sum_replicate, smul_eq_mul]
      simp [encOption_none]
    change (encList (encOption encNat) (noneRow x.dist.length)).length ≤ 3 * (encTSP x).length
    omega
  have hB : ∀ x k, k ≤ x.dist.length - 1 →
      (encPair (encList encRow) (encList encRow)
        (doubleStep^[k] ([row0 x.dist], [noneRow x.dist.length]))).length ≤ B x := by
    intro x k hk
    rw [length_encPair, (iterate_doubleStep _ _ k).1, (iterate_doubleStep _ _ k).2]
    have hsum_rep : ∀ (m : ℕ) (r : Row),
        (encList encRow (List.replicate m r)).length = m * (2 * (encRow r).length + 1) := by
      intro m r
      rw [length_encList, List.map_replicate, List.sum_replicate, smul_eq_mul]
    have h1 : (encList encRow
        ([row0 x.dist] ++ List.replicate (2 ^ k - 1) (noneRow x.dist.length))).length =
        2 * (encRow (row0 x.dist)).length + 1 +
          (2 ^ k - 1) * (2 * (encRow (noneRow x.dist.length)).length + 1) := by
      rw [encList_append, List.length_append, encList_cons, encList_nil, List.length_append,
        length_frame, List.length_nil, add_zero, hsum_rep]
    have h2 := hsum_rep (2 ^ k) (noneRow x.dist.length)
    have hpow : 2 ^ k ≤ 2 ^ (x.dist.length - 1) := Nat.pow_le_pow_right (by decide) hk
    have hr0 := hrow0_len x
    have hnr := hnone_len x
    have hL1 : (encTSP x).length + 1 ≤ ((encTSP x).length + 1) ^ 2 :=
      Nat.le_self_pow (by decide) _
    have hpow1 : 1 ≤ 2 ^ (x.dist.length - 1) := Nat.one_le_two_pow
    have hnr2 : 2 * (encRow (noneRow x.dist.length)).length + 1 ≤
        6 * ((encTSP x).length + 1) ^ 2 + 1 := by
      nlinarith only [hnr, hL1]
    have hmul1 : (2 ^ k - 1) * (2 * (encRow (noneRow x.dist.length)).length + 1) ≤
        2 ^ (x.dist.length - 1) * (6 * ((encTSP x).length + 1) ^ 2 + 1) :=
      Nat.mul_le_mul (by omega) hnr2
    have hmul2 : 2 ^ k * (2 * (encRow (noneRow x.dist.length)).length + 1) ≤
        2 ^ (x.dist.length - 1) * (6 * ((encTSP x).length + 1) ^ 2 + 1) :=
      Nat.mul_le_mul hpow hnr2
    rw [h1, h2]
    change 2 * (2 * (encRow (row0 x.dist)).length + 1 +
          (2 ^ k - 1) * (2 * (encRow (noneRow x.dist.length)).length + 1)) + 1 +
        2 ^ k * (2 * (encRow (noneRow x.dist.length)).length + 1) ≤
      2 ^ (x.dist.length - 1) * (32 * ((encTSP x).length + 1) ^ 2 + 16) + 16
    calc 2 * (2 * (encRow (row0 x.dist)).length + 1 +
            (2 ^ k - 1) * (2 * (encRow (noneRow x.dist.length)).length + 1)) + 1 +
          2 ^ k * (2 * (encRow (noneRow x.dist.length)).length + 1)
        ≤ 2 * (2 * (3 * ((encTSP x).length + 1) ^ 2) + 1 +
            2 ^ (x.dist.length - 1) * (6 * ((encTSP x).length + 1) ^ 2 + 1)) + 1 +
            2 ^ (x.dist.length - 1) * (6 * ((encTSP x).length + 1) ^ 2 + 1) := by
            omega
      _ = 12 * ((encTSP x).length + 1) ^ 2 + 3 +
            18 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) +
            3 * 2 ^ (x.dist.length - 1) := by ring
      _ ≤ 12 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) + 3 +
            18 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) +
            3 * 2 ^ (x.dist.length - 1) := by
            have := Nat.le_mul_of_pos_left (((encTSP x).length + 1) ^ 2) hpow1
            omega
      _ ≤ 2 ^ (x.dist.length - 1) * (32 * ((encTSP x).length + 1) ^ 2 + 16) + 16 := by
            have : 32 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) +
                16 * 2 ^ (x.dist.length - 1) + 16 =
                2 ^ (x.dist.length - 1) * (32 * ((encTSP x).length + 1) ^ 2 + 16) + 16 := by ring
            omega
  have hit := ComputableInO.iterate hn hi hstep
    (R := B) (Q := B) (B := B)
    (fun x k hk => hB x k hk) (fun x k hk => hB x k hk) (fun x k hk => hB x k hk)
  obtain ⟨Td, Sd, hTd, hSd, hd_inO⟩ := hdist.exists_computableInO
  have hinit_all : ComputableInO hkInit encTSP encHKState
      (fun x => Td x + (encTSP x).length + (Tn x + Ti x +
        (x.dist.length - 1 + 1) * (B x + B x + ((encNat (x.dist.length - 1)).length + 1) ^ 2)))
      (fun x => Sd x + (encTSP x).length +
        (Sn x + Si x + B x + B x + (encNat (x.dist.length - 1)).length)) :=
    ((hd_inO.prod (ComputableInO.const 0)).prod ((ComputableInO.fst _ _).comp_linear hit)).mono 1
      (fun _ => by dsimp; omega) (fun _ => by dsimp; omega)
  have hpoly_all : PolyBounded (fun x : TSPInstance => (encTSP x).length)
      (fun x => Td x + Sn x + Si x + Tn x + Ti x + x.dist.length +
        (encNat (x.dist.length - 1)).length + Sd x) := by
    growth_poly
  obtain ⟨c, d, hcd⟩ := hpoly_all.exists_le
  have hB_le : ∀ x : TSPInstance,
      B x ≤ 64 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) := fun x => by
    have hpow1 : 1 ≤ 2 ^ (x.dist.length - 1) := Nat.one_le_two_pow
    have hL2 : 1 ≤ ((encTSP x).length + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hm1 : 16 * 2 ^ (x.dist.length - 1) ≤
        16 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) :=
      Nat.mul_le_mul_left 16 (Nat.le_mul_of_pos_right _ hL2)
    have hm2 : 16 ≤ 16 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) :=
      Nat.mul_le_mul_left 16 (Nat.mul_le_mul hpow1 hL2)
    change 2 ^ (x.dist.length - 1) * (32 * ((encTSP x).length + 1) ^ 2 + 16) + 16 ≤ _
    calc 2 ^ (x.dist.length - 1) * (32 * ((encTSP x).length + 1) ^ 2 + 16) + 16
        = 32 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) +
            16 * 2 ^ (x.dist.length - 1) + 16 := by ring
      _ ≤ 64 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) := by omega
  refine ⟨2 * d + 4, hinit_all.mono (2 * (c + 1) ^ 2 + 200) (fun x => ?_) (fun x => ?_)⟩
  · have hp := hcd x
    have hpow1 : 1 ≤ 2 ^ (x.dist.length - 1) := Nat.one_le_two_pow
    have hL1 : 1 ≤ ((encTSP x).length + 1) ^ (2 * d + 4) := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hLd : ((encTSP x).length + 1) ^ d ≤ ((encTSP x).length + 1) ^ (2 * d + 4) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hlen_x : x.dist.length - 1 + 1 ≤ (encTSP x).length + 1 := by
      have : x.dist.length ≤ (encTSP x).length := by
        refine (length_le_length_encList (encList encNat) x.dist).trans ?_
        rw [encTSP_apply]; enc_len
      omega
    have hBx := hB_le x
    have hlen_sq : ((encNat (x.dist.length - 1)).length + 1) ^ 2 ≤
        (c + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * d) := by
      have h1 : (encNat (x.dist.length - 1)).length + 1 ≤
          (c + 1) * ((encTSP x).length + 1) ^ d := by
        have hLd' : 1 ≤ ((encTSP x).length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
        nlinarith only [hp, hLd']
      calc ((encNat (x.dist.length - 1)).length + 1) ^ 2
          ≤ ((c + 1) * ((encTSP x).length + 1) ^ d) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = (c + 1) ^ 2 * (((encTSP x).length + 1) ^ d) ^ 2 := Nat.mul_pow _ _ _
        _ = (c + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * d) := by rw [← pow_mul, mul_comm d 2]
    have hL2d3 : ((encTSP x).length + 1) * ((encTSP x).length + 1) ^ (2 * d) ≤
        ((encTSP x).length + 1) ^ (2 * d + 4) := by
      calc ((encTSP x).length + 1) * ((encTSP x).length + 1) ^ (2 * d)
          = ((encTSP x).length + 1) ^ (2 * d + 1) := by rw [pow_succ']
        _ ≤ ((encTSP x).length + 1) ^ (2 * d + 4) :=
            Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hL3 : ((encTSP x).length + 1) ^ 3 ≤ ((encTSP x).length + 1) ^ (2 * d + 4) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hL_pow : (encTSP x).length ≤ ((encTSP x).length + 1) ^ (2 * d + 4) :=
      (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
    have hpre : Td x + (encTSP x).length + Tn x + Ti x ≤
        (c + 1) * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * d + 4)) := by
      have hc1 : Td x + (encTSP x).length + Tn x + Ti x ≤
          (c + 1) * ((encTSP x).length + 1) ^ (2 * d + 4) := by
        nlinarith only [hp, hLd, hL_pow]
      calc Td x + (encTSP x).length + Tn x + Ti x
          ≤ (c + 1) * ((encTSP x).length + 1) ^ (2 * d + 4) := hc1
        _ ≤ (c + 1) * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * d + 4)) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hpow1)
    have hterm1 : (x.dist.length - 1 + 1) * (B x + B x) ≤
        128 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * d + 4)) := by
      calc (x.dist.length - 1 + 1) * (B x + B x)
          ≤ ((encTSP x).length + 1) * (2 * (64 * (2 ^ (x.dist.length - 1) *
              ((encTSP x).length + 1) ^ 2))) :=
            Nat.mul_le_mul hlen_x (by omega)
        _ = 128 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 3) := by ring
        _ ≤ 128 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * d + 4)) :=
            Nat.mul_le_mul_left 128 (Nat.mul_le_mul_left _ hL3)
    have hterm2 : (x.dist.length - 1 + 1) * ((encNat (x.dist.length - 1)).length + 1) ^ 2 ≤
        (c + 1) ^ 2 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * d + 4)) := by
      calc (x.dist.length - 1 + 1) * ((encNat (x.dist.length - 1)).length + 1) ^ 2
          ≤ ((encTSP x).length + 1) * ((c + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * d)) :=
            Nat.mul_le_mul hlen_x hlen_sq
        _ = (c + 1) ^ 2 * (((encTSP x).length + 1) * ((encTSP x).length + 1) ^ (2 * d)) := by ring
        _ ≤ (c + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * d + 4) := Nat.mul_le_mul_left _ hL2d3
        _ ≤ (c + 1) ^ 2 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * d + 4)) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hpow1)
    have hmul_sum : (x.dist.length - 1 + 1) *
          (B x + B x + ((encNat (x.dist.length - 1)).length + 1) ^ 2) =
        (x.dist.length - 1 + 1) * (B x + B x) +
          (x.dist.length - 1 + 1) * ((encNat (x.dist.length - 1)).length + 1) ^ 2 := by ring
    have hc_le : c + 1 ≤ (c + 1) ^ 2 := Nat.le_self_pow (by decide) _
    set M := 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * d + 4)
    have hpre' : Td x + (encTSP x).length + Tn x + Ti x ≤ (c + 1) ^ 2 * M :=
      hpre.trans (Nat.mul_le_mul_right M hc_le)
    calc Td x + (encTSP x).length + (Tn x + Ti x +
            (x.dist.length - 1 + 1) * (B x + B x + ((encNat (x.dist.length - 1)).length + 1) ^ 2))
        = (Td x + (encTSP x).length + Tn x + Ti x) +
            (x.dist.length - 1 + 1) * (B x + B x) +
            (x.dist.length - 1 + 1) * ((encNat (x.dist.length - 1)).length + 1) ^ 2 := by ring
      _ ≤ (c + 1) ^ 2 * M + 128 * M + (c + 1) ^ 2 * M := by omega
      _ = (2 * (c + 1) ^ 2 + 128) * M := by ring
      _ ≤ (2 * (c + 1) ^ 2 + 200) * M := Nat.mul_le_mul_right M (by omega)
      _ ≤ (2 * (c + 1) ^ 2 + 200) * (M + 1) := Nat.mul_le_mul_left _ (Nat.le_succ M)
  · have hp := hcd x
    have hpow1 : 1 ≤ 2 ^ (x.dist.length - 1) := Nat.one_le_two_pow
    have hLd : ((encTSP x).length + 1) ^ d ≤ ((encTSP x).length + 1) ^ (2 * d + 4) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hL2 : ((encTSP x).length + 1) ^ 2 ≤ ((encTSP x).length + 1) ^ (2 * d + 4) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hL_pow : (encTSP x).length ≤ ((encTSP x).length + 1) ^ (2 * d + 4) :=
      (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
    have hBx : B x ≤ 64 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * d + 4)) :=
      (hB_le x).trans (Nat.mul_le_mul_left 64 (Nat.mul_le_mul_left _ hL2))
    have hc_le : c + 1 ≤ (c + 1) ^ 2 := Nat.le_self_pow (by decide) _
    set M := 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * d + 4)
    have hrest : Sd x + (encTSP x).length + Sn x + Si x + (encNat (x.dist.length - 1)).length ≤
        (c + 1) ^ 2 * M := by
      have h1 : Sd x + (encTSP x).length + Sn x + Si x + (encNat (x.dist.length - 1)).length ≤
          (c + 1) * ((encTSP x).length + 1) ^ (2 * d + 4) := by
        nlinarith only [hp, hLd, hL_pow]
      calc Sd x + (encTSP x).length + Sn x + Si x + (encNat (x.dist.length - 1)).length
          ≤ (c + 1) * ((encTSP x).length + 1) ^ (2 * d + 4) := h1
        _ ≤ (c + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * d + 4) :=
            Nat.mul_le_mul_right _ hc_le
        _ ≤ (c + 1) ^ 2 * M := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hpow1)
    calc Sd x + (encTSP x).length + (Sn x + Si x + B x + B x + (encNat (x.dist.length - 1)).length)
        = (Sd x + (encTSP x).length + Sn x + Si x + (encNat (x.dist.length - 1)).length) +
            B x + B x := by ring
      _ ≤ (c + 1) ^ 2 * M + 64 * M + 64 * M := by omega
      _ ≤ (2 * (c + 1) ^ 2 + 200) * M := by
          have : (c + 1) ^ 2 * M + 128 * M = ((c + 1) ^ 2 + 128) * M := by ring
          have hmul := Nat.mul_le_mul_right M
            (show (c + 1) ^ 2 + 128 ≤ 2 * (c + 1) ^ 2 + 200 by omega)
          omega
      _ ≤ (2 * (c + 1) ^ 2 + 200) * (M + 1) := Nat.mul_le_mul_left _ (Nat.le_succ M)

private theorem computableInO_hkStep :
    ∃ d, ComputableInO hkStep encHKState encHKState
      (fun st => (encHKState st).length +
        (st.2.length + 1) * ((encList (encList encNat) st.1.1).length +
          (encUnary st.1.2).length + listMax (fun r => (encRow r).length) st.2 + 1) ^ d)
      (fun st => (encHKState st).length +
        (st.2.length + 1) * ((encList (encList encNat) st.1.1).length +
          (encUnary st.1.2).length + listMax (fun r => (encRow r).length) st.2 + 1) ^ d) := by
  obtain ⟨de, hev⟩ := computableInO_evens
  obtain ⟨do_, hodds⟩ := computableInO_passOdds
  let encHKParam : (List (List ℕ) × ℕ) ↪ List Bool :=
    encPair (encList (encList encNat)) encUnary
  have hnextParam : ComputableInPolyTime
      (fun p : List (List ℕ) × ℕ => (p.1, if p.2 + 1 = p.1.length - 1 then 0 else p.2 + 1))
      encHKParam encHKParam := by
    have hDp : ComputableInPolyTime (fun p : List (List ℕ) × ℕ => p.1)
        encHKParam (encList (encList encNat)) := by fun_prop
    have hip : ComputableInPolyTime (fun p : List (List ℕ) × ℕ => p.2)
        encHKParam encUnary := by fun_prop
    have hnp : ComputableInPolyTime (fun p : List (List ℕ) × ℕ => p.1.length - 1)
        encHKParam encUnary :=
      ComputableInDegree.unary_pred.computableInPolyTime.comp ((length_list _).comp hDp)
    have hcp : ComputableInPolyTime (fun p : List (List ℕ) × ℕ => decide (p.2 + 1 = p.1.length - 1))
        encHKParam encBool :=
      (ComputableInDegree.eq encUnary).computableInPolyTime.comp ((unary_succ.comp hip).prod hnp)
    exact hDp.prod (hcp.ite_decide (const 0) (unary_succ.comp hip))
  have hrowParam : ComputableInPolyTime
      (fun p : List (List ℕ) × ℕ => (p.1.getD (p.2 + 1) [], p.2))
      encHKParam encOddParams := by
    have hDp : ComputableInPolyTime (fun p : List (List ℕ) × ℕ => p.1)
        encHKParam (encList (encList encNat)) := by fun_prop
    have hip : ComputableInPolyTime (fun p : List (List ℕ) × ℕ => p.2)
        encHKParam encUnary := by fun_prop
    exact (listGetDWithInput hDp (unary_succ.comp hip) []).prod hip
  obtain ⟨T₁, S₁, hT₁, hS₁, hP₁⟩ := hnextParam.exists_computableInO
  obtain ⟨c₁, d₁, hcd₁⟩ := (hT₁.add hS₁).exists_le
  obtain ⟨T₂, S₂, hT₂, hS₂, hP₂⟩ := hrowParam.exists_computableInO
  obtain ⟨c₂, d₂, hcd₂⟩ := (hT₂.add hS₂).exists_le
  have h1 := hP₁.comp (ComputableInO.fst encHKParam (encList encRow))
  have h2 := hP₂.comp (ComputableInO.fst encHKParam (encList encRow))
  have hev_st := hev.comp (ComputableInO.snd encHKParam (encList encRow))
  have hodds_st := hodds.comp (h2.prod (ComputableInO.snd encHKParam (encList encRow)))
  let hfull := h1.prod (ComputableInO.listAppend' hev_st hodds_st)
  let d := max (max d₁ d₂) (max de do_) + 1
  let M : HKState → ℕ := fun st =>
    (encList (encList encNat) st.1.1).length + (encUnary st.1.2).length +
      listMax (fun r => (encRow r).length) st.2 + 1
  let C := 4 ^ d * (c₁ + c₂ + 8) + 12
  have hfacts : ∀ st : HKState,
      1 ≤ M st ∧ 1 ≤ M st ^ d ∧
      T₁ st.1 ≤ c₁ * 3 ^ d * M st ^ d ∧
      T₂ st.1 ≤ c₂ * 3 ^ d * M st ^ d ∧
      S₁ st.1 ≤ c₁ * 3 ^ d * M st ^ d ∧
      S₂ st.1 ≤ c₂ * 3 ^ d * M st ^ d ∧
      (encOddParams (st.1.1.getD (st.1.2 + 1) [], st.1.2)).length ≤ 3 * M st ∧
      (encList encRow st.2).length ≤ (encHKState st).length ∧
      (encPair encOddParams (encList encRow)
        ((st.1.1.getD (st.1.2 + 1) [], st.1.2), st.2)).length ≤
        (encHKState st).length + 7 * M st ∧
      (st.2.length + 1) * (listMax (fun r => (encRow r).length) st.2 + 1) ^ de ≤
        (st.2.length + 1) * M st ^ d ∧
      (listMax (fun r => (encRow r).length) st.2 + 1) ^ de ≤ M st ^ d ∧
      (st.2.length + 1) * ((encOddParams (st.1.1.getD (st.1.2 + 1) [], st.1.2)).length +
        listMax (fun r => (encRow r).length) st.2 + 1) ^ do_ ≤
        4 ^ d * ((st.2.length + 1) * M st ^ d) := fun st => by
    have hM1 : 1 ≤ M st := by dsimp [M]; omega
    have hM_pow : 1 ≤ M st ^ d := Nat.one_le_pow _ _ hM1
    have hlen_p : (encHKParam st.1).length ≤ 2 * M st := by
      simp only [encHKParam, length_encPair, M]
      omega
    have hgetD_le : (encList encNat (st.1.1.getD (st.1.2 + 1) [])).length ≤
        (encList (encList encNat) st.1.1).length + 1 := by
      rw [List.getD_eq_getElem?_getD]
      cases hget : st.1.1[st.1.2 + 1]? with
      | none => simp
      | some row =>
        exact (length_le_encList_of_mem (encList encNat) (List.mem_of_getElem? hget)).trans
          (Nat.le_succ _)
    have hodd : (encOddParams (st.1.1.getD (st.1.2 + 1) [], st.1.2)).length ≤ 3 * M st := by
      simp only [encOddParams, length_encPair, M]
      omega
    have hpow_le_pair : ∀ (e : ℕ), e ≤ d → ∀ (c' T' S' : ℕ),
        T' + S' ≤ c' * ((encHKParam st.1).length + 1) ^ e →
        T' ≤ c' * 3 ^ d * M st ^ d ∧ S' ≤ c' * 3 ^ d * M st ^ d := by
      intro e he c' T' S' hTS
      have hpow : ((encHKParam st.1).length + 1) ^ e ≤ 3 ^ d * M st ^ d := by
        have hle : (encHKParam st.1).length + 1 ≤ 3 * M st := by omega
        calc ((encHKParam st.1).length + 1) ^ e
            ≤ (3 * M st) ^ e := Nat.pow_le_pow_left hle e
          _ ≤ (3 * M st) ^ d := Nat.pow_le_pow_right (by omega) he
          _ = 3 ^ d * M st ^ d := Nat.mul_pow _ _ _
      have hle_sum : ∀ {u}, u ≤ T' + S' → u ≤ c' * 3 ^ d * M st ^ d := fun {u} hu =>
        calc u ≤ T' + S' := hu
          _ ≤ c' * ((encHKParam st.1).length + 1) ^ e := hTS
          _ ≤ c' * (3 ^ d * M st ^ d) := Nat.mul_le_mul_left _ hpow
          _ = c' * 3 ^ d * M st ^ d := by ring
      exact ⟨hle_sum (Nat.le_add_right _ _), hle_sum (Nat.le_add_left _ _)⟩
    obtain ⟨hT₁, hS₁⟩ := hpow_le_pair d₁ (by omega) c₁ (T₁ st.1) (S₁ st.1) (hcd₁ st.1)
    obtain ⟨hT₂, hS₂⟩ := hpow_le_pair d₂ (by omega) c₂ (T₂ st.1) (S₂ st.1) (hcd₂ st.1)
    have hL : (encList encRow st.2).length ≤ (encHKState st).length := by
      rw [show encHKState st = encPair encHKParam (encList encRow) (st.1, st.2) from rfl,
        length_encPair]
      dsimp only
      omega
    have hpair : (encPair encOddParams (encList encRow)
          ((st.1.1.getD (st.1.2 + 1) [], st.1.2), st.2)).length ≤
        (encHKState st).length + 7 * M st := by
      rw [length_encPair]
      dsimp only
      omega
    have hdeS : (listMax (fun r => (encRow r).length) st.2 + 1) ^ de ≤ M st ^ d := by
      have hle : listMax (fun r => (encRow r).length) st.2 + 1 ≤ M st := by dsimp [M]; omega
      exact (Nat.pow_le_pow_left hle de).trans (Nat.pow_le_pow_right hM1 (by omega))
    have hde : (st.2.length + 1) * (listMax (fun r => (encRow r).length) st.2 + 1) ^ de ≤
        (st.2.length + 1) * M st ^ d := Nat.mul_le_mul_left _ hdeS
    have hdo_pow : ((encOddParams (st.1.1.getD (st.1.2 + 1) [], st.1.2)).length +
        listMax (fun r => (encRow r).length) st.2 + 1) ^ do_ ≤ 4 ^ d * M st ^ d := by
      have hle : (encOddParams (st.1.1.getD (st.1.2 + 1) [], st.1.2)).length +
          listMax (fun r => (encRow r).length) st.2 + 1 ≤ 4 * M st := by
        dsimp [M] at hodd ⊢
        omega
      calc _ ≤ (4 * M st) ^ do_ := Nat.pow_le_pow_left hle do_
        _ ≤ (4 * M st) ^ d := Nat.pow_le_pow_right (by omega) (by omega)
        _ = 4 ^ d * M st ^ d := Nat.mul_pow _ _ _
    have hdo : (st.2.length + 1) * ((encOddParams (st.1.1.getD (st.1.2 + 1) [], st.1.2)).length +
          listMax (fun r => (encRow r).length) st.2 + 1) ^ do_ ≤
        4 ^ d * ((st.2.length + 1) * M st ^ d) := by
      calc _ ≤ (st.2.length + 1) * (4 ^ d * M st ^ d) := Nat.mul_le_mul_left _ hdo_pow
        _ = 4 ^ d * ((st.2.length + 1) * M st ^ d) := by ring
    exact ⟨hM1, hM_pow, hT₁, hT₂, hS₁, hS₂, hodd, hL, hpair, hde, hdeS, hdo⟩
  have hscale : ∀ (st : HKState) (f : List (List ℕ) × ℕ → ℕ) (cf : ℕ)
      (hf : f st.1 ≤ cf * 3 ^ d * M st ^ d),
      f st.1 ≤ 4 ^ d * cf * ((st.2.length + 1) * M st ^ d) := by
    intro st f cf hf
    have hs1 : 1 ≤ st.2.length + 1 := Nat.succ_pos _
    have h34 : 3 ^ d ≤ 4 ^ d := Nat.pow_le_pow_left (by decide) d
    have hMd_le : M st ^ d ≤ (st.2.length + 1) * M st ^ d := Nat.le_mul_of_pos_left _ hs1
    calc f st.1 ≤ cf * 3 ^ d * M st ^ d := hf
      _ ≤ cf * 4 ^ d * M st ^ d := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h34)
      _ = (4 ^ d * cf) * M st ^ d := by ring
      _ ≤ (4 ^ d * cf) * ((st.2.length + 1) * M st ^ d) := Nat.mul_le_mul_left _ hMd_le
  have hodd_eq : ∀ (st : HKState),
      (Turing.MultiTapeTM.frame ((encList encNat) (st.1.1.getD (st.1.2 + 1) [])) ++
        List.replicate st.1.2 true).length =
      (encOddParams (st.1.1.getD (st.1.2 + 1) [], st.1.2)).length := fun _ => rfl
  have hclose : ∀ (st : HKState) (k : ℕ), k ≤ 8 →
      6 * (encHKState st).length +
          (4 ^ d * c₁ + 4 ^ d * c₂ + 4 ^ d + k) * ((st.2.length + 1) * M st ^ d) ≤
        C * ((encHKState st).length + (st.2.length + 1) * M st ^ d + 1) := by
    intro st k hk
    set B := (st.2.length + 1) * M st ^ d
    have hC6 : 6 ≤ C := by dsimp [C]; omega
    have hCB : 4 ^ d * c₁ + 4 ^ d * c₂ + 4 ^ d + k ≤ C := by
      have : 4 ^ d * (c₁ + c₂ + 8) = 4 ^ d * c₁ + 4 ^ d * c₂ + 8 * 4 ^ d := by ring
      have h4_1 : 1 ≤ 4 ^ d := Nat.one_le_pow _ _ (by decide)
      dsimp [C]; omega
    have ha := Nat.mul_le_mul_right (encHKState st).length hC6
    have hb := Nat.mul_le_mul_right B hCB
    have : C * ((encHKState st).length + B + 1) = C * (encHKState st).length + C * B + C := by
      ring
    omega
  refine ⟨d, hfull.mono C (fun st => ?_) (fun st => ?_)⟩
  · obtain ⟨hM1, hM_pow, hT₁, hT₂, _, _, _, hL, hpair, hde, _, hdo⟩ := hfacts st
    have hM_le : M st ≤ M st ^ d := Nat.le_self_pow (by omega) _
    have h4_1 : 1 ≤ 4 ^ d := Nat.one_le_pow _ _ (by decide)
    have hMd_le : M st ^ d ≤ (st.2.length + 1) * M st ^ d :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    set B := (st.2.length + 1) * M st ^ d
    have hT₁' : T₁ st.1 ≤ 4 ^ d * c₁ * B := hscale st T₁ c₁ hT₁
    have hT₂' : T₂ st.1 ≤ 4 ^ d * c₂ * B := hscale st T₂ c₂ hT₂
    have hdo' : (st.2.length + 1) * ((Turing.MultiTapeTM.frame
          ((encList encNat) (st.1.1.getD (st.1.2 + 1) [])) ++
          List.replicate st.1.2 true).length +
          listMax (fun r => (encRow r).length) st.2 + 1) ^ do_ ≤ 4 ^ d * B := by
      rw [hodd_eq st]
      exact hdo
    have hM_tot : M st ≤ B := hM_le.trans hMd_le
    have hst_eq : (encPair encHKParam (encList encRow) st).length = (encHKState st).length := rfl
    dsimp only [Function.comp_def]
    have hcalc : (encPair encHKParam (encList encRow) st).length + T₁ st.1 +
          (((encPair encHKParam (encList encRow) st).length +
            ((encList encRow st.2).length +
              (st.2.length + 1) * (listMax (fun r => (encRow r).length) st.2 + 1) ^ de)) +
            (((encPair encHKParam (encList encRow) st).length + T₂ st.1 +
              (encPair encHKParam (encList encRow) st).length) +
              ((encPair encOddParams (encList encRow)
                ((st.1.1.getD (st.1.2 + 1) [], st.1.2), st.2)).length +
                (st.2.length + 1) * ((Turing.MultiTapeTM.frame ((encList encNat)
                  (st.1.1.getD (st.1.2 + 1) [])) ++ List.replicate st.1.2 true).length +
                  listMax (fun r => (encRow r).length) st.2 + 1) ^ do_)))
        ≤ 6 * (encHKState st).length + (4 ^ d * c₁ + 4 ^ d * c₂ + 4 ^ d + 8) * B := by
      have h7 : 7 * M st ≤ 7 * B := Nat.mul_le_mul_left 7 hM_tot
      have : (4 ^ d * c₁ + 4 ^ d * c₂ + 4 ^ d + 8) * B =
          4 ^ d * c₁ * B + 4 ^ d * c₂ * B + B + 7 * B + 4 ^ d * B := by ring
      omega
    exact hcalc.trans (hclose st 8 le_rfl)
  · obtain ⟨hM1, hM_pow, _, _, hS₁, hS₂, hodd, hL, _, _, hdeS, hdo⟩ := hfacts st
    have hdoS : (st.2.length + 1) * (listMax (fun r => (encRow r).length) st.2 +
          (encOddParams (st.1.1.getD (st.1.2 + 1) [], st.1.2)).length + 1) ^ do_ ≤
        4 ^ d * ((st.2.length + 1) * M st ^ d) := by
      simpa only [add_left_comm, add_comm] using hdo
    set B := (st.2.length + 1) * M st ^ d
    have hdoS' : (st.2.length + 1) * (listMax (fun r => (encRow r).length) st.2 +
          (Turing.MultiTapeTM.frame ((encList encNat) (st.1.1.getD (st.1.2 + 1) [])) ++
            List.replicate st.1.2 true).length + 1) ^ do_ ≤ 4 ^ d * B := by
      rw [hodd_eq st]
      exact hdoS
    have hM_le : M st ≤ M st ^ d := Nat.le_self_pow (by omega) _
    have h4_1 : 1 ≤ 4 ^ d := Nat.one_le_pow _ _ (by decide)
    have hMd_le : M st ^ d ≤ B := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have hS₁' : S₁ st.1 ≤ 4 ^ d * c₁ * B := hscale st S₁ c₁ hS₁
    have hS₂' : S₂ st.1 ≤ 4 ^ d * c₂ * B := hscale st S₂ c₂ hS₂
    have hodd' : (Turing.MultiTapeTM.frame ((encList encNat) (st.1.1.getD (st.1.2 + 1) [])) ++
          List.replicate st.1.2 true).length ≤ 3 * B := by
      rw [hodd_eq st]
      exact hodd.trans (Nat.mul_le_mul_left 3 (hM_le.trans hMd_le))
    have hst_eq : (encPair encHKParam (encList encRow) st).length = (encHKState st).length := rfl
    dsimp only [Function.comp_def]
    have hcalc : (encPair encHKParam (encList encRow) st).length + S₁ st.1 +
          (((encPair encHKParam (encList encRow) st).length +
            ((encList encRow st.2).length +
              (listMax (fun r => (encRow r).length) st.2 + 1) ^ de)) +
            (((encPair encHKParam (encList encRow) st).length + S₂ st.1 +
              (encPair encHKParam (encList encRow) st).length) +
              ((Turing.MultiTapeTM.frame ((encList encNat) (st.1.1.getD (st.1.2 + 1) [])) ++
                List.replicate st.1.2 true).length +
                (encList encRow st.2).length +
                (st.2.length + 1) * (listMax (fun r => (encRow r).length) st.2 +
                  (Turing.MultiTapeTM.frame ((encList encNat) (st.1.1.getD (st.1.2 + 1) [])) ++
                    List.replicate st.1.2 true).length + 1) ^ do_)))
        ≤ 6 * (encHKState st).length + (4 ^ d * c₁ + 4 ^ d * c₂ + 4 ^ d + 4) * B := by
      have : (4 ^ d * c₁ + 4 ^ d * c₂ + 4 ^ d + 4) * B =
          4 ^ d * c₁ * B + 4 ^ d * c₂ * B + B + 3 * B + 4 ^ d * B := by ring
      omega
    exact hcalc.trans (hclose st 4 (by omega))

private theorem computableInO_tmOptCost :
    ∃ e, ComputableInO tmOptCost encTSP encNat
      (fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e)
      (fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e) := by
  have hdist : ComputableInPolyTime TSPInstance.dist encTSP (encList (encList encNat)) := by
    fun_prop
  have hcnt_poly : ComputableInPolyTime
      (fun x : TSPInstance => (x.dist.length - 1) * (x.dist.length - 1))
      encTSP encNat := by
    have hn_bin := unary_to_binary.comp
      (ComputableInDegree.unary_pred.computableInPolyTime.comp ((length_list _).comp hdist))
    exact binary_mul' hn_bin hn_bin
  obtain ⟨Tcnt, Scnt, hTcnt, hScnt, hcnt⟩ := hcnt_poly.exists_computableInO
  obtain ⟨d₀, hinit⟩ := computableInO_hkInit
  obtain ⟨ds, hstep⟩ := computableInO_hkStep
  let B : TSPInstance → ℕ := fun x =>
    16 * 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2 + 16
  let R : TSPInstance → ℕ := fun x =>
    (16 + 2 * 8 ^ ds) * 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * ds + 2) + 16
  have hst_bound : ∀ (x : TSPInstance) (k : ℕ), k ≤ (x.dist.length - 1) * (x.dist.length - 1) →
      (hkStep^[k] (hkInit x)).2.length ≤ 2 ^ (x.dist.length - 1) ∧
        listMax (fun r => (encRow r).length) (hkStep^[k] (hkInit x)).2 ≤
          4 * ((encTSP x).length + 1) ^ 2 + 1 ∧
        (encList (encList encNat) (hkStep^[k] (hkInit x)).1.1).length ≤ (encTSP x).length + 1 ∧
        (encUnary (hkStep^[k] (hkInit x)).1.2).length ≤ (encTSP x).length + 1 ∧
        (encHKState (hkStep^[k] (hkInit x))).length ≤ B x := by
    intro x k hk
    cases hx : x.dist.length with
    | zero =>
      rw [hx] at hk
      obtain rfl : k = 0 := by omega
      have hxnil : x.dist = [] := List.length_eq_zero_iff.1 hx
      have hst0 : hkInit x = (([], 0), [[]]) := by
        simp [hkInit, initTable, hxnil, row0]
      rw [Function.iterate_zero_apply, hst0]
      simp only [B, hx, Nat.zero_sub, pow_zero, mul_one, List.length_singleton,
        listMax, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, max_self,
        encList_nil, encUnary_apply, List.length_replicate, encRow, List.length_nil]
      have hlen_st : (encHKState (([], 0), ([[]] : List Row))).length ≤ 12 := by
        simp [encHKState, encPair_apply, encList_cons, encList_nil, encUnary_apply,
          Turing.MultiTapeTM.frame, encRow]
      omega
    | succ n =>
      rw [hx] at hk
      rw [Nat.add_sub_cancel] at hk ⊢
      obtain ⟨h1, h2, hrow, -, hst_len⟩ := hkState_size_bound x hx hk
      have hL_max : listMax (fun r => (encRow r).length) (hkStep^[k] (hkInit x)).2 ≤
          4 * ((encTSP x).length + 1) ^ 2 + 1 :=
        (listMax_le (fun r hr => (hrow r hr).trans (Nat.le_succ _)))
      have hmod_le := mod_le_encTSP_length hx hk
      have hdist_le : (encList (encList encNat) x.dist).length ≤ (encTSP x).length := by
        rw [encTSP_apply]; enc_len
      refine ⟨h2.le, hL_max, ?_, ?_, ?_⟩
      · rw [h1]; exact hdist_le.trans (Nat.le_succ _)
      · rw [h1, encUnary_apply, List.length_replicate]; exact hmod_le.trans (Nat.le_succ _)
      · have hL1 : 1 ≤ ((encTSP x).length + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
        have hpow1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        change (encHKState (hkStep^[k] (hkInit x))).length ≤
          16 * 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2 + 16
        rw [hx, Nat.add_sub_cancel]
        nlinarith only [hst_len, hL1, hpow1]
  have hstep_cost : ∀ (x : TSPInstance) (k : ℕ), k ≤ (x.dist.length - 1) * (x.dist.length - 1) →
      (encHKState (hkStep^[k] (hkInit x))).length +
        ((hkStep^[k] (hkInit x)).2.length + 1) *
          ((encList (encList encNat) (hkStep^[k] (hkInit x)).1.1).length +
            (encUnary (hkStep^[k] (hkInit x)).1.2).length +
            listMax (fun r => (encRow r).length) (hkStep^[k] (hkInit x)).2 + 1) ^ ds ≤ R x := by
    intro x k hk
    obtain ⟨hlen, hmax, hdist_le, hmod_le, hB_le⟩ := hst_bound x k hk
    have hM : (encList (encList encNat) (hkStep^[k] (hkInit x)).1.1).length +
        (encUnary (hkStep^[k] (hkInit x)).1.2).length +
        listMax (fun r => (encRow r).length) (hkStep^[k] (hkInit x)).2 + 1 ≤
        8 * ((encTSP x).length + 1) ^ 2 := by
      have hL1 : (encTSP x).length + 1 ≤ ((encTSP x).length + 1) ^ 2 :=
        Nat.le_self_pow (by decide) _
      omega
    have hpow_ds : ((encList (encList encNat) (hkStep^[k] (hkInit x)).1.1).length +
        (encUnary (hkStep^[k] (hkInit x)).1.2).length +
        listMax (fun r => (encRow r).length) (hkStep^[k] (hkInit x)).2 + 1) ^ ds ≤
        8 ^ ds * ((encTSP x).length + 1) ^ (2 * ds) := by
      calc _ ≤ (8 * ((encTSP x).length + 1) ^ 2) ^ ds := Nat.pow_le_pow_left hM ds
        _ = 8 ^ ds * (((encTSP x).length + 1) ^ 2) ^ ds := Nat.mul_pow _ _ _
        _ = 8 ^ ds * ((encTSP x).length + 1) ^ (2 * ds) := by rw [← pow_mul]
    have hpow1 : 1 ≤ 2 ^ (x.dist.length - 1) := Nat.one_le_two_pow
    have hlen_add : (hkStep^[k] (hkInit x)).2.length + 1 ≤ 2 * 2 ^ (x.dist.length - 1) := by
      omega
    have hmul : ((hkStep^[k] (hkInit x)).2.length + 1) *
          ((encList (encList encNat) (hkStep^[k] (hkInit x)).1.1).length +
            (encUnary (hkStep^[k] (hkInit x)).1.2).length +
            listMax (fun r => (encRow r).length) (hkStep^[k] (hkInit x)).2 + 1) ^ ds ≤
        2 * 8 ^ ds * 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * ds) := by
      calc ((hkStep^[k] (hkInit x)).2.length + 1) *
              ((encList (encList encNat) (hkStep^[k] (hkInit x)).1.1).length +
                (encUnary (hkStep^[k] (hkInit x)).1.2).length +
                listMax (fun r => (encRow r).length) (hkStep^[k] (hkInit x)).2 + 1) ^ ds
          ≤ (2 * 2 ^ (x.dist.length - 1)) * (8 ^ ds * ((encTSP x).length + 1) ^ (2 * ds)) :=
            Nat.mul_le_mul hlen_add hpow_ds
        _ = 2 * 8 ^ ds * 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * ds) := by ring
    have hL2_le : ((encTSP x).length + 1) ^ 2 ≤ ((encTSP x).length + 1) ^ (2 * ds + 2) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hL2ds_le : ((encTSP x).length + 1) ^ (2 * ds) ≤ ((encTSP x).length + 1) ^ (2 * ds + 2) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hB_le' : (encHKState (hkStep^[k] (hkInit x))).length ≤
        16 * 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2 + 16 := hB_le
    change _ ≤ (16 + 2 * 8 ^ ds) * 2 ^ (x.dist.length - 1) *
        ((encTSP x).length + 1) ^ (2 * ds + 2) + 16
    calc (encHKState (hkStep^[k] (hkInit x))).length +
          ((hkStep^[k] (hkInit x)).2.length + 1) *
            ((encList (encList encNat) (hkStep^[k] (hkInit x)).1.1).length +
              (encUnary (hkStep^[k] (hkInit x)).1.2).length +
              listMax (fun r => (encRow r).length) (hkStep^[k] (hkInit x)).2 + 1) ^ ds
        ≤ (16 * 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2 + 16) +
            2 * 8 ^ ds * 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * ds) := by omega
      _ ≤ (16 * 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * ds + 2) + 16) +
            2 * 8 ^ ds * 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * ds + 2) := by
            have ha := Nat.mul_le_mul_left (16 * 2 ^ (x.dist.length - 1)) hL2_le
            have hb := Nat.mul_le_mul_left (2 * 8 ^ ds * 2 ^ (x.dist.length - 1)) hL2ds_le
            omega
      _ = (16 + 2 * 8 ^ ds) * 2 ^ (x.dist.length - 1) *
            ((encTSP x).length + 1) ^ (2 * ds + 2) + 16 := by ring
  have hit := ComputableInO.iterate hcnt hinit hstep (R := R) (Q := R) (B := B)
    hstep_cost hstep_cost fun x k hk => (hst_bound x k hk).2.2.2.2
  have hfin := (ComputableInO.snd _ _).comp hit
  have hlast := computableInO_lastRow.comp hfin
  have hval := ComputableInO.optionGetD 0 ((ComputableInO.headD' none).comp hlast)
  have hpoly_cnt : PolyBounded (fun x : TSPInstance => (encTSP x).length)
      (fun x => Tcnt x + Scnt x + (encNat ((x.dist.length - 1) * (x.dist.length - 1))).length +
        x.dist.length) := by
    growth_poly
  obtain ⟨c, d, hcd⟩ := hpoly_cnt.exists_le
  let e := 2 * max d d₀ + 2 * ds + 4
  have hmono_bound : ∀ x : TSPInstance,
      Tcnt x + 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ d₀ +
        ((x.dist.length - 1) * (x.dist.length - 1) + 1) *
          (R x + B x + ((encNat ((x.dist.length - 1) * (x.dist.length - 1))).length + 1) ^ 2) +
        (encHKState (hkStep^[((x.dist.length - 1) * (x.dist.length - 1))] (hkInit x))).length +
        ((encList encRow (hkStep^[((x.dist.length - 1) * (x.dist.length - 1))]
          (hkInit x)).2).length +
          (hkStep^[((x.dist.length - 1) * (x.dist.length - 1))] (hkInit x)).2.length *
            (listMax (fun r => (encRow r).length)
              (hkStep^[((x.dist.length - 1) * (x.dist.length - 1))] (hkInit x)).2 + 1)) +
        (encRow ((hkStep^[((x.dist.length - 1) * (x.dist.length - 1))]
          (hkInit x)).2.foldl (fun _ r => r) [])).length ≤
        (4 * c ^ 2 + 2 ^ 4 * 8 ^ ds + 250) *
          (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e) ∧
      Scnt x + 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ d₀ + R x + B x +
        (encNat ((x.dist.length - 1) * (x.dist.length - 1))).length +
        (encHKState (hkStep^[((x.dist.length - 1) * (x.dist.length - 1))] (hkInit x))).length +
        ((encList encRow (hkStep^[((x.dist.length - 1) * (x.dist.length - 1))]
          (hkInit x)).2).length +
          listMax (fun r => (encRow r).length)
            (hkStep^[((x.dist.length - 1) * (x.dist.length - 1))] (hkInit x)).2) +
        (encRow ((hkStep^[((x.dist.length - 1) * (x.dist.length - 1))]
          (hkInit x)).2.foldl (fun _ r => r) [])).length ≤
        (4 * c ^ 2 + 2 ^ 4 * 8 ^ ds + 250) *
          (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e) := by
    intro x
    have hp := hcd x
    have hk_self : (x.dist.length - 1) * (x.dist.length - 1) ≤
        (x.dist.length - 1) * (x.dist.length - 1) := le_rfl
    obtain ⟨hfin_len, hfin_max, -, -, hfin_st⟩ := hst_bound x _ hk_self
    have hfin_enc : (encList encRow (hkStep^[((x.dist.length - 1) * (x.dist.length - 1))]
        (hkInit x)).2).length ≤ B x := by
      have : (encList encRow (hkStep^[((x.dist.length - 1) * (x.dist.length - 1))]
          (hkInit x)).2).length ≤ (encHKState (hkStep^[((x.dist.length - 1) *
            (x.dist.length - 1))] (hkInit x))).length := by
        rw [show encHKState _ =
          encPair (encPair (encList (encList encNat)) encUnary) (encList encRow) _ from rfl,
          length_encPair]
        omega
      exact this.trans hfin_st
    have hlast_enc : (encRow ((hkStep^[((x.dist.length - 1) * (x.dist.length - 1))]
        (hkInit x)).2.foldl (fun _ r => r) [])).length ≤ 4 * ((encTSP x).length + 1) ^ 2 + 1 :=
      (length_encRow_foldl_last_le _).trans hfin_max
    have hpow1 : 1 ≤ 2 ^ (x.dist.length - 1) := Nat.one_le_two_pow
    have hL_pos : 1 ≤ (encTSP x).length + 1 := Nat.succ_pos _
    have hLe : 1 ≤ ((encTSP x).length + 1) ^ e := Nat.one_le_pow _ _ hL_pos
    have hLd0 : ((encTSP x).length + 1) ^ d₀ ≤ ((encTSP x).length + 1) ^ e :=
      Nat.pow_le_pow_right hL_pos (by omega)
    have hLd : ((encTSP x).length + 1) ^ d ≤ ((encTSP x).length + 1) ^ e :=
      Nat.pow_le_pow_right hL_pos (by omega)
    have hL2 : ((encTSP x).length + 1) ^ 2 ≤ ((encTSP x).length + 1) ^ e :=
      Nat.pow_le_pow_right hL_pos (by omega)
    have hL2ds : ((encTSP x).length + 1) ^ (2 * ds + 2) ≤ ((encTSP x).length + 1) ^ e :=
      Nat.pow_le_pow_right hL_pos (by omega)
    have hcnt_le : (x.dist.length - 1) * (x.dist.length - 1) + 1 ≤ ((encTSP x).length + 1) ^ 2 := by
      have hx : x.dist.length ≤ (encTSP x).length := by
        refine (length_le_length_encList (encList encNat) x.dist).trans ?_
        rw [encTSP_apply]; enc_len
      have : (x.dist.length - 1) ≤ (encTSP x).length := by omega
      nlinarith only [this]
    have hR_le : R x ≤ (32 + 2 * 8 ^ ds) *
        (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * ds + 2)) := by
      have hP := Nat.one_le_pow (2 * ds + 2) ((encTSP x).length + 1) hL_pos
      have hm1 : 16 ≤ 16 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * ds + 2)) :=
        Nat.mul_le_mul_left 16 (Nat.mul_le_mul hpow1 hP)
      change (16 + 2 * 8 ^ ds) * 2 ^ (x.dist.length - 1) *
          ((encTSP x).length + 1) ^ (2 * ds + 2) + 16 ≤ _
      calc (16 + 2 * 8 ^ ds) * 2 ^ (x.dist.length - 1) *
            ((encTSP x).length + 1) ^ (2 * ds + 2) + 16
          ≤ (16 + 2 * 8 ^ ds) * (2 ^ (x.dist.length - 1) *
              ((encTSP x).length + 1) ^ (2 * ds + 2)) +
              16 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * ds + 2)) := by
              have : (16 + 2 * 8 ^ ds) * 2 ^ (x.dist.length - 1) *
                  ((encTSP x).length + 1) ^ (2 * ds + 2) =
                  (16 + 2 * 8 ^ ds) * (2 ^ (x.dist.length - 1) *
                  ((encTSP x).length + 1) ^ (2 * ds + 2)) := by ring
              omega
        _ = (32 + 2 * 8 ^ ds) *
            (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * ds + 2)) := by ring
    have hB_le : B x ≤ 32 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) := by
      have hP := Nat.one_le_pow 2 ((encTSP x).length + 1) hL_pos
      have hm1 : 16 ≤ 16 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) :=
        Nat.mul_le_mul_left 16 (Nat.mul_le_mul hpow1 hP)
      change 16 * 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2 + 16 ≤ _
      calc 16 * 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2 + 16
          ≤ 16 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) +
              16 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) := by
              have : 16 * 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2 =
                  16 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) := by ring
              omega
        _ = 32 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) := by ring
    have hnat_sq : ((encNat ((x.dist.length - 1) * (x.dist.length - 1))).length + 1) ^ 2 ≤
        (c + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * d) := by
      have h1 : (encNat ((x.dist.length - 1) * (x.dist.length - 1))).length + 1 ≤
          (c + 1) * ((encTSP x).length + 1) ^ d := by
        have hLd' : 1 ≤ ((encTSP x).length + 1) ^ d := Nat.one_le_pow _ _ hL_pos
        nlinarith only [hp, hLd']
      calc _ ≤ ((c + 1) * ((encTSP x).length + 1) ^ d) ^ 2 := Nat.pow_le_pow_left h1 2
        _ = (c + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * d) := by
            rw [Nat.mul_pow, ← pow_mul, mul_comm d 2]
    have hmul_RB : ((x.dist.length - 1) * (x.dist.length - 1) + 1) *
          (R x + B x + ((encNat ((x.dist.length - 1) * (x.dist.length - 1))).length + 1) ^ 2) ≤
        ((c + 1) ^ 2 + 64 + 2 * 8 ^ ds) *
          (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e) := by
      have hL_add : ((encTSP x).length + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * ds + 2) ≤
          ((encTSP x).length + 1) ^ e := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right hL_pos (by omega)
      have hL_add2 : ((encTSP x).length + 1) ^ 2 * ((encTSP x).length + 1) ^ 2 ≤
          ((encTSP x).length + 1) ^ e := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right hL_pos (by omega)
      have hL_add_d : ((encTSP x).length + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * d) ≤
          ((encTSP x).length + 1) ^ e := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right hL_pos (by omega)
      set N := 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e
      have hN1 : (32 + 2 * 8 ^ ds) * (2 ^ (x.dist.length - 1) *
            (((encTSP x).length + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * ds + 2))) ≤
          (32 + 2 * 8 ^ ds) * N :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hL_add)
      have hN2 : 32 * (2 ^ (x.dist.length - 1) *
            (((encTSP x).length + 1) ^ 2 * ((encTSP x).length + 1) ^ 2)) ≤ 32 * N :=
        Nat.mul_le_mul_left 32 (Nat.mul_le_mul_left _ hL_add2)
      have hd1 : ((encTSP x).length + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * d) ≤ N :=
        hL_add_d.trans (Nat.le_mul_of_pos_left _ hpow1)
      have hN3 : (c + 1) ^ 2 * (((encTSP x).length + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * d)) ≤
          (c + 1) ^ 2 * N := Nat.mul_le_mul_left _ hd1
      calc ((x.dist.length - 1) * (x.dist.length - 1) + 1) *
            (R x + B x + ((encNat ((x.dist.length - 1) * (x.dist.length - 1))).length + 1) ^ 2)
          ≤ ((encTSP x).length + 1) ^ 2 *
            ((32 + 2 * 8 ^ ds) *
                (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * ds + 2)) +
             32 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) +
             (c + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * d)) :=
            Nat.mul_le_mul hcnt_le (by omega)
        _ = (32 + 2 * 8 ^ ds) * (2 ^ (x.dist.length - 1) *
              (((encTSP x).length + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * ds + 2))) +
            32 * (2 ^ (x.dist.length - 1) *
              (((encTSP x).length + 1) ^ 2 * ((encTSP x).length + 1) ^ 2)) +
            (c + 1) ^ 2 * (((encTSP x).length + 1) ^ 2 * ((encTSP x).length + 1) ^ (2 * d)) := by
            ring
        _ ≤ (32 + 2 * 8 ^ ds) * N + 32 * N + (c + 1) ^ 2 * N := by omega
        _ = ((c + 1) ^ 2 + 64 + 2 * 8 ^ ds) * N := by ring
    have hfin_mul : (hkStep^[((x.dist.length - 1) * (x.dist.length - 1))] (hkInit x)).2.length *
          (listMax (fun r => (encRow r).length)
            (hkStep^[((x.dist.length - 1) * (x.dist.length - 1))] (hkInit x)).2 + 1) ≤
        6 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e) := by
      calc _ ≤ 2 ^ (x.dist.length - 1) * (4 * ((encTSP x).length + 1) ^ 2 + 2) :=
            Nat.mul_le_mul hfin_len (by omega)
        _ ≤ 2 ^ (x.dist.length - 1) * (6 * ((encTSP x).length + 1) ^ 2) := by
            nlinarith only [hpow1, Nat.one_le_pow 2 ((encTSP x).length + 1) hL_pos]
        _ = 6 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) := by ring
        _ ≤ 6 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e) := by
            exact Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left _ hL2)
    have hc_sq : c ≤ c ^ 2 + 1 := by nlinarith only
    have hc1_sq : (c + 1) ^ 2 ≤ c ^ 2 + 2 * c ^ 2 + 2 := by nlinarith only
    have h8ds : 1 ≤ 8 ^ ds := Nat.one_le_pow _ _ (by decide)
    set N := 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e
    have hpoly_N : ∀ v, v ≤ c * ((encTSP x).length + 1) ^ d → v ≤ (c ^ 2 + 1) * N :=
      fun v hv => hv.trans
        ((Nat.mul_le_mul hc_sq hLd).trans (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hpow1)))
    have hTcnt_le := hpoly_N (Tcnt x) (by omega)
    have hScnt_le := hpoly_N (Scnt x) (by omega)
    have hnat_le := hpoly_N (encNat ((x.dist.length - 1) * (x.dist.length - 1))).length (by omega)
    have hL2_N : ((encTSP x).length + 1) ^ 2 ≤ N :=
      hL2.trans (Nat.le_mul_of_pos_left _ hpow1)
    have hd0_N : 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ d₀ ≤ N :=
      Nat.mul_le_mul_left _ hLd0
    have hR_N : R x ≤ (32 + 2 * 8 ^ ds) * N :=
      hR_le.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hL2ds))
    have hB_N : B x ≤ 32 * N :=
      hB_le.trans (Nat.mul_le_mul_left 32 (Nat.mul_le_mul_left _ hL2))
    have hfin_st' : (encHKState (hkStep^[((x.dist.length - 1) *
        (x.dist.length - 1))] (hkInit x))).length ≤ 32 * N := hfin_st.trans hB_N
    have hfin_enc' : (encList encRow (hkStep^[((x.dist.length - 1) * (x.dist.length - 1))]
        (hkInit x)).2).length ≤ 32 * N := hfin_enc.trans hB_N
    have hlast_N : (encRow ((hkStep^[((x.dist.length - 1) * (x.dist.length - 1))]
        (hkInit x)).2.foldl (fun _ r => r) [])).length ≤ 5 * N := by
      have : 1 ≤ N := Nat.mul_pos hpow1 hLe
      omega
    have hfin_max_N : listMax (fun r => (encRow r).length)
        (hkStep^[((x.dist.length - 1) * (x.dist.length - 1))] (hkInit x)).2 ≤ 5 * N := by
      have : 1 ≤ N := Nat.mul_pos hpow1 hLe
      omega
    have hc1_N : (c + 1) ^ 2 * N ≤ (3 * c ^ 2 + 2) * N := Nat.mul_le_mul_right N (by omega)
    have hm16 : (4 * c ^ 2 + 2 ^ 4 * 8 ^ ds + 250) * N =
        (4 * c ^ 2 + 16 * 8 ^ ds + 250) * N := by norm_num
    refine ⟨?_, ?_⟩
    · have hRB_N : ((x.dist.length - 1) * (x.dist.length - 1) + 1) *
            (R x + B x + ((encNat ((x.dist.length - 1) * (x.dist.length - 1))).length + 1) ^ 2) ≤
          (3 * c ^ 2 + 2) * N + (64 + 2 * 8 ^ ds) * N := by
        have hsplit : ((c + 1) ^ 2 + 64 + 2 * 8 ^ ds) * N =
            (c + 1) ^ 2 * N + (64 + 2 * 8 ^ ds) * N := by ring
        omega
      have htot : (c ^ 2 + 1) * N + N + ((3 * c ^ 2 + 2) * N + (64 + 2 * 8 ^ ds) * N) +
            32 * N + (32 * N + 6 * N) + 5 * N ≤
          (4 * c ^ 2 + 16 * 8 ^ ds + 250) * N := by
        calc (c ^ 2 + 1) * N + N + ((3 * c ^ 2 + 2) * N + (64 + 2 * 8 ^ ds) * N) +
              32 * N + (32 * N + 6 * N) + 5 * N
            = (4 * c ^ 2 + 2 * 8 ^ ds + 143) * N := by ring
          _ ≤ (4 * c ^ 2 + 16 * 8 ^ ds + 250) * N := Nat.mul_le_mul_right N (by omega)
      omega
    · have htot : (c ^ 2 + 1) * N + N + (32 + 2 * 8 ^ ds) * N + 32 * N + (c ^ 2 + 1) * N +
            32 * N + (32 * N + 5 * N) + 5 * N ≤
          (4 * c ^ 2 + 16 * 8 ^ ds + 250) * N := by
        calc (c ^ 2 + 1) * N + N + (32 + 2 * 8 ^ ds) * N + 32 * N + (c ^ 2 + 1) * N +
              32 * N + (32 * N + 5 * N) + 5 * N
            = (2 * c ^ 2 + 2 * 8 ^ ds + 141) * N := by ring
          _ ≤ (4 * c ^ 2 + 16 * 8 ^ ds + 250) * N := Nat.mul_le_mul_right N (by omega)
      omega
  refine ⟨e, hval.mono (4 * c ^ 2 + 2 ^ 4 * 8 ^ ds + 250) (fun x => ?_) (fun x => ?_)⟩
  · exact (hmono_bound x).1.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
  · exact (hmono_bound x).2.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))

@[growth_poly]
private theorem length_encNat_tmOptCost_le (x : TSPInstance) :
    (encNat (tmOptCost x)).length ≤ 4 * ((encTSP x).length + 1) ^ 2 + 2 := by
  unfold tmOptCost
  cases hx : x.dist.length with
  | zero =>
    have hxnil : x.dist = [] := List.length_eq_zero_iff.1 hx
    simp only [Nat.zero_sub, Nat.zero_mul, Function.iterate_zero_apply, hkInit, initTable,
      hxnil, row0, List.length_nil, List.range_zero, List.map_nil, noneRow, List.replicate_zero,
      List.foldl_cons, List.foldl_nil, List.headD_nil, Option.getD_none]
    have h0 : (encNat 0).length ≤ 1 := by simp [encNat_apply]
    omega
  | succ n =>
    rw [Nat.add_sub_cancel]
    obtain ⟨-, -, hrow, -, -⟩ := hkState_size_bound x hx le_rfl
    set fin := (hkStep^[n * n] (hkInit x)).2
    have hlast_max : (encRow (fin.foldl (fun _ r => r) [])).length ≤
        4 * ((encTSP x).length + 1) ^ 2 :=
      (length_encRow_foldl_last_le fin).trans (listMax_le hrow)
    set last := fin.foldl (fun _ r => r) []
    rcases hhead : last.headD none with _ | v
    · change (encNat ((last.headD none).getD 0)).length ≤ _
      rw [hhead, Option.getD_none]
      have h0 : (encNat 0).length ≤ 1 := by simp [encNat_apply]
      omega
    · change (encNat ((last.headD none).getD 0)).length ≤ _
      rw [hhead, Option.getD_some]
      cases hlast : last with
      | nil => simp [hlast] at hhead
      | cons a rest =>
        rw [hlast, List.headD_cons] at hhead
        cases hhead
        have hv : (encNat v).length ≤ (encRow (some v :: rest)).length := by
          simp only [encRow, encList_cons, encOption_some, List.length_append, length_frame,
            List.length_cons]
          omega
        rw [hlast] at hlast_max
        omega

private theorem computableInO_tmDecide :
    ∃ e, ComputableInO tmDecide encTSP encBool
      (fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e)
      (fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e) := by
  have hdist : ComputableInPolyTime TSPInstance.dist encTSP (encList (encList encNat)) := by
    fun_prop
  have hzero_poly : ComputableInPolyTime (fun x : TSPInstance => decide (x.dist.length = 0))
      encTSP encBool :=
    ComputableInDegree.unary_isZero.computableInPolyTime.comp ((length_list _).comp hdist)
  obtain ⟨Tz, Sz, hTz, hSz, hzero⟩ := hzero_poly.exists_computableInO
  obtain ⟨e₀, hopt⟩ := computableInO_tmOptCost
  have hbound_poly : ComputableInPolyTime TSPInstance.bound encTSP encNat := by fun_prop
  obtain ⟨Tb, Sb, hTb, hSb, hbound⟩ := hbound_poly.exists_computableInO
  obtain ⟨Tle, Sle, hTle, hSle, hle⟩ := ComputableInPolyTime.binary_le.exists_computableInO
  have hcmp := hle.comp (hopt.prod hbound)
  have hif := (hzero.ite (ComputableInO.const true) hcmp).of_enc_eq (g := tmDecide)
    (encC := encBool) fun x => by
    unfold tmDecide
    cases hx : x.dist.length with
    | zero => simp
    | succ n => simp
  have hpoly_all : PolyBounded (fun x : TSPInstance => (encTSP x).length)
      (fun x => Tz x + Sz x + Tb x + Sb x +
        (Tle (tmOptCost x, x.bound) + Sle (tmOptCost x, x.bound))) := by
    growth_poly
  obtain ⟨c, d, hcd⟩ := hpoly_all.exists_le
  let e := max e₀ d + 1
  refine ⟨e, hif.mono (c + 4) (fun x => ?_) (fun x => ?_)⟩
  all_goals
    have hp := hcd x
    have hpow1 : 1 ≤ 2 ^ (x.dist.length - 1) := Nat.one_le_two_pow
    have hL_pos : 1 ≤ (encTSP x).length + 1 := Nat.succ_pos _
    have hLe0 : ((encTSP x).length + 1) ^ e₀ ≤ ((encTSP x).length + 1) ^ e :=
      Nat.pow_le_pow_right hL_pos (by omega)
    have hLd : ((encTSP x).length + 1) ^ d ≤ ((encTSP x).length + 1) ^ e :=
      Nat.pow_le_pow_right hL_pos (by omega)
    have hL1 : (encTSP x).length ≤ ((encTSP x).length + 1) ^ e :=
      (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
    set N := 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e
    have hcN : c * ((encTSP x).length + 1) ^ d ≤ c * N :=
      Nat.mul_le_mul_left c (hLd.trans (Nat.le_mul_of_pos_left _ hpow1))
    have hLN : (encTSP x).length ≤ N := hL1.trans (Nat.le_mul_of_pos_left _ hpow1)
    have h2e0 : 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e₀ ≤ N :=
      Nat.mul_le_mul_left _ hLe0
    have hsum : (c + 4) * (N + 1) = c * N + 4 * N + c + 4 := by ring
    split_ifs <;> omega

end TuringRealization

/-- **`TSP` in exponential time `2 ^ (n - 1) · poly(|encTSP x|)` on multi-tape Turing machines.**
`heldKarpDecide` is computable within time and space
`O(2 ^ (x.dist.length - 1) · (|encTSP x| + 1) ^ e)` for some polynomial exponent `e`. -/
theorem exists_computableInO_heldKarpDecide :
    ∃ e : ℕ, Turing.MultiTapeTM.ComputableInO heldKarpDecide encTSP Turing.MultiTapeTM.encBool
      (fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e)
      (fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e) := by
  obtain ⟨e, h⟩ := computableInO_tmDecide
  exact ⟨e, h.of_enc_eq fun x =>
    congrArg Turing.MultiTapeTM.encBool (tmDecide_eq_heldKarpDecide x).symm⟩

/-- **`TSP` is in `DTIME(2 ^ (n - 1) · poly(|encTSP x|))`** on multi-tape Turing machines, where
`n = x.dist.length` is the number of cities (`μ x = x.dist.length - 1`, `δ = 1`). -/
theorem decidableInExpTime :
    DecidableInExpTime TSP encTSP (fun x => x.dist.length - 1) 1 := by
  obtain ⟨e, ⟨c, hc, hT⟩⟩ := exists_computableInO_heldKarpDecide
  refine DecidableInExpTime.of_computableInO ⟨c, hc, hT⟩
    (fun x => (heldKarpDecide_eq_true_iff x).symm) 1 e fun x => ?_
  simp only [one_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
    Real.rpow_natCast]
  exact le_rfl

end Cslib.Complexity.TSP

namespace Cslib.Complexity.HamCycle

open Turing.MultiTapeTM

/-- Deciding `HamCycle` by reducing to `TSP` via `HamCycle.toTSP` and running
`TSP.heldKarpDecide`. -/
theorem heldKarpDecide_toTSP_eq_true_iff (G : Graph) :
    TSP.heldKarpDecide (toTSP G) = true ↔ G ∈ HamCycle :=
  (TSP.heldKarpDecide_eq_true_iff (toTSP G)).trans (toTSP_mem_iff G)

/-- **`HamCycle` in exponential time `2 ^ (n - 1) · poly(|encGraph G|)` on multi-tape Turing
machines**, where `n = G.distinctVertices.length`. -/
theorem exists_computableInO_heldKarpDecide_toTSP :
    ∃ e : ℕ, ComputableInO (fun G => TSP.heldKarpDecide (toTSP G)) encGraph encBool
      (fun G => 2 ^ (G.distinctVertices.length - 1) * ((encGraph G).length + 1) ^ e)
      (fun G => 2 ^ (G.distinctVertices.length - 1) * ((encGraph G).length + 1) ^ e) := by
  obtain ⟨e₀, hHK⟩ := TSP.exists_computableInO_heldKarpDecide
  obtain ⟨Tr, Sr, hTr, hSr, hred⟩ := computableInPolyTime_toTSP.exists_computableInO
  have hcomp := hHK.comp hred
  have hpoly : PolyBounded (fun G : Graph => (encGraph G).length)
      (fun G => Tr G + Sr G + ((encTSP (toTSP G)).length + 1) ^ e₀) := by
    growth_poly [computableInPolyTime_toTSP]
  obtain ⟨c, d, hcd⟩ := hpoly.exists_le
  refine ⟨d, hcomp.mono (2 * c + 2) (fun G => ?_) (fun G => ?_)⟩
  all_goals
    have hlen_le : (toTSP G).dist.length - 1 ≤ G.distinctVertices.length - 1 := by
      unfold toTSP
      split_ifs <;> simp
    have hpow : 2 ^ ((toTSP G).dist.length - 1) ≤ 2 ^ (G.distinctVertices.length - 1) :=
      Nat.pow_le_pow_right (by decide) hlen_le
    have hpow1 : 1 ≤ 2 ^ (G.distinctVertices.length - 1) := Nat.one_le_two_pow
    have hp := hcd G
    set M := 2 ^ (G.distinctVertices.length - 1) * ((encGraph G).length + 1) ^ d
    have hpow_d : ((encGraph G).length + 1) ^ d ≤ M :=
      Nat.le_mul_of_pos_left _ hpow1
    have hc_le : c * ((encGraph G).length + 1) ^ d ≤ c * M := Nat.mul_le_mul_left c hpow_d
    have h1_le : 1 ≤ ((encGraph G).length + 1) ^ d :=
      Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hexp : 2 ^ ((toTSP G).dist.length - 1) * ((encTSP (toTSP G)).length + 1) ^ e₀ ≤ c * M := by
      calc 2 ^ ((toTSP G).dist.length - 1) * ((encTSP (toTSP G)).length + 1) ^ e₀
          ≤ 2 ^ (G.distinctVertices.length - 1) * (c * ((encGraph G).length + 1) ^ d) :=
            Nat.mul_le_mul hpow (by omega)
        _ = c * M := by ring
    have hmul : (2 * c + 2) * (M + 1) = 2 * (c * M) + 2 * M + 2 * c + 2 := by ring
    omega

/-- **`HamCycle` is in `DTIME(2 ^ (n - 1) · poly(|encGraph G|))`** on multi-tape Turing machines,
where `n = G.distinctVertices.length` (`μ G = G.distinctVertices.length - 1`, `δ = 1`). -/
theorem decidableInExpTime :
    DecidableInExpTime HamCycle encGraph (fun G => G.distinctVertices.length - 1) 1 := by
  obtain ⟨e, h⟩ := exists_computableInO_heldKarpDecide_toTSP
  refine DecidableInExpTime.of_computableInO h
    (fun G => (heldKarpDecide_toTSP_eq_true_iff G).symm) 1 e fun G => ?_
  simp only [one_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
    Real.rpow_natCast]
  exact le_rfl

end Cslib.Complexity.HamCycle
