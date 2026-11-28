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
      dsimp only; omega
    have hLnd : L.Nodup :=
      (hLmap ▸ (List.nodup_cons.1 hnd).2 : (L.map _).Nodup).of_map _
    have hLuniv : L.toFinset = Finset.univ := by
      ext i
      simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
      obtain ⟨j, hj, hji⟩ := List.mem_map.1 (hLmap.symm ▸ (List.mem_cons.1
        (hp'.symm.subset (List.mem_range.2 (Nat.succ_lt_succ i.isLt)))).resolve_left
          (Nat.succ_ne_zero i))
      exact Fin.ext (by omega : (j : ℕ) = i) ▸ hj
    calc heldKarp d ≤ walkCost d 0 (L.map Fin.succ) 0 :=
          (isLeast_heldKarp d).2 ⟨L, hLnd, hLuniv, rfl⟩
      _ = tourLength x.dist (A ++ 0 :: B) := by rw [walkCost_succ_eq_tourLength, hLmap, hrot]
      _ ≤ x.bound := hb
  · intro h
    obtain ⟨⟨L, hnd, hL, hc⟩, -⟩ := isLeast_heldKarp d
    refine ⟨0 :: L.map fun i : Fin n => (i : ℕ) + 1, ?_,
      walkCost_succ_eq_tourLength x.dist L ▸ (hc ▸ h)⟩
    rw [hn]
    refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 fun v => ?_
    · exact List.nodup_cons.2 ⟨by simp, hnd.map fun i j h => Fin.ext (by simpa using h)⟩
    · simp only [List.mem_cons, List.mem_map, List.mem_range]
      refine ⟨?_, fun hv => ?_⟩
      · rintro (rfl | ⟨i, -, rfl⟩) <;> omega
      · rcases v with _ | v
        · exact Or.inl rfl
        · exact Or.inr ⟨⟨v, by omega⟩, List.mem_toFinset.1 (hL.symm ▸ Finset.mem_univ _), rfl⟩

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
    exact iff_of_true rfl ⟨[], by simp [h],
      by simp [tourLength]⟩
  · rename_i n h
    exact decide_eq_true_iff.trans (mem_TSP_iff_heldKarp_le h).symm

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
  fun_induction interleave xs ys <;> simp [*]
  omega

private theorem mem_interleave {α : Type*} {xs ys : List α} {z : α} :
    z ∈ interleave xs ys ↔ z ∈ xs ∨ z ∈ ys := by
  fun_induction interleave xs ys <;> simp [*]
  tauto

private theorem evens_interleave {α : Type*} (xs ys : List α) (h : xs.length = ys.length) :
    evens (interleave xs ys) = xs := by
  induction xs generalizing ys <;> cases ys <;> simp_all [interleave, evens]

private theorem passOddsList_interleave {α : Type*} (f : α → α → α) (xs ys : List α)
    (h : xs.length = ys.length) :
    passOddsList f (interleave xs ys) = List.zipWith f xs ys := by
  induction xs generalizing ys <;> cases ys <;> simp_all [interleave, passOddsList]

private theorem interleave_append {α : Type*} (xs₁ ys₁ xs₂ ys₂ : List α)
    (h : xs₁.length = ys₁.length) :
    interleave xs₁ ys₁ ++ interleave xs₂ ys₂ = interleave (xs₁ ++ xs₂) (ys₁ ++ ys₂) := by
  induction xs₁ generalizing ys₁ <;> cases ys₁ <;> simp_all [interleave]

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
    have key : ∀ (a₁ b₁ a₂ b₂ : List α), a₁.length = b₁.length → a₂.length = b₂.length →
        a₁.length = a₂.length →
        List.zipWith f (interleave a₁ b₁) (interleave a₂ b₂) =
          interleave (List.zipWith f a₁ a₂) (List.zipWith f b₁ b₂) := by
      intro a₁ b₁ a₂ b₂ h1 h2 h12
      induction a₁ generalizing b₁ a₂ b₂ <;> cases b₁ <;> cases a₂ <;> cases b₂ <;>
        simp only [List.length_cons, List.length_nil] at h1 h2 h12 <;> try omega
      · simp [interleave]
      · simp only [interleave, List.zipWith_cons_cons, List.cons.injEq, true_and]
        apply_assumption <;> omega
    rw [tabulateLSB, tabulateLSB, tabulateLSB,
      key _ _ _ _ (by simp [length_tabulateLSB])
        (by simp [length_tabulateLSB])
        (by simp [length_tabulateLSB]), ih, ih]

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
  match xs, ys with
  | _, [] => exact absurd rfl hne
  | [], _ :: _ | [_], _ :: _ :: _ | _ :: _ :: _, [_] => simp at h
  | [_], [_] => simp [interleave]
  | _ :: x' :: xs', _ :: y' :: ys' =>
    have hlen : (x' :: xs').length = (y' :: ys').length := by
      simp only [List.length_cons] at h ⊢; omega
    simpa [interleave] using getLast?_interleave (x' :: xs') (y' :: ys') hlen (List.cons_ne_nil _ _)

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
  have hfl (l : List α) : ∀ d, l ≠ [] → some (l.foldl (fun _ x => x) d) = l.getLast? := by
    induction l with
    | nil => exact fun _ hne => absurd rfl hne
    | cons a t ih =>
      cases t with
      | nil => exact fun _ _ => rfl
      | cons b t => exact fun _ _ => ih a (List.cons_ne_nil _ _)
  refine Option.some.inj ((hfl (tabulateLSB m g) d ?_).trans (getLast?_tabulateLSB m g))
  intro he
  simpa [length_tabulateLSB] using congrArg List.length he

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
    simp only [hlen, Nat.add_sub_of_le j.isLt.le, Nat.mod_self, List.getElem_cons_zero, ↓reduceIte]
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
    simp only [hlen, hlenf, hk, List.getElem_cons_succ]

private theorem setOfBits_rotate_true {n i : ℕ} (hi : i < n) (r : List Bool)
    (hr : r.length + 1 = n) :
    setOfBits n ((true :: r).rotate (n - i)) =
      insert ⟨i, hi⟩ (setOfBits n ((false :: r).rotate (n - i))) := by
  ext j
  simp only [setOfBits, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.ext_iff, getD_rotate_cons hi true r hr false j]
  by_cases hji : j.val = i <;> simp [hji]

private theorem setOfBits_rotate_true_erase {n i : ℕ} (hi : i < n) (r : List Bool)
    (hr : r.length + 1 = n) :
    (setOfBits n ((true :: r).rotate (n - i))).erase ⟨i, hi⟩ =
      setOfBits n ((false :: r).rotate (n - i)) := by
  rw [setOfBits_rotate_true hi r hr, Finset.erase_insert]
  simp only [setOfBits, Finset.mem_filter, Finset.mem_univ, true_and,
    getD_rotate_cons hi false r hr false ⟨i, hi⟩, ↓reduceIte, Bool.false_eq_true, not_false_eq_true]

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
  · rw [rotate_cons_rotate_sub hi false r (by omega)]
    have hnot : (⟨i, hi⟩ : Fin (m + 1)) ∉ setOfBits (m + 1) ((false :: r).rotate (m + 1 - i)) := by
      simp only [setOfBits, Finset.mem_filter, Finset.mem_univ, true_and,
        getD_rotate_cons hi false r (by omega) false ⟨i, hi⟩, ↓reduceIte, Bool.false_eq_true,
        not_false_eq_true]
    simp [hnot]
  · rw [rotate_cons_rotate_sub hi true r (by omega)]
    have hmem : (⟨i, hi⟩ : Fin (m + 1)) ∈ setOfBits (m + 1) ((true :: r).rotate (m + 1 - i)) := by
      simp only [setOfBits, Finset.mem_filter, Finset.mem_univ, true_and,
        getD_rotate_cons hi true r (by omega) false ⟨i, hi⟩, ↓reduceIte]
    simp [hmem, setOfBits_rotate_true_erase hi r (by omega)]

/-! ### Streaming list-pass combinator and DP correctness -/

/-- A machine running within `t` and `s` is `ComputableInO` for asymptotically larger bounds. -/
private theorem computableInO_of_bigO {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} {t s T S : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s) (hT : t ≼ T) (hS : s ≼ S)
    (hl : (fun a => (encOut (f a)).length) ≼ S) : ComputableInO f encIn encOut T S := by
  obtain ⟨k₁, h₁⟩ := hT
  obtain ⟨k₂, h₂⟩ := hS
  obtain ⟨k₃, h₃⟩ := hl
  exact .of_bounds h (k₁ + k₂ + k₃) (fun a => (h₁ a).trans (Nat.mul_le_mul_right _ (by omega)))
    (fun a => (h₂ a).trans (Nat.mul_le_mul_right _ (by omega)))
    (fun a => (h₃ a).trans (Nat.mul_le_mul_right _ (by omega)))

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
    have ih := evens_odds_streamEmit rest b
    cases b <;> simpa [evens, odds, streamEmit, encList_cons, encList_nil] using ih

private theorem length_encList_evens_or_odds_le (b : Bool) (L : List Row) :
    (encList encRow (if b then evens L else odds L)).length ≤ (encList encRow L).length := by
  match L with
  | [] => cases b <;> simp [evens, odds]
  | [a] => cases b <;> simp [evens, odds]
  | a :: b' :: rest =>
    have ih := length_encList_evens_or_odds_le b rest
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, odds, evens, encList_cons,
      List.length_append] at ih ⊢ <;> omega

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
    have hpow (L : List Row) : (listMax (fun r => (encRow r).length) L + 1 + 1) ^ d ≤
        2 ^ d * (listMax (fun r => (encRow r).length) L + 1) ^ d :=
      (Nat.pow_le_pow_left (by omega) d).trans_eq (Nat.mul_pow _ _ _)
    refine computableInO_of_bigO h (.const_mul c (.add (.add (.of_le_linear 1 3 fun p => ?_)
      ⟨2 ^ d, fun p => ?_⟩) (.const 1 _))) (.const_mul c (.add ⟨2 ^ d, fun p => ?_⟩ (.const 1 _)))
      (.of_le fun p => (length_encList_evens_or_odds_le p.1 p.2).trans (Nat.le_add_right _ _))
    · rw [length_encPair]
      cases p.1 <;> simp only [encBool_apply, List.length_singleton] <;> omega
    · refine (Nat.mul_le_mul_left _ (hpow p.2)).trans ?_
      rw [Nat.mul_left_comm]
      exact Nat.mul_le_mul_left _ (Nat.le_succ_of_le (Nat.le_add_left _ _))
    · exact (hpow p.2).trans (Nat.mul_le_mul_left _ (Nat.le_succ_of_le (Nat.le_add_left _ _)))
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
        exact ⟨h1, h2.imp_right fun h => h.elim (fun h => Or.inr ⟨a, ha, h⟩) Or.inr⟩
      | some _ =>
        obtain ⟨h1, h2⟩ := ih hsub' none
        exact ⟨h1, h2.elim Or.inl fun h => h.elim Or.inl (Or.inr ∘ Or.inr)⟩
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
    have hpow (q : OddState × List Row) :
        (2 * (encOddParams q.1.1).length + 2 * (encOption encRow q.1.2).length +
            listMax (fun r => (encRow r).length) q.2 + 4 + 1) ^ d ≤
          5 ^ d * (listMax (fun r => (encRow r).length) q.2 +
            (encOddParams q.1.1).length + (encOption encRow q.1.2).length + 1) ^ d :=
      (Nat.pow_le_pow_left (by omega) d).trans_eq (Nat.mul_pow _ _ _)
    refine computableInO_of_bigO h ?hT (.const_mul c (.add ⟨5 ^ d, fun q => ?_⟩ (.const 1 _)))
      ((BigOLe.of_le h.length_le).trans ?hT)
    · refine .const_mul c (.add (.add (.of_le_linear 4 3 fun q => ?_) ⟨5 ^ d, fun q => ?_⟩)
        (.const 1 _))
      · simp only [length_encPair]
        omega
      · refine (Nat.mul_le_mul_left _ (hpow q)).trans ?_
        rw [Nat.mul_left_comm]
        exact Nat.mul_le_mul_left _ (Nat.le_succ_of_le (Nat.le_add_left _ _))
    · exact (hpow q).trans (Nat.mul_le_mul_left _ (Nat.le_succ_of_le
        ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans (Nat.le_add_left _ _))))
  refine ⟨d, (haux.comp hwrap).mono 4 (fun p => ?_) (fun p => ?_)⟩
  · rw [length_encPair, add_comm (listMax _ p.2) (encOddParams p.1).length]
    simp only [encOption_none, List.length_nil, add_zero]; omega
  · rw [length_encPair]
    simp only [encOption_none, List.length_nil, add_zero]; omega

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
  have hlen (L : List Row) (j : ℕ) (hj : j < L.length) :
      (encPair encRow encRow (streamState [] Prod.snd L j, L[j])).length + 1 ≤
        3 * (listMax (fun r => (encRow r).length) L + 1) := by
    have h0 := hstate_le L j
    have ha := le_listMax (f := fun r => (encRow r).length) (List.getElem_mem hj)
    rw [length_encPair]
    simp only [streamState] at h0 ⊢
    omega
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
    (roundCost := fun p _ =>
      (3 * cnext + 2 * ce + 6) * (listMax (fun r => (encRow r).length) p.2 + 1))
    (sMax := fun p => cnext * (3 * (listMax (fun r => (encRow r).length) p.2 + 1)))
    (lMax := fun p => listMax (fun r => (encRow r).length) p.2)
    (fun p j hj => by
      have h0 := hstate_le p.2 j
      have h1 := hstate_le p.2 (j + 1)
      have ha := le_listMax (f := fun r => (encRow r).length) (List.getElem_mem hj)
      have hl := Nat.mul_le_mul_left cnext (hlen p.2 j hj)
      have hM := Nat.zero_le (ce * listMax (fun r => (encRow r).length) p.2)
      simp only [streamState] at h0 h1 hl ⊢
      nlinarith)
    (fun p j hj => (Nat.add_zero _).trans_le (Nat.mul_le_mul_left _ (hlen p.2 j hj)))
    (fun p j _ => hstate_le p.2 j)
    (fun p j hj => le_listMax (f := fun r => (encRow r).length) (List.getElem_mem hj))
  have hwrap : ComputableInO (fun L : List Row => ((), L))
      (encList encRow) (encPair encUnit (encList encRow))
      (fun L => (encList encRow L).length) (fun L => (encList encRow L).length) := by
    have hp := (ComputableInO.const (encIn := encList encRow) (encMid := encUnit) ()).prod
      (ComputableInO.id' (encMid := encList encRow))
    exact hp.mono 2 (fun _ => by omega) (fun _ => by omega)
  have hf (L : List Row) : (encRow (L.foldl (fun _ r => r) [])).length ≤
      listMax (fun r => (encRow r).length) L := by
    simpa using hstate_le L L.length
  have hpair : ComputableInO (fun p : Unit × List Row => p.2.foldl (fun _ r => r) [])
      (encPair encUnit (encList encRow)) encRow
      (fun p => (encList encRow p.2).length +
        p.2.length * (listMax (fun r => (encRow r).length) p.2 + 1))
      (fun p => listMax (fun r => (encRow r).length) p.2) := by
    refine computableInO_of_bigO hc.computableInTimeAndSpace
      (.const_mul c (.of_le_linear (3 * cnext + 2 * ce + 9) 6 fun p => ?_))
      (.const_mul c (.of_le_linear (3 * cnext + 1) (3 * cnext + 1) fun p => by nlinarith))
      (.of_le fun p => hf p.2)
    have hlm : listMax (fun r => (encRow r).length) p.2 ≤
        p.2.length * (listMax (fun r => (encRow r).length) p.2 + 1) :=
      listMax_le fun r hr => (le_listMax (f := fun r => (encRow r).length) hr).trans
        ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (List.length_pos_of_mem hr)))
    have := hf p.2
    simp only [streamState, List.take_length, Finset.sum_const, Finset.card_range, smul_eq_mul,
      encPair_apply, encUnit_apply, Turing.MultiTapeTM.frame_nil, List.length_append,
      List.length_singleton]
    nlinarith
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
    nlinarith only [dist_le_maxDist D a x, ih x]

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
          exact Option.some.inj hv ▸ hcand_mem
        | some cur =>
          rw [hcur] at hv
          obtain rfl := Option.some.inj hv
          rcases min_cases cur (u + (D.getD (i + 1) []).getD t.val 0) with ⟨he, -⟩ | ⟨he, -⟩
          · exact he.symm ▸ (hG S).2 t cur hcur
          · exact he.symm ▸ hcand_mem
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
    let G' : Finset (Fin n) → Row := fun S =>
      if ⟨i, hi⟩ ∈ S then
        relaxRow (D.getD (i + 1) []) ((G (S.erase ⟨i, hi⟩)).getD (i + 1) none) (G S)
      else G S
    obtain ⟨hVG', hstep_mono, hstep_relax⟩ := validFun_pass hi hVG
    rw [Function.iterate_succ_apply']
    dsimp only [step]
    rw [hfst, hsnd]
    refine ⟨G', rfl, passStep_tabulateLSB_rotate hn hi _ G, hVG',
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
        rw [Fin.val_mk, hu] at hu₀
        cases hu₀
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
    have hcard_er : (S.erase a₀).card ≤ r := by simp [Finset.card_erase_of_mem ha₀, heq]
    obtain ⟨v, hv, hle_v⟩ := hdone a₀.val a₀.isLt a₀.isLt S ha₀ hcard_er t
    refine ⟨v, hv, (hVG S).2 t v hv, fun w hw => ?_⟩
    obtain ⟨L, hLnd, hLset, rfl⟩ := hw
    have hLne : L ≠ [] := by
      rintro rfl
      simp [← hLset] at hpos
    let L' := L.dropLast
    let j := L.getLast hLne
    have hLsplit : L = L' ++ [j] := (List.dropLast_append_getLast hLne).symm
    have hnd_split : (L' ++ [j]).Nodup := hLsplit ▸ hLnd
    have hj_mem : j ∈ S := hLset ▸ List.mem_toFinset.2 (List.getLast_mem hLne)
    have hnd' : L'.Nodup := (List.nodup_append.1 hnd_split).1
    have hj_nmem : j ∉ L' := fun h =>
      (List.nodup_append.1 hnd_split).2.2 j h j List.mem_cons_self rfl
    have hL'_set : L'.toFinset = S.erase j := by
      rw [← hLset, hLsplit, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
        Finset.union_comm, Finset.insert_union, Finset.empty_union,
        Finset.erase_insert (mt List.mem_toFinset.1 hj_nmem)]
    have hcard_er' : (S.erase j).card ≤ r := by simp [Finset.card_erase_of_mem hj_mem, heq]
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
      obtain rfl : t = 0 := Fin.ext (by omega)
      simp only [G₀, row0, hn_eq, List.range_succ, List.range_zero, List.nil_append,
        List.map_cons, List.map_nil, Fin.val_zero, List.getD_cons_zero] at hv
      obtain rfl := Option.some.inj hv
      exact ⟨[], List.nodup_nil, Subsingleton.elim _ _, rfl⟩⟩
    have hS0 : StageComplete x.dist 0 0 G₀ := ⟨hV0, fun S _ t => by
      obtain ⟨rfl, rfl⟩ : S = ∅ ∧ t = 0 := ⟨Finset.eq_empty_of_isEmpty _, Fin.ext (by omega)⟩
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
        obtain ⟨_, hstep_i, -⟩ := stage_correct hn_pos r G_r hSr i (by omega)
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
        simp only [Nat.sub_self, List.rotate_zero] at hsnd
        rw [(by ring : (r + 1) * n = r * n + n)]
        exact ⟨G_end, hs1, hs2.trans hsnd, hSr1⟩
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
  rw [h2, foldl_last_tabulateLSB, setOfBits_replicate_true]
  obtain ⟨v, hv, hv_least⟩ := hSn.2 Finset.univ (by rw [Finset.card_univ, Fintype.card_fin]) 0
  rw [Fin.val_zero, List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?] at hv
  rw [List.headD_eq_head?_getD, hv, Option.getD_some]
  exact hv_least.unique (isLeast_heldKarp _)

private theorem tmDecide_eq_heldKarpDecide (x : TSPInstance) :
    tmDecide x = heldKarpDecide x := by
  unfold tmDecide heldKarpDecide
  cases h : x.dist.length with
  | zero => rfl
  | succ n =>
    simp only [tmOptCost_eq_heldKarp x h]

private theorem length_dist_le (x : TSPInstance) : x.dist.length ≤ (encTSP x).length :=
  (length_le_length_encList _ _).trans (encTSP_dist_length_le x)

/-- The bounds `2 ^ (n - 1) * (|x| + 1) ^ a` grow with the exponent `a`. -/
private theorem bigO_expBound_mono (a b : ℕ) (h : a ≤ b) :
    (fun x : TSPInstance => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ a) ≼
      fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ b :=
  .of_le fun _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) h)

/-- A polynomial `(|x| + 1) ^ a` is within the bound `2 ^ (n - 1) * (|x| + 1) ^ b` for `a ≤ b`. -/
private theorem bigO_polyBound_expBound (a b : ℕ) (h : a ≤ b) :
    (fun x : TSPInstance => ((encTSP x).length + 1) ^ a) ≼
      fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ b :=
  (BigOLe.of_le fun _ => Nat.le_mul_of_pos_left _ Nat.one_le_two_pow).trans
    (bigO_expBound_mono a b h)

private theorem mod_le_encTSP_length {x : TSPInstance} {n k : ℕ} (hx : x.dist.length = n + 1)
    (hk : k ≤ n * n) : k % n ≤ (encTSP x).length := by
  have hdist_le : (encList (encList encNat) x.dist).length ≤ (encTSP x).length := by
    rw [encTSP_apply]; enc_len
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simp [Nat.eq_zero_of_le_zero hk]
  · have hn_le : n + 1 ≤ (encTSP x).length :=
      hx ▸ (length_le_length_encList (encList encNat) x.dist).trans hdist_le
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
      | zero => exact ⟨[], List.mem_singleton.1 ha⟩
      | succ m ih =>
        rcases mem_interleave.1 ha with h | h <;> obtain ⟨bs, hbs⟩ := ih _ h
        exacts [⟨false :: bs, hbs⟩, ⟨true :: bs, hbs⟩]
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
    64 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2)
  have hrow0_len : ∀ x : TSPInstance, (encRow (row0 x.dist)).length ≤
      3 * ((encTSP x).length + 1) ^ 2 := by
    intro x
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
    nlinarith only [h1, length_dist_le x]
  have hnone_len : ∀ x : TSPInstance, (encRow (noneRow x.dist.length)).length ≤
      3 * (encTSP x).length := by
    intro x
    have hsum : (encList (encOption encNat) (noneRow x.dist.length)).length = x.dist.length := by
      rw [noneRow, length_encList, List.map_replicate, List.sum_replicate, smul_eq_mul]
      simp [encOption_none]
    change (encList (encOption encNat) (noneRow x.dist.length)).length ≤ 3 * (encTSP x).length
    have := length_dist_le x
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
    have hpow : 2 ^ k ≤ 2 ^ (x.dist.length - 1) := Nat.pow_le_pow_right (by decide) hk
    have hnr : 2 * (encRow (noneRow x.dist.length)).length + 1 ≤
        6 * ((encTSP x).length + 1) ^ 2 + 1 := by
      have := hnone_len x
      have := Nat.le_self_pow two_ne_zero ((encTSP x).length + 1)
      omega
    rw [h1, hsum_rep]
    simp only [B]
    nlinarith only [hrow0_len x, Nat.mul_le_mul ((Nat.sub_le _ 1).trans hpow) hnr,
      Nat.mul_le_mul hpow hnr, @Nat.one_le_two_pow (x.dist.length - 1),
      Nat.one_le_pow 2 ((encTSP x).length + 1) (Nat.succ_pos _)]
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
      (fun x => Td x + Sn x + Si x + Tn x + Ti x + (encTSP x).length +
        (encNat (x.dist.length - 1)).length + ((encNat (x.dist.length - 1)).length + 1) ^ 2 +
          Sd x) := by
    growth_poly
  obtain ⟨c, d, hcd⟩ := hpoly_all.exists_le
  -- Every cost is `O(M x)` for `M x = 2 ^ (n - 1) * (|x| + 1) ^ (d + 2)`, except the `n` rounds
  -- of the iteration, which take `O((|x| + 1) * M x)`.
  have hpoly : (fun x => Td x + Sn x + Si x + Tn x + Ti x + (encTSP x).length +
      (encNat (x.dist.length - 1)).length + ((encNat (x.dist.length - 1)).length + 1) ^ 2 +
        Sd x) ≼ fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (d + 2) :=
    .trans ⟨c, fun x => (hcd x).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))⟩
      (bigO_polyBound_expBound d (d + 2) (by omega))
  have hB' : B ≼ fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (d + 2) :=
    .const_mul 64 (bigO_expBound_mono 2 (d + 2) (by omega))
  have hMN := bigO_expBound_mono (d + 2) (d + 3) (by omega)
  refine ⟨d + 3, hinit_all.weaken ?_ ?_⟩
  · refine BigOLe.add (.trans (.of_le fun _ => by omega) (hpoly.trans hMN))
      (BigOLe.add (.trans (.of_le fun _ => by omega) (hpoly.trans hMN)) ?_)
    exact (BigOLe.mul_left _ ((hB'.add hB').add (.trans (.of_le fun _ => by omega) hpoly))
      fun x => Nat.mul_le_mul Nat.one_le_two_pow (Nat.one_le_pow _ _ (Nat.succ_pos _))).trans
        (.of_le fun x => (Nat.mul_le_mul_right _ (Nat.add_le_add_right
          ((Nat.sub_le _ 1).trans (length_dist_le x)) 1)).trans_eq (by ring))
  · exact (BigOLe.add (.trans (.of_le fun _ => by omega) hpoly) (((BigOLe.add
      (.trans (.of_le fun _ => by omega) hpoly) hB').add hB').add
        (.trans (.of_le fun _ => by omega) hpoly))).trans hMN

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
  have hDp : ComputableInPolyTime (fun p : List (List ℕ) × ℕ => p.1)
      encHKParam (encList (encList encNat)) := by fun_prop
  have hip : ComputableInPolyTime (fun p : List (List ℕ) × ℕ => p.2)
      encHKParam encUnary := by fun_prop
  have hnextParam : ComputableInPolyTime
      (fun p : List (List ℕ) × ℕ => (p.1, if p.2 + 1 = p.1.length - 1 then 0 else p.2 + 1))
      encHKParam encHKParam := by
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
    exact (listGetDWithInput hDp (unary_succ.comp hip) []).prod hip
  obtain ⟨T₁, S₁, hT₁, hS₁, hP₁⟩ := hnextParam.exists_computableInO
  obtain ⟨c₁, d₁, hcd₁⟩ := (hT₁.add hS₁).exists_le
  obtain ⟨T₂, S₂, hT₂, hS₂, hP₂⟩ := hrowParam.exists_computableInO
  obtain ⟨c₂, d₂, hcd₂⟩ := (hT₂.add hS₂).exists_le
  have h2 := hP₂.comp (ComputableInO.fst encHKParam (encList encRow))
  have hfull := (hP₁.comp (ComputableInO.fst encHKParam (encList encRow))).prod
    (ComputableInO.listAppend' (hev.comp (ComputableInO.snd encHKParam (encList encRow)))
      (hodds.comp (h2.prod (ComputableInO.snd encHKParam (encList encRow)))))
  let d := max (max d₁ d₂) (max de do_) + 1
  let M : HKState → ℕ := fun st =>
    (encList (encList encNat) st.1.1).length + (encUnary st.1.2).length +
      listMax (fun r => (encRow r).length) st.2 + 1
  -- Every polynomial cost of the step is a multiple of `P st = 4 ^ d * (|st.2| + 1) * M ^ d`.
  let P : HKState → ℕ := fun st => (st.2.length + 1) * (4 * M st) ^ d
  have hP : ∀ st e a, e ≤ d → a ≤ 4 * M st → (st.2.length + 1) * a ^ e ≤ P st :=
    fun st e a he ha => Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left ha e).trans
      (Nat.pow_le_pow_right (by simp only [M]; omega) he))
  have hparam : ∀ (st : HKState) (f : List (List ℕ) × ℕ → ℕ) (c e : ℕ), e ≤ d →
      (∀ p, f p ≤ c * ((encHKParam p).length + 1) ^ e) → f st.1 ≤ c * P st := by
    intro st f c e he hf
    refine (hf st.1).trans (Nat.mul_le_mul_left c ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans
      (hP st e _ he ?_)))
    simp only [encHKParam, length_encPair, M]
    omega
  have hU : (fun st => 6 * (encHKState st).length + c₁ * P st + c₂ * P st + 9 * P st) ≼
      fun st => (encHKState st).length + (st.2.length + 1) * M st ^ d := by
    have hE : (fun st : HKState => (encHKState st).length) ≼
        fun st => (encHKState st).length + (st.2.length + 1) * M st ^ d :=
      .of_le fun _ => Nat.le_add_right _ _
    have hPT : P ≼ fun st => (encHKState st).length + (st.2.length + 1) * M st ^ d :=
      ⟨4 ^ d, fun st => (show P st = 4 ^ d * ((st.2.length + 1) * M st ^ d) by
        simp only [P, mul_pow]; ring).trans_le
          (Nat.mul_le_mul_left _ (Nat.le_succ_of_le (Nat.le_add_left _ _)))⟩
    exact (((hE.const_mul 6).add (hPT.const_mul c₁)).add (hPT.const_mul c₂)).add (hPT.const_mul 9)
  refine ⟨d, hfull.weaken ((BigOLe.of_le fun st => ?_).trans hU)
    ((BigOLe.of_le fun st => ?_).trans hU)⟩
  all_goals
    have hst : (encPair encHKParam (encList encRow) st).length = (encHKState st).length := rfl
    have hL := length_le_encPair_right encHKParam (encList encRow) st
    have hg : (encList encNat (st.1.1.getD (st.1.2 + 1) [])).length ≤
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
    have hpair := length_encPair (enc₁ := encOddParams) (enc₂ := encList encRow)
      ((st.1.1.getD (st.1.2 + 1) [], st.1.2), st.2)
    have hM1 : 1 ≤ M st := by simp only [M]; omega
    have hMP := (Nat.le_mul_of_pos_left (M st) (Nat.succ_pos st.2.length)).trans
      (by simpa only [pow_one] using hP st 1 (M st) (by omega) (by omega))
    have := hparam st T₁ c₁ d₁ (by omega) fun p => (Nat.le_add_right _ _).trans (hcd₁ p)
    have := hparam st S₁ c₁ d₁ (by omega) fun p => (Nat.le_add_left _ _).trans (hcd₁ p)
    have := hparam st T₂ c₂ d₂ (by omega) fun p => (Nat.le_add_right _ _).trans (hcd₂ p)
    have := hparam st S₂ c₂ d₂ (by omega) fun p => (Nat.le_add_left _ _).trans (hcd₂ p)
    have hlm := hP st de (listMax (fun r => (encRow r).length) st.2 + 1) (by omega)
      (by simp only [M]; omega)
    have := Nat.le_mul_of_pos_left (n := st.2.length + 1)
      ((listMax (fun r => (encRow r).length) st.2 + 1) ^ de) (Nat.succ_pos _)
    have := hP st do_ ((encOddParams (st.1.1.getD (st.1.2 + 1) [], st.1.2)).length +
      listMax (fun r => (encRow r).length) st.2 + 1) (by omega) (by simp only [M] at hodd ⊢; omega)
    have := hP st do_ (listMax (fun r => (encRow r).length) st.2 +
      (encOddParams (st.1.1.getD (st.1.2 + 1) [], st.1.2)).length + 1) (by omega)
      (by simp only [M] at hodd ⊢; omega)
    dsimp only [Function.comp_def] at *
    omega

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
    16 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) + 16
  let R : TSPInstance → ℕ := fun x =>
    B x + 2 * 8 ^ ds * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (2 * ds))
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
      simp only [B, hx, Nat.zero_sub, pow_zero, one_mul, List.length_singleton,
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
      refine ⟨h2.le, listMax_le fun r hr => (hrow r hr).trans (Nat.le_succ _), ?_, ?_, ?_⟩
      · rw [h1]; exact (encTSP_dist_length_le x).trans (Nat.le_succ _)
      · rw [h1, encUnary_apply, List.length_replicate]
        exact (mod_le_encTSP_length hx hk).trans (Nat.le_succ _)
      · change (encHKState (hkStep^[k] (hkInit x))).length ≤
          16 * (2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ 2) + 16
        rw [hx, Nat.add_sub_cancel]
        nlinarith only [hst_len, Nat.one_le_pow 2 ((encTSP x).length + 1) (Nat.succ_pos _),
          @Nat.one_le_two_pow n]
  have hstep_cost : ∀ (x : TSPInstance) (k : ℕ), k ≤ (x.dist.length - 1) * (x.dist.length - 1) →
      (encHKState (hkStep^[k] (hkInit x))).length +
        ((hkStep^[k] (hkInit x)).2.length + 1) *
          ((encList (encList encNat) (hkStep^[k] (hkInit x)).1.1).length +
            (encUnary (hkStep^[k] (hkInit x)).1.2).length +
            listMax (fun r => (encRow r).length) (hkStep^[k] (hkInit x)).2 + 1) ^ ds ≤ R x := by
    intro x k hk
    obtain ⟨hlen, hmax, hdist_le, hmod_le, hB_le⟩ := hst_bound x k hk
    have hL := Nat.le_self_pow two_ne_zero ((encTSP x).length + 1)
    have hpow1 : 1 ≤ 2 ^ (x.dist.length - 1) := Nat.one_le_two_pow
    refine Nat.add_le_add hB_le ((Nat.mul_le_mul (by omega : _ ≤ 2 * 2 ^ (x.dist.length - 1))
      (Nat.pow_le_pow_left (by omega : _ ≤ 8 * ((encTSP x).length + 1) ^ 2) ds)).trans_eq ?_)
    rw [Nat.mul_pow, ← pow_mul]
    ring
  have hit := ComputableInO.iterate hcnt hinit hstep (R := R) (Q := R) (B := B)
    hstep_cost hstep_cost fun x k hk => (hst_bound x k hk).2.2.2.2
  have hval := ComputableInO.optionGetD 0 ((ComputableInO.headD' none).comp
    (computableInO_lastRow.comp ((ComputableInO.snd _ _).comp hit)))
  have hpoly_cnt : PolyBounded (fun x : TSPInstance => (encTSP x).length)
      (fun x => Tcnt x + Scnt x + (encNat ((x.dist.length - 1) * (x.dist.length - 1))).length +
        ((encNat ((x.dist.length - 1) * (x.dist.length - 1))).length + 1) ^ 2) := by
    growth_poly
  obtain ⟨c, d, hcd⟩ := hpoly_cnt.exists_le
  -- Every cost is `O(M x)` for `M x = 2 ^ (n - 1) * (|x| + 1) ^ e`, except the
  -- `(n - 1) ^ 2 + 1 ≤ (|x| + 1) ^ 2` rounds of the iteration, which take `O((|x| + 1) ^ 2 * M x)`.
  let e := 2 * max d d₀ + 2 * ds + 2
  let M : TSPInstance → ℕ := fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e
  have hpoly : (fun x => Tcnt x + Scnt x +
      (encNat ((x.dist.length - 1) * (x.dist.length - 1))).length +
        ((encNat ((x.dist.length - 1) * (x.dist.length - 1))).length + 1) ^ 2) ≼ M :=
    .trans ⟨c, fun x => (hcd x).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))⟩
      (bigO_polyBound_expBound d e (by omega))
  have hinitM := bigO_expBound_mono d₀ e (by omega)
  have hB : B ≼ M :=
    BigOLe.add (.const_mul 16 (bigO_expBound_mono 2 e (by omega))) (.const 16 _)
  have hR : R ≼ M := hB.add (.const_mul _ (bigO_expBound_mono (2 * ds) e (by omega)))
  have hcnt_le : ∀ x : TSPInstance, (x.dist.length - 1) * (x.dist.length - 1) + 1 ≤
      ((encTSP x).length + 1) ^ 2 := fun x => by
    have : x.dist.length - 1 ≤ (encTSP x).length := (Nat.sub_le _ _).trans (length_dist_le x)
    nlinarith only [this]
  have hprod : (fun x => ((x.dist.length - 1) * (x.dist.length - 1) + 1) *
      (R x + B x + ((encNat ((x.dist.length - 1) * (x.dist.length - 1))).length + 1) ^ 2)) ≼
        fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (e + 2) :=
    (BigOLe.mul_left _ ((hR.add hB).add (.trans (.of_le fun _ => by omega) hpoly))
      fun x => Nat.mul_le_mul Nat.one_le_two_pow (Nat.one_le_pow _ _ (Nat.succ_pos _))).trans
        (.of_le fun x => (Nat.mul_le_mul_right _ (hcnt_le x)).trans_eq (by simp only [M]; ring))
  -- the final state, its table and its last row
  let fin := fun x : TSPInstance => hkStep^[(x.dist.length - 1) * (x.dist.length - 1)] (hkInit x)
  have hst : (fun x => (encHKState (fin x)).length) ≼ M :=
    (BigOLe.of_le fun x => (hst_bound x _ le_rfl).2.2.2.2).trans hB
  have htab : (fun x => (encList encRow (fin x).2).length) ≼ M :=
    (BigOLe.of_le fun x => length_le_encPair_right _ (encList encRow) (fin x)).trans hst
  have hmax : (fun x => listMax (fun r => (encRow r).length) (fin x).2 + 1) ≼
      fun x => ((encTSP x).length + 1) ^ 2 :=
    .of_le_linear 4 2 fun x => by have := (hst_bound x _ le_rfl).2.1; simp only [fin]; omega
  have hmaxM : (fun x => listMax (fun r => (encRow r).length) (fin x).2 + 1) ≼ M :=
    hmax.trans (bigO_polyBound_expBound 2 e (by omega))
  have hlast : (fun x => (encRow ((fin x).2.foldl (fun _ r => r) [])).length) ≼ M :=
    (BigOLe.of_le fun x => (length_encRow_foldl_last_le (fin x).2).trans (Nat.le_succ _)).trans
      hmaxM
  have hrows : (fun x => (fin x).2.length * (listMax (fun r => (encRow r).length) (fin x).2 + 1))
      ≼ M :=
    ((BigOLe.mul_left _ hmax fun x => Nat.one_le_pow _ _ (Nat.succ_pos _)).trans
      (.of_le fun x => Nat.mul_le_mul_right _ (hst_bound x _ le_rfl).1)).trans
        (bigO_expBound_mono 2 e (by omega))
  have hMN : M ≼ fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ (e + 2) :=
    bigO_expBound_mono e (e + 2) (by omega)
  refine ⟨e + 2, hval.weaken ?_ ?_⟩
  · exact (((((BigOLe.add (.trans (.of_le fun _ => by omega) hpoly) hinitM).trans hMN).add
      hprod).add (hst.trans hMN)).add ((htab.add hrows).trans hMN)).add (hlast.trans hMN)
  · exact (((((((BigOLe.add (.trans (.of_le fun _ => by omega) hpoly) hinitM).add hR).add hB).add
      (.trans (.of_le fun _ => by omega) hpoly)).add hst).add
        (htab.add ((BigOLe.of_le fun _ => Nat.le_succ _).trans hmaxM))).add hlast).trans hMN

@[growth_poly]
private theorem length_encNat_tmOptCost_le (x : TSPInstance) :
    (encNat (tmOptCost x)).length ≤ 4 * ((encTSP x).length + 1) ^ 2 + 2 := by
  have h0 : (encNat 0).length ≤ 1 := by simp [encNat_apply]
  unfold tmOptCost
  cases hx : x.dist.length with
  | zero =>
    have hxnil : x.dist = [] := List.length_eq_zero_iff.1 hx
    simp only [Nat.zero_sub, Nat.zero_mul, Function.iterate_zero_apply, hkInit, initTable,
      hxnil, row0, List.length_nil, List.range_zero, List.map_nil, noneRow, List.replicate_zero,
      List.foldl_cons, List.foldl_nil, List.headD_nil, Option.getD_none]
    omega
  | succ n =>
    dsimp only
    rw [Nat.add_sub_cancel]
    obtain ⟨-, -, hrow, -, -⟩ := hkState_size_bound x hx le_rfl
    set fin := (hkStep^[n * n] (hkInit x)).2
    have hlast_max : (encRow (fin.foldl (fun _ r => r) [])).length ≤
        4 * ((encTSP x).length + 1) ^ 2 :=
      (length_encRow_foldl_last_le fin).trans (listMax_le hrow)
    rcases hlast : fin.foldl (fun _ r => r) [] with _ | ⟨_ | v, rest⟩
    · simp
    · simp
    · rw [hlast] at hlast_max
      simp only [encRow, encList_cons, encOption_some, List.length_append, length_frame,
        List.length_cons] at hlast_max
      simp only [List.headD_cons, Option.getD_some]
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
    (encC := encBool) fun x => by cases hx : x.dist.length <;> simp [tmDecide, hx]
  have hpoly_all : PolyBounded (fun x : TSPInstance => (encTSP x).length)
      (fun x => Tz x + Sz x + Tb x + Sb x +
        (Tle (tmOptCost x, x.bound) + Sle (tmOptCost x, x.bound))) := by
    growth_poly
  obtain ⟨c, d, hcd⟩ := hpoly_all.exists_le
  let e := max e₀ d + 1
  have hpoly : (fun x => Tz x + Sz x + Tb x + Sb x +
      (Tle (tmOptCost x, x.bound) + Sle (tmOptCost x, x.bound))) ≼
        fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e :=
    .trans ⟨c, fun x => (hcd x).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))⟩
      (bigO_polyBound_expBound d e (by omega))
  have hL : (fun x => (encTSP x).length) ≼
      fun x => 2 ^ (x.dist.length - 1) * ((encTSP x).length + 1) ^ e :=
    .trans (.of_le fun _ => by simp) (bigO_polyBound_expBound 1 e (by omega))
  have hopt' := bigO_expBound_mono e₀ e (by omega)
  refine ⟨e, hif.weaken ?_ ?_⟩ <;>
    exact .add (.trans (.of_le fun _ => by omega) hpoly) (.ite _ hL (.add (.add hopt'
      (.trans (.of_le fun _ => by omega) hpoly)) (.trans (.of_le fun _ => by omega) hpoly)))

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
  simp [Real.rpow_natCast]

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
  simp [Real.rpow_natCast]

end Cslib.Complexity.HamCycle
