/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Yates
public import CslibFrontier.Foundations.Combinatorics.InclusionExclusion

/-!
# Inclusion–exclusion counting of Hamiltonian paths

Karp's inclusion–exclusion algorithm [Karp1982] [Bax1993] ([FominKratsch2010], Section 4.2.2,
Theorem 4.5 and Eq. (4.4), printed pp. 56–57 / PDF pp. 68–69) counts the Hamiltonian paths of a
directed graph on `Fin n` in `O(2ⁿ · n³)` operations while keeping only one length-`n` walk-count
vector at a time.

## Mathematical identity and source adaptation

A sequence `w : Fin n → Fin n` of `n` vertices is a Hamiltonian path of `adj` when consecutive
vertices are joined by arcs (`IsWalk adj w`) and `w` is injective. Specializing the general
inclusion–exclusion identity for injective self-maps
(`Finset.card_filter_injective_eq_sum_powerset` in
`CslibFrontier.Foundations.Combinatorics.InclusionExclusion`; cf. [FominKratsch2010], Section 4.1,
Theorem 4.2) to `IsWalk adj` expresses the number of Hamiltonian paths as the alternating sum
`(#(hamPaths adj) : ℤ) = ∑ S : Finset (Fin n), (-1 : ℤ) ^ (n - #S) * #(walksIn adj S n)`,
where `walksIn adj S k` is the set of `k`-vertex walks of `adj` whose vertices all lie in `S`
(`card_hamPaths_eq_sum_walksIn`).

In [FominKratsch2010], Section 4.2.2, Theorem 4.5 and Eq. (4.4), the algorithm fixes start and end
vertices `s, t` and counts `(s, t)`-walks on `n + 2` vertices. Here `hamPaths adj` and `walksIn adj`
range over all start and end vertices in `Fin n`, so `totalWalkCount adj S` sums the `(n - 1)`-step
walk counts across all starting vertices `u : Fin n`.

## Pure specification and word-RAM realization

Subsets `S ⊆ Fin n` are enumerated by their bitmasks `k : Fin (2 ^ n)` via `Fin.foldl (2 ^ n)`
(using `Cslib.Algorithms.Lean.Yates.maskSet`). For each `k`, the number of `n`-vertex walks inside
`maskSet n k` is computed by `n - 1` rounds of restricted vector–adjacency multiplication
(`walkCountFrom`, `rounds`), summed across starting vertices, and accumulated with sign
`(-1) ^ (n - #(maskSet n k))` (`countHamPaths`).

For the checked `O((n³ + 1) · 2 ^ n)` instruction-count realization on a width-blind
standard-basis word RAM (reading `n² + 1` flat input words and allocating `3 * n` working words
for an in-place binary odometer at word widths fitting the `n^n`-scale walk counts), see
`CslibFrontier.Algorithms.WordRAM.HamiltonianCount`.

## Main definitions

* `Cslib.Algorithms.Lean.TSP.IsWalk`: `k`-vertex walks `w : Fin k → Fin n` in `adj`.
* `Cslib.Algorithms.Lean.TSP.walksIn`, `walksFrom`: walks inside a vertex subset `S`.
* `Cslib.Algorithms.Lean.TSP.hamPaths`: Hamiltonian paths `w : Fin n → Fin n` in `adj`.
* `Cslib.Algorithms.Lean.TSP.walkCountFrom`, `totalWalkCount`: pure layered DP walk counts.
* `Cslib.Algorithms.Lean.TSP.countHamPaths`, `decideHamPath`: pure inclusion–exclusion counter and
  decider.

## Main results

* `Cslib.Algorithms.Lean.TSP.card_hamPaths_eq_sum_walksIn`: Karp–Bax inclusion–exclusion formula
  for Hamiltonian paths.
* `Cslib.Algorithms.Lean.TSP.card_walksFrom`, `card_walksIn_eq_totalWalkCount`: correctness of the
  layered walk-count recurrence.
* `Cslib.Algorithms.Lean.TSP.countHamPaths_eq`,
  `Cslib.Algorithms.Lean.TSP.card_hamPaths_eq_toNat_countHamPaths`: correctness of `countHamPaths`.
* `Cslib.Algorithms.Lean.TSP.decideHamPath_eq_true_iff`: decision corollary.

## References

* [E. T. Bax, *Inclusion and exclusion algorithm for the Hamiltonian path problem*][Bax1993]
* [F. V. Fomin and D. Kratsch, *Exact Exponential Algorithms*][FominKratsch2010], Section 4.1
  (Theorem 4.2) and Section 4.2.2 (Theorem 4.5 and Eq. (4.4), pp. 56–57)
* [R. M. Karp, *Dynamic programming meets the principle of inclusion and exclusion*][Karp1982]
-/

public section

namespace Cslib.Algorithms.Lean.TSP

open Finset Cslib.Algorithms.Lean Cslib.Algorithms.Lean.Yates

/-! ### Walks and Hamiltonian paths on `Fin n` -/

section Walks

variable {n : ℕ}

/-- A sequence `w : Fin k → Fin n` of `k` vertices is a walk in `adj` if every consecutive pair of
vertices is joined by an arc. -/
@[expose] def IsWalk (adj : Fin n → Fin n → Bool) {k : ℕ} (w : Fin k → Fin n) : Prop :=
  (List.ofFn w).IsChain fun u v => adj u v = true

instance {adj : Fin n → Fin n → Bool} {k : ℕ} : DecidablePred (IsWalk adj (k := k)) :=
  fun w => inferInstanceAs (Decidable ((List.ofFn w).IsChain _))

@[simp] theorem isWalk_zero (adj : Fin n → Fin n → Bool) (w : Fin 0 → Fin n) : IsWalk adj w := by
  simp [IsWalk]

@[simp] theorem isWalk_one (adj : Fin n → Fin n → Bool) (w : Fin 1 → Fin n) : IsWalk adj w := by
  simp [IsWalk, List.ofFn_succ]

theorem isWalk_succ_succ (adj : Fin n → Fin n → Bool) {k : ℕ} (w : Fin (k + 2) → Fin n) :
    IsWalk adj w ↔ adj (w 0) (w 1) = true ∧ IsWalk adj (w ∘ Fin.succ) := by
  rw [IsWalk, List.ofFn_succ, List.ofFn_succ, List.isChain_cons_cons, IsWalk, List.ofFn_succ]
  rfl

/-- The `k`-vertex walks in `adj` whose vertices all lie in `S`. -/
@[expose] def walksIn (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) (k : ℕ) :
    Finset (Fin k → Fin n) :=
  univ.filter fun w => IsWalk adj w ∧ ∀ i, w i ∈ S

/-- The `(k + 1)`-vertex walks in `adj` starting at `u` whose vertices all lie in `S`. -/
@[expose] def walksFrom (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) (k : ℕ) (u : Fin n) :
    Finset (Fin (k + 1) → Fin n) :=
  univ.filter fun w => w 0 = u ∧ IsWalk adj w ∧ ∀ i, w i ∈ S

/-- The Hamiltonian paths of `adj`: `n`-vertex walks visiting every vertex of `Fin n` once. -/
@[expose] def hamPaths (adj : Fin n → Fin n → Bool) : Finset (Fin n → Fin n) :=
  univ.filter fun w => IsWalk adj w ∧ Function.Injective w

/-- A sequence `w : Fin n → Fin n` is in `hamPaths adj` iff `List.ofFn w` is a duplicate-free chain
of arcs of `adj`. -/
theorem mem_hamPaths_iff_ofFn (adj : Fin n → Fin n → Bool) (w : Fin n → Fin n) :
    w ∈ hamPaths adj ↔
      (List.ofFn w).IsChain (fun u v => adj u v = true) ∧ (List.ofFn w).Nodup := by
  unfold hamPaths
  rw [Finset.mem_filter, IsWalk, List.nodup_ofFn]
  simp

/-- **Karp–Bax inclusion–exclusion formula for Hamiltonian paths** [Karp1982] [Bax1993]
([FominKratsch2010], Section 4.2.2, Eq. (4.4)): the number of Hamiltonian paths of `adj` on `Fin n`
equals the alternating sum over `S ⊆ Fin n` of the number of `n`-vertex walks inside `S`. -/
theorem card_hamPaths_eq_sum_walksIn (adj : Fin n → Fin n → Bool) :
    (#(hamPaths adj) : ℤ) =
      ∑ S : Finset (Fin n), (-1 : ℤ) ^ (n - #S) * #(walksIn adj S n) := by
  unfold hamPaths walksIn
  convert Finset.card_filter_injective_eq_sum_powerset (V := Fin n) (IsWalk adj)
  exact (Fintype.card_fin n).symm

end Walks

/-! ### Layered dynamic programming for walk counts -/

section LayeredDP

variable {n : ℕ}

/-- The number of `(k + 1)`-vertex walks in `adj` starting at `u` whose vertices all lie in `S`,
computed by `k` rounds of restricted vector–adjacency multiplication. -/
@[expose] def walkCountFrom (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) : ℕ → Fin n → ℕ
  | 0, u => if u ∈ S then 1 else 0
  | k + 1, u => ∑ v : Fin n, if u ∈ S ∧ adj u v then walkCountFrom adj S k v else 0

/-- The total number of `n`-vertex walks in `adj` whose vertices all lie in `S`. -/
@[expose] def totalWalkCount (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) : ℕ :=
  match n with
  | 0 => 1
  | m + 1 => ∑ u : Fin (m + 1), walkCountFrom adj S m u

/-- Base case: the only `1`-vertex walk starting at `u` is the constant map `fun _ => u`, which lies
in `S` iff `u ∈ S`. -/
theorem card_walksFrom_zero (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) (u : Fin n) :
    #(walksFrom adj S 0 u) = walkCountFrom adj S 0 u := by
  by_cases hu : u ∈ S
  · rw [walkCountFrom, ite_eq_left hu]
    refine Finset.card_eq_one.mpr ⟨fun _ => u, ?_⟩
    ext w
    simp +contextual [walksFrom, hu, funext_iff, Fin.forall_fin_one]
  · rw [walkCountFrom, ite_eq_right hu, Finset.card_eq_zero, walksFrom, Finset.filter_eq_empty_iff]
    rintro w - ⟨rfl, -, hS⟩
    exact hu (hS 0)

/-- Inductive step: partitioning `(k + 2)`-vertex walks starting at `u` by their second vertex
`w 1` (`Finset.card_eq_sum_card_fiberwise`) and removing `u` bijects each fiber with
`(k + 1)`-vertex walks starting at an out-neighbour `v` of `u`. -/
theorem card_walksFrom_succ (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) (k : ℕ) (u : Fin n) :
    #(walksFrom adj S (k + 1) u) =
      ∑ v : Fin n, if u ∈ S ∧ adj u v then #(walksFrom adj S k v) else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun w : Fin (k + 2) → Fin n => w 1) (t := univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases huv : u ∈ S ∧ adj u v = true
  · rw [ite_eq_left huv]
    refine Finset.card_bij (fun w _ => w ∘ Fin.succ) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, walksFrom, Finset.mem_univ, true_and,
        isWalk_succ_succ] at hw ⊢
      exact ⟨hw.2, hw.1.2.1.2, fun i => hw.1.2.2 i.succ⟩
    · intro w₁ hw₁ w₂ hw₂ h
      simp only [Finset.mem_filter, walksFrom, Finset.mem_univ, true_and] at hw₁ hw₂
      funext i
      refine Fin.cases ?_ (fun j => congrFun h j) i
      exact hw₁.1.1.trans hw₂.1.1.symm
    · intro w' hw'
      simp only [walksFrom, Finset.mem_filter, Finset.mem_univ, true_and] at hw'
      have htail : Fin.cons u w' ∘ Fin.succ = w' := rfl
      refine ⟨Fin.cons u w', ?_, htail⟩
      simp only [Finset.mem_filter, walksFrom, Finset.mem_univ, true_and, isWalk_succ_succ,
        Fin.cons_zero, Fin.cons_one]
      rw [htail, hw'.1]
      exact ⟨⟨⟨huv.2, hw'.2.1⟩, fun i => Fin.cases huv.1 (fun j => hw'.2.2 j) i⟩, rfl⟩
  · rw [ite_eq_right huv, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro w hw rfl
    simp only [walksFrom, Finset.mem_filter, Finset.mem_univ, true_and, isWalk_succ_succ] at hw
    exact huv ⟨hw.1 ▸ hw.2.2 0, hw.1 ▸ hw.2.1.1⟩

/-- **`walkCountFrom` counts `(k + 1)`-vertex walks inside `S` starting at `u`.** -/
theorem card_walksFrom (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) (k : ℕ) (u : Fin n) :
    #(walksFrom adj S k u) = walkCountFrom adj S k u := by
  induction k generalizing u with
  | zero => exact card_walksFrom_zero adj S u
  | succ k ih =>
    rw [card_walksFrom_succ, walkCountFrom]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ih v]

/-- Partitioning `(k + 1)`-vertex walks inside `S` by their starting vertex `w 0`. -/
theorem card_walksIn_succ (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) (k : ℕ) :
    #(walksIn adj S (k + 1)) = ∑ u : Fin n, walkCountFrom adj S k u := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun w : Fin (k + 1) → Fin n => w 0) (t := univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← card_walksFrom]
  congr 1
  ext w
  simp [walksIn, walksFrom, and_comm]

/-- **`totalWalkCount` counts `n`-vertex walks inside `S`.** -/
theorem card_walksIn_eq_totalWalkCount (adj : Fin n → Fin n → Bool) (S : Finset (Fin n)) :
    #(walksIn adj S n) = totalWalkCount adj S := by
  cases n with
  | zero =>
    have hset : walksIn adj S 0 = {Fin.elim0} := by
      ext w
      simp only [walksIn, Finset.mem_filter, Finset.mem_univ, true_and, isWalk_zero,
        Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim w Fin.elim0, fun _ i => Fin.elim0 i⟩
    simp [totalWalkCount, hset]
  | succ m =>
    simpa [totalWalkCount] using card_walksIn_succ adj S m

end LayeredDP

/-! ### Pure inclusion–exclusion counter -/

section Algorithm

variable {n : ℕ}

/-- Number of set bits of `k` in `0, …, n - 1`, equal to `#(maskSet n k)`. -/
@[expose] def maskCard (n k : ℕ) : ℕ :=
  (List.finRange n).countP fun i : Fin n => k.testBit i

@[simp] theorem maskCard_eq_card_maskSet (n k : ℕ) :
    maskCard n k = #(maskSet n k) := by
  rw [maskCard, maskSet, ← List.toFinset_finRange, ← List.toFinset_filter,
    List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _),
    List.countP_eq_length_filter]

/-- Initial walk-count vector for bitmask `k`: `1` at vertices in `maskSet n k`, `0` outside. -/
@[expose] def initVec (k : ℕ) : Vector ℕ n :=
  Vector.ofFn fun u : Fin n => if k.testBit u then 1 else 0

/-- Compute the next walk-count entry at vertex `u`. -/
@[expose] def stepCell (adj : Fin n → Fin n → Bool) (k : ℕ) (dp : Vector ℕ n)
    (u : Fin n) : ℕ :=
  (List.finRange n).foldl
    (fun acc (v : Fin n) => acc + if (k.testBit u && adj u v) then dp[v.val] else 0) 0

/-- One round of restricted vector–adjacency multiplication. -/
@[expose] def stepVec (adj : Fin n → Fin n → Bool) (k : ℕ) (dp : Vector ℕ n) :
    Vector ℕ n :=
  Vector.ofFn (stepCell adj k dp)

/-- `r` rounds of restricted vector–adjacency multiplication starting from `initVec k`. -/
@[expose] def rounds (adj : Fin n → Fin n → Bool) (k r : ℕ) : Vector ℕ n :=
  (List.finRange r).foldl (fun dp _ => stepVec adj k dp) (initVec k)

/-- Sum the entries of a length-`n` vector. -/
@[expose] def sumVec (dp : Vector ℕ n) : ℕ :=
  (List.finRange n).foldl (fun acc (u : Fin n) => acc + dp[u.val]) 0

/-- Count the `n`-vertex walks in `adj` whose vertices all lie in `maskSet n k`. -/
@[expose] def subsetWalks (adj : Fin n → Fin n → Bool) (k : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | m + 1 => sumVec (rounds adj k m)

/-- **Karp–Bax inclusion–exclusion Hamiltonian path counter** [Karp1982] [Bax1993]
([FominKratsch2010], Section 4.2.2, Theorem 4.5): enumerates all `2 ^ n` subsets `S = maskSet n k`
via `Fin.foldl (2 ^ n)`, computes `#(walksIn adj S n)` by `n - 1` rounds of restricted
vector–adjacency multiplication, and accumulates the signed sum in `ℤ`. -/
@[expose] def countHamPaths (adj : Fin n → Fin n → Bool) : ℤ :=
  Fin.foldl (2 ^ n)
    (fun acc (k : Fin (2 ^ n)) =>
      acc + (-1 : ℤ) ^ (n - maskCard n k) * (subsetWalks adj k : ℤ))
    0

/-- Decide whether `adj` has a Hamiltonian path by testing whether `countHamPaths adj > 0`. -/
@[expose] def decideHamPath (adj : Fin n → Fin n → Bool) : Bool :=
  decide (0 < countHamPaths adj)

@[simp] theorem stepCell_eq (adj : Fin n → Fin n → Bool) (k : ℕ) (dp : Vector ℕ n)
    (u : Fin n) :
    stepCell adj k dp u =
      ∑ v : Fin n, if u ∈ maskSet n k ∧ adj u v then dp[v.val] else 0 := by
  simp only [stepCell, Bool.and_eq_true, mem_maskSet]
  rw [← List.foldl_map, ← List.sum_eq_foldl, ← Fin.sum_univ_def]

@[simp] theorem stepVec_eq (adj : Fin n → Fin n → Bool) (k : ℕ) (dp : Vector ℕ n) :
    stepVec adj k dp =
      Vector.ofFn fun u => ∑ v : Fin n, if u ∈ maskSet n k ∧ adj u v then dp[v.val] else 0 := by
  ext u hu
  simp [stepVec]

private theorem foldl_stepVec_eq {α : Type*} (adj : Fin n → Fin n → Bool) (k : ℕ) :
    ∀ (l : List α) (r : ℕ) (dp : Vector ℕ n),
      dp = Vector.ofFn (walkCountFrom adj (maskSet n k) r) →
      l.foldl (fun dp _ => stepVec adj k dp) dp =
        Vector.ofFn (walkCountFrom adj (maskSet n k) (r + l.length))
  | [], r, dp, hdp => by simp [hdp]
  | _ :: l, r, dp, hdp => by
    rw [List.foldl_cons, foldl_stepVec_eq adj k l (r + 1)]
    · simp [Nat.add_right_comm, Nat.add_assoc]
    · rw [hdp, stepVec_eq]
      ext u hu
      simp only [Vector.getElem_ofFn, walkCountFrom]

theorem rounds_eq (adj : Fin n → Fin n → Bool) (k r : ℕ) :
    rounds adj k r = Vector.ofFn (walkCountFrom adj (maskSet n k) r) := by
  have h := foldl_stepVec_eq adj k (List.finRange r) 0 (initVec k) (by
    ext u hu
    simp [initVec, walkCountFrom])
  simpa [rounds] using h

@[simp] theorem sumVec_eq (dp : Vector ℕ n) :
    sumVec dp = ∑ u : Fin n, dp[u.val] := by
  simp only [sumVec]
  rw [← List.foldl_map, ← List.sum_eq_foldl, ← Fin.sum_univ_def]

@[simp] theorem subsetWalks_eq (adj : Fin n → Fin n → Bool) (k : ℕ) :
    subsetWalks adj k = totalWalkCount adj (maskSet n k) := by
  cases n with
  | zero => rfl
  | succ m =>
    simp only [subsetWalks, rounds_eq, sumVec_eq, Vector.getElem_ofFn, totalWalkCount]

/-- Accumulating `+ f i` over `Fin.foldl m` starting from `0` equals the finite sum `∑ i, f i`. -/
theorem fin_foldl_eq_sum {M : Type*} [AddCommMonoid M] (m : ℕ) (f : Fin m → M) :
    Fin.foldl m (fun acc i => acc + f i) 0 = ∑ i : Fin m, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.foldl_succ_last, ih, Fin.sum_univ_castSucc]

/-- **Correctness of `countHamPaths`** [Karp1982] [Bax1993]: `countHamPaths adj` equals the
number of Hamiltonian paths of `adj`. -/
@[simp] theorem countHamPaths_eq (adj : Fin n → Fin n → Bool) :
    countHamPaths adj = (#(hamPaths adj) : ℤ) := by
  rw [countHamPaths, fin_foldl_eq_sum, card_hamPaths_eq_sum_walksIn]
  simp only [maskCard_eq_card_maskSet, subsetWalks_eq, ← card_walksIn_eq_totalWalkCount]
  refine Finset.sum_bij (fun (k : Fin (2 ^ n)) _ => maskSet n k)
    (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro k₁ _ k₂ _ h
    have := congrArg maskIndex h
    simpa using this
  · intro S _
    exact ⟨maskIndex S, Finset.mem_univ _, maskSet_maskIndex S⟩

/-- **`#(hamPaths adj)` as the `ℕ`-valued projection of `countHamPaths`.** -/
theorem card_hamPaths_eq_toNat_countHamPaths (adj : Fin n → Fin n → Bool) :
    #(hamPaths adj) = (countHamPaths adj).toNat := by
  rw [countHamPaths_eq, Int.toNat_natCast]

/-- **Decision corollary**: `decideHamPath adj` returns `true` iff `adj` has a Hamiltonian path. -/
theorem decideHamPath_eq_true_iff (adj : Fin n → Fin n → Bool) :
    decideHamPath adj = true ↔ (hamPaths adj).Nonempty := by
  simp [decideHamPath, countHamPaths_eq, Finset.card_pos]

end Algorithm

end Cslib.Algorithms.Lean.TSP
