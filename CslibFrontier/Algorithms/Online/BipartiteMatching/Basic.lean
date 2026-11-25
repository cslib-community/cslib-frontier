/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.BipartiteMatching
public import Cslib.Probability.PMF
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Probability.Minimax
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.ToReal

/-!
# Online bipartite matching: model, greedy `1/2`-competitiveness, and deterministic hardness

This module formalizes the online bipartite matching model of Karp, Vazirani, and Vazirani
[KarpVaziraniVazirani1990]. A finite set `L` of offline vertices is known in advance; online
vertices arrive sequentially, each revealing its neighborhood `N : Finset L` upon arrival. An
online algorithm must irrevocably match the arriving vertex to an unmatched neighbor or leave it
unmatched, without seeing future arrivals.

## Model and conventions

* **Arrival sequences (`arrivals : List (Finset L)`):** the `j`-th arriving online vertex
  (`j : Fin arrivals.length`) has offline neighborhood `arrivals[j]`, inducing the bipartite graph
  `graphOfArrivals arrivals : L × Fin arrivals.length → Bool`, reusing the matching predicate
  `Cslib.Algorithms.Lean.MaxFlow.IsMatching`.
* **Deterministic online algorithms (`DetAlg L`):** a rule `choose hist matched N : Option L`
  depending only on the prefix of revealed neighborhoods `hist`, the already-matched offline
  vertices `matched`, and the current neighborhood `N`. Admissibility is enforced by `onlineStep`
  (an invalid choice leaves the arriving vertex unmatched), so every `A : DetAlg L` produces a
  valid matching (`DetAlg.isMatching_runMatching`) whose prefix decisions are independent of
  future arrivals (`DetAlg.runChoices_append`).
* **Randomized online algorithms against an oblivious adversary (`RandAlg L`):** discrete
  (countably supported) probability distributions `PMF (DetAlg L)` over deterministic online
  algorithms, evaluated by expected matching size `RandAlg.expectedMatchingSize` on a fixed
  arrival sequence.

## Main definitions

* `Cslib.Algorithms.Online.BipartiteMatching.graphOfArrivals`: bipartite graph indicator induced
  by an arrival sequence.
* `Cslib.Algorithms.Online.BipartiteMatching.IsMaximalMatching`: maximal matchings in a bipartite
  graph.
* `Cslib.Algorithms.Online.BipartiteMatching.onlineStep`, `DetAlg`, `DetAlg.runChoices`,
  `DetAlg.matchedLeft`, `DetAlg.runMatching`: deterministic online matching algorithms and their
  executions.
* `Cslib.Algorithms.Online.BipartiteMatching.DetAlg.IsGreedy`: greedy deterministic online
  matching algorithms.
* `Cslib.Algorithms.Online.BipartiteMatching.RandAlg`, `RandAlg.expectedMatchingSize`: randomized
  online matching algorithms against an oblivious adversary.

## Main results

* `Cslib.Algorithms.Online.BipartiteMatching.card_le_two_mul_of_isMaximalMatching`: every maximal
  matching has cardinality at least half of every matching (`|M'| ≤ 2 |M|`).
* `Cslib.Algorithms.Online.BipartiteMatching.DetAlg.isMaximalMatching_runMatching_of_isGreedy` and
  `DetAlg.card_le_two_mul_runMatching_of_isGreedy`: every greedy deterministic online algorithm
  produces a maximal matching and achieves competitive ratio `1/2`.
* `Cslib.Algorithms.Online.BipartiteMatching.exists_det_half_witness`,
  `exists_det_half_witness_mul`, and `not_det_competitive_of_gt_half`: no deterministic online
  matching algorithm beats ratio `1/2` (even with an arbitrary additive slack), witnessed on an
  adaptive `2 + 2` graph and its `k`-fold disjoint union.
* `Cslib.Algorithms.Online.BipartiteMatching.RandAlg.exists_expectedMatchingSize_le`: the easy
  direction of Yao's minimax principle [Yao1977] for expected matching size.

## References

* [R. M. Karp, U. V. Vazirani, and V. V. Vazirani, *An Optimal Algorithm for On-line Bipartite
  Matching*][KarpVaziraniVazirani1990]
* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
-/

open scoped ENNReal

public section

namespace Cslib.Algorithms.Online.BipartiteMatching

open Cslib.Algorithms.Lean.MaxFlow

/-! ### Arrival sequences and maximal matchings -/

section GraphAndMaximal

variable {L R : Type*}

/-- The bipartite graph on `L × Fin arrivals.length` whose `j`-th online vertex has offline
neighborhood `arrivals[j]`. -/
@[expose] def graphOfArrivals [DecidableEq L] (arrivals : List (Finset L)) :
    L × Fin arrivals.length → Bool
  | (u, j) => decide (u ∈ arrivals[j.1])

/-- `M` is a maximal matching in `G` if `M` is a matching and every edge of `G` shares an endpoint
with some edge in `M`. -/
@[expose] def IsMaximalMatching (G : L × R → Bool) (M : Finset (L × R)) : Prop :=
  IsMatching G M ∧ ∀ u v, G (u, v) = true → (∃ v', (u, v') ∈ M) ∨ (∃ u', (u', v) ∈ M)

private theorem card_filter_mem_image_le {α : Type*} [DecidableEq α]
    (M M' : Finset (L × R)) (proj : L × R → α)
    (hinj : Set.InjOn proj (M' : Set (L × R))) :
    (M'.filter (fun e => proj e ∈ M.image proj)).card ≤ M.card := by
  classical
  calc (M'.filter (fun e => proj e ∈ M.image proj)).card
      = ((M'.filter (fun e => proj e ∈ M.image proj)).image proj).card :=
        (Finset.card_image_of_injOn (hinj.mono fun _ he => (Finset.mem_filter.mp he).1)).symm
    _ ≤ (M.image proj).card :=
        Finset.card_le_card fun _ hx => by
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
          exact (Finset.mem_filter.mp he).2
    _ ≤ M.card := Finset.card_image_le

/-- Every maximal matching in a bipartite graph has size at least half of every matching. -/
theorem card_le_two_mul_of_isMaximalMatching
    {G : L × R → Bool} {M M' : Finset (L × R)}
    (hM' : IsMatching G M') (hM : IsMaximalMatching G M) :
    M'.card ≤ 2 * M.card := by
  classical
  have hsub : M' ⊆ M'.filter (fun e => e.1 ∈ M.image Prod.fst) ∪
      M'.filter (fun e => e.2 ∈ M.image Prod.snd) := by
    intro ⟨u, v⟩ huv
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hM.2 u v (hM'.1 (u, v) huv) with ⟨v', hv'⟩ | ⟨u', hu'⟩
    · exact Or.inl ⟨huv, Finset.mem_image.mpr ⟨(u, v'), hv', rfl⟩⟩
    · exact Or.inr ⟨huv, Finset.mem_image.mpr ⟨(u', v), hu', rfl⟩⟩
  have hleft : (M'.filter (fun e => e.1 ∈ M.image Prod.fst)).card ≤ M.card :=
    card_filter_mem_image_le M M' Prod.fst <| by
      intro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ (hu : u₁ = u₂)
      subst hu
      exact Prod.ext rfl (hM'.2.1 u₁ v₁ v₂ h₁ h₂)
  have hright : (M'.filter (fun e => e.2 ∈ M.image Prod.snd)).card ≤ M.card :=
    card_filter_mem_image_le M M' Prod.snd <| by
      intro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ (hv : v₁ = v₂)
      subst hv
      exact Prod.ext (hM'.2.2 u₁ u₂ v₁ h₁ h₂) rfl
  have hunion := Finset.card_union_le
    (M'.filter (fun e => e.1 ∈ M.image Prod.fst))
    (M'.filter (fun e => e.2 ∈ M.image Prod.snd))
  have hle := Finset.card_le_card hsub
  omega

end GraphAndMaximal

/-! ### Deterministic online matching algorithms -/

section Deterministic

variable {L : Type*}

/-- Admissible online matching step: match the arriving vertex to `u` if `choice = some u` with
`u ∈ N` and `u ∉ matched`; otherwise leave it unmatched. -/
@[expose] def onlineStep [DecidableEq L] (matched N : Finset L) : Option L → Option L
  | some u => if u ∈ N ∧ u ∉ matched then some u else none
  | none => none

theorem onlineStep_eq_some_iff [DecidableEq L] {matched N : Finset L} {o : Option L} {u : L} :
    onlineStep matched N o = some u ↔ o = some u ∧ u ∈ N ∧ u ∉ matched := by
  cases o with
  | none => simp [onlineStep]
  | some w =>
    by_cases hw : w = u
    · subst hw
      simp [onlineStep]
    · simp [onlineStep, hw]

/-- Update the set of matched offline vertices after an admissible step choice `c`. -/
@[expose] def updateMatched [DecidableEq L] (matched : Finset L) : Option L → Finset L
  | some u => insert u matched
  | none => matched

/-- A deterministic online bipartite matching algorithm on offline vertex set `L`. At each step,
given the list `hist` of previously revealed neighborhoods, the set `matched` of already-matched
offline vertices, and the newly arrived vertex's neighborhood `N`, `choose hist matched N` selects
an offline vertex to match (or `none` to leave the arriving vertex unmatched). -/
structure DetAlg (L : Type*) where
  /-- Choice rule for the newly arrived online vertex. -/
  choose : List (Finset L) → Finset L → Finset L → Option L

namespace DetAlg

variable [DecidableEq L] (A : DetAlg L)

/-- Execute `A` from history `hist` and already-matched offline set `matched` on the remaining
arrival sequence, returning the per-arrival match choices (`some u` or `none`). -/
@[expose] def runChoicesFrom : List (Finset L) → Finset L → List (Finset L) → List (Option L)
  | _, _, [] => []
  | hist, matched, N :: rest =>
    let c := onlineStep matched N (A.choose hist matched N)
    c :: runChoicesFrom (hist ++ [N]) (updateMatched matched c) rest

/-- The list of per-arrival match choices made by `A` on `arrivals`. -/
@[expose] def runChoices (arrivals : List (Finset L)) : List (Option L) :=
  A.runChoicesFrom [] ∅ arrivals

/-- The set of matched offline vertices after running `A` from `(hist, matched)` on `rest`. -/
@[expose] def matchedLeftFrom : List (Finset L) → Finset L → List (Finset L) → Finset L
  | _, matched, [] => matched
  | hist, matched, N :: rest =>
    let c := onlineStep matched N (A.choose hist matched N)
    matchedLeftFrom (hist ++ [N]) (updateMatched matched c) rest

/-- The set of offline vertices matched by `A` on `arrivals`. -/
@[expose] def matchedLeft (arrivals : List (Finset L)) : Finset L :=
  A.matchedLeftFrom [] ∅ arrivals

@[simp] theorem runChoices_nil : A.runChoices [] = [] := rfl

@[simp] theorem matchedLeft_nil : A.matchedLeft [] = ∅ := rfl

@[simp] theorem length_runChoicesFrom (hist : List (Finset L)) (matched : Finset L)
    (rest : List (Finset L)) :
    (A.runChoicesFrom hist matched rest).length = rest.length := by
  induction rest generalizing hist matched with
  | nil => rfl
  | cons N rest ih => simp [runChoicesFrom, ih]

@[simp] theorem length_runChoices (arrivals : List (Finset L)) :
    (A.runChoices arrivals).length = arrivals.length :=
  A.length_runChoicesFrom [] ∅ arrivals

theorem runChoicesFrom_append (hist : List (Finset L)) (matched : Finset L)
    (a₁ a₂ : List (Finset L)) :
    A.runChoicesFrom hist matched (a₁ ++ a₂) =
      A.runChoicesFrom hist matched a₁ ++
        A.runChoicesFrom (hist ++ a₁) (A.matchedLeftFrom hist matched a₁) a₂ := by
  induction a₁ generalizing hist matched with
  | nil => simp [runChoicesFrom, matchedLeftFrom]
  | cons N rest ih =>
    simp only [List.cons_append, runChoicesFrom, matchedLeftFrom, ih, List.append_assoc,
      List.nil_append]

/-- **Online causality:** the choices of `A` on `a₁ ++ a₂` extend its choices on `a₁` without
depending on `a₂`. -/
theorem runChoices_append (a₁ a₂ : List (Finset L)) :
    A.runChoices (a₁ ++ a₂) = A.runChoices a₁ ++ A.runChoicesFrom a₁ (A.matchedLeft a₁) a₂ := by
  simpa [runChoices, matchedLeft] using A.runChoicesFrom_append [] ∅ a₁ a₂

theorem matchedLeftFrom_append (hist : List (Finset L)) (matched : Finset L)
    (a₁ a₂ : List (Finset L)) :
    A.matchedLeftFrom hist matched (a₁ ++ a₂) =
      A.matchedLeftFrom (hist ++ a₁) (A.matchedLeftFrom hist matched a₁) a₂ := by
  induction a₁ generalizing hist matched with
  | nil => simp [matchedLeftFrom]
  | cons N rest ih =>
    simp only [List.cons_append, matchedLeftFrom, ih, List.append_assoc, List.nil_append]

theorem matchedLeft_append (a₁ a₂ : List (Finset L)) :
    A.matchedLeft (a₁ ++ a₂) = A.matchedLeftFrom a₁ (A.matchedLeft a₁) a₂ := by
  simpa [matchedLeft] using A.matchedLeftFrom_append [] ∅ a₁ a₂

theorem subset_matchedLeftFrom (hist : List (Finset L)) (matched : Finset L)
    (rest : List (Finset L)) :
    matched ⊆ A.matchedLeftFrom hist matched rest := by
  induction rest generalizing hist matched with
  | nil => exact Finset.Subset.rfl
  | cons N rest ih =>
    simp only [matchedLeftFrom]
    refine Finset.Subset.trans ?_ (ih _ _)
    cases onlineStep matched N (A.choose hist matched N) with
    | none => exact Finset.Subset.rfl
    | some u => exact Finset.subset_insert u matched

theorem mem_matchedLeftFrom_iff (hist : List (Finset L)) (matched : Finset L)
    (rest : List (Finset L)) (u : L) :
    u ∈ A.matchedLeftFrom hist matched rest ↔
      u ∈ matched ∨ some u ∈ A.runChoicesFrom hist matched rest := by
  induction rest generalizing hist matched with
  | nil => simp [matchedLeftFrom, runChoicesFrom]
  | cons N rest ih =>
    simp only [matchedLeftFrom, runChoicesFrom, List.mem_cons, ih]
    cases h : onlineStep matched N (A.choose hist matched N) with
    | none => simp [updateMatched]
    | some w =>
      simp only [updateMatched, Finset.mem_insert, Option.some.injEq]
      tauto

theorem mem_matchedLeft_iff (arrivals : List (Finset L)) (u : L) :
    u ∈ A.matchedLeft arrivals ↔ some u ∈ A.runChoices arrivals := by
  simpa [matchedLeft, runChoices] using A.mem_matchedLeftFrom_iff [] ∅ arrivals u

/-- Matched offline vertices grow monotonically with prefixes of the arrival sequence. -/
theorem matchedLeft_take_subset (arrivals : List (Finset L)) (i : ℕ) :
    A.matchedLeft (arrivals.take i) ⊆ A.matchedLeft arrivals := by
  have hsub := A.subset_matchedLeftFrom (arrivals.take i) (A.matchedLeft (arrivals.take i))
    (arrivals.drop i)
  rwa [← A.matchedLeft_append, List.take_append_drop] at hsub

/-- The `i`-th match choice of `A` on `arrivals` is the admissible online step from the state
after `arrivals.take i`. -/
theorem runChoices_getElem (arrivals : List (Finset L)) {i : ℕ} (hi : i < arrivals.length) :
    (A.runChoices arrivals)[i]'(by simp [hi]) =
      onlineStep (A.matchedLeft (arrivals.take i)) arrivals[i]
        (A.choose (arrivals.take i) (A.matchedLeft (arrivals.take i)) arrivals[i]) := by
  have hsplit : arrivals = arrivals.take i ++ arrivals[i] :: arrivals.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hlen : (A.runChoices (arrivals.take i)).length = i := by
    rw [A.length_runChoices, List.length_take, Nat.min_eq_left hi.le]
  have happ : A.runChoices arrivals =
      A.runChoices (arrivals.take i) ++
        onlineStep (A.matchedLeft (arrivals.take i)) arrivals[i]
          (A.choose (arrivals.take i) (A.matchedLeft (arrivals.take i)) arrivals[i]) ::
          A.runChoicesFrom (arrivals.take i ++ [arrivals[i]])
            (updateMatched (A.matchedLeft (arrivals.take i))
              (onlineStep (A.matchedLeft (arrivals.take i)) arrivals[i]
                (A.choose (arrivals.take i) (A.matchedLeft (arrivals.take i)) arrivals[i])))
            (arrivals.drop (i + 1)) := by
    conv_lhs => rw [hsplit]
    rw [A.runChoices_append, runChoicesFrom]
  have hle : (A.runChoices (arrivals.take i)).length ≤ i := hlen.le
  simp only [happ, List.getElem_append_right hle, hlen, Nat.sub_self, List.getElem_cons_zero]

private theorem runChoicesFrom_valid (hist : List (Finset L)) (matched : Finset L)
    (rest : List (Finset L)) :
    (∀ (i : ℕ) (hi : i < rest.length) (u : L),
      (A.runChoicesFrom hist matched rest)[i]'(by simp [hi]) = some u →
        u ∈ rest[i] ∧ u ∉ matched) ∧
    (∀ (i j : ℕ) (hi : i < rest.length) (hj : j < rest.length) (u : L),
      (A.runChoicesFrom hist matched rest)[i]'(by simp [hi]) = some u →
      (A.runChoicesFrom hist matched rest)[j]'(by simp [hj]) = some u → i = j) := by
  induction rest generalizing hist matched with
  | nil =>
    exact ⟨fun i hi => by simp at hi, fun i _ hi => by simp at hi⟩
  | cons N rest ih =>
    set c := onlineStep matched N (A.choose hist matched N) with hc_def
    obtain ⟨hmem_ih, hinj_ih⟩ := ih (hist ++ [N]) (updateMatched matched c)
    have hstep_sub : ∀ w, w ∈ matched → w ∈ updateMatched matched c := by
      intro w hw
      cases c with
      | none => exact hw
      | some u => exact Finset.mem_insert_of_mem hw
    constructor
    · intro i hi u hu
      cases i with
      | zero =>
        simp only [runChoicesFrom, List.getElem_cons_zero] at hu
        have ⟨_, huN, hum⟩ := onlineStep_eq_some_iff.mp hu
        exact ⟨huN, hum⟩
      | succ i' =>
        simp only [runChoicesFrom, List.getElem_cons_succ] at hu
        have ⟨huN, hu_not⟩ := hmem_ih i' (Nat.lt_of_succ_lt_succ hi) u hu
        exact ⟨huN, fun hm => hu_not (hstep_sub u hm)⟩
    · intro i j hi hj u hui huj
      have hzero {k : ℕ} (hk : k + 1 < (N :: rest).length)
          (h0 : (A.runChoicesFrom hist matched (N :: rest))[0]'(by simp) = some u)
          (hs : (A.runChoicesFrom hist matched (N :: rest))[k + 1]'(by simpa using hk) = some u) :
          False := by
        simp only [runChoicesFrom, List.getElem_cons_zero, List.getElem_cons_succ, ← hc_def]
          at h0 hs
        exact (hmem_ih k (Nat.lt_of_succ_lt_succ hk) u hs).2
          (h0 ▸ Finset.mem_insert_self u matched)
      cases i with
      | zero =>
        cases j with
        | zero => rfl
        | succ j' => exact (hzero hj hui huj).elim
      | succ i' =>
        cases j with
        | zero => exact (hzero hi huj hui).elim
        | succ j' =>
          simp only [runChoicesFrom, List.getElem_cons_succ] at hui huj
          exact congrArg Nat.succ
            (hinj_ih i' j' (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) u hui huj)

/-- The matching (set of `(offline, online)` edges) produced by `A` on `arrivals`. -/
@[expose] def runMatching (arrivals : List (Finset L)) : Finset (L × Fin arrivals.length) :=
  Finset.univ.biUnion fun j : Fin arrivals.length =>
    match (A.runChoices arrivals)[j.1]'(by simp [j.2]) with
    | some u => {(u, j)}
    | none => ∅

theorem mem_runMatching_iff (arrivals : List (Finset L)) (u : L) (j : Fin arrivals.length) :
    (u, j) ∈ A.runMatching arrivals ↔
      (A.runChoices arrivals)[j.1]'(by simp [j.2]) = some u := by
  simp only [runMatching, Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine ⟨fun ⟨j', hj'⟩ => ?_, fun h => ⟨j, by simp [h]⟩⟩
  cases h : (A.runChoices arrivals)[j'.1]'(by simp [j'.2]) with
  | none => simp [h] at hj'
  | some w =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Finset.mem_singleton.mp (by simpa [h] using hj'))
    exact h

/-- Every deterministic online matching algorithm produces a valid matching on every arrival
sequence. -/
theorem isMatching_runMatching (arrivals : List (Finset L)) :
    IsMatching (graphOfArrivals arrivals) (A.runMatching arrivals) := by
  obtain ⟨hmem, hinj⟩ := A.runChoicesFrom_valid [] ∅ arrivals
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨u, j⟩ huj
    rw [mem_runMatching_iff] at huj
    simp only [graphOfArrivals, decide_eq_true_eq]
    exact (hmem j.1 j.2 u huj).1
  · intro u j₁ j₂ h₁ h₂
    rw [mem_runMatching_iff] at h₁ h₂
    exact Fin.ext (hinj j₁.1 j₂.1 j₁.2 j₂.2 u h₁ h₂)
  · intro u₁ u₂ j h₁ h₂
    rw [mem_runMatching_iff] at h₁ h₂
    exact Option.some.inj (h₁.symm.trans h₂)

theorem image_fst_runMatching (arrivals : List (Finset L)) :
    (A.runMatching arrivals).image Prod.fst = A.matchedLeft arrivals := by
  ext u
  rw [Finset.mem_image, mem_matchedLeft_iff, List.mem_iff_getElem]
  constructor
  · rintro ⟨⟨u', j⟩, hj, rfl⟩
    rw [mem_runMatching_iff] at hj
    exact ⟨j.1, by simp [j.2], hj⟩
  · rintro ⟨i, hi, hui⟩
    have hi' : i < arrivals.length := by simpa using hi
    exact ⟨(u, ⟨i, hi'⟩), (A.mem_runMatching_iff arrivals u ⟨i, hi'⟩).mpr hui, rfl⟩

/-- The cardinality of `A.runMatching arrivals` equals the number of matched offline vertices. -/
theorem card_runMatching_eq_card_matchedLeft (arrivals : List (Finset L)) :
    (A.runMatching arrivals).card = (A.matchedLeft arrivals).card := by
  have hM := A.isMatching_runMatching arrivals
  have hinj : Set.InjOn Prod.fst (A.runMatching arrivals : Set (L × Fin arrivals.length)) := by
    intro ⟨u₁, j₁⟩ h₁ ⟨u₂, j₂⟩ h₂ (hu : u₁ = u₂)
    subst hu
    exact Prod.ext rfl (hM.2.1 u₁ j₁ j₂ h₁ h₂)
  rw [← image_fst_runMatching, Finset.card_image_of_injOn hinj]

private theorem card_filter_isSome_eq_countP {α : Type*} (l : List (Option α)) :
    (Finset.univ.filter fun j : Fin l.length => l[j.1].isSome).card =
      l.countP Option.isSome := by
  induction l with
  | nil => simp
  | cons o os ih =>
    rw [List.countP_cons, ← ih, Fin.univ_succ, Finset.cons_eq_insert, Finset.filter_insert,
      Finset.filter_map]
    simp only [Function.comp_def, Function.Embedding.coeFn_mk, Fin.val_zero,
      List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]
    split_ifs with ho
    · rw [Finset.card_insert_of_notMem (by simp), Finset.card_map]
    · rw [Finset.card_map]
      omega

/-- The cardinality of `A.runMatching arrivals` equals the sum of match indicators over arrivals. -/
theorem card_runMatching_eq_sum (arrivals : List (Finset L)) :
    (A.runMatching arrivals).card =
      ∑ j : Fin arrivals.length,
        if ((A.runChoices arrivals)[j.1]'(by simp [j.2])).isSome then 1 else 0 := by
  have hM := A.isMatching_runMatching arrivals
  have hinj : Set.InjOn Prod.snd (A.runMatching arrivals : Set (L × Fin arrivals.length)) := by
    intro ⟨u₁, j₁⟩ h₁ ⟨u₂, j₂⟩ h₂ (hv : j₁ = j₂)
    subst hv
    exact Prod.ext (hM.2.2 u₁ u₂ j₁ h₁ h₂) rfl
  have himg : (A.runMatching arrivals).image Prod.snd =
      Finset.univ.filter fun j : Fin arrivals.length =>
        ((A.runChoices arrivals)[j.1]'(by simp [j.2])).isSome := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
    constructor
    · rintro ⟨u, _, hmem, rfl⟩
      rw [mem_runMatching_iff] at hmem
      simp [hmem]
    · intro hsome
      cases h : (A.runChoices arrivals)[j.1]'(by simp [j.2]) with
      | none => simp [h] at hsome
      | some u =>
        exact ⟨u, j, (A.mem_runMatching_iff arrivals u j).mpr h, rfl⟩
  rw [← Finset.card_image_of_injOn hinj, himg]
  simp [Finset.sum_boole]

/-- The cardinality of `A.runMatching arrivals` equals the number of online vertices matched. -/
theorem card_runMatching_eq_countP (arrivals : List (Finset L)) :
    (A.runMatching arrivals).card = (A.runChoices arrivals).countP Option.isSome := by
  rw [card_runMatching_eq_sum, ← card_filter_isSome_eq_countP]
  simp only [Finset.sum_boole, Nat.cast_id]
  have hlen : (A.runChoices arrivals).length = arrivals.length := A.length_runChoices arrivals
  refine Finset.card_bij (fun j _ => ⟨j.1, by omega⟩) ?_ ?_ ?_
  · intro j hj
    simpa using hj
  · intro j₁ _ j₂ _ h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · intro j hj
    exact ⟨⟨j.1, by omega⟩, by simpa using hj, Fin.ext rfl⟩

theorem card_runMatching_le_length (arrivals : List (Finset L)) :
    (A.runMatching arrivals).card ≤ arrivals.length := by
  rw [card_runMatching_eq_countP, ← length_runChoices A arrivals]
  exact List.countP_le_length

/-- A deterministic online matching algorithm is *greedy* if it matches every arriving vertex that
has at least one unmatched neighbor. -/
@[expose] def IsGreedy (A : DetAlg L) : Prop :=
  ∀ hist matched N, (∃ u ∈ N, u ∉ matched) →
    ∃ u ∈ N, u ∉ matched ∧ A.choose hist matched N = some u

/-- Every greedy deterministic online matching algorithm produces a maximal matching. -/
theorem isMaximalMatching_runMatching_of_isGreedy (hA : A.IsGreedy) (arrivals : List (Finset L)) :
    IsMaximalMatching (graphOfArrivals arrivals) (A.runMatching arrivals) := by
  refine ⟨A.isMatching_runMatching arrivals, ?_⟩
  intro u j huj
  simp only [graphOfArrivals, decide_eq_true_eq] at huj
  by_cases hu : u ∈ A.matchedLeft arrivals
  · rw [← A.image_fst_runMatching] at hu
    obtain ⟨⟨u', j'⟩, hmem, rfl⟩ := Finset.mem_image.mp hu
    exact Or.inl ⟨j', hmem⟩
  · right
    have hu_pre : u ∉ A.matchedLeft (arrivals.take j.1) :=
      fun hmem => hu (A.matchedLeft_take_subset arrivals j.1 hmem)
    obtain ⟨w, hwN, hwm, hchoose⟩ :=
      hA (arrivals.take j.1) (A.matchedLeft (arrivals.take j.1)) arrivals[j.1] ⟨u, huj, hu_pre⟩
    refine ⟨w, (A.mem_runMatching_iff arrivals w j).mpr ?_⟩
    rw [A.runChoices_getElem arrivals j.2]
    exact onlineStep_eq_some_iff.mpr ⟨hchoose, hwN, hwm⟩

/-- **Greedy `1/2`-competitiveness:** every greedy deterministic online matching algorithm
produces a matching of size at least half of every matching in the graph. -/
theorem card_le_two_mul_runMatching_of_isGreedy (hA : A.IsGreedy) (arrivals : List (Finset L))
    {M : Finset (L × Fin arrivals.length)} (hM : IsMatching (graphOfArrivals arrivals) M) :
    M.card ≤ 2 * (A.runMatching arrivals).card :=
  card_le_two_mul_of_isMaximalMatching hM (A.isMaximalMatching_runMatching_of_isGreedy hA arrivals)

end DetAlg

end Deterministic

/-! ### Deterministic `1/2` impossibility -/

section DeterministicLowerBound

private def pairVertex (k : ℕ) (i : Fin k) (b : Bool) : Fin (2 * k) :=
  ⟨2 * i.1 + if b then 1 else 0, by cases b <;> dsimp <;> omega⟩

/-- Adaptive `k`-gadget adversarial construction on `Fin (2 * k)`: builds `m` pairs of arrivals
for `0 ≤ i < m`, each pair touching only `{2i, 2i + 1}`, matching at most `1` edge per pair while
admitting a matching of size `2 * m`. -/
private def detHardPrefix (k : ℕ) (A : DetAlg (Fin (2 * k))) :
    (m : ℕ) → m ≤ k → List (Finset (Fin (2 * k)))
  | 0, _ => []
  | m + 1, hm =>
    let pref := detHardPrefix k A m (Nat.le_of_succ_le hm)
    let u₀ := pairVertex k ⟨m, hm⟩ false
    let u₁ := pairVertex k ⟨m, hm⟩ true
    let N₀ : Finset (Fin (2 * k)) := {u₀, u₁}
    let matched := A.matchedLeft pref
    let c := onlineStep matched N₀ (A.choose pref matched N₀)
    let N₁ : Finset (Fin (2 * k)) := match c with | some u => {u} | none => {u₀}
    pref ++ [N₀, N₁]

private theorem length_detHardPrefix (k : ℕ) (A : DetAlg (Fin (2 * k))) (m : ℕ) (hm : m ≤ k) :
    (detHardPrefix k A m hm).length = 2 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [detHardPrefix, List.length_append, List.length_cons, List.length_nil]
    rw [ih (Nat.le_of_succ_le hm)]
    omega

private theorem detHardPrefix_card_le (k : ℕ) (A : DetAlg (Fin (2 * k))) (m : ℕ) (hm : m ≤ k) :
    (A.runMatching (detHardPrefix k A m hm)).card ≤ m := by
  induction m with
  | zero =>
    rw [DetAlg.card_runMatching_eq_countP]
    simp [detHardPrefix]
  | succ m ih =>
    set pref := detHardPrefix k A m (Nat.le_of_succ_le hm)
    set u₀ := pairVertex k ⟨m, hm⟩ false
    set u₁ := pairVertex k ⟨m, hm⟩ true
    set N₀ : Finset (Fin (2 * k)) := {u₀, u₁}
    set matched := A.matchedLeft pref
    set c := onlineStep matched N₀ (A.choose pref matched N₀)
    set N₁ : Finset (Fin (2 * k)) := match c with | some u => {u} | none => {u₀}
    have hpref : (A.runChoices pref).countP Option.isSome ≤ m := by
      rw [← A.card_runMatching_eq_countP]
      exact ih (Nat.le_of_succ_le hm)
    rw [DetAlg.card_runMatching_eq_countP]
    change (A.runChoices (pref ++ [N₀, N₁])).countP Option.isSome ≤ m + 1
    rw [A.runChoices_append, List.countP_append]
    have htail :
        (A.runChoicesFrom pref (A.matchedLeft pref) [N₀, N₁]).countP Option.isSome ≤ 1 := by
      change (A.runChoicesFrom pref matched [N₀, N₁]).countP Option.isSome ≤ 1
      simp only [DetAlg.runChoicesFrom, List.countP_cons, List.countP_nil, zero_add]
      change ((if (onlineStep (updateMatched matched c) N₁
            (A.choose (pref ++ [N₀]) (updateMatched matched c) N₁)).isSome then 1 else 0) +
          if c.isSome then 1 else 0) ≤ 1
      cases hc : c with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, add_zero]
        split_ifs <;> omega
      | some u =>
        have hnone : onlineStep (updateMatched matched (some u)) N₁
            (A.choose (pref ++ [N₀]) (updateMatched matched (some u)) N₁) = none := by
          refine Option.eq_none_iff_forall_not_mem.mpr fun w hw => ?_
          obtain ⟨-, hwN₁, hwm⟩ := onlineStep_eq_some_iff.mp hw
          simp only [N₁, hc, Finset.mem_singleton, updateMatched, Finset.mem_insert] at hwN₁ hwm
          exact hwm (Or.inl hwN₁)
        simp [hnone]
    omega

private theorem detHardPrefix_exists_matching (k : ℕ) (A : DetAlg (Fin (2 * k)))
    (m : ℕ) (hm : m ≤ k) :
    ∃ M : Finset (Fin (2 * k) × Fin (detHardPrefix k A m hm).length),
      IsMatching (graphOfArrivals (detHardPrefix k A m hm)) M ∧
      M.card = 2 * m ∧
      ∀ e ∈ M, e.1.1 < 2 * m := by
  induction m with
  | zero =>
    refine ⟨∅, ⟨by simp, by simp, by simp⟩, rfl, by simp⟩
  | succ m ih =>
    have hm' : m ≤ k := Nat.le_of_succ_le hm
    set pref := detHardPrefix k A m hm'
    obtain ⟨M₀, hM₀, hcard₀, hlt₀⟩ := ih hm'
    set u₀ := pairVertex k ⟨m, hm⟩ false
    set u₁ := pairVertex k ⟨m, hm⟩ true
    set N₀ : Finset (Fin (2 * k)) := {u₀, u₁}
    set matched := A.matchedLeft pref
    set c := onlineStep matched N₀ (A.choose pref matched N₀)
    set N₁ : Finset (Fin (2 * k)) := match c with | some u => {u} | none => {u₀}
    set full := detHardPrefix k A (m + 1) hm
    have hfull_eq : full = pref ++ [N₀, N₁] := rfl
    have hlen_pref : pref.length = 2 * m := length_detHardPrefix k A m hm'
    have hlen_full : full.length = 2 * (m + 1) := length_detHardPrefix k A (m + 1) hm
    let liftJ : Fin pref.length → Fin full.length := fun j => ⟨j.1, by omega⟩
    let M₀' : Finset (Fin (2 * k) × Fin full.length) := M₀.image fun e => (e.1, liftJ e.2)
    have hlift_inj :
        Function.Injective (fun e : Fin (2 * k) × Fin pref.length => (e.1, liftJ e.2)) := by
      rintro ⟨a₁, j₁⟩ ⟨a₂, j₂⟩ h
      simp only [Prod.mk.injEq, liftJ, Fin.mk.injEq] at h
      exact Prod.ext h.1 (Fin.ext h.2)
    have hM₀'_card : M₀'.card = 2 * m := by
      rw [Finset.card_image_of_injective _ hlift_inj, hcard₀]
    have hpair : ∃ a₀ a₁ : Fin (2 * k),
        a₀ ∈ N₀ ∧ a₁ ∈ N₁ ∧ a₀ ≠ a₁ ∧
          (2 * m ≤ a₀.1 ∧ a₀.1 < 2 * (m + 1)) ∧ (2 * m ≤ a₁.1 ∧ a₁.1 < 2 * (m + 1)) := by
      have hu₀_val : u₀.1 = 2 * m := by simp [u₀, pairVertex]
      have hu₁_val : u₁.1 = 2 * m + 1 := by simp [u₁, pairVertex]
      have hne : u₀ ≠ u₁ := fun h => by
        have := congrArg Fin.val h
        omega
      have hbd {a : Fin (2 * k)} (ha : a = u₀ ∨ a = u₁) : 2 * m ≤ a.1 ∧ a.1 < 2 * (m + 1) := by
        rcases ha with rfl | rfl <;> omega
      cases hc : c with
      | none =>
        exact ⟨u₁, u₀, by simp [N₀], by simp [N₁, hc], hne.symm, hbd (.inr rfl), hbd (.inl rfl)⟩
      | some u =>
        rcases Finset.mem_insert.mp (onlineStep_eq_some_iff.mp hc).2.1 with rfl | hu
        · exact ⟨u₁, u₀, by simp [N₀], by simp [N₁, hc], hne.symm, hbd (.inr rfl), hbd (.inl rfl)⟩
        · obtain rfl := Finset.mem_singleton.mp hu
          exact ⟨u₀, u₁, by simp [N₀], by simp [N₁, hc], hne, hbd (.inl rfl), hbd (.inr rfl)⟩
    obtain ⟨a₀, a₁, ha₀N₀, ha₁N₁, hne_a, ⟨ha₀_ge, ha₀_lt⟩, ⟨ha₁_ge, ha₁_lt⟩⟩ := hpair
    let j₀ : Fin full.length := ⟨2 * m, by omega⟩
    let j₁ : Fin full.length := ⟨2 * m + 1, by omega⟩
    have hj₀_val : j₀.1 = 2 * m := rfl
    have hj₁_val : j₁.1 = 2 * m + 1 := rfl
    have hj_ne : j₀ ≠ j₁ := fun h => by
      have := congrArg Fin.val h
      omega
    have hM₀'_lt {x : Fin (2 * k)} {v : Fin full.length} (h : (x, v) ∈ M₀') :
        x.1 < 2 * m ∧ v.1 < 2 * m := by
      obtain ⟨⟨u, j⟩, hj, heq⟩ := Finset.mem_image.mp h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨hlt₀ (u, j) hj, by dsimp [liftJ]; omega⟩
    have ha₀_not {v} (h : (a₀, v) ∈ M₀') : False := by
      have := (hM₀'_lt h).1
      omega
    have ha₁_not {v} (h : (a₁, v) ∈ M₀') : False := by
      have := (hM₀'_lt h).1
      omega
    have hj₀_not {x} (h : (x, j₀) ∈ M₀') : False := by
      have := (hM₀'_lt h).2
      omega
    have hj₁_not {x} (h : (x, j₁) ∈ M₀') : False := by
      have := (hM₀'_lt h).2
      omega
    refine ⟨insert (a₀, j₀) (insert (a₁, j₁) M₀'), ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro e he
        simp only [Finset.mem_insert, Finset.mem_image, M₀'] at he
        rcases he with rfl | rfl | ⟨⟨u, j⟩, hj, rfl⟩
        · simp only [graphOfArrivals, decide_eq_true_eq, full, hfull_eq, j₀]
          rw [List.getElem_append_right (by omega : pref.length ≤ 2 * m)]
          simpa [hlen_pref] using ha₀N₀
        · simp only [graphOfArrivals, decide_eq_true_eq, full, hfull_eq, j₁]
          rw [List.getElem_append_right (by omega : pref.length ≤ 2 * m + 1)]
          simpa [hlen_pref] using ha₁N₁
        · simp only [graphOfArrivals, decide_eq_true_eq, full, hfull_eq, liftJ]
          rw [List.getElem_append_left j.2]
          simpa [graphOfArrivals] using hM₀.1 (u, j) hj
      · intro u v₁ v₂ h₁ h₂
        simp only [Finset.mem_insert, Prod.mk.injEq] at h₁ h₂
        rcases h₁ with ⟨hu₁, hv₁⟩ | ⟨hu₁, hv₁⟩ | h₁ <;>
        rcases h₂ with ⟨hu₂, hv₂⟩ | ⟨hu₂, hv₂⟩ | h₂
        · exact hv₁.trans hv₂.symm
        · exact absurd (hu₁.symm.trans hu₂) hne_a
        · exact (ha₀_not (hu₁ ▸ h₂)).elim
        · exact absurd (hu₂.symm.trans hu₁) hne_a
        · exact hv₁.trans hv₂.symm
        · exact (ha₁_not (hu₁ ▸ h₂)).elim
        · exact (ha₀_not (hu₂ ▸ h₁)).elim
        · exact (ha₁_not (hu₂ ▸ h₁)).elim
        · obtain ⟨⟨u₁', r₁⟩, hr₁, heq₁⟩ := Finset.mem_image.mp h₁
          obtain ⟨⟨u₂', r₂⟩, hr₂, heq₂⟩ := Finset.mem_image.mp h₂
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq₁
          obtain ⟨hu, rfl⟩ := Prod.mk.inj heq₂
          subst hu
          exact congrArg liftJ (hM₀.2.1 _ r₁ r₂ hr₁ hr₂)
      · intro x₁ x₂ v h₁ h₂
        simp only [Finset.mem_insert, Prod.mk.injEq] at h₁ h₂
        rcases h₁ with ⟨hx₁, hv₁⟩ | ⟨hx₁, hv₁⟩ | h₁ <;>
        rcases h₂ with ⟨hx₂, hv₂⟩ | ⟨hx₂, hv₂⟩ | h₂
        · exact hx₁.trans hx₂.symm
        · exact absurd (hv₁.symm.trans hv₂) hj_ne
        · exact (hj₀_not (hv₁ ▸ h₂)).elim
        · exact absurd (hv₂.symm.trans hv₁) hj_ne
        · exact hx₁.trans hx₂.symm
        · exact (hj₁_not (hv₁ ▸ h₂)).elim
        · exact (hj₀_not (hv₂ ▸ h₁)).elim
        · exact (hj₁_not (hv₂ ▸ h₁)).elim
        · obtain ⟨⟨u₁', r₁⟩, hr₁, heq₁⟩ := Finset.mem_image.mp h₁
          obtain ⟨⟨u₂', r₂⟩, hr₂, heq₂⟩ := Finset.mem_image.mp h₂
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq₁
          obtain ⟨rfl, hv⟩ := Prod.mk.inj heq₂
          have hr : r₁ = r₂ := Fin.ext (by simpa [liftJ] using congrArg Fin.val hv.symm)
          exact hM₀.2.2 u₁' _ r₁ hr₁ (hr ▸ hr₂)
    · have hnot_in₁ : (a₁, j₁) ∉ M₀' := hj₁_not
      have hnot_in₀ : (a₀, j₀) ∉ insert (a₁, j₁) M₀' := by
        rw [Finset.mem_insert, Prod.mk.injEq]
        exact not_or.mpr ⟨fun h => hne_a h.1, hj₀_not⟩
      rw [Finset.card_insert_of_notMem hnot_in₀, Finset.card_insert_of_notMem hnot_in₁, hM₀'_card]
      omega
    · rintro ⟨x, v⟩ he
      simp only [Finset.mem_insert, Prod.mk.injEq] at he
      rcases he with ⟨rfl, -⟩ | ⟨rfl, -⟩ | he
      · exact ha₀_lt
      · exact ha₁_lt
      · exact (hM₀'_lt he).1.trans (by omega)

/-- **`2k + 2k` deterministic lower bound:** for every `k` and every deterministic online algorithm
on `Fin (2 * k)`, there is an arrival sequence admitting a perfect matching of size `2 * k` on
which the algorithm matches at most `k` edges. -/
theorem exists_det_half_witness_mul (k : ℕ) (A : DetAlg (Fin (2 * k))) :
    ∃ arrivals : List (Finset (Fin (2 * k))),
      arrivals.length = 2 * k ∧
      (∃ M, IsMatching (graphOfArrivals arrivals) M ∧ M.card = 2 * k) ∧
      (A.runMatching arrivals).card ≤ k := by
  obtain ⟨M, hM, hcard, _⟩ := detHardPrefix_exists_matching k A k le_rfl
  exact ⟨detHardPrefix k A k le_rfl, length_detHardPrefix k A k le_rfl, ⟨M, hM, hcard⟩,
    detHardPrefix_card_le k A k le_rfl⟩

/-- **Tight `1/2` deterministic lower bound on a `2 + 2` graph** [KarpVaziraniVazirani1990]:
for every deterministic online matching algorithm on `Fin 2`, there is a 2-arrival sequence
admitting a perfect matching of size `2` on which the algorithm matches at most `1` edge. -/
theorem exists_det_half_witness (A : DetAlg (Fin 2)) :
    ∃ arrivals : List (Finset (Fin 2)),
      arrivals.length = 2 ∧
      (∃ M, IsMatching (graphOfArrivals arrivals) M ∧ M.card = 2) ∧
      (A.runMatching arrivals).card ≤ 1 :=
  exists_det_half_witness_mul 1 A

/-- No deterministic online matching algorithm achieves competitive ratio strictly above `1/2`,
even with an arbitrary additive slack `b`. -/
theorem not_det_competitive_of_gt_half {c : ℝ} (hc : (1 / 2 : ℝ) < c) (b : ℝ) :
    ∃ k : ℕ, ∀ A : DetAlg (Fin (2 * k)),
      ∃ (arrivals : List (Finset (Fin (2 * k)))) (M : Finset (Fin (2 * k) × Fin arrivals.length)),
        IsMatching (graphOfArrivals arrivals) M ∧
        ((A.runMatching arrivals).card : ℝ) < c * (M.card : ℝ) - b := by
  have hpos : 0 < 2 * c - 1 := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (b / (2 * c - 1))
  refine ⟨k, fun A => ?_⟩
  obtain ⟨arrivals, _, ⟨M, hM, hcard⟩, hle⟩ := exists_det_half_witness_mul k A
  refine ⟨arrivals, M, hM, ?_⟩
  have hbk : b < (2 * c - 1) * (k : ℝ) := by
    have := (div_lt_iff₀ hpos).mp hk
    linarith
  have hle' : ((A.runMatching arrivals).card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hle
  have hcard' : (M.card : ℝ) = 2 * (k : ℝ) := by exact_mod_cast hcard
  have hmul : c * (M.card : ℝ) = 2 * c * (k : ℝ) := by rw [hcard']; ring
  linarith

end DeterministicLowerBound

/-! ### Randomized online matching algorithms and Yao's principle -/

section Randomized

variable {L : Type*}

/-- A randomized online matching algorithm against an oblivious adversary: a discrete (countably
supported) probability distribution over deterministic online matching algorithms. -/
abbrev RandAlg (L : Type*) : Type _ := PMF (DetAlg L)

namespace RandAlg

variable [DecidableEq L]

/-- Expected matching size of `μ : RandAlg L` on a fixed arrival sequence `arrivals`. -/
noncomputable def expectedMatchingSize (μ : RandAlg L) (arrivals : List (Finset L)) :
    ℝ :=
  ∑' A, (μ A).toReal * ((A.runMatching arrivals).card : ℝ)

private theorem expectedMatchingSize_eq_toReal_tsum (μ : RandAlg L) (arrivals : List (Finset L)) :
    expectedMatchingSize μ arrivals =
      (∑' A, μ A * ((A.runMatching arrivals).card : ℝ≥0∞)).toReal := by
  have hfin : ∀ A, μ A * ((A.runMatching arrivals).card : ℝ≥0∞) ≠ ∞ := fun A =>
    ENNReal.mul_ne_top (PMF.apply_ne_top μ A) (ENNReal.natCast_ne_top _)
  rw [ENNReal.tsum_toReal_eq hfin]
  refine tsum_congr fun A => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]

theorem expectedMatchingSize_nonneg (μ : RandAlg L) (arrivals : List (Finset L)) :
    0 ≤ expectedMatchingSize μ arrivals :=
  tsum_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

@[simp] theorem expectedMatchingSize_pure (A : DetAlg L) (arrivals : List (Finset L)) :
    expectedMatchingSize (PMF.pure A) arrivals = (A.runMatching arrivals).card := by
  rw [expectedMatchingSize, tsum_eq_single A]
  · simp
  · intro A' hA'
    simp [PMF.pure_apply_of_ne _ _ hA']

/-- Expected matching size of a randomized algorithm drawn by mapping a finite distribution `ν`. -/
theorem expectedMatchingSize_map {α : Type*} [Fintype α] (ν : PMF α) (f : α → DetAlg L)
    (arrivals : List (Finset L)) :
    expectedMatchingSize (ν.map f) arrivals =
      ∑ a, (ν a).toReal * (((f a).runMatching arrivals).card : ℝ) :=
  Cslib.Probability.PMF.tsum_toReal_map_mul_natCast ν f fun A => (A.runMatching arrivals).card

/-- Expected matching size of a uniformly sampled finite family of deterministic algorithms. -/
theorem expectedMatchingSize_map_uniformOfFintype {α : Type*} [Fintype α] [Nonempty α]
    (f : α → DetAlg L) (arrivals : List (Finset L)) :
    expectedMatchingSize ((Cslib.Probability.PMF.uniformOfFintype α).map f) arrivals =
      (∑ a : α, (((f a).runMatching arrivals).card : ℝ)) / (Fintype.card α : ℝ) := by
  rw [expectedMatchingSize_map, div_eq_inv_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv]

/-- **Yao's principle** [Yao1977] for expected matching size: if under an input distribution `ν`
over arrival sequences, every deterministic online algorithm has expected matching size at most
`B`, then every randomized online algorithm has some instance in the support of `ν` on which its
expected matching size is at most `B`. -/
theorem exists_expectedMatchingSize_le {ι : Type*} [Fintype ι] (ν : PMF ι)
    (arrivals : ι → List (Finset L)) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ A : DetAlg L,
      ∑ i : ι, (ν i).toReal * ((A.runMatching (arrivals i)).card : ℝ) ≤ B)
    (μ : RandAlg L) :
    ∃ i ∈ ν.support, expectedMatchingSize μ (arrivals i) ≤ B := by
  obtain ⟨i, hi, hle⟩ := Cslib.Probability.PMF.exists_mem_support_tsum_mul_le ν μ
    (fun i A => ((A.runMatching (arrivals i)).card : ℝ≥0∞)) (ε := ENNReal.ofReal B) fun A _ => by
      have hA := h A
      rw [tsum_fintype]
      have hsum_ne_top :
          (∑ i : ι, ν i * ((A.runMatching (arrivals i)).card : ℝ≥0∞)) ≠ ∞ :=
        ENNReal.sum_ne_top.mpr fun i _ =>
          ENNReal.mul_ne_top (PMF.apply_ne_top ν i) (ENNReal.natCast_ne_top _)
      rw [← ENNReal.ofReal_toReal hsum_ne_top, ENNReal.ofReal_le_ofReal_iff hB,
        ENNReal.toReal_sum fun i _ =>
          ENNReal.mul_ne_top (PMF.apply_ne_top ν i) (ENNReal.natCast_ne_top _)]
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hA
  refine ⟨i, hi, ?_⟩
  rw [expectedMatchingSize_eq_toReal_tsum]
  exact ENNReal.toReal_le_of_le_ofReal hB hle

end RandAlg

end Randomized

end Cslib.Algorithms.Online.BipartiteMatching
